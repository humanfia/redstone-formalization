import Redstone
import Lean.Data.Json

/-!
# Differential tests

`lake exe difftest [paths...]` runs scenarios through the Lean model and compares the result,
game tick by game tick, with the traces recorded from a real Minecraft server (see
`tests/FORMAT.md`). A path is a scenario file or a directory of scenarios; without arguments
every scenario under `tests/scenarios` is run. The trace of `tests/scenarios/<unit>/<name>.json`
is `tests/traces/<unit>/<name>.trace.json`.

The model starts from frame 0 of the trace. Before each game tick the scenario's actions for
that tick are applied; after it the model is compared with the frame: every block and block
entity in the box, the order in which block entities tick, the scheduled ticks, the block
events, the scheduled fluid ticks (`compareFluidTicks`) and the entities.

A run without arguments first checks the model's container signal against the same
computation in `Float32` (`signalSelfCheck`); a difference fails the run.

This program is a test tool and not part of the formalization.
-/

open Lean (Json)
open Redstone

namespace Difftest

abbrev Key := ℤ × ℤ × ℤ

def Pos.key (p : Pos) : Key := (p.x, p.y, p.z)

def posOfKey (k : Key) : Pos := ⟨k.1, k.2.1, k.2.2⟩

def showPos (p : Pos) : String := s!"({p.x}, {p.y}, {p.z})"

/-! ### Reading JSON -/

def parsePos (j : Json) : Except String Pos := do
  match ← j.getArr? with
  | #[x, y, z] => return ⟨← x.getInt?, ← y.getInt?, ← z.getInt?⟩
  | _ => throw s!"not a position: {j.compress}"

def parsePosKey (s : String) : Except String Pos :=
  match (s.splitOn ",").map String.toInt? with
  | [some x, some y, some z] => return ⟨x, y, z⟩
  | _ => throw s!"not a position: {s}"

def parseDirection (s : String) : Except String Direction :=
  match Direction.ofName? s with
  | some d => return d
  | none => throw s!"not a direction: {s}"

def parseBlock (s : String) : Except String Block :=
  match Block.parse? s with
  | some b => return b
  | none => throw s!"not a block state: {s}"

def parseBlockId (s : String) : Except String BlockId :=
  match BlockId.ofName? s with
  | some b => return b
  | none => throw s!"not a block: {s}"

def hexToNat (s : String) : Except String ℕ :=
  s.foldl (init := pure 0) fun acc c => do
    let n ← acc
    if c.isDigit then return 16 * n + (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then return 16 * n + (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then return 16 * n + (c.toNat - 'A'.toNat + 10)
    else throw s!"not hexadecimal: {s}"

def parseDouble (j : Json) : Except String Float := do
  return Float.ofBits (UInt64.ofNat (← hexToNat (← j.getStr?)))

def parseVec3 (j : Json) : Except String Vec3 := do
  match ← j.getArr? with
  | #[x, y, z] => return ⟨← parseDouble x, ← parseDouble y, ← parseDouble z⟩
  | _ => throw s!"not a vector: {j.compress}"

def objEntries (j : Json) : Except String (List (String × Json)) :=
  match j with
  | .obj kvs => return kvs.toList
  | _ => throw s!"not an object: {j.compress}"

def parseIntStr (j : Json) : Except String ℤ := do
  match (← j.getStr?).toInt? with
  | some n => return n
  | none => throw s!"not an integer: {j.compress}"

/-- The typed JSON encoding of NBT used in traces. -/
partial def parseNbt (j : Json) : Except String Nbt := do
  match j with
  | .num _ => return .int (← j.getInt?)
  | .str s => return .string s
  | .arr a => return .list (← a.toList.mapM parseNbt)
  | .obj kvs =>
    match kvs.toList with
    | [("b", v)] => return .byte (← v.getInt?)
    | [("s", v)] => return .short (← v.getInt?)
    | [("l", v)] => return .long (← parseIntStr v)
    | [("f", v)] => return .float (← hexToNat (← v.getStr?))
    | [("d", v)] => return .double (← hexToNat (← v.getStr?))
    | [("B", v)] => return .byteArray (← (← v.getArr?).toList.mapM (·.getInt?))
    | [("I", v)] => return .intArray (← (← v.getArr?).toList.mapM (·.getInt?))
    | [("L", v)] => return .longArray (← (← v.getArr?).toList.mapM parseIntStr)
    | [("c", v)] =>
      return .compound (← (← objEntries v).mapM fun (k, x) => return (k, ← parseNbt x))
    | _ => throw s!"not an NBT tag: {j.compress}"
  | _ => throw s!"not an NBT tag: {j.compress}"

/-! ### SNBT

The text form of NBT (`TagParser`), in which a scenario gives the data of an entity it
summons. -/

namespace Snbt

def isBare (c : Char) : Bool := c.isAlphanum || c == '.' || c == '_' || c == '+' || c == '-'

def skip : List Char → List Char
  | c :: cs => if c.isWhitespace then skip cs else c :: cs
  | [] => []

/-- A quoted string, after its opening quote `q`. -/
def quoted (q : Char) : List Char → String → Except String (String × List Char)
  | '\\' :: c :: cs, acc => quoted q cs (acc.push c)
  | c :: cs, acc => if c == q then pure (acc, cs) else quoted q cs (acc.push c)
  | [], _ => throw "SNBT: a string is not closed"

/-- A decimal number. SNBT allows `.5` and `5.`, which JSON does not. -/
def float? (text : String) : Option Float :=
  let (sign, digits) := if text.startsWith "-" then ("-", (text.drop 1).toString) else ("", text)
  let digits := if digits.startsWith "." then "0" ++ digits else digits
  let digits := if digits.endsWith "." then digits ++ "0" else digits
  match Json.parse (sign ++ digits) with
  | .ok (.num n) => some n.toFloat
  | _ => none

/-- The tag an unquoted token stands for: a number with its suffix, a boolean, or a string. -/
def ofBare (t : String) : Nbt :=
  let body := (t.dropEnd 1).toString
  let lower := t.toLower
  if lower == "true" then .byte 1
  else if lower == "false" then .byte 0
  else if let some n := t.toInt? then .int n
  else match t.back.toLower, body.toInt?, float? body with
    | 'b', some n, _ => .byte n
    | 's', some n, _ => .short n
    | 'l', some n, _ => .long n
    | 'f', _, some x => .float x.toFloat32.toBits.toNat
    | 'd', _, some x => .double x.toBits.toNat
    | _, _, _ =>
      match float? t with
      | some x => if t.contains '.' then .double x.toBits.toNat else .string t
      | none => .string t

mutual

partial def value (cs : List Char) : Except String (Nbt × List Char) := do
  match skip cs with
  | '{' :: cs => fields (skip cs) []
  | '[' :: 'B' :: ';' :: cs => do
    let (l, cs) ← elements (skip cs) []
    pure (.byteArray (l.filterMap (·.toInt?)), cs)
  | '[' :: 'I' :: ';' :: cs => do
    let (l, cs) ← elements (skip cs) []
    pure (.intArray (l.filterMap (·.toInt?)), cs)
  | '[' :: 'L' :: ';' :: cs => do
    let (l, cs) ← elements (skip cs) []
    pure (.longArray (l.filterMap (·.toInt?)), cs)
  | '[' :: cs => do
    let (l, cs) ← elements (skip cs) []
    pure (.list l, cs)
  | '"' :: cs => do
    let (v, cs) ← quoted '"' cs ""
    pure (.string v, cs)
  | '\'' :: cs => do
    let (v, cs) ← quoted '\'' cs ""
    pure (.string v, cs)
  | cs =>
    let token := cs.takeWhile isBare
    if token.isEmpty then throw s!"SNBT: unexpected `{String.ofList (cs.take 8)}`"
    else pure (ofBare (String.ofList token), cs.dropWhile isBare)

/-- The elements of a list, up to its closing bracket. -/
partial def elements (cs : List Char) (acc : List Nbt) : Except String (List Nbt × List Char) := do
  match cs with
  | ']' :: cs => pure (acc.reverse, cs)
  | cs =>
    let (v, cs) ← value cs
    match skip cs with
    | ',' :: cs => elements (skip cs) (v :: acc)
    | ']' :: cs => pure ((v :: acc).reverse, cs)
    | _ => throw "SNBT: a list is not closed"

/-- The entries of a compound, up to its closing brace. -/
partial def fields (cs : List Char) (acc : List (String × Nbt)) :
    Except String (Nbt × List Char) := do
  match cs with
  | '}' :: cs => pure (.compound acc.reverse, cs)
  | cs =>
    let (key, cs) ← match cs with
      | '"' :: cs => quoted '"' cs ""
      | '\'' :: cs => quoted '\'' cs ""
      | cs => pure (String.ofList (cs.takeWhile isBare), cs.dropWhile isBare)
    let ':' :: cs := skip cs | throw s!"SNBT: no value for the key `{key}`"
    let (v, cs) ← value cs
    match skip cs with
    | ',' :: cs => fields (skip cs) ((key, v) :: acc)
    | '}' :: cs => pure (.compound ((key, v) :: acc).reverse, cs)
    | _ => throw "SNBT: a compound is not closed"

end

/-- Reads a tag from its text form. -/
def parse (text : String) : Except String Nbt := do
  let (v, rest) ← value text.toList
  if (skip rest).isEmpty then pure v else throw "SNBT: text after the tag"

end Snbt

/-! ### Scenarios and traces -/

/-- The actions of a scenario are the inputs of the model. -/
abbrev Action := Redstone.Input

structure Scenario where
  name : String
  ticks : ℕ
  lo : Pos
  hi : Pos
  actions : List (ℕ × Action)
  dayTime : ℕ
  advanceTime : Bool
  weather : Weather
  randomTickSpeed : ℕ
  blockDrops : Bool
  fireSpreadRadiusAroundPlayer : ℤ

/-- A coordinate of an entity in a scenario: a JSON number. -/
def parseCoordinate (j : Json) : Except String Float := do
  return (← j.getNum?).toFloat

def parseAction (j : Json) : Except String (ℕ × Action) := do
  let tick ← (← j.getObjVal? "tick").getNat?
  let type ← (← j.getObjVal? "type").getStr?
  let pos := j.getObjVal? "pos" >>= parsePos
  let face := j.getObjVal? "face" >>= (·.getStr?) >>= parseDirection
  match type with
  | "use" => return (tick, .use (← pos) (← face))
  | "use_item" => return (tick, .useItem (← pos) (← face) (← (← j.getObjVal? "item").getStr?))
  | "set" =>
    let flags := (j.getObjValAs? ℕ "flags").toOption.getD 3
    return (tick, .set (← pos) (← parseBlock (← (← j.getObjVal? "state").getStr?)) flags)
  | "destroy" => return (tick, .destroy (← pos) ((j.getObjValAs? Bool "drop").toOption.getD false))
  | "kill" => return (tick, .kill (← (← j.getObjVal? "entity").getNat?))
  | "summon" =>
    let e ← j.getObjVal? "entity"
    let pos ← match ← (← e.getObjVal? "pos").getArr? with
      | #[x, y, z] => pure (⟨← parseCoordinate x, ← parseCoordinate y, ← parseCoordinate z⟩ : Vec3)
      | _ => throw s!"not a position: {e.compress}"
    let nbt ← match e.getObjVal? "nbt" with
      | .ok v => Snbt.parse (← v.getStr?)
      | .error _ => pure (.compound [])
    return (tick, .summon (← (← e.getObjVal? "type").getStr?) pos nbt)
  | _ => throw s!"the Lean runner does not support the action `{type}`"

def parseScenario (j : Json) : Except String Scenario := do
  let box ← j.getObjVal? "box"
  let actions := (j.getObjVal? "actions" >>= (·.getArr?)).toOption.getD #[]
  let settings := (j.getObjVal? "settings").toOption.getD (Json.mkObj [])
  -- A setting that is absent has its default value; one that is present must be well formed.
  let setting (α : Type) [Lean.FromJson α] (key : String) (default : α) : Except String α :=
    match settings.getObjVal? key with
    | .ok v => Lean.fromJson? v
    | .error _ => pure default
  let weather ← match ← setting String "weather" "clear" with
    | "clear" => pure Weather.clear
    | "rain" => pure Weather.rain
    | "thunder" => pure Weather.thunder
    | w => throw s!"not a weather: {w}"
  let fireSpreadRadiusAroundPlayer ← setting ℤ "fireSpreadRadiusAroundPlayer" 128
  if fireSpreadRadiusAroundPlayer < -1 then
    throw s!"settings.fireSpreadRadiusAroundPlayer must be >= -1: {fireSpreadRadiusAroundPlayer}"
  return {
    name := ← (← j.getObjVal? "name").getStr?
    ticks := ← (← j.getObjVal? "ticks").getNat?
    lo := ← parsePos (← box.getObjVal? "min")
    hi := ← parsePos (← box.getObjVal? "max")
    actions := ← actions.toList.mapM parseAction
    dayTime := ← setting ℕ "dayTime" 6000
    advanceTime := ← setting Bool "advanceTime" false
    weather
    randomTickSpeed := ← setting ℕ "randomTickSpeed" 0
    blockDrops := ← setting Bool "blockDrops" false
    fireSpreadRadiusAroundPlayer }

structure Frame where
  gameTime : ℕ
  blocks : List (Pos × Block)
  blockEntities : List (Pos × Option BlockEntity)
  tickers : List Pos
  scheduled : List (Pos × BlockId × ℤ × ℤ)
  fluidTicks : List (Pos × Fluid × ℤ × ℤ)
  blockEvents : List BlockEvent
  entities : List Entity

def parseBlockEntity (j : Json) : Except String (Option BlockEntity) := do
  if j.isNull then return none
  let type ← (← j.getObjVal? "type").getStr?
  match BlockEntity.ofNbt? type (← parseNbt (← j.getObjVal? "nbt")) with
  | some be => return some be
  | none => throw s!"cannot read the block entity {j.compress}"

def parseEntity (j : Json) : Except String Entity := do
  let type ← (← j.getObjVal? "type").getStr?
  let nbt ← parseNbt (← j.getObjVal? "nbt")
  let base := Entities.Base.ofTrace? (← parseVec3 (← j.getObjVal? "pos"))
    (← parseVec3 (← j.getObjVal? "motion")) (← (← j.getObjVal? "onGround").getBool?) nbt
  match base, EntityData.ofNbt? type nbt with
  | some base, some data => return ⟨← (← j.getObjVal? "index").getNat?, base, data⟩
  | _, _ => throw s!"cannot read the entity {j.compress}"

def parseFrame (j : Json) : Except String Frame := do
  let arr (k : String) := (j.getObjVal? k >>= (·.getArr?)).toOption.getD #[]
  let obj (k : String) := (j.getObjVal? k >>= objEntries).toOption.getD []
  return {
    gameTime := ← (← j.getObjVal? "gameTime").getNat?
    blocks := ← (obj "blocks").mapM fun (k, v) =>
      return (← parsePosKey k, ← parseBlock (← v.getStr?))
    blockEntities := ← (obj "blockEntities").mapM fun (k, v) =>
      return (← parsePosKey k, ← parseBlockEntity v)
    tickers := ← (arr "blockEntityTickers").toList.mapM parsePos
    scheduled := ← (arr "scheduled").toList.mapM fun t =>
      return (← parsePos (← t.getObjVal? "pos"),
        ← parseBlockId (← (← t.getObjVal? "block").getStr?),
        ← (← t.getObjVal? "delay").getInt?, ← (← t.getObjVal? "priority").getInt?)
    fluidTicks := ← (arr "fluidTicks").toList.mapM fun t => do
      let name ← (← t.getObjVal? "fluid").getStr?
      let some fluid := Fluid.ofName? name | throw s!"not a fluid: {name}"
      return (← parsePos (← t.getObjVal? "pos"), fluid,
        ← (← t.getObjVal? "delay").getInt?, ← (← t.getObjVal? "priority").getInt?)
    blockEvents := ← (arr "blockEvents").toList.mapM fun e =>
      return ⟨← parsePos (← e.getObjVal? "pos"),
        ← parseBlockId (← (← e.getObjVal? "block").getStr?),
        ← (← e.getObjVal? "a").getInt?, ← (← e.getObjVal? "b").getInt?⟩
    entities := ← (arr "entities").toList.mapM parseEntity }

/-! ### Running and comparing -/

def boxPositions (s : Scenario) : List Pos := Id.run do
  let mut out := []
  for x in [0:(s.hi.x - s.lo.x + 1).toNat] do
    for y in [0:(s.hi.y - s.lo.y + 1).toNat] do
      for z in [0:(s.hi.z - s.lo.z + 1).toNat] do
        out := ⟨s.lo.x + x, s.lo.y + y, s.lo.z + z⟩ :: out
  return out.reverse

/-- What the server's world looks like, accumulated from the frames. -/
structure Expected where
  blocks : Std.HashMap Key Block := {}
  blockEntities : Std.HashMap Key BlockEntity := {}

def Expected.apply (e : Expected) (f : Frame) : Expected :=
  { blocks := f.blocks.foldl (fun m (p, b) => m.insert (Pos.key p) b) e.blocks
    blockEntities := f.blockEntities.foldl
      (fun m (p, be) => match be with
        | some be => m.insert (Pos.key p) be
        | none => m.erase (Pos.key p)) e.blockEntities }

/-- Rebuilds the block and block entity maps of a level from its content in the box. Nothing
outside the box is kept. -/
def normalize (s : Scenario) (l : Level) : Level :=
  let ps := boxPositions s
  { l with
    world := World.ofList (ps.filterMap fun p =>
      let b := l.blockAt p
      if b = .AIR then none else some (p, b))
    blockEntities := PosMap.ofList (ps.filterMap fun p =>
      (l.blockEntities p).map fun be => (p, be)) }

/-- Whether the scheduled fluid ticks of the model are compared with the trace. A trace lists
the ticks inside the box of the scenario, so those of the model outside it are not compared
(nor is anything else out there: the runner forgets the blocks outside the box after every
tick, so a scenario should keep its fluids inside). -/
def compareFluidTicks : Bool := true

def initialLevel (s : Scenario) (f : Frame) : Level :=
  let e := ({} : Expected).apply f
  let l := normalize s { Level.empty with
    world := World.ofList (e.blocks.toList.map fun (k, b) => (posOfKey k, b))
    blockEntities := PosMap.ofList (e.blockEntities.toList.map fun (k, be) => (posOfKey k, be))
    blockEntityTickers := f.tickers
    ticks := f.scheduled.zipIdx.map fun ((p, b, delay, prio), i) =>
      ⟨p, b, (f.gameTime + delay).toNat, .ofValue prio, i⟩
    fluidTicks := f.fluidTicks.zipIdx.map fun ((p, fluid, delay, prio), i) =>
      ⟨p, fluid, (f.gameTime + delay).toNat, .ofValue prio, f.scheduled.length + i⟩
    subTickCount := f.scheduled.length + f.fluidTicks.length
    blockEvents := f.blockEvents
    entities := f.entities
    nextEntityIndex := f.entities.foldl (fun n e => max n (e.index + 1)) 0
    gameTime := f.gameTime
    dayTime := s.dayTime
    advanceTime := s.advanceTime
    weather := s.weather
    randomTickSpeed := s.randomTickSpeed
    blockDrops := s.blockDrops
    fireSpreadRadiusAroundPlayer := s.fireSpreadRadiusAroundPlayer
    randomTickBox := some (s.lo, s.hi) }
  { l with lightWorld := l.world }

def applyAction (a : Action) : M Unit := a.apply

/-- The differences between the model and the server after a tick. -/
def compare (s : Scenario) (l : Level) (e : Expected) (f : Frame) : List String := Id.run do
  let mut out : List String := []
  if l.overflow then out := "the model reached one of its bounds (Level.overflow)" :: out
  if l.gameTime ≠ f.gameTime then
    out := s!"game time: expected {f.gameTime}, got {l.gameTime}" :: out
  for p in boxPositions s do
    let want := e.blocks.getD (Pos.key p) .AIR
    let got := l.blockAt p
    if want ≠ got then out := s!"block at {showPos p}: expected {want}, got {got}" :: out
    let wantBe := e.blockEntities.get? (Pos.key p)
    -- A trace shows saved data only: the fields the game does not save are left out.
    let gotBe := (l.blockEntities p).map Component.Container.savedData
    if wantBe ≠ gotBe then
      out := s!"block entity at {showPos p}: expected {repr wantBe}, got {repr gotBe}" :: out
  let tickers := l.blockEntityTickers ++ l.pendingBlockEntityTickers
  if tickers ≠ f.tickers then
    out := s!"block entity tickers: expected {f.tickers.map showPos}, \
      got {tickers.map showPos}" :: out
  let scheduled := (ScheduledTickOf.sortTicks l.ticks).map fun t =>
    (t.pos, t.block, (t.trigger : ℤ) - l.gameTime, t.priority.value)
  if scheduled ≠ f.scheduled then
    let show' (ts : List (Pos × BlockId × ℤ × ℤ)) :=
      ts.map fun (p, b, d, pr) => s!"{b.name}@{showPos p} in {d} priority {pr}"
    out := s!"scheduled ticks: expected {show' f.scheduled}, got {show' scheduled}" :: out
  if compareFluidTicks then
    -- The trace lists the fluid ticks inside the box only.
    let inBox (p : Pos) : Bool :=
      s.lo.x ≤ p.x && p.x ≤ s.hi.x && s.lo.y ≤ p.y && p.y ≤ s.hi.y && s.lo.z ≤ p.z && p.z ≤ s.hi.z
    let fluidTicks := (ScheduledTickOf.sortTicks (l.fluidTicks.filter (inBox ·.pos))).map fun t =>
      (t.pos, t.fluid, (t.trigger : ℤ) - l.gameTime, t.priority.value)
    if fluidTicks ≠ f.fluidTicks then
      let show' (ts : List (Pos × Fluid × ℤ × ℤ)) :=
        ts.map fun (p, b, d, pr) => s!"{b.name}@{showPos p} in {d} priority {pr}"
      out := s!"fluid ticks: expected {show' f.fluidTicks}, got {show' fluidTicks}" :: out
  if l.blockEvents ≠ f.blockEvents then
    out := s!"block events: expected {repr f.blockEvents}, got {repr l.blockEvents}" :: out
  if l.entities.length ≠ f.entities.length then
    out := s!"entities: expected {f.entities.length}, got {l.entities.length}" :: out
  for want in f.entities do
    match l.entity? want.index with
    | none => out := s!"entity {want.index}: missing" :: out
    | some got =>
      if !(want == got) then
        out := s!"entity {want.index}: expected {repr want}, got {repr got}" :: out
  return out.reverse

/-- Runs a scenario against its trace. Returns the first tick at which the model differs from
the server, with the differences. -/
def runScenario (s : Scenario) (frames : List Frame) :
    Except String (Option (ℕ × List String)) := do
  let f0 :: rest := frames | throw "the trace has no frames"
  if rest.length ≠ s.ticks then throw s!"the trace has {rest.length} ticks, the scenario {s.ticks}"
  let mut e := ({} : Expected).apply f0
  let mut l := initialLevel s f0
  let mut t := 0
  for f in rest do
    t := t + 1
    for (tick, a) in s.actions do
      if tick = t then l := (rules.run (applyAction a) l).2
    l := normalize s l.step
    e := e.apply f
    let diffs := compare s l e f
    if !diffs.isEmpty then return some (t, diffs)
  return none

def tracePath (scenario : System.FilePath) : System.FilePath :=
  let parts := scenario.components.map fun c => if c == "scenarios" then "traces" else c
  (System.mkFilePath parts).withExtension "trace.json"

partial def collect (path : System.FilePath) : IO (List System.FilePath) := do
  if ← path.isDir then
    let entries := (← path.readDir).qsort (·.fileName < ·.fileName)
    return (← entries.toList.mapM (collect ·.path)).flatten
  else if path.extension == some "json" then return [path]
  else return []

def runFile (path : System.FilePath) : IO Bool := do
  let scenarioText ← IO.FS.readFile path
  let trace := tracePath path
  if !(← trace.pathExists) then
    IO.println s!"FAIL {path}: no trace at {trace}; record it with tools/record.sh"
    return false
  let traceText ← IO.FS.readFile trace
  let outcome : Except String (Option (ℕ × List String)) := do
    let scenario ← parseScenario (← Json.parse scenarioText)
    let frames ← (← Json.parse traceText).getObjVal? "frames"
    let frames ← (← frames.getArr?).toList.mapM parseFrame
    runScenario scenario frames
  match outcome with
  | .error err =>
    IO.println s!"FAIL {path}: {err}"
    return false
  | .ok (some (t, diffs)) =>
    IO.println s!"FAIL {path}: first difference at tick {t}"
    for d in diffs.take 8 do IO.println s!"  {d}"
    if diffs.length > 8 then IO.println s!"  ... and {diffs.length - 8} more"
    return false
  | .ok none =>
    IO.println s!"ok   {path}"
    return true

/-! ### Self-check: the signal of a container

The model computes the signal a comparator reads from a container with exact arithmetic that
is rounded to single precision after each operation (`Container.redstoneSignal`), so that the
kernel can evaluate it. The check below compares it with the same computation done in
`Float32`, as the game does it. -/

/-- `AbstractContainerMenu.getRedstoneSignalFromContainer` computed in `Float32`, as the model
did before it was made exact. Only the self-check uses it. -/
def redstoneSignalF32 (items : Inventory) (limit : ℕ := 99) : ℕ :=
  let total : Float32 := items.foldl (init := 0) fun acc s =>
    if s.isEmpty then acc
    else acc + s.count.toFloat32 / (s.containerMaxStackSize limit).toFloat32
  let total := total / items.length.toFloat32
  -- `Mth.lerpDiscrete(totalPercent, 0, 15)`
  (total * 14).floor.toUInt32.toNat + (if total > 0 then 1 else 0)

/-- The numbers of slots the containers of the game have. -/
def containerSizes : List ℕ := [1, 3, 5, 9, 27, 54]

/-- A stack of `count` items that stacks up to `max`. -/
def stackOf (count max : ℕ) : ItemStack :=
  { id := "minecraft:redstone", count
    components := [("minecraft:max_stack_size", toString max)] }

/-- Every container with one stack in its first slot: `count ≤ max ≤ 99`, in each size. -/
def singleSlotCases : List (Inventory × ℕ) := Id.run do
  let mut out := []
  for slots in containerSizes do
    for max in List.range 100 do
      for count in List.range (max + 1) do
        if count > 0 then
          out := ((Inventory.empty slots).setItem 0 (stackOf count max), 99) :: out
  return out

/-- A step of a linear congruential generator (the constants of Knuth's MMIX). -/
def nextSeed (seed : UInt64) : UInt64 := seed * 6364136223846793005 + 1442695040888963407

/-- A number below `bound` from the high bits of the seed. -/
def below (seed : UInt64) (bound : ℕ) : ℕ := (seed >>> 33).toNat % bound

/-- Inventories filled by a fixed generator: each slot is empty or holds a stack whose greatest
size is 1, 16, 64 or any number up to 99, with any count up to that size; the container's own
limit is 99, 64 or 1. The same inventories every run. -/
def randomCases (n : ℕ) : List (Inventory × ℕ) := Id.run do
  let mut seed : UInt64 := 20261128
  let mut out := []
  for _ in List.range n do
    seed := nextSeed seed
    let slots := containerSizes.getD (below seed containerSizes.length) 1
    seed := nextSeed seed
    let limit := [99, 99, 64, 1].getD (below seed 4) 99
    let mut items : Inventory := []
    for _ in List.range slots do
      seed := nextSeed seed
      let kind := below seed 6
      seed := nextSeed seed
      let max :=
        match kind with
        | 0 => 1
        | 1 => 16
        | 2 | 3 => 64
        | _ => below seed 99 + 1
      seed := nextSeed seed
      let count := below seed max + 1
      seed := nextSeed seed
      -- One slot in four is empty, and some containers are full to the brim.
      let stack :=
        if below seed 4 = 0 then ItemStack.empty
        else if below seed 4 = 1 then stackOf max max
        else stackOf count max
      items := stack :: items
    out := (items, limit) :: out
  return out

/-- Compares the two computations of the container signal. Returns the number of cases and
the ones on which they differ. -/
def signalSelfCheck (_ : Unit) : ℕ × List String :=
  let cases := singleSlotCases ++ randomCases 20000
  let bad := cases.filterMap fun (items, limit) =>
    let exact := Component.Container.redstoneSignal items limit
    let float := redstoneSignalF32 items limit
    if exact = float then none
    else
      let slots := items.map fun s => (s.count, s.containerMaxStackSize limit)
      some s!"limit {limit}, slots {slots}: exact {exact}, Float32 {float}"
  (cases.length, bad)

end Difftest

def main (args : List String) : IO UInt32 := do
  let roots := if args.isEmpty then ["tests/scenarios"] else args
  let files := (← roots.mapM fun r => Difftest.collect r).flatten
  if files.isEmpty then
    IO.println "no scenarios found"
    return 1
  -- The self-check belongs to the full run, which is what `lake test` does.
  let (cases, bad) := if args.isEmpty then Difftest.signalSelfCheck () else (0, [])
  for b in bad.take 8 do IO.println s!"FAIL container signal: {b}"
  if args.isEmpty then
    IO.println s!"container signal: {cases - bad.length} of {cases} cases agree with Float32"
  let mut failed := 0
  for f in files do
    if !(← Difftest.runFile f) then failed := failed + 1
  IO.println s!"{files.length - failed} of {files.length} scenarios agree with the server"
  return if failed == 0 && bad.isEmpty then 0 else 1
