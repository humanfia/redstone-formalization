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
events and the entities.

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

/-! ### Scenarios and traces -/

inductive Action
  | use (p : Pos) (face : Direction)
  | useItem (p : Pos) (face : Direction) (item : String)
  | set (p : Pos) (b : Block) (flags : ℕ)
  | destroy (p : Pos) (drop : Bool)
  | kill (index : ℕ)

structure Scenario where
  name : String
  ticks : ℕ
  lo : Pos
  hi : Pos
  actions : List (ℕ × Action)
  dayTime : ℕ
  advanceTime : Bool
  weather : Weather

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
  return {
    name := ← (← j.getObjVal? "name").getStr?
    ticks := ← (← j.getObjVal? "ticks").getNat?
    lo := ← parsePos (← box.getObjVal? "min")
    hi := ← parsePos (← box.getObjVal? "max")
    actions := ← actions.toList.mapM parseAction
    dayTime := ← setting ℕ "dayTime" 6000
    advanceTime := ← setting Bool "advanceTime" false
    weather }

structure Frame where
  gameTime : ℕ
  blocks : List (Pos × Block)
  blockEntities : List (Pos × Option BlockEntity)
  tickers : List Pos
  scheduled : List (Pos × BlockId × ℤ × ℤ)
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

/-- Rebuilds the block and block entity maps of a level from its content in the box, so that
lookups stay fast however many blocks were set. Nothing outside the box is kept. -/
def normalize (s : Scenario) (l : Level) : Level :=
  let ps := boxPositions s
  let blocks : Std.HashMap Key Block :=
    ps.foldl (fun m p => let b := l.blockAt p; if b = .AIR then m else m.insert (Pos.key p) b) {}
  let bes : Std.HashMap Key BlockEntity :=
    ps.foldl (fun m p => match l.blockEntities p with
      | some be => m.insert (Pos.key p) be
      | none => m) {}
  { l with
    world := ⟨fun p => blocks.getD (Pos.key p) .AIR⟩
    blockEntities := fun p => bes.get? (Pos.key p) }

def initialLevel (s : Scenario) (f : Frame) : Level :=
  let e := ({} : Expected).apply f
  let l := normalize s { Level.empty with
    world := ⟨fun p => e.blocks.getD (Pos.key p) .AIR⟩
    blockEntities := fun p => e.blockEntities.get? (Pos.key p)
    blockEntityTickers := f.tickers
    ticks := f.scheduled.zipIdx.map fun ((p, b, delay, prio), i) =>
      ⟨p, b, (f.gameTime + delay).toNat, .ofValue prio, i⟩
    subTickCount := f.scheduled.length
    blockEvents := f.blockEvents
    entities := f.entities
    nextEntityIndex := f.entities.foldl (fun n e => max n (e.index + 1)) 0
    gameTime := f.gameTime
    dayTime := s.dayTime
    advanceTime := s.advanceTime
    weather := s.weather }
  { l with lightWorld := l.world }

def applyAction (a : Action) : M Unit :=
  match a with
  | .use p face => discard <| Level.useWithoutItem p face
  | .useItem p face item => discard <| Level.useItemOn p face item
  | .set p b flags => discard <| Level.setBlock p b flags
  | .destroy p drop => discard <| Level.destroyBlock p drop
  | .kill index => Level.removeEntity index

def sortTicks (ts : List ScheduledTick) : List ScheduledTick :=
  ts.foldl (fun acc t => ScheduledTick.insertSorted t acc) []

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
  let scheduled := (sortTicks l.ticks).map fun t =>
    (t.pos, t.block, (t.trigger : ℤ) - l.gameTime, t.priority.value)
  if scheduled ≠ f.scheduled then
    let show' (ts : List (Pos × BlockId × ℤ × ℤ)) :=
      ts.map fun (p, b, d, pr) => s!"{b.name}@{showPos p} in {d} priority {pr}"
    out := s!"scheduled ticks: expected {show' f.scheduled}, got {show' scheduled}" :: out
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

end Difftest

def main (args : List String) : IO UInt32 := do
  let roots := if args.isEmpty then ["tests/scenarios"] else args
  let files := (← roots.mapM fun r => Difftest.collect r).flatten
  if files.isEmpty then
    IO.println "no scenarios found"
    return 1
  let mut failed := 0
  for f in files do
    if !(← Difftest.runFile f) then failed := failed + 1
  IO.println s!"{files.length - failed} of {files.length} scenarios agree with the server"
  return if failed == 0 then 0 else 1
