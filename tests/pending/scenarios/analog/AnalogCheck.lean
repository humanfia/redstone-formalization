import Redstone
import Lean.Data.Json

/-!
# Checking `getAnalogOutputSignal` against recorded comparators

    lake env lean --run tests/pending/scenarios/analog/AnalogCheck.lean tests/pending/traces/analog

The scenarios `analog-*` of this directory put a comparator behind each block of the component
`Redstone.Component.AnalogSource`. They cannot be run as differential tests before the
comparator is formalized, but their traces already say what the comparator read: at the end of
a trace the `OutputSignal` of a comparator in comparison mode without side input is the analog
signal of the block behind it. This program rebuilds the last frame of every trace given to it
and compares that number with the model's `analogSignal`. It does not use any model of the
comparator.

This program is a test tool and not part of the formalization.
-/

open Lean (Json)
open Redstone

namespace AnalogCheck

abbrev Key := ℤ × ℤ × ℤ

def key (p : Pos) : Key := (p.x, p.y, p.z)

def parsePosKey (s : String) : Except String Pos :=
  match (s.splitOn ",").map String.toInt? with
  | [some x, some y, some z] => return ⟨x, y, z⟩
  | _ => throw s!"not a position: {s}"

def objEntries (j : Json) : Except String (List (String × Json)) :=
  match j with
  | .obj kvs => return kvs.toList
  | _ => throw s!"not an object: {j.compress}"

/-- The typed JSON encoding of NBT used in traces, without the floating point tags. -/
partial def parseNbt (j : Json) : Except String Nbt := do
  match j with
  | .num _ => return .int (← j.getInt?)
  | .str s => return .string s
  | .arr a => return .list (← a.toList.mapM parseNbt)
  | .obj kvs =>
    match kvs.toList with
    | [("b", v)] => return .byte (← v.getInt?)
    | [("s", v)] => return .short (← v.getInt?)
    | [("l", v)] => return .long ((← v.getStr?).toInt?.getD 0)
    | [("c", v)] =>
      return .compound (← (← objEntries v).mapM fun (k, x) => return (k, ← parseNbt x))
    | _ => return .compound []
  | _ => throw s!"not an NBT tag: {j.compress}"

structure World where
  blocks : Std.HashMap Key Block := {}
  blockEntities : Std.HashMap Key BlockEntity := {}
  /-- The `OutputSignal` of the comparators. -/
  outputs : Std.HashMap Key ℤ := {}

def World.apply (w : World) (frame : Json) : Except String World := do
  let mut w := w
  for (k, v) in (frame.getObjVal? "blocks" >>= objEntries).toOption.getD [] do
    let some b := Block.parse? (← v.getStr?) | throw s!"not a block state: {v.compress}"
    w := { w with blocks := w.blocks.insert (key (← parsePosKey k)) b }
  for (k, v) in (frame.getObjVal? "blockEntities" >>= objEntries).toOption.getD [] do
    let p := key (← parsePosKey k)
    if v.isNull then
      w := { w with blockEntities := w.blockEntities.erase p, outputs := w.outputs.erase p }
    else
      let type ← (← v.getObjVal? "type").getStr?
      let nbt ← parseNbt (← v.getObjVal? "nbt")
      if type == "minecraft:comparator" then
        w := { w with outputs := w.outputs.insert p (nbt.intD "OutputSignal" 0) }
      match BlockEntity.ofNbt? type nbt with
      | some be => w := { w with blockEntities := w.blockEntities.insert p be }
      | none => throw s!"cannot read the block entity {v.compress}"
  return w

def World.level (w : World) : Level :=
  { Level.empty with
    world := ⟨fun p => w.blocks.getD (key p) .AIR⟩
    blockEntities := fun p => w.blockEntities.get? (key p) }

/-- `ComparatorBlock.getInputSignal` for a comparator at `c` that gets no redstone power from
behind: the analog signal of the block behind it, or of the block behind a conductor. `none`
when the comparator reads nothing. -/
def expected (l : Level) (c : Pos) (facing : Direction) : Option ℕ :=
  let target := c.step facing
  let b := l.blockAt target
  if b.attrs.analog then some ((rules.block b).analogSignal l target facing.opposite)
  else if b.isConductor then
    let target := target.step facing
    let b := l.blockAt target
    if b.attrs.analog then some ((rules.block b).analogSignal l target facing.opposite) else none
  else none

/-- Checks one trace. Returns the number of comparators checked and the failures. -/
def check (text : String) : Except String (ℕ × List String) := do
  let frames ← (← (← Json.parse text).getObjVal? "frames").getArr?
  let mut w : World := {}
  for f in frames do w ← w.apply f
  let l := w.level
  let mut n := 0
  let mut failures := []
  for (k, b) in w.blocks.toList do
    match b with
    | .comparator s =>
      let c : Pos := ⟨k.1, k.2.1, k.2.2⟩
      if let some want := expected l c s.facing.toDirection then
        n := n + 1
        let got := w.outputs.getD k 0
        if got ≠ want then
          let target := c.step s.facing.toDirection
          failures := s!"comparator at {k}: the server read {got}, the model gives {want} \
            for {l.blockAt target} {repr (l.blockEntities target)}" :: failures
    | _ => pure ()
  return (n, failures)

end AnalogCheck

def main (args : List String) : IO UInt32 := do
  let mut files : List System.FilePath := []
  for a in args do
    let path : System.FilePath := a
    if ← path.isDir then
      files := files ++ ((← path.readDir).qsort (·.fileName < ·.fileName)).toList.map (·.path)
    else files := files ++ [path]
  let mut total := 0
  let mut bad := 0
  for f in files do
    if f.extension != some "json" then continue
    match AnalogCheck.check (← IO.FS.readFile f) with
    | .error e =>
      IO.println s!"FAIL {f}: {e}"
      bad := bad + 1
    | .ok (0, _) => pure ()
    | .ok (n, failures) =>
      total := total + n
      if failures.isEmpty then IO.println s!"ok   {f}: {n} comparators"
      else
        bad := bad + failures.length
        IO.println s!"FAIL {f}: {failures.length} of {n} comparators"
        for m in failures do IO.println s!"  {m}"
  IO.println s!"{total} comparators checked, {bad} failures"
  return if bad == 0 then 0 else 1
