import Redstone.Proof.Circuit

/-!
# The torch cell of the adders and the decoder

Every circuit of this directory is built from one cell of redstone torches: two input blocks
`A` and `B`, and four NOR gates that between them decode the two inputs. A redstone torch on a
block is a NOR gate of everything that powers the block.

| torch | on the block | which is powered by | so the torch is lit when |
|---|---|---|---|
| `nA`, `nB` | `A`, `B` | the input | the input is off |
| `n` | `N` | the dust `D` between the inputs | neither input is on |
| `p` | `P` | `A`, or the torch `n` | only `B` is on |
| `q` | `Q` | `B`, or the torch `n` | only `A` is on |
| `c` | `G` | the dust `E` between `nA` and `nB` | both inputs are on |

The dust `S` between `p` and `q` is therefore the exclusive or of the inputs, and the torch `c`
their conjunction. The cell is a half adder (`HalfAdder.lean`); its torches `n`, `q`, `p` and
`c` are the four outputs of a 2-to-4 line decoder (`Decoder.lean`); two cells with an OR of
their `c` torches are a full adder (`adderBit`, `FullAdder.lean`), and full adders in a row,
each taking the carry of the one before, are a ripple-carry adder (`TwoBitAdder.lean`,
`FourBitAdder.lean`). This is the textbook construction of an adder from NOR gates, as it is
built with torches. The arrangement in space is ours: it is chosen so that every piece of dust
but the carry is on its own or in a line of three, because dust is what the kernel evaluates
slowly (`Redstone/Proof/README.md`).

The cell, with `o` the position of the block `P` (east is `+x`, up is `+y`, south is `+z`).
Each layer is seen from above, north at the top:

```
        y = 2      y = 1      y = 0      y = -1
z = -2  .  .  .    .  c  .    .  .  .    .  .  .
z = -1  nA E  nB   .  G  .    p  S  q    .  L  .
z =  0  A  .  B    XP n  XQ   P  .  Q    .  .  .
z =  1  a  D  b    #  N  #    .  .  .    .  .  .
    x = 0  1  2
```

* `A`, `B`, `N`, `G`, `P`, `Q`: stone. `L`, the block under `S`, is not part of `cell`: it is
  stone, or the lamp that shows `S`.
* `nA`, `nB`, `n`, `p`, `q`, `c`: redstone wall torches. Each is on the block south of it, so
  all of them face north.
* `D`: dust on `N`, which it powers. `a` and `b` are what gives `D` the inputs. For an input
  that is a lever, the lever is there, on the south side of the input block, and there is
  nothing under it. For an input that comes through a repeater pointing into the input block,
  it is one more piece of dust, on the stone `#`: dust takes power from a block when a lever,
  a repeater or a torch powers the block itself (a *strongly* powered block), and not when
  only other dust powers it.
* `XP`, `XQ`: dust on `P` and on `Q`, under `A` and under `B`, next to the torch `n`. `XP` is
  on when `A` is strongly powered or `n` is lit, and powers `P`. Because `XP` cannot take
  power from blocks that only dust powers, nothing flows back from `n` into the inputs.
* `E`: dust on `G`, between the torches `nA` and `nB`. `S`: dust on `L`, between `p` and `q`.

With both inputs off the cell is at rest with `nA`, `nB` and `n` lit, `XP`, `XQ` and `E` at
power 15, and everything else off: `cell` is that state. `cell o true ..` is the mirror image,
with `B` to the west of `A`.

The full adder `adderBit` is described at its definition. The rest of the file is what the
circuit files share: the observations (`lampLit`, `reading`), the inputs (`useLevers`), and
the lemma that extends a run that has come to rest (`runSchedule_first_of_quiescent`).

## Not yet proved

* **The 2-bit adder with all levers used together.** Its truth table (`TwoBitAdder.adds`, all
  32 inputs) sets the inputs in two steps, bit 0 and the carry in first and bit 1 when the
  circuit is at rest again. With the levers of both bits used before the same game tick it is
  proved for `3 + 0 + 1` only (`TwoBitAdder/AtOnce.lean`); one such run costs the kernel 20 to
  30 seconds.
* **The 4-bit adder for all 512 inputs.** `FourBitAdder.lean` proves three of them. One input
  of the 4-bit adder costs the kernel between 25 and 80 seconds (a game tick in which nothing
  happens costs over a second in a level of 227 blocks, and the carry takes 30 game ticks), so
  all of them would be hours. A proof by composition (four proved full adders, joined) needs a frame
  rule, "the blocks outside this box do not matter", which the proof foundation does not have
  (`Redstone/Proof/README.md`, "What is not here").
* **Inputs that change while the circuit is not at rest, and changes back to zero**, except
  for the half adder (`HalfAdder.walk`). Every other run here starts from a circuit at rest
  and only switches levers on.
* **Binary to 7-segment decoder, the comparator full adder and the analog (hex) adder** of the
  catalogue: not built here.
-/

namespace Redstone.Theorems.Arithmetic

/-- Stone. -/
def stone : Block := .plain .stone

/-- A redstone torch on the north side of a block. -/
def torch (lit : Bool) : Block := .redstoneWallTorch ⟨.north, lit⟩

/-- A redstone lamp. -/
def lamp (lit : Bool) : Block := .redstoneLamp ⟨lit⟩

/-- Redstone dust that runs east and west. -/
def dustEW (power : Fin 16) : Block := .redstoneWire ⟨.side, .none, power, .none, .side⟩

/-- The position `(u, v, w)` of a cell at `o`: `u` to the east (to the west in the mirror
image), `v` up, `w` to the south. -/
def Pos.rel (o : Pos) (mirror : Bool) (u v w : ℤ) : Pos :=
  ⟨o.x + (if mirror then -u else u), o.y + v, o.z + w⟩

/-- A lever on the south side of a block. -/
def lever (on : Bool) : Block := .lever ⟨.wall, .south, on⟩

/-- The cell with both inputs off, at rest, without the block `L` under the dust `S`. An input
that is a lever (`leverA`, `leverB`) has the lever in the place of the end of the line of dust,
on the south side of the input block, and nothing under it. -/
def cell (o : Pos) (mirror leverA leverB : Bool) : List (Pos × Block) :=
  let put (u v w : ℤ) (b : Block) : Pos × Block := (Pos.rel o mirror u v w, b)
  [ -- the input blocks and their inverters
    put 0 2 0 stone, put 2 2 0 stone, put 0 2 (-1) (torch true), put 2 2 (-1) (torch true),
    -- the dust `D`, the block `N` and the torch `n`
    put 1 1 1 stone, put 1 2 1 (dustEW 0), put 1 1 0 (torch true),
    -- `P` and `Q` with their dust and their torches, and the dust `S`
    put 0 0 0 stone, put 2 0 0 stone, put 0 1 0 (dustEW 15), put 2 1 0 (dustEW 15),
    put 0 0 (-1) (torch false), put 2 0 (-1) (torch false), put 1 0 (-1) (dustEW 0),
    -- the dust `E`, the block `G` and the torch `c`
    put 1 2 (-1) (dustEW 15), put 1 1 (-1) stone, put 1 1 (-2) (torch false) ] ++
  -- the ends of the line of dust, or the levers
  (if leverA then [put 0 2 1 (lever false)] else [put 0 1 1 stone, put 0 2 1 (dustEW 0)]) ++
  (if leverB then [put 2 2 1 (lever false)] else [put 2 1 1 stone, put 2 2 1 (dustEW 0)])

/-- Redstone dust with the given connections. -/
def dust (north east south west : RedstoneSide) (power : Fin 16 := 0) : Block :=
  .redstoneWire ⟨east, north, power, south, west⟩

/-- Redstone dust with the given connections, east and west exchanged in the mirror image. -/
def dustIn (mirror : Bool) (north east south west : RedstoneSide) : Block :=
  if mirror then dust north west south east else dust north east south west

/-- A repeater with the least delay (two game ticks), not powered, that reads the block to its
west and points east. -/
def repeaterEast : Block :=
  .repeater
    { delay := ⟨1, by decide, by decide⟩, facing := .west, locked := false, powered := false }

/-- A repeater with the least delay (two game ticks), not powered, that reads the block to its
east and points west. -/
def repeaterWest : Block :=
  .repeater
    { delay := ⟨1, by decide, by decide⟩, facing := .east, locked := false, powered := false }

/-- One bit of a ripple-carry adder: a full adder of two cells, at rest with all inputs off.

* The first cell, at `o`, takes the bits `a` and `b` from levers. Its dust `S` (their
  exclusive or) lies on a stone block; a repeater east of that block reads it and points into
  the block `A` of the second cell.
* The second cell is three blocks east, three down and one north of the first. Its other
  input is the carry in: a lever in the first bit of an adder (`first`); in the others a
  repeater east of its block `B`, which reads the carry out of the bit before. Its dust `S` is
  the sum, on a lamp.
* The carry out is the OR of the torches `c` of the two cells: a line of five dust that starts
  north of the torch of the first cell, comes down three steps (one to the north, two to the
  east) and ends north of the torch of the second. In the last bit of an adder (`last`) the
  block under that end is a lamp; in the others the line goes one piece of dust further north,
  to where the repeater of the next bit reads it.

The positions, as `(east, up, south)` from `o`, mirrored in `x` when `mirror` is set:

| what | where |
|---|---|
| first cell, with the levers `a` at `(0, 2, 1)` and `b` at `(2, 2, 1)` | `(0, 0, 0)` |
| stone under its `S`; the repeater, on stone | `(1, -1, -1)`; `(2, -1, -1)` |
| second cell, with the carry lever at `(5, -1, 0)` in a first bit | `(3, -3, -1)` |
| the repeater of the carry in, on stone, in the other bits | `(6, -1, -1)` |
| the sum lamp | `(4, -4, -2)` |
| the carry dust, on stone | `(1, 1, -3)`, `(1, 0, -4)`, `(2, -1, -4)`, `(3, -2, -4)` |
| the end of the carry dust, north of the torch `c` of the second cell | `(4, -2, -4)` |
| the carry lamp of a last bit, under the end of the dust | `(4, -3, -4)` |
| the carry dust to the next bit, on stone | `(4, -2, -5)` |

The next bit of an adder is the mirror image of this one, placed so that its repeater reads
the last piece of carry dust: a bit at `(x, y, z)` is followed by the mirrored bit at
`(x + 11, y - 1, z - 4)`, and that one by a bit at `(x, y - 2, z - 8)`. -/
def adderBit (o : Pos) (mirror first last : Bool) : List (Pos × Block) :=
  let put (u v w : ℤ) (b : Block) : Pos × Block := (Pos.rel o mirror u v w, b)
  cell o mirror true true ++ cell (Pos.rel o mirror 3 (-3) (-1)) mirror false first ++
  [ -- the sum of the first cell, and the repeater that takes it to the second
    put 1 (-1) (-1) stone, put 2 (-2) (-1) stone,
    put 2 (-1) (-1) (if mirror then repeaterWest else repeaterEast),
    -- the sum
    put 4 (-4) (-2) (lamp false),
    -- the carry: from the torch `c` of the first cell down to the torch `c` of the second
    put 1 0 (-3) stone, put 1 1 (-3) (dustIn mirror .side .none .side .none),
    put 1 (-1) (-4) stone, put 1 0 (-4) (dustIn mirror .none .side .up .none),
    put 2 (-2) (-4) stone, put 2 (-1) (-4) (dustIn mirror .none .side .none .up),
    put 3 (-3) (-4) stone, put 3 (-2) (-4) (dustIn mirror .none .side .none .up),
    put 4 (-3) (-4) (if last then lamp false else stone),
    put 4 (-2) (-4) (dustIn mirror (if last then .none else .side) .none .side .side) ] ++
  (if first then []
    else [put 6 (-2) (-1) stone,
      put 6 (-1) (-1) (if mirror then repeaterEast else repeaterWest)]) ++
  (if last then []
    else [put 4 (-3) (-5) stone, put 4 (-2) (-5) (dustIn mirror .none .side .side .none)])

/-- The lever of the bit `a` of an adder bit at `o`. -/
def leverA (o : Pos) (mirror : Bool) : Pos := Pos.rel o mirror 0 2 1

/-- The lever of the bit `b` of an adder bit at `o`. -/
def leverB (o : Pos) (mirror : Bool) : Pos := Pos.rel o mirror 2 2 1

/-- The lever of the carry in of an adder bit at `o` that is the first of its adder. -/
def leverCarry (o : Pos) (mirror : Bool) : Pos := Pos.rel o mirror 5 (-1) 0

/-- The lamp of the sum of an adder bit at `o`. -/
def sumLamp (o : Pos) (mirror : Bool) : Pos := Pos.rel o mirror 4 (-4) (-2)

/-- The lamp of the carry out of an adder bit at `o` that is the last of its adder. -/
def carryLamp (o : Pos) (mirror : Bool) : Pos := Pos.rel o mirror 4 (-3) (-4)

/-- Whether the lamp at `p` is lit. -/
def lampLit (l : Level) (p : Pos) : Bool := l.blockAt p == lamp true

/-- The number a row of lamps shows in binary, the least significant lamp first. -/
def reading (l : Level) : List Pos → ℕ
  | [] => 0
  | p :: ps => (if lampLit l p then 1 else 0) + 2 * reading l ps

theorem lampLit_advance (l : Level) (n : ℕ) (p : Pos) :
    lampLit (l.advance n) p = lampLit l p := rfl

theorem reading_advance (l : Level) (n : ℕ) (ps : List Pos) :
    reading (l.advance n) ps = reading l ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [reading, reading, ih, lampLit_advance]

/-- The number of a list of bits, the least significant first. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBits bs

/-- The inputs that use each lever whose bit is set. -/
def useLevers : List (Pos × Bool) → List Input
  | [] => []
  | (p, b) :: ps => if b then .use p .south :: useLevers ps else useLevers ps

/-- **A run that has come to rest stays there.** If the inputs `is` followed by `k` game ticks
take `l` to a level at rest, then the same inputs followed by `k + m` game ticks end in that
level with its clocks moved on by `m`. This is how a theorem says "from game tick `k` on, for
ever" about a run that `checkpoints` has followed for `k` game ticks. -/
theorem runSchedule_first_of_quiescent {is : List Input} {k : ℕ} {l l' : Level} (hk : 0 < k)
    (h : rules.runSchedule (Schedule.first is k) l = l') (hq : l'.Quiescent) (m : ℕ) :
    rules.runSchedule (Schedule.first is (k + m)) l = l'.advance m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hs : Schedule.first is (j + 1 + m) = Schedule.first is (j + 1) ++ Schedule.idle m := by
    rw [show j + 1 + m = (j + m) + 1 by omega]
    simp only [Schedule.first, Schedule.idle, List.replicate_add, List.cons_append]
  rw [hs, Rules.runSchedule_append, h, Rules.runSchedule_idle_of_quiescent rules hq]

end Redstone.Theorems.Arithmetic
