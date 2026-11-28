import Redstone.Theorems.Arithmetic.Cell

/-!
# The 2-to-4 line decoder

A 2-to-4 line decoder has two inputs and four outputs, and switches on the one output whose
number the inputs spell in binary. Built from NOR gates it is four of them, one per output:

| output | is on when | its torch | is the NOR of |
|---|---|---|---|
| 0 | neither input is on | `n` | `a` and `b` |
| 1 | only `a` is on | `q` | `b` and output 0 |
| 2 | only `b` is on | `p` | `a` and output 0 |
| 3 | both inputs are on | `c` | the inverted inputs, `nA` and `nB` |

These are the four torches `n`, `q`, `p` and `c` of the torch cell
(`Redstone/Theorems/Arithmetic/Cell.lean`, where the layout is explained). The decoder is the
cell with a lever on each input block and a lamp at each of the four torches:

```
        y = 2      y = 1      y = 0
z = -3  .  .  .    .  3  .    .  .  .  .  .      0, 1, 2, 3: the lamps of the outputs
z = -2  .  .  .    .  c  .    .  .  .  .  .      a, b: the levers, on the south side of the
z = -1  nA E  nB   .  G  .    2  p  S  q  1            blocks A and B
z =  0  A  .  B    XP n  XQ   .  P  .  Q  .      n': a second torch on the block N, on its
z =  1  a  D  b    .  N  .    .  .  .  .  .            south side
z =  2  .  .  .    .  n' .    .  .  .  .  .
z =  3  .  .  .    .  0  .    .  .  .  .  .
    x = 0  1  2    0  1  2   -1  0  1  2  3
```

The dust `S` (the exclusive or of the half adder) lies on a stone block and is not used.

What is proved, about the real rules of the model:

* `decodes`: the truth table. For each of the four inputs, the levers are used on the circuit
  at rest (where lamp 0 is lit), and from game tick 7 on, for ever, exactly the lamp with the
  number `a + 2 b` is lit.
* `lamp_lags`: how the display changes. The new lamp lights in game tick 4, in the very tick
  in which its torch lights. The torch of lamp 0 goes out in game tick 2, and lamp 0 stays lit
  for four game ticks more: a redstone lamp lights at once and goes dark four game ticks after
  its signal is gone (`Redstone/Lemmas/Lamp.lean`). So in game ticks 4 and 5 two lamps are lit.

The level is loaded raw, with both levers off; `circuit_quiescent` shows it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.Decoder

/-- The lever of the input `a`, worth 1. -/
def leverA : Pos := ⟨0, 2, 1⟩

/-- The lever of the input `b`, worth 2. -/
def leverB : Pos := ⟨2, 2, 1⟩

/-- The second torch on the block `N`, which lights lamp 0. -/
def torch0 : Pos := ⟨1, 1, 2⟩

/-- The lamps of the outputs 0, 1, 2 and 3: at the torches `n'`, `q`, `p` and `c`. -/
def outputs : List Pos := [⟨1, 1, 3⟩, ⟨3, 0, -1⟩, ⟨-1, 0, -1⟩, ⟨1, 1, -3⟩]

/-- The decoder, with both levers off and lamp 0 lit. -/
def circuit : Level :=
  .ofCells (cell ⟨0, 0, 0⟩ false true true ++
    [(⟨1, -1, -1⟩, stone), (torch0, .redstoneWallTorch ⟨.south, true⟩),
      (⟨1, 1, 3⟩, lamp true), (⟨3, 0, -1⟩, lamp false), (⟨-1, 0, -1⟩, lamp false),
      (⟨1, 1, -3⟩, lamp false)])

/-- Which of the four lamps are lit. -/
def lit (l : Level) : List Bool := outputs.map (lampLit l)

theorem lit_advance (l : Level) (n : ℕ) : lit (l.advance n) = lit l := rfl

/-- The levers whose input is on are used. -/
def inputs (a b : Bool) : List Input := useLevers [(leverA, a), (leverB, b)]

/-- No lever is used; one game tick. -/
def schedule00 : Schedule := .first (inputs false false) 1

/-- The lever `a` is used before game tick 1; seven game ticks. -/
def schedule10 : Schedule := .first (inputs true false) 7

/-- The lever `b` is used before game tick 1; seven game ticks. -/
def schedule01 : Schedule := .first (inputs false true) 7

/-- Both levers are used before game tick 1; seven game ticks. -/
def schedule11 : Schedule := .first (inputs true true) 7

checkpoints run00 := schedule00 from circuit
checkpoints run10 := schedule10 from circuit
checkpoints run01 := schedule01 from circuit
checkpoints run11 := schedule11 from circuit

/-- The circuit as built is at rest, with lamp 0 lit and the others dark. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧
      circuit.blocksAt outputs = [lamp true, lamp false, lamp false, lamp false] := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- What the truth table says about the inputs `a` and `b`: from game tick 7 on exactly the
lamp with the number `a + 2 b` is lit, and the model has reached no bound. -/
def Decodes (a b : Bool) (n : ℕ) : Prop :=
  lit (rules.runSchedule (.first (inputs a b) (7 + n)) circuit) =
      [!a && !b, a && !b, !a && b, a && b] ∧
    (rules.runSchedule (.first (inputs a b) (7 + n)) circuit).overflow = false

theorem decodes00 (n : ℕ) : Decodes false false n := by
  have h := runSchedule_first_of_quiescent (m := 6 + n) (by decide) run00_run (by circuit_decide)
  unfold Decodes
  rw [show 7 + n = 1 + (6 + n) by omega, h, lit_advance, Level.overflow_advance]
  circuit_decide

theorem decodes10 (n : ℕ) : Decodes true false n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run10_run (by circuit_decide)
  unfold Decodes
  rw [h, lit_advance, Level.overflow_advance]
  circuit_decide

theorem decodes01 (n : ℕ) : Decodes false true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run01_run (by circuit_decide)
  unfold Decodes
  rw [h, lit_advance, Level.overflow_advance]
  circuit_decide

theorem decodes11 (n : ℕ) : Decodes true true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run11_run (by circuit_decide)
  unfold Decodes
  rw [h, lit_advance, Level.overflow_advance]
  circuit_decide

/-- **The truth table of the decoder.** Whatever the inputs `a` and `b`: when the levers of
the inputs that are on are used on the circuit at rest, then after seven game ticks, and after
any number of game ticks more, lamp 0 is lit exactly when no input is on, lamp 1 when only `a`
is, lamp 2 when only `b` is, and lamp 3 when both are: one lamp, the one with the number
`a + 2 b`. -/
theorem decodes (a b : Bool) (n : ℕ) :
    lit (rules.runSchedule (.first (inputs a b) (7 + n)) circuit) =
        [!a && !b, a && !b, !a && b, a && b] ∧
      (rules.runSchedule (.first (inputs a b) (7 + n)) circuit).overflow = false := by
  cases a <;> cases b
  exacts [decodes00 n, decodes01 n, decodes10 n, decodes11 n]

assert_standard_axioms decodes

/-- **The new lamp lights at once, the old one goes dark four game ticks late.** The lever `a`
is used before game tick 1. The torch of lamp 0 is lit after game tick 1 and out after game
tick 2. Lamp 1 is dark after game tick 3 and lit after game tick 4. Lamp 0 is still lit after
game tick 5 and dark after game tick 6, four game ticks after its torch went out. -/
theorem lamp_lags :
    (rules.runSchedule (schedule10.take 1) circuit).blockAt torch0 =
        .redstoneWallTorch ⟨.south, true⟩ ∧
      (rules.runSchedule (schedule10.take 2) circuit).blockAt torch0 =
        .redstoneWallTorch ⟨.south, false⟩ ∧
      lit (rules.runSchedule (schedule10.take 2) circuit) = [true, false, false, false] ∧
      lit (rules.runSchedule (schedule10.take 3) circuit) = [true, false, false, false] ∧
      lit (rules.runSchedule (schedule10.take 4) circuit) = [true, true, false, false] ∧
      lit (rules.runSchedule (schedule10.take 5) circuit) = [true, true, false, false] ∧
      lit (rules.runSchedule (schedule10.take 6) circuit) = [false, true, false, false] := by
  rw [run10_run_1, run10_run_2, run10_run_3, run10_run_4, run10_run_5, run10_run_6]
  circuit_decide

assert_standard_axioms lamp_lags

end Redstone.Theorems.Arithmetic.Decoder
