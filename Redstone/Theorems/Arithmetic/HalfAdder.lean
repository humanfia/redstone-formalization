import Redstone.Theorems.Arithmetic.Cell

/-!
# The half adder

One torch cell (`Redstone/Theorems/Arithmetic/Cell.lean`, where the layout is explained) with
a lever on each input block, a lamp under the dust `S` and a lamp north of the torch `c`:

```
        y = 2      y = 1      y = 0      y = -1
z = -3  .  .  .    .  C  .    .  .  .    .  .  .       C: the carry lamp
z = -2  .  .  .    .  c  .    .  .  .    .  .  .       Σ: the sum lamp, under the dust S
z = -1  nA E  nB   .  G  .    p  S  q    .  Σ  .       a, b: the levers, on the south side of
z =  0  A  .  B    XP n  XQ   P  .  Q    .  .  .             the blocks A and B
z =  1  a  D  b    .  N  .    .  .  .    .  .  .
    x = 0  1  2
```

Three torches make the exclusive or (`n`, the NOR of the inputs; `p` and `q`, each the NOR of
one input and `n`; the dust `S` joins `p` and `q`), and three make the conjunction (`nA` and
`nB` invert the inputs, `c` is the NOR of the two). So the sum lamp is lit when exactly one
lever is on, and the carry lamp when both are: the two lamps show `a + b` in binary.

What is proved, about the real rules of the model:

* `adds`: the truth table. For each of the four inputs, the levers are used on the circuit at
  rest, and from game tick 5 on, for ever, the sum lamp shows `a xor b` and the carry lamp
  `a and b`.
* `delay`: a lamp that goes on does so in game tick 4 and not before, two redstone ticks
  after the levers: each output is two torches away from the inputs.
* `walk`: the levers are used one at a time, `a`, `b`, `a`, `b`, ten game ticks apart, so the
  inputs go through 1 + 0, 1 + 1, 0 + 1 and back to 0 + 0. Ten game ticks after each change
  the circuit is at rest and shows the sum, and at the end its blocks are those it started
  with. This is the only place in this directory where an input changes on a circuit that is
  not in its zero state.

The level is loaded raw, with both levers off; `circuit_quiescent` shows it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.HalfAdder

/-- The lever of the input `a`. -/
def leverA : Pos := ⟨0, 2, 1⟩

/-- The lever of the input `b`. -/
def leverB : Pos := ⟨2, 2, 1⟩

/-- The lamp of the sum, under the dust `S`. -/
def sumLamp : Pos := ⟨1, -1, -1⟩

/-- The lamp of the carry, north of the torch `c`. -/
def carryLamp : Pos := ⟨1, 1, -3⟩

/-- The half adder, with both levers off. -/
def circuit : Level :=
  .ofCells (cell ⟨0, 0, 0⟩ false true true ++ [(sumLamp, lamp false), (carryLamp, lamp false)])

/-- The levers whose input is on are used. -/
def inputs (a b : Bool) : List Input := useLevers [(leverA, a), (leverB, b)]

/-- No lever is used; one game tick. -/
def schedule00 : Schedule := .first (inputs false false) 1

/-- The lever `a` is used before game tick 1; five game ticks. -/
def schedule10 : Schedule := .first (inputs true false) 5

/-- The lever `b` is used before game tick 1; five game ticks. -/
def schedule01 : Schedule := .first (inputs false true) 5

/-- Both levers are used before game tick 1; five game ticks. -/
def schedule11 : Schedule := .first (inputs true true) 5

checkpoints run00 := schedule00 from circuit
checkpoints run10 := schedule10 from circuit
checkpoints run01 := schedule01 from circuit
checkpoints run11 := schedule11 from circuit

/-- The circuit as built is at rest, with both lamps dark. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ circuit.blocksAt [sumLamp, carryLamp] = [lamp false, lamp false] := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- What the truth table says about the inputs `a` and `b`: from game tick 5 on the sum lamp
shows `a xor b`, the carry lamp `a and b`, and the model has reached no bound. -/
def Adds (a b : Bool) (n : ℕ) : Prop :=
  lampLit (rules.runSchedule (.first (inputs a b) (5 + n)) circuit) sumLamp = (a != b) ∧
    lampLit (rules.runSchedule (.first (inputs a b) (5 + n)) circuit) carryLamp = (a && b) ∧
    (rules.runSchedule (.first (inputs a b) (5 + n)) circuit).overflow = false

theorem adds00 (n : ℕ) : Adds false false n := by
  have h := runSchedule_first_of_quiescent (m := 4 + n) (by decide) run00_run (by circuit_decide)
  unfold Adds
  rw [show 5 + n = 1 + (4 + n) by omega, h, lampLit_advance, lampLit_advance,
    Level.overflow_advance]
  circuit_decide

theorem adds10 (n : ℕ) : Adds true false n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run10_run (by circuit_decide)
  unfold Adds
  rw [h, lampLit_advance, lampLit_advance, Level.overflow_advance]
  circuit_decide

theorem adds01 (n : ℕ) : Adds false true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run01_run (by circuit_decide)
  unfold Adds
  rw [h, lampLit_advance, lampLit_advance, Level.overflow_advance]
  circuit_decide

theorem adds11 (n : ℕ) : Adds true true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run11_run (by circuit_decide)
  unfold Adds
  rw [h, lampLit_advance, lampLit_advance, Level.overflow_advance]
  circuit_decide

/-- **The truth table of the half adder.** Whatever the inputs `a` and `b`: when the levers of
the inputs that are on are used on the circuit at rest, then after five game ticks, and after
any number of game ticks more, the sum lamp is lit exactly when one of the inputs is on and the
carry lamp exactly when both are. -/
theorem adds (a b : Bool) (n : ℕ) :
    lampLit (rules.runSchedule (.first (inputs a b) (5 + n)) circuit) sumLamp = (a != b) ∧
      lampLit (rules.runSchedule (.first (inputs a b) (5 + n)) circuit) carryLamp = (a && b) ∧
      (rules.runSchedule (.first (inputs a b) (5 + n)) circuit).overflow = false := by
  cases a <;> cases b
  exacts [adds00 n, adds01 n, adds10 n, adds11 n]

assert_standard_axioms adds

/-- The two lamps as a number: the sum lamp is worth 1, the carry lamp 2. -/
def lamps : List Pos := [sumLamp, carryLamp]

/-- **The delay is four game ticks.** After game tick 3 both lamps are still dark, whatever
the levers; after game tick 4 they show the sum. -/
theorem delay :
    reading (rules.runSchedule (schedule10.take 3) circuit) lamps = 0 ∧
      reading (rules.runSchedule (schedule10.take 4) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule01.take 3) circuit) lamps = 0 ∧
      reading (rules.runSchedule (schedule01.take 4) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule11.take 3) circuit) lamps = 0 ∧
      reading (rules.runSchedule (schedule11.take 4) circuit) lamps = 2 := by
  rw [run10_run_3, run10_run_4, run01_run_3, run01_run_4, run11_run_3, run11_run_4]
  circuit_decide

assert_standard_axioms delay

/-- The lever `a` is used before game tick 1, `b` before game tick 11, `a` again before game
tick 21 and `b` again before game tick 31; forty game ticks. -/
def walkSchedule : Schedule :=
  .first [.use leverA .south] 10 ++ .first [.use leverB .south] 10 ++
    .first [.use leverA .south] 10 ++ .first [.use leverB .south] 10

checkpoints step := walkSchedule from circuit

/-- **One lever at a time.** The inputs go from 0 + 0 to 1 + 0, to 1 + 1, to 0 + 1 and back.
Ten game ticks after each change the circuit is at rest and the lamps show the sum: 1, 2, 1
and 0. At the end the blocks are those the circuit started with, and it stays so for ever. -/
theorem walk (n : ℕ) :
    reading (rules.runSchedule (walkSchedule.take 10) circuit) lamps = 1 ∧
      (rules.runSchedule (walkSchedule.take 10) circuit).Quiescent ∧
      reading (rules.runSchedule (walkSchedule.take 20) circuit) lamps = 2 ∧
      (rules.runSchedule (walkSchedule.take 20) circuit).Quiescent ∧
      reading (rules.runSchedule (walkSchedule.take 30) circuit) lamps = 1 ∧
      (rules.runSchedule (walkSchedule.take 30) circuit).Quiescent ∧
      (rules.runSchedule walkSchedule circuit).world = circuit.world ∧
      reading (rules.steps n (rules.runSchedule walkSchedule circuit)) lamps = 0 ∧
      (rules.steps n (rules.runSchedule walkSchedule circuit)).overflow = false := by
  rw [step_run_10, step_run_20, step_run_30, step_run,
    rules.steps_of_quiescent (by circuit_decide), reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms walk

end Redstone.Theorems.Arithmetic.HalfAdder
