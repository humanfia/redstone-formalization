module

public import Redstone.Component.Comparator

/-!
# Lemmas about the comparator

Generic facts about the comparator, over an arbitrary level; the theorems about concrete
circuits are in `Redstone/Theorems/Analog`.

* **The formula.** `Comparator.output mode input side` is the closed form of what a comparator
  emits: in compare mode the input if the side input is not stronger and nothing otherwise, in
  subtract mode the input less the side input, never below zero. It is the same as the game's
  own case distinction (`output_eq_game`), for all natural numbers and so for all
  16 × 16 × 2 combinations of signals. `calculateOutputSignal_eq` says that
  `ComparatorBlock.calculateOutputSignal` computes `output` of the two signals the comparator
  reads, on any level, and reads only; `shouldTurnOn_eq` that the comparator wants to be on
  exactly when that output is not zero.
* **Reading only.** The input, the side input, the output and `shouldTurnOn` leave the level
  as it is (`inputSignal_eq`, `alternateSignal_eq`, ...); the values they return are named
  `input`, `side`, `controlInput`.
* **The side input rule** (`SignalGetter.getControlInputSignal`): a block of redstone counts
  15, redstone dust its power, a signal source its *direct* signal towards the comparator (a
  repeater or comparator that points at the side; a redstone torch at the side gives none,
  its direct signal goes up only), and every other block nothing, however strongly it is
  powered
  (`controlInput_redstone_block`, `controlInput_wire`, `controlInput_of_not_source`,
  `controlInput_of_source`). The side input is the stronger of the two sides (`side_eq`).
* **What it reads at the back** (`input_of_analog`, `input_through_conductor`,
  `input_of_full`, `input_of_not_conductor`, `input_of_plain`): the measure of a block that
  can be measured; through one conductor that gives less than 15, the measure of the block
  behind it; otherwise the redstone signal, or the power of dust if that is more.
* **The delay is two game ticks.** `checkTickOnNeighbor_schedules`: a comparator whose stored
  output or whose `powered` property is out of date, with no tick of its own waiting,
  schedules exactly one tick two game ticks ahead and changes nothing else;
  `checkTickOnNeighbor_of_agrees`: one that is up to date does nothing.
* **Attribute lemmas**: the comparator gives its stored output to the block in front of it
  while it is powered, and nothing to any other side (`signal_comparator`).

## What is not proved here

* `refreshOutputState` (the scheduled tick) over an arbitrary level: it stores the new output
  in the block entity, and then, through `Level.setBlock` and `updateNeighborsInFront`, runs
  the reactions of every block around; what they do depends on the whole level. Its first
  half is `calculateOutputSignal_eq`; the whole tick is checked on concrete circuits
  (`Redstone/Theorems/Analog/CompareSubtract.lean` and the files next to it).
* "The output follows the input two game ticks later" over an arbitrary level, for the same
  reason as for the repeater (`Redstone/Lemmas/Repeater.lean`).
-/

@[expose] public section

namespace Redstone.Component.Comparator

/-! ### The formula -/

/-- What a comparator emits when it reads `input` at its back and `side` at its sides: in
compare mode the input, unless the side is stronger; in subtract mode the input less the side
(subtraction of natural numbers: never below zero). -/
def output (mode : ComparatorMode) (input side : ℕ) : ℕ :=
  match mode with
  | .compare => if side ≤ input then input else 0
  | .subtract => input - side

/-- Compare mode: the rear input if it is at least the side input, and nothing otherwise. -/
theorem output_compare (input side : ℕ) :
    output .compare input side = if side ≤ input then input else 0 := rfl

/-- Subtract mode: the rear input less the side input, never below zero. -/
theorem output_subtract (input side : ℕ) : output .subtract input side = input - side := rfl

/-- The closed form is the game's case distinction (`ComparatorBlock.calculateOutputSignal`):
nothing without an input, nothing if the side input is stronger, otherwise the input, less the
side input in subtract mode. -/
theorem output_eq_game (mode : ComparatorMode) (input side : ℕ) :
    output mode input side =
      if input = 0 then 0 else if side > input then 0
      else if mode = .subtract then input - side else input := by
  cases mode <;> simp only [output, reduceCtorEq, ↓reduceIte] <;> split_ifs <;> omega

/-- A comparator never emits more than it reads at its back. -/
theorem output_le (mode : ComparatorMode) (input side : ℕ) : output mode input side ≤ input := by
  cases mode <;> simp only [output] <;> (try split_ifs) <;> omega

/-- With nothing at its sides a comparator passes its input on unchanged, in both modes. -/
@[simp]
theorem output_side_zero (mode : ComparatorMode) (input : ℕ) : output mode input 0 = input := by
  cases mode <;> simp [output]

/-- Without an input a comparator emits nothing. -/
@[simp]
theorem output_input_zero (mode : ComparatorMode) (side : ℕ) : output mode 0 side = 0 := by
  cases mode <;> simp [output]

/-- A side input stronger than the input switches the comparator off, in both modes. -/
theorem output_of_lt (mode : ComparatorMode) {input side : ℕ} (h : input < side) :
    output mode input side = 0 := by
  cases mode <;> simp only [output] <;> (try split_ifs) <;> omega

/-- Equal inputs: compare mode passes the input, subtract mode gives nothing. This is the one
case in which the two modes differ in whether the comparator is on. -/
theorem output_self (mode : ComparatorMode) (input : ℕ) :
    output mode input input = if mode = .compare then input else 0 := by
  cases mode <;> simp [output]

/-- The comparator emits something exactly when there is an input and the side input is
weaker, or equal in compare mode: the condition of `ComparatorBlock.shouldTurnOn`. -/
theorem output_ne_zero_iff (mode : ComparatorMode) (input side : ℕ) :
    output mode input side ≠ 0 ↔
      input ≠ 0 ∧ (side < input ∨ (input = side ∧ mode = .compare)) := by
  cases mode <;> simp only [output, reduceCtorEq, and_true, and_false, or_false] <;>
    (try split_ifs) <;> omega

/-- The analog inverter: a subtract comparator with a full signal at its back turns a side
input `s` into `15 - s`, and doing it twice gives `s` back. -/
theorem output_subtract_invert {s : ℕ} (h : s ≤ 15) :
    output .subtract 15 (output .subtract 15 s) = s := by
  simp only [output]
  omega

/-- Signals stay signals: an input of at most 15 gives an output of at most 15. -/
theorem output_le_fifteen (mode : ComparatorMode) {input : ℕ} (side : ℕ) (h : input ≤ 15) :
    output mode input side ≤ 15 :=
  (output_le mode input side).trans h

/-! ### What the comparator reads, as functions of the level -/

/-- The value of `DiodeBlock.getInputSignal` for the comparator `s` at `p` in the level `l`: the
redstone signal the block behind gives, or the power of the redstone dust there if that is
more. -/
def diodeInput (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) : ℕ :=
  if l.signalAt env (p.step (facing s)) (facing s) ≥ 15 then
    l.signalAt env (p.step (facing s)) (facing s)
  else max (l.signalAt env (p.step (facing s)) (facing s))
    (wirePower (l.blockAt (p.step (facing s))))

/-- The value of `ComparatorBlock.getInputSignal`: what the comparator `s` at `p` reads at its
back in the level `l`. The measure of the block behind if it has one; behind a conductor that
gives less than 15, the measure of the block after it if that has one; otherwise
`diodeInput`. -/
def input (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) : ℕ :=
  if (l.blockAt (p.step (facing s))).attrs.analog then
    (env.block (l.blockAt (p.step (facing s)))).analogSignal l (p.step (facing s))
      (facing s).opposite
  else if diodeInput s p env l < 15 && (l.blockAt (p.step (facing s))).isConductor then
    if (l.blockAt ((p.step (facing s)).step (facing s))).attrs.analog then
      (env.block (l.blockAt ((p.step (facing s)).step (facing s)))).analogSignal l
        ((p.step (facing s)).step (facing s)) (facing s).opposite
    else diodeInput s p env l
  else diodeInput s p env l

/-- The value of `SignalGetter.getControlInputSignal(q, d, false)`: what the block at `q` gives
to the side of a diode. `d` points from the diode to `q`. -/
def controlInput (q : Pos) (d : Direction) (env : Env) (l : Level) : ℕ :=
  if (l.blockAt q).is .redstone_block then 15
  else if (l.blockAt q).is .redstone_wire then wirePower (l.blockAt q)
  else if (l.blockAt q).attrs.signalSource then l.directSignalAt env q d
  else 0

/-- The value of `DiodeBlock.getAlternateSignal`: the side input of the comparator `s` at `p`
in the level `l`. -/
def side (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) : ℕ :=
  max (controlInput (p.step (clockWise (facing s))) (clockWise (facing s)) env l)
    (controlInput (p.step (counterClockWise (facing s))) (counterClockWise (facing s)) env l)

/-! ### Reading leaves the level as it is -/

/-- Unfolds the monad of a computation that only reads, with the given lemmas about the
computations it calls, and splits its case distinctions. -/
local syntax "read_only" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| read_only [$ls,*]) =>
    `(tactic| repeat (first
      | rfl
      | simp only [bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure, StateT.pure, get, getThe,
          MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, read, readThe,
          MonadReaderOf.read, ReaderT.read, Level.getSignal, Level.getDirectSignal,
          Level.getBlock, Level.behaviour, $ls,*]
      | split
      | contradiction))

/-- `DiodeBlock.getInputSignal` only reads the level, and returns `diodeInput`. -/
theorem diodeInputSignal_eq (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) :
    diodeInputSignal s p env l = (diodeInput s p env l, l) := by
  unfold diodeInput diodeInputSignal
  read_only []

/-- `SignalGetter.getControlInputSignal` only reads the level, and returns `controlInput`. -/
theorem controlInputSignal_eq (q : Pos) (d : Direction) (env : Env) (l : Level) :
    controlInputSignal q d env l = (controlInput q d env l, l) := by
  unfold controlInput controlInputSignal
  read_only []

/-- `DiodeBlock.getAlternateSignal` only reads the level, and returns `side`. -/
theorem alternateSignal_eq (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) :
    alternateSignal s p env l = (side s p env l, l) := by
  unfold side alternateSignal
  read_only [controlInputSignal_eq]

/-- `ComparatorBlock.getInputSignal` only reads the level, and returns `input`. -/
theorem inputSignal_eq (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) :
    inputSignal s p env l = (input s p env l, l) := by
  unfold input inputSignal
  read_only [diodeInputSignal_eq]

/-! ### The side input rule -/

/-- A block of redstone at the side counts as 15. -/
theorem controlInput_redstone_block (q : Pos) (d : Direction) (env : Env) (l : Level)
    (h : (l.blockAt q).is .redstone_block = true) : controlInput q d env l = 15 := by
  simp [controlInput, h]

/-- Redstone dust at the side counts with its power, whatever its shape: it need not point at
the comparator. -/
theorem controlInput_wire (q : Pos) (d : Direction) (env : Env) (l : Level)
    (w : Blocks.RedstoneWire) (h : l.blockAt q = .redstoneWire w) :
    controlInput q d env l = w.power.val := by
  have h₁ : (Block.redstoneWire w).is .redstone_block = false := rfl
  have h₂ : (Block.redstoneWire w).is .redstone_wire = true := rfl
  simp [controlInput, h, h₁, h₂, wirePower]

/-- **Only signal sources count at the side.** A block that is not a block of redstone, not
redstone dust and not a signal source gives nothing to the side of a comparator, whatever
power it receives itself: a powered solid block or a lit lamp at the side is not a side
input. -/
theorem controlInput_of_not_source (q : Pos) (d : Direction) (env : Env) (l : Level)
    (h₁ : (l.blockAt q).is .redstone_block = false) (h₂ : (l.blockAt q).is .redstone_wire = false)
    (h₃ : (l.blockAt q).attrs.signalSource = false) : controlInput q d env l = 0 := by
  simp [controlInput, h₁, h₂, h₃]

/-- A signal source at the side other than dust and the block of redstone counts with its
*direct* signal towards the comparator: a repeater or a comparator counts when it points at the
side, and then with its output. -/
theorem controlInput_of_source (q : Pos) (d : Direction) (env : Env) (l : Level)
    (h₁ : (l.blockAt q).is .redstone_block = false) (h₂ : (l.blockAt q).is .redstone_wire = false)
    (h₃ : (l.blockAt q).attrs.signalSource = true) :
    controlInput q d env l = l.directSignalAt env q d := by
  simp [controlInput, h₁, h₂, h₃]

/-- The side input is the stronger of the two sides. -/
theorem side_eq (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) :
    side s p env l =
      max (controlInput (p.step (clockWise (facing s))) (clockWise (facing s)) env l)
        (controlInput (p.step (counterClockWise (facing s))) (counterClockWise (facing s)) env l) :=
  rfl

/-- With nothing that counts at either side, there is no side input. -/
theorem side_eq_zero (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (h₁ : controlInput (p.step (clockWise (facing s))) (clockWise (facing s)) env l = 0)
    (h₂ : controlInput (p.step (counterClockWise (facing s))) (counterClockWise (facing s)) env l
      = 0) : side s p env l = 0 := by
  simp [side, h₁, h₂]

/-! ### What the comparator reads at its back -/

/-- **A block that can be measured is measured.** If the block behind the comparator has an
analog output (a container, a cake, a composter, ...), the input is that measure, and the
redstone signal of the block is ignored. -/
theorem input_of_analog (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (h : (l.blockAt (p.step (facing s))).attrs.analog = true) :
    input s p env l =
      (env.block (l.blockAt (p.step (facing s)))).analogSignal l (p.step (facing s))
        (facing s).opposite := by
  simp [input, h]

/-- **Through one conductor.** If the block behind the comparator cannot be measured, is a
conductor and gives less than 15, and the block behind it can be measured, the input is the
measure of that second block. -/
theorem input_through_conductor (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (h₁ : (l.blockAt (p.step (facing s))).attrs.analog = false)
    (h₂ : diodeInput s p env l < 15)
    (h₃ : (l.blockAt (p.step (facing s))).isConductor = true)
    (h₄ : (l.blockAt ((p.step (facing s)).step (facing s))).attrs.analog = true) :
    input s p env l =
      (env.block (l.blockAt ((p.step (facing s)).step (facing s)))).analogSignal l
        ((p.step (facing s)).step (facing s)) (facing s).opposite := by
  simp [input, h₁, h₂, h₃, h₄]

/-- **A full signal is not looked through.** If the block behind the comparator cannot be
measured and gives 15 or more, the input is that signal, whatever stands behind the block. -/
theorem input_of_full (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (h₁ : (l.blockAt (p.step (facing s))).attrs.analog = false)
    (h₂ : 15 ≤ diodeInput s p env l) : input s p env l = diodeInput s p env l := by
  simp [input, h₁, Nat.not_lt.mpr h₂]

/-- **Only a conductor is looked through.** If the block behind the comparator cannot be
measured and is not a conductor (air, glass, dust, another comparator), the input is the
redstone signal, whatever stands behind the block. -/
theorem input_of_not_conductor (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (h₁ : (l.blockAt (p.step (facing s))).attrs.analog = false)
    (h₂ : (l.blockAt (p.step (facing s))).isConductor = false) :
    input s p env l = diodeInput s p env l := by
  simp [input, h₁, h₂]

/-- If neither the block behind the comparator can be measured nor the block after it, the
input is the redstone signal (`diodeInput`). -/
theorem input_of_plain (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (h₁ : (l.blockAt (p.step (facing s))).attrs.analog = false)
    (h₂ : (l.blockAt ((p.step (facing s)).step (facing s))).attrs.analog = false) :
    input s p env l = diodeInput s p env l := by
  simp [input, h₁, h₂]

/-! ### The output and `shouldTurnOn` -/

/-- **The comparator computes `output`.** On any level, `ComparatorBlock.calculateOutputSignal`
returns `output mode input side` for the input and the side input the comparator reads, and
leaves the level as it is. With `output_compare` and `output_subtract` this is the formula of
the comparator for every combination of signals. -/
theorem calculateOutputSignal_eq (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) :
    calculateOutputSignal s p env l = (output s.mode (input s p env l) (side s p env l), l) := by
  rw [output_eq_game]
  unfold calculateOutputSignal
  read_only [inputSignal_eq, alternateSignal_eq]

/-- The case distinction of `ComparatorBlock.shouldTurnOn` says whether `output` is positive. -/
theorem turnsOn_eq (mode : ComparatorMode) (input side : ℕ) :
    (if input = 0 then false
      else if input > side then true else decide (input = side) && decide (mode = .compare)) =
      decide (output mode input side ≠ 0) := by
  have key := output_ne_zero_iff mode input side
  by_cases h : output mode input side ≠ 0
  · obtain ⟨h0, h1⟩ := key.mp h
    rcases h1 with h1 | ⟨h1, h2⟩
    · simp [h, h0, h1]
    · subst h1 h2
      simp [h, h0]
  · have h' := mt key.mpr h
    by_cases h0 : input = 0
    · simp [h0]
    · have h1 : ¬ side < input := fun hlt => h' ⟨h0, .inl hlt⟩
      have h2 : ¬ (input = side ∧ mode = .compare) := fun hh => h' ⟨h0, .inr hh⟩
      simp only [h, h0, h1, ↓reduceIte, decide_false, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      tauto

/-- **The comparator is on exactly when its output is not zero.** `ComparatorBlock.shouldTurnOn`
only reads the level, and says whether `output mode input side` is positive. -/
theorem shouldTurnOn_eq (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) :
    shouldTurnOn s p env l =
      (decide (output s.mode (input s p env l) (side s p env l) ≠ 0), l) := by
  rw [← turnsOn_eq]
  unfold shouldTurnOn
  read_only [inputSignal_eq, alternateSignal_eq]

/-! ### Attribute lemmas -/

/-- A comparator gives a signal only to the block in front of it (the direction `d` points from
that block back to the comparator, which is the comparator's `facing`): its stored output while
it is powered. -/
theorem signal_comparator (s : Blocks.Comparator) (l : Level) (p : Pos) (d : Direction) :
    (comparator s).signal l p d =
      if s.facing.toDirection = d ∧ s.powered = true then outputSignal l p else 0 := by
  change (if s.facing.toDirection = d then (if s.powered then outputSignal l p else 0) else 0) = _
  by_cases h : s.facing.toDirection = d <;> by_cases h' : s.powered = true <;> simp [h, h']

/-- The direct signal of a comparator is its signal: what stands in front of a comparator is
powered strongly, and a comparator that points at the side of another one is a side input. -/
theorem directSignal_comparator (s : Blocks.Comparator) :
    (comparator s).directSignal = (comparator s).signal := rfl

/-- A comparator that is not powered gives no signal. -/
theorem signal_comparator_of_unpowered (s : Blocks.Comparator) (l : Level) (p : Pos)
    (d : Direction) (h : s.powered = false) : (comparator s).signal l p d = 0 := by
  simp [signal_comparator, h]

/-! ### The delay -/

/-- The value of `DiodeBlock.shouldPrioritize`: the block in front of the comparator is a
repeater or a comparator that does not face it. -/
def prioritize (s : Blocks.Comparator) (p : Pos) (l : Level) : Bool :=
  (diodeFacing? (l.blockAt (p.step (facing s).opposite))).any (· ≠ (facing s).opposite)

/-- `DiodeBlock.shouldPrioritize` only reads the level, and returns `prioritize`. -/
theorem shouldPrioritize_eq (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level) :
    shouldPrioritize s p env l = (prioritize s p l, l) := by
  unfold shouldPrioritize prioritize
  read_only []

/-- The priority with which `checkTickOnNeighbor` schedules the tick of the comparator: `high`
in front of a diode that does not face it, `normal` otherwise. -/
def tickPriority (s : Blocks.Comparator) (p : Pos) (l : Level) : TickPriority :=
  if prioritize s p l then .high else .normal

/-- **The delay of a comparator is two game ticks.** Let no tick of the comparator at `p` be
collected for the current game tick or waiting, and let the comparator be out of date: the
output stored in its block entity is not `output mode input side`, or its `powered` property
is not whether that output is positive. Then a neighbour update makes it schedule exactly one
tick, due two game ticks after the current game time, and changes nothing else in the level
but the counter that orders the ticks. That tick is what changes the output
(`refreshOutputState`). -/
theorem checkTickOnNeighbor_schedules (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (hwill : l.willTickThisTick p .comparator = false)
    (hsched : l.hasScheduledTick p .comparator = false)
    (hne : output s.mode (input s p env l) (side s p env l) ≠ outputSignal l p ∨
      s.powered ≠ decide (output s.mode (input s p env l) (side s p env l) ≠ 0)) :
    checkTickOnNeighbor s p env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++
          [⟨p, .comparator, l.gameTime + 2, tickPriority s p l, l.subTickCount⟩] }) := by
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p
      .comparator = false := hsched
  have hne' : (output s.mode (input s p env l) (side s p env l) != outputSignal l p ||
      s.powered != decide (output s.mode (input s p env l) (side s p env l) ≠ 0)) = true := by
    rcases hne with h | h
    · simp [h]
    · simp only [Bool.or_eq_true, bne_iff_ne]
      exact .inr h
  unfold checkTickOnNeighbor tickPriority
  read_only [calculateOutputSignal_eq, shouldTurnOn_eq, shouldPrioritize_eq, Level.scheduleTick,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, hwill, hne', hsched',
    Bool.not_false, Bool.false_eq_true, ↓reduceIte]

/-- **A comparator that is up to date does nothing**: if the stored output is
`output mode input side` and `powered` says whether it is positive, a neighbour update leaves
the level as it is. -/
theorem checkTickOnNeighbor_of_agrees (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (hout : output s.mode (input s p env l) (side s p env l) = outputSignal l p)
    (hon : s.powered = decide (output s.mode (input s p env l) (side s p env l) ≠ 0)) :
    checkTickOnNeighbor s p env l = ((), l) := by
  have h : (output s.mode (input s p env l) (side s p env l) != outputSignal l p ||
      s.powered != decide (output s.mode (input s p env l) (side s p env l) ≠ 0)) = false := by
    rw [← hon, hout]
    simp
  unfold checkTickOnNeighbor
  read_only [calculateOutputSignal_eq, shouldTurnOn_eq, h, Bool.false_eq_true, ↓reduceIte]

/-- While a tick of the comparator is still to run in the current game tick, a neighbour
update does nothing: the tick that is about to run will read the inputs itself. -/
theorem checkTickOnNeighbor_of_willTick (s : Blocks.Comparator) (p : Pos) (env : Env) (l : Level)
    (hwill : l.willTickThisTick p .comparator = true) :
    checkTickOnNeighbor s p env l = ((), l) := by
  unfold checkTickOnNeighbor
  read_only [hwill, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

end Redstone.Component.Comparator
