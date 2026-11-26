module

public import Mathlib.Tactic

/-!
# Signal strength

Redstone signals carry a strength between 0 and 15.
-/

@[expose] public section

namespace Redstone

/-- A redstone signal strength, from 0 (off) to 15 (full). -/
abbrev Signal := Fin 16

namespace Signal

/-- No signal. -/
def off : Signal := 0

/-- The strongest signal, 15. -/
def full : Signal := 15

/-- A signal is on when its strength is not zero. -/
def IsOn (s : Signal) : Prop := s ≠ 0

instance : DecidablePred IsOn := fun s => by
  unfold IsOn
  infer_instance

@[simp]
theorem not_isOn_off : ¬IsOn off := by decide

@[simp]
theorem isOn_full : IsOn full := by decide

theorem le_full (s : Signal) : s ≤ full := Fin.le_last s

end Signal

end Redstone
