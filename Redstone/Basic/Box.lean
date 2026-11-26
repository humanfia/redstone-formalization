module

public import Redstone.Basic.Pos

/-!
# Bounding boxes

Axis-aligned boxes of block positions and their volume. The size of a contraption is measured
by the volume of its bounding box, so this is what minimality theorems talk about.
-/

@[expose] public section

namespace Redstone

/-- An axis-aligned box of positions, given by its two corners. Both corners are included. -/
structure Box where
  /-- The corner with the smallest coordinates. -/
  lo : Pos
  /-- The corner with the largest coordinates. -/
  hi : Pos
  deriving DecidableEq, Repr

namespace Box

/-- `b.Contains p` means that `p` lies inside the box `b`. Written `p ∈ b`. -/
def Contains (b : Box) (p : Pos) : Prop :=
  b.lo.x ≤ p.x ∧ p.x ≤ b.hi.x ∧ b.lo.y ≤ p.y ∧ p.y ≤ b.hi.y ∧ b.lo.z ≤ p.z ∧ p.z ≤ b.hi.z

instance : Membership Pos Box := ⟨Contains⟩

instance (b : Box) (p : Pos) : Decidable (b.Contains p) := by
  unfold Contains
  infer_instance

instance (b : Box) (p : Pos) : Decidable (p ∈ b) := inferInstanceAs (Decidable (b.Contains p))

theorem mem_iff {b : Box} {p : Pos} :
    p ∈ b ↔
      b.lo.x ≤ p.x ∧ p.x ≤ b.hi.x ∧ b.lo.y ≤ p.y ∧ p.y ≤ b.hi.y ∧ b.lo.z ≤ p.z ∧ p.z ≤ b.hi.z :=
  Iff.rfl

/-- The number of blocks the box spans along the x axis. Zero if the box is empty. -/
def width (b : Box) : ℕ := (b.hi.x - b.lo.x + 1).toNat

/-- The number of blocks the box spans along the y axis. Zero if the box is empty. -/
def height (b : Box) : ℕ := (b.hi.y - b.lo.y + 1).toNat

/-- The number of blocks the box spans along the z axis. Zero if the box is empty. -/
def depth (b : Box) : ℕ := (b.hi.z - b.lo.z + 1).toNat

/-- The number of positions in the box. -/
def volume (b : Box) : ℕ := b.width * b.height * b.depth

/-- The box that contains only `p`. -/
def single (p : Pos) : Box := ⟨p, p⟩

@[simp]
theorem mem_single {p q : Pos} : q ∈ single p ↔ q = p := by
  rw [mem_iff, Pos.ext_iff]
  simp only [single]
  omega

@[simp]
theorem volume_single (p : Pos) : (single p).volume = 1 := by
  simp [volume, width, height, depth, single]

theorem lo_mem {b : Box} (hx : b.lo.x ≤ b.hi.x) (hy : b.lo.y ≤ b.hi.y) (hz : b.lo.z ≤ b.hi.z) :
    b.lo ∈ b := by
  rw [mem_iff]
  omega

theorem hi_mem {b : Box} (hx : b.lo.x ≤ b.hi.x) (hy : b.lo.y ≤ b.hi.y) (hz : b.lo.z ≤ b.hi.z) :
    b.hi ∈ b := by
  rw [mem_iff]
  omega

/-- A box 7 wide, 8 high and 1 deep has volume 56. -/
example : (Box.mk ⟨0, 0, 0⟩ ⟨6, 7, 0⟩).volume = 56 := by decide

end Box

end Redstone
