import Redstone.Component.AnalogSource
import Redstone.Lemmas.ContainerSignal
import Redstone.Proof.Axioms

/-!
# The signals of the blocks a comparator measures, in closed form

Generic facts about the analog sources that are not containers: what a comparator reads from
each of them (`getAnalogOutputSignal`), as a formula in the block state or the block entity,
on any level. The theorems about concrete circuits are in `Redstone/Theorems/Analog`; the
signal of a container is in `Redstone/Lemmas/ContainerSignal.lean`.

* **Block state alone** (the level and the position do not matter): a cake gives
  `(7 - bites) * 2`, so 14, 12, ..., 2 (`analogSignal_cake`, `analogSignal_cake_mem`); a
  composter its level 0..8 (`analogSignal_composter`); a water or powder snow cauldron its
  level 1..3, a lava cauldron 3 and an empty cauldron 0 (`analogSignal_layeredCauldron`, ...);
  an end portal frame 15 with an eye and 0 without (`analogSignal_endPortalFrame`); a respawn
  anchor `charges * 15 / 4`, which is 0, 3, 7, 11, 15 (`analogSignal_respawnAnchor`,
  `respawnAnchor_table`); a bee nest or beehive its honey level (`analogSignal_beehive`); a
  copper golem statue, waxed or not, 1 to 4 by its pose (`analogSignal_copperGolemStatue`,
  `analogSignal_weatheringCopperGolemStatue`), and four turns of the pose come back to the
  first (`nextPose_four`).
* **Block entity**: a chiseled bookshelf gives the number of the slot used last, counted from
  one, and 0 before any slot was used (`analogSignal_chiseledBookShelf`,
  `analogSignal_chiseledBookShelf_fresh`); a jukebox the number of its record, which lies
  between 1 and 15 for every record (`analogSignal_jukebox`, `musicDiscs_signal`), and 0
  without a record.
* **Lectern.** The game computes `floor(page / (pageCount - 1.0F) * 14.0F) + 1` in single
  precision. `lecternSignal_eq`: for a book of `m + 1` pages (`m ≥ 1`, at most 262145 pages)
  open at page `k ≤ m`, counted from zero, the signal is `14 * k / m + 1`, with division
  rounding down: the rounding of the `float` arithmetic never matters. So the first page gives
  1 and the last 15 (`lecternSignal_first`, `lecternSignal_last`), and a book of 15 pages gives
  every strength: page `k` gives `k + 1` (`lecternSignal_fifteen_pages`). A book of one page
  gives 15, an empty book and quill 15 too (`lecternSignal_of_pageCount_le_one`); a lectern
  without a book gives 0 (`analogSignal_lectern_of_no_book`).

## What is not proved here

* The decorated pot and the shelf: they are containers in all but name; the pot's signal is
  `Container.redstoneSignal` of one slot (`Redstone/Lemmas/ContainerSignal.lean`).
* The creaking heart, whose signal depends on a walk through the logs around it.
* The copper bulb (15 while lit): its lemmas belong with the flip-flop theorems;
  `Redstone/Theorems/Analog/CopperBulb.lean` reads one with a comparator.
* How these blocks get into their states (eating, composting, charging, turning a page): those
  are reactions that run neighbour updates over the whole level. `Redstone/Theorems/Analog`
  has them on concrete levels.

This file is not a `module`, unlike `Redstone/Lemmas/Repeater.lean`: the page formula of the
lectern needs `Redstone/Lemmas/ContainerSignal.lean`, which is not one either, and the two
facts about the list of records are checked by evaluation.
-/

set_option Elab.async false

namespace Redstone.Component.AnalogSource

/-! ### Sources that are measured by their block state -/

/-- A comparator reads `(7 - bites) * 2` from a cake. -/
theorem analogSignal_cake (s : Blocks.Cake) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.cake s)).analogSignal l p d = (7 - s.bites.val) * 2 := rfl

assert_standard_axioms analogSignal_cake

/-- A cake gives one of 14, 12, 10, 8, 6, 4, 2: a whole cake 14, and two less for each bite. -/
theorem analogSignal_cake_mem (s : Blocks.Cake) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.cake s)).analogSignal l p d ∈ [14, 12, 10, 8, 6, 4, 2] := by
  have h := s.bites.isLt
  rw [analogSignal_cake]
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  omega

assert_standard_axioms analogSignal_cake_mem

/-- A cake with a candle is a whole cake: it gives 14. -/
theorem analogSignal_candleCake (id : Blocks.CandleCake.Id) (s : Blocks.CandleCake) (l : Level)
    (p : Pos) (d : Direction) : (behaviour (.candleCake id s)).analogSignal l p d = 14 := rfl

assert_standard_axioms analogSignal_candleCake

/-- A comparator reads the level of a composter: 0 when empty, 7 when full, 8 when the bone
meal is ready. -/
theorem analogSignal_composter (s : Blocks.Composter) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.composter s)).analogSignal l p d = s.level.val := rfl

assert_standard_axioms analogSignal_composter

/-- The signal of a composter is at most 8. -/
theorem analogSignal_composter_le (s : Blocks.Composter) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.composter s)).analogSignal l p d ≤ 8 := by
  have h := s.level.isLt
  rw [analogSignal_composter]
  omega

assert_standard_axioms analogSignal_composter_le

/-- An empty cauldron gives nothing. -/
theorem analogSignal_cauldron (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.plain .cauldron)).analogSignal l p d = 0 := rfl

assert_standard_axioms analogSignal_cauldron

/-- A lava cauldron gives 3. -/
theorem analogSignal_lavaCauldron (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.plain .lava_cauldron)).analogSignal l p d = 3 := rfl

assert_standard_axioms analogSignal_lavaCauldron

/-- A water or powder snow cauldron gives its level. -/
theorem analogSignal_layeredCauldron (id : Blocks.LayeredCauldron.Id)
    (s : Blocks.LayeredCauldron) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.layeredCauldron id s)).analogSignal l p d = s.level.val := rfl

assert_standard_axioms analogSignal_layeredCauldron

/-- The signal of a water or powder snow cauldron is 1, 2 or 3. -/
theorem analogSignal_layeredCauldron_mem (id : Blocks.LayeredCauldron.Id)
    (s : Blocks.LayeredCauldron) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.layeredCauldron id s)).analogSignal l p d ∈ [1, 2, 3] := by
  have h₁ := s.level.lo_le
  have h₂ := s.level.le_hi
  rw [analogSignal_layeredCauldron]
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  omega

assert_standard_axioms analogSignal_layeredCauldron_mem

/-- An end portal frame gives 15 when it holds an eye and nothing otherwise. -/
theorem analogSignal_endPortalFrame (s : Blocks.EndPortalFrame) (l : Level) (p : Pos)
    (d : Direction) :
    (behaviour (.endPortalFrame s)).analogSignal l p d = if s.eye then 15 else 0 := rfl

assert_standard_axioms analogSignal_endPortalFrame

/-- A respawn anchor gives `charges * 15 / 4`, rounded down. -/
theorem analogSignal_respawnAnchor (s : Blocks.RespawnAnchor) (l : Level) (p : Pos)
    (d : Direction) :
    (behaviour (.respawnAnchor s)).analogSignal l p d = s.charges.val * 15 / 4 := rfl

assert_standard_axioms analogSignal_respawnAnchor

/-- The signals of a respawn anchor with 0, 1, 2, 3 and 4 charges are 0, 3, 7, 11 and 15. -/
theorem respawnAnchor_table :
    (List.finRange 5).map (fun c : Fin 5 => c.val * 15 / 4) = [0, 3, 7, 11, 15] := by decide

assert_standard_axioms respawnAnchor_table

/-- A bee nest or beehive gives its honey level, 0 to 5. -/
theorem analogSignal_beehive (id : Blocks.Beehive.Id) (s : Blocks.Beehive) (l : Level) (p : Pos)
    (d : Direction) : (behaviour (.beehive id s)).analogSignal l p d = s.honey_level.val := rfl

assert_standard_axioms analogSignal_beehive

/-- A copper golem statue gives 1, 2, 3 or 4 by its pose: standing, sitting, running, star. -/
theorem analogSignal_copperGolemStatue (id : Blocks.CopperGolemStatue.Id)
    (s : Blocks.CopperGolemStatue) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.copperGolemStatue id s)).analogSignal l p d = poseSignal s.copper_golem_pose :=
  rfl

assert_standard_axioms analogSignal_copperGolemStatue

/-- A copper golem statue that is not waxed gives the same: 1 to 4 by its pose. -/
theorem analogSignal_weatheringCopperGolemStatue (id : Blocks.WeatheringCopperGolemStatue.Id)
    (s : Blocks.WeatheringCopperGolemStatue) (l : Level) (p : Pos) (d : Direction) :
    (behaviour (.weatheringCopperGolemStatue id s)).analogSignal l p d =
      poseSignal s.copper_golem_pose :=
  rfl

assert_standard_axioms analogSignal_weatheringCopperGolemStatue

/-- Turning a statue to its next pose adds one to its signal, and goes from 4 back to 1. -/
theorem poseSignal_nextPose (pose : Pose) :
    poseSignal (nextPose pose) = if poseSignal pose = 4 then 1 else poseSignal pose + 1 := by
  cases pose <;> rfl

assert_standard_axioms poseSignal_nextPose

/-- Four turns bring a statue back to the pose it had. -/
theorem nextPose_four (pose : Pose) : nextPose (nextPose (nextPose (nextPose pose))) = pose := by
  cases pose <;> rfl

assert_standard_axioms nextPose_four

/-! ### Sources that are measured by their block entity -/

/-- A chiseled bookshelf gives the number of the slot that was used last, counted from one. -/
theorem analogSignal_chiseledBookShelf (s : Blocks.ChiseledBookShelf) (l : Level) (p : Pos)
    (d : Direction) (e : BlockEntities.ChiseledBookshelf)
    (h : l.blockEntities p = some (.chiseledBookshelf e)) :
    (behaviour (.chiseledBookShelf s)).analogSignal l p d = (e.lastInteractedSlot + 1).toNat := by
  change (match l.blockEntities p with
    | some (.chiseledBookshelf d) => (d.lastInteractedSlot + 1).toNat
    | _ => 0) = _
  rw [h]

assert_standard_axioms analogSignal_chiseledBookShelf

/-- A chiseled bookshelf that no book was put into or taken from gives nothing. -/
theorem analogSignal_chiseledBookShelf_fresh (s : Blocks.ChiseledBookShelf) (l : Level) (p : Pos)
    (d : Direction) (h : l.blockEntities p = some (.chiseledBookshelf default)) :
    (behaviour (.chiseledBookShelf s)).analogSignal l p d = 0 := by
  rw [analogSignal_chiseledBookShelf s l p d default h]
  rfl

assert_standard_axioms analogSignal_chiseledBookShelf_fresh

/-- A jukebox gives the `comparator_output` of the song of its record, and nothing when what
it holds has no song. -/
theorem analogSignal_jukebox (s : Blocks.Jukebox) (l : Level) (p : Pos) (d : Direction)
    (e : BlockEntities.Jukebox) (h : l.blockEntities p = some (.jukebox e)) :
    (behaviour (.jukebox s)).analogSignal l p d =
      ((jukeboxSong e.record.item).map Prod.fst).getD 0 := by
  change (match l.blockEntities p with
    | some (.jukebox d) => ((jukeboxSong d.record.item).map Prod.fst).getD 0
    | _ => 0) = _
  rw [h]

assert_standard_axioms analogSignal_jukebox

/-- Every record gives a signal between 1 and 15. -/
theorem musicDiscs_signal : ∀ e ∈ musicDiscs, 1 ≤ e.2.1 ∧ e.2.1 ≤ 15 := by decide +kernel

assert_standard_axioms musicDiscs_signal

/-- Every strength from 1 to 15 is the signal of some record. -/
theorem musicDiscs_all_strengths :
    ∀ n ∈ List.range' 1 15, n ∈ musicDiscs.map (·.2.1) := by decide +kernel

assert_standard_axioms musicDiscs_all_strengths

/-! ### The lectern -/

/-- A comparator reads `lecternSignal` of the block entity from a lectern that shows a book. -/
theorem analogSignal_lectern (s : Blocks.Lectern) (l : Level) (p : Pos) (d : Direction)
    (e : BlockEntities.Lectern) (h : l.blockEntities p = some (.lectern e))
    (hbook : s.has_book = true) :
    (behaviour (.lectern s)).analogSignal l p d = lecternSignal e := by
  change (match l.blockEntities p with
    | some (.lectern d) => if s.has_book then lecternSignal d else 0
    | _ => 0) = _
  rw [h]
  simp [hbook]

assert_standard_axioms analogSignal_lectern

/-- A lectern without a book gives nothing. -/
theorem analogSignal_lectern_of_no_book (s : Blocks.Lectern) (l : Level) (p : Pos)
    (d : Direction) (hbook : s.has_book = false) :
    (behaviour (.lectern s)).analogSignal l p d = 0 := by
  change (match l.blockEntities p with
    | some (.lectern d) => if s.has_book then lecternSignal d else 0
    | _ => 0) = _
  split <;> simp [hbook]

assert_standard_axioms analogSignal_lectern_of_no_book

/-- **The page formula of the lectern.** A book of `m + 1` pages (`m ≥ 1`) open at page `k`,
counted from zero, gives `14 * k / m + 1`, the division rounding down. The game computes this
in single precision; the rounding never changes the result (`F32.lerpDiscrete_div`). -/
theorem lecternSignal_eq (e : BlockEntities.Lectern) (m k : ℕ) (hm : 0 < m) (hm2 : m ≤ 262144)
    (hk : k ≤ m) (hpages : e.book.bind (·.pages) = some (m + 1)) (hpage : e.page = k) :
    lecternSignal e = 14 * k / m + 1 := by
  have hcount : e.pageCount = m + 1 := by simp [BlockEntities.Lectern.pageCount, hpages]
  have hbook : e.hasBook = true := by simp [BlockEntities.Lectern.hasBook, hpages]
  have hgt : e.pageCount > 1 := by omega
  have hden : ((e.pageCount : ℚ) - 1) = (m : ℚ) := by
    rw [hcount]
    push_cast
    ring
  have hnum : ((e.page : ℤ) : ℚ) = (k : ℚ) := by
    rw [hpage]
    push_cast
    rfl
  have key := F32.lerpDiscrete_div k m hm hm2 hk
  have hfloor : ∀ q : ℚ, q.floor = ⌊q⌋ := fun _ => rfl
  unfold lecternSignal
  simp only [roundFloat, hgt, ↓reduceIte, hbook, hden, hnum, hfloor]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [F32.roundFloat_zero]
  · have hq : (0 : ℚ) < (k : ℚ) / m := div_pos (by exact_mod_cast hkpos) (by exact_mod_cast hm)
    have hpos : F32.roundFloat ((k : ℚ) / m) > 0 :=
      lt_of_lt_of_le (mul_pos hq (by norm_num)) (F32.roundFloat_bounds hq).1
    simp only [hpos, hkpos, ↓reduceIte] at key
    omega

assert_standard_axioms lecternSignal_eq

/-- The first page of a book of several pages gives 1. -/
theorem lecternSignal_first (e : BlockEntities.Lectern) (m : ℕ) (hm : 0 < m) (hm2 : m ≤ 262144)
    (hpages : e.book.bind (·.pages) = some (m + 1)) (hpage : e.page = 0) :
    lecternSignal e = 1 := by
  rw [lecternSignal_eq e m 0 hm hm2 (Nat.zero_le m) hpages (by simpa using hpage)]
  simp

assert_standard_axioms lecternSignal_first

/-- The last page of a book of several pages gives 15. -/
theorem lecternSignal_last (e : BlockEntities.Lectern) (m : ℕ) (hm : 0 < m) (hm2 : m ≤ 262144)
    (hpages : e.book.bind (·.pages) = some (m + 1)) (hpage : e.page = m) :
    lecternSignal e = 15 := by
  rw [lecternSignal_eq e m m hm hm2 le_rfl hpages hpage, Nat.mul_div_cancel _ hm]

assert_standard_axioms lecternSignal_last

/-- **A book of fifteen pages gives every strength**: open at page `k` (counted from zero) it
gives `k + 1`. -/
theorem lecternSignal_fifteen_pages (e : BlockEntities.Lectern) (k : ℕ) (hk : k ≤ 14)
    (hpages : e.book.bind (·.pages) = some 15) (hpage : e.page = k) :
    lecternSignal e = k + 1 := by
  rw [lecternSignal_eq e 14 k (by norm_num) (by norm_num) hk hpages hpage,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 14)]

assert_standard_axioms lecternSignal_fifteen_pages

/-- A book with content of at most one page gives 15: an empty book and quill, or a book of
one page. -/
theorem lecternSignal_of_pageCount_le_one (e : BlockEntities.Lectern) (n : ℕ) (hn : n ≤ 1)
    (hpages : e.book.bind (·.pages) = some n) : lecternSignal e = 15 := by
  have hcount : e.pageCount = n := by simp [BlockEntities.Lectern.pageCount, hpages]
  have hbook : e.hasBook = true := by simp [BlockEntities.Lectern.hasBook, hpages]
  have hgt : ¬ e.pageCount > 1 := by omega
  have h14 : F32.roundFloat (14 : ℚ) = 14 := by
    have := F32.roundFloat_natCast_div_two_pow 14 0 (by norm_num)
    simpa using this
  unfold lecternSignal
  simp only [roundFloat, hgt, ↓reduceIte, hbook, one_mul, h14]
  rfl

assert_standard_axioms lecternSignal_of_pageCount_le_one

end Redstone.Component.AnalogSource
