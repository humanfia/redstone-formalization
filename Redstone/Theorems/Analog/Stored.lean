import Redstone.Theorems.Analog.Common

/-!
# Analog sources that keep their measure in a block entity

A source block, a comparator that reads it, and a piece of redstone dust in front of the
comparator, on a stone floor; one such level for each source.

```
z = 0:  S  C  o        S: the source, C: comparator (reads west, emits east), o: output dust
x =     0  1  2        y = 1, seen from above
```

The measure of these sources is not in the block state: it is the slot of a chiseled bookshelf
that was used last, the record of a jukebox, the page of the book on a lectern. The formulas
are in `Redstone/Lemmas/AnalogSource.lean`; here a player acts on the block and the comparator
follows two game ticks later (1 redstone tick = 2 game ticks). The four levels have the same
layout, which is why they share a file.

* **Chiseled bookshelf** (`bookshelf_table`): a book is put into the shelf through the centre
  of its front, which is slot 4 of the slots 0 to 5; the comparator emits 5, the number of the
  slot counted from one. The book is taken out again: the shelf is empty and the comparator
  still emits 5, because the slot used last is still slot 4.
* **Jukebox** (`jukebox_plays`): the record "Pigstep" is put in; the comparator emits 13, the
  number of that record. The jukebox plays (its block entity is ticked every game tick), so
  this level is never at rest, and the statement is about the six game ticks of the run.
* **Lectern** (`lectern_book`): a book and quill is put on an empty lectern; it has no page, and
  such a book gives 15.
* **Lectern, by the page** (`lectern_page`): a written book of fifteen pages lies open at its
  eighth page (page 7, counted from zero). The comparator emits 8: page `k` of fifteen gives
  `k + 1` (`AnalogSource.lecternSignal_fifteen_pages`).

## What the last level assumes

Turning a page is done through the menu of the lectern, which no input of the model reaches
(`AnalogSource.setPage` is defined and nothing calls it). So the level `paged` is loaded raw
with the book already open at page 7 and the comparator still off, which is the state right
after the page was turned and before the comparator has been told. What tells it here is a
block placed next to the comparator: any neighbour update makes a comparator look at its
input. The other three levels are loaded raw in a state of rest (`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.Stored

/-- The source. -/
def src : Pos := ⟨0, 1, 0⟩

/-- The comparator that reads the source. -/
def cmp : Pos := ⟨1, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨2, 1, 0⟩

/-- The block `source` with the given block entity (a fresh one if none is given), a
comparator that reads it and a piece of dust, on a stone floor. -/
def reader (source : Block) (blockEntity : List (Pos × BlockEntity) := []) : Level :=
  .ofCells (floor [0, 1, 2] [0] ++
    [(src, source), (cmp, .comparator ⟨.west, .compare, false⟩), (out, wireEW)]) blockEntity

/-- What is observed: the source block, the comparator, and the power of the dust at the
output. -/
def observe (l : Level) : Block × (Bool × ℕ) × ℕ :=
  (l.blockAt src, comparator l cmp, l.dustPower out)

/-! ### Chiseled bookshelf -/

/-- A chiseled bookshelf that faces north, with a book in slot 4 or without. -/
def shelfBlock (book : Bool) : Block :=
  .chiseledBookShelf ⟨.north, false, false, false, false, book, false⟩

/-- The reader with an empty chiseled bookshelf. -/
def bookshelf : Level := reader (shelfBlock false)

/-- A book is used on the front of the shelf before game tick 1; the shelf is used with an
empty hand before game tick 5. -/
def bookshelfSchedule : Schedule :=
  .first [.useItem src .north "minecraft:book"] 4 ++ .first [.use src .north] 4

checkpoints bs := bookshelfSchedule from bookshelf

/-- The slot of the shelf that was used last. -/
def lastSlot (l : Level) : ℤ :=
  match l.blockEntities src with
  | some (.chiseledBookshelf d) => d.lastInteractedSlot
  | _ => -1

/-- **A chiseled bookshelf gives the number of the slot used last, counted from one**, also
after the book has been taken out again. -/
theorem bookshelf_table :
    observe bookshelf = (shelfBlock false, (false, 0), 0) ∧
      lastSlot bookshelf = -1 ∧
      observe (rules.runSchedule (bookshelfSchedule.take 1) bookshelf) =
        (shelfBlock true, (false, 0), 0) ∧
      observe (rules.runSchedule (bookshelfSchedule.take 2) bookshelf) =
        (shelfBlock true, (true, 5), 5) ∧
      observe (rules.runSchedule (bookshelfSchedule.take 4) bookshelf) =
        (shelfBlock true, (true, 5), 5) ∧
      lastSlot (rules.runSchedule (bookshelfSchedule.take 4) bookshelf) = 4 ∧
      observe (rules.runSchedule bookshelfSchedule bookshelf) =
        (shelfBlock false, (true, 5), 5) ∧
      lastSlot (rules.runSchedule bookshelfSchedule bookshelf) = 4 ∧
      (rules.runSchedule (bookshelfSchedule.take 4) bookshelf).Quiescent ∧
      (rules.runSchedule bookshelfSchedule bookshelf).Quiescent ∧
      (rules.runSchedule bookshelfSchedule bookshelf).overflow = false := by
  rw [bs_run_1, bs_run_2, bs_run_4, bs_run]
  circuit_decide

assert_standard_axioms bookshelf_table

/-! ### Jukebox -/

/-- The reader with an empty jukebox. -/
def jukebox : Level := reader (.jukebox ⟨false⟩)

/-- The record "Pigstep" is put into the jukebox before game tick 1; six game ticks. -/
def jukeboxSchedule : Schedule :=
  .first [.useItem src .up "minecraft:music_disc_pigstep"] 6

checkpoints jb := jukeboxSchedule from jukebox

/-- **A jukebox gives the number of its record**: 13 for "Pigstep", from the second game tick
after the record was put in. -/
theorem jukebox_plays :
    observe jukebox = (.jukebox ⟨false⟩, (false, 0), 0) ∧
      observe (rules.runSchedule (jukeboxSchedule.take 1) jukebox) =
        (.jukebox ⟨true⟩, (false, 0), 0) ∧
      observe (rules.runSchedule (jukeboxSchedule.take 2) jukebox) =
        (.jukebox ⟨true⟩, (true, 13), 13) ∧
      observe (rules.runSchedule jukeboxSchedule jukebox) =
        (.jukebox ⟨true⟩, (true, 13), 13) ∧
      (rules.runSchedule jukeboxSchedule jukebox).overflow = false := by
  rw [jb_run_1, jb_run_2, jb_run]
  circuit_decide

assert_standard_axioms jukebox_plays

/-! ### Lectern -/

/-- A lectern that faces north, with or without a book. -/
def lecternBlock (book : Bool) : Block := .lectern ⟨.north, book, false⟩

/-- The reader with an empty lectern. -/
def lectern : Level := reader (lecternBlock false)

/-- A book and quill is put on the lectern before game tick 1; four game ticks. -/
def lecternSchedule : Schedule := .first [.useItem src .up "minecraft:writable_book"] 4

checkpoints lb := lecternSchedule from lectern

/-- **A lectern with a book without pages gives 15.** -/
theorem lectern_book :
    observe lectern = (lecternBlock false, (false, 0), 0) ∧
      observe (rules.runSchedule (lecternSchedule.take 1) lectern) =
        (lecternBlock true, (false, 0), 0) ∧
      observe (rules.runSchedule (lecternSchedule.take 2) lectern) =
        (lecternBlock true, (true, 15), 15) ∧
      observe (rules.runSchedule lecternSchedule lectern) =
        (lecternBlock true, (true, 15), 15) ∧
      (rules.runSchedule lecternSchedule lectern).Quiescent ∧
      (rules.runSchedule lecternSchedule lectern).overflow = false := by
  rw [lb_run_1, lb_run_2, lb_run]
  circuit_decide

assert_standard_axioms lectern_book

/-- The reader with a lectern that holds a written book of fifteen pages, open at page 7
(counted from zero). The comparator has not been told yet. -/
def paged : Level :=
  reader (lecternBlock true)
    [(src, .lectern ⟨some ⟨"minecraft:written_book", some 15, []⟩, 7⟩)]

/-- The place next to the comparator where a block is put to give it a neighbour update. -/
def nudge : Pos := ⟨1, 1, 1⟩

/-- A stone block is placed next to the comparator before game tick 1; four game ticks. -/
def pagedSchedule : Schedule := .first [.set nudge (.plain .stone)] 4

checkpoints pg := pagedSchedule from paged

/-- **Page 7 of fifteen gives 8.** The comparator emits 8 from the second game tick after it
got a neighbour update, and the level is then at rest. -/
theorem lectern_page :
    observe paged = (lecternBlock true, (false, 0), 0) ∧
      observe (rules.runSchedule (pagedSchedule.take 1) paged) =
        (lecternBlock true, (false, 0), 0) ∧
      observe (rules.runSchedule (pagedSchedule.take 2) paged) =
        (lecternBlock true, (true, 8), 8) ∧
      observe (rules.runSchedule pagedSchedule paged) = (lecternBlock true, (true, 8), 8) ∧
      (rules.runSchedule pagedSchedule paged).Quiescent ∧
      (rules.runSchedule pagedSchedule paged).overflow = false := by
  rw [pg_run_1, pg_run_2, pg_run]
  circuit_decide

assert_standard_axioms lectern_page

/-- Before the schedules, the levels with the bookshelf, the jukebox and the empty lectern are
at rest. (So is `paged` by this measure, which only says that nothing is scheduled; see the
module docstring.) -/
theorem circuit_quiescent :
    bookshelf.Quiescent ∧ jukebox.Quiescent ∧ lectern.Quiescent ∧ paged.Quiescent := by
  circuit_decide

assert_standard_axioms circuit_quiescent

end Redstone.Theorems.Analog.Stored
