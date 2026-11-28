module

public import Redstone.Basic.Pos

/-!
# The iteration order of a Java hash set of positions

An explosion collects the positions it reaches in a `java.util.HashSet<BlockPos>` and then
goes through the set, so the order in which blocks explode is the iteration order of
`java.util.HashMap`. `JHashSet` reproduces it:

* the hash of a position (`Vec3i.hashCode`), spread as `HashMap.hash` does;
* the table of buckets, which starts with 16 and doubles when three quarters full
  (`HashMap.resize`), each bucket splitting in two that keep their order;
* a bucket that grows to nine positions: in a table of fewer than 64 buckets the table
  doubles, otherwise the bucket becomes a red-black tree (`HashMap.TreeNode`). A tree bucket is
  still iterated along its list of `next` pointers, but the root of the tree is moved to the
  front of that list and a new position is put right after its parent in the tree, so the
  order depends on the shape of the tree. `RBTree` reproduces `treeify`, `putTreeVal` and
  `balanceInsertion`.

Two different positions with the same hash in a tree bucket are ordered by
`System.identityHashCode` in Java, which no model can know: `JHashSet.unordered` reports this.
It needs two positions 31 blocks apart, further than an explosion of TNT reaches.
-/

@[expose] public section

namespace Redstone.Entity.Tnt

/-- `HashMap.hash(Vec3i.hashCode())`: the hash of a position, spread as `java.util.HashMap`
does, as an unsigned 32-bit number. -/
def posHash (p : Pos) : ℕ :=
  let h := (((p.y + p.z * 31) * 31 + p.x) % 4294967296).toNat
  h ^^^ (h >>> 16)

/-- `posHash` as the signed `int` that `HashMap.TreeNode` compares. -/
def posHashInt (p : Pos) : ℤ :=
  let h := posHash p
  if h ≥ 2147483648 then (h : ℤ) - 4294967296 else h

/-! ### Red-black trees -/

/-- The tree of a tree bucket (`HashMap.TreeNode`), with nodes numbered in the order of their
creation. -/
structure RBTree where
  /-- The hash of each node. -/
  hash : Array ℤ
  left : Array (Option ℕ)
  right : Array (Option ℕ)
  parent : Array (Option ℕ)
  red : Array Bool
  root : Option ℕ
  /-- The nodes along the `next` pointers, which is the order of iteration. -/
  next : List ℕ
  /-- Two nodes had the same hash, so that Java orders them by identity hash code. -/
  tie : Bool

namespace RBTree

/-- The tree without nodes. -/
def empty : RBTree := ⟨#[], #[], #[], #[], #[], none, [], false⟩

/-- `p.left`. -/
def l (t : RBTree) (p : ℕ) : Option ℕ := t.left.getD p none

/-- `p.right`. -/
def r (t : RBTree) (p : ℕ) : Option ℕ := t.right.getD p none

/-- `p.parent`. -/
def up (t : RBTree) (p : ℕ) : Option ℕ := t.parent.getD p none

/-- `p.red`. -/
def isRed (t : RBTree) (p : ℕ) : Bool := t.red.getD p false

/-- `p.left = v`. -/
def setL (t : RBTree) (p : ℕ) (v : Option ℕ) : RBTree :=
  { t with left := t.left.setIfInBounds p v }

/-- `p.right = v`. -/
def setR (t : RBTree) (p : ℕ) (v : Option ℕ) : RBTree :=
  { t with right := t.right.setIfInBounds p v }

/-- `p.parent = v`. -/
def setUp (t : RBTree) (p : ℕ) (v : Option ℕ) : RBTree :=
  { t with parent := t.parent.setIfInBounds p v }

/-- `p.red = v`. -/
def setRed (t : RBTree) (p : ℕ) (v : Bool) : RBTree := { t with red := t.red.setIfInBounds p v }

/-- `TreeNode.rotateLeft(root, p)`. -/
def rotateLeft (t : RBTree) (p : ℕ) : RBTree :=
  match t.r p with
  | none => t
  | some r =>
    let rl := t.l r
    let t := t.setR p rl
    let t := match rl with
      | some rl => t.setUp rl (some p)
      | none => t
    let pp := t.up p
    let t := t.setUp r pp
    let t := match pp with
      | none => { t.setRed r false with root := some r }
      | some pp => if t.l pp == some p then t.setL pp (some r) else t.setR pp (some r)
    (t.setL r (some p)).setUp p (some r)

/-- `TreeNode.rotateRight(root, p)`. -/
def rotateRight (t : RBTree) (p : ℕ) : RBTree :=
  match t.l p with
  | none => t
  | some l =>
    let lr := t.r l
    let t := t.setL p lr
    let t := match lr with
      | some lr => t.setUp lr (some p)
      | none => t
    let pp := t.up p
    let t := t.setUp l pp
    let t := match pp with
      | none => { t.setRed l false with root := some l }
      | some pp => if t.r pp == some p then t.setR pp (some l) else t.setL pp (some l)
    (t.setR l (some p)).setUp p (some l)

/-- The loop of `TreeNode.balanceInsertion(root, x)`, bounded by `fuel` rounds: restores the
red-black properties after the red node `x` was attached. -/
def balanceLoop : ℕ → RBTree → ℕ → RBTree
  | 0, t, _ => t
  | fuel + 1, t, x =>
    match t.up x with
    | none => { t.setRed x false with root := some x }
    | some xp =>
      if !t.isRed xp then t
      else
        match t.up xp with
        | none => t
        | some xpp =>
          if t.l xpp == some xp then
            match (t.r xpp).filter t.isRed with
            | some xppr =>
              balanceLoop fuel (((t.setRed xppr false).setRed xp false).setRed xpp true) xpp
            | none =>
              let (t, x) := if t.r xp == some x then (t.rotateLeft xp, xp) else (t, x)
              let t := match t.up x with
                | some xp =>
                  let xpp := t.up xp
                  let t := t.setRed xp false
                  match xpp with
                  | some xpp => (t.setRed xpp true).rotateRight xpp
                  | none => t
                | none => t
              balanceLoop fuel t x
          else
            match (t.l xpp).filter t.isRed with
            | some xppl =>
              balanceLoop fuel (((t.setRed xppl false).setRed xp false).setRed xpp true) xpp
            | none =>
              let (t, x) := if t.l xp == some x then (t.rotateRight xp, xp) else (t, x)
              let t := match t.up x with
                | some xp =>
                  let xpp := t.up xp
                  let t := t.setRed xp false
                  match xpp with
                  | some xpp => (t.setRed xpp true).rotateLeft xpp
                  | none => t
                | none => t
              balanceLoop fuel t x

/-- `TreeNode.balanceInsertion(root, x)`. -/
def balanceInsertion (t : RBTree) (x : ℕ) : RBTree :=
  balanceLoop (2 * t.hash.size + 2) (t.setRed x true) x

/-- The descent of `treeify` and `putTreeVal`, bounded by `fuel` steps: from the node `p` down
to the place of a new node with hash `h`. Returns the parent of that place, whether the place
is its left child, and whether a node with the same hash was passed. -/
def descend (t : RBTree) (h : ℤ) : ℕ → ℕ → Bool → ℕ × Bool × Bool
  | 0, p, tie => (p, true, tie)
  | fuel + 1, p, tie =>
    let ph := t.hash.getD p 0
    let tie := tie || ph == h
    -- `dir <= 0`; for equal hashes Java asks the identity hash code, here left is taken
    let goLeft := ph ≥ h
    match (if goLeft then t.l p else t.r p) with
    | some q => descend t h fuel q tie
    | none => (p, goLeft, tie)

/-- Adds a node with hash `h` to the arrays, not yet attached. Returns its number. -/
def newNode (t : RBTree) (h : ℤ) : RBTree × ℕ :=
  ({ t with
      hash := t.hash.push h, left := t.left.push none, right := t.right.push none,
      parent := t.parent.push none, red := t.red.push false }, t.hash.size)

/-- Attaches the new node `x` below the place found by `descend` and rebalances. -/
def attach (t : RBTree) (x : ℕ) : RBTree × ℕ :=
  match t.root with
  | none => ({ t with root := some x }, x)
  | some root =>
    let (xp, goLeft, tie) := t.descend (t.hash.getD x 0) (t.hash.size + 1) root false
    let t := { t.setUp x (some xp) with tie := t.tie || tie }
    let t := if goLeft then t.setL xp (some x) else t.setR xp (some x)
    (t.balanceInsertion x, xp)

/-- `TreeNode.moveRootToFront`: the root of the tree becomes the first node of the bucket. -/
def moveRootToFront (t : RBTree) : RBTree :=
  match t.root with
  | some root => { t with next := root :: t.next.erase root }
  | none => t

/-- `TreeNode.treeify`: the tree of a bucket whose nodes have the given hashes, in the order of
the bucket. -/
def treeify (hashes : List ℤ) : RBTree :=
  let t := hashes.foldl
    (fun t h =>
      let (t, x) := t.newNode h
      (t.attach x).1)
    empty
  { t with next := List.range hashes.length }.moveRootToFront

/-- `TreeNode.putTreeVal` for a key that is not in the tree: the new node is put after its
parent in the list of `next` pointers. -/
def putTreeVal (t : RBTree) (h : ℤ) : RBTree :=
  let (t, x) := t.newNode h
  let (t, xp) := t.attach x
  let next := t.next.flatMap fun i => if i == xp then [i, x] else [i]
  { t with next := next }.moveRootToFront

end RBTree

/-! ### The hash set -/

/-- A bucket of the table (a bin). -/
inductive JBin
  /-- A linked list of positions, in the order in which they were added. -/
  | list (keys : List Pos)
  /-- A red-black tree: built from the positions `initial`, in this order, to which `added` were
  then added. -/
  | tree (initial added : List Pos)

namespace JBin

/-- The tree of a tree bucket. -/
def rbTree (initial added : List Pos) : RBTree :=
  added.foldl (fun t p => t.putTreeVal (posHashInt p)) (RBTree.treeify (initial.map posHashInt))

/-- The positions of the bucket in the order of iteration. -/
def keys : JBin → List Pos
  | list keys => keys
  | tree initial added =>
    let all := (initial ++ added).toArray
    (rbTree initial added).next.filterMap (all[·]?)

/-- The bucket contains the position. -/
def contains : JBin → Pos → Bool
  | list keys, p => keys.contains p
  | tree initial added, p => initial.contains p || added.contains p

/-- Two positions of a tree bucket have the same hash. -/
def unordered : JBin → Bool
  | list _ => false
  | tree initial added => (rbTree initial added).tie

end JBin

/-- A `java.util.HashSet` of positions, as far as its iteration order goes. -/
structure JHashSet where
  /-- The buckets of the table, whose size is a power of two. -/
  buckets : Array JBin
  /-- The number of positions. -/
  size : ℕ

namespace JHashSet

/-- The set before the first insertion; the game allocates 16 buckets then. -/
def empty : JHashSet := ⟨Array.replicate 16 (.list []), 0⟩

/-- `HashMap.resize`: doubles the table. Every bucket splits in two that keep its order
(`TreeNode.split` for a tree: a half of at most six positions becomes a list again, a longer
half becomes a new tree, unless the other half is empty and the tree stays as it is). -/
def resize (s : JHashSet) : JHashSet :=
  let old := s.buckets.size
  let halves := s.buckets.map fun bin =>
    let (lo, hi) := bin.keys.partition fun p => posHash p % (2 * old) < old
    match bin with
    | .list _ => (JBin.list lo, JBin.list hi)
    | .tree _ _ =>
      let half (part other : List Pos) : JBin :=
        if part.length ≤ 6 then .list part else if other.isEmpty then bin else .tree part []
      (half lo hi, half hi lo)
  { s with buckets := halves.map (·.1) ++ halves.map (·.2) }

/-- Replaces the bucket with index `i`. -/
def set (s : JHashSet) (i : ℕ) (bin : JBin) : JHashSet :=
  { s with buckets := s.buckets.setIfInBounds i bin }

/-- `HashSet.add`. -/
def insert (s : JHashSet) (p : Pos) : JHashSet :=
  let cap := s.buckets.size
  let i := posHash p % cap
  let bin := s.buckets.getD i (.list [])
  if bin.contains p then s
  else
    let s := { s with size := s.size + 1 }
    let s : JHashSet :=
      match bin with
      | .list keys =>
        -- `treeifyBin` for a bucket that had eight positions already
        if keys.length ≥ 8 then
          if cap < 64 then (s.set i (.list (keys ++ [p]))).resize
          else s.set i (.tree (keys ++ [p]) [])
        else s.set i (.list (keys ++ [p]))
      | .tree initial added =>
        s.set i (.tree initial (added ++ [p]))
    if s.size > s.buckets.size * 3 / 4 then s.resize else s

/-- The positions in the order in which `HashSet.iterator` gives them. -/
def toList (s : JHashSet) : List Pos := s.buckets.toList.flatMap (·.keys)

/-- The order of the set is not determined: see `JBin.unordered`. -/
def unordered (s : JHashSet) : Bool := s.buckets.any (·.unordered)

end JHashSet

end Redstone.Entity.Tnt
