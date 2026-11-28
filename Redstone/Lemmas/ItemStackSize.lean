module

public import Redstone.Block.Generated.Items

/-!
# The item table is what its list says

The maximal stack size of an item is looked up in a search tree on `itemKey`
(`Redstone.itemStackSizeTable`), so that the Lean kernel can evaluate it cheaply; see
`Redstone/Basic/ItemKey.lean`. The tree is generated next to the list of names it was made from
(`Redstone.itemStackSizes`). Here the kernel checks that the tree holds exactly the entries of
the list, in ascending order, and from that `itemMaxStackSize_eq_lookup` follows: for every
string, the stack size is the one the list gives for that name, and 64 for a name that is not
listed. That is a scan of the list, the definition the model had before the tree.
-/

@[expose] public section

set_option Elab.async false

namespace Redstone

/-- The search tree holds the entries of `itemStackSizes`, by key, in the order of the list. -/
theorem itemStackSizeTable_toList :
    itemStackSizeTable.toList = itemStackSizes.map fun e => (itemKey e.1, e.2) := by
  decide +kernel

/-- The keys of the search tree ascend from left to right. -/
theorem itemStackSizeTable_ascending :
    ItemTable.ascending itemStackSizeTable.toList = true := by
  decide +kernel

/-- `itemMaxStackSize` is a scan of `itemStackSizes`: the size listed for the name, 64 if the
name is not listed. -/
theorem itemMaxStackSize_eq_lookup (id : String) :
    itemMaxStackSize id = (itemStackSizes.lookup id).getD 64 := by
  rw [itemMaxStackSize,
    ItemTable.find?_itemKey _ _ itemStackSizeTable_toList itemStackSizeTable_ascending]

end Redstone
