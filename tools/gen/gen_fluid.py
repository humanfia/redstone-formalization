#!/usr/bin/env python3
"""Generates `Redstone/Block/Generated/Fluid.lean`: the fluid state of every block state, the
property `waterlogged`, and the block tags the flow of fluids reads, all without strings.

    python3 tools/gen/gen_fluid.py $MC_REPORTS/blockdump.json [server.jar]

Reads the server's block dump and `Redstone/Block/Generated/families.json` (written by
gen_blocks.py). The dump gives, for every block state, the block its fluid state leaves behind
(`getFluidState().createLegacyBlock()`, the attribute `fluid`). The script finds the rule each
block follows, writes it as a match on the block's constructor, and checks that the rule gives
back the dump for every single state, so that `Block.fluidState` followed by
`FluidState.createLegacyBlock` is the attribute `fluid` of `Redstone.Block.Generated.Attrs`.
It fails on a block that follows none of the rules.

The dump does not say whether a fluid state is falling. Only one class makes a falling source:
`WaterloggedTransparentBlock.getFluidState` returns `Fluids.WATER.getSource(true)`; the blocks
of that class are recognised by their class chain.

The block tags are read from the server jar, which defaults to
`$MC_HOME/bundle/META-INF/versions/<version>/server-<version>.jar`.
"""
import glob
import json
import os
import sys
import zipfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_blocks import ident  # noqa: E402

root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
dump = json.load(open(sys.argv[1]))
families = json.load(open(os.path.join(root, "Redstone/Block/Generated/families.json")))
blocks = {b["id"]: b for b in dump["blocks"]}

WATER = "minecraft:water[level=0]"


def legacy(kind, level):
    """`createLegacyBlock` of `FluidState.ofLevel kind level`, as the dump writes it."""
    return f"minecraft:{kind}[level={0 if level == 0 else level if level < 8 else 8}]"


# The block tags (`BlockTags`) that `FlowingFluid`, `LiquidBlock` and `BubbleColumnBlock` read.
TAGS = ["washed_away_by_fluids", "enables_bubble_column_drag_down",
        "enables_bubble_column_push_up"]


def find_jar():
    if len(sys.argv) > 2:
        return sys.argv[2]
    home = os.environ.get("MC_HOME")
    if not home:
        sys.exit("give the server jar as the second argument or set MC_HOME")
    jars = glob.glob(os.path.join(home, "bundle/META-INF/versions/*/server-*.jar"))
    if len(jars) != 1:
        sys.exit(f"{len(jars)} server jars under {home}/bundle/META-INF/versions: "
                 "give the one of the block dump as the second argument")
    return jars[0]


def resolve(jar, name, seen=()):
    """The blocks of a tag, in the order of the tag file, without the `minecraft:` prefix."""
    if name in seen:
        sys.exit(f"tag {name} refers to itself")
    out = []
    for v in json.loads(jar.read(f"data/minecraft/tags/block/{name}.json"))["values"]:
        if isinstance(v, dict):  # {"id": ..., "required": false}
            v = v["id"]
        ns, _, rest = v.lstrip("#").partition(":")
        if ns != "minecraft":
            sys.exit(f"tag {name}: unexpected namespace in {v}")
        for b in resolve(jar, rest, seen + (name,)) if v.startswith("#") else [rest]:
            if b not in out:
                out.append(b)
    return out


def predicate(doc, name, ids, known):
    unknown = [b for b in ids if b not in known]
    if unknown:
        sys.exit(f"{name}: not in the block inventory: {unknown}")
    o = [f"/-- {doc} -/", f"def {ident(name)} : BlockId → Bool"]
    line = "  |"
    for i, b in enumerate(ids):
        piece = f" .{ident(b)}" + (" |" if i + 1 < len(ids) else " => true")
        if len(line) + len(piece) > 100:
            o.append(line)
            line = "  " + piece
        else:
            line += piece
    o.append(line)
    o.append("  | _ => false\n")
    return o


classes = {x["id"]: x["classes"] for fam in families for x in fam["blocks"]}


def rule(b):
    """The rule the block follows: (key, Lean term in `s`), checked against every state."""
    props = [p["name"] for p in b["properties"]]
    fluids = [s["attrs"].get("fluid") for s in b["states"]]
    if not any(fluids):
        return ("empty", None)
    if all(f == WATER for f in fluids) and b["id"] not in ("minecraft:water", "minecraft:lava"):
        return ("water", ".source .water")
    if b["id"] in ("minecraft:water", "minecraft:lava") and props == ["level"]:
        kind = b["id"].split(":")[1]
        values = b["properties"][0]["values"]
        for s in b["states"]:
            assert s["attrs"].get("fluid") == legacy(kind, int(values[s["values"][0]])), b["id"]
        return (kind, f".ofLevel .{kind} s.level.val")
    if "waterlogged" in props:
        i = props.index("waterlogged")
        values = b["properties"][i]["values"]
        for s in b["states"]:
            logged = values[s["values"][i]] == "true"
            assert s["attrs"].get("fluid") == (WATER if logged else None), b["id"]
        if "WaterloggedTransparentBlock" in classes[b["id"]]:
            return ("waterloggedFalling", ".waterloggedFalling s.waterlogged")
        return ("waterlogged", ".waterlogged s.waterlogged")
    raise SystemExit(f"{b['id']}: the fluid state follows no known rule")


o = ["""module

public import Redstone.Block.Fluid

/-!
# The fluid state of every block state

Generated by `tools/gen/gen_fluid.py` from the Minecraft block dump. Do not edit.
-/

set_option linter.all false
set_option maxRecDepth 100000

@[expose] public section

namespace Redstone

namespace Block

/-- `BlockState.getFluidState()`: the fluid the block holds. Blocks of water and lava hold
their fluid, a block with the property `waterlogged` set holds a water source (a falling one
for a `WaterloggedTransparentBlock`), and so do the few blocks that only exist under water. -/
def fluidState : Block → FluidState"""]
logged, count = [], 0
for fam in families:
    multi, has_props = len(fam["blocks"]) > 1, bool(fam["props"])
    rules = [rule(blocks[x["id"]]) for x in fam["blocks"]]
    count += sum(r[0] != "empty" for r in rules)
    ctor = "." + ident(fam["ctor"])
    if "waterlogged" in fam["props"]:
        logged.append((ctor, multi))
    if all(r[0] == "empty" for r in rules):
        continue
    if len(set(rules)) == 1:
        s = " s" if "s." in rules[0][1] else " _" if has_props else ""
        o.append(f"  | {ctor}{' _' if multi else ''}{s} => {rules[0][1]}")
        continue
    assert multi
    groups = {}
    for x, r in zip(fam["blocks"], rules):
        if r[0] != "empty":
            groups.setdefault(r, []).append(x["id"].split(":")[1])
    s = " s" if any("s." in r[1] for r in groups) else " _" if has_props else ""
    o.append(f"  | {ctor} i{s} =>\n    match i with")
    for r, ids in groups.items():
        o.append("    | " + " | ".join("." + ident(i) for i in ids) + f" => {r[1]}")
    if len(groups) and sum(len(v) for v in groups.values()) < len(fam["blocks"]):
        o.append("    | _ => .empty")
o.append("  | _ => .empty")
o.append("""
/-- The value of the property `waterlogged`, for the states that have it. -/
def waterlogged? : Block → Option Bool""")
for ctor, multi in logged:
    o.append(f"  | {ctor}{' _' if multi else ''} s => some s.waterlogged")
o.append("  | _ => none")
o.append("""
/-- `state.setValue(WATERLOGGED, v)`, for the states that have the property; the other states
are left as they are. -/
def setWaterlogged (b : Block) (v : Bool) : Block :=
  match b with""")
for ctor, multi in logged:
    i = " i" if multi else ""
    o.append(f"  | {ctor}{i} s => {ctor}{i} {{ s with waterlogged := v }}")
o.append("  | _ => b")
o.append("""
end Block

/-! ### Block tags

The block tags (`BlockTags`) that the flow of fluids reads, as predicates on blocks:
`FluidBlockTag.t id` is `state.is(BlockTags.T)` for a state of the block `id`. -/

namespace FluidBlockTag
""")
known = {i.split(":")[1] for i in classes}
with zipfile.ZipFile(find_jar()) as jar:
    for t in TAGS:
        o += predicate(f"The block tag `minecraft:{t}`.", t, resolve(jar, t), known)
o.append("end FluidBlockTag\n\nend Redstone\n")
with open(os.path.join(root, "Redstone/Block/Generated/Fluid.lean"), "w") as f:
    f.write("\n".join(o))
print(f"{count} blocks hold a fluid in some state, {len(logged)} families have `waterlogged`")
