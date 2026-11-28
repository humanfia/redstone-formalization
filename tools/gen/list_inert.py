#!/usr/bin/env python3
"""Lists the Java block classes whose blocks no component covers: the blocks that are inert.

    python3 tools/gen/list_inert.py            # one line per class
    python3 tools/gen/list_inert.py --hooks    # with the methods each class overrides ($MC_SRC)
    python3 tools/gen/list_inert.py --ground   # the blocks of the component Ground instead

Reads `Redstone/Block/Generated/families.json` (written by gen_blocks.py) and
`tools/gen/components.json`, with the rule of gen_dispatch.py: a block belongs to the first
component that names a class of its class chain, and to none when no component does. The blocks
are grouped by their own class (the first of the chain). The table of inert classes in
`Redstone/Component/Ground.lean` is written from this list; run the script again after a change
to `components.json` or to the game version and compare.

With `--hooks` the decompiled sources are read (`$MC_SRC`, see tools/env.sh), and every method
that a class of the chain other than `Block` and `BlockBehaviour` declares is printed, with the
class that declares it. Methods of `BlockBehaviour` that only the client or the world generator
calls are left out of the print (see `QUIET`).
"""
import json
import os
import re
import sys

root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
families = json.load(open(os.path.join(root, "Redstone/Block/Generated/families.json")))
components = json.load(open(os.path.join(root, "tools/gen/components.json")))["components"]

# Methods that never change what the server does to the level in a game tick: rendering,
# particles, placement by a player (`ItemStack.useOn` is not modelled), state definition,
# rotation of structures, codecs, path finding of mobs, and names.
QUIET = {
    "codec", "createBlockStateDefinition", "getStateForPlacement", "rotate", "mirror",
    "animateTick", "getRenderShape", "skipRendering", "getVisualShape", "getShadeBrightness",
    "propagatesSkylightDown", "isPathfindable", "getCloneItemStack", "appendHoverText",
    "getDescriptionId", "getName", "getMenuProvider", "getSeed", "getOcclusionShape",
    "getInteractionShape", "useShapeForLightOcclusion", "getParticlePos", "getType",
    "isValidBonemealTarget", "isBonemealSuccess", "performBonemeal", "canBeReplaced",
    "setPlacedBy", "playerWillDestroy", "playerDestroy", "attack", "getDestroyProgress",
    "getMaxHorizontalOffset", "getMaxVerticalOffset", "getSoundType", "spawnDestroyParticles",
}


def module_of(classes):
    for c in components:
        if any(k in classes for k in c["classes"]):
            return c["module"]
    return None


def source_of(cls):
    src = os.environ.get("MC_SRC")
    if not src:
        sys.exit("MC_SRC is not set: source tools/env.sh")
    for sub in ("", "piston", "entity"):
        path = os.path.join(src, "net/minecraft/world/level/block", sub, cls + ".java")
        if os.path.exists(path):
            return open(path).read()
    return None


METHOD = re.compile(
    r"^   (?:@\w+\s+)*(?:public|protected|private)\s+(?:static\s+)?(?:final\s+)?"
    r"(?:<[^>]+>\s+)?[\w.<>\[\], ?]+\s+(\w+)\(", re.M)


def hooks_of(chain):
    out = []
    for cls in chain:
        if cls in ("Block", "BlockBehaviour"):
            continue
        text = source_of(cls)
        if text is None:
            out.append(f"{cls}: source not found")
            continue
        names = sorted({m for m in METHOD.findall(text) if m not in QUIET and m != cls})
        interfaces = re.search(r"class \w+(?:<[^{]*>)? (?:extends [\w.<>]+ )?implements ([^{]+)\{", text)
        tag = f" [implements {interfaces.group(1).strip()}]" if interfaces else ""
        out.append(f"{cls}{tag}: " + (", ".join(names) if names else "nothing"))
    return out


def main():
    want = "Ground" if "--ground" in sys.argv else None
    groups = {}
    for fam in families:
        for b in fam["blocks"]:
            if module_of(b["classes"]) == want:
                g = groups.setdefault(b["classes"][0], {"chain": b["classes"], "ids": [], "be": set()})
                g["ids"].append(b["id"].split(":")[1])
                if b["blockEntity"]:
                    g["be"].add(b["blockEntity"])
    total = 0
    for cls in sorted(groups):
        g = groups[cls]
        total += len(g["ids"])
        be = (" blockEntity=" + ",".join(sorted(g["be"]))) if g["be"] else ""
        ids = ", ".join(g["ids"][:4]) + (", …" if len(g["ids"]) > 4 else "")
        print(f"{cls} ({' < '.join(g['chain'])}) {len(g['ids'])}{be}: {ids}")
        if "--hooks" in sys.argv:
            for line in hooks_of(g["chain"]):
                print("    " + line)
    print(f"{len(groups)} classes, {total} blocks", file=sys.stderr)


if __name__ == "__main__":
    main()
