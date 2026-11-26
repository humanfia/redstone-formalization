module

public import Redstone.World.Level

/-!
# Sky light

Java classes: `SkyLightEngine`, `LightEngine`, `ChunkSkyLightSources`.

The sky light of a cell, as the light engine stores it (`getBrightness(LightLayer.SKY, pos)`),
before the time of day and the weather darken it. The engine works incrementally; what it
converges to is described directly here:

* a cell is a *source*, with light 15, when nothing stops the light of the sky on its way
  straight down to the cell (`ChunkSkyLightSources`);
* a cell that is opaque has light 0;
* any other cell has the light of its brightest neighbour minus one, where light does not pass
  through a face that is occluded (`SkyLightEngine.propagateIncrease`).

So the light of a cell is 15 minus the length of the shortest path of cells that are not opaque
from the cell to a source, and 0 if there is no such path of length at most 14.

## What is modelled exactly, and what is not

* `lightDampening` follows `BlockBehaviour.getLightDampening` and the default
  `propagatesSkylightDown`, with the override of `TransparentBlock` for glass. The overrides of
  the other classes are not modelled: stained and tinted glass, copper grates (the other
  `TransparentBlock`s), leaves, panes, fences, walls, vines, bamboo, barriers, light blocks,
  glow lichen, hanging moss, mossy carpets, chorus plants, shulker boxes. Measured against the
  server, the model is wrong for stained glass, tinted glass, copper grates, barriers, glow
  lichen, vines and chorus plants above a detector; for the others the override happens to
  agree with the default in the states tried.
* Of the blocks whose shape occludes light (`useShapeForLightOcclusion`), only the daylight
  detector is modelled: light does not pass through its bottom face. Slabs, stairs, farmland,
  paths, snow layers, enchanting tables, end portal frames, lecterns, sculk sensors, sculk
  shriekers, shelves, stonecutters, **extended piston bases and piston heads** are treated as
  if they had no such shape: a detector below one of them reads the open sky where the game
  reads darkness (`tests/pending/scenarios/sensor/dd-piston-roof.json`). A faithful model
  needs the occlusion shapes of both blocks at a face (`Shapes.faceShapeOccludes` joins them),
  which the block attributes do not carry.
* The world is the overworld: sky light comes from above the build height, `y = 319`. The
  light engine keeps one more section of 16 layers below and above the build limits, which is
  enough for every path of 14 steps, so the search is not bounded in space.

For worlds built from full opaque blocks, air, glass, daylight detectors and blocks that are
neither full cubes nor light-occluding shapes (levers, lightning rods, ...), the result is the
light of the game.
-/

@[expose] public section

namespace Redstone.Component.Sensor.Light

/-- The highest layer of blocks in the overworld. Every cell above it is air. -/
def maxY : ℤ := 319

/-- The index of the full cube in the shape table of the block dump (`Attrs.outline`); index 0
is the empty shape. -/
def fullBlockShape : ℕ := 1

/-- `BlockState.getLightDampening`: 15 for a block that is `isSolidRender`, 0 for a block that
lets the light of the sky pass downwards (`propagatesSkylightDown`), 1 otherwise. By default a
block lets it pass when its shape is not a full cube and it holds no fluid; glass always does. -/
def lightDampening (b : Block) : ℕ :=
  if b.attrs.solidRender then 15
  else if b.is .glass || (b.attrs.outline != fullBlockShape && b.attrs.fluid == "") then 0
  else 1

/-- The block does not let light in: `LightEngine.getOpacity` is 15. -/
def isOpaque (b : Block) : Bool := b.attrs.solidRender

/-- The bottom face of the block occludes light. Among the modelled blocks this is the daylight
detector, whose shape is used for light occlusion and covers the whole bottom face. -/
def occludesBelow (b : Block) : Bool := b.is .daylight_detector

/-- The cell `p` is a source of sky light: `p.y` is at least `getLowestSourceY` of its column.
Going down from the sky to `p`, no edge between two cells is occluded
(`ChunkSkyLightSources.isEdgeOccluded`): every cell from `p` upwards has light dampening 0, and
no cell above `p` occludes light with its bottom face. -/
def isSource (w : World) (p : Pos) : Bool :=
  (List.range (maxY + 1 - p.y).toNat).all fun i =>
    let b := w.blockAt ⟨p.x, p.y + i, p.z⟩
    lightDampening b == 0 && (i == 0 || !occludesBelow b)

/-- Light passes from the cell `c.step d` into the cell `c` (`LightEngine.shapeOccludes` is
false): neither is the bottom face of the upper of two cells occluding, nor is `c` opaque. -/
def passesFrom (w : World) (c : Pos) (d : Direction) : Bool :=
  let here := w.blockAt c
  !isOpaque here &&
    match d with
    | .up => !occludesBelow (w.blockAt (c.step d))
    | .down => !occludesBelow here
    | _ => true

/-- The cells from which light passes into one of the cells of `frontier`, except those in
`seen`. -/
def expand (w : World) (seen frontier : List Pos) : List Pos :=
  frontier.foldl
    (fun acc c =>
      Direction.values.foldl
        (fun acc d =>
          let n := c.step d
          if passesFrom w c d && !seen.contains n && !acc.contains n then n :: acc else acc)
        acc)
    []

/-- The search for a source, breadth first. `frontier` holds the cells whose shortest path to
the start has `15 - light` steps, `seen` those and all nearer ones. Returns the sky light of
the start. A source in the frontier ends the search; so does `light = 0`. -/
def search (w : World) : ℕ → List Pos → List Pos → ℕ
  | 0, _, _ => 0
  | light + 1, seen, frontier =>
    if frontier.any (isSource w) then light + 1
    else
      -- Light only spreads from cells that are lit, and an opaque cell never is.
      let next := (expand w seen frontier).filter fun n => !isOpaque (w.blockAt n)
      if next.isEmpty then 0 else search w light (next ++ seen) next

/-- `getBrightness(LightLayer.SKY, pos)`: the sky light of the cell `p` in the world `w`. -/
def skyLight (w : World) (p : Pos) : ℕ :=
  if isOpaque (w.blockAt p) then 0 else search w 15 [p] [p]

end Redstone.Component.Sensor.Light
