module

public import Redstone.World.Light

/-!
# Sky light

The sky light of a cell is computed in `Redstone.World.Light`, together with block light, the
dampening of blocks and the occlusion of faces. This file only keeps the names under which the
daylight detector asks for it.
-/

@[expose] public section

namespace Redstone.Component.Sensor.Light

export Redstone.Light (lightDampening isOpaque isSource skyLight)

end Redstone.Component.Sensor.Light
