module

public import Redstone.World.Level

/-!
# The sky: sun angle and sky darkening

Java classes: `Timelines` (the timeline `minecraft:day`), `KeyframeTrackSampler`,
`EasingType.CubicBezier`, `WeatherAttributes`, `EnvironmentAttributeSystem`, `Mth`.

In 26.3 the position of the sun and the brightness of the sky are *environment attributes*.
Their values are computed from the overworld clock by the timeline `minecraft:day` and then
modified by the weather. This file computes the two attributes a daylight detector reads:

* `EnvironmentAttributes.SUN_ANGLE`, in degrees: `sunAngle`;
* `EnvironmentAttributes.SKY_LIGHT_LEVEL`, from which `Level.updateSkyBrightness` derives
  `Level.skyDarken`: `skyDarken`.

The game computes them with `float` arithmetic, and so does this file, operation by operation,
with `Float32`. Constants are given by their IEEE bits, so that they are exactly the `float`
constants of the game.

## Assumptions

* The dimension is the overworld, and no biome changes the two attributes (none does in 26.3).
* The rain level and the thunder level are `0` or `1` (`Weather`).
* `Level.skyDarken` is recomputed at the start of every game tick, after the clock has advanced.
  Nothing in the model changes the clock or the weather at another moment, so the stored value
  always equals `skyDarken` of the current clock and weather, and it is not kept as state.
* `Mth.sin` reads a table of `(float) Math.sin(i / 10430.378350470453)`. The table entry is
  computed here with `Float.sin`, the sine of the C library. Both are accurate to less than one
  unit in the last place of a `double`, so the entries agree after rounding to `float`, unless
  a sine lies within that distance of the midpoint of two `float`s.
-/

@[expose] public section

namespace Redstone.Component.Sensor.Sky

/-- A `float` given by its IEEE bits. -/
def f32 (bits : UInt32) : Float32 := Float32.ofBits bits

/-- `0.362F`: the first control point of the easing of the sun angle, `x`. -/
def bezierX1 : Float32 := f32 0x3eb95810
/-- `0.241F`: the first control point of the easing of the sun angle, `y`. -/
def bezierY1 : Float32 := f32 0x3e76c8b4
/-- `1.0E-5F`: the tolerance of `EasingType.CubicBezier`. -/
def epsilon : Float32 := f32 0x3727c5ac
/-- `0.26666668F`: the factor of the sky light level at night (`4 / 15`). -/
def nightFactor : Float32 := f32 0x3e888889
/-- `0.3125F`: how much rain blends the sky light level towards `4`. -/
def rainAlpha : Float32 := f32 0x3ea00000
/-- `0.52734375F`: how much a thunderstorm blends the sky light level towards `4`. -/
def thunderAlpha : Float32 := f32 0x3f070000
/-- `0.2F`. -/
def fifth : Float32 := f32 0x3e4ccccd
/-- `(float) (Math.PI / 180.0)`. -/
def degToRad : Float32 := f32 0x3c8efa35
/-- `(float) Math.PI`. -/
def pi : Float32 := f32 0x40490fdb
/-- `(float) (Math.PI * 2)`. -/
def twoPi : Float32 := f32 0x40c90fdb
/-- `Mth.SIN_SCALE`, the `double` `10430.378350470453`. -/
def sinScale : Float := Float.ofBits 0x40c45f306dc9c883

/-- `Mth.lerp(alpha, p0, p1)`. -/
def lerp (alpha p0 p1 : Float32) : Float32 := p0 + alpha * (p1 - p0)

/-- `Mth.clamp(value, min, max)` for `float`. -/
def clamp (value min max : Float32) : Float32 :=
  if value < min then min else if value ≤ max then value else max

/-! ### The easing of the sun angle -/

/-- `EasingType.CubicBezier.CubicCurve`: the polynomial `((a t + b) t + c) t`. -/
structure CubicCurve where
  a : Float32
  b : Float32
  c : Float32

namespace CubicCurve

/-- `CubicBezier.curveFromControls(v1, v2)`. -/
def ofControls (v1 v2 : Float32) : CubicCurve :=
  ⟨3 * v1 - 3 * v2 + 1, -6 * v1 + 3 * v2, 3 * v1⟩

/-- `CubicCurve.sample(t)`. -/
def sample (k : CubicCurve) (t : Float32) : Float32 := ((k.a * t + k.b) * t + k.c) * t

/-- `CubicCurve.sampleGradient(t)`. -/
def sampleGradient (k : CubicCurve) (t : Float32) : Float32 :=
  (3 * k.a * t + 2 * k.b) * t + k.c

end CubicCurve

/-- The curve of `x` of `EasingType.symmetricCubicBezier(0.362F, 0.241F)`. -/
def xCurve : CubicCurve := .ofControls bezierX1 (1 - bezierX1)

/-- The curve of `y` of `EasingType.symmetricCubicBezier(0.362F, 0.241F)`. -/
def yCurve : CubicCurve := .ofControls bezierY1 (1 - bezierY1)

/-- The loop of `CubicBezier.solveTBisect(x, initialT)`, bounded by `fuel` rounds: bisection
for a `t` in `[t0, t1]` with `xCurve.sample t` close to `x`, starting from the guess `t`. -/
def solveTBisectLoop (x : Float32) : ℕ → Float32 → Float32 → Float32 → Float32
  | 0, _, _, t => t
  | fuel + 1, t0, t1, t =>
    if t0 < t1 then
      let error := xCurve.sample t - x
      if error.abs < epsilon then t
      else
        let t0 := if error < 0 then t else t0
        let t1 := if error < 0 then t1 else t
        solveTBisectLoop x fuel t0 t1 ((t1 + t0) / 2)
    else t

/-- `CubicBezier.solveTBisect(x, initialT)`. The interval is halved every round, so after 64
rounds its ends are equal or adjacent `float`s. -/
def solveTBisect (x initialT : Float32) : Float32 := solveTBisectLoop x 64 0 1 initialT

/-- The loop of `CubicBezier.solveT(x)`: `n` more rounds of Newton's method from the guess `t`,
then bisection. -/
def solveTLoop (x : Float32) : ℕ → Float32 → Float32
  | 0, t => solveTBisect x t
  | n + 1, t =>
    let error := xCurve.sample t - x
    if error.abs < epsilon then t
    else
      let gradient := xCurve.sampleGradient t
      if gradient < epsilon then solveTBisect x t
      else solveTLoop x n (t - clamp (error / gradient) (-0.25) 0.25)

/-- `CubicBezier.apply(x)` for the easing of the sun angle. -/
def ease (x : Float32) : Float32 := yCurve.sample (solveTLoop x 4 x)

/-! ### The sun angle -/

/-- `EnvironmentAttributes.SUN_ANGLE` in degrees, when the overworld clock shows `clock`.

The track of the timeline `minecraft:day` has two keyframes at tick 6000, with values 360 and
0, and a period of 24000 ticks. `KeyframeTrackSampler` turns it into a segment from 0 at tick
-18000 to 360 at tick 6000 and a segment from 0 at tick 6000 to 360 at tick 30000: the angle is
0 at noon and grows through the day, eased by a cubic Bézier curve. -/
def sunAngle (clock : ℕ) : Float32 :=
  let t := clock % 24000
  if t = 6000 then 0
  else
    let elapsed := if t < 6000 then t + 18000 else t - 6000
    let alpha := Float32.ofNat elapsed / 24000
    lerp (ease alpha) 0 360

/-! ### The sky light level -/

/-- A segment of a baked keyframe track (`KeyframeTrackSampler.Segment`) with linear easing. -/
structure Segment where
  fromTicks : ℤ
  fromValue : Float32
  toTicks : ℤ
  toValue : Float32

/-- The segments of the track of `SKY_LIGHT_LEVEL` in the timeline `minecraft:day`. Its
keyframes are 1 at ticks 133 and 11867 and `nightFactor` at ticks 13670 and 22330. -/
def skyLightSegments : List Segment :=
  [⟨22330 - 24000, nightFactor, 133, 1⟩, ⟨133, 1, 11867, 1⟩, ⟨11867, 1, 13670, nightFactor⟩,
    ⟨13670, nightFactor, 22330, nightFactor⟩, ⟨22330, nightFactor, 133 + 24000, 1⟩]

/-- `KeyframeTrackSampler.sample` on one segment, with linear easing. -/
def Segment.sample (s : Segment) (t : ℤ) : Float32 :=
  if t ≤ s.fromTicks then s.fromValue
  else if t ≥ s.toTicks then s.toValue
  else
    let alpha := Float32.ofInt (t - s.fromTicks) / Float32.ofInt (s.toTicks - s.fromTicks)
    lerp alpha s.fromValue s.toValue

/-- `KeyframeTrackSampler.sample(ticks)` for the track of `SKY_LIGHT_LEVEL`: the factor by which
the time of day multiplies the sky light level. -/
def skyLightFactor (clock : ℕ) : Float32 :=
  let t : ℤ := clock % 24000
  match skyLightSegments.find? (t < ·.toTicks) with
  | some s => s.sample t
  | none => nightFactor

/-- `EnvironmentAttributes.SKY_LIGHT_LEVEL` (`getDimensionValue`): the default 15, multiplied by
the factor of the time of day, blended towards 4 by rain or by a thunderstorm
(`WeatherAttributes`), and brought into the range from 0 to 15. -/
def skyLightLevel (clock : ℕ) (weather : Weather) : Float32 :=
  let result := 15 * skyLightFactor clock
  let result :=
    match weather with
    | .clear => result
    | .rain => lerp 1 result (lerp rainAlpha result 4)
    | .thunder => lerp 1 result (lerp thunderAlpha result 4)
  if result ≥ 0 ∧ result ≤ 15 then result else clamp result 0 15

/-- `Level.skyDarken` as `Level.updateSkyBrightness` sets it: `(int) (15.0F - skyLightLevel)`.
It is 0 by day in clear weather and 11 at night. -/
def skyDarken (clock : ℕ) (weather : Weather) : ℕ :=
  (15 - skyLightLevel clock weather).toUInt8.toNat

/-! ### Cosine -/

/-- `Mth.cos(i)` for a `float` argument that is not negative: the entry
`(int) ((long) (i * SIN_SCALE + 16384.0) & 65535)` of the table `Mth.SIN`, whose entry `k` is
`(float) Math.sin(k / SIN_SCALE)`. -/
def cos (i : Float32) : Float32 :=
  let index := (i.toFloat * sinScale + 16384).floor.toUInt64.toNat % 65536
  (Float.sin (Float.ofNat index / sinScale)).toFloat32

/-- `Math.round(x)` for a `float`, cut off below at 0 and above at 15. -/
def roundClamped (x : Float32) : ℕ :=
  let r := (x.toFloat + 0.5).floor
  if r ≤ 0 then 0 else if r ≥ 15 then 15 else r.toUInt8.toNat

end Redstone.Component.Sensor.Sky
