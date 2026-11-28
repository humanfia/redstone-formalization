module

public import Redstone.Component.Button

/-!
# Lemmas about the button

Generic facts about one component, over an arbitrary level; the pulses of concrete circuits
are in `Redstone/Theorems/Pulse/ButtonPulse.lean`.

* **Attribute lemmas.** A button stays down for 20 game ticks if arrows cannot press it (the
  two buttons of stone) and for 30 otherwise (`ticksToStayPressed_eq`,
  `ticksToStayPressed_mem`); a button that is down gives 15 to every neighbour and strong power
  to the block it is attached to only (`signal_button`, `directSignal_button`); no arrow holds
  a button of stone, or any button in a level without entities (`hasArrow_of_stone`,
  `hasArrow_of_no_entities`).
* **Single-reaction lemmas.**
  * `press_schedules`: **a button schedules its release.** After the button has gone down and
    its neighbours have been told (`pressed`), `press` adds exactly one scheduled tick at the
    button, due `ticksToStayPressed` game ticks later, with normal priority, and then announces
    the game event; it changes nothing else in the level but the counter that orders the ticks.
  * `use_of_pressed`: a button that is down ignores the player.
  * `tick_of_unpressed`: the scheduled tick of a button that is up does nothing.
  * `checkPressed_releases`: the tick of a button that is down and that no arrow touches
    releases it and schedules nothing more; `checkPressed_holds`: while an arrow touches it,
    the tick only schedules the next check.

Left out: the whole pulse over an arbitrary level ("the button is up again exactly 20 game
ticks later"). Between the press and the release the rest of the level runs, and the lemma
would have to know that nothing else touches the button or its scheduled tick; that is proved
for concrete circuits by evaluation.
-/

@[expose] public section

namespace Redstone.Component.Button

/-- How a program of the model that is a `bind` runs: the first part, then the second from the
level the first one leaves. -/
theorem bind_apply {α β : Type} (m : M α) (k : α → M β) (env : Env) (l : Level) :
    (m >>= k) env l = k (m env l).1 env (m env l).2 := rfl

/-- What `Level.scheduleTick` does when no tick of the block is waiting at the position: one
more scheduled tick, due `delay` game ticks from now, and the counter that orders the ticks
moves on. -/
theorem scheduleTick_apply (p : Pos) (block : BlockId) (delay : ℕ) (priority : TickPriority)
    (env : Env) (l : Level) (h : l.hasScheduledTick p block = false) :
    Level.scheduleTick p block delay priority env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, block, l.gameTime + delay, priority, l.subTickCount⟩] }) := by
  have h' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p block
      = false := h
  simp only [Level.scheduleTick, modify, modifyGet, MonadStateOf.modifyGet, monadLift,
    MonadLift.monadLift, StateT.modifyGet, pure, h', Bool.false_eq_true, ite_false]

/-! ### Attribute lemmas -/

/-- A button that arrows can press (a wooden one) stays down for 30 game ticks, the others (of
stone) for 20. -/
theorem ticksToStayPressed_eq (id : Blocks.Button.Id) :
    ticksToStayPressed id = if canButtonBeActivatedByArrows id then 30 else 20 := by
  cases id <;> rfl

/-- A button stays down for 20 or for 30 game ticks. -/
theorem ticksToStayPressed_mem (id : Blocks.Button.Id) : ticksToStayPressed id ∈ [20, 30] := by
  cases id <;> simp [ticksToStayPressed]

/-- The stone button stays down for 20 game ticks. -/
theorem ticksToStayPressed_stone : ticksToStayPressed .stone_button = 20 := rfl

/-- The oak button stays down for 30 game ticks. -/
theorem ticksToStayPressed_oak : ticksToStayPressed .oak_button = 30 := rfl

/-- A button gives a signal of 15 to every neighbour while it is down, and none while it is
up. -/
theorem signal_button (id : Blocks.Button.Id) (s : Blocks.Button) (l : Level) (p : Pos)
    (d : Direction) : (button id s).signal l p d = if s.powered then 15 else 0 := rfl

/-- A button gives strong power only to the block it is attached to (the direction `d` points
from that block to the button), and only while it is down. -/
theorem directSignal_button (id : Blocks.Button.Id) (s : Blocks.Button) (l : Level) (p : Pos)
    (d : Direction) :
    (button id s).directSignal l p d =
      if s.powered && connectedDirection s = d then 15 else 0 := rfl

/-- A button that arrows cannot press is never held down by one. -/
theorem hasArrow_of_stone (id : Blocks.Button.Id) (s : Blocks.Button) (l : Level) (p : Pos)
    (h : canButtonBeActivatedByArrows id = false) : hasArrow id s l p = false := by
  simp [hasArrow, h]

/-- In a level without entities no arrow holds a button down. -/
theorem hasArrow_of_no_entities (id : Blocks.Button.Id) (s : Blocks.Button) (l : Level)
    (p : Pos) (h : l.entities = []) : hasArrow id s l p = false := by
  simp [hasArrow, h]

/-! ### Single-reaction lemmas -/

/-- The first half of `press`: the button goes down and its neighbours, and those of the block
it is attached to, are told. -/
def pressed (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) : M Unit := do
  discard <| Level.setBlock p (.button id { s with powered := true })
  updateNeighbours id s p

/-- **A button schedules its release.** Let `l'` be the level after the button at `p` has gone
down and the neighbours have reacted (`pressed`), and let no tick of the button be waiting in
`l'`. Then `press` leaves `l'` with one more scheduled tick, at `p`, due `ticksToStayPressed`
game ticks (20 or 30) after the game time of `l'`, with normal priority, and announces the
game event `block_activate` on that level. -/
theorem press_schedules (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) (env : Env)
    (l : Level)
    (hsched : (pressed id s p env l).2.hasScheduledTick p id.toBlockId = false) :
    press id s p env l =
      (Level.gameEvent "minecraft:block_activate" p : M Unit) env
        { (pressed id s p env l).2 with
          subTickCount := (pressed id s p env l).2.subTickCount + 1
          ticks := (pressed id s p env l).2.ticks ++
            [⟨p, id.toBlockId, (pressed id s p env l).2.gameTime + ticksToStayPressed id, .normal,
              (pressed id s p env l).2.subTickCount⟩] } := by
  have h : press id s p =
      pressed id s p >>= fun _ =>
        Level.scheduleTick p id.toBlockId (ticksToStayPressed id) >>= fun _ =>
          Level.gameEvent "minecraft:block_activate" p := by
    simp only [press, pressed, bind_assoc]
  rw [h, bind_apply, bind_apply, scheduleTick_apply _ _ _ _ _ _ hsched]

/-- **A button that is down ignores the player**: using it does nothing, and the use counts as
handled. -/
theorem use_of_pressed (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) (face : Direction)
    (h : s.powered = true) : (button id s).useWithoutItem p face = pure true := by
  simp [button, h]

/-- Using a button that is up presses it. -/
theorem use_of_unpressed (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos)
    (face : Direction) (h : s.powered = false) :
    (button id s).useWithoutItem p face = (do press id s p; return true) := by
  simp [button, h]

/-- The scheduled tick of a button that is up does nothing. -/
theorem tick_of_unpressed (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos)
    (h : s.powered = false) : (button id s).tick p = pure () := by
  simp [button, h]

/-- The scheduled tick of a button that is down is `checkPressed`. -/
theorem tick_of_pressed (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos)
    (h : s.powered = true) : (button id s).tick p = checkPressed id s p := by
  simp [button, h]

/-- **The release.** When no arrow touches a button that is down, `checkPressed` (its scheduled
tick) lets it come up, tells the neighbours and announces the game event `block_deactivate`.
It schedules nothing: the button stays up until it is pressed again. -/
theorem checkPressed_releases (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) (env : Env)
    (l : Level) (hs : s.powered = true) (harrow : hasArrow id s l p = false) :
    checkPressed id s p env l =
      (do
        discard <| Level.setBlock p (.button id { s with powered := false })
        updateNeighbours id s p
        Level.gameEvent "minecraft:block_deactivate" p : M Unit) env l := by
  have h : checkPressed id s p env l =
      (do
        if hasArrow id s l p != s.powered then
          discard <| Level.setBlock p (.button id { s with powered := hasArrow id s l p })
          updateNeighbours id s p
          Level.gameEvent
            (if hasArrow id s l p then "minecraft:block_activate"
              else "minecraft:block_deactivate") p
        if hasArrow id s l p then Level.scheduleTick p id.toBlockId (ticksToStayPressed id)
          : M Unit) env l := rfl
  rw [h, harrow, hs]
  simp

/-- **A button held by an arrow.** While an arrow touches a button that is down, `checkPressed`
leaves the button as it is and only schedules the next check, `ticksToStayPressed` game ticks
ahead. -/
theorem checkPressed_holds (id : Blocks.Button.Id) (s : Blocks.Button) (p : Pos) (env : Env)
    (l : Level) (hs : s.powered = true) (harrow : hasArrow id s l p = true) :
    checkPressed id s p env l =
      (Level.scheduleTick p id.toBlockId (ticksToStayPressed id) : M Unit) env l := by
  have h : checkPressed id s p env l =
      (do
        if hasArrow id s l p != s.powered then
          discard <| Level.setBlock p (.button id { s with powered := hasArrow id s l p })
          updateNeighbours id s p
          Level.gameEvent
            (if hasArrow id s l p then "minecraft:block_activate"
              else "minecraft:block_deactivate") p
        if hasArrow id s l p then Level.scheduleTick p id.toBlockId (ticksToStayPressed id)
          : M Unit) env l := rfl
  rw [h, harrow, hs]
  simp

end Redstone.Component.Button
