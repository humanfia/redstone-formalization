module

public import Redstone.Component.Lamp

/-!
# Lemmas about the copper bulb

Generic facts about one component (`Redstone.Component.Lamp`, the part for
`CopperBulbBlock`), over an arbitrary level. The theorems about concrete circuits with bulbs
are in `Redstone/Theorems/Memory` (`CopperBulbTFF`, `RippleCounter`).

* **The state machine.** `bulbNext lit powered signal` is the pair `(lit, powered)` a bulb has
  after it looks at its signal. A rising edge switches `lit`, a falling edge only clears
  `powered`, and a signal that agrees with `powered` changes nothing (`bulbNext_rising`,
  `bulbNext_falling`, `bulbNext_of_agrees`); `powered` always ends up equal to the signal
  (`bulbNext_powered`); two rising edges, with the falling edges between them, bring the bulb
  back to the state it started in (`bulbNext_four_edges`), and one pulse switches `lit` and
  leaves `powered` off (`bulbNext_pulse`).
* **Single-reaction lemmas.** What `checkAndFlip`, the reaction of the bulb to a neighbour
  update, does to an arbitrary level: nothing when the signal agrees with `powered`
  (`checkAndFlip_of_agrees`); otherwise one `Level.setBlock` of the bulb in the state `bulbNext`
  (`checkAndFlip_eq`, with the two cases `checkAndFlip_rising` and `checkAndFlip_falling`).
  The signal is `Level.hasNeighborSignalAt`, a function of the level: the reaction reads the
  level and does not change it before the `setBlock`.
* **The comparator output.** A comparator reads 15 from a lit bulb and 0 from an unlit one
  (`analogSignal_bulb`), for both families of bulbs (`analogSignal_copperBulb`,
  `analogSignal_weatheringCopperBulb`); a bulb gives no redstone signal itself (`signal_bulb`).

Left out: what the `Level.setBlock` of `checkAndFlip` does to the rest of the level (the
neighbour updates it sends reach arbitrary blocks), and so a lemma "the bulb at `p` is lit
after the tick" over an arbitrary level. That is proved for concrete circuits by evaluation.
-/

@[expose] public section

namespace Redstone.Component.Lamp

/-! ### The state machine -/

/-- The properties `(lit, powered)` of a bulb after it has looked at its signal:
`CopperBulbBlock.checkAndFlip` as a function of the state. -/
def bulbNext (lit powered signal : Bool) : Bool × Bool :=
  if signal != powered then (if !powered then !lit else lit, signal) else (lit, powered)

/-- **Rising edge.** A bulb that was not powered and gets a signal switches its light. -/
theorem bulbNext_rising (lit : Bool) : bulbNext lit false true = (!lit, true) := rfl

/-- **Falling edge.** A bulb that was powered and loses its signal keeps its light and only
records that the signal is gone. -/
theorem bulbNext_falling (lit : Bool) : bulbNext lit true false = (lit, false) := rfl

/-- A signal that agrees with `powered` changes nothing. -/
theorem bulbNext_of_agrees (lit powered : Bool) :
    bulbNext lit powered powered = (lit, powered) := by
  simp [bulbNext]

/-- After the bulb has looked at its signal, `powered` is the signal. -/
theorem bulbNext_powered (lit powered signal : Bool) :
    (bulbNext lit powered signal).2 = signal := by
  cases lit <;> cases powered <;> cases signal <;> rfl

/-- The light changes exactly on a rising edge. -/
theorem bulbNext_lit (lit powered signal : Bool) :
    (bulbNext lit powered signal).1 = if signal && !powered then !lit else lit := by
  cases lit <;> cases powered <;> cases signal <;> rfl

/-- **One pulse switches the light.** A rising edge and then a falling edge, from a bulb that
is not powered: the light is switched and the bulb is not powered again. -/
theorem bulbNext_pulse (lit : Bool) :
    bulbNext (bulbNext lit false true).1 (bulbNext lit false true).2 false = (!lit, false) := rfl

/-- **Four edges return to the start.** Two pulses (rising, falling, rising, falling) bring a
bulb that is not powered back to the state it started in: the bulb is a divider by two. -/
theorem bulbNext_four_edges (lit : Bool) :
    let s₁ := bulbNext lit false true
    let s₂ := bulbNext s₁.1 s₁.2 false
    let s₃ := bulbNext s₂.1 s₂.2 true
    let s₄ := bulbNext s₃.1 s₃.2 false
    s₄ = (lit, false) := by
  cases lit <;> rfl

/-! ### Single-reaction lemmas -/

/-- **`checkAndFlip` in one equation.** The bulb reads its signal; when the signal is not what
`powered` says, the bulb is set to the state `bulbNext`, and otherwise nothing happens. -/
theorem checkAndFlip_eq (mk : Bool → Bool → Block) (lit powered : Bool) (p : Pos) (env : Env)
    (l : Level) :
    checkAndFlip mk lit powered p env l =
      if l.hasNeighborSignalAt env p = powered then ((), l)
      else ((), (Level.setBlock p (mk (bulbNext lit powered (l.hasNeighborSignalAt env p)).1
        (bulbNext lit powered (l.hasNeighborSignalAt env p)).2) UpdateFlag.all 512 env l).2) := by
  unfold checkAndFlip Level.hasNeighborSignal
  by_cases h : l.hasNeighborSignalAt env p = powered
  · simp [h, bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, StateT.get, read, readThe, MonadReaderOf.read, ReaderT.read, pure,
      ReaderT.pure, StateT.pure]
  · have h' : (l.hasNeighborSignalAt env p != powered) = true := by simpa using h
    simp only [h, h', bulbNext, discard, Functor.discard, bind, ReaderT.bind, StateT.bind, get,
      getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, read, readThe,
      MonadReaderOf.read, ReaderT.read, pure, ReaderT.pure, StateT.pure, ite_true, ite_false]
    rfl

/-- **A bulb whose signal agrees with `powered` does nothing**: the level is left as it is. -/
theorem checkAndFlip_of_agrees (mk : Bool → Bool → Block) (lit powered : Bool) (p : Pos)
    (env : Env) (l : Level) (h : l.hasNeighborSignalAt env p = powered) :
    checkAndFlip mk lit powered p env l = ((), l) := by
  simp [checkAndFlip_eq, h]

/-- **Rising edge: the light toggles.** A bulb that is not powered and now receives a signal
is set to the state with the light switched and `powered` on; that one `Level.setBlock` is all
the reaction does. -/
theorem checkAndFlip_rising (mk : Bool → Bool → Block) (lit : Bool) (p : Pos) (env : Env)
    (l : Level) (h : l.hasNeighborSignalAt env p = true) :
    checkAndFlip mk lit false p env l =
      ((), (Level.setBlock p (mk (!lit) true) UpdateFlag.all 512 env l).2) := by
  simp [checkAndFlip_eq, h, bulbNext]

/-- **Falling edge: `powered` is cleared, the light stays.** A bulb that is powered and has
lost its signal is set to the state with the same light and `powered` off. -/
theorem checkAndFlip_falling (mk : Bool → Bool → Block) (lit : Bool) (p : Pos) (env : Env)
    (l : Level) (h : l.hasNeighborSignalAt env p = false) :
    checkAndFlip mk lit true p env l =
      ((), (Level.setBlock p (mk lit false) UpdateFlag.all 512 env l).2) := by
  simp [checkAndFlip_eq, h, bulbNext]

/-- The reaction of a bulb to a neighbour update is `checkAndFlip`, whatever the neighbour. -/
theorem neighborChanged_bulb (mk : Bool → Bool → Block) (lit powered : Bool) (p : Pos)
    (b : BlockId) (moved : Bool) :
    (bulb mk lit powered).neighborChanged p b moved = checkAndFlip mk lit powered p := rfl

/-! ### The comparator output -/

/-- A comparator reads 15 from a bulb whose state in the level is lit, and 0 otherwise. -/
theorem analogSignal_bulb (mk : Bool → Bool → Block) (lit powered : Bool) (l : Level) (p : Pos)
    (d : Direction) :
    (bulb mk lit powered).analogSignal l p d =
      if bulbLit? (l.blockAt p) = some true then 15 else 0 :=
  rfl

/-- The comparator output of a copper bulb at `p` is 15 exactly when the bulb is lit. -/
theorem analogSignal_copperBulb (id : Blocks.CopperBulb.Id) (s s' : Blocks.CopperBulb)
    (l : Level) (p : Pos) (d : Direction) (h : l.blockAt p = .copperBulb id s') :
    (behaviour (.copperBulb id s)).analogSignal l p d = if s'.lit = true then 15 else 0 := by
  change (if bulbLit? (l.blockAt p) = some true then 15 else 0) = _
  rw [h]
  simp [bulbLit?]

/-- The comparator output of a copper bulb that oxidizes, at `p`, is 15 exactly when the bulb
is lit. -/
theorem analogSignal_weatheringCopperBulb (id : Blocks.WeatheringCopperBulb.Id)
    (s s' : Blocks.WeatheringCopperBulb) (l : Level) (p : Pos) (d : Direction)
    (h : l.blockAt p = .weatheringCopperBulb id s') :
    (behaviour (.weatheringCopperBulb id s)).analogSignal l p d =
      if s'.lit = true then 15 else 0 := by
  change (if bulbLit? (l.blockAt p) = some true then 15 else 0) = _
  rw [h]
  simp [bulbLit?]

/-- A bulb gives no redstone signal of its own: only a comparator reads it. -/
theorem signal_bulb (mk : Bool → Bool → Block) (lit powered : Bool) (l : Level) (p : Pos)
    (d : Direction) : (bulb mk lit powered).signal l p d = 0 := rfl

end Redstone.Component.Lamp
