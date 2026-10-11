/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.U2.Assembly
import OrbicurveCores.Genuine.Transfer.SpreadDescent
import OrbicurveCores.Genuine.AltU2

/-!
# [CanLift] Prop. 2.7 over every field of characteristic `0`, in every universe

`U2.canLift27C` proves [CanLift] Prop. 2.7 over `ℂ` (`CanLift27C`). The transfer
`hemiCoreTransfer : HemiCoreTransfer` (`Genuine/Transfer/`, spreading out to a subfield
`k₀ ⊆ ℂ` with `k₀ : Type`, base change of affine orbicurves, and descent of the core property
along `k₀ → k` for `k` in an arbitrary universe) carries it to every field of characteristic `0`:

* `canLift27 : AffOrbicurve.CanLift27.{u}`: pi1's form (the core of `E ∖ {0}` is
  `(E ∖ {0}) / {±1}` for non-exceptional `j`), for fields `k : Type u` in every universe `u`;
* `canLift27Genuine : CanLift27Genuine.{u}`: the [EstIUT] Prop. 2.1 form (`k`-arithmetic
  `E ∖ {0}` has exceptional `j`).

pi1's Lefschetz principle `AffOrbicurve.canLift27_of_complex` gives the same conclusion for
fields in `Type` (`CanLift27.{0}`); the transfer here also covers fields in higher universes.

`Alt.canLift27Genuine` is the same statement obtained from the alternative proof over `ℂ`
(`Alt.canLift27C`, `Genuine/AltU2.lean`).
-/

universe u

namespace OrbicurveCores

/-- **[CanLift] Proposition 2.7** (pi1's form), over every field of characteristic `0` in every
universe: for `j(E)` not exceptional, `(E ∖ {0}) / {±1}` is the `k`-core of `E ∖ {0}`. -/
theorem canLift27 : AffOrbicurve.CanLift27.{u} :=
  hemiCoreTransfer U2.canLift27C

/-- **[CanLift] Proposition 2.7, genuine form** ([EstIUT] Prop. 2.1): for an elliptic curve `E`
over a field of characteristic `0`, if `E ∖ {0}` has no `k`-core then `j(E)` is exceptional. -/
theorem canLift27Genuine : CanLift27Genuine.{u} :=
  canLift27Genuine_of_canLift27 canLift27

/-- `CanLift27Genuine` along the alternative route over `ℂ` (`Alt.canLift27C`). -/
theorem Alt.canLift27Genuine : CanLift27Genuine.{u} :=
  canLift27Genuine_of_canLift27 (hemiCoreTransfer Alt.canLift27C)

end OrbicurveCores
