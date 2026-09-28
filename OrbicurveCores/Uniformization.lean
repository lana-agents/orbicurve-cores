/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Oka.Uniformization.OncePunctured
import OrbicurveCores.GroupCanLift

/-!
# U1: every once-punctured elliptic curve over `ℂ` is uniformised by a once-punctured torus group

This file consumes `Uniformization.uniformization_oncePunctured` (from `lana-agents/oka`): for an
elliptic curve `E : y² = …` over `ℂ`, the affine curve `E ∖ {O}` is `ℍ / ⟨A, B⟩` with
`tr [A, B] = -2`, via a locally biholomorphic surjection `π : ℍ → E ∖ {O}` whose fibres are exactly
the `⟨A, B⟩`-orbits.

* `uniformization`: the U1 statement restated with the project's `tr`;
* `exists_uniformization_core_iff`: combined with `canLift27_group_unconditional`, every such
  uniformising group admits no core iff it is one of Takeuchi's four groups.

Identifying *which* curves have Takeuchi uniformising groups (S1: `j(E)` in the exceptional set)
and that the uniformising group is well defined up to conjugacy (U2) are separate steps.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace OrbicurveCores

/-- A pair `(A, B)` uniformises the once-punctured elliptic curve `W ∖ {O}`: there is a locally
biholomorphic `π : ℍ → W ∖ {O}` onto the affine points whose fibres are the `⟨A, B⟩`-orbits. -/
def Uniformizes (W : WeierstrassCurve ℂ) (A B : SL(2, ℝ)) : Prop :=
  ∃ π : ℂ → ℂ × ℂ,
    (∀ z : ℍ, DifferentiableAt ℂ π z ∧ deriv π z ≠ 0) ∧
    (∀ z : ℍ, W.toAffine.Equation (π z).1 (π z).2) ∧
    (∀ x y : ℂ, W.toAffine.Equation x y → ∃ z : ℍ, π z = (x, y)) ∧
    (∀ z w : ℍ, π z = π w ↔ ∃ γ ∈ Subgroup.closure {A, B}, γ • z = w)

/-- **U1.** Every once-punctured elliptic curve over `ℂ` is uniformised by a once-punctured torus
group `⟨A, B⟩` (`tr [A, B] = -2`, `tr A ≠ 0`). -/
theorem uniformization (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ A B : SL(2, ℝ), tr (A * B * A⁻¹ * B⁻¹) = -2 ∧ tr A ≠ 0 ∧ Uniformizes W A B := by
  obtain ⟨A, B, π, hc, hA, h1, h2, h3, h4⟩ := Uniformization.uniformization_oncePunctured W
  exact ⟨A, B, hc, hA, π, h1, h2, h3, h4⟩

/-- **[CanLift] Prop. 2.7, group form, for the uniformising group of a curve.** Every
once-punctured elliptic curve over `ℂ` has a uniformising once-punctured torus group, and any such
group admits no core iff it is one of Takeuchi's four groups. -/
theorem exists_uniformization_core_iff (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ A B : SL(2, ℝ), tr (A * B * A⁻¹ * B⁻¹) = -2 ∧ tr A ≠ 0 ∧ Uniformizes W A B ∧
      (¬ AdmitsCore (Subgroup.closure {A, B}) ↔ IsTakeuchiConj A B) := by
  obtain ⟨A, B, hc, hA, hU⟩ := uniformization W
  exact ⟨A, B, hc, hA, hU, canLift27_group_unconditional hc hA⟩

end OrbicurveCores
