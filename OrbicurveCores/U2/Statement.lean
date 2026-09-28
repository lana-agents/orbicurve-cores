/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Uniformization
import OrbicurveCores.Reconcile

/-!
# U2: the `ℂ`-level target

* `CanLift27C`: **[CanLift] Prop. 2.7 over `ℂ`**, in pi1's genuine form: for an elliptic curve
  `E / ℂ` with non-exceptional `j`, the punctured hemi-elliptic orbicurve `(E ∖ {0}) / {±1}` is
  the `ℂ`-core of `E ∖ {0}` (`AffOrbicurve.IsCoreOf`).
* `S1NonExceptional`: the part of S1 used for it: a once-punctured elliptic curve over `ℂ` with
  non-exceptional `j` is not uniformised by one of Takeuchi's four groups.

U2 proves `CanLift27C` (`OrbicurveCores.U2.canLift27C`, in `U2/Assembly.lean`) from
`S1NonExceptional` (which is `s1NonExceptional`, from S1). Passing from `ℂ` to arbitrary fields
of characteristic `0` (Lefschetz principle, descent) is separate.

Ingredients already proved in `lana-agents/oka` (branch `wp-u2`):
* **R3**: `Uniformization.Peripheral.commensurator_eq_pmDeck_or`: if the `±`-deck group `Γ̃` of the
  uniformisation of `ℂ/Λ ∖ 0` has finite index in its commensurator, then `Comm(Γ̃) = Γ̃`, unless
  `g₃(Λ) = 0` (`j = 1728`) or `g₂(Λ) = 0` (`j = 0`);
* the polynomial Riemann–Hurwitz count used for R3 and for uniqueness of the map to `hemi E`:
  `Uniformization.RatFuncPoly.orbifold_count` (a polynomial map `A¹ → A¹` for which `e · m` is
  constant on fibres, `m = 2` on a 3-element set `E₂`, has degree `1`, or degree `2` with `E₂`
  symmetric, or degree `3` with `E₂` equilateral) with `g₃_eq_zero_of_symm`,
  `g₂_eq_zero_of_cube`;
* K2 (`Peripheral.exists_monic_wpΨ_smul`), finite étale algebras over holomorphic functions on `ℍ`
  (`FEt.exists_isLift`, `FEt.exists_smul_eq`).
-/

open scoped MatrixGroups

namespace OrbicurveCores

/-- **S1, non-exceptional half**: a once-punctured elliptic curve over `ℂ` whose `j`-invariant
is not one of the four exceptional values is not uniformised by a Takeuchi group. -/
def S1NonExceptional : Prop :=
  ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (A B : SL(2, ℝ)), Uniformizes W A B →
    (∀ c ∈ AffOrbicurve.excJ, W.j ≠ (c : ℂ)) → ¬ IsTakeuchiConj A B

/-- **[CanLift] Prop. 2.7 over `ℂ`** (genuine cores): if `j(E)` is not exceptional, the punctured
hemi-elliptic orbicurve `(E ∖ {0}) / {±1}` is the `ℂ`-core of `E ∖ {0}`. -/
def CanLift27C : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], (∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : ℂ)) →
    AffOrbicurve.IsCoreOf (AffOrbicurve.punctured E) (AffOrbicurve.hemi E)

end OrbicurveCores
