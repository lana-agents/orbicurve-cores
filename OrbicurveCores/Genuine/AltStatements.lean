/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Uniformization
import OrbicurveCores.Genuine.HemiCore

/-!
# U2 over `ℂ` along the alternative route: statements

The alternative proof of [CanLift] Prop. 2.7 over `ℂ` (`Alt.canLift27C`, `Genuine/AltU2.lean`)
splits U2 into a descent and a rigidity half for a uniformisation `(A, B)` of `E ∖ {0}` with
`[Comm(⟨A, B⟩) : ⟨A, B⟩] = 4` (which is R3, `commIndexFour`):

* `HemiCoreComplex`: `(E ∖ {0}) / ±1` is then the `ℂ`-core of `E ∖ {0}`;
* `U2Descent`: the `x`-coordinate of a finite étale cover `Z → E ∖ {0}` descends along every
  finite étale `Z → Y` (`Genuine.HemiDescends`);
* `U2Rigidity`: every finite étale `Z → (E ∖ 0)/±1` from a finite étale cover
  `p : Z → E ∖ 0` is `x ∘ p` (`Genuine.HemiRigid`).

`hemiCoreComplex_of` combines the halves (`Genuine.isCoreOf_hemi_of`).
-/

open Matrix
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace OrbicurveCores.Alt

/-- **U2 over `ℂ`**: if `(A, B)` uniformises `E ∖ {0}` and `Comm(⟨A, B⟩) : ⟨A, B⟩` has index `4`,
then the punctured hemi-elliptic orbicurve is the `ℂ`-core of `E ∖ {0}` in the sense of
[CanLift] Def. 2.1. -/
def HemiCoreComplex : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic] (A B : SL(2, ℝ)),
    tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 → Uniformizes E A B →
      (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) = 4 →
        AffOrbicurve.IsCoreOf (AffOrbicurve.punctured E) (AffOrbicurve.hemi E)

/-- **U2, descent half, over `ℂ`**: with the hypotheses of `HemiCoreComplex`, the
`x`-coordinate of a finite étale cover `Z → E ∖ 0` descends along every finite étale `Z → Y`. -/
def U2Descent : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic] (A B : SL(2, ℝ)),
    tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 → Uniformizes E A B →
      (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) = 4 →
        Genuine.HemiDescends E

/-- **U2, rigidity half, over `ℂ`**: with the hypotheses of `HemiCoreComplex`, every finite étale
`Z → (E ∖ 0)/±1` from a finite étale cover `p : Z → E ∖ 0` is `x ∘ p`. -/
def U2Rigidity : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic] (A B : SL(2, ℝ)),
    tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 → Uniformizes E A B →
      (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) = 4 →
        Genuine.HemiRigid E

/-- U2 over `ℂ` from its descent and rigidity halves (`Genuine.isCoreOf_hemi_of`). -/
theorem hemiCoreComplex_of (hD : U2Descent) (hR : U2Rigidity) : HemiCoreComplex :=
  fun E _ A B hc hA hU hi ↦
    Genuine.isCoreOf_hemi_of E (hD E A B hc hA hU hi) (hR E A B hc hA hU hi)

end OrbicurveCores.Alt
