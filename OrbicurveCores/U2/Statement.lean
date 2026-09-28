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

U2 proves `CanLift27C` from `S1NonExceptional` (`canLift27C_of_s1`, in progress). Passing from
`ℂ` to arbitrary fields of characteristic `0` (Lefschetz principle, descent) is separate.
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
