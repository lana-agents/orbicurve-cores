/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Classification
import OrbicurveCores.Fuchsian.OneInftyLattice

/-!
# The group-level form of [CanLift] Prop. 2.7, conditional only on Margulis

`OrbicurveCores.canLift27_group_iff`: assuming Margulis' commensurator theorem in its standard
form (`MargulisDenseOneInfty`: a dense commensurator forces arithmeticity), a once-punctured torus
group `⟨A, B⟩ ⊆ SL(2, ℝ)` admits no core iff it is one of Takeuchi's four groups.

The other ingredients are proved: finite covolume of once-punctured torus groups
(`Fuchsian.oneInftyFiniteCovolume`), infinite commensurator index ⇒ dense commensurator
(`Fuchsian.commensurator_dense`), Takeuchi's classification, and sharpness.
-/

open Matrix
open scoped MatrixGroups

namespace OrbicurveCores

/-- **[CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1, group-theoretic form**, conditional only on
Margulis' commensurator theorem (dense form). -/
theorem canLift27_group_iff (hM : MargulisDenseOneInfty) {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0) :
    ¬ AdmitsCore (Subgroup.closure {A, B}) ↔ IsTakeuchiConj A B :=
  not_admitsCore_iff_isTakeuchiConj (margulisOneInfty_of_margulisDense hM) hcomm hA

end OrbicurveCores
