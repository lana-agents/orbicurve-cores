/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.GroupMain
import OrbicurveCores.M2.Final

/-!
# The group-level form of [CanLift] Prop. 2.7, unconditionally

Margulis' commensurator theorem for once-punctured torus groups is proved in `M2/`
(`M2.margulisDenseOneInfty`). Hence, unconditionally: a once-punctured torus group
`⟨A, B⟩ ⊆ SL(2, ℝ)` (`tr [A, B] = -2`, `tr A ≠ 0`) admits no core iff it is, up to Nielsen moves,
signs and `GL(2, ℝ)`-conjugacy, one of Takeuchi's four arithmetic groups (`canLift27_group`).
These four groups uniformise the once-punctured elliptic curves with
`j = 2¹⁴·31³/5³, 2²·73³/3⁴, 1728, 0` ([Sijs] Table 4).
-/

open Matrix
open scoped MatrixGroups

namespace OrbicurveCores

/-- **Margulis' theorem for once-punctured torus groups**, in the form used by `Core.lean`:
without a core, the group is arithmetic. -/
theorem margulisOneInfty : MargulisOneInfty :=
  margulisOneInfty_of_margulisDense M2.margulisDenseOneInfty

/-- **[CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1, group-theoretic form (unconditional).** A
once-punctured torus group admits no core iff it is one of Takeuchi's four groups. -/
theorem canLift27_group_unconditional {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) : ¬ AdmitsCore (Subgroup.closure {A, B}) ↔ IsTakeuchiConj A B :=
  canLift27_group_iff M2.margulisDenseOneInfty hcomm hA

end OrbicurveCores
