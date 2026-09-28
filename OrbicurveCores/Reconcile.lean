/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.JValues
import Pi1.Orbicurve.Elliptic

/-!
# Reconciliation with the genuine `k`-cores of `lana-agents/pi1`

`lana-agents/pi1` (branch `wp-orbicurve-pi1`) defines affine orbicurves, their finite étale
morphisms, `\overline{Loc}_k(X)` and `k`-cores following [CanLift] Def. 2.1
(`AffOrbicurve.IsCoreOf`, `AffOrbicurve.IsArithmetic`). It also defines the once-punctured
elliptic curve `AffOrbicurve.punctured E`, its hemi-elliptic quotient `AffOrbicurve.hemi E`,
the exceptional set `AffOrbicurve.excJ`, and the statement `AffOrbicurve.CanLift27`: the `k`-core
of `E ∖ {0}` is `(E ∖ {0})/±1` unless `j(E)` is exceptional.

This file shows:

* `exceptionalJ_eq_excJ`: both repositories use the same four exceptional values;
* `canLift27Genuine_of_canLift27`: pi1's `CanLift27` implies the [EstIUT] Prop. 2.1 form
  `CanLift27Genuine` (no `k`-core ⇒ exceptional `j`), phrased with the genuine notion of core.
-/

universe u

namespace OrbicurveCores

/-- The two definitions of the exceptional set agree. -/
lemma exceptionalJ_eq_excJ : exceptionalJ = AffOrbicurve.excJ := by
  rw [exceptionalJ_eq]; rfl

/-- **[EstIUT] Prop. 2.1 / [CanLift] Prop. 2.7 with genuine cores**: if the once-punctured
elliptic curve `E ∖ {0}` over a field of characteristic `0` is `k`-arithmetic (has no `k`-core in
the sense of [CanLift] Def. 2.1), then `j(E)` is exceptional. Not proved here. -/
def CanLift27Genuine : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic],
    AffOrbicurve.IsArithmetic (AffOrbicurve.punctured E) → IsExceptionalJ E.j

/-- pi1's form of [CanLift] Prop. 2.7 (the core is the hemi-elliptic quotient for
non-exceptional `j`) implies the [EstIUT] form. -/
theorem canLift27Genuine_of_canLift27 (h : AffOrbicurve.CanLift27.{u}) :
    CanLift27Genuine.{u} := by
  intro k _ _ E _ harith
  by_contra hj
  apply harith
  refine ⟨AffOrbicurve.hemi E, h k E fun c hc hjc ↦ hj ⟨c, ?_, hjc.symm⟩⟩
  rw [exceptionalJ_eq_excJ]; exact hc

end OrbicurveCores
