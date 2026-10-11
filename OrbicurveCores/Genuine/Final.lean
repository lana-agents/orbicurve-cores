/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.TranslationCase

/-!
# `CanLift27Genuine` from the remaining four interfaces

Combining `commIndexFour_of_translationCase` (R3b–R3c) with `canLift27Genuine_of'`:
`CanLift27Genuine` follows from

* `TranslationCase` (R3d): a normal-form once-punctured torus group whose commensurator contains
  `z ↦ z + 1/m`, `m ≥ 2`, has no core;
* `U2Descent`, `U2Rigidity` (the analytic halves of U2 over `ℂ`);
* `HemiCoreTransfer` ([CanLift] Prop. 2.3 and the Lefschetz principle).

R3d is proved (`translationCase`, `Genuine/TranslationCase.lean`), so `CanLift27Genuine` follows
from the remaining three interfaces (`canLift27Genuine_of_U2_transfer`).
-/

universe u

namespace OrbicurveCores

/-- **`CanLift27Genuine` from R3d, the two analytic halves of U2, and the transfer.** -/
theorem canLift27Genuine_of_remaining (hR3d : TranslationCase) (hD : U2Descent)
    (hR : U2Rigidity) (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of' (commIndexFour_of_translationCase hR3d) hD hR hT

/-- **`CanLift27Genuine` from the two analytic halves of U2 and the transfer** (R3 is proved). -/
theorem canLift27Genuine_of_U2_transfer (hD : U2Descent) (hR : U2Rigidity)
    (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of_remaining translationCase hD hR hT

end OrbicurveCores
