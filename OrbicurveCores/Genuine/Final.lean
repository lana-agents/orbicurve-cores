/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.CommIndex
import OrbicurveCores.Genuine.Descent

/-!
# `CanLift27Genuine` from the remaining four interfaces

Combining `commIndexFour_of_translationCase` (R3b–R3c) with `canLift27Genuine_of'`:
`CanLift27Genuine` follows from

* `TranslationCase` (R3d): a normal-form once-punctured torus group whose commensurator contains
  `z ↦ z + 1/m`, `m ≥ 2`, has no core;
* `U2Descent`, `U2Rigidity` (the analytic halves of U2 over `ℂ`);
* `HemiCoreTransfer` ([CanLift] Prop. 2.3 and the Lefschetz principle).

By U2b (`Genuine.hemiDescends_of`), `U2Descent` follows from `U2Rigidity` and the algebraic
statement `Genuine.CompositumSeparates ℂ` (Abhyankar's lemma), so `CanLift27Genuine` follows from
`TranslationCase`, `U2Rigidity`, `CompositumSeparates ℂ` and `HemiCoreTransfer`
(`canLift27Genuine_of_remaining'`).
-/

universe u

namespace OrbicurveCores

/-- **`CanLift27Genuine` from R3d, the two analytic halves of U2, and the transfer.** -/
theorem canLift27Genuine_of_remaining (hR3d : TranslationCase) (hD : U2Descent)
    (hR : U2Rigidity) (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of' (commIndexFour_of_translationCase hR3d) hD hR hT

/-- **U2b.** The descent half of U2 from the rigidity half and Abhyankar's lemma. -/
theorem u2Descent_of (hR : U2Rigidity) (hC : Genuine.CompositumSeparates ℂ) : U2Descent :=
  fun E _ A B hc hA hU hi ↦ Genuine.hemiDescends_of E (hR E A B hc hA hU hi) hC

/-- **`CanLift27Genuine` from R3d, U2 rigidity, Abhyankar's lemma over `ℂ`, and the
transfer.** -/
theorem canLift27Genuine_of_remaining' (hR3d : TranslationCase) (hR : U2Rigidity)
    (hC : Genuine.CompositumSeparates ℂ) (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of_remaining hR3d (u2Descent_of hR hC) hR hT

end OrbicurveCores
