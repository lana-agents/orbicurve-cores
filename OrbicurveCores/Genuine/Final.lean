/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.TranslationCase
import OrbicurveCores.Genuine.CommIndex
import OrbicurveCores.Genuine.Descent
import OrbicurveCores.Genuine.Rigid.Main
import OrbicurveCores.Genuine.Abhyankar.Separates
import OrbicurveCores.Genuine.Transfer.SpreadDescent

/-!
# `CanLift27Genuine` from the remaining four interfaces

Combining `commIndexFour_of_translationCase` (R3b–R3c) with `canLift27Genuine_of'`:
`CanLift27Genuine` follows from

* `TranslationCase` (R3d): a normal-form once-punctured torus group whose commensurator contains
  `z ↦ z + 1/m`, `m ≥ 2`, has no core;
* `U2Descent`, `U2Rigidity` (the analytic halves of U2 over `ℂ`);
* `HemiCoreTransfer` ([CanLift] Prop. 2.3 and the Lefschetz principle).

R3d is proved (`translationCase`, `Genuine/TranslationCase.lean`).

By U2b (`Genuine.hemiDescends_of`), `U2Descent` follows from `U2Rigidity` and the algebraic
statement `Genuine.CompositumSeparates ℂ` (Abhyankar's lemma), so `CanLift27Genuine` follows from
`TranslationCase`, `U2Rigidity`, `CompositumSeparates ℂ` and `HemiCoreTransfer`
(`canLift27Genuine_of_remaining'`).

`U2Rigidity` is proved (`u2Rigidity`, `Genuine/Rigid/Main.lean`), so `CanLift27Genuine` follows
from `TranslationCase`, `CompositumSeparates ℂ` and `HemiCoreTransfer`
(`canLift27Genuine_of_remaining''`).

`CompositumSeparates ℂ` is proved (`Abhyankar.compositumSeparates`, U2f), so U2 is proved
(`u2Descent`, `hemiCoreComplex`) and `CanLift27Genuine` follows from `TranslationCase` and
`HemiCoreTransfer` (`canLift27Genuine_of_translationCase_of_transfer`).

R3d (`translationCase`) and the transfer (`hemiCoreTransfer`, `Genuine/Transfer/`) are proved, so
`CanLift27Genuine` holds unconditionally (`canLift27Genuine`).
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

/-- **U2b.** The descent half of U2 from the rigidity half and Abhyankar's lemma. -/
theorem u2Descent_of (hR : U2Rigidity) (hC : Genuine.CompositumSeparates ℂ) : U2Descent :=
  fun E _ A B hc hA hU hi ↦ Genuine.hemiDescends_of E (hR E A B hc hA hU hi) hC

/-- **`CanLift27Genuine` from R3d, U2 rigidity, Abhyankar's lemma over `ℂ`, and the
transfer.** -/
theorem canLift27Genuine_of_remaining' (hR3d : TranslationCase) (hR : U2Rigidity)
    (hC : Genuine.CompositumSeparates ℂ) (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of_remaining hR3d (u2Descent_of hR hC) hR hT

/-- `U2Descent` from Abhyankar's lemma (`CompositumSeparates ℂ`), using `u2Rigidity`. -/
theorem u2Descent_of_compositumSeparates (hC : Genuine.CompositumSeparates ℂ) : U2Descent :=
  u2Descent_of u2Rigidity hC

/-- U2 over `ℂ` (`(E ∖ 0)/±1` is the `ℂ`-core when `[Comm(Γ) : Γ] = 4`) from Abhyankar's
lemma. -/
theorem hemiCoreComplex_of_compositumSeparates (hC : Genuine.CompositumSeparates ℂ) :
    HemiCoreComplex :=
  hemiCoreComplex_of (u2Descent_of_compositumSeparates hC) u2Rigidity

/-- **`CanLift27Genuine` from R3d, Abhyankar's lemma over `ℂ`, and the transfer.** -/
theorem canLift27Genuine_of_remaining'' (hR3d : TranslationCase)
    (hC : Genuine.CompositumSeparates ℂ) (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of_remaining' hR3d u2Rigidity hC hT

/-- **U2, descent half** (proved). -/
theorem u2Descent : U2Descent :=
  u2Descent_of_compositumSeparates Abhyankar.compositumSeparates

/-- **U2 over `ℂ`** (proved): `(E ∖ 0)/±1` is the `ℂ`-core when `[Comm(Γ) : Γ] = 4`. -/
theorem hemiCoreComplex : HemiCoreComplex :=
  hemiCoreComplex_of_compositumSeparates Abhyankar.compositumSeparates

/-- **`CanLift27Genuine` from R3d and the transfer.** -/
theorem canLift27Genuine_of_translationCase_of_transfer (hR3d : TranslationCase)
    (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of_remaining'' hR3d Abhyankar.compositumSeparates hT

/-- **`CanLift27Genuine` from the transfer alone**: R3 (`translationCase`) and U2
(`u2Rigidity`, `u2Descent`) are proved, so only `HemiCoreTransfer` remains. -/
theorem canLift27Genuine_of_transfer (hT : HemiCoreTransfer.{u}) : CanLift27Genuine.{u} :=
  canLift27Genuine_of_translationCase_of_transfer translationCase hT

/-- **[CanLift] Proposition 2.7, genuine form**: for an elliptic curve `E` over a field of
characteristic `0` with `j(E)` not exceptional, the punctured hemi-elliptic orbicurve is the core
of `E ∖ 0`. -/
theorem canLift27Genuine : CanLift27Genuine.{u} :=
  canLift27Genuine_of_transfer hemiCoreTransfer

end OrbicurveCores
