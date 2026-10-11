/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.S1.Main
import OrbicurveCores.U2.Statement
import OrbicurveCores.Genuine.TranslationCase
import OrbicurveCores.Genuine.Rigid.Main
import OrbicurveCores.Genuine.Separates

/-!
# An alternative proof of [CanLift] Prop. 2.7 over `ℂ`

`Alt.canLift27C : CanLift27C` proves the same statement as `U2.canLift27C` along a different
route, which does not use oka's R3 (`Uniformization.Peripheral.le_pmDeck_or`) or the
Galois-closure argument of `U2/TheoremG.lean`:

* **R3** by elementary Fuchsian group theory: `commIndexFour` (`Genuine/TranslationCase.lean`,
  `Genuine/CommIndex.lean`): a once-punctured torus group admitting a core has index `4` in its
  commensurator;
* **U2, rigidity half** analytically: `u2Rigidity` (`Genuine/Rigid/`): lifts of the
  uniformisation to a finite étale cover are holomorphic families of points, and a function on
  `ℍ` with the local normal forms of `(E ∖ 0)/±1` that is invariant under a finite-index
  subgroup is the `x`-coordinate;
* **U2, descent half** from rigidity and Abhyankar's lemma: `u2Descent`
  (`Genuine.hemiDescends_of`, `Abhyankar.compositumSeparates`).

U1 (`uniformization`), S1 (`S1.not_takeuchi_of_nonExceptional`) and the group-level theorem
(`canLift27_group_unconditional`) are shared with the main proof.
-/

open Matrix

namespace OrbicurveCores.Alt

/-- **U2, descent half** (proved), from rigidity and Abhyankar's lemma. -/
theorem u2Descent : U2Descent :=
  fun E _ A B hc hA hU hi ↦
    Genuine.hemiDescends_of E (u2Rigidity E A B hc hA hU hi) Abhyankar.compositumSeparates

/-- **U2 over `ℂ`** (proved): `(E ∖ 0)/±1` is the `ℂ`-core when `[Comm(Γ) : Γ] = 4`. -/
theorem hemiCoreComplex : HemiCoreComplex :=
  hemiCoreComplex_of u2Descent u2Rigidity

/-- [CanLift] Prop. 2.7 over `ℂ` from R3 and U2 over `ℂ`, using U1, S1, and the group-level
theorem (Margulis, Takeuchi, sharpness). -/
theorem canLift27C_of (hR3 : CommIndexFour) (hU2 : HemiCoreComplex) : CanLift27C := by
  intro E _ hj
  obtain ⟨A, B, hc, hA, hU⟩ := uniformization E
  have hT := S1.not_takeuchi_of_nonExceptional E A B hU hj
  have hcore : AdmitsCore (Subgroup.closure {A, B}) := by
    by_contra h
    exact hT ((canLift27_group_unconditional hc hA).1 h)
  exact hU2 E A B hc hA hU (hR3 A B hc hA hcore)

/-- **[CanLift] Prop. 2.7 over `ℂ`, alternative proof** (same statement as `U2.canLift27C`). -/
theorem canLift27C : CanLift27C :=
  canLift27C_of commIndexFour hemiCoreComplex

end OrbicurveCores.Alt
