/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.SharpnessData

/-!
# The classification of arithmetic (and coreless) `(1;∞)`-groups

For `A, B ∈ SL(2, ℝ)` with `tr [A, B] = -2`, write `IsTakeuchiConj A B` for: some
Nielsen-equivalent generating pair `(A', B')` of `⟨A, B⟩` is, up to signs, simultaneously
`GL(2, ℝ)`-conjugate to one of the four explicit pairs `takeuchiPair i`.

* `isArithmeticSL_iff_isTakeuchiConj`: `⟨A, B⟩` is arithmetic iff `IsTakeuchiConj A B`. This is
  Takeuchi's theorem ([Take2] Thm. 4.1(i), `e = ∞`), fully proved.
* `not_admitsCore_of_isTakeuchiConj`: the four groups admit no core (unconditional).
* `not_admitsCore_iff_isTakeuchiConj`: assuming `MargulisOneInfty`, `⟨A, B⟩` admits no core iff
  `IsTakeuchiConj A B`. This is the group-theoretic form of [CanLift] Prop. 2.7 /
  [EstIUT] Prop. 2.1: the coreless once-punctured tori are exactly the four arithmetic ones.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores

/-- `⟨A, B⟩` has a Nielsen-equivalent generating pair which, up to signs, is simultaneously
`GL(2, ℝ)`-conjugate to one of Takeuchi's four pairs. -/
def IsTakeuchiConj (A B : SL(2, ℝ)) : Prop :=
  ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
    ∃ i : Fin 4, ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
      ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 ∧
        g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2

/-- Arithmeticity is invariant under commensurability. -/
lemma IsArithmeticSL.of_commensurable {Γ Γ' : Subgroup SL(2, ℝ)} (h : IsArithmeticSL Γ')
    (hc : Commensurable (Γ.map toGL) (Γ'.map toGL)) : IsArithmeticSL Γ := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, ⟨(hc.conj _).trans hg.is_commensurable⟩⟩

lemma toGL_neg (A : SL(2, ℝ)) : toGL (-A) = -toGL A := by
  ext1; simp [Matrix.SpecialLinearGroup.coe_neg]

/-- The image in `GL(2, ℝ)` of `⟨A, B⟩`. -/
lemma map_toGL_closure_pair (A B : SL(2, ℝ)) :
    (Subgroup.closure {A, B}).map toGL = Subgroup.closure {toGL A, toGL B} := by
  rw [MonoidHom.map_closure, Set.image_pair]

lemma adjoinNegOne_le {P Q : Subgroup (GL (Fin 2) ℝ)} (h : P ≤ Q) (hQ : -1 ∈ Q) :
    P.adjoinNegOne ≤ Q := by
  intro g hg
  rcases hg with hg | hg
  · exact h hg
  · simpa using mul_mem hQ (h hg)

/-- Changing the signs of the generators gives a commensurable group. -/
lemma commensurable_signs {A B A'' B'' : SL(2, ℝ)} (hA : A'' ∈ ({A, -A} : Set SL(2, ℝ)))
    (hB : B'' ∈ ({B, -B} : Set SL(2, ℝ))) :
    Commensurable ((Subgroup.closure {A'', B''}).map toGL)
      ((Subgroup.closure {A, B}).map toGL) := by
  set P := (Subgroup.closure {A, B}).map toGL
  set Q := (Subgroup.closure {A'', B''}).map toGL
  have mem : ∀ {X Y : SL(2, ℝ)}, Y ∈ ({X, -X} : Set SL(2, ℝ)) →
      ∀ {K : Subgroup (GL (Fin 2) ℝ)}, toGL X ∈ K → toGL Y ∈ K.adjoinNegOne := by
    intro X Y hY K hX
    rcases hY with rfl | rfl
    · exact K.le_adjoinNegOne hX
    · exact Or.inr (by rw [toGL_neg, neg_neg]; exact hX)
  have hQP : Q ≤ P.adjoinNegOne := by
    change (Subgroup.closure {A'', B''}).map toGL ≤ P.adjoinNegOne
    rw [map_toGL_closure_pair, closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨mem hA ?_, mem hB ?_⟩
    · exact mem_map_of_mem _ (subset_closure (by simp))
    · exact mem_map_of_mem _ (subset_closure (by simp))
  have hA' : A ∈ ({A'', -A''} : Set SL(2, ℝ)) := by
    rcases hA with rfl | rfl <;> simp
  have hB' : B ∈ ({B'', -B''} : Set SL(2, ℝ)) := by
    rcases hB with rfl | rfl <;> simp
  have hPQ : P ≤ Q.adjoinNegOne := by
    change (Subgroup.closure {A, B}).map toGL ≤ Q.adjoinNegOne
    rw [map_toGL_closure_pair, closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨mem hA' ?_, mem hB' ?_⟩
    · exact mem_map_of_mem _ (subset_closure (by simp))
    · exact mem_map_of_mem _ (subset_closure (by simp))
  have heq : Q.adjoinNegOne = P.adjoinNegOne :=
    le_antisymm (adjoinNegOne_le hQP (P.negOne_mem_adjoinNegOne))
      (adjoinNegOne_le hPQ (Q.negOne_mem_adjoinNegOne))
  exact (Q.commensurable_adjoinNegOne_self.symm.trans (heq ▸ P.commensurable_adjoinNegOne_self))

/-- Simultaneous conjugation of a pair conjugates the generated group. -/
lemma conjAct_smul_closure_pair {A B A' B' : SL(2, ℝ)} {g : GL (Fin 2) ℝ}
    (hA : g * toGL A * g⁻¹ = toGL A') (hB : g * toGL B * g⁻¹ = toGL B') :
    ConjAct.toConjAct g • (Subgroup.closure {A, B}).map toGL =
      (Subgroup.closure {A', B'}).map toGL := by
  rw [map_toGL_closure_pair, map_toGL_closure_pair, Subgroup.pointwise_smul_def,
    MonoidHom.map_closure, Set.image_pair]
  simp [ConjAct.toConjAct_smul, hA, hB]

/-- **Takeuchi's theorem** ([Take2] Thm. 4.1(i), `e = ∞`): a `(1;∞)`-group `⟨A, B⟩` is
arithmetic iff it is (up to Nielsen moves, signs and `GL(2, ℝ)`-conjugacy) one of the four
explicit groups. -/
theorem isArithmeticSL_iff_isTakeuchiConj {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) :
    IsArithmeticSL (Subgroup.closure {A, B}) ↔ IsTakeuchiConj A B := by
  refine ⟨takeuchi_one_infty_conj hcomm, ?_⟩
  rintro ⟨A', B', hcl, i, A'', hA'', B'', hB'', g, hgA, hgB⟩
  -- `⟨A'', B''⟩` is conjugate to the arithmetic `Γᵢ`
  obtain ⟨h, hh⟩ := Sharp.takeuchiPair_isArithmeticSL i
  have h2 : IsArithmeticSL (Subgroup.closure {A'', B''}) := by
    refine ⟨h * g, ?_⟩
    rw [map_mul, mul_smul, conjAct_smul_closure_pair hgA hgB]
    exact hh
  rw [← hcl]
  exact h2.of_commensurable (commensurable_signs hA'' hB'').symm

/-- The four groups admit **no core** (unconditionally). -/
theorem not_admitsCore_of_isTakeuchiConj {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (h : IsTakeuchiConj A B) :
    ¬ AdmitsCore (Subgroup.closure {A, B}) :=
  ((isArithmeticSL_iff_isTakeuchiConj hcomm).mpr h).not_admitsCore

/-- **[CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1, group-theoretic form.** Assuming Margulis'
commensurator theorem (`MargulisOneInfty`), a `(1;∞)`-group `⟨A, B⟩ ⊆ SL(2, ℝ)` admits no core iff
it is one of Takeuchi's four groups, which uniformise the once-punctured elliptic curves with
`j = 2¹⁴·31³/5³, 2²·73³/3⁴, 1728, 0` ([Sijs] Table 4). Margulis is used only for `→`. -/
theorem not_admitsCore_iff_isTakeuchiConj (hM : MargulisOneInfty) {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0) :
    ¬ AdmitsCore (Subgroup.closure {A, B}) ↔ IsTakeuchiConj A B :=
  ⟨canLift27_group_conj hM hcomm hA, not_admitsCore_of_isTakeuchiConj hcomm⟩

end OrbicurveCores
