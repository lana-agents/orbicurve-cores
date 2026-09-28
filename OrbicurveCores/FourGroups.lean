/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Core
import OrbicurveCores.FrickeRigidity

/-!
# Takeuchi's four `(1;∞)`-groups, explicitly

Explicit generating pairs `(Aᵢ, Bᵢ)` in `SL(2, ℝ)` with trace triples

| case | `(tr A, tr B, tr AB)` | `A` | `B` |
|---|---|---|---|
| I | `(√5, 2√5, 5)` | `[[4, 1], [-1, 1]]/√5` | `[[3, 2], [8, 7]]/√5` |
| II | `(√6, 2√3, 3√2)` | `[[5, 1], [-1, 1]]/√6` | `[[2, 1], [5, 4]]/√3` |
| III | `(2√2, 2√2, 4)` | `[[3, 1], [1, 1]]/√2` | `[[1, 1], [1, 3]]/√2` |
| IV | `(3, 3, 3)` | `[[2, 1], [1, 1]]` | `[[0, -1], [1, 3]]` |

The numbering follows [Sijs] Table 1. By Fricke rigidity (`exists_conj_of_tr_eq`), any pair
with one of these trace triples, up to sign, is simultaneously `GL(2, ℝ)`-conjugate to
`(±Aᵢ, ±Bᵢ)`. With `takeuchi_one_infty` this gives:

* `OrbicurveCores.takeuchi_one_infty_conj`: an arithmetic `(1;∞)`-group is, up to Nielsen moves,
  signs and `GL(2, ℝ)`-conjugacy, one of the four explicit groups;
* `OrbicurveCores.canLift27_group_conj`: the same for `(1;∞)`-groups without core, assuming
  `MargulisOneInfty`.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace OrbicurveCores

/-- The element `c • M` of `SL(2, ℝ)` for an integer matrix `M` of determinant `n > 0`, with
`c = 1/√n`. -/
noncomputable def scaledSL (n : ℕ) (hn : 0 < n) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M.det = n) : SL(2, ℝ) :=
  ⟨(Real.sqrt n)⁻¹ • M, by
    rw [det_smul, hM, Fintype.card_fin, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp⟩

lemma tr_scaledSL (n : ℕ) (hn : 0 < n) (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det = n) :
    tr (scaledSL n hn M hM) = M.trace / Real.sqrt n := by
  simp [tr, scaledSL, trace_smul, div_eq_inv_mul]

lemma tr_scaledSL_mul (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M.det = n) (hN : N.det = k) :
    tr (scaledSL n hn M hM * scaledSL k hk N hN) = (M * N).trace / (Real.sqrt n * Real.sqrt k) := by
  simp only [tr, scaledSL, Matrix.SpecialLinearGroup.coe_mul]
  rw [smul_mul_smul_comm, trace_smul, smul_eq_mul, div_eq_inv_mul, mul_inv]

/-- Case I: `A = [[4, 1], [-1, 1]]/√5`. -/
noncomputable def pairIA : SL(2, ℝ) := scaledSL 5 (by norm_num) !![4, 1; -1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case I: `B = [[3, 2], [8, 7]]/√5`. -/
noncomputable def pairIB : SL(2, ℝ) := scaledSL 5 (by norm_num) !![3, 2; 8, 7]
  (by simp [det_fin_two]; norm_num)
/-- Case II: `A = [[5, 1], [-1, 1]]/√6`. -/
noncomputable def pairIIA : SL(2, ℝ) := scaledSL 6 (by norm_num) !![5, 1; -1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case II: `B = [[2, 1], [5, 4]]/√3`. -/
noncomputable def pairIIB : SL(2, ℝ) := scaledSL 3 (by norm_num) !![2, 1; 5, 4]
  (by simp [det_fin_two]; norm_num)
/-- Case III: `A = [[3, 1], [1, 1]]/√2`. -/
noncomputable def pairIIIA : SL(2, ℝ) := scaledSL 2 (by norm_num) !![3, 1; 1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case III: `B = [[1, 1], [1, 3]]/√2`. -/
noncomputable def pairIIIB : SL(2, ℝ) := scaledSL 2 (by norm_num) !![1, 1; 1, 3]
  (by simp [det_fin_two]; norm_num)
/-- Case IV: `A = [[2, 1], [1, 1]]`. -/
noncomputable def pairIVA : SL(2, ℝ) := scaledSL 1 (by norm_num) !![2, 1; 1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case IV: `B = [[0, -1], [1, 3]]`. -/
noncomputable def pairIVB : SL(2, ℝ) := scaledSL 1 (by norm_num) !![0, -1; 1, 3]
  (by simp [det_fin_two])

/-- The four explicit pairs. -/
noncomputable def takeuchiPair : Fin 4 → SL(2, ℝ) × SL(2, ℝ)
  | 0 => (pairIA, pairIB)
  | 1 => (pairIIA, pairIIB)
  | 2 => (pairIIIA, pairIIIB)
  | 3 => (pairIVA, pairIVB)

lemma div_sqrt_eq_sqrt {t n X : ℝ} (ht : 0 ≤ t) (hn : 0 < n) (h : t ^ 2 = X * n) :
    t / Real.sqrt n = Real.sqrt X := by
  have hX : 0 ≤ X := by
    by_contra hX; push Not at hX; nlinarith [sq_nonneg t]
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hX (by positivity), div_mul_div_comm,
    Real.mul_self_sqrt hn.le, eq_div_iff hn.ne', ← h]
  ring

lemma div_sqrt_mul_sqrt_eq_sqrt {t n k X : ℝ} (ht : 0 ≤ t) (hn : 0 < n) (hk : 0 < k)
    (h : t ^ 2 = X * (n * k)) : t / (Real.sqrt n * Real.sqrt k) = Real.sqrt X := by
  rw [← Real.sqrt_mul hn.le]
  exact div_sqrt_eq_sqrt ht (by positivity) h

/-- The (positive) trace triples of the four pairs. -/
lemma takeuchiPair_traces :
    (tr pairIA = Real.sqrt 5 ∧ tr pairIB = Real.sqrt 20 ∧ tr (pairIA * pairIB) = Real.sqrt 25) ∧
    (tr pairIIA = Real.sqrt 6 ∧ tr pairIIB = Real.sqrt 12 ∧
      tr (pairIIA * pairIIB) = Real.sqrt 18) ∧
    (tr pairIIIA = Real.sqrt 8 ∧ tr pairIIIB = Real.sqrt 8 ∧
      tr (pairIIIA * pairIIIB) = Real.sqrt 16) ∧
    (tr pairIVA = Real.sqrt 9 ∧ tr pairIVB = Real.sqrt 9 ∧
      tr (pairIVA * pairIVB) = Real.sqrt 9) := by
  simp only [pairIA, pairIB, pairIIA, pairIIB, pairIIIA, pairIIIB, pairIVA, pairIVB,
    tr_scaledSL, tr_scaledSL_mul]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
  first
    | (apply div_sqrt_eq_sqrt <;>
        simp [trace_fin_two] <;> norm_num)
    | (apply div_sqrt_mul_sqrt_eq_sqrt <;>
        simp [trace_fin_two] <;> norm_num)

lemma tr_neg (A : SL(2, ℝ)) : tr (-A) = -tr A := by
  simp [tr, Matrix.SpecialLinearGroup.coe_neg, trace_neg]

/-- Changing the signs of `A` and `B` so that the trace triple becomes `(|x|, |y|, |z|)`; this is
possible when `xyz > 0`. -/
lemma exists_sign_normalize {A B : SL(2, ℝ)} (hpos : 0 < tr A * tr B * tr (A * B)) :
    ∃ A' ∈ ({A, -A} : Set SL(2, ℝ)), ∃ B' ∈ ({B, -B} : Set SL(2, ℝ)),
      tr A' = |tr A| ∧ tr B' = |tr B| ∧ tr (A' * B') = |tr (A * B)| ∧
      tr (A' * B' * A'⁻¹ * B'⁻¹) = tr (A * B * A⁻¹ * B⁻¹) := by
  have hx : tr A ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  have hy : tr B ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  have hz : tr (A * B) ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · have hz' : 0 < tr (A * B) := by
      by_contra h; push Not at h; nlinarith [mul_pos_of_neg_of_neg hx hy]
    refine ⟨-A, by simp, -B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [tr_neg, abs_of_neg hx]
    · rw [tr_neg, abs_of_neg hy]
    · rw [neg_mul_neg, abs_of_pos hz']
    · rw [tr_commutator, tr_commutator, tr_neg, tr_neg, neg_mul_neg]; ring
  · have hz' : tr (A * B) < 0 := by
      by_contra h; push Not at h
      have : tr A * tr B < 0 := mul_neg_of_neg_of_pos hx hy
      nlinarith
    refine ⟨-A, by simp, B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [tr_neg, abs_of_neg hx]
    · rw [abs_of_pos hy]
    · rw [neg_mul, tr_neg, abs_of_neg hz']
    · rw [tr_commutator, tr_commutator, tr_neg, neg_mul, tr_neg]; ring
  · have hz' : tr (A * B) < 0 := by
      by_contra h; push Not at h
      have : tr A * tr B < 0 := mul_neg_of_pos_of_neg hx hy
      nlinarith
    refine ⟨A, by simp, -B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_pos hx]
    · rw [tr_neg, abs_of_neg hy]
    · rw [mul_neg, tr_neg, abs_of_neg hz']
    · rw [tr_commutator, tr_commutator, tr_neg, mul_neg, tr_neg]; ring
  · have hz' : 0 < tr (A * B) := by
      by_contra h; push Not at h; nlinarith [mul_pos hx hy]
    exact ⟨A, by simp, B, by simp, (abs_of_pos hx).symm, (abs_of_pos hy).symm,
      (abs_of_pos hz').symm, rfl⟩

/-- A pair with commutator trace `-2` and one of Takeuchi's squared trace triples is, up to signs,
simultaneously `GL(2, ℝ)`-conjugate to one of the four explicit pairs `takeuchiPair i`. -/
theorem exists_conj_of_takeuchiSq {A' B' : SL(2, ℝ)} (hc' : tr (A' * B' * A'⁻¹ * B'⁻¹) = -2)
    (hT : TakeuchiSq (tr A') (tr B') (tr (A' * B'))) :
    ∃ i : Fin 4, ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
      ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 ∧
        g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2 := by
  have hrel := (tr_commutator_eq_neg_two_iff A' B').mp hc'
  have hX : 4 < tr A' ^ 2 := by
    rcases hT with h | h | h | h <;> linarith [h.1]
  have hpos : 0 < tr A' * tr B' * tr (A' * B') := by
    rw [← hrel]; positivity
  obtain ⟨A'', hA'', B'', hB'', h1, h2, h3, h4⟩ := exists_sign_normalize hpos
  have hx'' : 4 < tr A'' ^ 2 := by rw [h1, sq_abs]; exact hX
  have hc'' : tr (A'' * B'' * A''⁻¹ * B''⁻¹) ≠ 2 := by rw [h4, hc']; norm_num
  obtain ⟨⟨t1a, t1b, t1c⟩, ⟨t2a, t2b, t2c⟩, ⟨t3a, t3b, t3c⟩, ⟨t4a, t4b, t4c⟩⟩ :=
    takeuchiPair_traces
  simp only [← Real.sqrt_sq_eq_abs] at h1 h2 h3
  rcases hT with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_conj_of_tr_eq (A' := pairIVA) (B' := pairIVB) hx'' hc''
      (by rw [h1, ha, t4a]) (by rw [h2, hb, t4b]) (by rw [h3, hc, t4c])
    exact ⟨3, A'', hA'', B'', hB'', g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_conj_of_tr_eq (A' := pairIIIA) (B' := pairIIIB) hx'' hc''
      (by rw [h1, ha, t3a]) (by rw [h2, hb, t3b]) (by rw [h3, hc, t3c])
    exact ⟨2, A'', hA'', B'', hB'', g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_conj_of_tr_eq (A' := pairIA) (B' := pairIB) hx'' hc''
      (by rw [h1, ha, t1a]) (by rw [h2, hb, t1b]) (by rw [h3, hc, t1c])
    exact ⟨0, A'', hA'', B'', hB'', g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := exists_conj_of_tr_eq (A' := pairIIA) (B' := pairIIB) hx'' hc''
      (by rw [h1, ha, t2a]) (by rw [h2, hb, t2b]) (by rw [h3, hc, t2c])
    exact ⟨1, A'', hA'', B'', hB'', g, hg1, hg2⟩


/-- **Takeuchi's theorem, up to conjugacy.** An arithmetic `(1;∞)`-group `⟨A, B⟩ ⊆ SL(2, ℝ)` has
a Nielsen-equivalent generating pair `(A', B')` which, up to signs, is simultaneously
`GL(2, ℝ)`-conjugate to one of the four explicit pairs `takeuchiPair i`. -/
theorem takeuchi_one_infty_conj {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (harith : IsArithmeticSL (Subgroup.closure {A, B})) :
    ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
      ∃ i : Fin 4, ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
        ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 ∧
          g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2 := by
  obtain ⟨A', B', hcl, hc', hT⟩ := takeuchi_one_infty hcomm harith
  exact ⟨A', B', hcl, exists_conj_of_takeuchiSq hc' hT⟩

/-- **[CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1, group-theoretic form up to conjugacy,
conditional on Margulis.** A `(1;∞)`-group `⟨A, B⟩ ⊆ SL(2, ℝ)` without core is, after Nielsen
moves and signs, simultaneously `GL(2, ℝ)`-conjugate to one of the four explicit pairs
`takeuchiPair i`. These uniformise the once-punctured elliptic curves with
`j = 2¹⁴·31³/5³, 2²·73³/3⁴, 1728, 0` (`i = 0, 1, 2, 3`; [Sijs] Table 4). -/
theorem canLift27_group_conj (hM : MargulisOneInfty) {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0)
    (hno : ¬ AdmitsCore (Subgroup.closure {A, B})) :
    ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
      ∃ i : Fin 4, ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
        ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 ∧
          g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2 :=
  takeuchi_one_infty_conj hcomm (hM A B hcomm hA hno)

end OrbicurveCores
