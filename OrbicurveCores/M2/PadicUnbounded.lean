/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.ThreePoint

/-!
# M2: iterates of a `p`-adic matrix with non-integral `tr² / det`

If `R ∈ GL(2, ℚ_p)` satisfies `|det R| < |tr R|²`, i.e. `tr(R)² / det(R)` is not a `p`-adic
integer, then the iterates `Rⁿ (0, 1, ∞)` converge to a triple with a repeated point
(`Padic.exists_degenerate_limit`).

Proof: by Hensel's lemma the characteristic polynomial has roots `μ₁, μ₂` with `|μ₂| < |μ₁|`.
With `A = R - μ₂`, `B = R - μ₁` one has `(μ₁ - μ₂) Rⁿ = μ₁ⁿ A - μ₂ⁿ B`, so projectively
`Rⁿ x = [A v - (μ₂/μ₁)ⁿ B v]` for `v` a coordinate vector of `x`. This tends to `[A v]` when
`A v ≠ 0` and is constant otherwise. Since `det A = 0`, all the points `[A v]` coincide, and
`A v = 0` holds for at most one of `0, 1, ∞`.
-/

open Topology Filter OnePoint OnePoint.Proj

namespace OrbicurveCores.M2

section algebra

variable {k : Type*} [Field k]

lemma mul_sub_smul_one_eq {M : Matrix (Fin 2) (Fin 2) k} {μ₁ μ₂ : k} (hs : μ₁ + μ₂ = M.trace)
    (hp : μ₁ * μ₂ = M.det) : M * (M - μ₂ • 1) = μ₁ • (M - μ₂ • 1) := by
  rw [Matrix.trace_fin_two] at hs
  rw [Matrix.det_fin_two] at hp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination (-M 0 0) * hs + hp
  · linear_combination (-M 0 1) * hs
  · linear_combination (-M 1 0) * hs
  · linear_combination (-M 1 1) * hs + hp

lemma pow_mul_sub_smul_one_eq {M : Matrix (Fin 2) (Fin 2) k} {μ₁ μ₂ : k}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det) (n : ℕ) :
    M ^ n * (M - μ₂ • 1) = μ₁ ^ n • (M - μ₂ • 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, mul_sub_smul_one_eq hs hp, Matrix.mul_smul, ih, smul_smul,
      pow_succ']

/-- `(μ₁ - μ₂) Mⁿ = μ₁ⁿ (M - μ₂) - μ₂ⁿ (M - μ₁)` for the roots `μ₁, μ₂` of the characteristic
polynomial of `M`. -/
lemma sub_smul_pow_eq {M : Matrix (Fin 2) (Fin 2) k} {μ₁ μ₂ : k}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det) (n : ℕ) :
    (μ₁ - μ₂) • M ^ n = μ₁ ^ n • (M - μ₂ • 1) - μ₂ ^ n • (M - μ₁ • 1) := by
  have e : (μ₁ - μ₂) • (1 : Matrix (Fin 2) (Fin 2) k) = (M - μ₂ • 1) - (M - μ₁ • 1) := by
    rw [sub_smul]; abel
  rw [← mul_one (M ^ n), ← Matrix.mul_smul, e, mul_sub,
    pow_mul_sub_smul_one_eq hs hp, pow_mul_sub_smul_one_eq (by rw [add_comm, hs])
      (by rw [mul_comm, hp])]

lemma br_mv_padic (A : Matrix (Fin 2) (Fin 2) k) (u w : k × k) :
    br (mv A u) (mv A w) = A.det * br u w := by
  simp only [br, mv, Matrix.det_fin_two]
  ring

end algebra

/-- The roots of the characteristic polynomial `X² - t X + d` over `ℚ_p` when `|d| < |t|²`. -/
lemma Padic.exists_roots_of_norm_lt {p : ℕ} [Fact p.Prime] {t d : ℚ_[p]} (h : ‖d‖ < ‖t‖ ^ 2) :
    ∃ μ₁ μ₂ : ℚ_[p], μ₁ + μ₂ = t ∧ μ₁ * μ₂ = d ∧ ‖μ₂‖ < ‖μ₁‖ := by
  have ht : t ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    linarith [norm_nonneg d]
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  set ε : ℚ_[p] := d / t ^ 2 with hεdef
  have hε : ‖ε‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]
    exact h
  let e : ℤ_[p] := ⟨ε, hε.le⟩
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C e
  have hn : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    have h1 : F.aeval (1 : ℤ_[p]) = e := by simp [F]
    have h2 : F.derivative.aeval (1 : ℤ_[p]) = 1 := by
      simp only [F, Polynomial.derivative_add, Polynomial.derivative_sub,
        Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_C]
      simp
      norm_num
    rw [h1, h2, norm_one, one_pow]
    exact hε
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma hn
  set l : ℚ_[p] := (z : ℚ_[p]) with hl
  have hzq : l ^ 2 - l + ε = 0 := by
    have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hz
    simpa [F, e, hl] using this
  have hl2 : ‖1 - l‖ < 1 := by
    have h2 : F.derivative.aeval (1 : ℤ_[p]) = 1 := by
      simp only [F, Polynomial.derivative_add, Polynomial.derivative_sub,
        Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_C]
      simp
      norm_num
    rw [h2, norm_one] at hz1
    have h3 : ‖((z - 1 : ℤ_[p]) : ℚ_[p])‖ < 1 := hz1
    rw [norm_sub_rev]
    simpa [hl] using h3
  have hl1 : 1 ≤ ‖l‖ := by
    have := IsUltrametricDist.norm_add_le_max l (1 - l)
    rw [add_sub_cancel, norm_one] at this
    rcases le_max_iff.mp this with h' | h'
    · exact h'
    · linarith
  refine ⟨t * l, t * (1 - l), by ring, ?_, ?_⟩
  · have : ε * t ^ 2 = d := by rw [hεdef]; field_simp
    linear_combination (-t ^ 2) * hzq + this
  · rw [norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left (by linarith) htn

open OnePoint.Proj in
/-- If `tr(R)² / det(R)` is not a `p`-adic integer, the iterates `Rⁿ (0, 1, ∞)` converge to a
triple with a repeated point. -/
theorem Padic.exists_degenerate_limit {p : ℕ} [Fact p.Prime] [DecidableEq ℚ_[p]]
    (R : GL (Fin 2) ℚ_[p])
    (h : ‖(R : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ <
      ‖(R : Matrix (Fin 2) (Fin 2) ℚ_[p]).trace‖ ^ 2) :
    ∃ τ : Triple ℚ_[p], ¬ Distinct3 τ ∧
      Tendsto (fun n : ℕ ↦ smul3 (R ^ n) e₃) atTop (𝓝 τ) := by
  set M : Matrix (Fin 2) (Fin 2) ℚ_[p] := ↑R with hM
  obtain ⟨μ₁, μ₂, hs, hp, hlt⟩ := Padic.exists_roots_of_norm_lt h
  have hdet : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp R.isUnit |>.ne_zero
  have hμ₁ : μ₁ ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hlt)
  have hμ₂ : μ₂ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hp, mul_zero])
  have h12 : μ₁ - μ₂ ≠ 0 := by
    intro e
    rw [sub_eq_zero] at e
    rw [e] at hlt
    exact lt_irrefl _ hlt
  set A := M - μ₂ • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hA
  set B := M - μ₁ • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hB
  set q := μ₂ / μ₁ with hq
  have hq1 : ‖q‖ < 1 := by
    rw [hq, norm_div, div_lt_one (norm_pos_iff.mpr hμ₁)]
    exact hlt
  have hq0 : q ≠ 0 := div_ne_zero hμ₂ hμ₁
  -- projective formula for the iterates
  have hmob : ∀ (n : ℕ) (x : OnePoint ℚ_[p]),
      (R ^ n) • x = proj (mv A (lift x) - q ^ n • mv B (lift x)) := by
    intro n x
    rw [gl_smul_eq_mob, Units.val_pow_eq_pow_val, ← hM, ← mob_smul_matrix h12,
      sub_smul_pow_eq hs hp, ← mob_smul_matrix (inv_ne_zero (pow_ne_zero n hμ₁)), mob]
    congr 1
    have e : (μ₁ ^ n)⁻¹ • (μ₁ ^ n • A - μ₂ ^ n • B) = A - q ^ n • B := by
      rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero n hμ₁), one_smul, hq,
        div_pow, div_eq_inv_mul]
    rw [e]
    simp only [mv, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk,
      Prod.mk_sub_mk]
    congr 1 <;> ring
  -- the limit of the orbit of a point
  let φ : OnePoint ℚ_[p] → OnePoint ℚ_[p] := fun x ↦
    if mv A (lift x) = 0 then proj (mv B (lift x)) else proj (mv A (lift x))
  have hlim : ∀ x, Tendsto (fun n : ℕ ↦ (R ^ n) • x) atTop (𝓝 (φ x)) := by
    intro x
    simp only [hmob, φ]
    split_ifs with hAx
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [hAx, zero_sub, ← neg_smul, proj_smul (neg_ne_zero.mpr (pow_ne_zero n hq0))]
    · have hqn : Tendsto (fun n : ℕ ↦ q ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1
      have hv : Tendsto (fun n : ℕ ↦ mv A (lift x) - q ^ n • mv B (lift x)) atTop
          (𝓝 (mv A (lift x))) := by
        have := tendsto_const_nhds (x := mv A (lift x)) |>.sub (hqn.smul_const (mv B (lift x)))
        rwa [zero_smul, sub_zero] at this
      exact (continuousAt_proj hAx).tendsto.comp hv
  refine ⟨(φ (0 : ℚ_[p]), φ (1 : ℚ_[p]), φ ∞), ?_, ?_⟩
  · -- two of the three limits coincide
    have hdetA : A.det = 0 := by
      rw [Matrix.trace_fin_two] at hs
      rw [Matrix.det_fin_two] at hp
      rw [hA, Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, mul_one, sub_zero]
      linear_combination μ₂ * hs - hp
    have hsame : ∀ u w : ℚ_[p] × ℚ_[p], u ≠ 0 → w ≠ 0 → mv A u ≠ 0 → mv A w ≠ 0 →
        proj (mv A u) = proj (mv A w) := by
      intro u w _ _ hu hw
      rw [proj_eq_proj_iff hu hw, br_mv_padic, hdetA, zero_mul]
    have hnot : ¬ (mv A (lift ((0 : ℚ_[p]) : OnePoint ℚ_[p])) = 0 ∧
        mv A (lift (∞ : OnePoint ℚ_[p])) = 0) := by
      rintro ⟨h0, hi⟩
      simp only [lift_coe, lift_infty, mv, hA, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, mul_zero, mul_one, add_zero, zero_add, Prod.ext_iff, Prod.fst_zero,
        Prod.snd_zero, Matrix.one_apply_eq,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero, sub_eq_zero] at h0 hi
      rw [Matrix.trace_fin_two, Matrix.det_fin_two, h0.1, h0.2, hi.1, hi.2] at h
      have h2 : ‖(2 : ℚ_[p])‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_natCast_le_one ℚ_[p] 2
      have : ‖μ₂ * μ₂ - 0 * 0‖ < ‖μ₂ + μ₂‖ ^ 2 := h
      rw [mul_zero, sub_zero, ← two_mul, norm_mul, norm_mul, mul_pow] at this
      have h4 : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h2
      nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖μ₂‖)]
    have hsum : mv A (lift ((1 : ℚ_[p]) : OnePoint ℚ_[p])) =
        mv A (lift ((0 : ℚ_[p]) : OnePoint ℚ_[p])) + mv A (lift (∞ : OnePoint ℚ_[p])) := by
      simp only [lift_coe, lift_infty, mv, Prod.mk_add_mk]
      congr 1 <;> ring
    simp only [Distinct3, not_and_or, not_not]
    by_cases h0 : mv A (lift ((0 : ℚ_[p]) : OnePoint ℚ_[p])) = 0
    · have hi : mv A (lift (∞ : OnePoint ℚ_[p])) ≠ 0 := fun hi ↦ hnot ⟨h0, hi⟩
      have h1 : mv A (lift ((1 : ℚ_[p]) : OnePoint ℚ_[p])) ≠ 0 := by
        rwa [hsum, h0, zero_add]
      right; right
      simp only [φ, if_neg h1, if_neg hi]
      exact hsame _ _ (lift_ne_zero _) (lift_ne_zero _) h1 hi
    · by_cases hi : mv A (lift (∞ : OnePoint ℚ_[p])) = 0
      · have h1 : mv A (lift ((1 : ℚ_[p]) : OnePoint ℚ_[p])) ≠ 0 := by
          rwa [hsum, hi, add_zero]
        left
        simp only [φ, if_neg h1, if_neg h0]
        exact hsame _ _ (lift_ne_zero _) (lift_ne_zero _) h0 h1
      · right; left
        simp only [φ, if_neg h0, if_neg hi]
        exact hsame _ _ (lift_ne_zero _) (lift_ne_zero _) h0 hi
  · exact (hlim _).prodMk_nhds ((hlim _).prodMk_nhds (hlim _))

end OrbicurveCores.M2
