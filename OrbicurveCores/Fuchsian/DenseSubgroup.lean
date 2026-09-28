/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# Non-discrete subgroups of `SL(2, ℝ)` containing unipotent directions

Elementary replacement for the Lie-algebra argument "a closed non-discrete subgroup normalised by
a Zariski-dense group is everything", specialised to `SL(2, ℝ)`.

* `SL2R.uU t = [[1, t], [0, 1]]`, `SL2R.uL t = [[1, 0], [t, 1]]`.
* `SL2R.eq_top_of_unipotents`: a subgroup containing all `uU t` and `uL t` is `⊤`
  (every matrix is a product of at most four elementary matrices).
* `SL2R.uU_mem_of_tendsto`: a **closed** subgroup `K` containing `D = diag(l, l⁻¹)` (`l > 1`) and
  a sequence `gₙ → 1` with nonzero upper-right entries contains every `uU t`. Conjugating by
  powers of `D` rescales the upper-right entry to a fixed size, and a limit point lies in `K`.
-/

open Matrix Filter Topology
open scoped MatrixGroups

namespace OrbicurveCores.SL2R

/-- The upper unipotent `[[1, t], [0, 1]]`. -/
def uU (t : ℝ) : SL(2, ℝ) := ⟨!![1, t; 0, 1], by simp [det_fin_two]⟩

/-- The lower unipotent `[[1, 0], [t, 1]]`. -/
def uL (t : ℝ) : SL(2, ℝ) := ⟨!![1, 0; t, 1], by simp [det_fin_two]⟩

@[simp] lemma coe_uU (t : ℝ) : ((uU t : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, t; 0, 1] :=
  rfl

@[simp] lemma coe_uL (t : ℝ) : ((uL t : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; t, 1] :=
  rfl

lemma uU_add (s t : ℝ) : uU (s + t) = uU s * uU t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma uU_zero : uU 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

set_option linter.flexible false in
lemma continuous_uU : Continuous uU := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

set_option linter.flexible false in
lemma continuous_uL : Continuous uL := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- A subgroup containing all elementary unipotents is everything. -/
theorem eq_top_of_unipotents {K : Subgroup SL(2, ℝ)} (hU : ∀ t, uU t ∈ K) (hL : ∀ t, uL t ∈ K) :
    K = ⊤ := by
  -- matrices with nonzero lower-left entry
  have key : ∀ M : SL(2, ℝ), M 1 0 ≠ 0 → M ∈ K := by
    intro M hc
    have hdet := M.det_coe
    rw [det_fin_two] at hdet
    have : M = uU ((M 0 0 - 1) / M 1 0) * uL (M 1 0) * uU ((M 1 1 - 1) / M 1 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf
      linear_combination (-1 : ℝ) * hdet
    rw [this]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  rw [eq_top_iff]
  intro M _
  by_cases hc : M 1 0 = 0
  · -- `M uL(1)` has nonzero lower-left entry
    have hd : M 1 1 ≠ 0 := by
      intro h
      have hdet := M.det_coe
      rw [det_fin_two, hc, h] at hdet
      simp at hdet
    have h1 : (M * uL 1) 1 0 ≠ 0 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    have := mul_mem (key _ h1) (hL (-1))
    rwa [mul_assoc, show uL 1 * uL (-1) = 1 by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      mul_one] at this
  · exact key M hc

lemma tendsto_entry {g : ℕ → SL(2, ℝ)} {M : SL(2, ℝ)} (h : Tendsto g atTop (𝓝 M)) (i j : Fin 2) :
    Tendsto (fun n ↦ (g n : Matrix (Fin 2) (Fin 2) ℝ) i j) atTop (𝓝 (M i j)) := by
  have h1 : Tendsto (fun n ↦ (g n : Matrix (Fin 2) (Fin 2) ℝ)) atTop
      (𝓝 (M : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (continuous_subtype_val.tendsto _).comp h
  exact (continuous_apply j).tendsto _ |>.comp ((continuous_apply i).tendsto _ |>.comp h1)

lemma tendsto_of_entries {g : ℕ → SL(2, ℝ)} {M : SL(2, ℝ)}
    (h : ∀ i j, Tendsto (fun n ↦ (g n : Matrix (Fin 2) (Fin 2) ℝ) i j) atTop (𝓝 (M i j))) :
    Tendsto g atTop (𝓝 M) := by
  apply (Topology.IsInducing.subtypeVal).tendsto_nhds_iff.mpr
  exact tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ h i j

/-- **Rescaling lemma.** A closed subgroup containing `D = diag(l, l⁻¹)` with `l > 1` and a
sequence converging to `1` with nonzero upper-right entries contains all `uU t`. -/
theorem uU_mem_of_tendsto {K : Subgroup SL(2, ℝ)} (hK : IsClosed (K : Set SL(2, ℝ)))
    {D : SL(2, ℝ)} {l : ℝ} (hl : 1 < l)
    (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, l⁻¹]) (hDK : D ∈ K)
    {g : ℕ → SL(2, ℝ)} (hg : ∀ n, g n ∈ K) (hlim : Tendsto g atTop (𝓝 1))
    (h01 : ∀ n, (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0) (t : ℝ) : uU t ∈ K := by
  set q : ℝ := l ^ 2 with hq
  have hq1 : 1 < q := by rw [hq]; nlinarith
  have hl0 : 0 < l := by linarith
  -- conjugation by `D^k`
  have hDk : ∀ k : ℕ, ((D ^ k : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![l ^ k, 0; 0, (l⁻¹) ^ k] := by
    intro k
    induction k with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
    | succ k ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, hD]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
  have hDki : ∀ k : ℕ, (((D ^ k)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(l⁻¹) ^ k, 0; 0, l ^ k] := by
    intro k
    rw [Matrix.SpecialLinearGroup.coe_inv, hDk, adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have conj : ∀ (k : ℕ) (x : SL(2, ℝ)),
      ((D ^ k * x * (D ^ k)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![x 0 0, q ^ k * x 0 1; (q ^ k)⁻¹ * x 1 0, x 1 1] := by
    intro k x
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hDk, hDki,
      eta_fin_two (x : Matrix (Fin 2) (Fin 2) ℝ), Matrix.mul_fin_two, Matrix.mul_fin_two]
    have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl0.ne'
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hq, ← pow_mul] <;> field_simp <;> ring
  -- the set of admissible `t` is a closed additive subgroup of `ℝ`
  let S : AddSubgroup ℝ :=
    { carrier := {t | uU t ∈ K}
      add_mem' := fun {a b} ha hb ↦ by simp only [Set.mem_setOf_eq, uU_add]; exact mul_mem ha hb
      zero_mem' := by simp [uU_zero]
      neg_mem' := fun {a} ha ↦ by
        have : uU (-a) = (uU a)⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← uU_add, neg_add_cancel, uU_zero]
        simp only [Set.mem_setOf_eq, this]; exact inv_mem ha }
  have hSclosed : IsClosed (S : Set ℝ) := hK.preimage continuous_uU
  -- small positive elements of `S`
  have hsmall : ∀ ε > 0, ∃ s ∈ S, s ∈ Set.Ioo 0 ε := by
    intro ε hε
    set c := ε / 2 with hc
    have hc0 : 0 < c := by positivity
    have hβ := tendsto_entry hlim 0 1
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
      at hβ
    -- eventually `|β_n| < c`
    have hev : ∀ᶠ n in atTop, |(g n : Matrix (Fin 2) (Fin 2) ℝ) 0 1| < c := by
      have := (hβ.abs).eventually (gt_mem_nhds (by simpa using hc0))
      simpa using this
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    -- choose exponents
    have hk : ∀ n, ∃ k : ℕ, c / q < q ^ k * |(g (n + N) : Matrix (Fin 2) (Fin 2) ℝ) 0 1| ∧
        q ^ k * |(g (n + N) : Matrix (Fin 2) (Fin 2) ℝ) 0 1| ≤ c := by
      intro n
      set b := |(g (n + N) : Matrix (Fin 2) (Fin 2) ℝ) 0 1|
      have hb0 : 0 < b := abs_pos.mpr (h01 _)
      have hbc : b < c := hN (n + N) (by lia)
      obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := c / b) (y := q)
        (by rw [le_div_iff₀ hb0]; linarith) hq1
      refine ⟨k, ?_, ?_⟩
      · rw [div_lt_iff₀ (by linarith)]
        have h := (div_lt_iff₀ hb0).mp hk2
        rw [pow_succ] at h
        linarith
      · rwa [le_div_iff₀ hb0] at hk1
    choose k hk using hk
    set x : ℕ → SL(2, ℝ) := fun n ↦ D ^ k n * g (n + N) * (D ^ k n)⁻¹ with hx
    have hxK : ∀ n, x n ∈ K := fun n ↦
      mul_mem (mul_mem (pow_mem hDK _) (hg _)) (inv_mem (pow_mem hDK _))
    -- the upper-right entries are bounded, extract a convergent subsequence
    have hbd : ∀ n, (x n : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (-c) c := by
      intro n
      rw [hx, conj]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        Set.mem_Icc]
      have h1 := (hk n).2
      have hqk : 0 < q ^ k n := pow_pos (by linarith) _
      rw [← abs_le, abs_mul, abs_of_pos hqk]
      exact h1
    obtain ⟨s, hs, φ, hφ, hlimφ⟩ := isCompact_Icc.tendsto_subseq hbd
    have hgN : Tendsto (fun n ↦ g (φ n + N)) atTop (𝓝 1) :=
      hlim.comp (tendsto_atTop_mono (fun n ↦ Nat.le_add_right (φ n) N) hφ.tendsto_atTop)
    have hxlim : Tendsto (x ∘ φ) atTop (𝓝 (uU s)) := by
      apply tendsto_of_entries
      intro i j
      fin_cases i <;> fin_cases j
      · simp only [Function.comp, hx, conj]
        simpa using tendsto_entry hgN 0 0
      · exact hlimφ
      · simp only [Function.comp, hx, conj]
        have h10 := tendsto_entry hgN 1 0
        simp only [Matrix.SpecialLinearGroup.coe_one,
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h10
        have hbound : ∀ n, |(q ^ k (φ n))⁻¹| ≤ 1 := by
          intro n
          rw [abs_inv, abs_of_pos (pow_pos (by linarith) _)]
          exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1.le)
        have h0 : Tendsto (fun n ↦ (q ^ k (φ n))⁻¹ * (g (φ n + N) : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
            atTop (𝓝 0) := by
          have hn : Tendsto (fun n ↦ ‖(g (φ n + N) : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖) atTop
              (𝓝 0) := by simpa using h10.norm
          refine squeeze_zero_norm (fun n ↦ ?_) hn
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hbound n)
        simpa using h0
      · simp only [Function.comp, hx, conj]
        simpa using tendsto_entry hgN 1 1
    have hmem : uU s ∈ K := hK.mem_of_tendsto hxlim (Eventually.of_forall fun n ↦ hxK _)
    -- `|s| ≥ c/q > 0`
    have hsabs : c / q ≤ |s| := by
      have hab : Tendsto (fun n ↦ |(x (φ n) : Matrix (Fin 2) (Fin 2) ℝ) 0 1|) atTop (𝓝 |s|) :=
        hlimφ.abs
      refine ge_of_tendsto hab (Eventually.of_forall fun n ↦ ?_)
      rw [hx, conj]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      rw [abs_mul, abs_of_pos (pow_pos (by linarith) _)]
      exact (hk (φ n)).1.le
    have hcq : 0 < c / q := by positivity
    have hs0 : s ≠ 0 := by
      intro h; rw [h, abs_zero] at hsabs; linarith
    have hsle : |s| ≤ c := abs_le.mpr ⟨hs.1, hs.2⟩
    rcases hs0.lt_or_gt with hneg | hpos
    · refine ⟨-s, neg_mem hmem, ?_, ?_⟩ <;> [linarith; (rw [abs_of_neg hneg] at hsle; linarith)]
    · refine ⟨s, hmem, hpos, ?_⟩
      rw [abs_of_pos hpos] at hsle; linarith
  have hdense : Dense (S : Set ℝ) := AddSubgroup.dense_of_not_isolated_zero S hsmall
  have : (S : Set ℝ) = Set.univ := by
    rw [← hSclosed.closure_eq]; exact hdense.closure_eq
  have ht : t ∈ (S : Set ℝ) := by rw [this]; trivial
  exact ht

/-- The element `S = [[0, -1], [1, 0]]` of `SL(2, ℝ)`. -/
def wS : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

lemma wS_conj_uU (t : ℝ) : wS * uU t * wS⁻¹ = uL (-t) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, wS, coe_uU,
    coe_uL, adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma continuous_conj (g : SL(2, ℝ)) : Continuous fun x : SL(2, ℝ) ↦ g * x * g⁻¹ := by
  fun_prop

/-- **Rescaling lemma, lower version.** -/
theorem uL_mem_of_tendsto {K : Subgroup SL(2, ℝ)} (hK : IsClosed (K : Set SL(2, ℝ)))
    {D : SL(2, ℝ)} {l : ℝ} (hl : 1 < l)
    (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, l⁻¹]) (hDK : D ∈ K)
    {g : ℕ → SL(2, ℝ)} (hg : ∀ n, g n ∈ K) (hlim : Tendsto g atTop (𝓝 1))
    (h10 : ∀ n, (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0) (t : ℝ) : uL t ∈ K := by
  let K' : Subgroup SL(2, ℝ) := K.comap (MulAut.conj wS).toMonoidHom
  have hK' : IsClosed (K' : Set SL(2, ℝ)) := hK.preimage (continuous_conj wS)
  have hl0 : 0 < l := by linarith
  have hDK' : D ∈ K' := by
    change wS * D * wS⁻¹ ∈ K
    have : wS * D * wS⁻¹ = D⁻¹ := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, wS, hD,
        adjugate_fin_two]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]; exact inv_mem hDK
  have hgK' : ∀ n, wS⁻¹ * g n * wS ∈ K' := by
    intro n
    change wS * (wS⁻¹ * g n * wS) * wS⁻¹ ∈ K
    simpa [mul_assoc] using hg n
  have hlim' : Tendsto (fun n ↦ wS⁻¹ * g n * wS) atTop (𝓝 1) := by
    have := ((continuous_conj wS⁻¹).tendsto 1).comp hlim
    simpa [Function.comp_def] using this
  have h01' : ∀ n, ((wS⁻¹ * g n * wS : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0 := by
    intro n
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, wS,
      adjugate_fin_two]
    rw [eta_fin_two (g n : Matrix (Fin 2) (Fin 2) ℝ)]
    simp only [Matrix.mul_fin_two]
    simpa using h10 n
  have := uU_mem_of_tendsto hK' hl hD hDK' hgK' hlim' h01' (-t)
  change wS * uU (-t) * wS⁻¹ ∈ K at this
  rwa [wS_conj_uU, neg_neg] at this

/-- The key step: a closed subgroup containing `D = diag(l, l⁻¹)` (`l > 1`) and an element `C`
with nonzero off-diagonal entries, together with a sequence tending to `1` with nonzero upper-right
(or nonzero lower-left) entries, is all of `SL(2, ℝ)`. -/
theorem eq_top_of_seq {K : Subgroup SL(2, ℝ)} (hK : IsClosed (K : Set SL(2, ℝ)))
    {D : SL(2, ℝ)} {l : ℝ} (hl : 1 < l)
    (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, l⁻¹]) (hDK : D ∈ K)
    {C : SL(2, ℝ)} (hCK : C ∈ K) (hb : C 0 1 ≠ 0) (hc : C 1 0 ≠ 0)
    {g : ℕ → SL(2, ℝ)} (hg : ∀ n, g n ∈ K) (hlim : Tendsto g atTop (𝓝 1))
    (hne : (∀ n, (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0) ∨
      (∀ n, (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0)) : K = ⊤ := by
  have hdet := C.det_coe
  rw [det_fin_two] at hdet
  -- conjugates of unipotents by `C`
  have hseq : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≠ 0 := fun n ↦ by positivity
  have hCU : (∀ t, uU t ∈ K) → ∀ t, uL t ∈ K := by
    intro hU
    refine uL_mem_of_tendsto hK hl hD hDK (g := fun n ↦ C * uU (1 / (n + 1)) * C⁻¹)
      (fun n ↦ mul_mem (mul_mem hCK (hU _)) (inv_mem hCK)) ?_ ?_
    · have h1 : Tendsto (fun n : ℕ ↦ uU (1 / (n + 1))) atTop (𝓝 1) := by
        have := (continuous_uU.tendsto 0).comp hseq
        simpa [Function.comp_def, uU_zero] using this
      have := ((continuous_conj C).tendsto 1).comp h1
      simpa [Function.comp_def] using this
    · intro n
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uU,
        adjugate_fin_two]
      rw [eta_fin_two (C : Matrix (Fin 2) (Fin 2) ℝ)]
      simp only [Matrix.mul_fin_two]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      have hc2 : C 1 0 * C 1 0 ≠ 0 := mul_ne_zero hc hc
      intro h
      apply hc2
      have : (1 : ℝ) / (n + 1) * (C 1 0 * C 1 0) = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left (hpos n)
  have hCL : (∀ t, uL t ∈ K) → ∀ t, uU t ∈ K := by
    intro hL
    refine uU_mem_of_tendsto hK hl hD hDK (g := fun n ↦ C * uL (1 / (n + 1)) * C⁻¹)
      (fun n ↦ mul_mem (mul_mem hCK (hL _)) (inv_mem hCK)) ?_ ?_
    · have hcL : Continuous uL := continuous_uL
      have h1 : Tendsto (fun n : ℕ ↦ uL (1 / (n + 1))) atTop (𝓝 1) := by
        have := (hcL.tendsto 0).comp hseq
        have e : uL 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp
        simpa [Function.comp_def, e] using this
      have := ((continuous_conj C).tendsto 1).comp h1
      simpa [Function.comp_def] using this
    · intro n
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uL,
        adjugate_fin_two]
      rw [eta_fin_two (C : Matrix (Fin 2) (Fin 2) ℝ)]
      simp only [Matrix.mul_fin_two]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      have hb2 : C 0 1 * C 0 1 ≠ 0 := mul_ne_zero hb hb
      intro h
      apply hb2
      have : (1 : ℝ) / (n + 1) * (C 0 1 * C 0 1) = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left (hpos n)
  rcases hne with h01 | h10
  · have hU := uU_mem_of_tendsto hK hl hD hDK hg hlim h01
    exact eq_top_of_unipotents hU (hCU hU)
  · have hL := uL_mem_of_tendsto hK hl hD hDK hg hlim h10
    exact eq_top_of_unipotents (hCL hL) hL

end OrbicurveCores.SL2R
