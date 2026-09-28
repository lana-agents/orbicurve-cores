/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# Tail convex combinations in Hilbert spaces

In a real Hilbert space, every bounded sequence `x` admits *tail convex combinations*
`y n ∈ conv {x k | n ≤ k}` which converge in norm (a weak form of the Banach–Saks / Komlós
theorems). The proof: pick `y n` with norm within `1 / (n + 1)` of the minimal norm `d n` on the
`n`-th tail hull. Since midpoints stay in the hull, the parallelogram law makes `(y n)` Cauchy.

The weights are recorded as finitely supported functions `w n : ℕ →₀ ℝ`.
-/

open Filter Topology

namespace OrbicurveCores

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The convex combinations of `x k`, `n ≤ k`. -/
def tailHull (x : ℕ → E) (n : ℕ) : Set E :=
  {y | ∃ w : ℕ →₀ ℝ, (∀ k, 0 ≤ w k) ∧ (w.sum fun _ c ↦ c) = 1 ∧ (∀ k ∈ w.support, n ≤ k) ∧
    y = w.sum fun k c ↦ c • x k}

lemma self_mem_tailHull (x : ℕ → E) (n : ℕ) : x n ∈ tailHull x n := by
  refine ⟨Finsupp.single n 1, fun k ↦ ?_, by simp, fun k hk ↦ ?_, by simp⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hk
    split_ifs at hk with h
    · exact h.le
    · exact absurd rfl hk

lemma tailHull_anti (x : ℕ → E) {n m : ℕ} (h : n ≤ m) : tailHull x m ⊆ tailHull x n := by
  rintro y ⟨w, h0, h1, hs, rfl⟩
  exact ⟨w, h0, h1, fun k hk ↦ h.trans (hs k hk), rfl⟩

lemma midpoint_mem_tailHull (x : ℕ → E) (n : ℕ) {y y' : E} (hy : y ∈ tailHull x n)
    (hy' : y' ∈ tailHull x n) : (1 / 2 : ℝ) • (y + y') ∈ tailHull x n := by
  obtain ⟨w, h0, h1, hs, rfl⟩ := hy
  obtain ⟨w', h0', h1', hs', rfl⟩ := hy'
  refine ⟨(1 / 2 : ℝ) • (w + w'), fun k ↦ ?_, ?_, fun k hk ↦ ?_, ?_⟩
  · simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
    have := h0 k; have := h0' k; positivity
  · rw [Finsupp.sum_smul_index' (fun _ ↦ rfl), Finsupp.sum_add_index' (fun _ ↦ smul_zero _)
      (fun _ _ _ ↦ smul_add _ _ _), ← Finsupp.smul_sum, ← Finsupp.smul_sum, h1, h1']
    norm_num
  · have hk' := Finsupp.support_smul hk
    rcases Finset.mem_union.mp (Finsupp.support_add hk') with h | h
    exacts [hs k h, hs' k h]
  · symm
    rw [Finsupp.sum_smul_index' (fun i ↦ zero_smul ℝ (x i)), Finsupp.sum_add_index'
      (fun i ↦ by simp) (fun i _ _ ↦ by rw [← add_smul, smul_add]), smul_add]
    simp only [Finsupp.smul_sum, smul_smul, smul_eq_mul]

/-- **Tail convex combinations.** A bounded sequence in a real Hilbert space has convex
combinations of its tails that converge in norm. -/
theorem exists_tail_convex_tendsto [CompleteSpace E] (x : ℕ → E) {M : ℝ}
    (hx : ∀ n, ‖x n‖ ≤ M) :
    ∃ w : ℕ → ℕ →₀ ℝ, (∀ n k, 0 ≤ w n k) ∧ (∀ n, ((w n).sum fun _ c ↦ c) = 1) ∧
      (∀ n, ∀ k ∈ (w n).support, n ≤ k) ∧
      ∃ z, Tendsto (fun n ↦ (w n).sum fun k c ↦ c • x k) atTop (𝓝 z) := by
  set d : ℕ → ℝ := fun n ↦ sInf (norm '' tailHull x n) with hd_def
  have hne : ∀ n, (norm '' tailHull x n).Nonempty := fun n ↦
    ⟨_, Set.mem_image_of_mem _ (self_mem_tailHull x n)⟩
  have hbdd : ∀ n, BddBelow (norm '' tailHull x n) := fun n ↦
    ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg y⟩
  have hd_le : ∀ n, ∀ y ∈ tailHull x n, d n ≤ ‖y‖ := fun n y hy ↦
    csInf_le (hbdd n) (Set.mem_image_of_mem _ hy)
  have hd0 : ∀ n, 0 ≤ d n := fun n ↦ le_csInf (hne n) (by rintro _ ⟨y, -, rfl⟩; positivity)
  have hdM : ∀ n, d n ≤ M := fun n ↦ (hd_le n _ (self_mem_tailHull x n)).trans (hx n)
  have hmono : Monotone d := fun n m h ↦
    csInf_le_csInf (hbdd n) (hne m) (Set.image_mono (tailHull_anti x h))
  have hbddA : BddAbove (Set.range d) := ⟨M, by rintro _ ⟨n, rfl⟩; exact hdM n⟩
  set D := ⨆ n, d n
  have hdD : ∀ n, d n ≤ D := fun n ↦ le_ciSup hbddA n
  have hdlim : Tendsto d atTop (𝓝 D) := tendsto_atTop_ciSup hmono hbddA
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεanti : Antitone ε := fun n m h ↦ by
    simp only [ε]; gcongr
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hy : ∀ n, ∃ y ∈ tailHull x n, ‖y‖ < d n + ε n := fun n ↦ by
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_lt_of_csInf_lt (hne n) (lt_add_of_pos_right (d n) (hε n))
    exact ⟨y, hy, h⟩
  choose y hyT hyn using hy
  -- the Cauchy estimate
  set b : ℕ → ℝ := fun n ↦ 2 * (d n + ε n) ^ 2 + 2 * (D + ε n) ^ 2 - 4 * d n ^ 2
  have hb : ∀ n m, n ≤ m → ‖y n - y m‖ ^ 2 ≤ b n := by
    intro n m hnm
    have hmid := hd_le n _ (midpoint_mem_tailHull x n (hyT n) (tailHull_anti x hnm (hyT m)))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at hmid
    have h1 : 2 * d n ≤ ‖y n + y m‖ := by linarith
    have h2 : (2 * d n) ^ 2 ≤ ‖y n + y m‖ ^ 2 := pow_le_pow_left₀ (by linarith [hd0 n]) h1 2
    have h3 : ‖y n‖ ^ 2 ≤ (d n + ε n) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hyn n).le 2
    have h4 : ‖y m‖ ^ 2 ≤ (D + ε n) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((hyn m).le.trans (add_le_add (hdD m) (hεanti hnm))) 2
    have hpar := parallelogram_law_with_norm ℝ (y n) (y m)
    simp only [b]
    nlinarith
  have hblim : Tendsto b atTop (𝓝 0) := by
    have : Tendsto b atTop (𝓝 (2 * (D + 0) ^ 2 + 2 * (D + 0) ^ 2 - 4 * D ^ 2)) := by
      simp only [b]
      exact (((hdlim.add hεlim).pow 2).const_mul 2 |>.add
        (((tendsto_const_nhds.add hεlim).pow 2).const_mul 2)).sub ((hdlim.pow 2).const_mul 4)
    simpa [show 2 * D ^ 2 + 2 * D ^ 2 - 4 * D ^ 2 = 0 by ring] using this
  have hcauchy : CauchySeq y := by
    refine cauchySeq_of_le_tendsto_0 (fun N ↦ 2 * √(b N)) (fun n m N hn hm ↦ ?_) ?_
    · calc dist (y n) (y m) ≤ dist (y N) (y n) + dist (y N) (y m) := dist_triangle_left _ _ _
        _ ≤ √(b N) + √(b N) := by
          gcongr <;> rw [dist_eq_norm] <;>
            exact Real.le_sqrt_of_sq_le (hb N _ ‹_›)
        _ = 2 * √(b N) := by ring
    · simpa using (hblim.sqrt).const_mul 2
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  choose w hw0 hw1 hws hwy using hyT
  exact ⟨w, hw0, hw1, hws, z, by simpa only [← hwy] using hz⟩

end OrbicurveCores
