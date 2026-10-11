/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.CuspStructure
import OrbicurveCores.Genuine.Assembly

/-!
# R3b–R3c: reduction of `CommIndexFour` to the translation case

Let `Γ₀ = ⟨A₀, B₀⟩` be a once-punctured torus group in Fricke normal form (with the triangle
inequalities) which admits a core, and `Δ = Comm(Γ₀)`. Write `N = [Δ : Γ₀]!`, so that `δ ^ N ∈ Γ₀`
for every `δ ∈ Δ` (`pow_factorial_relIndex_mem`).

* For `δ ∈ Δ`, `δ u_{4N} δ⁻¹ = (δ u₄ δ⁻¹) ^ N ∈ Γ₀`, so by the one-cusp lemma
  (`exists_mem_lowerLeft_eq_zero`) some `γ δ` (`γ ∈ Γ₀`) is upper triangular.
* Upper triangular elements `u ∈ Δ` are `±uU s`: `u ^ N ∈ Γ₀` has diagonal `±1`
  (`upper_mem_commensurator`).
* The translations `{s | uU s ∈ Δ}` form a discrete subgroup of `ℝ` (if `uU s ∈ Δ` then
  `uU (N s) ∈ Γ₀`) containing `1` (`uU_one_mem_nHemi`), hence equal `(1/m) ℤ`, `m ≥ 1`
  (`exists_transl_commensurator`).
* If `m = 1`, then `Δ ≤ Γ⁺ = nHemi`, so `[Δ : Γ₀] = 4`; otherwise `uU (1/m) ∈ Δ` with `m ≥ 2`
  (`relIndex_commensurator_normal_or`).

The remaining case is `TranslationCase` (R3d, not proved here). Finally the index `[Comm(Γ) : Γ]`
is transported from the normal form to arbitrary once-punctured torus groups: it is invariant under
`GL(2, ℝ)`-conjugation (`relIndex_commensurator_map`) and under sign changes of the generators
(`relIndex_commensurator_signs`; both groups miss `-1` by freeness of the normal form).

Main result: `commIndexFour_of_translationCase : TranslationCase → CommIndexFour`.
-/

open Matrix UpperHalfPlane
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace OrbicurveCores.Fuchsian

/-- If `[K : H] ≠ 0`, then `a ^ [K : H]! ∈ H` for all `a ∈ K`. -/
lemma pow_factorial_relIndex_mem {G : Type*} [Group G] {H K : Subgroup G}
    (h : H.relIndex K ≠ 0) {a : G} (ha : a ∈ K) : a ^ (H.relIndex K).factorial ∈ H := by
  obtain ⟨n, hn, hle, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h ha
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hn hle
  rw [hk, pow_mul]; exact pow_mem hmem.1 k

section normal

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

include hx hy in
/-- Upper triangular elements of `Comm(Γ₀)` are `±` translations. -/
lemma upper_mem_commensurator (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel}))
    {u : SL(2, ℝ)} (hu : u ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}))
    (hu10 : u 1 0 = 0) : ∃ s, u = SL2R.uU s ∨ u = -SL2R.uU s := by
  haveI := discreteTopology_normal hx hy hz hrel
  set N := ((Subgroup.closure {nA hz hrel, nB hz hrel}).relIndex
    (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}))).factorial
  have hN : 0 < N := Nat.factorial_pos _
  have hmem := pow_factorial_relIndex_mem hcore hu
  have hD := lowerRight_eq_one_or_neg_one (by norm_num : (4 : ℝ) ≠ 0) (uU_four_mem hz hrel) hmem
    (upper_pow hu10 N).1
  rw [(upper_pow hu10 N).2] at hD
  have habs : |u 1 1| = 1 := by
    have : |u 1 1| ^ N = 1 := by
      rw [← abs_pow]; rcases hD with h | h <;> simp [h]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hN.ne').mp this
  have hdet := det_upper hu10
  rcases (abs_eq zero_le_one).mp habs with h | h
  · refine ⟨u 0 1, Or.inl ?_⟩
    have h00 : u 0 0 = 1 := by rw [h] at hdet; linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h, hu10]
  · refine ⟨-u 0 1, Or.inr ?_⟩
    have h00 : u 0 0 = -1 := by rw [h] at hdet; linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h, hu10]

include hx hy in
/-- Every `δ ∈ Comm(Γ₀)` is, up to `Γ₀` on the left, `± uU s` with `uU s ∈ Comm(Γ₀)`. -/
lemma exists_mul_eq_uU (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})) {δ : SL(2, ℝ)}
    (hδ : δ ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) :
    ∃ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}, ∃ s,
      SL2R.uU s ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) ∧
        (γ * δ = SL2R.uU s ∨ γ * δ = -SL2R.uU s) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  set N := (Γ.relIndex (commensurator Γ)).factorial
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos _
  have hu4 : SL2R.uU 4 ∈ commensurator Γ := le_commensurator _ (uU_four_mem hz hrel)
  have hc : δ * SL2R.uU (N * 4) * δ⁻¹ ∈ Γ := by
    have := pow_factorial_relIndex_mem hcore (mul_mem (mul_mem hδ hu4) (inv_mem hδ))
    rwa [conj_pow, uU_pow_eq] at this
  obtain ⟨γ, hγ, h0⟩ := exists_mem_lowerLeft_eq_zero hx hy hz hrel h1 h2 h3
    (by positivity : (N : ℝ) * 4 ≠ 0) hc
  have hγδ : γ * δ ∈ commensurator Γ := mul_mem (le_commensurator _ hγ) hδ
  obtain ⟨s, hs⟩ := upper_mem_commensurator hx hy hz hrel hcore hγδ h0
  refine ⟨γ, hγ, s, ?_, hs⟩
  rcases hs with hs | hs
  · rwa [← hs]
  · have := mul_mem hγδ (neg_one_mem_commensurator' Γ)
    rw [hs] at this
    simpa using this

include hx hy in
/-- The translations in `Comm(Γ₀)` are `(1/m) ℤ` for some `m ≥ 1`. -/
lemma exists_transl_commensurator
    (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})) :
    ∃ m : ℕ, 0 < m ∧ transl (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) =
      AddSubgroup.zmultiples (1 / (m : ℝ)) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  haveI := discreteTopology_normal hx hy hz hrel
  obtain ⟨ε, hε, hb⟩ := exists_transl_bound Γ
  set N := (Γ.relIndex (commensurator Γ)).factorial
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos _
  have h1 : (1 : ℝ) ∈ transl (commensurator Γ) :=
    nHemi_le_commensurator hz hrel (uU_one_mem_nHemi hz hrel)
  rcases (transl (commensurator Γ)).dense_or_cyclic with hd | ⟨a, ha⟩
  · exfalso
    obtain ⟨s, hs, hs0, hsε⟩ := hd.exists_between (show (0 : ℝ) < ε / N by positivity)
    have hmem : SL2R.uU (N * s) ∈ Γ := by
      rw [← uU_pow_eq]; exact pow_factorial_relIndex_mem hcore hs
    rw [lt_div_iff₀ hN] at hsε
    have := hb _ hmem (by rw [abs_of_pos (by positivity)]; linarith)
    exact (mul_pos hN hs0).ne' this
  · rw [← AddSubgroup.zmultiples_eq_closure] at ha
    rw [ha] at h1 ⊢
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp h1
    have hja : (j : ℝ) * a = 1 := by simpa [zsmul_eq_mul] using hj
    have hj0 : j ≠ 0 := by rintro rfl; simp at hja
    refine ⟨j.natAbs, Int.natAbs_pos.mpr hj0, ?_⟩
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj0
    have ha' : a = 1 / j := by field_simp; linarith
    rcases le_or_gt 0 j with hpos | hneg
    · have : ((j.natAbs : ℕ) : ℝ) = j := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hpos)]
      rw [this, ha']
    · have : ((j.natAbs : ℕ) : ℝ) = -j := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
      rw [this, ha', ← AddSubgroup.zmultiples_neg]
      congr 1; ring

include hx hy in
/-- **R3c (normal form).** If `Γ₀` admits a core, then either `[Comm(Γ₀) : Γ₀] = 4`, or
`Comm(Γ₀)` contains the translation `z ↦ z + 1/m` for some `m ≥ 2`. -/
theorem relIndex_commensurator_normal_or (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})) :
    (Subgroup.closure {nA hz hrel, nB hz hrel}).relIndex
        (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) = 4 ∨
      ∃ m : ℕ, 2 ≤ m ∧
        SL2R.uU (1 / m) ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  obtain ⟨m, hm, hS⟩ := exists_transl_commensurator hx hy hz hrel hcore
  by_cases hm1 : m = 1
  · left
    subst hm1
    have hle : commensurator Γ ≤ nHemi hz hrel := by
      intro δ hδ
      obtain ⟨γ, hγ, s, hs, hγδ⟩ := exists_mul_eq_uU hx hy hz hrel h1 h2 h3 hcore hδ
      have hsZ : s ∈ AddSubgroup.zmultiples (1 / ((1 : ℕ) : ℝ)) := hS ▸ hs
      have hsH : SL2R.uU s ∈ nHemi hz hrel := by
        have hZ : AddSubgroup.zmultiples (1 / ((1 : ℕ) : ℝ)) ≤ transl (nHemi hz hrel) := by
          rw [AddSubgroup.zmultiples_le]
          simpa [mem_transl] using uU_one_mem_nHemi hz hrel
        exact hZ hsZ
      have hγδ' : γ * δ ∈ nHemi hz hrel := by
        rcases hγδ with e | e
        · rw [e]; exact hsH
        · rw [e]; simpa using mul_mem (neg_one_mem_nHemi hz hrel) hsH
      simpa using mul_mem (inv_mem (le_nHemi hz hrel hγ)) hγδ'
    have : commensurator Γ = nHemi hz hrel := le_antisymm hle (nHemi_le_commensurator hz hrel)
    rw [this]; exact relIndex_nHemi hx hy hz hrel
  · right
    refine ⟨m, by omega, ?_⟩
    have : (1 / (m : ℝ)) ∈ transl (commensurator Γ) := by
      rw [hS]; exact AddSubgroup.mem_zmultiples _
    exact this

end normal

end OrbicurveCores.Fuchsian
