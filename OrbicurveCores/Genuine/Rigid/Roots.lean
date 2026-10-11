/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.Basic

/-!
# Simple roots of polynomials with holomorphic coefficients

Let `Q z` be monic polynomials of fixed degree whose coefficients are holomorphic in `z` on an open
set `U`. A simple root `τ` of `Q z₀` continues to a holomorphic root `s z` of `Q z` near `z₀`,
which is the only root of `Q z` near `τ` (`exists_root_branch`).

The proof follows oka's `differentiableAt_of_isRoot`: the divided difference
`H(z, σ, σ') = (Q_z σ - Q_z σ') / (σ - σ')` is continuous and equals `Q_z' τ ≠ 0` at
`(z₀, τ, τ)`, which gives uniqueness; existence comes from `|Q_z τ| = ∏ |τ - σᵢ|`; and
`s z = s z₁ - Q_z (s z₁) / H(z, s z, s z₁)` gives holomorphy.
-/

open Polynomial Metric Set Filter
open scoped Topology

namespace OrbicurveCores.Rigid

variable {Q : ℂ → ℂ[X]} {N : ℕ}

/-- The divided difference of `Q z` at `σ, σ'`. -/
noncomputable def divDiff (Q : ℂ → ℂ[X]) (N : ℕ) (z σ σ' : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), (Q z).coeff k * ∑ i ∈ Finset.range k, σ ^ i * σ' ^ (k - 1 - i)

lemma eval_eq_sum (hN : ∀ z, (Q z).natDegree ≤ N) (z T : ℂ) :
    (Q z).eval T = ∑ k ∈ Finset.range (N + 1), (Q z).coeff k * T ^ k :=
  eval_eq_sum_range' (Nat.lt_succ_of_le (hN z)) T

lemma eval_sub_eval (hN : ∀ z, (Q z).natDegree ≤ N) (z σ σ' : ℂ) :
    (Q z).eval σ - (Q z).eval σ' = (σ - σ') * divDiff Q N z σ σ' := by
  rw [eval_eq_sum hN, eval_eq_sum hN, ← Finset.sum_sub_distrib, divDiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← mul_sub, mul_left_comm, ← (Commute.all σ σ').geom_sum₂_mul k, mul_comm (_ : ℂ) (σ - σ')]

lemma divDiff_self (hN : ∀ z, (Q z).natDegree ≤ N) (z τ : ℂ) :
    divDiff Q N z τ τ = (Q z).derivative.eval τ := by
  rw [divDiff, derivative_eval, Polynomial.sum_over_range' _ (fun n ↦ by simp) (N + 1)
    (Nat.lt_succ_of_le (hN z))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have : ∀ i ∈ Finset.range k, τ ^ i * τ ^ (k - 1 - i) = τ ^ (k - 1) := fun i hi ↦ by
    rw [← pow_add]; congr 1; rw [Finset.mem_range] at hi; omega
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma continuousOn_divDiff {U : Set ℂ} (hc : ∀ k, ContinuousOn (fun z ↦ (Q z).coeff k) U) :
    ContinuousOn (fun q : ℂ × ℂ × ℂ ↦ divDiff Q N q.1 q.2.1 q.2.2) (U ×ˢ univ) := by
  unfold divDiff
  refine continuousOn_finsetSum _ fun k _ ↦ ((hc k).comp continuousOn_fst
    fun q hq ↦ hq.1).mul (Continuous.continuousOn ?_)
  fun_prop

lemma continuousOn_eval {U : Set ℂ} (hN : ∀ z, (Q z).natDegree ≤ N)
    (hc : ∀ k, ContinuousOn (fun z ↦ (Q z).coeff k) U) :
    ContinuousOn (fun q : ℂ × ℂ ↦ (Q q.1).eval q.2) (U ×ˢ univ) := by
  simp_rw [eval_eq_sum hN]
  exact continuousOn_finsetSum _ fun k _ ↦ ((hc k).comp continuousOn_fst
    fun q hq ↦ hq.1).mul (continuous_snd.pow k).continuousOn

/-- Near a root of a monic polynomial, nearby monic polynomials of the same degree have a root. -/
lemma eventually_exists_root (hmon : ∀ z, (Q z).Monic) {n : ℕ} (hn : ∀ z, (Q z).natDegree = n)
    {z₀ τ : ℂ} (hτ : (Q z₀).IsRoot τ) (hcont : ContinuousAt (fun z ↦ (Q z).eval τ) z₀) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ z in 𝓝 z₀, ∃ σ, (Q z).IsRoot σ ∧ ‖σ - τ‖ < ε := by
  have hc : Tendsto (fun z ↦ (Q z).eval τ) (𝓝 z₀) (𝓝 0) := by
    simpa [hτ.eq_zero] using hcont.tendsto
  filter_upwards [(tendsto_norm_zero.comp hc).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε ^ n by positivity))] with z hz
  by_contra! h
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hmon z)
    IsAlgClosed.card_roots_eq_natDegree
  have hev : ‖(Q z).eval τ‖ = ((Q z).roots.map fun σ ↦ ‖τ - σ‖).prod := by
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    change (normHom : ℂ →*₀ ℝ) _ = _
    rw [map_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hpow : ∀ (m : Multiset ℝ), (∀ x ∈ m, ε ≤ x) → ε ^ Multiset.card m ≤ m.prod := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons x m ih =>
      intro hm
      rw [Multiset.card_cons, pow_succ, Multiset.prod_cons, mul_comm]
      have hx := hm x (Multiset.mem_cons_self x m)
      exact mul_le_mul hx (ih fun y hy ↦ hm y (Multiset.mem_cons_of_mem hy)) (by positivity)
        (hε.le.trans hx)
  have hle : ε ^ n ≤ ‖(Q z).eval τ‖ := by
    rw [hev, ← hn z, ← IsAlgClosed.card_roots_eq_natDegree,
      ← Multiset.card_map (fun σ ↦ ‖τ - σ‖)]
    refine hpow _ fun x hx ↦ ?_
    obtain ⟨σ, hσ, rfl⟩ := Multiset.mem_map.1 hx
    rw [norm_sub_rev]
    exact h σ (isRoot_of_mem_roots hσ)
  exact lt_irrefl _ (hle.trans_lt hz)

/-- If `a` is differentiable at `x` with `a x = 0` and `k` is continuous at `x`, then `a * k` is
differentiable at `x` (oka's `hasFDerivAt_mul_of_continuousAt`, in one variable). -/
lemma differentiableAt_mul_of_continuousAt {a k : ℂ → ℂ} {x : ℂ} (ha : DifferentiableAt ℂ a x)
    (ha0 : a x = 0) (hk : ContinuousAt k x) : DifferentiableAt ℂ (fun y ↦ a y * k y) x := by
  have hd := ha.hasFDerivAt
  refine (HasFDerivAt.of_isLittleO (f' := k x • fderiv ℂ a x) ?_).differentiableAt
  have h₁ : (fun y ↦ k y • (a y - a x - fderiv ℂ a x (y - x))) =o[𝓝 x]
      fun y ↦ (1 : ℂ) • (y - x) :=
    (hk.tendsto.isBigO_one ℂ).smul_isLittleO hd.isLittleO
  have h₂ : (fun y ↦ (k y - k x) • fderiv ℂ a x (y - x)) =o[𝓝 x]
      fun y ↦ (1 : ℂ) • (y - x) := by
    refine Asymptotics.IsLittleO.smul_isBigO ?_ ((fderiv ℂ a x).isBigO_sub _ x)
    rw [Asymptotics.isLittleO_one_iff]
    simpa using hk.tendsto.sub_const (k x)
  refine ((h₁.add h₂).congr_left fun y ↦ ?_).congr_right fun y ↦ one_smul ℂ _
  simp only [smul_eq_mul, ha0, FunLike.coe_smul, Pi.smul_apply]
  ring

/-- **Holomorphic continuation of a simple root.** -/
theorem exists_root_branch {U : Set ℂ} (hU : IsOpen U) (hN : ∀ z, (Q z).natDegree ≤ N)
    (hmon : ∀ z, (Q z).Monic) {n : ℕ} (hn : ∀ z, (Q z).natDegree = n)
    (hd : ∀ k, DifferentiableOn ℂ (fun z ↦ (Q z).coeff k) U) {z₀ τ : ℂ} (hz₀ : z₀ ∈ U)
    (hτ : (Q z₀).IsRoot τ) (hsimple : (Q z₀).derivative.eval τ ≠ 0) :
    ∃ V ⊆ U, IsOpen V ∧ z₀ ∈ V ∧ ∃ ε > (0 : ℝ), ∃ s : ℂ → ℂ, DifferentiableOn ℂ s V ∧
      s z₀ = τ ∧ ∀ z ∈ V, (Q z).IsRoot (s z) ∧ ‖s z - τ‖ < ε ∧
        ∀ σ, (Q z).IsRoot σ → ‖σ - τ‖ < ε → σ = s z := by
  have hc : ∀ k, ContinuousOn (fun z ↦ (Q z).coeff k) U := fun k ↦ (hd k).continuousOn
  have hUU : U ×ˢ (univ : Set (ℂ × ℂ)) ∈ 𝓝 (z₀, τ, τ) :=
    prod_mem_nhds (hU.mem_nhds hz₀) univ_mem
  have hHc : ContinuousAt (fun q : ℂ × ℂ × ℂ ↦ divDiff Q N q.1 q.2.1 q.2.2) (z₀, τ, τ) :=
    (continuousOn_divDiff (N := N) hc).continuousAt hUU
  have hH0 : divDiff Q N z₀ τ τ ≠ 0 := by rwa [divDiff_self hN]
  obtain ⟨r, hr, hrH⟩ := Metric.eventually_nhds_iff.mp (hHc.eventually_ne hH0)
  obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set ε := r
  have hHne : ∀ z σ σ', dist z z₀ < r → ‖σ - τ‖ < ε → ‖σ' - τ‖ < ε →
      divDiff Q N z σ σ' ≠ 0 := fun z σ σ' hz hσ hσ' ↦ by
    refine hrH (y := (z, σ, σ')) ?_
    rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
    exact ⟨hz, by rwa [dist_eq_norm], by rwa [dist_eq_norm]⟩
  have huniq : ∀ z σ σ', dist z z₀ < r → (Q z).IsRoot σ → (Q z).IsRoot σ' → ‖σ - τ‖ < ε →
      ‖σ' - τ‖ < ε → σ = σ' := fun z σ σ' hz h1 h2 h3 h4 ↦ by
    have := eval_sub_eval hN z σ σ'
    rw [h1.eq_zero, h2.eq_zero, sub_zero, eq_comm, mul_eq_zero] at this
    exact sub_eq_zero.mp (this.resolve_right (hHne z σ σ' hz h3 h4))
  have hcont : ∀ z₁ ∈ U, ∀ T, ContinuousAt (fun z ↦ (Q z).eval T) z₁ := fun z₁ hz₁ T ↦
    ((continuousOn_eval hN hc).comp (continuousOn_id.prodMk continuousOn_const)
      fun z hz ↦ ⟨hz, trivial⟩).continuousAt (hU.mem_nhds hz₁)
  obtain ⟨r₂, hr₂, hex⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_exists_root hmon hn hτ (hcont z₀ hz₀ τ) hr)
  set ρ := min (min r r') r₂
  have hρ : 0 < ρ := lt_min (lt_min hr hr') hr₂
  set V := ball z₀ ρ
  have hVU : V ⊆ U := (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))).trans hr'U
  have hVr : ∀ z ∈ V, dist z z₀ < r := fun z hz ↦
    lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hVex : ∀ z ∈ V, ∃ σ, (Q z).IsRoot σ ∧ ‖σ - τ‖ < ε := fun z hz ↦
    hex z (ball_subset_ball (min_le_right _ _) hz)
  classical
  set s : ℂ → ℂ := fun z ↦ if h : ∃ σ, (Q z).IsRoot σ ∧ ‖σ - τ‖ < ε then h.choose else τ
  have hs : ∀ z ∈ V, (Q z).IsRoot (s z) ∧ ‖s z - τ‖ < ε := fun z hz ↦ by
    simp only [s, dif_pos (hVex z hz)]; exact (hVex z hz).choose_spec
  have hsu : ∀ z ∈ V, ∀ σ, (Q z).IsRoot σ → ‖σ - τ‖ < ε → σ = s z := fun z hz σ h1 h2 ↦
    huniq z σ (s z) (hVr z hz) h1 (hs z hz).1 h2 (hs z hz).2
  have hz₀V : z₀ ∈ V := mem_ball_self hρ
  have hs0 : s z₀ = τ := (hsu z₀ hz₀V τ hτ (by simpa using hr)).symm
  -- continuity
  have hsc : ∀ z₁ ∈ V, ContinuousAt s z₁ := by
    intro z₁ hz₁
    rw [Metric.continuousAt_iff]
    intro ε' hε'
    have hε'' : 0 < min ε' (ε - ‖s z₁ - τ‖) := lt_min hε' (sub_pos.mpr (hs z₁ hz₁).2)
    obtain ⟨δ, hδ, hδex⟩ := Metric.eventually_nhds_iff.mp
      ((eventually_exists_root hmon hn (hs z₁ hz₁).1 (hcont z₁ (hVU hz₁) _) hε'').and
        (isOpen_ball.mem_nhds hz₁))
    refine ⟨δ, hδ, fun z hz ↦ ?_⟩
    obtain ⟨⟨σ, hσ, hσd⟩, hzV⟩ := hδex hz
    have hστ : ‖σ - τ‖ < ε := by
      have := norm_sub_le_norm_sub_add_norm_sub σ (s z₁) τ
      have := hσd.trans_le (min_le_right _ _)
      linarith
    rw [← hsu z hzV σ hσ hστ, dist_eq_norm]
    exact hσd.trans_le (min_le_left _ _)
  -- differentiability
  refine ⟨V, hVU, isOpen_ball, hz₀V, ε, hr, s, fun z₁ hz₁ ↦ ?_, hs0,
    fun z hz ↦ ⟨(hs z hz).1, (hs z hz).2, hsu z hz⟩⟩
  have hg : DifferentiableAt ℂ (fun z ↦ (Q z).eval (s z₁)) z₁ := by
    simp_rw [eval_eq_sum hN]
    exact DifferentiableAt.fun_sum fun k _ ↦
      ((hd k).differentiableAt (hU.mem_nhds (hVU hz₁))).mul_const _
  have hg0 : (Q z₁).eval (s z₁) = 0 := (hs z₁ hz₁).1
  set k : ℂ → ℂ := fun z ↦ -(divDiff Q N z (s z) (s z₁))⁻¹
  have hkc : ContinuousAt k z₁ := by
    have hp : ContinuousAt (fun z ↦ (z, s z, s z₁)) z₁ :=
      continuousAt_id.prodMk ((hsc z₁ hz₁).prodMk continuousAt_const)
    have hH : ContinuousAt (fun q : ℂ × ℂ × ℂ ↦ divDiff Q N q.1 q.2.1 q.2.2) (z₁, s z₁, s z₁) :=
      (continuousOn_divDiff (N := N) hc).continuousAt
        (prod_mem_nhds (hU.mem_nhds (hVU hz₁)) univ_mem)
    have h1 : ContinuousAt (fun z ↦ divDiff Q N z (s z) (s z₁)) z₁ :=
      ContinuousAt.comp_of_eq (g := fun q : ℂ × ℂ × ℂ ↦ divDiff Q N q.1 q.2.1 q.2.2)
        (f := fun z ↦ (z, s z, s z₁)) hH hp rfl
    exact (h1.inv₀ (hHne _ _ _ (hVr z₁ hz₁) (hs z₁ hz₁).2 (hs z₁ hz₁).2)).neg
  have hm := (differentiableAt_mul_of_continuousAt hg hg0 hkc).const_add (s z₁)
  refine (hm.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_ball.mem_nhds hz₁] with z hz
  have h1 := eval_sub_eval hN z (s z) (s z₁)
  rw [(hs z hz).1.eq_zero, zero_sub] at h1
  have hne := hHne z (s z) (s z₁) (hVr z hz) (hs z hz).2 (hs z₁ hz₁).2
  simp only [k]
  field_simp
  linear_combination -h1

end OrbicurveCores.Rigid
