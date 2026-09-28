/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Defs

/-!
# The `j`-function is an orbifold covering

We prove `JOrbStatement`: `jC` is an orbifold covering of `ℂ` from `ℍ` with signature `sig`.

* `exists_localForm`: a nonconstant analytic `f` is `f z₀ + g ^ n` near `z₀` for a local
  coordinate `g`; `exists_localForm_of_rot`: if `F` is invariant under a rotation of order `e` and
  equal values of `F` near `0` differ by `e`-th roots of unity, then `n = e` (both divisibilities
  are read off from slopes at `0`).
* In the Cayley coordinate `cay τ₀` at `τ₀ ∈ ℍ`, the stabiliser of `τ₀` in `SL(2, ℤ)` acts by the
  rotations `cmul γ τ₀` (`cay_smulC`); these are square roots of unity at `i` and cube roots of
  unity at `ρ` (`cmul_sq_of_fix_I`, `cmul_cube_of_fix_ρ`), with `-1`, resp. `ρ`, attained. The
  Eisenstein transformation laws give `j(ρ) = 0` and `j(i) = 1728`.
* `exists_localData`: by proper discontinuity, the fibres of `j` near `τ₀` are orbits of the
  stabiliser, which yields an orbifold chart of order `e` at `τ₀` (`LocalData`); its translates by
  `SL(2, ℤ)` are pairwise equal or disjoint and cover `j⁻¹(disc)` (`LocalData.cover`), and they give
  local normal forms along the whole fibre (`LocalData.hasLocalForm`).
-/

open Complex Metric Set Filter Topology Function UpperHalfPlane Uniformization
open scoped ComplexConjugate MatrixGroups

namespace OrbicurveCores.S1

/-! ### Local normal forms of analytic functions -/

/-- **Local normal form.** A nonconstant analytic function is `f z₀ + g ^ n` near `z₀`, for a
local coordinate `g` at `z₀` and some `n ≥ 1`. -/
theorem exists_localForm {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hnc : ¬ ∀ᶠ z in 𝓝 z₀, f z = f z₀) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = 0 ∧ deriv g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, f z = f z₀ + g z ^ n := by
  have han : AnalyticAt ℂ (fun z ↦ f z - f z₀) z₀ := hf.sub analyticAt_const
  have hnc' : ¬ ∀ᶠ z in 𝓝 z₀, f z - f z₀ = 0 := by
    simpa only [sub_eq_zero] using hnc
  obtain ⟨n, g, hg, hg0, hfg⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnc'
  simp only [smul_eq_mul] at hfg
  have hn : n ≠ 0 := by
    rintro rfl
    have := hfg.self_of_nhds
    simp only [sub_self, pow_zero, one_mul] at this
    exact hg0 this.symm
  set c := g z₀ ^ ((n : ℂ)⁻¹)
  have hc : c ^ n = g z₀ := cpow_nat_inv_pow _ hn
  have hc0 : c ≠ 0 := by
    rintro h
    rw [h, zero_pow hn] at hc
    exact hg0 hc.symm
  set q : ℂ → ℂ := fun z ↦ g z / g z₀
  have hq : AnalyticAt ℂ q z₀ := hg.div analyticAt_const hg0
  have hq1 : q z₀ = 1 := div_self hg0
  set r : ℂ → ℂ := fun z ↦ c * q z ^ ((n : ℂ)⁻¹)
  have hr : AnalyticAt ℂ r z₀ := analyticAt_const.mul
    (hq.cpow analyticAt_const (by rw [hq1]; exact one_mem_slitPlane))
  have hr0 : r z₀ = c := by simp only [r, hq1, one_cpow, mul_one]
  refine ⟨n, Nat.pos_of_ne_zero hn, fun z ↦ (z - z₀) * r z,
    (analyticAt_id.sub analyticAt_const).mul hr, by simp, ?_, ?_⟩
  · have hd : HasDerivAt (fun z ↦ (z - z₀) * r z) (1 * r z₀ + (z₀ - z₀) * deriv r z₀) z₀ :=
      ((hasDerivAt_id z₀).sub_const z₀).mul hr.differentiableAt.hasDerivAt
    rw [hd.deriv, hr0]
    simpa using hc0
  · filter_upwards [hfg] with z hz
    have hrn : r z ^ n = g z := by
      simp only [r, mul_pow, cpow_nat_inv_pow _ hn, hc, q]
      field_simp
    rw [mul_pow, hrn, ← hz]
    ring

/-- The slope of a function with a derivative at `0` vanishing at `0`. -/
theorem tendsto_div_of_hasDerivAt {h : ℂ → ℂ} {a : ℂ} (hd : HasDerivAt h a 0) (h0 : h 0 = 0) :
    Tendsto (fun t ↦ h t / t) (𝓝[≠] 0) (𝓝 a) := by
  have := hd.tendsto_slope_zero
  refine this.congr' (Eventually.of_forall fun t ↦ ?_)
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  ring

/-- **Local normal form under a rotation symmetry.** Let `F` be analytic at `0`, invariant under
the rotation by `u₀` of order `e`, and suppose that near `0` equal values of `F` differ by an
`e`-th root of unity. Then `F = F 0 + g ^ e` for a local coordinate `g` at `0`. -/
theorem exists_localForm_of_rot {F : ℂ → ℂ} {e : ℕ} (hF : AnalyticAt ℂ F 0) {δ : ℝ}
    (hδ : 0 < δ)
    (hQ : ∀ s₁ ∈ ball (0 : ℂ) δ, ∀ s₂ ∈ ball (0 : ℂ) δ, F s₁ = F s₂ →
      ∃ u : ℂ, u ^ e = 1 ∧ s₂ = u * s₁)
    {u₀ : ℂ} (hu₀ : ∀ m : ℕ, u₀ ^ m = 1 → e ∣ m)
    (hR : ∀ s ∈ ball (0 : ℂ) δ, F (u₀ * s) = F s) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 0, F s = F 0 + g s ^ e := by
  -- `F` is not locally constant
  have hnc : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), F s = F 0 := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
    set s : ℂ := ((min ε δ / 2 : ℝ) : ℂ)
    have hs : s ∈ ball (0 : ℂ) (min ε δ) := by
      rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [lt_min hε hδ]
    have hs0 : s ≠ 0 := by
      simp only [s, ne_eq, ofReal_eq_zero]; exact (by positivity : min ε δ / 2 ≠ 0)
    obtain ⟨u, -, hu⟩ := hQ 0 (mem_ball_self hδ) s (ball_subset_ball (min_le_right _ _) hs)
      (hball s (ball_subset_ball (min_le_left _ _) hs)).symm
    exact hs0 (by rw [hu, mul_zero])
  obtain ⟨n, hn, φ, hφ, hφ0, hφ', hFφ⟩ := exists_localForm hF hnc
  set a := deriv φ 0
  have hsφ : HasStrictDerivAt φ a 0 := hφ.hasStrictDerivAt
  set ψ := hsφ.localInverse φ a 0 hφ'
  have hψ : HasStrictDerivAt ψ a⁻¹ 0 := by
    have := hsφ.to_localInverse hφ'
    rwa [hφ0] at this
  have hleft : ∀ᶠ s in 𝓝 0, ψ (φ s) = s := hsφ.eventually_left_inverse hφ'
  have hright : ∀ᶠ t in 𝓝 0, φ (ψ t) = t := by
    have := hsφ.eventually_right_inverse hφ'
    rwa [hφ0] at this
  have hψ0 : ψ 0 = 0 := by
    have := hleft.self_of_nhds
    rwa [hφ0] at this
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by
    have := hψ.hasDerivAt.continuousAt.tendsto
    rwa [hψ0] at this
  have hslope : Tendsto (fun t ↦ ψ t / t) (𝓝[≠] 0) (𝓝 a⁻¹) :=
    tendsto_div_of_hasDerivAt hψ.hasDerivAt hψ0
  have hball : ∀ᶠ s in 𝓝 (0 : ℂ), s ∈ ball (0 : ℂ) δ := ball_mem_nhds 0 hδ
  -- eventually along `t → 0`, `ψ t` is a good point
  have hgood : ∀ᶠ t in 𝓝 (0 : ℂ), ψ t ∈ ball (0 : ℂ) δ ∧ F (ψ t) = F 0 + t ^ n ∧
      (t ≠ 0 → ψ t ≠ 0) := by
    filter_upwards [hψt.eventually hball, hψt.eventually hFφ, hright] with t h1 h2 h3
    refine ⟨h1, by rw [h2, h3], fun ht h ↦ ht ?_⟩
    rw [← h3, h, hφ0]
  -- upper bound: `n ∣ e`
  have hne : n ∣ e := by
    set ζ := exp (2 * Real.pi * Complex.I / n)
    have hζ : IsPrimitiveRoot ζ n := isPrimitiveRoot_exp n hn.ne'
    have hζ0 : ζ ≠ 0 := exp_ne_zero _
    have hζt : Tendsto (fun t ↦ ζ * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun t ↦ ζ * t) (𝓝 0) (𝓝 (ζ * 0)) := (continuous_const_mul ζ).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_ne_zero hζ0 ht
    have hU : Tendsto (fun t ↦ ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t))) (𝓝[≠] 0)
        (𝓝 (ζ * (a⁻¹ / a⁻¹))) :=
      tendsto_const_nhds.mul ((hslope.comp hζt).div hslope (inv_ne_zero hφ'))
    rw [div_self (inv_ne_zero hφ'), mul_one] at hU
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t))) ^ e = 1 := by
      filter_upwards [hgood.filter_mono nhdsWithin_le_nhds,
        (hζt.eventually (hgood.filter_mono nhdsWithin_le_nhds)), self_mem_nhdsWithin]
        with t h1 h2 ht
      have ht : t ≠ 0 := ht
      have hψt0 := h1.2.2 ht
      have heq : F (ψ t) = F (ψ (ζ * t)) := by
        rw [h1.2.1, h2.2.1, mul_pow, hζ.pow_eq_one, one_mul]
      obtain ⟨u, hu, hu'⟩ := hQ _ h1.1 _ h2.1 heq
      have : ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t)) = u := by
        rw [hu']; field_simp
      rw [this, hu]
    have hlim : Tendsto (fun t ↦ (ζ * ((ψ (ζ * t) / (ζ * t)) / (ψ t / t))) ^ e) (𝓝[≠] 0)
        (𝓝 (ζ ^ e)) := hU.pow e
    have : ζ ^ e = 1 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono
      fun _ h ↦ h.symm))
    exact hζ.dvd_of_pow_eq_one e this
  -- lower bound: `e ∣ n`
  have hen : e ∣ n := by
    set h : ℂ → ℂ := fun t ↦ φ (u₀ * ψ t)
    have hd : HasDerivAt h (a * (u₀ * a⁻¹)) 0 := by
      have h1 : HasDerivAt (fun t ↦ u₀ * ψ t) (u₀ * a⁻¹) 0 := hψ.hasDerivAt.const_mul u₀
      have h2 : HasDerivAt φ a (u₀ * ψ 0) := by
        rw [hψ0, mul_zero]; exact hφ.differentiableAt.hasDerivAt
      exact h2.comp 0 h1
    have ha : a * (u₀ * a⁻¹) = u₀ := by field_simp
    rw [ha] at hd
    have h0 : h 0 = 0 := by simp only [h, hψ0, mul_zero, hφ0]
    have hsl := tendsto_div_of_hasDerivAt hd h0
    have hut : Tendsto (fun t ↦ u₀ * ψ t) (𝓝 0) (𝓝 0) := by
      have := hψt.const_mul u₀
      rwa [mul_zero] at this
    have hev : ∀ᶠ t in 𝓝 (0 : ℂ), h t ^ n = t ^ n := by
      filter_upwards [hgood, hut.eventually hFφ] with t h1 h2
      have := h2.symm.trans ((hR _ h1.1).trans h1.2.1)
      exact add_left_cancel this
    have hev' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (h t / t) ^ n = 1 := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t h1 ht
      have ht : t ≠ 0 := ht
      rw [div_pow, h1, div_self (pow_ne_zero _ ht)]
    have : u₀ ^ n = 1 := tendsto_nhds_unique (hsl.pow n) (tendsto_const_nhds.congr' (hev'.mono
      fun _ h ↦ h.symm))
    exact hu₀ n this
  exact ⟨φ, hφ, hφ0, hφ', by rwa [Nat.dvd_antisymm hne hen] at hFφ⟩

/-! ### The Cayley map centred at a point of `ℍ` -/

/-- The Cayley map `ℍ → 𝔻` centred at `τ`. -/
noncomputable def cay (τ z : ℂ) : ℂ := (z - τ) / (z - conj τ)

/-- The inverse of the Cayley map centred at `τ`. -/
noncomputable def cayInv (τ s : ℂ) : ℂ := (τ - conj τ * s) / (1 - s)

theorem sub_conj_ne_zero {τ z : ℂ} (hτ : 0 < τ.im) (hz : 0 < z.im) : z - conj τ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [sub_im, conj_im, zero_im] at this
  linarith

theorem one_sub_ne_zero_of_norm_lt {s : ℂ} (hs : ‖s‖ < 1) : 1 - s ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hs
  exact lt_irrefl _ hs

theorem cay_self (τ : ℂ) : cay τ τ = 0 := by simp [cay]

theorem cayInv_zero (τ : ℂ) : cayInv τ 0 = τ := by simp [cayInv]

theorem cayInv_cay {τ z : ℂ} (hτ : 0 < τ.im) (hz : 0 < z.im) : cayInv τ (cay τ z) = z := by
  have h1 := sub_conj_ne_zero hτ hz
  have h2 : τ - conj τ ≠ 0 := sub_conj_ne_zero hτ hτ
  unfold cayInv cay
  rw [div_eq_iff]
  · field_simp
    ring
  · rw [one_sub_div h1]
    exact div_ne_zero (by rwa [sub_sub_sub_cancel_left]) h1

theorem cay_cayInv {τ s : ℂ} (hτ : 0 < τ.im) (hs : ‖s‖ < 1) : cay τ (cayInv τ s) = s := by
  have h1 := one_sub_ne_zero_of_norm_lt hs
  have h2 : τ - conj τ ≠ 0 := sub_conj_ne_zero hτ hτ
  unfold cayInv cay
  have h3 : (τ - conj τ * s) / (1 - s) - conj τ = (τ - conj τ) / (1 - s) := by
    field_simp; ring
  rw [h3, div_eq_iff (div_ne_zero h2 h1)]
  field_simp
  ring

theorem cayInv_eq (τ s : ℂ) (hs : ‖s‖ < 1) :
    cayInv τ s = τ.re + τ.im * Uniformization.cayleyInv s := by
  have h1 := one_sub_ne_zero_of_norm_lt hs
  unfold cayInv Uniformization.cayleyInv
  field_simp
  apply Complex.ext <;> simp <;> ring

theorem im_cayInv_pos {τ s : ℂ} (hτ : 0 < τ.im) (hs : ‖s‖ < 1) : 0 < (cayInv τ s).im := by
  rw [cayInv_eq τ s hs]
  have := Uniformization.im_cayleyInv_pos (w := s) (by rwa [mem_ball_zero_iff])
  simpa using mul_pos hτ this

theorem analyticAt_cayInv (τ : ℂ) {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (cayInv τ) s :=
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hs.symm)

theorem analyticAt_cay {τ z : ℂ} (hτ : 0 < τ.im) (hz : 0 < z.im) : AnalyticAt ℂ (cay τ) z :=
  (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
    (sub_conj_ne_zero hτ hz)

theorem deriv_cay_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : deriv (cay τ) τ ≠ 0 := by
  have h2 : τ - conj τ ≠ 0 := sub_conj_ne_zero hτ hτ
  have hd : HasDerivAt (cay τ) ((1 * (τ - conj τ) - (τ - τ) * 1) / (τ - conj τ) ^ 2) τ :=
    ((hasDerivAt_id τ).sub_const τ).div ((hasDerivAt_id τ).sub_const _) h2
  rw [hd.deriv, sub_self, zero_mul, sub_zero, one_mul]
  exact div_ne_zero h2 (pow_ne_zero _ h2)

theorem continuousOn_cay {τ : ℂ} (hτ : 0 < τ.im) : ContinuousOn (cay τ) upper :=
  fun _ hz ↦ (analyticAt_cay hτ hz).continuousAt.continuousWithinAt

/-! ### The action of `SL(2, ℤ)` on `ℂ` -/

/-- The Möbius transformation of `γ` as a function on `ℂ`. -/
noncomputable def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)

theorem det_coe (γ : SL(2, ℤ)) : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2
  rw [Matrix.det_fin_two] at this
  exact_mod_cast this

theorem denom_coe_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im] at him
  have hc : γ 1 0 = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' hz.ne'
  have hre := congrArg Complex.re h
  simp only [hc, Int.cast_zero, zero_mul, zero_add, intCast_re, zero_re] at hre
  have hd : γ 1 1 = 0 := by exact_mod_cast hre
  have := det_coe γ
  rw [hc, hd] at this
  simp at this

theorem smulC_eq_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : smulC γ z = mob γ z := by
  rw [smulC_of_im_pos γ hz, coe_specialLinearGroup_apply]
  simp [mob]

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) z := by
  have h := ((hasDerivAt_id z).const_mul (γ 0 0 : ℂ) |>.add_const (γ 0 1 : ℂ)).div
    ((hasDerivAt_id z).const_mul (γ 1 0 : ℂ) |>.add_const (γ 1 1 : ℂ)) (denom_coe_ne_zero γ hz)
  refine h.congr_deriv ?_
  congr 1
  simp only [id]
  linear_combination det_coe γ

theorem smulC_eventuallyEq_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    smulC γ =ᶠ[𝓝 z] mob γ := by
  filter_upwards [Uniformization.isOpen_upper.mem_nhds hz] with y hy
  exact smulC_eq_mob γ hy

theorem hasDerivAt_smulC (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (smulC γ) (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) z :=
  (hasDerivAt_mob γ hz).congr_of_eventuallyEq (smulC_eventuallyEq_mob γ hz)

theorem differentiableOn_smulC (γ : SL(2, ℤ)) : DifferentiableOn ℂ (smulC γ) upper :=
  fun _ hz ↦ (hasDerivAt_smulC γ hz).differentiableAt.differentiableWithinAt

theorem analyticAt_smulC (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (smulC γ) z :=
  (differentiableOn_smulC γ).analyticAt (Uniformization.isOpen_upper.mem_nhds hz)

theorem deriv_smulC_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : deriv (smulC γ) z ≠ 0 := by
  rw [(hasDerivAt_smulC γ hz).deriv]
  exact div_ne_zero one_ne_zero (pow_ne_zero _ (denom_coe_ne_zero γ hz))

theorem smulC_smulC (γ γ' : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    smulC γ (smulC γ' z) = smulC (γ * γ') z := by
  rw [smulC_of_im_pos γ' hz, smulC_of_im_pos γ (γ' • (⟨z, hz⟩ : ℍ)).im_pos,
    smulC_of_im_pos _ hz, mul_smul]

theorem smulC_one {z : ℂ} (hz : 0 < z.im) : smulC 1 z = z := by
  rw [smulC_of_im_pos 1 hz, one_smul]

theorem smulC_inv_smulC (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : smulC γ⁻¹ (smulC γ z) = z := by
  rw [smulC_smulC _ _ hz, inv_mul_cancel, smulC_one hz]

theorem smulC_smulC_inv (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : smulC γ (smulC γ⁻¹ z) = z := by
  rw [smulC_smulC _ _ hz, mul_inv_cancel, smulC_one hz]

theorem smulC_coe (γ : SL(2, ℤ)) (τ : ℍ) : smulC γ τ = ((γ • τ : ℍ) : ℂ) :=
  smulC_of_im_pos γ τ.im_pos

/-! ### The stabiliser acts by rotations in the Cayley coordinate -/

/-- The rotation factor of `γ` at a fixed point `τ`, in the Cayley coordinate at `τ`. -/
noncomputable def cmul (γ : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  ((γ 1 0 : ℂ) * conj τ + γ 1 1) / ((γ 1 0 : ℂ) * τ + γ 1 1)

theorem fix_eq {γ : SL(2, ℤ)} {τ : ℍ} (h : γ • τ = τ) :
    (γ 0 0 : ℂ) * τ + γ 0 1 = τ * ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  have h' := congrArg ((↑) : ℍ → ℂ) h
  rw [← smulC_coe, smulC_eq_mob γ τ.im_pos, mob, div_eq_iff (denom_coe_ne_zero γ τ.im_pos)] at h'
  exact h'

theorem smul_eq_self_of {γ : SL(2, ℤ)} {τ : ℍ}
    (h : (γ 0 0 : ℂ) * τ + γ 0 1 = τ * ((γ 1 0 : ℂ) * τ + γ 1 1)) : γ • τ = τ := by
  apply UpperHalfPlane.ext
  rw [← smulC_coe, smulC_eq_mob γ τ.im_pos, mob, div_eq_iff (denom_coe_ne_zero γ τ.im_pos)]
  exact h

theorem conj_denom (γ : SL(2, ℤ)) (τ : ℂ) :
    (γ 1 0 : ℂ) * conj τ + γ 1 1 = conj ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  simp only [map_add, map_mul, map_intCast]

theorem mob_sub_aux (a b c d t z : ℂ) (hdet : a * d - b * c = 1)
    (ht : a * t + b = t * (c * t + d)) (hD : c * z + d ≠ 0) (hDt : c * t + d ≠ 0) :
    (a * z + b) / (c * z + d) - t = (z - t) / ((c * z + d) * (c * t + d)) := by
  rw [eq_div_iff (mul_ne_zero hD hDt)]
  have e : (a * z + b) / (c * z + d) * (c * z + d) = a * z + b := div_mul_cancel₀ _ hD
  linear_combination (c * t + d) * e + (z - t) * hdet + (c * z + d) * ht

theorem cay_smulC {γ : SL(2, ℤ)} {τ : ℍ} (hγ : γ • τ = τ) {z : ℂ} (hz : 0 < z.im) :
    cay τ (smulC γ z) = cmul γ τ * cay τ z := by
  have hdet := det_coe γ
  have ht := fix_eq hγ
  have ht' : (γ 0 0 : ℂ) * conj (τ : ℂ) + γ 0 1 =
      conj (τ : ℂ) * ((γ 1 0 : ℂ) * conj (τ : ℂ) + γ 1 1) := by
    have := congrArg conj ht
    simpa only [map_add, map_mul, map_intCast] using this
  have hD := denom_coe_ne_zero γ hz
  have hDt := denom_coe_ne_zero γ τ.im_pos
  have hDt' : (γ 1 0 : ℂ) * conj (τ : ℂ) + γ 1 1 ≠ 0 := by
    rw [conj_denom]; exact (map_ne_zero _).mpr hDt
  have hz' := sub_conj_ne_zero τ.im_pos hz
  rw [smulC_eq_mob γ hz, cay, mob, mob_sub_aux _ _ _ _ _ _ hdet ht hD hDt,
    mob_sub_aux _ _ _ _ _ _ hdet ht' hD hDt', cmul, cay]
  have hD2 : z * (γ 1 0 : ℂ) + γ 1 1 ≠ 0 := by rwa [mul_comm]
  have hDt2 : (τ : ℂ) * (γ 1 0 : ℂ) + γ 1 1 ≠ 0 := by rwa [mul_comm]
  field_simp

theorem norm_cmul (γ : SL(2, ℤ)) (τ : ℍ) : ‖cmul γ τ‖ = 1 := by
  have hDt := denom_coe_ne_zero γ τ.im_pos
  rw [cmul, conj_denom, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hDt)]

/-! ### The stabilisers of `i` and `ρ` -/

theorem cmul_sq_of_fix_I {γ : SL(2, ℤ)} (h : γ • UpperHalfPlane.I = UpperHalfPlane.I) :
    cmul γ UpperHalfPlane.I ^ 2 = 1 := by
  have hfix := fix_eq h
  have hre : ((γ 0 1 : ℤ) : ℝ) = -(γ 1 0 : ℝ) := by simpa using congrArg Complex.re hfix
  have him : ((γ 0 0 : ℤ) : ℝ) = (γ 1 1 : ℝ) := by simpa using congrArg Complex.im hfix
  have hb : γ 0 1 = -γ 1 0 := by exact_mod_cast hre
  have ha : γ 0 0 = γ 1 1 := by exact_mod_cast him
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast det_coe γ
  rw [ha, hb] at hdet
  have hcd : γ 1 0 * γ 1 1 = 0 := by
    have h1 : γ 1 0 ^ 2 ≤ 1 := by nlinarith
    have h2 : -1 ≤ γ 1 0 ∧ γ 1 0 ≤ 1 := by constructor <;> nlinarith
    rcases h2 with ⟨h2, h3⟩
    interval_cases hc : γ 1 0
    · have : γ 1 1 = 0 := by nlinarith
      simp [this]
    · simp
    · have : γ 1 1 = 0 := by nlinarith
      simp [this]
  have hcd' : (γ 1 0 : ℂ) * γ 1 1 = 0 := by exact_mod_cast hcd
  have hD := denom_coe_ne_zero γ (z := Complex.I) (by simp)
  rw [cmul, coe_I, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hD), conj_I]
  linear_combination (-4 * Complex.I) * hcd'

theorem coe_ρ : (ρ : ℂ) = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := rfl

theorem conj_ρ : conj (ρ : ℂ) = -1 - ρ := by
  apply Complex.ext <;> norm_num [coe_ρ]

theorem ρ_sq' : (ρ : ℂ) ^ 2 + ρ + 1 = 0 := by
  linear_combination ρ_sq

theorem ρ_im_ne : (ρ : ℂ).im ≠ 0 := ρ.im_pos.ne'

theorem cmul_cube_of_fix_ρ {γ : SL(2, ℤ)} (h : γ • ρ = ρ) : cmul γ ρ ^ 3 = 1 := by
  have hfix := fix_eq h
  have key : (((γ 0 0 + γ 1 0 - γ 1 1 : ℤ) : ℂ)) * ρ + ((γ 0 1 + γ 1 0 : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination hfix + (γ 1 0 : ℂ) * ρ_sq'
  have him := congrArg Complex.im key
  have hre := congrArg Complex.re key
  simp only [mul_im, intCast_re, intCast_im, zero_mul, add_zero, add_im, zero_im,
    mul_re, add_re, sub_zero, zero_re] at him hre
  have ha : γ 0 0 + γ 1 0 - γ 1 1 = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' ρ_im_ne
  rw [ha] at hre
  simp only [Int.cast_zero, zero_mul, zero_add] at hre
  have hb : γ 0 1 + γ 1 0 = 0 := by exact_mod_cast hre
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast det_coe γ
  have hq : γ 1 1 ^ 2 - γ 1 0 * γ 1 1 + γ 1 0 ^ 2 = 1 := by
    have h1 : γ 0 0 = γ 1 1 - γ 1 0 := by linarith
    have h2 : γ 0 1 = - γ 1 0 := by linarith
    rw [h1, h2] at hdet
    linear_combination hdet
  have hc3 : γ 1 0 ^ 3 = γ 1 0 := by
    have h1 : -1 ≤ γ 1 0 ∧ γ 1 0 ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (2 * γ 1 1 - γ 1 0)]
    rcases h1 with ⟨h1, h2⟩
    interval_cases γ 1 0 <;> norm_num
  have hq' : (γ 1 1 : ℂ) ^ 2 - γ 1 0 * γ 1 1 + (γ 1 0 : ℂ) ^ 2 = 1 := by exact_mod_cast hq
  have hc3' : (γ 1 0 : ℂ) ^ 3 = γ 1 0 := by exact_mod_cast hc3
  have hD := denom_coe_ne_zero γ ρ.im_pos
  rw [cmul, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hD), conj_ρ]
  linear_combination (-2 * (γ 1 0 : ℂ) ^ 3 * ρ - (γ 1 0 : ℂ) ^ 3) * ρ_sq' +
    (-6 * (γ 1 0 : ℂ) * ρ - 3 * (γ 1 0 : ℂ)) * hq' + (6 * (ρ : ℂ) + 3) * hc3'

/-- The element `[[-1, -1], [1, 0]]` of order `3` in `PSL(2, ℤ)`, fixing `ρ`. -/
def gρ : SL(2, ℤ) := ⟨!![-1, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem gρ_smul : gρ • ρ = ρ := by
  apply smul_eq_self_of
  simp only [gρ, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Int.cast_neg, Int.cast_one, Int.cast_zero]
  linear_combination -ρ_sq

theorem cmul_gρ : cmul gρ ρ = ρ := by
  have hρ : (ρ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; exact ρ_im_ne (by simpa using this)
  simp only [cmul, gρ, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Int.cast_one, Int.cast_zero, one_mul, add_zero, conj_ρ]
  rw [div_eq_iff hρ]
  linear_combination -ρ_sq

theorem ρ_ne_one : (ρ : ℂ) ≠ 1 := by
  intro h; have := congrArg Complex.re h; norm_num [coe_ρ] at this

theorem ρ_cube : (ρ : ℂ) ^ 3 = 1 := by
  linear_combination ((ρ : ℂ) - 1) * ρ_sq'

theorem dvd_of_ρ_pow {m : ℕ} (h : (ρ : ℂ) ^ m = 1) : 3 ∣ m := by
  have : orderOf (ρ : ℂ) = 3 := orderOf_eq_prime ρ_cube ρ_ne_one
  rw [← this]
  exact orderOf_dvd_of_pow_eq_one h

theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply smul_eq_self_of
  simp only [ModularGroup.S, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one, Int.cast_zero, coe_I]
  ring_nf
  rw [I_sq]

theorem cmul_S_I : cmul ModularGroup.S UpperHalfPlane.I = -1 := by
  simp only [cmul, ModularGroup.S, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Int.cast_one, Int.cast_zero, one_mul, add_zero, coe_I, conj_I]
  rw [div_eq_iff I_ne_zero]
  ring

theorem dvd_of_neg_one_pow {m : ℕ} (h : (-1 : ℂ) ^ m = 1) : 2 ∣ m := by
  have : orderOf (-1 : ℂ) = 2 := orderOf_eq_prime (by norm_num) (by norm_num)
  rw [← this]
  exact orderOf_dvd_of_pow_eq_one h

section values

open Matrix.SpecialLinearGroup CongruenceSubgroup

theorem E₄_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₄ (γ • τ) = denom γ τ ^ (4 : ℤ) * ModularForm.E₄ τ := by
  letI : SlashInvariantFormClass (ModularForm 𝒮ℒ 4) Γ(1) 4 :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  exact SlashInvariantForm.slash_action_eqn_SL'' ModularForm.E₄ (mem_Gamma_one γ) τ

theorem E₆_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₆ (γ • τ) = denom γ τ ^ (6 : ℤ) * ModularForm.E₆ τ := by
  letI : SlashInvariantFormClass (ModularForm 𝒮ℒ 6) Γ(1) 6 :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  exact SlashInvariantForm.slash_action_eqn_SL'' ModularForm.E₆ (mem_Gamma_one γ) τ

theorem E₄_ρ : ModularForm.E₄ ρ = 0 := by
  have h := E₄_smul gρ ρ
  rw [gρ_smul] at h
  have hd : denom gρ ρ = ρ := by
    simp [denom, gρ]
  rw [hd] at h
  have h4 : (ρ : ℂ) ^ (4 : ℤ) = ρ := by
    rw [show (4 : ℤ) = ((3 + 1 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, ρ_cube, one_mul]
  rw [h4] at h
  have : (1 - (ρ : ℂ)) * ModularForm.E₄ ρ = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ρ_ne_one.symm)

theorem E₆_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have h := E₆_smul ModularGroup.S UpperHalfPlane.I
  rw [S_smul_I] at h
  have hd : denom ModularGroup.S UpperHalfPlane.I = Complex.I := by
    simp [denom, ModularGroup.S]
  rw [hd] at h
  have h6 : Complex.I ^ (6 : ℤ) = -1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast,
      show 6 = 2 * 3 by norm_num, pow_mul, I_sq]
    norm_num
  rw [h6] at h
  linear_combination h / 2

theorem modularJ_ρ : Heights.modularJ ρ = 0 := (Heights.modularJ_eq_zero_iff ρ).mpr E₄_ρ

theorem modularJ_I : Heights.modularJ UpperHalfPlane.I = 1728 := by
  have hΔ := Heights.modularJ_denominator_eq_E₄_E₆ UpperHalfPlane.I
  rw [E₆_I] at hΔ
  have hne := ModularForm.discriminant_ne_zero UpperHalfPlane.I
  have hE : ModularForm.E₄ UpperHalfPlane.I ^ 3 ≠ 0 := by
    intro h; rw [h] at hΔ; apply hne; rw [hΔ]; ring
  rw [Heights.modularJ, hΔ, zero_pow two_ne_zero, sub_zero, div_div_eq_mul_div,
    mul_div_cancel_left₀ _ hE]

end values

theorem jC_ρ : jC ρ = 0 := by rw [jC_coe, modularJ_ρ]

theorem jC_I : jC UpperHalfPlane.I = 1728 := by rw [jC_coe, modularJ_I]

theorem jBranch_eq : jBranch = {1728, 0} := by
  rw [jBranch, modularJ_I, modularJ_ρ]

/-! ### Orbifold charts of `j` at a point of `ℍ` -/

/-- Orbifold chart data of `jC` at `τ₀`: an `OrbChart` over `jC τ₀` whose domain `U` is a
neighbourhood of `τ₀` in `ℍ`, stable under the stabiliser of `τ₀`, meeting its translates only
through the stabiliser, and whose coordinate `u` is a local coordinate at `τ₀`. -/
structure LocalData (τ₀ : ℂ) (e : ℕ) (r : ℝ) (U : Set ℂ) (u v : ℂ → ℂ) : Prop where
  chart : OrbChart jC (jC τ₀) e r U u v
  mem : τ₀ ∈ U
  sub : U ⊆ upper
  analyticAt : AnalyticAt ℂ u τ₀
  u_self : u τ₀ = 0
  deriv_ne : deriv u τ₀ ≠ 0
  stab : ∀ γ : SL(2, ℤ), ∀ z ∈ U, smulC γ z ∈ U → smulC γ τ₀ = τ₀
  inv : ∀ γ : SL(2, ℤ), smulC γ τ₀ = τ₀ → ∀ z ∈ U, smulC γ z ∈ U

/-- Proper discontinuity: a neighbourhood of `τ₀` meeting its translates only through the
stabiliser of `τ₀`. -/
theorem exists_nhds_stab (τ₀ : ℍ) :
    ∃ N ∈ 𝓝 τ₀, ∀ γ : SL(2, ℤ), ∀ z ∈ N, γ • z ∈ N → γ • τ₀ = τ₀ := by
  obtain ⟨U, hU, hUγ⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self 𝒮ℒ τ₀
  refine ⟨U, hU, fun γ z hz hγz ↦ ?_⟩
  let g : 𝒮ℒ := ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ, γ, rfl⟩
  have hg : ∀ x : ℍ, g • x = γ • x := fun x ↦ rfl
  have := hUγ g ⟨γ • z, ⟨z, hz, hg z⟩, hγz⟩
  rwa [hg] at this

theorem smulC_eq_self_iff {γ : SL(2, ℤ)} {τ₀ : ℍ} : smulC γ τ₀ = τ₀ ↔ γ • τ₀ = τ₀ := by
  rw [smulC_coe]
  exact ⟨fun h ↦ UpperHalfPlane.ext h, fun h ↦ by rw [h]⟩

/-- **Orbifold charts of `j`.** If the stabiliser of `τ₀` acts in the Cayley coordinate by `e`-th
roots of unity, one of which has order exactly `e`, then `j` has an orbifold chart of order `e`
at `τ₀`. -/
theorem exists_localData (τ₀ : ℍ) {e : ℕ} (he : 0 < e)
    (hS : ∀ γ : SL(2, ℤ), γ • τ₀ = τ₀ → cmul γ τ₀ ^ e = 1)
    {γ₀ : SL(2, ℤ)} (hγ₀ : γ₀ • τ₀ = τ₀) (hR : ∀ m : ℕ, cmul γ₀ τ₀ ^ m = 1 → e ∣ m) :
    ∃ r > 0, ∃ U u v, LocalData (τ₀ : ℂ) e r U u v := by
  set τ : ℂ := ↑τ₀
  have hτ : 0 < τ.im := τ₀.im_pos
  set w := jC τ
  set F : ℂ → ℂ := fun s ↦ jC (cayInv τ s)
  -- proper discontinuity
  obtain ⟨N, hN, hNγ⟩ := exists_nhds_stab τ₀
  set N' : Set ℂ := (↑) '' N
  have hN' : N' ∈ 𝓝 τ := by
    have := isOpenEmbedding_coe.isOpenMap.image_mem_nhds hN
    simpa using this
  have hN'mem : ∀ z (hz : 0 < z.im), z ∈ N' → (⟨z, hz⟩ : ℍ) ∈ N := by
    rintro z hz ⟨x, hx, rfl⟩
    exact hx
  have hstab : ∀ (γ : SL(2, ℤ)) (z : ℂ), 0 < z.im → z ∈ N' → smulC γ z ∈ N' →
      γ • τ₀ = τ₀ := by
    intro γ z hz h1 h2
    refine hNγ γ ⟨z, hz⟩ (hN'mem z hz h1) ?_
    have := hN'mem _ (im_smulC_pos γ hz) h2
    simpa only [smulC_of_im_pos γ hz] using this
  -- a disc on which `F` has fibres the orbits of the stabiliser
  have hcont : Tendsto (cayInv τ) (𝓝 0) (𝓝 τ) := by
    have := (analyticAt_cayInv τ (zero_ne_one (α := ℂ))).continuousAt.tendsto
    rwa [cayInv_zero] at this
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < 1 ∧ cayInv τ s ∈ N' := by
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos, hcont hN'] with s h1 h2
    exact ⟨by rwa [mem_ball_zero_iff] at h1, h2⟩
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hQ : ∀ s₁ ∈ ball (0 : ℂ) δ₀, ∀ s₂ ∈ ball (0 : ℂ) δ₀, F s₁ = F s₂ →
      ∃ u : ℂ, u ^ e = 1 ∧ s₂ = u * s₁ := by
    intro s₁ h₁ s₂ h₂ hF
    obtain ⟨h₁1, h₁N⟩ := hball s₁ h₁
    obtain ⟨h₂1, h₂N⟩ := hball s₂ h₂
    have hz₁ := im_cayInv_pos hτ h₁1
    have hz₂ := im_cayInv_pos hτ h₂1
    obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq ⟨_, hz₂⟩ ⟨_, hz₁⟩ (by
      rw [← jC_of_im_pos hz₂, ← jC_of_im_pos hz₁]; exact hF.symm)
    have hsm : smulC γ (cayInv τ s₁) = cayInv τ s₂ := by rw [smulC_of_im_pos γ hz₁, hγ]
    have hfix : γ • τ₀ = τ₀ := hstab γ _ hz₁ h₁N (by rw [hsm]; exact h₂N)
    refine ⟨cmul γ τ₀, hS γ hfix, ?_⟩
    have := cay_smulC hfix hz₁
    rwa [hsm, cay_cayInv hτ h₂1, cay_cayInv hτ h₁1] at this
  have hRF : ∀ s ∈ ball (0 : ℂ) δ₀, F (cmul γ₀ τ₀ * s) = F s := by
    intro s hs
    obtain ⟨h1, -⟩ := hball s hs
    have hz := im_cayInv_pos hτ h1
    have h2 := cay_smulC hγ₀ hz
    rw [cay_cayInv hτ h1] at h2
    have h3 : cayInv τ (cmul γ₀ τ₀ * s) = smulC γ₀ (cayInv τ s) := by
      rw [← h2, cayInv_cay hτ (im_smulC_pos γ₀ hz)]
    simp only [F]
    rw [h3, jC_smulC γ₀ hz]
  have hj : AnalyticAt ℂ jC τ := differentiableOn_jC.analyticAt (isOpen_upper.mem_nhds hτ)
  have hFan : AnalyticAt ℂ F 0 :=
    (by rw [cayInv_zero]; exact hj : AnalyticAt ℂ jC (cayInv τ 0)).comp
      (analyticAt_cayInv τ (zero_ne_one (α := ℂ)))
  obtain ⟨φ, hφ, hφ0, hφ', hFφ⟩ := exists_localForm_of_rot hFan hδ₀ hQ hR hRF
  have hF0 : F 0 = w := by simp only [F, cayInv_zero, w]
  -- the inverse of the local coordinate
  set a := deriv φ 0
  have hs : HasStrictDerivAt φ a 0 := hφ.hasStrictDerivAt
  set E := (hs.hasStrictFDerivAt_equiv hφ').toOpenPartialHomeomorph φ
  have hsrc : (0 : ℂ) ∈ E.source :=
    (hs.hasStrictFDerivAt_equiv hφ').mem_toOpenPartialHomeomorph_source
  have htgt : (0 : ℂ) ∈ E.target := by
    have := (hs.hasStrictFDerivAt_equiv hφ').image_mem_toOpenPartialHomeomorph_target
    rwa [hφ0] at this
  have hEφ : ∀ x, E x = φ x := fun _ ↦ rfl
  have hE0 : E.symm 0 = 0 := by
    have := E.left_inv hsrc
    rwa [hEφ, hφ0] at this
  have hanN : ∀ᶠ s in 𝓝 (0 : ℂ), AnalyticAt ℂ φ s := hφ.eventually_analyticAt
  have hdN : ∀ᶠ s in 𝓝 (0 : ℂ), deriv φ s ≠ 0 := hφ.deriv.continuousAt.eventually_ne hφ'
  have hev1 : ∀ᶠ s in 𝓝 (0 : ℂ), s ∈ E.source ∧ F s = w + φ s ^ e ∧ AnalyticAt ℂ φ s ∧
      deriv φ s ≠ 0 ∧ s ∈ ball (0 : ℂ) δ₀ := by
    filter_upwards [E.open_source.mem_nhds hsrc, hFφ, hanN, hdN, ball_mem_nhds _ hδ₀]
      with s h1 h2 h3 h4 h5
    exact ⟨h1, by rw [h2, hF0], h3, h4, h5⟩
  obtain ⟨δ₁, hδ₁, hb1⟩ := Metric.eventually_nhds_iff_ball.mp hev1
  have hsymm : Tendsto E.symm (𝓝 0) (𝓝 0) := by
    have := (E.continuousAt_symm htgt).tendsto
    rwa [hE0] at this
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ E.target ∧ E.symm t ∈ ball (0 : ℂ) δ₁ := by
    filter_upwards [E.open_target.mem_nhds htgt, hsymm (ball_mem_nhds _ hδ₁)] with t h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨r, hr, hb2⟩ := Metric.eventually_nhds_iff_ball.mp hev2
  -- the chart
  set U : Set ℂ := upper ∩ cay τ ⁻¹' ball 0 δ₁ ∩ jC ⁻¹' ball w (r ^ e)
  have hmemU : ∀ z ∈ U, 0 < z.im ∧ cay τ z ∈ ball (0 : ℂ) δ₁ ∧ jC z = w + φ (cay τ z) ^ e ∧
      ‖φ (cay τ z)‖ < r := by
    rintro z ⟨⟨hz, hs⟩, hj⟩
    obtain ⟨-, hF, -⟩ := hb1 _ hs
    have hjz : jC z = w + φ (cay τ z) ^ e := by
      rw [← hF]; simp only [F, cayInv_cay hτ hz]
    refine ⟨hz, hs, hjz, ?_⟩
    rw [mem_preimage, mem_ball, dist_eq_norm, hjz, add_sub_cancel_left, norm_pow] at hj
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le he.ne').mp hj
  have hnorm1 : ∀ s ∈ ball (0 : ℂ) δ₁, ‖s‖ < 1 := fun s hs ↦ (hball _ (hb1 s hs).2.2.2.2).1
  refine ⟨r, hr, U, fun z ↦ φ (cay τ z), fun t ↦ cayInv τ (E.symm t), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : IsOpen (upper ∩ cay τ ⁻¹' ball 0 δ₁) :=
      (continuousOn_cay hτ).isOpen_inter_preimage isOpen_upper isOpen_ball
    exact (continuousOn_jC.mono inter_subset_left).isOpen_inter_preimage h1 isOpen_ball
  · intro z hz
    rw [mem_ball_zero_iff]
    exact (hmemU z hz).2.2.2
  · intro t ht
    obtain ⟨htt, hst⟩ := hb2 t ht
    obtain ⟨-, hF, -⟩ := hb1 _ hst
    have h1 := hnorm1 _ hst
    have hz := im_cayInv_pos hτ h1
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · rw [mem_preimage, cay_cayInv hτ h1]; exact hst
    · have : jC (cayInv τ (E.symm t)) = w + t ^ e := by
        have h2 : F (E.symm t) = jC (cayInv τ (E.symm t)) := rfl
        rw [← h2, hF, ← hEφ, E.right_inv htt]
      rw [mem_preimage, this, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_pow]
      rw [mem_ball_zero_iff] at ht
      exact pow_lt_pow_left₀ ht (norm_nonneg _) he.ne'
  · intro z hz
    obtain ⟨hz, hs, -, -⟩ := hmemU z hz
    have := E.left_inv (hb1 _ hs).1
    rw [hEφ] at this
    change cayInv τ (E.symm (φ (cay τ z))) = z
    rw [this, cayInv_cay hτ hz]
  · intro t ht
    obtain ⟨htt, hst⟩ := hb2 t ht
    rw [cay_cayInv hτ (hnorm1 _ hst), ← hEφ, E.right_inv htt]
  · intro t ht
    obtain ⟨htt, hst⟩ := hb2 t ht
    obtain ⟨-, -, han, hd, -⟩ := hb1 _ hst
    have h1 : HasDerivAt E.symm (deriv φ (E.symm t))⁻¹ t :=
      E.hasDerivAt_symm htt hd han.differentiableAt.hasDerivAt
    have h2 : DifferentiableAt ℂ (cayInv τ) (E.symm t) := by
      refine (analyticAt_cayInv τ ?_).differentiableAt
      intro h
      have := hnorm1 _ hst
      rw [h, norm_one] at this
      exact lt_irrefl _ this
    exact (h2.comp t h1.differentiableAt).differentiableWithinAt
  · intro z hz
    exact (hmemU z hz).2.2.1
  · refine ⟨⟨hτ, ?_⟩, ?_⟩
    · rw [mem_preimage, cay_self]; exact mem_ball_self hδ₁
    · rw [mem_preimage, mem_ball, dist_self]; exact pow_pos hr e
  · exact inter_subset_left.trans inter_subset_left
  · exact (by rw [cay_self]; exact hφ : AnalyticAt ℂ φ (cay τ τ)).comp (analyticAt_cay hτ hτ)
  · rw [cay_self, hφ0]
  · change deriv (φ ∘ cay τ) τ ≠ 0
    rw [deriv_comp _ (by rw [cay_self]; exact hφ.differentiableAt)
      (analyticAt_cay hτ hτ).differentiableAt, cay_self]
    exact mul_ne_zero hφ' (deriv_cay_ne_zero hτ)
  · intro γ z hz hγz
    obtain ⟨hz', hs, -, -⟩ := hmemU z hz
    obtain ⟨hγz', hγs, -, -⟩ := hmemU _ hγz
    have h1 := (hball _ (hb1 _ hs).2.2.2.2).2
    have h2 := (hball _ (hb1 _ hγs).2.2.2.2).2
    rw [cayInv_cay hτ hz'] at h1
    rw [cayInv_cay hτ hγz'] at h2
    exact smulC_eq_self_iff.mpr (hstab γ z hz' h1 h2)
  · intro γ hγ z hz
    have hfix := smulC_eq_self_iff.mp hγ
    obtain ⟨⟨hz', hs⟩, hj⟩ := hz
    refine ⟨⟨im_smulC_pos γ hz', ?_⟩, ?_⟩
    · rw [mem_preimage, cay_smulC hfix hz', mem_ball_zero_iff, norm_mul, norm_cmul, one_mul,
        ← mem_ball_zero_iff]
      exact hs
    · rw [mem_preimage, jC_smulC γ hz']
      exact hj

/-! ### Translates of the charts -/

theorem image_smulC_eq {U : Set ℂ} (hU : U ⊆ upper) (γ : SL(2, ℤ)) :
    smulC γ '' U = upper ∩ smulC γ⁻¹ ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨im_smulC_pos γ (hU hz), by rw [mem_preimage, smulC_inv_smulC γ (hU hz)]; exact hz⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨_, hy', smulC_smulC_inv γ hy⟩

variable {τ₀ : ℂ} {e : ℕ} {r : ℝ} {U : Set ℂ} {u v : ℂ → ℂ}

theorem LocalData.translate (hD : LocalData τ₀ e r U u v) (γ : SL(2, ℤ)) :
    smulC γ '' U ⊆ upper ∧ OrbChart jC (jC τ₀) e r (smulC γ '' U)
      (fun z ↦ u (smulC γ⁻¹ z)) (fun t ↦ smulC γ (v t)) := by
  have hsub := hD.sub
  have hC := hD.chart
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact im_smulC_pos γ (hsub hz)
  · rw [image_smulC_eq hsub]
    exact (continuousOn_smulC γ⁻¹).isOpen_inter_preimage isOpen_upper hC.isOpen
  · rintro _ ⟨z, hz, rfl⟩
    change u (smulC γ⁻¹ (smulC γ z)) ∈ ball 0 r
    rw [smulC_inv_smulC γ (hsub hz)]
    exact hC.mapsTo_u hz
  · intro t ht
    exact ⟨v t, hC.mapsTo_v ht, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [smulC_inv_smulC γ (hsub hz), hC.v_u z hz]
  · intro t ht
    rw [smulC_inv_smulC γ (hsub (hC.mapsTo_v ht)), hC.u_v t ht]
  · exact (differentiableOn_smulC γ).comp hC.differentiableOn_v
      (fun t ht ↦ hsub (hC.mapsTo_v ht))
  · rintro _ ⟨z, hz, rfl⟩
    rw [smulC_inv_smulC γ (hsub hz), jC_smulC γ (hsub hz), hC.eq_pow z hz]

theorem LocalData.image_stab (hD : LocalData τ₀ e r U u v) {σ : SL(2, ℤ)}
    (hσ : smulC σ τ₀ = τ₀) : smulC σ '' U = U := by
  have hσ' : smulC σ⁻¹ τ₀ = τ₀ := by
    have := smulC_inv_smulC σ (hD.sub hD.mem)
    rwa [hσ] at this
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hD.inv σ hσ z hz
  · intro z hz
    exact ⟨_, hD.inv σ⁻¹ hσ' z hz, smulC_smulC_inv σ (hD.sub hz)⟩

theorem LocalData.translate_eq (hD : LocalData τ₀ e r U u v) {γ γ' : SL(2, ℤ)}
    (h : ¬ Disjoint (smulC γ '' U) (smulC γ' '' U)) : smulC γ '' U = smulC γ' '' U := by
  obtain ⟨_, ⟨z, hz, rfl⟩, ⟨z', hz', hzz⟩⟩ := not_disjoint_iff.mp h
  have h1 : smulC (γ'⁻¹ * γ) z = z' := by
    rw [← smulC_smulC _ _ (hD.sub hz), ← hzz, smulC_inv_smulC _ (hD.sub hz')]
  have hσ : smulC (γ'⁻¹ * γ) τ₀ = τ₀ := hD.stab _ z hz (by rw [h1]; exact hz')
  have e1 : smulC (γ' * (γ'⁻¹ * γ)) '' U = smulC γ' '' (smulC (γ'⁻¹ * γ) '' U) := by
    rw [image_image]
    exact image_congr fun x hx ↦ (smulC_smulC _ _ (hD.sub hx)).symm
  rw [mul_inv_cancel_left] at e1
  rw [e1, hD.image_stab hσ]

theorem LocalData.cover (hD : LocalData τ₀ e r U u v) (he : 0 < e) (hr : 0 < r) :
    ∃ ρ > (0 : ℝ), ∃ (ι : Type) (U' : ι → Set ℂ) (u' v' : ι → ℂ → ℂ),
      Pairwise (Disjoint on U') ∧
      (∀ i, U' i ⊆ upper ∧ OrbChart jC (jC τ₀) e ρ (U' i) (u' i) (v' i)) ∧
      ∀ y ∈ upper, jC y ∈ ball (jC τ₀) (ρ ^ e) → ∃ i, y ∈ U' i := by
  let ι := {V : Set ℂ // ∃ γ : SL(2, ℤ), V = smulC γ '' U}
  let g : ι → SL(2, ℤ) := fun i ↦ i.2.choose
  have hg : ∀ i : ι, i.1 = smulC (g i) '' U := fun i ↦ i.2.choose_spec
  refine ⟨r, hr, ι, fun i ↦ i.1, fun i z ↦ u (smulC (g i)⁻¹ z),
    fun i t ↦ smulC (g i) (v t), ?_, ?_, ?_⟩
  · intro i j hij
    by_contra h
    apply hij
    apply Subtype.ext
    change ¬ Disjoint i.1 j.1 at h
    rw [hg i, hg j] at h ⊢
    exact hD.translate_eq h
  · intro i
    change i.1 ⊆ upper ∧ OrbChart jC (jC τ₀) e r i.1 (fun z ↦ u (smulC (g i)⁻¹ z))
      (fun t ↦ smulC (g i) (v t))
    rw [hg i]
    exact hD.translate (g i)
  · intro y hy hjy
    rw [mem_ball, dist_eq_norm] at hjy
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (jC y - jC τ₀) he
    have htr : t ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff]
      rw [← ht, norm_pow] at hjy
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le he.ne').mp hjy
    have hz := hD.chart.mapsTo_v htr
    have hz1 := hD.sub hz
    have hjz : jC (v t) = jC y := by
      rw [hD.chart.eq_pow _ hz, hD.chart.u_v t htr, ht]
      ring
    obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq ⟨y, hy⟩ ⟨v t, hz1⟩ (by
      rw [← jC_of_im_pos hy, ← jC_of_im_pos hz1, hjz])
    refine ⟨⟨smulC γ '' U, γ, rfl⟩, v t, hz, ?_⟩
    rw [smulC_of_im_pos γ hz1, hγ]

theorem LocalData.hasLocalForm (hD : LocalData τ₀ e r U u v) {z : ℂ} (hz : 0 < z.im)
    (hjz : jC z = jC τ₀) : HasLocalForm jC z e := by
  have hτ := hD.sub hD.mem
  obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq ⟨z, hz⟩ ⟨τ₀, hτ⟩ (by
    rw [← jC_of_im_pos hz, ← jC_of_im_pos hτ, hjz])
  have hγz : smulC γ τ₀ = z := by rw [smulC_of_im_pos γ hτ, hγ]
  have hinv : smulC γ⁻¹ z = τ₀ := by rw [← hγz, smulC_inv_smulC γ hτ]
  obtain ⟨-, hC⟩ := hD.translate γ
  have hu : AnalyticAt ℂ u (smulC γ⁻¹ z) := by rw [hinv]; exact hD.analyticAt
  refine ⟨fun y ↦ u (smulC γ⁻¹ y), hu.comp (analyticAt_smulC γ⁻¹ hz), ?_, ?_, ?_⟩
  · change u (smulC γ⁻¹ z) = 0
    rw [hinv, hD.u_self]
  · change deriv (u ∘ smulC γ⁻¹) z ≠ 0
    rw [deriv_comp _ hu.differentiableAt (analyticAt_smulC γ⁻¹ hz).differentiableAt, hinv]
    exact mul_ne_zero hD.deriv_ne (deriv_smulC_ne_zero γ⁻¹ hz)
  · have hmem : z ∈ smulC γ '' U := ⟨τ₀, hD.mem, hγz⟩
    filter_upwards [hC.isOpen.mem_nhds hmem] with y hy
    rw [hC.eq_pow y hy, hjz]

/-! ### The main theorem -/

theorem exists_localData_sig (w : ℂ) :
    ∃ τ₀ : ℍ, jC τ₀ = w ∧ ∃ r > 0, ∃ U u v, LocalData (τ₀ : ℂ) (sig w) r U u v := by
  by_cases h0 : w = 0
  · subst h0
    refine ⟨ρ, jC_ρ, ?_⟩
    have : sig 0 = 3 := if_pos rfl
    rw [this]
    exact exists_localData ρ (by norm_num) (fun γ hγ ↦ cmul_cube_of_fix_ρ hγ) gρ_smul
      (fun m hm ↦ dvd_of_ρ_pow (by rwa [cmul_gρ] at hm))
  by_cases h1 : w = 1728
  · subst h1
    refine ⟨UpperHalfPlane.I, jC_I, ?_⟩
    have : sig 1728 = 2 := by simp [sig]
    rw [this]
    exact exists_localData _ (by norm_num) (fun γ hγ ↦ cmul_sq_of_fix_I hγ) S_smul_I
      (fun m hm ↦ dvd_of_neg_one_pow (by rwa [cmul_S_I] at hm))
  obtain ⟨τ₀, hτ₀⟩ := Heights.modularJ_surjective w
  refine ⟨τ₀, by rw [jC_coe, hτ₀], ?_⟩
  have : sig w = 1 := by simp [sig, h0, h1]
  rw [this]
  refine exists_localData τ₀ one_pos (fun γ hγ ↦ ?_) (one_smul _ τ₀) (fun m _ ↦ one_dvd m)
  have hB : Heights.modularJ τ₀ ∉ jBranch := by
    rw [hτ₀, jBranch_eq]
    simp [h0, h1]
  by_cases g1 : γ = 1
  · subst g1
    simp [cmul]
  by_cases g2 : γ = -1
  · subst g2
    simp [cmul]
  exact absurd (modularJ_mem_jBranch_of_smul_eq hγ g1 g2) hB

/-- **The `j`-function is an orbifold covering** of `ℂ` with signature `sig` (ramification `3`
over `0 = j(ρ)`, `2` over `1728 = j(i)`, and `1` elsewhere), with local normal forms of order
`sig (j z)` at every point of `ℍ`. -/
theorem jOrbStatement : JOrbStatement := by
  refine ⟨fun w ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨τ₀, hτ₀, r, hr, U, u, v, hD⟩ := exists_localData_sig w
    refine ⟨⟨τ₀, τ₀.im_pos, hτ₀⟩, ?_⟩
    have := hD.cover (sig_pos w) hr
    rwa [hτ₀] at this
  · obtain ⟨τ₀, hτ₀, r, hr, U, u, v, hD⟩ := exists_localData_sig (jC z)
    exact hD.hasLocalForm hz hτ₀.symm

end OrbicurveCores.S1
