/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.LocalForm

/-!
# Rational orbifold coverings of the `j`-line

A **Belyi certificate** `RatCert f N D H K R c` for the rational function `G = N / D` of the
`x`-coordinate of the curve `y² = f(x)`: the poles of `G` (in `ℂ`) are exactly the roots of `f`,
`N = c H³`, `N − 1728 D = c K²`, the critical points of `G` off the roots of `f` are roots of `H`
or `K` (`N' D − N D' = R H² K`, roots of `R` among those of `f`), and `H, K` are squarefree and
coprime to `f`. All of these are polynomial identities with explicit Bézout witnesses.

From a certificate we derive the hypotheses of `EllOrbStatement` on `Z = {f = 0}`: holomorphy
off `Z`, local normal forms of order `sig (G x)`, finite fibres, surjectivity, and poles at `Z` and
at `∞` (`RatCert.differentiableOn`, `RatCert.hasLocalForm`, `RatCert.finite_fiber`,
`RatCert.surj`, `RatCert.tendsto_nhdsNE`, `RatCert.tendsto_cobounded`).
-/

open Complex Metric Set Filter Topology Polynomial Bornology Asymptotics

namespace OrbicurveCores.S1

/-- A certificate that `G = N / D` is an orbifold covering of the `j`-line, with poles exactly at
the roots of `f` and at `∞`. -/
structure RatCert (f N D H K R : ℂ[X]) (c : ℂ) : Prop where
  c_ne : c ≠ 0
  hN : N = C c * H ^ 3
  hK : N - 1728 * D = C c * K ^ 2
  hcrit : derivative N * D - N * derivative D = R * H ^ 2 * K
  f_dvd_D : ∃ q, D = f * q
  D_dvd_f : ∃ q, ∃ d : ℂ, d ≠ 0 ∧ C d * f ^ 6 = D * q
  R_dvd_f : ∃ q, ∃ d : ℂ, d ≠ 0 ∧ C d * f ^ 6 = R * q
  H_cop : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * H + b * f = C d
  K_cop : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * K + b * f = C d
  H_sqf : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * derivative H + b * H = C d
  K_sqf : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * derivative K + b * K = C d
  deg : D.natDegree < N.natDegree
  D_ne : D ≠ 0

lemma eval_ne_of_cop {P Q : ℂ[X]} (h : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * P + b * Q = C d) {x : ℂ}
    (hQ : Q.eval x = 0) : P.eval x ≠ 0 := by
  obtain ⟨a, b, d, hd, h⟩ := h
  intro hP
  have := congrArg (eval x) h
  simp only [eval_add, eval_mul, hP, hQ, mul_zero, add_zero, eval_C] at this
  exact hd this.symm

lemma eval_zero_of_dvd {f P : ℂ[X]} (h : ∃ q, ∃ d : ℂ, d ≠ 0 ∧ C d * f ^ 6 = P * q) {x : ℂ}
    (hP : P.eval x = 0) : f.eval x = 0 := by
  obtain ⟨q, d, hd, h⟩ := h
  have := congrArg (eval x) h
  simp only [eval_mul, eval_pow, eval_C, hP, zero_mul] at this
  exact pow_eq_zero_iff (n := 6) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left hd)

lemma polyAn (P : ℂ[X]) (x : ℂ) : AnalyticAt ℂ (fun y ↦ P.eval y) x :=
  P.differentiable.analyticAt x

namespace RatCert

variable {f N D H K R : ℂ[X]} {c : ℂ} (hc : RatCert f N D H K R c)
include hc

lemma D_eval_eq_zero_iff (x : ℂ) : D.eval x = 0 ↔ f.eval x = 0 := by
  refine ⟨eval_zero_of_dvd hc.D_dvd_f, fun h ↦ ?_⟩
  obtain ⟨q, hq⟩ := hc.f_dvd_D
  rw [hq, eval_mul, h, zero_mul]

lemma H_eval_ne {x : ℂ} (hx : f.eval x = 0) : H.eval x ≠ 0 := eval_ne_of_cop hc.H_cop hx

lemma N_eval_ne {x : ℂ} (hx : f.eval x = 0) : N.eval x ≠ 0 := by
  rw [hc.hN, eval_mul, eval_C, eval_pow]
  exact mul_ne_zero hc.c_ne (pow_ne_zero _ (hc.H_eval_ne hx))

lemma D_ne_zero : D ≠ 0 := hc.D_ne

/-- The rational function `G = N / D`. -/
noncomputable def G (_ : RatCert f N D H K R c) (x : ℂ) : ℂ := N.eval x / D.eval x

lemma G_def (x : ℂ) : hc.G x = N.eval x / D.eval x := rfl

lemma differentiableAt {x : ℂ} (hx : f.eval x ≠ 0) : DifferentiableAt ℂ hc.G x :=
  N.differentiableAt.div D.differentiableAt (by rwa [ne_eq, hc.D_eval_eq_zero_iff])

lemma differentiableOn : DifferentiableOn ℂ hc.G {x | f.eval x = 0}ᶜ :=
  fun _ hx ↦ (hc.differentiableAt hx).differentiableWithinAt

lemma analyticAt {x : ℂ} (hx : f.eval x ≠ 0) : AnalyticAt ℂ hc.G x := by
  have hD : D.eval x ≠ 0 := by rwa [ne_eq, hc.D_eval_eq_zero_iff]
  exact (polyAn N x).div (polyAn D x) hD

lemma eventually_D_ne {x : ℂ} (hx : f.eval x ≠ 0) : ∀ᶠ y in 𝓝 x, D.eval y ≠ 0 :=
  D.continuous.continuousAt.eventually_ne (by rwa [ne_eq, hc.D_eval_eq_zero_iff])

lemma G_eq_zero_iff {x : ℂ} (hx : f.eval x ≠ 0) : hc.G x = 0 ↔ H.eval x = 0 := by
  have hD : D.eval x ≠ 0 := by rwa [ne_eq, hc.D_eval_eq_zero_iff]
  rw [G_def, div_eq_zero_iff, or_iff_left hD, hc.hN, eval_mul, eval_C, eval_pow,
    mul_eq_zero, or_iff_right hc.c_ne, pow_eq_zero_iff (by norm_num)]

lemma G_sub_eq {x : ℂ} (hx : D.eval x ≠ 0) :
    hc.G x - 1728 = c * K.eval x ^ 2 / D.eval x := by
  have := congrArg (eval x) hc.hK
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_ofNat] at this
  rw [G_def, div_sub' hx, ← this]
  congr 1; ring

lemma G_eq_1728_iff {x : ℂ} (hx : f.eval x ≠ 0) : hc.G x = 1728 ↔ K.eval x = 0 := by
  have hD : D.eval x ≠ 0 := by rwa [ne_eq, hc.D_eval_eq_zero_iff]
  rw [← sub_eq_zero, hc.G_sub_eq hD, div_eq_zero_iff, or_iff_left hD, mul_eq_zero,
    or_iff_right hc.c_ne, pow_eq_zero_iff (by norm_num)]

lemma sig_G {x : ℂ} (hx : f.eval x ≠ 0) :
    sig (hc.G x) = if H.eval x = 0 then 3 else if K.eval x = 0 then 2 else 1 := by
  simp only [sig, hc.G_eq_zero_iff hx, hc.G_eq_1728_iff hx]

/-- **Local normal forms** of `G` off the roots of `f`. -/
lemma hasLocalForm {x : ℂ} (hx : f.eval x ≠ 0) : HasLocalForm hc.G x (sig (hc.G x)) := by
  have hD : D.eval x ≠ 0 := by rwa [ne_eq, hc.D_eval_eq_zero_iff]
  have hφ : AnalyticAt ℂ (fun y ↦ c / D.eval y) x := analyticAt_const.div (polyAn D x) hD
  rw [hc.sig_G hx]
  split_ifs with hH hK
  · -- a zero of `G`: `G = H³ · (c / D)`
    refine hasLocalForm_of_eq_pow_mul (by norm_num) (polyAn H x) hH ?_ hφ
      (div_ne_zero hc.c_ne hD) ?_
    · rw [Polynomial.deriv]; exact eval_ne_of_cop hc.H_sqf hH
    · filter_upwards [hc.eventually_D_ne hx] with y hy
      rw [(hc.G_eq_zero_iff hx).mpr hH, zero_add, G_def, hc.hN, eval_mul, eval_C, eval_pow]
      field_simp
  · -- a `1728`-point: `G = 1728 + K² · (c / D)`
    refine hasLocalForm_of_eq_pow_mul (by norm_num) (polyAn K x) hK ?_ hφ
      (div_ne_zero hc.c_ne hD) ?_
    · rw [Polynomial.deriv]; exact eval_ne_of_cop hc.K_sqf hK
    · filter_upwards [hc.eventually_D_ne hx] with y hy
      rw [(hc.G_eq_1728_iff hx).mpr hK, ← sub_eq_iff_eq_add', hc.G_sub_eq hy]
      field_simp
  · -- an unramified point
    refine hasLocalForm_one (hc.analyticAt hx) ?_
    have hd : HasDerivAt hc.G ((N.derivative.eval x * D.eval x - N.eval x *
        D.derivative.eval x) / D.eval x ^ 2) x :=
      (N.hasDerivAt x).div (D.hasDerivAt x) hD
    rw [hd.deriv]
    have := congrArg (eval x) hc.hcrit
    simp only [eval_sub, eval_mul, eval_pow] at this
    rw [this]
    refine div_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hH)) hK) (pow_ne_zero _ hD)
    exact fun h ↦ hx (eval_zero_of_dvd hc.R_dvd_f h)

lemma natDegree_sub_C_mul (w : ℂ) : (N - C w * D).natDegree = N.natDegree := by
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  exact lt_of_le_of_lt (natDegree_C_mul_le _ _) hc.deg

lemma sub_C_mul_ne_zero (w : ℂ) : N - C w * D ≠ 0 := by
  intro h
  have := hc.natDegree_sub_C_mul w
  rw [h, natDegree_zero] at this
  have := hc.deg; omega

/-- Finite fibres. -/
lemma finite_fiber (w : ℂ) : {x | f.eval x ≠ 0 ∧ hc.G x = w}.Finite := by
  refine (Polynomial.finite_setOf_isRoot (hc.sub_C_mul_ne_zero w)).subset ?_
  rintro x ⟨hx, hGx⟩
  have hD : D.eval x ≠ 0 := by rwa [ne_eq, hc.D_eval_eq_zero_iff]
  rw [G_def, div_eq_iff hD] at hGx
  simp only [mem_setOf_eq, IsRoot, eval_sub, eval_mul, eval_C, hGx, sub_self]

/-- Every value is attained off the roots of `f`. -/
lemma surj (w : ℂ) : ∃ x, f.eval x ≠ 0 ∧ hc.G x = w := by
  have hdeg : 0 < degree (N - C w * D) := by
    rw [degree_eq_natDegree (hc.sub_C_mul_ne_zero w), hc.natDegree_sub_C_mul]
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hc.deg
  obtain ⟨x, hx⟩ := Complex.exists_root hdeg
  simp only [IsRoot, eval_sub, eval_mul, eval_C] at hx
  have hfx : f.eval x ≠ 0 := by
    intro hf
    have hD : D.eval x = 0 := (hc.D_eval_eq_zero_iff x).mpr hf
    rw [hD, mul_zero, sub_zero] at hx
    exact hc.N_eval_ne hf hx
  refine ⟨x, hfx, ?_⟩
  have hD : D.eval x ≠ 0 := by rwa [ne_eq, hc.D_eval_eq_zero_iff]
  rw [G_def, div_eq_iff hD]
  linear_combination hx

/-- Poles at the roots of `f`. -/
lemma tendsto_nhdsNE {z : ℂ} (hz : f.eval z = 0) :
    Tendsto hc.G (𝓝[≠] z) (cobounded ℂ) := by
  have hN : N.eval z ≠ 0 := hc.N_eval_ne hz
  have hD : D.eval z = 0 := (hc.D_eval_eq_zero_iff z).mpr hz
  -- `D` has an isolated zero at `z`
  have hDne : ∀ᶠ y in 𝓝[≠] z, D.eval y ≠ 0 := by
    have hfin := Polynomial.finite_setOf_isRoot hc.D_ne_zero
    have : ∀ᶠ y in 𝓝[≠] z, y ∉ {y | D.IsRoot y} \ {z} :=
      (hfin.sdiff).isClosed.isOpen_compl.mem_nhds (by simp) |> nhdsWithin_le_nhds
    filter_upwards [this, self_mem_nhdsWithin] with y hy hyz
    intro h; exact hy ⟨h, hyz⟩
  have hDt : Tendsto (fun y ↦ D.eval y) (𝓝[≠] z) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hDne⟩
    have := (D.continuous.tendsto z).mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    rwa [hD] at this
  have hinv := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp hDt
  rw [← tendsto_norm_atTop_iff_cobounded] at hinv ⊢
  have hNt : Tendsto (fun y ↦ ‖N.eval y‖) (𝓝[≠] z) (𝓝 ‖N.eval z‖) :=
    ((N.continuous.tendsto z).mono_left nhdsWithin_le_nhds).norm
  have := hNt.pos_mul_atTop (norm_pos_iff.mpr hN) hinv
  refine this.congr fun y ↦ ?_
  simp only [Function.comp, G_def, div_eq_mul_inv, norm_mul]

/-- A pole at `∞`. -/
lemma tendsto_cobounded : Tendsto hc.G (cobounded ℂ) (cobounded ℂ) := by
  have hN0 : N ≠ 0 := by
    intro h; have := hc.deg; rw [h, natDegree_zero] at this; omega
  have heN := isEquivalent_cobounded_leading_monomial (P := N)
  have heD := isEquivalent_cobounded_leading_monomial (P := D)
  have he := heN.div heD
  obtain ⟨φ, hφ, hGφ⟩ := he.exists_eq_mul
  set k := N.natDegree - D.natDegree
  have hk : 0 < k := Nat.sub_pos_of_lt hc.deg
  have hlN : N.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hN0
  have hlD : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hc.D_ne_zero
  -- the monomial quotient
  have hmon : ∀ᶠ x in cobounded ℂ, (N.leadingCoeff * x ^ N.natDegree) /
      (D.leadingCoeff * x ^ D.natDegree) = N.leadingCoeff / D.leadingCoeff * x ^ k := by
    filter_upwards [eventually_ne_cobounded 0] with x hx
    have hpow : x ^ N.natDegree = x ^ k * x ^ D.natDegree := by
      rw [← pow_add, Nat.sub_add_cancel hc.deg.le]
    rw [hpow]; field_simp
  have hmt : Tendsto (fun x : ℂ ↦ ‖N.leadingCoeff / D.leadingCoeff * x ^ k‖)
      (cobounded ℂ) atTop := by
    simp only [norm_mul, norm_pow]
    exact (tendsto_pow_atTop hk.ne').comp tendsto_norm_cobounded_atTop |>.const_mul_atTop
      (norm_pos_iff.mpr (div_ne_zero hlN hlD))
  have hφt : Tendsto (fun x ↦ ‖φ x‖) (cobounded ℂ) (𝓝 1) := by
    simpa using hφ.norm
  rw [← tendsto_norm_atTop_iff_cobounded]
  have := hφt.pos_mul_atTop one_pos hmt
  refine this.congr' ?_
  filter_upwards [hGφ, hmon] with x hx hx'
  simp only [Pi.mul_apply, Pi.div_apply] at hx
  rw [G_def, hx, hx', norm_mul, norm_mul, norm_mul]

end RatCert

end OrbicurveCores.S1
