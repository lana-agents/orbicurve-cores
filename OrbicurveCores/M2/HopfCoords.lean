/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.Setup

/-!
# Hopf coordinates on `SL(2, ℝ)`

We parametrise (almost all of) `SL(2, ℝ)` by `(x, u, s) ∈ ℝ³` and a sign:

  `hopf (x, u, s) = [[x eˢ, (x u - 1) e⁻ˢ], [eˢ, u e⁻ˢ]]`.

The first column spans the line of `x ∈ ℙ¹(ℝ)` and the second column the line of
`y = x - 1/u`. In these coordinates

* right multiplication by `unip t = [[1, t], [0, 1]]` is the shear `u ↦ u + e²ˢ t`;
* right multiplication by `diagA σ = diag(e^σ, e^{-σ})` is the translation `s ↦ s + σ`;
* left multiplication by `γ = [[a, b], [c, d]]` is, up to sign and off the null set
  `c x + d = 0`, the map `(x, u, s) ↦ (γ x, α² u - c α, s + log |α|)` with `α = c x + d`.

All three preserve Lebesgue measure on `ℝ³`, so `hopfMeasure`, the push-forward of Lebesgue
measure under `hopf` and `-hopf`, is left-invariant and right-invariant under `A` and `N`.
(It is a Haar measure of `SL(2, ℝ)`, but we never need this.)
-/

open MeasureTheory Matrix Matrix.SpecialLinearGroup Set Filter Real
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

/-- The Borel structure on `SL(2, ℝ)`. -/
instance instMeasurableSpaceSL : MeasurableSpace SL(2, ℝ) := borel _

instance : BorelSpace SL(2, ℝ) := ⟨rfl⟩

/-- The upper unipotent `n_t`. -/
noncomputable def unip (t : ℝ) : SL(2, ℝ) :=
  ⟨!![1, t; 0, 1], by rw [det_fin_two_of]; ring⟩

/-- The diagonal element `a_σ = diag(e^σ, e^{-σ})`. -/
noncomputable def diagA (σ : ℝ) : SL(2, ℝ) :=
  ⟨!![exp σ, 0; 0, exp (-σ)], by rw [det_fin_two_of, ← exp_add]; simp⟩

lemma exp_mul_exp_neg (s : ℝ) : exp s * exp (-s) = 1 := by rw [← exp_add]; simp

/-- The Hopf chart. -/
noncomputable def hopf (p : ℝ × ℝ × ℝ) : SL(2, ℝ) :=
  ⟨!![p.1 * exp p.2.2, (p.1 * p.2.1 - 1) * exp (-p.2.2); exp p.2.2, p.2.1 * exp (-p.2.2)], by
    rw [det_fin_two_of]; linear_combination exp_mul_exp_neg p.2.2⟩

lemma coe_hopf (p : ℝ × ℝ × ℝ) : ((hopf p : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![p.1 * exp p.2.2, (p.1 * p.2.1 - 1) * exp (-p.2.2); exp p.2.2, p.2.1 * exp (-p.2.2)] :=
  rfl

/-- The shear `(x, u, s) ↦ (x, u + e²ˢ t, s)`. -/
noncomputable def hopfN (t : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1, p.2.1 + exp (2 * p.2.2) * t, p.2.2)

/-- The translation `(x, u, s) ↦ (x, u, s + σ)`. -/
def hopfA (σ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, p.2.1, p.2.2 + σ)

lemma exp_two_mul' (s : ℝ) : exp (2 * s) = exp s * exp s := by rw [← exp_add]; ring_nf

lemma hopf_mul_unip (p : ℝ × ℝ × ℝ) (t : ℝ) : hopf p * unip t = hopf (hopfN t p) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_hopf, coe_hopf]
  have h := exp_mul_exp_neg p.2.2
  fin_cases i <;> fin_cases j <;>
    simp [unip, hopfN, Matrix.mul_apply, Fin.sum_univ_two, exp_two_mul']
  · linear_combination (-(p.1 * t * exp p.2.2)) * h
  · linear_combination (-(t * exp p.2.2)) * h

lemma hopf_mul_diagA (p : ℝ × ℝ × ℝ) (σ : ℝ) : hopf p * diagA σ = hopf (hopfA σ p) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_hopf, coe_hopf]
  fin_cases i <;> fin_cases j <;>
    simp [diagA, hopfA, Matrix.mul_apply, Fin.sum_univ_two, exp_add] <;> ring

lemma diagA_mul_unip (σ t : ℝ) : diagA σ * unip t = unip (exp (2 * σ) * t) * diagA σ := by
  ext i j
  have h := exp_mul_exp_neg σ
  fin_cases i <;> fin_cases j <;>
    simp [diagA, unip, Matrix.mul_apply, Fin.sum_univ_two, exp_two_mul']
  linear_combination (-(exp σ * t)) * h

/-! ### The left action -/

/-- The Möbius cocycle `α = c x + d`. -/
def cocy (γ : SL(2, ℝ)) (x : ℝ) : ℝ := γ 1 0 * x + γ 1 1

/-- The Möbius map `x ↦ (a x + b) / (c x + d)` on `ℝ` (junk value at the pole). -/
noncomputable def mob (γ : SL(2, ℝ)) (x : ℝ) : ℝ := (γ 0 0 * x + γ 0 1) / cocy γ x

/-- Left multiplication in Hopf coordinates. -/
noncomputable def hopfT (γ : SL(2, ℝ)) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (mob γ p.1, cocy γ p.1 ^ 2 * p.2.1 - γ 1 0 * cocy γ p.1, p.2.2 + log |cocy γ p.1|)

lemma det_SL (γ : SL(2, ℝ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe; rwa [det_fin_two] at this

/-- The matrix identity behind the left action: `γ · hopf p = ε · hopf (T p)` where
`|α| = ε α`. -/
lemma mul_hopf_aux (γ : SL(2, ℝ)) (p : ℝ × ℝ × ℝ) (hα : cocy γ p.1 ≠ 0) {ε : ℝ}
    (hε : ε * ε = 1) (he : |cocy γ p.1| = ε * cocy γ p.1) :
    ((γ * hopf p : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      ε • ((hopf (hopfT γ p) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_hopf, coe_hopf]
  have hdet := det_SL γ
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have e1 : exp (p.2.2 + log |cocy γ p.1|) = exp p.2.2 * (ε * cocy γ p.1) := by
    rw [exp_add, exp_log (abs_pos.mpr hα), he]
  have e2 : exp (-(p.2.2 + log |cocy γ p.1|)) = exp (-p.2.2) / (ε * cocy γ p.1) := by
    rw [neg_add, exp_add, exp_neg (log _), exp_log (abs_pos.mpr hα), he]; ring
  simp only [hopfT, mob]
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, of_apply, cons_val', cons_val_zero, cons_val_one,
      cons_val_fin_one, empty_val', Matrix.smul_apply, smul_eq_mul] <;>
    field_simp <;> simp only [cocy] at *
  · linear_combination (-(γ 0 0 * p.1 + γ 0 1)) * hε
  · linear_combination (-1 : ℝ) * hdet
  · linear_combination (-(γ 1 0 * p.1 + γ 1 1)) * hε
  · ring

lemma mul_hopf_of_pos (γ : SL(2, ℝ)) (p : ℝ × ℝ × ℝ) (hα : 0 < cocy γ p.1) :
    γ * hopf p = hopf (hopfT γ p) := by
  ext1
  rw [mul_hopf_aux γ p hα.ne' (ε := 1) (by norm_num) (by rw [abs_of_pos hα, one_mul]), one_smul]

lemma mul_hopf_of_neg (γ : SL(2, ℝ)) (p : ℝ × ℝ × ℝ) (hα : cocy γ p.1 < 0) :
    γ * hopf p = -hopf (hopfT γ p) := by
  ext1
  rw [mul_hopf_aux γ p hα.ne (ε := -1) (by norm_num) (by rw [abs_of_neg hα]; ring),
    Matrix.SpecialLinearGroup.coe_neg, neg_one_smul]

/-! ### Measurability -/

set_option linter.flexible false in
lemma continuous_hopf : Continuous hopf := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

@[fun_prop]
lemma measurable_hopf : Measurable hopf := continuous_hopf.measurable

lemma continuous_neg_SL : Continuous fun g : SL(2, ℝ) ↦ -g :=
  (continuous_const_mul (-1)).congr fun g ↦ neg_one_mul g

@[fun_prop]
lemma measurable_neg_hopf : Measurable fun p ↦ -hopf p :=
  (continuous_neg_SL.comp continuous_hopf).measurable

@[fun_prop]
lemma measurable_hopfN (t : ℝ) : Measurable (hopfN t) := by unfold hopfN; fun_prop

@[fun_prop]
lemma measurable_hopfA (σ : ℝ) : Measurable (hopfA σ) := by unfold hopfA; fun_prop

@[fun_prop]
lemma measurable_cocy (γ : SL(2, ℝ)) : Measurable (cocy γ) := by unfold cocy; fun_prop

@[fun_prop]
lemma measurable_mob (γ : SL(2, ℝ)) : Measurable (mob γ) := by unfold mob; fun_prop

@[fun_prop]
lemma measurable_hopfT (γ : SL(2, ℝ)) : Measurable (hopfT γ) := by unfold hopfT; fun_prop

/-! ### Measure preservation in coordinates -/

lemma measurePreserving_shear (t : ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1 + exp (2 * q.2) * t, q.2)) volume volume := by
  have h1 : MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1, q.2 + exp (2 * q.1) * t))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (f := id) (MeasurePreserving.id volume)
      (g := fun s u ↦ u + exp (2 * s) * t) (by fun_prop)
      (Eventually.of_forall fun s ↦ map_add_right_eq_self volume _)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).comp (h1.comp Measure.measurePreserving_swap)
  exact h2

lemma measurePreserving_hopfN (t : ℝ) : MeasurePreserving (hopfN t) volume volume :=
  MeasurePreserving.skew_product (f := id) (MeasurePreserving.id volume)
    (g := fun (_ : ℝ) (q : ℝ × ℝ) ↦ (q.1 + exp (2 * q.2) * t, q.2)) (by fun_prop)
    (Eventually.of_forall fun _ ↦ (measurePreserving_shear t).map_eq)

lemma measurePreserving_hopfA (σ : ℝ) : MeasurePreserving (hopfA σ) volume volume :=
  (MeasurePreserving.id volume).prod
    ((MeasurePreserving.id volume).prod (measurePreserving_add_right volume σ))

/-- A nonzero affine function has at most one zero. -/
lemma subsingleton_affine {c d : ℝ} (h : c ≠ 0 ∨ d ≠ 0) :
    {x : ℝ | c * x + d = 0}.Subsingleton := by
  intro x hx y hy
  simp only [Set.mem_setOf_eq] at hx hy
  by_cases hc : c = 0
  · simp only [hc, zero_mul, zero_add] at hx
    exact absurd hx (h.resolve_left (not_not.mpr hc))
  · exact mul_left_cancel₀ hc (by linarith)

lemma cocy_coeffs_ne (γ : SL(2, ℝ)) : γ 1 0 ≠ 0 ∨ γ 1 1 ≠ 0 := by
  by_contra h
  push Not at h
  have := det_SL γ
  rw [h.1, h.2] at this
  simp at this

lemma volume_cocy_eq_zero (γ : SL(2, ℝ)) : volume {x : ℝ | cocy γ x = 0} = 0 :=
  (subsingleton_affine (cocy_coeffs_ne γ)).measure_zero _

lemma ae_cocy_ne (γ : SL(2, ℝ)) : ∀ᵐ p : ℝ × ℝ × ℝ, cocy γ p.1 ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {p : ℝ × ℝ × ℝ | cocy γ p.1 = 0} = {x : ℝ | cocy γ x = 0} ×ˢ Set.univ := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, volume_cocy_eq_zero, zero_mul]

/-- The one-dimensional change of variables for a Möbius map. -/
lemma lintegral_mob (γ : SL(2, ℝ)) (K : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal ((cocy γ x ^ 2)⁻¹) * K (mob γ x) = ∫⁻ x, K x := by
  have hdet := det_SL γ
  set S := {x : ℝ | cocy γ x ≠ 0}
  have hS : MeasurableSet S := (measurableSet_eq_fun (measurable_cocy γ) measurable_const).compl
  have hderiv : ∀ x ∈ S, HasDerivWithinAt (mob γ) ((cocy γ x ^ 2)⁻¹) S x := by
    intro x hx
    refine HasDerivAt.hasDerivWithinAt ?_
    have h := (((hasDerivAt_id x).const_mul (γ 0 0)).add_const (γ 0 1)).div
      (((hasDerivAt_id x).const_mul (γ 1 0)).add_const (γ 1 1)) hx
    refine h.congr_deriv ?_
    have hx' : cocy γ x ≠ 0 := hx
    simp only [cocy, id, mul_one] at hx' ⊢
    field_simp
    linear_combination hdet
  have hinj : InjOn (mob γ) S := by
    intro x hx y hy hxy
    simp only [mob] at hxy
    rw [div_eq_div_iff hx hy] at hxy
    simp only [cocy] at hxy
    linear_combination hxy - (x - y) * hdet
  have main := lintegral_image_eq_lintegral_abs_deriv_mul hS hderiv hinj K
  have hSae : ∀ᵐ x : ℝ, x ∈ S := by
    rw [ae_iff]
    simpa [S] using volume_cocy_eq_zero γ
  have himae : ∀ᵐ x : ℝ, x ∈ mob γ '' S := by
    rw [ae_iff]
    refine measure_mono_null (t := {x : ℝ | (-γ 1 0) * x + γ 0 0 = 0}) ?_
      ((subsingleton_affine ?_).measure_zero _)
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      by_contra hne
      apply hx
      set D := -γ 1 0 * x + γ 0 0
      have hc : cocy γ ((γ 1 1 * x - γ 0 1) / D) = 1 / D := by
        simp only [cocy]
        field_simp
        linear_combination hdet
      refine ⟨(γ 1 1 * x - γ 0 1) / D, ?_, ?_⟩
      · simp only [S, Set.mem_setOf_eq, hc]
        exact one_div_ne_zero hne
      · rw [mob, hc]
        field_simp
        linear_combination x * hdet
    · by_cases h : γ 1 0 = 0
      · right
        intro h0
        rw [h0, h] at hdet
        simp at hdet
      · exact Or.inl (neg_ne_zero.mpr h)
  have e1 : ∫⁻ x, ENNReal.ofReal ((cocy γ x ^ 2)⁻¹) * K (mob γ x) =
      ∫⁻ x in S, ENNReal.ofReal ((cocy γ x ^ 2)⁻¹) * K (mob γ x) := by
    rw [Measure.restrict_eq_self_of_ae_mem hSae]
  have e2 : ∫⁻ x, K x = ∫⁻ x in mob γ '' S, K x := by
    rw [Measure.restrict_eq_self_of_ae_mem himae]
  rw [e1, e2, main]
  refine setLIntegral_congr_fun hS fun x _ ↦ ?_
  rw [abs_of_nonneg (by positivity)]

/-- Affine change of variables on `ℝ`. -/
lemma lintegral_comp_mul_add {a : ℝ} (ha : a ≠ 0) (b : ℝ) (J : ℝ → ℝ≥0∞) :
    ∫⁻ u, J (a * u + b) = ENNReal.ofReal |a⁻¹| * ∫⁻ u, J u := by
  set e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv
  have he : Measure.map e volume = ENNReal.ofReal |a⁻¹| • volume :=
    Real.map_volume_mul_left ha
  have h1 := lintegral_map_equiv (μ := volume) (fun v ↦ J (v + b)) e
  rw [he, lintegral_smul_measure, lintegral_add_right_eq_self, smul_eq_mul] at h1
  exact h1.symm

/-- **Left multiplication preserves Lebesgue measure in Hopf coordinates.** -/
lemma lintegral_comp_hopfT (γ : SL(2, ℝ)) {H : ℝ × ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p, H (hopfT γ p) = ∫⁻ p, H p := by
  rw [Measure.volume_eq_prod,
    lintegral_prod _ (by fun_prop : Measurable fun p ↦ H (hopfT γ p)).aemeasurable,
    lintegral_prod _ hH.aemeasurable]
  have inner : ∀ x, cocy γ x ≠ 0 → ∫⁻ q : ℝ × ℝ, H (hopfT γ (x, q)) =
      ENNReal.ofReal ((cocy γ x ^ 2)⁻¹) * ∫⁻ q : ℝ × ℝ, H (mob γ x, q) := by
    intro x hx
    have hm : Measurable fun q : ℝ × ℝ ↦ H (mob γ x, q) := by fun_prop
    have hm' : Measurable fun q : ℝ × ℝ ↦ H (hopfT γ (x, q)) := by fun_prop
    rw [Measure.volume_eq_prod, lintegral_prod _ hm'.aemeasurable,
      lintegral_prod _ hm.aemeasurable]
    simp only [hopfT]
    have hs : ∀ v : ℝ, ∫⁻ s, H (mob γ x, v, s + log |cocy γ x|) = ∫⁻ s, H (mob γ x, v, s) :=
      fun v ↦ lintegral_add_right_eq_self (fun s ↦ H (mob γ x, v, s)) _
    simp_rw [hs, sub_eq_add_neg]
    rw [lintegral_comp_mul_add (pow_ne_zero 2 hx) _ (fun v ↦ ∫⁻ s, H (mob γ x, v, s)),
      abs_of_nonneg (by positivity)]
  rw [← lintegral_mob γ (fun x' ↦ ∫⁻ q : ℝ × ℝ, H (x', q))]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ x : ℝ, cocy γ x ≠ 0 := by
    rw [ae_iff]; simpa using volume_cocy_eq_zero γ
  filter_upwards [hae] with x hx
  exact inner x hx

/-! ### The measure on `SL(2, ℝ)` -/

/-- The push-forward of Lebesgue measure under `± hopf` (a Haar measure on `SL(2, ℝ)`). -/
noncomputable def hopfMeasure : Measure SL(2, ℝ) :=
  volume.map hopf + volume.map fun p ↦ -hopf p

lemma lintegral_hopfMeasure {F : SL(2, ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F g ∂hopfMeasure = ∫⁻ p, (F (hopf p) + F (-hopf p)) := by
  rw [hopfMeasure, lintegral_add_measure, lintegral_map hF measurable_hopf,
    lintegral_map hF measurable_neg_hopf,
    ← lintegral_add_left (by fun_prop : Measurable fun p ↦ F (hopf p))]

@[fun_prop]
lemma measurable_mul_left_SL (γ : SL(2, ℝ)) : Measurable fun g : SL(2, ℝ) ↦ γ * g :=
  (continuous_const_mul γ).measurable

@[fun_prop]
lemma measurable_mul_right_SL (γ : SL(2, ℝ)) : Measurable fun g : SL(2, ℝ) ↦ g * γ :=
  (continuous_mul_const γ).measurable

/-- **Left invariance.** -/
theorem lintegral_hopfMeasure_mul_left (γ : SL(2, ℝ)) {F : SL(2, ℝ) → ℝ≥0∞}
    (hF : Measurable F) : ∫⁻ g, F (γ * g) ∂hopfMeasure = ∫⁻ g, F g ∂hopfMeasure := by
  rw [lintegral_hopfMeasure (by fun_prop : Measurable fun g ↦ F (γ * g)),
    lintegral_hopfMeasure hF]
  have hH : Measurable fun p ↦ F (hopf p) + F (-hopf p) := by fun_prop
  rw [← lintegral_comp_hopfT γ hH]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_cocy_ne γ] with p hp
  rcases hp.lt_or_gt with h | h
  · simp only [mul_neg, mul_hopf_of_neg γ p h, neg_neg]
    rw [add_comm]
  · simp only [mul_neg, mul_hopf_of_pos γ p h]

/-- **Right invariance under `N`.** -/
theorem lintegral_hopfMeasure_mul_unip (t : ℝ) {F : SL(2, ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F (g * unip t) ∂hopfMeasure = ∫⁻ g, F g ∂hopfMeasure := by
  rw [lintegral_hopfMeasure (by fun_prop : Measurable fun g ↦ F (g * unip t)),
    lintegral_hopfMeasure hF]
  have hH : Measurable fun p ↦ F (hopf p) + F (-hopf p) := by fun_prop
  rw [← (measurePreserving_hopfN t).lintegral_comp hH]
  simp only [neg_mul, hopf_mul_unip]

/-- **Right invariance under `A`.** -/
theorem lintegral_hopfMeasure_mul_diagA (σ : ℝ) {F : SL(2, ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F (g * diagA σ) ∂hopfMeasure = ∫⁻ g, F g ∂hopfMeasure := by
  rw [lintegral_hopfMeasure (by fun_prop : Measurable fun g ↦ F (g * diagA σ)),
    lintegral_hopfMeasure hF]
  have hH : Measurable fun p ↦ F (hopf p) + F (-hopf p) := by fun_prop
  rw [← (measurePreserving_hopfA σ).lintegral_comp hH]
  simp only [neg_mul, hopf_mul_diagA]

end OrbicurveCores.M2
