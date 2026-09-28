/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.HopfCoords

/-!
# The base-point map and hyperbolic area

For `E ⊆ ℍ` measurable, `hopfMeasure {g | g • I ∈ E} = π · area(E)`
(`hopfMeasure_basept`). In Hopf coordinates `hopf (x, u, s) • I = x - 1 / (u + i e²ˢ)`; we
integrate first over `x` (a horizontal translation), then substitute `u = e²ˢ v` and
`η = e⁻²ˢ / (1 + v²)`, and finally use `∫ dv / (1 + v²) = π`.
-/

open MeasureTheory Matrix Set Filter Real UpperHalfPlane
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

lemma exp_neg_eq_inv' (s : ℝ) : exp (-s) = (exp s)⁻¹ := exp_neg s

/-- The base point in Hopf coordinates. -/
lemma coe_hopf_smul_I (p : ℝ × ℝ × ℝ) :
    ((hopf p • I : ℍ) : ℂ) =
      ((p.1 - p.2.1 / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2) : ℝ) : ℂ) +
        ((exp (2 * p.2.2) / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2) : ℝ) : ℂ) * Complex.I := by
  rw [coe_specialLinearGroup_apply]
  obtain ⟨x, u, s⟩ := p
  simp only [coe_hopf, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one,
    empty_val', coe_I]
  have hE := exp_pos s
  have h2 : exp (2 * s) = exp s ^ 2 := by rw [← exp_nat_mul]; ring_nf
  rw [h2, exp_neg_eq_inv']
  generalize exp s = E at hE ⊢
  have hD : (0 : ℝ) < (E ^ 2) ^ 2 + u ^ 2 := by positivity
  have hden : ((E : ℝ) : ℂ) * Complex.I + ((u * E⁻¹ : ℝ) : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_im, mul_one, zero_mul, add_zero] at this
    exact hE.ne' this
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hden ⊢
  rw [div_eq_iff hden]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    field_simp <;> ring

lemma re_hopf_smul_I (p : ℝ × ℝ × ℝ) :
    (hopf p • I).re = p.1 - p.2.1 / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2) := by
  have := congrArg Complex.re (coe_hopf_smul_I p)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, coe_re] at this
  rw [this]; ring

lemma im_hopf_smul_I (p : ℝ × ℝ × ℝ) :
    (hopf p • I).im = exp (2 * p.2.2) / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2) := by
  have := congrArg Complex.im (coe_hopf_smul_I p)
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, coe_im] at this
  rw [this]; ring

/-- The substitution `η = k e^{-2s}`. -/
lemma lintegral_exp_subst {k : ℝ} (hk : 0 < k) (L : ℝ → ℝ≥0∞) :
    ∫⁻ s, ENNReal.ofReal (exp (2 * s)) * L (k * exp (-(2 * s))) =
      ENNReal.ofReal (k / 2) * ∫⁻ η in Ioi 0, ENNReal.ofReal ((η ^ 2)⁻¹) * L η := by
  set f : ℝ → ℝ := fun s ↦ k * exp (-(2 * s))
  have hf : ∀ s ∈ (univ : Set ℝ), HasDerivWithinAt f (k * (exp (-(2 * s)) * -(2 * 1))) univ s :=
    fun s _ ↦ (((hasDerivAt_id s).const_mul 2).neg.exp.const_mul k).hasDerivWithinAt
  have hinj : InjOn f univ := by
    intro a _ b _ hab
    have h1 := mul_left_cancel₀ hk.ne' hab
    have h2 := exp_injective h1
    linarith
  have himg : f '' univ = Ioi 0 := by
    ext η
    constructor
    · rintro ⟨s, -, rfl⟩
      exact mul_pos hk (exp_pos _)
    · intro hη
      refine ⟨-(log (η / k)) / 2, trivial, ?_⟩
      simp only [f]
      rw [show -(2 * (-log (η / k) / 2)) = log (η / k) by ring, exp_log (div_pos hη hk)]
      field_simp
  have main := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hf hinj
    (fun η ↦ ENNReal.ofReal (k / 2) * (ENNReal.ofReal ((η ^ 2)⁻¹) * L η))
  rw [himg, Measure.restrict_univ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at main
  rw [main]
  refine lintegral_congr fun s ↦ ?_
  simp only [f]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hE := exp_pos (-(2 * s))
  have e : exp (2 * s) = (exp (-(2 * s)))⁻¹ := by rw [exp_neg, inv_inv]
  rw [e, abs_of_neg (by nlinarith)]
  field_simp

/-- The length of a horizontal slice. -/
noncomputable def sliceLen (S : Set (ℝ × ℝ)) (η : ℝ) : ℝ≥0∞ := ∫⁻ x, S.indicator 1 (x, η)

lemma measurable_sliceLen {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) : Measurable (sliceLen S) :=
  (measurable_one.indicator hS).lintegral_prod_left'

/-- **The base-point integral in Hopf coordinates.** -/
lemma lintegral_basept (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    ∫⁻ p : ℝ × ℝ × ℝ, S.indicator 1 (p.1 - p.2.1 / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2),
      exp (2 * p.2.2) / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2)) =
      ENNReal.ofReal (π / 2) * ∫⁻ η in Ioi 0, ENNReal.ofReal ((η ^ 2)⁻¹) * sliceLen S η := by
  have hL := measurable_sliceLen hS
  set I₀ := ∫⁻ η in Ioi 0, ENNReal.ofReal ((η ^ 2)⁻¹) * sliceLen S η
  -- integrate over `x` first
  have step1 : ∫⁻ p : ℝ × ℝ × ℝ, S.indicator 1 (p.1 - p.2.1 / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2),
      exp (2 * p.2.2) / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2)) =
      ∫⁻ q : ℝ × ℝ, sliceLen S (exp (2 * q.2) / (exp (2 * q.2) ^ 2 + q.1 ^ 2)) := by
    have hm : Measurable fun p : ℝ × ℝ × ℝ ↦
        S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (p.1 - p.2.1 / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2),
          exp (2 * p.2.2) / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2)) :=
      (measurable_one.indicator hS).comp (by fun_prop)
    rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ), lintegral_prod_symm _ hm.aemeasurable]
    refine lintegral_congr fun q ↦ ?_
    simp only [sliceLen, sub_eq_add_neg]
    exact lintegral_add_right_eq_self (fun x ↦ S.indicator 1 (x, _)) _
  -- substitute `u = e²ˢ v`
  have step2 : ∀ s : ℝ, ∫⁻ u, sliceLen S (exp (2 * s) / (exp (2 * s) ^ 2 + u ^ 2)) =
      ENNReal.ofReal (exp (2 * s)) *
        ∫⁻ v, sliceLen S ((1 + v ^ 2)⁻¹ * exp (-(2 * s))) := by
    intro s
    have hr0 := exp_pos (2 * s)
    have h := lintegral_comp_mul_add hr0.ne' 0
      (fun u ↦ sliceLen S (exp (2 * s) / (exp (2 * s) ^ 2 + u ^ 2)))
    have key : ∫⁻ u, sliceLen S (exp (2 * s) / (exp (2 * s) ^ 2 + u ^ 2)) =
        ENNReal.ofReal (exp (2 * s)) * ∫⁻ v, sliceLen S
          (exp (2 * s) / (exp (2 * s) ^ 2 + (exp (2 * s) * v + 0) ^ 2)) := by
      rw [h, ← mul_assoc, ← ENNReal.ofReal_mul hr0.le, abs_of_pos (inv_pos.2 hr0),
        mul_inv_cancel₀ hr0.ne', ENNReal.ofReal_one, one_mul]
    rw [key]
    congr 1
    refine lintegral_congr fun v ↦ ?_
    congr 1
    rw [exp_neg]
    field_simp
    ring
  -- substitute `η = e⁻²ˢ / (1 + v²)`
  have step3 : ∀ v : ℝ, ∫⁻ s, ENNReal.ofReal (exp (2 * s)) *
      sliceLen S ((1 + v ^ 2)⁻¹ * exp (-(2 * s))) = ENNReal.ofReal ((1 + v ^ 2)⁻¹ / 2) * I₀ :=
    fun v ↦ lintegral_exp_subst (by positivity) _
  have hm2 : Measurable fun q : ℝ × ℝ ↦
      sliceLen S (exp (2 * q.2) / (exp (2 * q.2) ^ 2 + q.1 ^ 2)) := hL.comp (by fun_prop)
  rw [step1, Measure.volume_eq_prod, lintegral_prod_symm _ hm2.aemeasurable]
  simp only [step2]
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (by
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      (hL.comp (by fun_prop)) |>.aemeasurable)]
  simp only [step3]
  rw [lintegral_mul_const _ (by fun_prop)]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inv_one_add_sq.div_const 2)
    (ae_of_all _ fun v ↦ by positivity), integral_div, integral_univ_inv_one_add_sq]

/-- A subset of `ℍ` in real coordinates. -/
def realCoords (E : Set ℍ) : Set (ℝ × ℝ) :=
  Complex.measurableEquivRealProd.symm ⁻¹' (((↑) : ℍ → ℂ) '' E)

lemma measurableSet_realCoords {E : Set ℍ} (hE : MeasurableSet E) :
    MeasurableSet (realCoords E) :=
  (measurableEmbedding_coe.measurableSet_image.mpr hE).preimage
    Complex.measurableEquivRealProd.symm.measurable

lemma mem_realCoords (E : Set ℍ) (z : ℍ) : (z.re, z.im) ∈ realCoords E ↔ z ∈ E := by
  simp only [realCoords, Set.mem_preimage, Complex.measurableEquivRealProd_symm_apply,
    Set.mem_image]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have : w = z := UpperHalfPlane.ext (by rw [hwz]; rfl)
    exact this ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

lemma pos_of_mem_realCoords {E : Set ℍ} {q : ℝ × ℝ} (hq : q ∈ realCoords E) : 0 < q.2 := by
  obtain ⟨w, -, hw⟩ := hq
  have := congrArg Complex.im hw
  simp only [Complex.measurableEquivRealProd_symm_apply] at this
  rw [← this]
  exact w.im_pos

/-- **Hyperbolic area via horizontal slices.** -/
lemma volume_eq_sliceLen {E : Set ℍ} (hE : MeasurableSet E) :
    volume E = ∫⁻ η in Ioi 0, ENNReal.ofReal ((η ^ 2)⁻¹) * sliceLen (realCoords E) η := by
  have hE₂ := measurableSet_realCoords hE
  rw [volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  have hpt : ∀ q : ℝ × ℝ, ((((1 / ‖(Complex.measurableEquivRealProd.symm q).im‖₊) ^ 2 : NNReal)) :
      ℝ≥0∞) = ENNReal.ofReal ((q.2 ^ 2)⁻¹) := by
    intro q
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [sq_abs]
  simp_rw [hpt]
  have hm : Measurable fun a : ℝ × ℝ ↦
      (realCoords E).indicator (fun a ↦ ENNReal.ofReal ((a.2 ^ 2)⁻¹)) a :=
    (by fun_prop : Measurable fun a : ℝ × ℝ ↦ ENNReal.ofReal ((a.2 ^ 2)⁻¹)).indicator hE₂
  rw [← realCoords, ← lintegral_indicator hE₂, Measure.volume_eq_prod,
    lintegral_prod_symm _ hm.aemeasurable, ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun η ↦ ?_
  by_cases hη : η ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hη, sliceLen, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : (x, η) ∈ realCoords E
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  · rw [Set.indicator_of_notMem hη]
    have h0 : ∀ x, (realCoords E).indicator (fun a ↦ ENNReal.ofReal ((a.2 ^ 2)⁻¹)) (x, η) = 0 :=
      fun x ↦ Set.indicator_of_notMem (fun h ↦ hη (pos_of_mem_realCoords (q := (x, η)) h)) _
    simp [h0]

lemma neg_smul_SL' (γ : SL(2, ℝ)) (z : ℍ) : (-γ) • z = γ • z := by
  have h : ∀ g : SL(2, ℝ), g • z = (Matrix.SpecialLinearGroup.mapGL ℝ g) • z := fun g ↦ rfl
  rw [h, h, show Matrix.SpecialLinearGroup.mapGL ℝ (-γ) = -Matrix.SpecialLinearGroup.mapGL ℝ γ by
    ext; simp [Matrix.SpecialLinearGroup.coe_neg]]
  exact UpperHalfPlane.neg_smul _ _

lemma measurableSet_basept {E : Set ℍ} (hE : MeasurableSet E) :
    MeasurableSet {g : SL(2, ℝ) | g • I ∈ E} :=
  hE.preimage (continuous_id.smul continuous_const).measurable

/-- **The base-point map pushes `hopfMeasure` to `π` times hyperbolic area.** -/
theorem hopfMeasure_basept {E : Set ℍ} (hE : MeasurableSet E) :
    hopfMeasure {g : SL(2, ℝ) | g • I ∈ E} = ENNReal.ofReal π * volume E := by
  have hS := measurableSet_basept hE
  rw [← lintegral_indicator_one hS, lintegral_hopfMeasure (measurable_one.indicator hS),
    volume_eq_sliceLen hE]
  have hpt : ∀ p : ℝ × ℝ × ℝ, {g : SL(2, ℝ) | g • I ∈ E}.indicator (1 : SL(2, ℝ) → ℝ≥0∞) (hopf p) +
      {g : SL(2, ℝ) | g • I ∈ E}.indicator 1 (-hopf p) = 2 * (realCoords E).indicator 1
        (p.1 - p.2.1 / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2),
          exp (2 * p.2.2) / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2)) := by
    intro p
    have hiff : hopf p ∈ {g : SL(2, ℝ) | g • I ∈ E} ↔
        (p.1 - p.2.1 / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2),
          exp (2 * p.2.2) / (exp (2 * p.2.2) ^ 2 + p.2.1 ^ 2)) ∈ realCoords E := by
      rw [← re_hopf_smul_I, ← im_hopf_smul_I, mem_realCoords]; rfl
    have hneg : -hopf p ∈ {g : SL(2, ℝ) | g • I ∈ E} ↔ hopf p ∈ {g : SL(2, ℝ) | g • I ∈ E} := by
      simp only [Set.mem_setOf_eq, neg_smul_SL']
    by_cases h : hopf p ∈ {g : SL(2, ℝ) | g • I ∈ E}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hneg.mpr h),
        Set.indicator_of_mem (hiff.mp h)]
      simp only [Pi.one_apply]
      norm_num
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' ↦ h (hneg.mp h')),
        Set.indicator_of_notMem (fun h' ↦ h (hiff.mpr h'))]
      rw [add_zero, mul_zero]
  refine (lintegral_congr hpt).trans ?_
  have hm : Measurable fun a : ℝ × ℝ × ℝ ↦ (realCoords E).indicator (1 : ℝ × ℝ → ℝ≥0∞)
      (a.1 - a.2.1 / (rexp (2 * a.2.2) ^ 2 + a.2.1 ^ 2),
        rexp (2 * a.2.2) / (rexp (2 * a.2.2) ^ 2 + a.2.1 ^ 2)) :=
    (measurable_one.indicator (measurableSet_realCoords hE)).comp (by fun_prop)
  rw [lintegral_const_mul _ hm, lintegral_basept _ (measurableSet_realCoords hE), ← mul_assoc]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  ring_nf

end OrbicurveCores.M2
