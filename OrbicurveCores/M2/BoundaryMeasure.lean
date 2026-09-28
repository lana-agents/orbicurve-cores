/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.Setup
import OrbicurveCores.ForMathlib.ProjectiveLine

/-!
# M2: measure theory of the boundary action

The boundary `B = OnePoint ℝ` carries the Cauchy measure `cauchy`, a finite measure in the
Lebesgue class (`bdry ≪ cauchy ≪ bdry`). For `g ∈ SL(2, ℝ)`:

* `cauchy_preimage_le`: `ν(g⁻¹E) ≤ ‖g‖² ν(E)` (explicit Radon–Nikodym bound, by the
  one-dimensional change of variables);
* `quasiMeasurePreserving_smul`: `g` preserves the Lebesgue class;
* `tendsto_lintegral_comp_smul`: translation is continuous in `L¹` for bounded measurable
  functions;
* `exists_subseq_ae_tendsto`: if `gₙ → g₀` and `ψ : B → Y` is measurable into a compact
  metrizable space, a subsequence of `ψ ∘ gₙ` converges a.e. to `ψ ∘ g₀`.
-/

open MeasureTheory Matrix Matrix.SpecialLinearGroup OnePoint Set Filter Topology
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

/-- The Möbius function of `g ∈ SL(2, ℝ)` on `ℝ`. -/
noncomputable def mobR (g : SL(2, ℝ)) (x : ℝ) : ℝ := (g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1)

/-- The squared Frobenius norm. -/
def frob (g : SL(2, ℝ)) : ℝ := g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2

lemma det_eq_one (g : SL(2, ℝ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.2; rw [Matrix.det_fin_two] at this; exact this

lemma smul_coe_of_ne (g : SL(2, ℝ)) {x : ℝ} (hx : g 1 0 * x + g 1 1 ≠ 0) :
    g • (x : OnePoint ℝ) = (mobR g x : OnePoint ℝ) := by
  rw [sl_smul_bdry, OnePoint.smul_some_eq_ite]
  simp [hx, mobR]

lemma hasDerivAt_mobR (g : SL(2, ℝ)) {x : ℝ} (hx : g 1 0 * x + g 1 1 ≠ 0) :
    HasDerivAt (mobR g) (1 / (g 1 0 * x + g 1 1) ^ 2) x := by
  have h1 : HasDerivAt (fun x ↦ g 0 0 * x + g 0 1) (g 0 0) x := by
    simpa using ((hasDerivAt_id x).const_mul (g 0 0)).add_const (g 0 1)
  have h2 : HasDerivAt (fun x ↦ g 1 0 * x + g 1 1) (g 1 0) x := by
    simpa using ((hasDerivAt_id x).const_mul (g 1 0)).add_const (g 1 1)
  refine (h1.div h2 hx).congr_deriv ?_
  have hd := det_eq_one g
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (g 1 0 * x + g 1 1) ^ 2 * hd

/-- The Cauchy density bound: `|f'(y)| w(f y) ≤ ‖g‖² w(y)` for `w(y) = (1 + y²)⁻¹`. -/
lemma cauchy_density_le (g : SL(2, ℝ)) {y : ℝ} (hy : g 1 0 * y + g 1 1 ≠ 0) :
    |1 / (g 1 0 * y + g 1 1) ^ 2| * (1 + mobR g y ^ 2)⁻¹ ≤ frob g * (1 + y ^ 2)⁻¹ := by
  set D := g 1 0 * y + g 1 1
  set N := g 0 0 * y + g 0 1
  have hD : 0 < D ^ 2 := by positivity
  have hdet := det_eq_one g
  have e : |1 / D ^ 2| * (1 + mobR g y ^ 2)⁻¹ = (N ^ 2 + D ^ 2)⁻¹ := by
    have hm : mobR g y = N / D := rfl
    rw [abs_of_pos (by positivity), hm]
    field_simp
    ring
  rw [e]
  have hND : 0 < N ^ 2 + D ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hND]
  -- `y = g₁₁ N − g₀₁ D` and `1 = g₀₀ D − g₁₀ N`
  have ey : y = g 1 1 * N - g 0 1 * D := by simp only [N, D]; linear_combination (-y) * hdet
  have e1 : (1 : ℝ) = g 0 0 * D - g 1 0 * N := by simp only [N, D]; linear_combination -hdet
  rw [frob]
  nth_rewrite 1 [ey]
  nth_rewrite 1 [e1]
  nlinarith [sq_nonneg (g 1 1 * D + g 0 1 * N), sq_nonneg (g 0 0 * N + g 1 0 * D)]

/-- `SL(2, ℝ)` acts continuously on the boundary. -/
lemma continuous_smul_bdry (g : SL(2, ℝ)) : Continuous fun x : OnePoint ℝ ↦ g • x := by
  simp_rw [sl_smul_bdry]; exact OnePoint.Proj.continuous_gl_smul _

lemma measurable_smul_bdry (g : SL(2, ℝ)) : Measurable fun x : OnePoint ℝ ↦ g • x :=
  (continuous_smul_bdry g).measurable

/-- The Cauchy weight. -/
noncomputable def cw (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 + x ^ 2)⁻¹

lemma measurable_cw : Measurable cw := by unfold cw; fun_prop

/-- The Cauchy measure on `ℝ`, and on the boundary `OnePoint ℝ` (a finite measure in the
Lebesgue class). -/
noncomputable def cauchyR : Measure ℝ := volume.withDensity cw

noncomputable def cauchy : Measure (OnePoint ℝ) := cauchyR.map ((↑) : ℝ → OnePoint ℝ)

instance : IsFiniteMeasure cauchyR := by
  refine ⟨?_⟩
  rw [cauchyR, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := integrable_inv_one_add_sq.hasFiniteIntegral
  unfold HasFiniteIntegral at this
  convert this using 2
  funext x
  simp only [cw]
  rw [Real.enorm_eq_ofReal (by positivity)]

instance : IsFiniteMeasure cauchy := by unfold cauchy; infer_instance

lemma cauchy_apply {E : Set (OnePoint ℝ)} (hE : MeasurableSet E) :
    cauchy E = ∫⁻ x in (↑) ⁻¹' E, cw x := by
  rw [cauchy, Measure.map_apply OnePoint.continuous_coe.measurable hE, cauchyR,
    withDensity_apply _ (OnePoint.continuous_coe.measurable hE)]

lemma frob_inv (g : SL(2, ℝ)) : frob g⁻¹ = frob g := by
  simp only [frob, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero]
  ring

lemma frob_nonneg (g : SL(2, ℝ)) : 0 ≤ frob g := by unfold frob; positivity

/-- **Quasi-invariance with a bound.** `ν(g⁻¹ E) ≤ ‖g‖² ν(E)` for the Cauchy measure. -/
theorem cauchy_preimage_le (g : SL(2, ℝ)) {E : Set (OnePoint ℝ)} (hE : MeasurableSet E) :
    cauchy ((fun x ↦ g • x) ⁻¹' E) ≤ ENNReal.ofReal (frob g) * cauchy E := by
  set h := g⁻¹
  have hdg := det_eq_one g
  have hh : ∀ i j, h i j = (g⁻¹ : SL(2, ℝ)) i j := fun _ _ ↦ rfl
  have h00 : h 0 0 = g 1 1 := by simp [h, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have h01 : h 0 1 = -g 0 1 := by simp [h, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have h10 : h 1 0 = -g 1 0 := by simp [h, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have h11 : h 1 1 = g 0 0 := by simp [h, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  set S' : Set ℝ := ((↑) ⁻¹' E) ∩ {e | h 1 0 * e + h 1 1 ≠ 0}
  set P : Set ℝ := {x | g 1 0 * x + g 1 1 = 0}
  have hS' : MeasurableSet S' :=
    (OnePoint.continuous_coe.measurable hE).inter
      (isOpen_ne_fun (by fun_prop) (by fun_prop)).measurableSet
  have hP : volume P = 0 := by
    by_cases hg : g 1 0 = 0
    · have : P = ∅ := by
        ext x; simp only [P, hg, zero_mul, zero_add, mem_setOf_eq, mem_empty_iff_false,
          iff_false]
        intro h0; rw [hg, h0] at hdg; simp at hdg
      rw [this, measure_empty]
    · have : P = {-g 1 1 / g 1 0} := by
        ext x; simp only [P, mem_setOf_eq, mem_singleton_iff]
        constructor
        · intro hx; field_simp; linear_combination hx
        · rintro rfl; field_simp; ring
      rw [this, Real.volume_singleton]
  have hsub : (↑) ⁻¹' ((fun x ↦ g • x) ⁻¹' E) ⊆ mobR h '' S' ∪ P := by
    intro x hx
    by_cases hxP : x ∈ P
    · exact Or.inr hxP
    left
    have hD : g 1 0 * x + g 1 1 ≠ 0 := hxP
    simp only [mem_preimage] at hx
    rw [smul_coe_of_ne g hD] at hx
    refine ⟨mobR g x, ⟨hx, ?_⟩, ?_⟩
    · have e : h 1 0 * mobR g x + h 1 1 = 1 / (g 1 0 * x + g 1 1) := by
        rw [h10, h11, mobR, eq_div_iff hD]
        field_simp
        linear_combination hdg
      change h 1 0 * mobR g x + h 1 1 ≠ 0
      rw [e]; exact one_div_ne_zero hD
    · have e : h 1 0 * mobR g x + h 1 1 = 1 / (g 1 0 * x + g 1 1) := by
        rw [h10, h11, mobR, eq_div_iff hD]
        field_simp
        linear_combination hdg
      change (h 0 0 * mobR g x + h 0 1) / (h 1 0 * mobR g x + h 1 1) = x
      have hn : mobR g x * (g 1 0 * x + g 1 1) = g 0 0 * x + g 0 1 := div_mul_cancel₀ _ hD
      rw [e, h00, h01, div_div_eq_mul_div, div_one]
      linear_combination g 1 1 * hn + x * hdg
  have hinj : InjOn (mobR h) S' := by
    intro a ha b hb hab
    have ha' : h 1 0 * a + h 1 1 ≠ 0 := ha.2
    have hb' : h 1 0 * b + h 1 1 ≠ 0 := hb.2
    have hdh := det_eq_one h
    simp only [mobR] at hab
    rw [div_eq_div_iff ha' hb'] at hab
    linear_combination hab - (a - b) * hdh
  rw [cauchy_apply ((measurable_smul_bdry g) hE), cauchy_apply hE]
  calc ∫⁻ x in (↑) ⁻¹' ((fun x ↦ g • x) ⁻¹' E), cw x
      ≤ ∫⁻ x in mobR h '' S' ∪ P, cw x := lintegral_mono_set hsub
    _ ≤ (∫⁻ x in mobR h '' S', cw x) + ∫⁻ x in P, cw x := lintegral_union_le (μ := volume) cw _ _
    _ = ∫⁻ x in mobR h '' S', cw x := by
        simp [Measure.restrict_eq_zero.mpr hP]
    _ = ∫⁻ x in S', ENNReal.ofReal |1 / (h 1 0 * x + h 1 1) ^ 2| * cw (mobR h x) :=
        lintegral_image_eq_lintegral_abs_deriv_mul hS'
          (fun x hx ↦ (hasDerivAt_mobR h hx.2).hasDerivWithinAt) hinj cw
    _ ≤ ∫⁻ x in S', ENNReal.ofReal (frob g) * cw x := by
        refine setLIntegral_mono (measurable_cw.const_mul _) fun x hx ↦ ?_
        rw [cw, cw, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (frob_nonneg g)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← frob_inv g]
        exact cauchy_density_le h hx.2
    _ = ENNReal.ofReal (frob g) * ∫⁻ x in S', cw x := lintegral_const_mul _ measurable_cw
    _ ≤ ENNReal.ofReal (frob g) * ∫⁻ x in (↑) ⁻¹' E, cw x := by
        gcongr
        exact inter_subset_left

lemma map_smul_cauchy_le (g : SL(2, ℝ)) :
    cauchy.map (fun x ↦ g • x) ≤ ENNReal.ofReal (frob g) • cauchy := by
  refine Measure.le_iff.2 fun E hE ↦ ?_
  rw [Measure.map_apply (measurable_smul_bdry g) hE, Measure.smul_apply, smul_eq_mul]
  exact cauchy_preimage_le g hE

lemma cauchy_absolutelyContinuous_bdry : cauchy ≪ bdry :=
  (withDensity_absolutelyContinuous _ _).map OnePoint.continuous_coe.measurable

lemma bdry_absolutelyContinuous_cauchy : bdry ≪ cauchy := by
  refine Measure.AbsolutelyContinuous.map ?_ OnePoint.continuous_coe.measurable
  refine withDensity_absolutelyContinuous' measurable_cw.aemeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [cw, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity

/-- Each `g ∈ SL(2, ℝ)` preserves the Lebesgue class on the boundary. -/
lemma quasiMeasurePreserving_smul (g : SL(2, ℝ)) :
    Measure.QuasiMeasurePreserving (fun x : OnePoint ℝ ↦ g • x) bdry bdry := by
  refine ⟨measurable_smul_bdry g, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun E hE h0 ↦ ?_
  rw [Measure.map_apply (measurable_smul_bdry g) hE]
  refine bdry_absolutelyContinuous_cauchy ?_
  refine le_antisymm ?_ bot_le
  calc cauchy ((fun x ↦ g • x) ⁻¹' E) ≤ ENNReal.ofReal (frob g) * cauchy E :=
        cauchy_preimage_le g hE
    _ = 0 := by rw [cauchy_absolutelyContinuous_bdry h0, mul_zero]

lemma continuous_smul_bdry_left (x : OnePoint ℝ) :
    Continuous fun g : SL(2, ℝ) ↦ g • x := by
  refine continuous_iff_continuousAt.2 fun g₀ ↦ ?_
  have hM : Continuous fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) :=
    continuous_subtype_val
  have h := OnePoint.Proj.continuousAt_mob_param hM.continuousAt
    (by rw [g₀.2]; exact one_ne_zero) x
  have e : ∀ g : SL(2, ℝ), g • x = OnePoint.Proj.mob (g : Matrix (Fin 2) (Fin 2) ℝ) x := by
    intro g; rw [sl_smul_bdry, OnePoint.Proj.gl_smul_eq_mob]; rfl
  simp_rw [e]
  exact h.comp (f := fun g : SL(2, ℝ) ↦ (g, x)) (by fun_prop)

lemma continuous_frob : Continuous frob := by
  unfold frob
  have e : ∀ i j, Continuous fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) i j := fun i j ↦
    continuous_subtype_val.matrix_elem i j
  fun_prop

lemma lintegral_comp_smul_le (g : SL(2, ℝ)) {h : OnePoint ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, h (g • x) ∂cauchy ≤ ENNReal.ofReal (frob g) * ∫⁻ x, h x ∂cauchy := by
  rw [← lintegral_map hh (measurable_smul_bdry g)]
  calc ∫⁻ a, h a ∂(cauchy.map fun x ↦ g • x)
      ≤ ∫⁻ a, h a ∂(ENNReal.ofReal (frob g) • cauchy) :=
        lintegral_mono' (map_smul_cauchy_le g) le_rfl
    _ = _ := lintegral_smul_measure _ _

/-- **Continuity of translation in `L¹`** for bounded measurable functions on the boundary. -/
theorem tendsto_lintegral_comp_smul {F : OnePoint ℝ → ℝ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ x, |F x| ≤ B) {g : ℕ → SL(2, ℝ)} {g₀ : SL(2, ℝ)} (hg : Tendsto g atTop (𝓝 g₀)) :
    Tendsto (fun n ↦ ∫⁻ x, ‖F (g n • x) - F (g₀ • x)‖ₑ ∂cauchy) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Filter.Eventually.of_forall fun _ ↦ hεt ▸ le_top
  set C := frob g₀ + 1
  have hC : 0 < C := by have := frob_nonneg g₀; simp only [C]; linarith
  set η := ε.toReal / (2 * C + 1)
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  have hη : 0 < η := by positivity
  -- approximation by a bounded continuous function
  have hmem : MemLp F 1 cauchy :=
    MemLp.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]; exact hb x)
  obtain ⟨φ, hφ, -⟩ := hmem.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top
    (ENNReal.ofReal_pos.2 hη).ne'
  rw [eLpNorm_one_eq_lintegral_enorm] at hφ
  have hFφ : Measurable fun x ↦ ‖F x - φ x‖ₑ := (hF.sub φ.continuous.measurable).enorm
  have hφφ : ∀ n, Measurable fun x ↦ ‖φ (g n • x) - φ (g₀ • x)‖ₑ := fun n ↦
    ((φ.continuous.measurable.comp (measurable_smul_bdry _)).sub
      (φ.continuous.measurable.comp (measurable_smul_bdry _))).enorm
  -- the middle term tends to zero
  have hmid : Tendsto (fun n ↦ ∫⁻ x, ‖φ (g n • x) - φ (g₀ • x)‖ₑ ∂cauchy) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := cauchy)
      (fun _ ↦ ENNReal.ofReal (2 * ‖φ‖)) hφφ ?_
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (f := fun _ ↦ 0) ?_
    · simpa using this
    · intro n
      refine Filter.Eventually.of_forall fun x ↦ ?_
      change ‖φ (g n • x) - φ (g₀ • x)‖ₑ ≤ ENNReal.ofReal (2 * ‖φ‖)
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖φ (g n • x) - φ (g₀ • x)‖ ≤ ‖φ (g n • x)‖ + ‖φ (g₀ • x)‖ := norm_sub_le _ _
        _ ≤ ‖φ‖ + ‖φ‖ := add_le_add (φ.norm_coe_le_norm _) (φ.norm_coe_le_norm _)
        _ = 2 * ‖φ‖ := by ring
    · refine Filter.Eventually.of_forall fun x ↦ ?_
      have hc : Tendsto (fun n ↦ φ (g n • x)) atTop (𝓝 (φ (g₀ • x))) :=
        (φ.continuous.tendsto _).comp ((continuous_smul_bdry_left x).tendsto g₀ |>.comp hg)
      have := (hc.sub_const (φ (g₀ • x))).enorm
      simpa using this
  have hev1 : ∀ᶠ n in atTop, frob (g n) ≤ C :=
    (continuous_frob.tendsto g₀ |>.comp hg).eventually (gt_mem_nhds (by simp [C])) |>.mono
      fun n hn ↦ hn.le
  have hev2 := (ENNReal.tendsto_nhds_zero.1 hmid) (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  filter_upwards [hev1, hev2] with n hn1 hn2
  have hsplit : ∀ x, ‖F (g n • x) - F (g₀ • x)‖ₑ ≤ ‖F (g n • x) - φ (g n • x)‖ₑ +
      ‖φ (g n • x) - φ (g₀ • x)‖ₑ + ‖F (g₀ • x) - φ (g₀ • x)‖ₑ := by
    intro x
    calc ‖F (g n • x) - F (g₀ • x)‖ₑ = ‖(F (g n • x) - φ (g n • x)) +
          (φ (g n • x) - φ (g₀ • x)) - (F (g₀ • x) - φ (g₀ • x))‖ₑ := by congr 1; ring
      _ ≤ ‖(F (g n • x) - φ (g n • x)) + (φ (g n • x) - φ (g₀ • x))‖ₑ +
          ‖F (g₀ • x) - φ (g₀ • x)‖ₑ := enorm_sub_le
      _ ≤ _ := by gcongr; exact enorm_add_le _ _
  have t1 : ∫⁻ x, ‖F (g n • x) - φ (g n • x)‖ₑ ∂cauchy ≤ ENNReal.ofReal C * ENNReal.ofReal η :=
    (lintegral_comp_smul_le (g n) hFφ).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hn1) hφ)
  have t3 : ∫⁻ x, ‖F (g₀ • x) - φ (g₀ • x)‖ₑ ∂cauchy ≤ ENNReal.ofReal C * ENNReal.ofReal η :=
    (lintegral_comp_smul_le g₀ hFφ).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (by simp [C])) hφ)
  calc ∫⁻ x, ‖F (g n • x) - F (g₀ • x)‖ₑ ∂cauchy
      ≤ ∫⁻ x, (‖F (g n • x) - φ (g n • x)‖ₑ + ‖φ (g n • x) - φ (g₀ • x)‖ₑ +
          ‖F (g₀ • x) - φ (g₀ • x)‖ₑ) ∂cauchy := lintegral_mono hsplit
    _ = ∫⁻ x, ‖F (g n • x) - φ (g n • x)‖ₑ ∂cauchy +
          ∫⁻ x, ‖φ (g n • x) - φ (g₀ • x)‖ₑ ∂cauchy +
          ∫⁻ x, ‖F (g₀ • x) - φ (g₀ • x)‖ₑ ∂cauchy := by
        have m1 : Measurable fun x ↦ ‖F (g n • x) - φ (g n • x)‖ₑ :=
          hFφ.comp (measurable_smul_bdry _)
        rw [lintegral_add_left (f := fun x ↦ ‖F (g n • x) - φ (g n • x)‖ₑ +
          ‖φ (g n • x) - φ (g₀ • x)‖ₑ) (m1.add (hφφ n)), lintegral_add_left m1]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal η + ENNReal.ofReal η +
          ENNReal.ofReal C * ENNReal.ofReal η := by gcongr
    _ = ENNReal.ofReal ((2 * C + 1) * η) := by
        rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_add (by positivity) hη.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ = ε := by
        rw [show (2 * C + 1) * η = ε.toReal by simp only [η]; field_simp,
          ENNReal.ofReal_toReal hεt]
    _ ≤ ε := le_rfl

/-- **Continuity of translation in measure.** If `gₙ → g₀` then, for a measurable map `ψ` from
the boundary to a compact metrizable space, a subsequence of `x ↦ ψ(gₙ x)` converges almost
everywhere to `x ↦ ψ(g₀ x)`. -/
theorem exists_subseq_ae_tendsto {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {ψ : OnePoint ℝ → Y} (hψ : Measurable ψ) {g : ℕ → SL(2, ℝ)} {g₀ : SL(2, ℝ)}
    (hg : Tendsto g atTop (𝓝 g₀)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂bdry, Tendsto (fun i ↦ ψ (g (ns i) • x)) atTop (𝓝 (ψ (g₀ • x))) := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 (isCompact_univ (X := Y)).isBounded
  have hTM : TendstoInMeasure cauchy (fun n x ↦ ψ (g n • x)) atTop (fun x ↦ ψ (g₀ • x)) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεt ↦ ?_
    set e := ε.toReal
    have he : 0 < e := ENNReal.toReal_pos hε.ne' hεt
    obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := Y))
      (show 0 < e / 4 by positivity)
    set T := htf.toFinset
    -- each coordinate `dist · y` converges in `L¹`
    have hF : ∀ y : Y, Tendsto (fun n ↦ ∫⁻ x, ‖dist (ψ (g n • x)) y - dist (ψ (g₀ • x)) y‖ₑ
        ∂cauchy) atTop (𝓝 0) := by
      intro y
      refine tendsto_lintegral_comp_smul (F := fun z ↦ dist (ψ z) y) (B := D)
        ((continuous_id.dist continuous_const).measurable.comp hψ) (fun z ↦ ?_) hg
      rw [abs_of_nonneg dist_nonneg]; exact hD (mem_univ _) (mem_univ _)
    have hsub : ∀ n, {x | ε ≤ edist (ψ (g n • x)) (ψ (g₀ • x))} ⊆
        ⋃ y ∈ T, {x | ENNReal.ofReal (e / 2) ≤
          ‖dist (ψ (g n • x)) y - dist (ψ (g₀ • x)) y‖ₑ} := by
      intro n x hx
      simp only [mem_setOf_eq, edist_dist] at hx
      have hx' : e ≤ dist (ψ (g n • x)) (ψ (g₀ • x)) := by
        rw [← ENNReal.ofReal_toReal hεt] at hx
        exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1 hx
      obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hcov (mem_univ (ψ (g n • x))))
      refine mem_iUnion₂.2 ⟨y, htf.mem_toFinset.2 hyt, ?_⟩
      simp only [mem_setOf_eq]
      rw [← ofReal_norm, Real.norm_eq_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Metric.mem_ball] at hy
      have := dist_triangle_right (ψ (g n • x)) (ψ (g₀ • x)) y
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      linarith
    have hbound : ∀ n, cauchy {x | ε ≤ edist (ψ (g n • x)) (ψ (g₀ • x))} ≤
        ∑ y ∈ T, (∫⁻ x, ‖dist (ψ (g n • x)) y - dist (ψ (g₀ • x)) y‖ₑ ∂cauchy) /
          ENNReal.ofReal (e / 2) := by
      intro n
      refine (measure_mono (hsub n)).trans ((measure_biUnion_finset_le _ _).trans ?_)
      refine Finset.sum_le_sum fun y _ ↦ ?_
      refine meas_ge_le_lintegral_div ?_ (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) ENNReal.ofReal_ne_top
      exact ((((continuous_id.dist continuous_const).measurable.comp hψ).comp
        (measurable_smul_bdry _)).sub (((continuous_id.dist continuous_const).measurable.comp
          hψ).comp (measurable_smul_bdry _))).enorm.aemeasurable
    have hlim : Tendsto (fun n ↦ ∑ y ∈ T, (∫⁻ x, ‖dist (ψ (g n • x)) y -
        dist (ψ (g₀ • x)) y‖ₑ ∂cauchy) / ENNReal.ofReal (e / 2)) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ∑ y ∈ T, 0 / ENNReal.ofReal (e / 2) by simp]
      refine tendsto_finsetSum _ fun y _ ↦ ?_
      exact ENNReal.Tendsto.div_const (hF y) (Or.inr (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ bot_le) hbound
  obtain ⟨ns, hns, hae⟩ := hTM.exists_seq_tendsto_ae
  exact ⟨ns, hns, bdry_absolutelyContinuous_cauchy.ae_le hae⟩

end OrbicurveCores.M2
