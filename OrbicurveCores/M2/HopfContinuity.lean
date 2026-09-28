/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.HopfCoords

/-!
# Continuity of right translation by `N` in `L¹`

For `ψ ∈ L¹(SL(2, ℝ), hopfMeasure)`, `‖ψ(· n_t) - ψ‖₁ → 0` as `t → 0`
(`tendsto_lintegral_hopfMeasure_unip`). In Hopf coordinates `n_t` is the shear
`(x, u, s) ↦ (x, u + e²ˢ t, s)`; we approximate by continuous compactly supported functions
and use dominated convergence.
-/

open MeasureTheory Matrix Set Filter Topology Real
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

lemma hopfN_hopfN (t t' : ℝ) (p : ℝ × ℝ × ℝ) : hopfN t (hopfN t' p) = hopfN (t' + t) p := by
  simp only [hopfN]; ext <;> simp; ring

lemma hopfN_zero (p : ℝ × ℝ × ℝ) : hopfN 0 p = p := by simp [hopfN]

/-- The shear as a measurable equivalence. -/
noncomputable def hopfNEquiv (t : ℝ) : (ℝ × ℝ × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) where
  toFun := hopfN t
  invFun := hopfN (-t)
  left_inv p := by rw [hopfN_hopfN, add_neg_cancel, hopfN_zero]
  right_inv p := by rw [hopfN_hopfN, neg_add_cancel, hopfN_zero]
  measurable_toFun := measurable_hopfN t
  measurable_invFun := measurable_hopfN (-t)

lemma continuous_hopfN_uncurry : Continuous fun q : ℝ × (ℝ × ℝ × ℝ) ↦ hopfN q.1 q.2 := by
  unfold hopfN; fun_prop

lemma continuous_hopfN (t : ℝ) : Continuous (hopfN t) :=
  continuous_hopfN_uncurry.comp (continuous_const.prodMk continuous_id)

/-- Dominated convergence for continuous compactly supported functions. -/
lemma tendsto_lintegral_hopfN_of_continuous {g : ℝ × ℝ × ℝ → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    Tendsto (fun t ↦ ∫⁻ p, ‖g (hopfN t p) - g p‖ₑ) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgs
  set K' : Set (ℝ × ℝ × ℝ) :=
    (fun q : ℝ × (ℝ × ℝ × ℝ) ↦ hopfN (-q.1) q.2) '' (Icc (-1) 1 ×ˢ tsupport g) ∪ tsupport g
  have hK' : IsCompact K' := by
    refine IsCompact.union ?_ hgs
    refine (isCompact_Icc.prod hgs).image ?_
    exact continuous_hopfN_uncurry.comp (continuous_fst.neg.prodMk continuous_snd)
  have hbound : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ p, ‖g (hopfN t p) - g p‖ₑ ≤
      K'.indicator (fun _ ↦ 2 * ENNReal.ofReal C) p := by
    intro t ht p
    by_cases hp : p ∈ K'
    · rw [Set.indicator_of_mem hp]
      refine (enorm_sub_le).trans ?_
      rw [two_mul]
      refine add_le_add ?_ ?_ <;> rw [← ofReal_norm] <;> exact ENNReal.ofReal_le_ofReal (hC _)
    · rw [Set.indicator_of_notMem hp]
      have h1 : p ∉ tsupport g := fun h ↦ hp (Or.inr h)
      have h2 : hopfN t p ∉ tsupport g := fun h ↦ hp (Or.inl ⟨(t, hopfN t p), ⟨ht, h⟩, by
        simp only; rw [hopfN_hopfN, add_neg_cancel, hopfN_zero]⟩)
      rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
      simp
  have hlim := tendsto_lintegral_filter_of_dominated_convergence
    (μ := (volume : Measure (ℝ × ℝ × ℝ))) (l := 𝓝 (0 : ℝ))
    (F := fun t p ↦ ‖g (hopfN t p) - g p‖ₑ) (f := fun _ ↦ 0)
    (K'.indicator fun _ ↦ 2 * ENNReal.ofReal C)
    (Eventually.of_forall fun t ↦ ((hg.comp (continuous_hopfN t)).sub hg).enorm.measurable)
    (Filter.eventually_of_mem (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)) fun t ht ↦ Eventually.of_forall (hbound t ht))
    (by
      rw [lintegral_indicator_const hK'.measurableSet]
      exact ENNReal.mul_ne_top (by finiteness) hK'.measure_lt_top.ne)
    (Eventually.of_forall fun p ↦ by
      have hc : Continuous fun t : ℝ ↦ ‖g (hopfN t p) - g p‖ₑ := by
        refine (hg.comp ?_ |>.sub continuous_const).enorm
        exact continuous_hopfN_uncurry.comp (continuous_id.prodMk continuous_const)
      simpa [hopfN_zero] using hc.tendsto 0)
  simpa using hlim

/-- **Continuity of the shear in `L¹(ℝ³)`.** -/
theorem tendsto_lintegral_hopfN {φ : ℝ × ℝ × ℝ → ℝ} (hφ : Integrable φ) :
    Tendsto (fun t ↦ ∫⁻ p, ‖φ (hopfN t p) - φ p‖ₑ) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩
  obtain ⟨g, hgs, hφg, hgc, -⟩ := hφ.exists_hasCompactSupport_lintegral_sub_le hε3
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (tendsto_lintegral_hopfN_of_continuous hgc hgs)
    (ε / 3) (pos_iff_ne_zero.mpr hε3)] with t ht
  have hmp := measurePreserving_hopfN t
  have hemb : MeasurableEmbedding (hopfN t) := (hopfNEquiv t).measurableEmbedding
  have hNc : Continuous (hopfN t) := continuous_hopfN t
  have hA : AEMeasurable fun p ↦ ‖φ (hopfN t p) - g (hopfN t p)‖ₑ :=
    ((hφ.aestronglyMeasurable.comp_measurePreserving hmp).sub
      (hgc.comp hNc).aestronglyMeasurable).enorm
  have hC : AEMeasurable fun p ↦ ‖g p - φ p‖ₑ :=
    (hgc.aestronglyMeasurable.sub hφ.aestronglyMeasurable).enorm
  have hAeq : ∫⁻ p, ‖φ (hopfN t p) - g (hopfN t p)‖ₑ = ∫⁻ p, ‖φ p - g p‖ₑ :=
    hmp.lintegral_comp_emb hemb fun q ↦ ‖φ q - g q‖ₑ
  have hCeq : ∫⁻ p, ‖g p - φ p‖ₑ = ∫⁻ p, ‖φ p - g p‖ₑ := by
    simp_rw [enorm_sub_rev]
  calc ∫⁻ p, ‖φ (hopfN t p) - φ p‖ₑ
      ≤ ∫⁻ p, (‖φ (hopfN t p) - g (hopfN t p)‖ₑ + ‖g (hopfN t p) - g p‖ₑ +
          ‖g p - φ p‖ₑ) := by
        refine lintegral_mono fun p ↦ ?_
        simp only [← edist_eq_enorm_sub]
        exact edist_triangle4 _ _ _ _
    _ = (∫⁻ p, ‖φ (hopfN t p) - g (hopfN t p)‖ₑ) + (∫⁻ p, ‖g (hopfN t p) - g p‖ₑ) +
          ∫⁻ p, ‖g p - φ p‖ₑ := by
        rw [lintegral_add_right' _ hC, lintegral_add_left' hA]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [hAeq, hCeq]
        exact add_le_add (add_le_add hφg ht) hφg
    _ = ε := ENNReal.add_thirds ε

/-- **Continuity of right translation by `N` in `L¹(SL(2, ℝ))`.** -/
theorem tendsto_lintegral_hopfMeasure_unip {ψ : SL(2, ℝ) → ℝ} (hψm : Measurable ψ)
    (hψ : ∫⁻ g, ‖ψ g‖ₑ ∂hopfMeasure ≠ ∞) :
    Tendsto (fun t ↦ ∫⁻ g, ‖ψ (g * unip t) - ψ g‖ₑ ∂hopfMeasure) (𝓝 0) (𝓝 0) := by
  rw [lintegral_hopfMeasure (by fun_prop)] at hψ
  have h1 : Integrable fun p ↦ ψ (hopf p) := by
    refine ⟨(hψm.comp measurable_hopf).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (lintegral_mono fun p ↦ le_self_add) hψ.lt_top
  have h2 : Integrable fun p ↦ ψ (-hopf p) := by
    refine ⟨(hψm.comp measurable_neg_hopf).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (lintegral_mono fun p ↦ le_add_self) hψ.lt_top
  have key : ∀ t, ∫⁻ g, ‖ψ (g * unip t) - ψ g‖ₑ ∂hopfMeasure =
      (∫⁻ p, ‖ψ (hopf (hopfN t p)) - ψ (hopf p)‖ₑ) +
        ∫⁻ p, ‖ψ (-hopf (hopfN t p)) - ψ (-hopf p)‖ₑ := by
    intro t
    rw [lintegral_hopfMeasure (by fun_prop), lintegral_add_left (by fun_prop)]
    simp [hopf_mul_unip]
  simp_rw [key]
  simpa using (tendsto_lintegral_hopfN h1).add (tendsto_lintegral_hopfN h2)

end OrbicurveCores.M2
