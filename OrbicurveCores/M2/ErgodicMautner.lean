/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.HopfContinuity
import OrbicurveCores.M2.HopfFinite

/-!
# The Mautner phenomenon on `Γ \ SL(2, ℝ)`

Let `Γ` be countable with a measurable fundamental set `F ⊆ ℍ` of finite area and finite
multiplicity. Then

* `pou Γ F g = 1_F(g i) / #{γ ∈ Γ | γ g i ∈ F}` is a `Γ`-partition of unity on `SL(2, ℝ)`
  (`tsum_pou`) of finite total mass (`lintegral_pou_lt_top`);
* the weighted `L¹`-norm `∫ pou · |Ψ|` of a `Γ`-invariant `Ψ` is invariant under right
  translations preserving `hopfMeasure` (`lintegral_pou_mul_right`, "unfolding");
* **Mautner** (`ae_mul_unip_eq`): a bounded measurable `Φ` that is left `Γ`-invariant and right
  `A`-invariant is right `N`-invariant almost everywhere.
-/

open MeasureTheory Set Filter Topology Real UpperHalfPlane
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

variable (Γ : Subgroup SL(2, ℝ)) (F : Set ℍ)

/-- The multiplicity of `F` along the orbit of `z`. -/
noncomputable def mult (z : ℍ) : ℝ≥0∞ := ∑' γ : Γ, F.indicator 1 ((γ : SL(2, ℝ)) • z)

/-- The partition of unity. -/
noncomputable def pou (g : SL(2, ℝ)) : ℝ≥0∞ := F.indicator 1 (g • I) * (mult Γ F (g • I))⁻¹

variable {Γ F}

lemma mult_smul {δ : SL(2, ℝ)} (hδ : δ ∈ Γ) (z : ℍ) : mult Γ F (δ • z) = mult Γ F z := by
  simp only [mult, ← mul_smul]
  exact (Equiv.mulRight (⟨δ, hδ⟩ : Γ)).tsum_eq fun γ : Γ ↦ F.indicator 1 ((γ : SL(2, ℝ)) • z)

lemma one_le_mult (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F) (z : ℍ) : 1 ≤ mult Γ F z := by
  obtain ⟨γ, hγ, hγz⟩ := hcov z
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : Γ))
  rw [Set.indicator_of_mem hγz]; rfl

lemma mult_ne_top (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite) (z : ℍ) :
    mult Γ F z ≠ ⊤ := by
  classical
  have hS : {γ : Γ | (γ : SL(2, ℝ)) • z ∈ F}.Finite :=
    (hfin z).preimage (Subtype.val_injective.injOn) |>.subset fun γ hγ ↦ ⟨γ.2, hγ⟩
  rw [mult, tsum_eq_sum (s := hS.toFinset) fun γ hγ ↦ by
    rw [Set.Finite.mem_toFinset] at hγ
    exact Set.indicator_of_notMem (show (γ : SL(2, ℝ)) • z ∉ F from hγ) _]
  exact ENNReal.sum_ne_top.mpr fun γ _ ↦ by
    unfold Set.indicator; split_ifs <;> simp

lemma measurable_basept : Measurable fun g : SL(2, ℝ) ↦ g • I :=
  (continuous_id.smul continuous_const).measurable

lemma measurable_mult [Countable Γ] (hF : MeasurableSet F) : Measurable (mult Γ F) :=
  Measurable.tsum fun γ ↦ (measurable_one.indicator hF).comp
    (continuous_const_smul (γ : SL(2, ℝ))).measurable

lemma measurable_pou [Countable Γ] (hF : MeasurableSet F) : Measurable (pou Γ F) :=
  ((measurable_one.indicator hF).comp measurable_basept).mul
    ((measurable_mult hF).comp measurable_basept).inv

variable (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F)
  (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite)

include hcov in
lemma pou_le_one (g : SL(2, ℝ)) : pou Γ F g ≤ 1 := by
  have h1 : F.indicator (1 : ℍ → ℝ≥0∞) (g • I) ≤ 1 := by
    unfold Set.indicator; split_ifs <;> simp
  calc pou Γ F g ≤ 1 * (mult Γ F (g • I))⁻¹ := mul_le_mul_left h1 _
    _ = (mult Γ F (g • I))⁻¹ := one_mul _
    _ ≤ 1 := ENNReal.inv_le_one.mpr (one_le_mult hcov _)

include hcov in
lemma pou_ne_top (g : SL(2, ℝ)) : pou Γ F g ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (pou_le_one hcov g)

include hcov hfin in
/-- **The partition of unity.** -/
theorem tsum_pou (g : SL(2, ℝ)) : ∑' γ : Γ, pou Γ F ((γ : SL(2, ℝ)) * g) = 1 := by
  simp only [pou, mul_smul, mult_smul (Subtype.prop _)]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_inv_cancel (one_pos.trans_le (one_le_mult hcov _)).ne'
    (mult_ne_top hfin _)

include hcov hfin in
lemma tsum_pou_inv (g : SL(2, ℝ)) : ∑' γ : Γ, pou Γ F ((γ : SL(2, ℝ))⁻¹ * g) = 1 := by
  rw [← tsum_pou hcov hfin g]
  exact (Equiv.inv Γ).tsum_eq fun γ : Γ ↦ pou Γ F ((γ : SL(2, ℝ)) * g)

include hcov in
lemma lintegral_pou_lt_top [Countable Γ] (hF : MeasurableSet F) (hvol : volume F < ⊤) :
    ∫⁻ g, pou Γ F g ∂hopfMeasure < ⊤ := by
  have hS := measurableSet_basept hF
  calc ∫⁻ g, pou Γ F g ∂hopfMeasure
      ≤ ∫⁻ g, {g : SL(2, ℝ) | g • I ∈ F}.indicator 1 g ∂hopfMeasure := by
        refine lintegral_mono fun g ↦ ?_
        by_cases hg : g ∈ {g : SL(2, ℝ) | g • I ∈ F}
        · rw [Set.indicator_of_mem hg]; exact pou_le_one hcov g
        · rw [Set.indicator_of_notMem hg, pou,
            Set.indicator_of_notMem (show g • I ∉ F from hg), zero_mul]
    _ = ENNReal.ofReal π * volume F := by
        rw [lintegral_indicator_one hS, hopfMeasure_basept hF]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol

include hcov hfin in
/-- **Unfolding**: the weighted `L¹`-norm of a `Γ`-invariant function is invariant under right
translations preserving `hopfMeasure`. -/
theorem lintegral_pou_mul_right [Countable Γ] (hF : MeasurableSet F) {Ψ : SL(2, ℝ) → ℝ≥0∞}
    (hΨ : Measurable Ψ) (hinv : ∀ γ ∈ Γ, ∀ g, Ψ (γ * g) = Ψ g) {h : SL(2, ℝ)}
    (hR : ∀ G : SL(2, ℝ) → ℝ≥0∞, Measurable G →
      ∫⁻ g, G (g * h) ∂hopfMeasure = ∫⁻ g, G g ∂hopfMeasure) :
    ∫⁻ g, pou Γ F g * Ψ (g * h) ∂hopfMeasure = ∫⁻ g, pou Γ F g * Ψ g ∂hopfMeasure := by
  have hχ : Measurable (pou Γ F) := measurable_pou hF
  calc ∫⁻ g, pou Γ F g * Ψ (g * h) ∂hopfMeasure
      = ∫⁻ g, pou Γ F (g * h⁻¹) * Ψ g ∂hopfMeasure := by
        rw [← hR (fun g ↦ pou Γ F (g * h⁻¹) * Ψ g) (by fun_prop)]
        simp only [mul_inv_cancel_right]
    _ = ∫⁻ g, ∑' γ : Γ, pou Γ F (g * h⁻¹) * Ψ g * pou Γ F ((γ : SL(2, ℝ)) * g)
          ∂hopfMeasure := by
        refine lintegral_congr fun g ↦ ?_
        rw [ENNReal.tsum_mul_left, tsum_pou hcov hfin, mul_one]
    _ = ∑' γ : Γ, ∫⁻ g, pou Γ F (g * h⁻¹) * Ψ g * pou Γ F ((γ : SL(2, ℝ)) * g)
          ∂hopfMeasure :=
        lintegral_tsum fun γ ↦ by fun_prop
    _ = ∑' γ : Γ, ∫⁻ g, pou Γ F ((γ : SL(2, ℝ))⁻¹ * (g * h⁻¹)) * Ψ g * pou Γ F g
          ∂hopfMeasure := by
        refine tsum_congr fun γ ↦ ?_
        refine Eq.trans ?_ (lintegral_hopfMeasure_mul_left (γ : SL(2, ℝ))
          (F := fun g ↦ pou Γ F ((γ : SL(2, ℝ))⁻¹ * (g * h⁻¹)) * Ψ g * pou Γ F g)
          (by fun_prop))
        refine lintegral_congr fun g ↦ ?_
        simp only [hinv _ γ.2, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = ∫⁻ g, ∑' γ : Γ, pou Γ F ((γ : SL(2, ℝ))⁻¹ * (g * h⁻¹)) * (Ψ g * pou Γ F g)
          ∂hopfMeasure := by
        rw [lintegral_tsum fun γ ↦ by fun_prop]
        simp only [mul_assoc]
    _ = ∫⁻ g, pou Γ F g * Ψ g ∂hopfMeasure := by
        refine lintegral_congr fun g ↦ ?_
        rw [ENNReal.tsum_mul_right, tsum_pou_inv hcov hfin, one_mul, mul_comm]

include hcov hfin in
/-- A `Γ`-invariant function is recovered from the partition of unity. -/
lemma hasSum_pou_mul {Φ : SL(2, ℝ) → ℝ} (hinv : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g)
    (g : SL(2, ℝ)) :
    HasSum (fun γ : Γ ↦ (pou Γ F ((γ : SL(2, ℝ)) * g)).toReal * Φ ((γ : SL(2, ℝ)) * g))
      (Φ g) := by
  have h1 : HasSum (fun γ : Γ ↦ (pou Γ F ((γ : SL(2, ℝ)) * g)).toReal) 1 := by
    have hs := ENNReal.summable_toReal (f := fun γ : Γ ↦ pou Γ F ((γ : SL(2, ℝ)) * g))
      (by rw [tsum_pou hcov hfin]; exact ENNReal.one_ne_top)
    convert hs.hasSum using 1
    rw [← ENNReal.tsum_toReal_eq fun _ ↦ pou_ne_top hcov _, tsum_pou hcov hfin,
      ENNReal.toReal_one]
  simpa only [hinv _ (Subtype.prop _), one_mul] using h1.mul_right (Φ g)

include hcov hfin in
/-- **The Mautner phenomenon.** A bounded measurable function on `SL(2, ℝ)` which is left
`Γ`-invariant and right `A`-invariant is right `N`-invariant almost everywhere. -/
theorem ae_mul_unip_eq [Countable Γ] (hF : MeasurableSet F) (hvol : volume F < ⊤)
    {Φ : SL(2, ℝ) → ℝ} (hΦm : Measurable Φ) (hΦb : ∀ g, |Φ g| ≤ 1)
    (hinv : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hA : ∀ σ g, Φ (g * diagA σ) = Φ g) (t : ℝ) :
    ∀ᵐ g ∂hopfMeasure, Φ (g * unip t) = Φ g := by
  set χ := pou Γ F with hχdef
  have hχ : Measurable χ := measurable_pou hF
  set Ψ : ℝ → SL(2, ℝ) → ℝ≥0∞ := fun τ g ↦ ‖Φ (g * unip τ) - Φ g‖ₑ with hΨdef
  have hΨm : ∀ τ, Measurable (Ψ τ) := fun τ ↦ by simp only [Ψ]; fun_prop
  have hΨinv : ∀ τ, ∀ γ ∈ Γ, ∀ g, Ψ τ (γ * g) = Ψ τ g := by
    intro τ γ hγ g
    simp only [Ψ, mul_assoc, hinv γ hγ]
  set D : ℝ → ℝ≥0∞ := fun τ ↦ ∫⁻ g, χ g * Ψ τ g ∂hopfMeasure with hDdef
  -- `D` is invariant under the scaling `τ ↦ e^{2σ} τ`
  have hscale : ∀ σ τ, D (exp (2 * σ) * τ) = D τ := by
    intro σ τ
    have h := lintegral_pou_mul_right hcov hfin hF (hΨm τ) (hΨinv τ) (h := diagA σ)
      (fun G hG ↦ lintegral_hopfMeasure_mul_diagA σ hG)
    rw [← hχdef] at h
    simp only [D]
    rw [← h]
    refine lintegral_congr fun g ↦ ?_
    congr 1
    simp only [Ψ]
    rw [mul_assoc g (diagA σ) (unip τ), diagA_mul_unip, ← mul_assoc, hA, hA]
  -- `D` is dominated by the `L¹` modulus of continuity of `ψ = χ Φ`
  set ψ : SL(2, ℝ) → ℝ := fun g ↦ (χ g).toReal * Φ g with hψdef
  have hψm : Measurable ψ := by simp only [ψ]; fun_prop
  have hψfin : ∫⁻ g, ‖ψ g‖ₑ ∂hopfMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top (lintegral_pou_lt_top hcov hF hvol).ne (lintegral_mono fun g ↦ ?_)
    simp only [ψ, enorm_mul]
    calc ‖(χ g).toReal‖ₑ * ‖Φ g‖ₑ ≤ ‖(χ g).toReal‖ₑ * 1 := by
          gcongr
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_one.mpr (hΦb g)
      _ = χ g := by
          rw [mul_one, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (pou_ne_top hcov g)]
  have hle : ∀ τ, D τ ≤ ∫⁻ g, ‖ψ (g * unip τ) - ψ g‖ₑ ∂hopfMeasure := by
    intro τ
    set Δ : SL(2, ℝ) → ℝ≥0∞ := fun g ↦ ‖ψ (g * unip τ) - ψ g‖ₑ with hΔdef
    have hΔm : Measurable Δ := by simp only [Δ]; fun_prop
    have hpt : ∀ g, Ψ τ g ≤ ∑' γ : Γ, Δ ((γ : SL(2, ℝ)) * g) := by
      intro g
      have hs := (hasSum_pou_mul hcov hfin hinv (g * unip τ)).sub
        (hasSum_pou_mul hcov hfin hinv g)
      simp only [Ψ, ← hs.tsum_eq]
      refine le_trans enorm_tsum_le_tsum_enorm (le_of_eq (tsum_congr fun γ ↦ ?_))
      simp only [Δ, ψ, hχdef, mul_assoc]
    calc D τ ≤ ∫⁻ g, χ g * ∑' γ : Γ, Δ ((γ : SL(2, ℝ)) * g) ∂hopfMeasure :=
          lintegral_mono fun g ↦ by gcongr; exact hpt g
      _ = ∑' γ : Γ, ∫⁻ g, χ g * Δ ((γ : SL(2, ℝ)) * g) ∂hopfMeasure := by
          simp_rw [← ENNReal.tsum_mul_left]
          exact lintegral_tsum fun γ ↦ by fun_prop
      _ = ∑' γ : Γ, ∫⁻ g, χ ((γ : SL(2, ℝ))⁻¹ * g) * Δ g ∂hopfMeasure := by
          refine tsum_congr fun γ ↦ ?_
          refine Eq.trans ?_ (lintegral_hopfMeasure_mul_left (γ : SL(2, ℝ))
            (F := fun g ↦ χ ((γ : SL(2, ℝ))⁻¹ * g) * Δ g) (by fun_prop))
          refine lintegral_congr fun g ↦ ?_
          simp only [inv_mul_cancel_left]
      _ = ∫⁻ g, Δ g ∂hopfMeasure := by
          rw [← lintegral_tsum fun γ ↦ by fun_prop]
          refine lintegral_congr fun g ↦ ?_
          rw [ENNReal.tsum_mul_right, tsum_pou_inv hcov hfin, one_mul]
  -- hence `D → 0` at `0`, and by scaling `D t = 0`
  have hlim : Tendsto D (𝓝 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_lintegral_hopfMeasure_unip hψm hψfin) (fun _ ↦ bot_le) hle
  have hD0 : D t = 0 := by
    have hexp : Tendsto (fun σ : ℝ ↦ exp (2 * σ) * t) atBot (𝓝 0) := by
      have := (tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot two_pos)).mul_const t
      simpa using this
    have h1 := hlim.comp hexp
    simp only [Function.comp_def, hscale] at h1
    exact tendsto_nhds_unique tendsto_const_nhds h1
  -- the exceptional set is null
  have hZ₀ : hopfMeasure {g | χ g * Ψ t g ≠ 0} = 0 := by
    rw [← ae_iff]
    exact (lintegral_eq_zero_iff (hχ.mul (hΨm t))).mp hD0
  have hZ₀m : MeasurableSet {g | χ g * Ψ t g ≠ 0} :=
    (measurableSet_eq_fun (hχ.mul (hΨm t)) measurable_const).compl
  have hsub : {g | Ψ t g ≠ 0} ⊆
      ⋃ γ : Γ, (fun g ↦ (γ : SL(2, ℝ)) * g) ⁻¹' {g | χ g * Ψ t g ≠ 0} := by
    intro g hg
    have hne : ∃ γ : Γ, χ ((γ : SL(2, ℝ)) * g) ≠ 0 := by
      by_contra hall
      push Not at hall
      have := tsum_pou hcov hfin (Γ := Γ) (F := F) g
      simp only [← hχdef, hall, tsum_zero] at this
      exact zero_ne_one this
    obtain ⟨γ, hγ⟩ := hne
    refine Set.mem_iUnion.mpr ⟨γ, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hΨinv t _ γ.2]
    exact mul_ne_zero hγ hg
  have hZ : hopfMeasure {g | Ψ t g ≠ 0} = 0 := by
    refine measure_mono_null hsub (measure_iUnion_null fun γ ↦ ?_)
    calc hopfMeasure ((fun g ↦ (γ : SL(2, ℝ)) * g) ⁻¹' {g | χ g * Ψ t g ≠ 0})
        = ∫⁻ g, {g | χ g * Ψ t g ≠ 0}.indicator 1 ((γ : SL(2, ℝ)) * g) ∂hopfMeasure := by
          rw [← lintegral_indicator_one (hZ₀m.preimage (measurable_mul_left_SL _))]
          rfl
      _ = ∫⁻ g, {g | χ g * Ψ t g ≠ 0}.indicator 1 g ∂hopfMeasure :=
          lintegral_hopfMeasure_mul_left _ (measurable_one.indicator hZ₀m)
      _ = 0 := by rw [lintegral_indicator_one hZ₀m, hZ₀]
  rw [ae_iff]
  refine measure_mono_null (fun g hg ↦ ?_) hZ
  simp only [Set.mem_setOf_eq] at hg ⊢
  simp only [Ψ]
  exact enorm_ne_zero.mpr (sub_ne_zero.mpr hg)

end OrbicurveCores.M2
