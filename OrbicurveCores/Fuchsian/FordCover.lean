/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fuchsian.Covolume

/-!
# A Ford-type covering criterion for finite covolume

`OrbicurveCores.Fuchsian.hasFiniteCovolume_of_cover`: if `Γ ≤ SL(2, ℝ)` contains a translation
`z ↦ z + w` (`w > 0`) and finitely many elements `gᵢ` whose open isometric discs
`{|cᵢ z + dᵢ| < 1}` cover a period `[a, a + w]` of the real axis, then `Γ` has finite covolume.

Proof: shrink the discs slightly (compactness of `[a, a + w]`), which gives `ρ < 1` and `η > 0`
such that every point of the strip below height `η` lies in some `{|cᵢ z + dᵢ| < ρ}`. The
reduction "translate into the strip; if below height `η`, apply `gᵢ`" multiplies the imaginary
part by at least `ρ⁻²` at each step, so it ends in the strip above height `η`, which has finite
area `w / η`. Discreteness of `Γ` is not needed.
-/

open MeasureTheory Matrix UpperHalfPlane Set Topology Filter
open scoped MatrixGroups ENNReal NNReal

namespace OrbicurveCores.Fuchsian

/-- The strip `a ≤ Re z ≤ b`, `Im z ≥ η > 0`, has finite hyperbolic area. -/
lemma volume_strip_lt_top (a b η : ℝ) (hη : 0 < η) :
    volume {z : ℍ | z.re ∈ Icc a b ∧ η ≤ z.im} < ∞ := by
  rw [volume_eq_lintegral]
  set f : ℂ → ℝ≥0∞ := fun z ↦ (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)
  set T : Set ℂ := Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Ici η)
  have hsub : ((↑) '' {z : ℍ | z.re ∈ Icc a b ∧ η ≤ z.im} : Set ℂ) ⊆ T := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [T, Complex.measurableEquivRealProd] using hz
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' T = Icc a b ×ˢ Ici η := by
    ext p; simp [T]
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hg : Measurable fun y : ℝ ↦ (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by fun_prop
  have hfeq : ∀ p : ℝ × ℝ, (Complex.measurableEquivRealProd.symm p).im = p.2 := by
    intro p; simp [Complex.measurableEquivRealProd]
  simp_rw [hfeq]
  rw [lintegral_prod (fun p : ℝ × ℝ ↦ (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
    (hg.comp measurable_snd).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  have hint := (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hη).2
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  refine lt_of_le_of_lt (le_of_eq ?_) hint
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy0 : 0 < y := lt_trans hη hy
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _), ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.rpow_neg hy0.le, Real.rpow_two, Real.norm_of_nonneg hy0.le]
  ring


/-- The imaginary part after acting by an element of `SL(2, ℝ)`. -/
lemma im_smul_SL (g : SL(2, ℝ)) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (g 1 0 * (z : ℂ) + g 1 1) := by
  change ((SpecialLinearGroup.mapGL ℝ g) • z).im = _
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp [denom]

/-- **Ford-type covering criterion**, explicit form: every orbit meets the strip
`a ≤ Re z ≤ a + w`, `Im z ≥ η` for some `η > 0`. -/
theorem exists_strip_cover_of_cover {Γ : Subgroup SL(2, ℝ)} {w a : ℝ} (hw : 0 < w)
    {τ : SL(2, ℝ)} (hτ : τ ∈ Γ) (hτz : ∀ z : ℍ, ((τ • z : ℍ) : ℂ) = z + w)
    {ι : Type*} [Finite ι] (g : ι → SL(2, ℝ)) (hg : ∀ i, g i ∈ Γ)
    (hcov : ∀ t ∈ Icc a (a + w), ∃ i, |g i 1 0 * t + g i 1 1| < 1) :
    ∃ η > 0, ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ {z : ℍ | z.re ∈ Icc a (a + w) ∧ η ≤ z.im} := by
  obtain ⟨i₀, -⟩ := hcov a ⟨le_rfl, by linarith⟩
  haveI := Fintype.ofFinite ι
  haveI : Nonempty ι := ⟨i₀⟩
  -- the minimum over the discs
  set φ : ℝ → ℝ := fun t ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ |g i 1 0 * t + g i 1 1|
  have hφc : Continuous φ := by
    refine Continuous.finset_inf'_apply _ fun i _ ↦ ?_
    fun_prop
  have hφlt : ∀ t ∈ Icc a (a + w), φ t < 1 := by
    intro t ht
    obtain ⟨i, hi⟩ := hcov t ht
    exact lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ i)) hi
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := a) (b := a + w)).exists_isMaxOn
    (nonempty_Icc.mpr (by linarith))
    hφc.continuousOn
  set ρ₀ := φ t₀
  have hρ₀ : ρ₀ < 1 := hφlt t₀ ht₀
  have hρ₀0 : 0 ≤ ρ₀ := Finset.le_inf' Finset.univ_nonempty _ fun i _ ↦ abs_nonneg _
  set ρ := (1 + ρ₀) / 2
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  have hρ0 : 0 < ρ := by simp only [ρ]; linarith
  set C := 1 + ∑ i, |g i 1 0|
  have hC : 0 < C := by positivity
  have hCi : ∀ i, |g i 1 0| ≤ C := fun i ↦ by
    have := Finset.single_le_sum (f := fun i ↦ |g i 1 0|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    simp only [C]; linarith
  set η := (ρ - ρ₀) / C
  have hη : 0 < η := div_pos (by simp only [ρ]; linarith) hC
  -- below height `η`, some shrunken disc applies
  have hlow : ∀ z : ℍ, z.re ∈ Icc a (a + w) → z.im < η →
      ∃ i, Complex.normSq (g i 1 0 * (z : ℂ) + g i 1 1) < ρ ^ 2 := by
    intro z hz hzi
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      fun i ↦ |g i 1 0 * z.re + g i 1 1|
    refine ⟨i, ?_⟩
    have hle : |g i 1 0 * z.re + g i 1 1| ≤ ρ₀ := by
      have := hmax hz
      simp only [Set.mem_setOf_eq] at this
      rw [← hi]; exact this
    have habs : ‖(g i 1 0 * (z : ℂ) + g i 1 1)‖ ≤ |g i 1 0 * z.re + g i 1 1| +
        |g i 1 0| * z.im := by
      have e : (g i 1 0 * (z : ℂ) + g i 1 1) = ((g i 1 0 * z.re + g i 1 1 : ℝ) : ℂ) +
          ((g i 1 0 * z.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [e]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos z.im_pos]
    have hlt : ‖(g i 1 0 * (z : ℂ) + g i 1 1)‖ < ρ := by
      have h1 : |g i 1 0| * z.im ≤ C * z.im := mul_le_mul_of_nonneg_right (hCi i) z.im_pos.le
      have h2 : C * z.im < C * η := mul_lt_mul_of_pos_left hzi hC
      have h3 : C * η = ρ - ρ₀ := by simp only [η]; field_simp
      linarith
    rw [Complex.normSq_eq_norm_sq]
    exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
  -- translation into the strip
  have hτk : ∀ (k : ℤ) (z : ℍ), (((τ ^ k) • z : ℍ) : ℂ) = z + k * w := by
    intro k
    induction k using Int.induction_on with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [_root_.zpow_add_one, mul_smul, ih, hτz]; push_cast; ring
    | pred n ih =>
      intro z
      have h := hτz ((τ ^ (-(n : ℤ) - 1)) • z)
      rw [← mul_smul, ← _root_.zpow_one_add,
        show (1 : ℤ) + (-(n : ℤ) - 1) = -(n : ℤ) by ring, ih] at h
      push_cast at h ⊢
      linear_combination -h
  have htrans : ∀ z : ℍ, ∃ k : ℤ, ((τ ^ k) • z).re ∈ Icc a (a + w) ∧
      ((τ ^ k) • z).im = z.im := by
    intro z
    refine ⟨⌈(a - z.re) / w⌉, ?_, ?_⟩
    · have hre : ((τ ^ ⌈(a - z.re) / w⌉) • z).re = z.re + ⌈(a - z.re) / w⌉ * w := by
        have := congrArg Complex.re (hτk ⌈(a - z.re) / w⌉ z)
        simpa using this
      rw [hre]
      have h1 := Int.le_ceil ((a - z.re) / w)
      have h2 := Int.ceil_lt_add_one ((a - z.re) / w)
      rw [div_le_iff₀ hw] at h1
      have h2' : (⌈(a - z.re) / w⌉ : ℝ) * w < ((a - z.re) / w + 1) * w :=
        mul_lt_mul_of_pos_right h2 hw
      rw [add_mul, div_mul_cancel₀ _ hw.ne'] at h2'
      constructor <;> linarith
    · have := congrArg Complex.im (hτk ⌈(a - z.re) / w⌉ z)
      simpa using this
  -- the covering set
  refine ⟨η, hη, ?_⟩
  -- the reduction
  have hP : ∀ n : ℕ, ∀ z : ℍ, η * ρ ^ (2 * n) ≤ z.im →
      ∃ γ ∈ Γ, γ • z ∈ {z : ℍ | z.re ∈ Icc a (a + w) ∧ η ≤ z.im} := by
    intro n
    induction n with
    | zero =>
      intro z hz
      obtain ⟨k, hk1, hk2⟩ := htrans z
      exact ⟨τ ^ k, zpow_mem hτ k, hk1, by rw [hk2]; simpa using hz⟩
    | succ n ih =>
      intro z hz
      obtain ⟨k, hk1, hk2⟩ := htrans z
      set z' := (τ ^ k) • z
      by_cases hhigh : η ≤ z'.im
      · exact ⟨τ ^ k, zpow_mem hτ k, hk1, hhigh⟩
      push Not at hhigh
      obtain ⟨i, hi⟩ := hlow z' hk1 hhigh
      have hpos : 0 < Complex.normSq (g i 1 0 * (z' : ℂ) + g i 1 1) := by
        have := (g i • z').im_pos
        rw [im_smul_SL] at this
        exact (div_pos_iff.mp this).elim (fun h ↦ h.2) fun h ↦ absurd z'.im_pos (not_lt.mpr h.1.le)
      have him : η * ρ ^ (2 * n) ≤ (g i • z').im := by
        rw [im_smul_SL, le_div_iff₀ hpos]
        have h1 : η * ρ ^ (2 * (n + 1)) ≤ z'.im := by rw [hk2]; exact hz
        have h2 : η * ρ ^ (2 * n) * Complex.normSq (g i 1 0 * (z' : ℂ) + g i 1 1) ≤
            η * ρ ^ (2 * n) * ρ ^ 2 :=
          mul_le_mul_of_nonneg_left hi.le (by positivity)
        calc η * ρ ^ (2 * n) * Complex.normSq (g i 1 0 * (z' : ℂ) + g i 1 1)
            ≤ η * ρ ^ (2 * n) * ρ ^ 2 := h2
          _ = η * ρ ^ (2 * (n + 1)) := by ring
          _ ≤ z'.im := h1
      obtain ⟨γ, hγ, hγz⟩ := ih _ him
      exact ⟨γ * g i * τ ^ k, mul_mem (mul_mem hγ (hg i)) (zpow_mem hτ k), by
        rw [mul_smul, mul_smul]; exact hγz⟩
  intro z
  have hlim : Tendsto (fun n : ℕ ↦ η * ρ ^ (2 * n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ (ρ ^ 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by nlinarith)
    simpa [pow_mul] using this.const_mul η
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds z.im_pos)).exists
  exact hP n z hn.le

/-- **Ford-type covering criterion.** -/
theorem hasFiniteCovolume_of_cover {Γ : Subgroup SL(2, ℝ)} {w a : ℝ} (hw : 0 < w)
    {τ : SL(2, ℝ)} (hτ : τ ∈ Γ) (hτz : ∀ z : ℍ, ((τ • z : ℍ) : ℂ) = z + w)
    {ι : Type*} [Finite ι] (g : ι → SL(2, ℝ)) (hg : ∀ i, g i ∈ Γ)
    (hcov : ∀ t ∈ Icc a (a + w), ∃ i, |g i 1 0 * t + g i 1 1| < 1) :
    HasFiniteCovolume Γ := by
  obtain ⟨η, hη, h⟩ := exists_strip_cover_of_cover hw hτ hτz g hg hcov
  refine ⟨{z : ℍ | z.re ∈ Icc a (a + w) ∧ η ≤ z.im}, ?_, volume_strip_lt_top _ _ _ hη, h⟩
  exact (measurableSet_Icc.preimage continuous_re.measurable).inter
    (measurableSet_Ici.preimage continuous_im.measurable)

end OrbicurveCores.Fuchsian
