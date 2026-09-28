/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.Setup
import OrbicurveCores.Fuchsian.OneInftyLattice
import OrbicurveCores.Fuchsian.PingPong

/-!
# Good lattices

* `GoodLattice.of_le`: a finite-index subgroup of a good lattice is a good lattice.
* `goodLattice_normal`: the Fricke normal form group is a good lattice.

Finite multiplicity of the explicit strip `-1 ≤ Re z ≤ 1`, `Im z ≥ η` comes from a height bound
(a weak form of Shimizu's lemma): if a discrete `Γ` contains a translation `z ↦ z + h`, `h ≠ 0`,
then the bottom rows `(c, d)` of elements of `Γ` stay away from `0` (otherwise the conjugates
`γ⁻¹ (z ↦ z + h) γ` accumulate at `1`), so the heights `Im (γ z)` along an orbit are bounded.
-/

open MeasureTheory Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set Topology Filter
open scoped MatrixGroups Pointwise

namespace OrbicurveCores.M2

open Fuchsian

/-- Discreteness passes to subgroups. -/
lemma discreteTopology_of_le {Γ Γ' : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] (hle : Γ' ≤ Γ) :
    DiscreteTopology Γ' := by
  obtain ⟨U, hU, h⟩ := exists_nhds_of_discrete Γ
  exact discreteTopology_of_nhds hU fun g hg hgU ↦ h g (hle hg) hgU

/-- **Finite-index subgroups of good lattices are good lattices.** -/
theorem GoodLattice.of_le {Γ Γ' : Subgroup SL(2, ℝ)} (h : GoodLattice Γ) (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) : GoodLattice Γ' := by
  classical
  haveI := h.discrete
  refine ⟨discreteTopology_of_le hle, ?_⟩
  obtain ⟨F, hFm, hFv, hcov, hfin⟩ := h.exists_fund
  haveI : Finite (Γ ⧸ Γ'.subgroupOf Γ) := Subgroup.index_ne_zero_iff_finite.mp hidx
  haveI := Fintype.ofFinite (Γ ⧸ Γ'.subgroupOf Γ)
  set r : Γ ⧸ Γ'.subgroupOf Γ → SL(2, ℝ) := fun q ↦ (q.out : SL(2, ℝ))
  refine ⟨⋃ q, (r q)⁻¹ • F, MeasurableSet.iUnion fun q ↦ hFm.const_smul _, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_iUnion_fintype_le _ _) ?_
    simp only [volume_smul, Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hFv
  · intro z
    obtain ⟨γ, hγ, hγz⟩ := hcov z
    set q : Γ ⧸ Γ'.subgroupOf Γ := QuotientGroup.mk ⟨γ, hγ⟩
    have hq : (q.out)⁻¹ * ⟨γ, hγ⟩ ∈ Γ'.subgroupOf Γ := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    refine ⟨(r q)⁻¹ * γ, hq, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    rw [mul_smul]
    exact Set.smul_mem_smul_set hγz
  · intro z
    refine (Set.finite_iUnion fun q ↦ (hfin z).image fun g ↦ (r q)⁻¹ * g).subset ?_
    rintro γ' ⟨hγ', hz⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
    rw [Set.mem_inv_smul_set_iff, ← mul_smul] at hq
    refine Set.mem_iUnion.mpr ⟨q, r q * γ', ⟨mul_mem (q.out).2 (hle hγ'), hq⟩, ?_⟩
    simp

/-- The conjugate of a translation. -/
lemma conj_translation (γ P : SL(2, ℝ)) {h : ℝ}
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = !![1, h; 0, 1]) :
    ((γ⁻¹ * P * γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 + h * γ 1 0 * γ 1 1, h * γ 1 1 ^ 2; -h * γ 1 0 ^ 2, 1 - h * γ 1 0 * γ 1 1] := by
  have hdet := γ.det_coe
  rw [det_fin_two] at hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hP, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

set_option linter.flexible false in
/-- **Height bound (weak Shimizu).** If a discrete `Γ` contains a nontrivial translation, the
bottom rows of its elements are bounded away from `0`. -/
theorem exists_bottom_row_bound {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] {P : SL(2, ℝ)}
    (hPΓ : P ∈ Γ) {h : ℝ} (hh : h ≠ 0) (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = !![1, h; 0, 1]) :
    ∃ δ > 0, ∀ γ ∈ Γ, δ ≤ γ 1 0 ^ 2 + γ 1 1 ^ 2 := by
  obtain ⟨U, hU, hU1⟩ := exists_nhds_of_discrete Γ
  let M : ℝ × ℝ → SL(2, ℝ) := fun p ↦
    ⟨!![1 + h * p.1 * p.2, h * p.2 ^ 2; -h * p.1 ^ 2, 1 - h * p.1 * p.2], by
      rw [det_fin_two_of]; ring⟩
  have hMc : Continuous M := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hM0 : M (0, 0) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M]
  have hpre : M ⁻¹' U ∈ 𝓝 ((0, 0) : ℝ × ℝ) := hMc.continuousAt.preimage_mem_nhds (hM0 ▸ hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε ^ 2, by positivity, fun γ hγ ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have hc : |γ 1 0| < ε := by
    have : γ 1 0 ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg (γ 1 1)]
    exact abs_lt_of_sq_lt_sq this hε.le
  have hd : |γ 1 1| < ε := by
    have : γ 1 1 ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg (γ 1 0)]
    exact abs_lt_of_sq_lt_sq this hε.le
  have hmem : ((γ 1 0, γ 1 1) : ℝ × ℝ) ∈ Metric.ball (0, 0) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    simpa [Real.dist_eq] using ⟨hc, hd⟩
  have heq : M (γ 1 0, γ 1 1) = γ⁻¹ * P * γ := by
    ext i j
    rw [conj_translation γ P hP]
  have h1 := hU1 _ (mul_mem (mul_mem (inv_mem hγ) hPΓ) hγ) (heq ▸ hball hmem)
  rw [← heq] at h1
  have e01 := congrArg (fun g : SL(2, ℝ) ↦ g 0 1) h1
  have e10 := congrArg (fun g : SL(2, ℝ) ↦ g 1 0) h1
  simp [M] at e01 e10
  have hdet := γ.det_coe
  rw [det_fin_two] at hdet
  rw [e01.resolve_left hh, e10.resolve_left hh] at hdet
  simp at hdet

/-- Heights along an orbit are bounded. -/
lemma im_smul_le_of_bound {δ : ℝ} (hδ : 0 < δ) (γ : SL(2, ℝ))
    (hγ : δ ≤ γ 1 0 ^ 2 + γ 1 1 ^ 2) (z : ℍ) :
    (γ • z).im ≤ (2 * z.im ^ 2 + 1 + 2 * z.re ^ 2) / (z.im * δ) := by
  rw [im_smul_SL]
  set c := γ 1 0
  set d := γ 1 1
  have hQ : Complex.normSq (c * (z : ℂ) + d) = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hy := z.im_pos
  have hpos : 0 < Complex.normSq (c * (z : ℂ) + d) := by
    have := (γ • z).im_pos
    rw [im_smul_SL] at this
    exact (div_pos_iff.mp this).elim (fun h ↦ h.2) fun h ↦ absurd hy (not_lt.mpr h.1.le)
  rw [div_le_div_iff₀ hpos (by positivity), hQ]
  have key : z.im ^ 2 * (c ^ 2 + d ^ 2) ≤
      ((c * z.re + d) ^ 2 + (c * z.im) ^ 2) * (2 * z.im ^ 2 + 1 + 2 * z.re ^ 2) := by
    nlinarith [sq_nonneg (2 * c * z.re + d), sq_nonneg (c * z.re + d), sq_nonneg c,
      sq_nonneg (c * z.im), sq_nonneg z.re, mul_nonneg (sq_nonneg (c * z.im)) (sq_nonneg z.re),
      mul_nonneg (sq_nonneg (c * z.re + d)) (sq_nonneg z.im)]
  have : z.im ^ 2 * δ ≤ z.im ^ 2 * (c ^ 2 + d ^ 2) := mul_le_mul_of_nonneg_left hγ (by positivity)
  nlinarith

/-- Boxes in `ℍ` are compact. -/
lemma isCompact_box (a b η H : ℝ) (hη : 0 < η) :
    IsCompact {w : ℍ | w.re ∈ Icc a b ∧ w.im ∈ Icc η H} := by
  rw [isEmbedding_coe.isInducing.isCompact_iff]
  have : ((↑) '' {w : ℍ | w.re ∈ Icc a b ∧ w.im ∈ Icc η H} : Set ℂ) =
      Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Icc a b ×ˢ Icc η H) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [Set.mem_preimage, Set.mem_prod]
      exact ⟨by simpa using hz.1, by simpa using hz.2⟩
    · intro hw
      simp only [Set.mem_preimage, Set.mem_prod] at hw
      refine ⟨⟨w, ?_⟩, ?_, rfl⟩
      · have := hw.2.1
        simp at this
        linarith
      · simpa using hw
  rw [this, Homeomorph.isCompact_preimage]
  exact isCompact_Icc.prod isCompact_Icc

/-- **Finite multiplicity of a strip.** -/
theorem finite_strip_multiplicity {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] {P : SL(2, ℝ)}
    (hPΓ : P ∈ Γ) {h : ℝ} (hh : h ≠ 0) (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = !![1, h; 0, 1])
    (a b η : ℝ) (hη : 0 < η) (z : ℍ) :
    {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ {w : ℍ | w.re ∈ Icc a b ∧ η ≤ w.im}}.Finite := by
  obtain ⟨δ, hδ, hb⟩ := exists_bottom_row_bound hPΓ hh hP
  set H := (2 * z.im ^ 2 + 1 + 2 * z.re ^ 2) / (z.im * δ)
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ)
    (isCompact_singleton (x := z)) (isCompact_box a b η H hη)
  refine (hfin.image Subtype.val).subset ?_
  rintro γ ⟨hγ, hre, him⟩
  refine ⟨⟨γ, hγ⟩, ⟨γ • z, ⟨z, rfl, rfl⟩, hre, him, ?_⟩, rfl⟩
  exact im_smul_le_of_bound hδ γ (hb γ hγ) z

section normal

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- **The Fricke normal form group is a good lattice** (under the triangle inequalities). -/
theorem goodLattice_normal (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y) : GoodLattice (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  haveI hdisc : DiscreteTopology Γ := discreteTopology_normal hx hy hz hrel
  refine ⟨hdisc, ?_⟩
  obtain ⟨η, hη, hcov⟩ := exists_strip_cover_normal hz hrel hx hy h1 h2 h3
  have hA : nA hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  have hB : nB hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  set K := nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹
  have hK : K ∈ Γ := mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
  have hK2 : ((K * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 4; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_commutator_n hz hrel]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  refine ⟨_, (measurableSet_Icc.preimage continuous_re.measurable).inter
    (measurableSet_Ici.preimage continuous_im.measurable), volume_strip_lt_top _ _ _ hη, hcov,
    fun w ↦ ?_⟩
  exact finite_strip_multiplicity (mul_mem hK hK) (by norm_num) hK2 _ _ η hη w

end normal

end OrbicurveCores.M2
