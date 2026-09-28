/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Rigidity.Lattice

/-!
# Rigidity, step 2: lifting a uniformisation of a lattice curve to `ℂ ∖ Λ`

The Weierstrass point map `ℂ → E_τ(ℂ)` is a covering map (it is `ℂ → ℂ / Λ` followed by a
homeomorphism). A uniformisation `π : ℍ → E_τ ∖ {O}` therefore lifts to `σ : ℍ → ℂ ∖ Λ` with
`(℘, ℘' / 2) ∘ σ = π`; the lift is holomorphic with nonvanishing derivative, meets every
`Λ`-coset of `ℂ ∖ Λ`, and `σ z - σ w ∈ Λ` iff `z, w` are in the same orbit.
-/

open Complex Metric Set Filter Topology Function
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace OrbicurveCores.S1.Rigidity

/-- The Weierstrass point map `ℂ → E_τ(ℂ)` is a covering map. -/
theorem isCoveringMap_latticeCurvePointMap (τ : ℍ) :
    IsCoveringMap (Heights.latticeCurvePointMap τ) := by
  have hbij : Bijective (Heights.latticeQuotientCurvePointMap τ) := by
    refine ⟨(Heights.isClosedEmbedding_latticeQuotientCurvePointMap τ).injective, fun P ↦ ?_⟩
    obtain ⟨z, hz⟩ := Heights.latticePointMap_surjective τ P
    exact ⟨Heights.latticeQuotientMk τ z, hz⟩
  let h := (Heights.continuous_latticeQuotientCurvePointMap τ).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hbij)
  have : Heights.latticeCurvePointMap τ = h ∘ Heights.latticeQuotientMk τ := rfl
  rw [this]
  exact (Heights.isCoveringMap_latticeQuotientMk τ).homeomorph_comp h

/-- A holomorphic lift `σ : ℍ → ℂ ∖ Λ` of a uniformisation of the lattice curve `E_τ`. -/
structure IsLatticeLift (τ : ℍ) (σ : ℂ → ℂ) : Prop where
  notMem : ∀ z : ℂ, 0 < z.im → σ z ∉ (Lt τ).lattice
  differentiableAt : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ σ z
  deriv_ne_zero : ∀ z : ℂ, 0 < z.im → deriv σ z ≠ 0
  exists_sub_mem : ∀ x ∉ (Lt τ).lattice,
    ∃ z : ℂ, 0 < z.im ∧ σ z - x ∈ (Lt τ).lattice

/-- **Lifting a uniformisation of `E_τ` to `ℂ ∖ Λ`.** -/
theorem exists_isLatticeLift {τ : ℍ} {A B : SL(2, ℝ)}
    (h : Uniformizes (Heights.latticeWeierstrassCurve τ) A B) :
    ∃ σ : ℂ → ℂ, IsLatticeLift τ σ ∧ ∀ z w : ℍ,
      (σ z - σ w ∈ (Lt τ).lattice ↔
        ∃ γ ∈ Subgroup.closure {A, B}, γ • z = w) := by
  obtain ⟨π, hd, heq, hsurj, hfib⟩ := h
  have hd' : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ π z ∧ deriv π z ≠ 0 :=
    fun z hz ↦ hd ⟨z, hz⟩
  have heq' : ∀ z : ℂ, 0 < z.im →
      (Heights.latticeWeierstrassCurve τ).toAffine.Equation (π z).1 (π z).2 :=
    fun z hz ↦ heq ⟨z, hz⟩
  have hπc : ContinuousOn π {z : ℂ | 0 < z.im} :=
    fun z hz ↦ (hd' z hz).1.continuousAt.continuousWithinAt
  classical
  let g : ℂ → Heights.LatticeCurvePoint τ := fun z ↦
    if hz : 0 < z.im then Heights.latticeCurvePointOfAffine τ ⟨π z, heq' z hz⟩
    else Heights.latticeCurvePointInfinity τ
  have hgc : ContinuousOn g {z : ℂ | 0 < z.im} := by
    rw [continuousOn_iff_continuous_restrict]
    have : {z : ℂ | 0 < z.im}.restrict g =
        fun z : {z : ℂ | 0 < z.im} ↦ Heights.latticeCurvePointOfAffine τ ⟨π z, heq' z z.2⟩ := by
      funext z
      exact dif_pos z.2
    rw [this]
    exact (Heights.isOpenEmbedding_latticeCurvePointOfAffine τ).continuous.comp
      (hπc.restrict.subtype_mk _)
  obtain ⟨e₀, he₀⟩ := Heights.latticePointMap_surjective τ (g I)
  obtain ⟨σ, hσc, hσ, -⟩ := (isCoveringMap_latticeCurvePointMap τ).isCoveringMapOn
    |>.exists_lift_of_convex (convex_halfSpace_im_gt 0) hgc (mapsTo_univ _ _)
    (a₀ := I) (by simp) (e₀ := e₀) he₀
  -- the lift lands in `ℂ ∖ Λ` and lies over `π`
  have key : ∀ z : ℂ, 0 < z.im →
      σ z ∉ (Lt τ).lattice ∧ Uniformization.wpt τ (σ z) = π z := by
    intro z hz
    have h1 := hσ z hz
    simp only [g, dif_pos hz, Heights.latticeCurvePointMap_eq,
      Heights.latticeCurvePointOfAffine_eq_mk] at h1
    by_cases hmem : σ z ∈ (Lt τ).lattice
    · rw [Heights.latticePointMap_of_mem τ _ hmem] at h1
      exact absurd h1.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
    · refine ⟨hmem, ?_⟩
      rw [Uniformization.latticePointMap_eq_mk τ hmem] at h1
      simp only [WeierstrassCurve.Affine.Point.mk] at h1
      obtain ⟨e1, e2⟩ := WeierstrassCurve.Affine.Point.some.inj h1
      exact Prod.ext e1 e2
  have hev : ∀ z : ℂ, 0 < z.im → (fun v ↦ Uniformization.wpt τ (σ v)) =ᶠ[𝓝 z] π := by
    intro z hz
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with v hv
    exact (key v hv).2
  have hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ σ z := by
    intro z hz
    obtain ⟨hx, -⟩ := key z hz
    have hσz : ContinuousAt σ z :=
      hσc.continuousAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
    have hπz := (hd' z hz).1
    by_cases h0 : (Lt τ).derivWeierstrassP (σ z) = 0
    · have hs := (((Lt τ).analyticOnNhd_derivWeierstrassP _ hx)).hasStrictDerivAt
      refine Uniformization.differentiableAt_of_comp_eq hs
        (Uniformization.not_deriv_deriv_eq_zero τ hx h0) hσz ?_
        (g := fun v ↦ 2 * (π v).2) ?_
      · filter_upwards [hev z hz] with v hv
        rw [← hv]
        simp only [Uniformization.wpt]
        ring
      · exact ((hasDerivAt_snd' hπz.hasDerivAt).const_mul 2).differentiableAt
    · have hs := (((Lt τ).analyticOnNhd_weierstrassP _ hx)).hasStrictDerivAt
      rw [PeriodPair.deriv_weierstrassP] at hs
      refine Uniformization.differentiableAt_of_comp_eq hs h0 hσz ?_
        (g := fun v ↦ (π v).1) ?_
      · filter_upwards [hev z hz] with v hv
        rw [← hv]
        rfl
      · exact (hasDerivAt_fst' hπz.hasDerivAt).differentiableAt
  refine ⟨σ, ⟨fun z hz ↦ (key z hz).1, hdiff, ?_, ?_⟩, ?_⟩
  · -- nonvanishing derivative
    intro z hz h0
    obtain ⟨hx, -⟩ := key z hz
    have hσd : HasDerivAt σ 0 z := by
      have := (hdiff z hz).hasDerivAt
      rwa [h0] at this
    have h1 := (Uniformization.hasDerivAt_wp τ hx).comp z hσd
    have h2 := ((Uniformization.hasDerivAt_wp' τ hx).comp z hσd).div_const 2
    have h3 : HasDerivAt (fun v ↦ Uniformization.wpt τ (σ v))
        ((Lt τ).derivWeierstrassP (σ z) * 0,
          deriv (Lt τ).derivWeierstrassP (σ z) * 0 / 2) z := h1.prodMk h2
    have h4 := (h3.congr_of_eventuallyEq (hev z hz).symm).deriv
    apply (hd' z hz).2
    rw [h4]
    simp
  · -- every coset is met
    intro x hx
    obtain ⟨z, hz⟩ := hsurj _ _ (Uniformization.wpt_equation τ hx)
    refine ⟨z, z.im_pos, ?_⟩
    obtain ⟨hz', hw⟩ := key z z.im_pos
    exact (Uniformization.wpt_eq_iff τ hz' hx).mp (hw.trans hz)
  · intro z w
    obtain ⟨hz, hwz⟩ := key z z.im_pos
    obtain ⟨hw, hww⟩ := key w w.im_pos
    rw [← Uniformization.wpt_eq_iff τ hz hw, hwz, hww]
    exact hfib z w

end OrbicurveCores.S1.Rigidity
