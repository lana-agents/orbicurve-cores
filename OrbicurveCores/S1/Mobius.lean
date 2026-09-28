/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Defs

/-!
# Möbius maps from the Schwarz lemma and from `j`

* `exists_SL2R_eq_of_leftInverse`: a holomorphic `T : ℍ → ℍ` with a holomorphic left inverse is
  Möbius. (This is oka's `Uniformization.exists_SL2R_eq_of_holomorphic`, whose proof only uses the
  left inverse.)
* `exists_SL2Z_eq_of_modularJ`: a holomorphic `H : ℍ → ℍ` with `j ∘ H = j` is an element of
  `SL(2, ℤ)`, by Baire's theorem and the identity theorem.
-/

open Complex Metric Set Filter Topology Uniformization
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace OrbicurveCores.S1

/-- **A holomorphic self-map of `ℍ` with a holomorphic left inverse is Möbius.** -/
theorem exists_SL2R_eq_of_leftInverse {T S : ℍ → ℍ} (hT : HolomorphicH T) (hS : HolomorphicH S)
    (hST : ∀ τ, S (T τ) = τ) : ∃ g : SL(2, ℝ), ∀ τ, T τ = g • τ := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq SL(2, ℝ) (T UpperHalfPlane.I) UpperHalfPlane.I
  set F : ℍ → ℍ := fun τ ↦ g₀ • T τ
  set Fi : ℍ → ℍ := fun τ ↦ S (g₀⁻¹ • τ)
  have hFiF : Fi ∘ F = id := by funext τ; simp [F, Fi, hST]
  have hF : HolomorphicH F := hT.smul g₀
  have hFi : HolomorphicH Fi := hS.comp_smul g₀⁻¹
  set G := discConj F
  set H := discConj Fi
  have hofI : (ofComplex (cayleyInv 0) : ℍ) = UpperHalfPlane.I := by
    rw [cayleyInv_zero]; exact ofComplex_apply UpperHalfPlane.I
  have hG0 : G 0 = 0 := by
    change cayley (F (ofComplex (cayleyInv 0))) = 0
    rw [hofI]; simp only [F, hg₀]; exact cayley_I
  have hH0 : H 0 = 0 := by
    change cayley (Fi (ofComplex (cayleyInv 0))) = 0
    rw [hofI]
    have : g₀⁻¹ • UpperHalfPlane.I = T UpperHalfPlane.I := by rw [inv_smul_eq_iff, hg₀]
    simp only [Fi, this, hST]; exact cayley_I
  have hHG : ∀ w ∈ ball (0 : ℂ) 1, H (G w) = w := fun w hw ↦ by
    change discConj Fi (discConj F w) = w
    rw [discConj_comp, hFiF, discConj_id hw]
  have hmaps : ∀ K : ℍ → ℍ, MapsTo (discConj K) (ball 0 1) (closedBall 0 1) :=
    fun K w _ ↦ ball_subset_closedBall (discConj_mem_ball K w)
  have hGle : ∀ w ∈ ball (0 : ℂ) 1, ‖G w‖ ≤ ‖w‖ := fun w hw ↦
    Complex.norm_le_norm_of_mapsTo_ball (differentiableOn_discConj hF) (hmaps F) hG0
      (mem_ball_zero_iff.mp hw)
  have hHle : ∀ w ∈ ball (0 : ℂ) 1, ‖H w‖ ≤ ‖w‖ := fun w hw ↦
    Complex.norm_le_norm_of_mapsTo_ball (differentiableOn_discConj hFi) (hmaps Fi) hH0
      (mem_ball_zero_iff.mp hw)
  have hGnorm : ∀ w ∈ ball (0 : ℂ) 1, ‖G w‖ = ‖w‖ := fun w hw ↦ le_antisymm (hGle w hw) (by
    have := hHle (G w) (discConj_mem_ball F w)
    rwa [hHG w hw] at this)
  -- `G` is a rotation
  have hhalf : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; norm_num
  set u := dslope G 0 (1 / 2)
  have hu : ‖u‖ = 1 := by
    simp only [u]
    rw [dslope_of_ne _ (by norm_num), slope_def_field, hG0, sub_zero, sub_zero, norm_div,
      hGnorm _ hhalf]
    norm_num
  have hGu : ∀ w ∈ ball (0 : ℂ) 1, G w = w * u := by
    intro w hw
    have := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div (R₁ := 1) (R₂ := 1)
      (differentiableOn_discConj hF)
      (by change MapsTo G _ (closedBall (G 0) 1); rw [hG0]; exact hmaps F) hhalf
      (by change ‖u‖ = 1 / 1; rw [hu]; norm_num) hw
    change G w = _ at this
    rw [this]
    change G 0 + (w - 0) • u = w * u
    rw [hG0]; simp [smul_eq_mul]
  -- the rotation matrix
  set e : ℂ := u ^ ((2 : ℕ) : ℂ)⁻¹
  have he2 : e ^ 2 = u := cpow_nat_inv_pow u two_ne_zero
  have he : ‖e‖ = 1 := by
    have h1 : ‖e‖ ^ 2 = 1 := by rw [← norm_pow, he2, hu]
    nlinarith [norm_nonneg e]
  refine ⟨g₀⁻¹ * rot e he, fun τ ↦ ?_⟩
  have hFτ : F τ = rot e he • τ := by
    apply UpperHalfPlane.ext
    have h1 : cayley (F τ) = cayley ((rot e he • τ : ℍ) : ℂ) := by
      rw [cayley_rot_smul, he2]
      have : G (cayley τ) = cayley (F τ) := by
        change cayley (F (ofComplex (cayleyInv (cayley τ)))) = _
        rw [cayleyInv_cayley τ.im_pos, ofComplex_apply]
      rw [← this, hGu _ (cayley_mem_ball τ.im_pos), mul_comm]
    have := congrArg cayleyInv h1
    rwa [cayleyInv_cayley (F τ).im_pos, cayleyInv_cayley (rot e he • τ).im_pos] at this
  rw [mul_smul, ← hFτ]
  simp [F]

/-- The image of `δ ∈ SL(2, ℤ)` in `SL(2, ℝ)`. -/
abbrev toSLR (δ : SL(2, ℤ)) : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ

lemma toSLR_smul (δ : SL(2, ℤ)) (τ : ℍ) : toSLR δ • τ = δ • τ := by
  ext
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  simp

lemma continuous_of_holomorphicH {H : ℍ → ℍ} (hH : HolomorphicH H) : Continuous H := by
  have hc : Continuous fun τ : ℍ ↦ (H τ : ℂ) := by
    have := hH.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos
    refine this.congr fun τ ↦ ?_
    simp [ofComplex_apply]
  exact continuous_induced_rng.mpr hc

lemma holomorphicH_smul (g : SL(2, ℝ)) : HolomorphicH fun τ ↦ g • τ := by
  have hid : HolomorphicH id := by
    unfold HolomorphicH
    refine (differentiableOn_id).congr fun z hz ↦ ?_
    simp [ofComplex_of_im_pos hz]
  exact hid.smul g

/-- **Identity theorem** for holomorphic self-maps of `ℍ`. -/
lemma eq_of_eqOn_open {H₁ H₂ : ℍ → ℍ} (h₁ : HolomorphicH H₁) (h₂ : HolomorphicH H₂)
    {V : Set ℍ} (hV : IsOpen V) (hne : V.Nonempty) (heq : EqOn H₁ H₂ V) : H₁ = H₂ := by
  obtain ⟨τ₀, hτ₀⟩ := hne
  set f₁ : ℂ → ℂ := fun z ↦ (H₁ (ofComplex z) : ℂ)
  set f₂ : ℂ → ℂ := fun z ↦ (H₂ (ofComplex z) : ℂ)
  have ho : IsOpen {z : ℂ | 0 < z.im} := isOpen_upper
  have ha₁ : AnalyticOnNhd ℂ f₁ {z | 0 < z.im} := h₁.analyticOnNhd ho
  have ha₂ : AnalyticOnNhd ℂ f₂ {z | 0 < z.im} := h₂.analyticOnNhd ho
  have hconv : Convex ℝ {z : ℂ | 0 < z.im} := convex_halfSpace_im_gt 0
  have hev : f₁ =ᶠ[𝓝 (τ₀ : ℂ)] f₂ := by
    have hVc : IsOpen (((↑) : ℍ → ℂ) '' V) := (isOpenEmbedding_coe).isOpenMap _ hV
    filter_upwards [hVc.mem_nhds ⟨τ₀, hτ₀, rfl⟩] with z ⟨σ, hσ, hσz⟩
    subst hσz
    simp only [f₁, f₂, ofComplex_apply]
    rw [heq hσ]
  have := ha₁.eqOn_of_preconnected_of_eventuallyEq ha₂ hconv.isPreconnected τ₀.im_pos hev
  funext τ
  apply UpperHalfPlane.ext
  have h := this τ.im_pos
  simpa [f₁, f₂, ofComplex_apply] using h

instance : Countable SL(2, ℤ) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  Function.Injective.countable (f := fun A : SL(2, ℤ) ↦ (A : Matrix (Fin 2) (Fin 2) ℤ))
    Subtype.coe_injective

/-- **A holomorphic `H : ℍ → ℍ` with `j ∘ H = j` is an element of `SL(2, ℤ)`.** -/
theorem exists_SL2Z_eq_of_modularJ {H : ℍ → ℍ} (hH : HolomorphicH H)
    (hj : ∀ τ, Heights.modularJ (H τ) = Heights.modularJ τ) :
    ∃ δ : SL(2, ℤ), ∀ τ, H τ = toSLR δ • τ := by
  have hHc := continuous_of_holomorphicH hH
  set S : SL(2, ℤ) → Set ℍ := fun δ ↦ {τ | H τ = toSLR δ • τ}
  have hS : ∀ δ, IsClosed (S δ) := fun δ ↦
    isClosed_eq hHc (continuous_of_holomorphicH (holomorphicH_smul (toSLR δ)))
  have hU : ⋃ δ, S δ = univ := by
    refine eq_univ_of_forall fun τ ↦ mem_iUnion.mpr ?_
    obtain ⟨δ, hδ⟩ := Heights.exists_smul_eq_of_modularJ_eq (H τ) τ (hj τ)
    exact ⟨δ, by simp only [S, mem_setOf_eq, toSLR_smul, hδ]⟩
  obtain ⟨δ, hδ⟩ := nonempty_interior_of_iUnion_of_closed hS hU
  refine ⟨δ, fun τ ↦ ?_⟩
  have := eq_of_eqOn_open hH (holomorphicH_smul (toSLR δ)) isOpen_interior hδ
    fun σ hσ ↦ (interior_subset hσ : σ ∈ S δ)
  exact congrFun this τ

end OrbicurveCores.S1
