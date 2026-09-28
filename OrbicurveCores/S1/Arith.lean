/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.LocalForm
import OrbicurveCores.S1.Mobius
import OrbicurveCores.Fricke

/-!
# An orbifold covering of the `j`-line forces integral traces

Let `ψ : ℍ → ℂ ∖ Λ` be oka's universal covering, `Γ = ⟨A, B⟩` its extended deck group, and let
`F : ℂ ∖ Λ → ℂ` be an orbifold covering of the `j`-line (`IsOrbCover F Λᶜ sig`, local normal forms
of order `sig`) which is `2Λ`-periodic. Then `tr(γ)² ∈ ℤ` for every `γ ∈ Γ` (`int_sq_traces`).

Proof (Blueprint §2.3c, item 5): lift `Ψ = F ∘ ψ` through `j` to `h : ℍ → ℍ`, and `j` through `F`
and then through `ψ` to `k : ℍ → ℍ`. Then `j ∘ h ∘ k = j`, so `h ∘ k ∈ SL(2, ℤ)`
(`exists_SL2Z_eq_of_modularJ`). So `k` has a holomorphic left inverse and is Möbius
(`exists_SL2R_eq_of_leftInverse`), hence so is `h = m`. For `γ ∈ Γ`, `Ψ ∘ γ² = Ψ`, so
`m γ² m⁻¹ ∈ ±SL(2, ℤ)` and `tr(γ)² = tr(γ²) + 2 ∈ ℤ`.
-/

open Complex Metric Set Filter Topology Uniformization
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace OrbicurveCores.S1

lemma tr_sq_eq (γ : SL(2, ℝ)) : tr (γ * γ) = tr γ ^ 2 - 2 := by
  have h := congrArg Matrix.trace (sq_eq γ)
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul] at h
  unfold tr
  rw [Matrix.SpecialLinearGroup.coe_mul, h]
  norm_num; ring

lemma tr_conj (m γ : SL(2, ℝ)) : tr (m * γ * m⁻¹) = tr γ := by
  rw [tr_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

lemma tr_toSLR (δ : SL(2, ℤ)) : ∃ n : ℤ, tr (toSLR δ) = n :=
  ⟨δ 0 0 + δ 1 1, by simp [tr_def]⟩

/-- A Möbius map preserving `j` has integral trace up to sign. -/
lemma exists_int_tr_of_modularJ {M : SL(2, ℝ)}
    (hM : ∀ σ : ℍ, Heights.modularJ (M • σ) = Heights.modularJ σ) : ∃ n : ℤ, tr M = n := by
  obtain ⟨δ, hδ⟩ := exists_SL2Z_eq_of_modularJ (holomorphicH_smul M) hM
  have hfix : ∀ σ : ℍ, ((toSLR δ)⁻¹ * M) • σ = σ := fun σ ↦ by
    rw [mul_smul, hδ σ, inv_smul_smul]
  obtain ⟨n, hn⟩ := tr_toSLR δ
  rcases Unif.eq_one_or_neg_one_of_forall hfix with h | h
  · rw [inv_mul_eq_one] at h
    exact ⟨n, by rw [← h, hn]⟩
  · have hM : M = -toSLR δ := by
      rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at h; exact h
    refine ⟨-n, ?_⟩
    rw [hM]
    simp only [tr, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg] at hn ⊢
    rw [hn]; push_cast; ring

lemma holomorphicH_of_differentiableOn {h₀ : ℂ → ℂ} (hd : DifferentiableOn ℂ h₀ upper)
    (hm : MapsTo h₀ upper upper) :
    HolomorphicH (fun τ : ℍ ↦ (⟨h₀ τ, hm τ.im_pos⟩ : ℍ)) := by
  unfold HolomorphicH
  refine hd.congr fun z hz ↦ ?_
  simp only [ofComplex_of_im_pos hz]

/-- **Integral traces.** If `F` is a `2Λ`-periodic orbifold covering of the `j`-line on `ℂ ∖ Λ`,
then every element of the uniformising group `⟨A, B⟩` of `(ℂ ∖ Λ)/Λ` has `tr(γ)² ∈ ℤ`. -/
theorem int_sq_traces (hL : OrbLiftStatement) (hJ : JOrbStatement) (τ₀ : ℍ) {F : ℂ → ℂ}
    (hFo : IsOrbCover F ((Heights.periodPairOfUpperHalfPlane τ₀).lattice : Set ℂ)ᶜ sig)
    (hFl : ∀ u ∉ (Heights.periodPairOfUpperHalfPlane τ₀).lattice, HasLocalForm F u (sig (F u)))
    (hFp : ∀ u, ∀ l ∈ (Heights.periodPairOfUpperHalfPlane τ₀).lattice, F (u + 2 * l) = F u) :
    ∀ γ ∈ Subgroup.closure {Generators.A (unifOf (Heights.periodPairOfUpperHalfPlane τ₀)),
      Generators.B (unifOf (Heights.periodPairOfUpperHalfPlane τ₀))}, ∃ m : ℤ, tr γ ^ 2 = m := by
  set L := Heights.periodPairOfUpperHalfPlane τ₀
  set U := unifOf L
  -- `Ψ = F ∘ ψ` and its local normal forms
  set Ψ : ℂ → ℂ := fun z ↦ F (U.Ψ z)
  have hΨloc : ∀ z ∈ upper, HasLocalForm Ψ z (sig (Ψ z)) := fun z hz ↦
    HasLocalForm.comp (hFl _ (U.notMem z hz))
      (U.differentiableOn.analyticAt (isOpen_upper.mem_nhds hz))
      (U.deriv_ne_zero z hz)
  have hΨd : DifferentiableOn ℂ Ψ upper := fun z hz ↦
    (HasLocalForm.analyticAt (hΨloc z hz)).differentiableAt.differentiableWithinAt
  -- `h₀`: lift of `Ψ` through `j`
  obtain ⟨h₀, hh₀d, hh₀m, hh₀⟩ := hL jC Ψ upper sig sig_pos hJ.1 hΨd hΨloc
  -- `k₁`: lift of `j` through `F`
  obtain ⟨k₁, hk₁d, hk₁m, hk₁⟩ := hL F jC _ sig sig_pos hFo differentiableOn_jC hJ.2
  -- `k`: lift of `k₁` through `ψ`
  have hk₁c : Continuous fun τ : ℍ ↦ k₁ τ :=
    hk₁d.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos
  obtain ⟨z₀, hz₀⟩ := U.surj (k₁ UpperHalfPlane.I) (hk₁m (UpperHalfPlane.I).im_pos)
  obtain ⟨kC, ⟨-, hkC⟩, -⟩ := U.covering.existsUnique_continuousMap_lifts
    (⟨fun τ : ℍ ↦ k₁ τ, hk₁c⟩ : C(ℍ, ℂ)) (a₀ := UpperHalfPlane.I) (e₀ := z₀) hz₀
    fun τ ↦ hk₁m τ.im_pos
  set k : ℍ → ℍ := ⇑kC
  have hkψ : ∀ τ, U.Ψ (k τ) = k₁ τ := fun τ ↦ congrFun hkC τ
  have hkH : HolomorphicH k := by
    intro z hz
    refine (differentiableAt_of_comp_eq (f := U.Ψ) (g := k₁)
      (U.hasStrictDerivAt_Ψ (k (ofComplex z)).im_pos) (U.deriv_ne_zero _ (k _).im_pos) ?_ ?_
      ?_).differentiableWithinAt
    · exact (continuous_coe.comp kC.continuous).continuousAt.comp
        (ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds (by
          change z ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
          simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
          exact ⟨⟨z, hz⟩, rfl⟩)))
    · filter_upwards [isOpen_upper.mem_nhds hz] with w hw
      rw [hkψ, ofComplex_of_im_pos hw]
    · exact hk₁d.differentiableAt (isOpen_upper.mem_nhds hz)
  -- `h`, and `H = h ∘ k ∈ SL(2, ℤ)`
  set h : ℍ → ℍ := fun τ ↦ ⟨h₀ τ, hh₀m τ.im_pos⟩
  have hhH : HolomorphicH h := holomorphicH_of_differentiableOn hh₀d hh₀m
  have hjh : ∀ τ, Heights.modularJ (h τ) = Ψ τ := fun τ ↦ by
    rw [← jC_coe]; exact hh₀ _ τ.im_pos
  have hHH : HolomorphicH fun τ ↦ h (k τ) := by
    unfold HolomorphicH at hkH ⊢
    refine (hh₀d.comp hkH fun z _ ↦ (k (ofComplex z)).im_pos).congr fun z _ ↦ rfl
  have hHj : ∀ τ, Heights.modularJ (h (k τ)) = Heights.modularJ τ := fun τ ↦ by
    rw [hjh, ← jC_coe]
    change F (U.Ψ (k τ)) = jC τ
    rw [hkψ]; exact hk₁ _ τ.im_pos
  obtain ⟨δ, hδ⟩ := exists_SL2Z_eq_of_modularJ hHH hHj
  -- `k` and `h` are Möbius
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_leftInverse (S := fun τ ↦ (toSLR δ)⁻¹ • h τ) hkH
    (hhH.smul _) fun τ ↦ by rw [hδ, inv_smul_smul]
  set m : SL(2, ℝ) := toSLR δ * g⁻¹
  have hm : ∀ τ, h τ = m • τ := fun τ ↦ by
    have := hδ (g⁻¹ • τ)
    rw [hg, smul_inv_smul] at this
    rw [this, mul_smul]
  -- traces
  intro γ hγ
  have hΓ : γ ∈ U.deckGroup := by
    refine (Subgroup.closure_le _).mpr ?_ hγ
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [Generators.A_mem U, Generators.B_mem U]
  obtain ⟨l, hl, hγl⟩ := hΓ
  have hγ2 : ∀ τ : ℍ, Ψ (((γ * γ) • τ : ℍ) : ℂ) = Ψ τ := fun τ ↦ by
    change F (U.ψ ((γ * γ) • τ)) = F (U.ψ τ)
    rw [mul_smul, hγl, hγl, add_assoc, ← two_mul]
    exact hFp _ l hl
  have hM : ∀ σ : ℍ, Heights.modularJ ((m * (γ * γ) * m⁻¹) • σ) = Heights.modularJ σ := by
    intro σ
    obtain ⟨τ, rfl⟩ : ∃ τ, σ = m • τ := ⟨m⁻¹ • σ, by rw [smul_inv_smul]⟩
    rw [mul_smul, mul_smul, inv_smul_smul, ← hm, ← hm, hjh, hjh, hγ2]
  obtain ⟨n, hn⟩ := exists_int_tr_of_modularJ hM
  rw [tr_conj, tr_sq_eq] at hn
  exact ⟨n + 2, by push_cast; linarith⟩

end OrbicurveCores.S1
