/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.U2.CoordRing
import OrbicurveCores.U2.EtalePoints
import OrbicurveCores.U2.GaloisClosure
import OrbicurveCores.U2.Realize
import OrbicurveCores.U2.R3
import Oka.Uniformization.FEtLattice

/-!
# Theorem G: automorphisms of finite étale covers fix the `x`-coordinate

For a uniformisation `(G₁, G₂, π)` of `E ∖ {0}` and a finite étale `A_X`-algebra `B`
(`A_X = ℂ[E]`), every Möbius transformation `g` realising an automorphism `σ` of `B` on a
holomorphic lift (`FEt.exists_mobius`) lies in the commensurator of `⟨G₁, G₂⟩`
(`U2.mobius_mem_commensurator`): it normalises the stabiliser `S` of the lift, which is
commensurable with `⟨G₁, G₂⟩`.
-/

open Polynomial Uniformization Uniformization.FEt
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Pointwise

namespace OrbicurveCores.U2

section Commensurator

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  {ι₀ : A →ₐ[ℂ] (ℍ → ℂ)} {n : ℕ}

theorem finite_over {τ : ℍ} (hloc : LocPres ι₀ (B := B) n τ) : Finite (Over B (FEt.pt ι₀ τ)) := by
  classical
  obtain ⟨b₀, F, δ, hFm, -, hF, hδ, hpres⟩ := hloc
  have hmaps : ∀ ψ : Over B (FEt.pt ι₀ τ),
      ψ.1 b₀ ∈ (F.map (FEt.pt ι₀ τ : A →+* ℂ)).roots.toFinset := fun ψ ↦ by
    rw [Multiset.mem_toFinset, mem_roots ((hFm.map _).ne_zero)]; exact ψ.isRoot hF
  exact Finite.of_injective (fun ψ ↦ (⟨ψ.1 b₀, hmaps ψ⟩ :
    (F.map (FEt.pt ι₀ τ : A →+* ℂ)).roots.toFinset))
    fun ψ ψ' h ↦ Over.ext_of_apply_eq hδ hpres (congrArg Subtype.val h)

variable {W : WeierstrassCurve ℂ} {G₁ G₂ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- The stabiliser of a lift. -/
def liftStab (ι : ℍ → B → ℂ) : Subgroup SL(2, ℝ) where
  carrier := {δ | ∀ τ b, ι (δ • τ) b = ι τ b}
  mul_mem' {δ δ'} h h' τ b := by rw [mul_smul, h, h']
  one_mem' τ b := by rw [one_smul]
  inv_mem' {δ} h τ b := by
    have := h (δ⁻¹ • τ) b
    rw [smul_inv_smul] at this
    exact this.symm

/-- **Möbius transformations realising automorphisms lie in the commensurator.** -/
theorem mobius_mem_commensurator [W.IsElliptic] (h : IsUniformization W G₁ G₂ π) {x y : A}
    (hx : ∀ τ, ι₀ x τ = (π τ).1) (hy : ∀ τ, ι₀ y τ = (π τ).2)
    (hxy : ∀ χ χ' : A →ₐ[ℂ] ℂ, χ x = χ' x → χ y = χ' y → χ = χ')
    (hhol : ∀ a, Unif.HolH (ι₀ a))
    (hcount : ∀ τ, Nat.card (Over B (FEt.pt ι₀ τ)) = n) (hloc : ∀ τ, LocPres ι₀ (B := B) n τ)
    (σ : B ≃ₐ[ℂ] B) {ι : ℍ → B → ℂ} (hι : IsLift ι₀ ι) {g : SL(2, ℝ)}
    (hg : ∀ τ b, ι τ (σ b) = ι (g • τ) b) :
    g ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {G₁, G₂}) := by
  classical
  set S := liftStab ι
  set Γ := Subgroup.closure {G₁, G₂}
  have hcov := isCoveringMap_proj hhol hcount hloc
  -- `S ≤ ±Γ`
  have hSpm : S ≤ IsUniformization.pmGroup G₁ G₂ := by
    intro δ hδ
    refine h.mem_pmGroup_of_deck fun w ↦ Subtype.ext (Prod.ext ?_ ?_)
    · change (π ((δ • w : ℍ) : ℂ)).1 = (π (w : ℂ)).1
      rw [← hx, ← hx, ← IsLift.apply_algebraMap hι, ← IsLift.apply_algebraMap hι, hδ]
    · change (π ((δ • w : ℍ) : ℂ)).2 = (π (w : ℂ)).2
      rw [← hy, ← hy, ← IsLift.apply_algebraMap hι, ← IsLift.apply_algebraMap hι, hδ]
  -- `g` normalises `S`
  have hg' : ∀ τ b, ι (g⁻¹ • τ) b = ι τ (σ.symm b) := fun τ b ↦ by
    have := hg (g⁻¹ • τ) (σ.symm b)
    rw [AlgEquiv.apply_symm_apply, smul_inv_smul] at this
    exact this
  have hconj : ConjAct.toConjAct g • S = S := by
    apply le_antisymm
    · intro δ hδ
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hδ
      have e : (ConjAct.toConjAct g)⁻¹ • δ = g⁻¹ * δ * g := by
        rw [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      rw [e] at hδ
      intro τ b
      have e1 : δ • τ = g • ((g⁻¹ * δ * g) • (g⁻¹ • τ)) := by
        rw [← mul_smul, ← mul_smul]; congr 1; group
      rw [e1, ← hg, hδ, hg, smul_inv_smul]
    · intro δ hδ
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have e : (ConjAct.toConjAct g)⁻¹ • δ = g⁻¹ * δ * g := by
        rw [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      rw [e]
      intro τ b
      rw [mul_smul, mul_smul, hg', hδ, ← hg, AlgEquiv.apply_symm_apply]
  have hgS : g ∈ Subgroup.Commensurable.commensurator S := by
    rw [Subgroup.Commensurable.commensurator_mem_iff, hconj]
  -- `Γ`-invariance of `ι₀`
  have hΓ : ∀ γ ∈ Γ, ∀ (a : A) (τ : ℍ), ι₀ a (γ • τ) = ι₀ a τ := by
    intro γ hγ a τ
    have hπ : π ((γ • τ : ℍ) : ℂ) = π (τ : ℂ) := ((h.fibre τ (γ • τ)).mpr ⟨γ, hγ, rfl⟩).symm
    have := hxy (FEt.pt ι₀ (γ • τ)) (FEt.pt ι₀ τ) (by simp [hx, hπ]) (by simp [hy, hπ])
    exact congrArg (fun χ : A →ₐ[ℂ] ℂ ↦ χ a) this
  -- `S ∩ Γ` has finite index in `Γ`
  set τ₀ := UpperHalfPlane.I
  haveI := finite_over (hloc τ₀)
  set R := Set.range fun ψ : Over B (FEt.pt ι₀ τ₀) ↦ (⇑ψ.1 : B → ℂ)
  haveI : Finite R := Set.finite_range _
  have hmemR : ∀ γ ∈ Γ, ι (γ⁻¹ • τ₀) ∈ R := by
    intro γ hγ
    obtain ⟨ψ, hψ⟩ := (hι.smul hΓ (Γ.inv_mem hγ)).pt τ₀
    exact ⟨ψ, hψ⟩
  have hSΓ : S.relIndex Γ ≠ 0 := by
    let f : Γ ⧸ S.subgroupOf Γ → R := Quotient.lift (fun γ : Γ ↦ ⟨ι ((γ : SL(2, ℝ))⁻¹ • τ₀),
      hmemR γ γ.2⟩) (by
        intro γ₁ γ₂ hγ
        have hS : (γ₁ : SL(2, ℝ))⁻¹ * γ₂ ∈ S := by
          have := (QuotientGroup.leftRel_apply).mp hγ
          exact Subgroup.mem_subgroupOf.mp this
        apply Subtype.ext
        funext b
        have := (S.inv_mem hS) ((γ₁ : SL(2, ℝ))⁻¹ • τ₀) b
        rw [← mul_smul, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] at this
        exact this.symm)
    have hf : Function.Injective f := by
      intro q₁ q₂ hq
      induction q₁ using QuotientGroup.induction_on with
      | H γ₁ =>
      induction q₂ using QuotientGroup.induction_on with
      | H γ₂ =>
      have h1 : ι ((γ₁ : SL(2, ℝ))⁻¹ • τ₀) = ι ((γ₂ : SL(2, ℝ))⁻¹ • τ₀) :=
        congrArg Subtype.val hq
      have hl := (hι.smul hΓ (Γ.inv_mem γ₁.2)).eq hcov (hι.smul hΓ (Γ.inv_mem γ₂.2)) h1
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      intro τ b
      have := congrFun (congrFun hl ((γ₂ : SL(2, ℝ)) • τ)) b
      simp only [inv_smul_smul] at this
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
      exact this
    haveI : Finite (Γ ⧸ S.subgroupOf Γ) := Finite.of_injective f hf
    exact Subgroup.index_ne_zero_of_finite
  have hΓS : Γ.relIndex S ≠ 0 := fun h0 ↦
    relIndex_closure_pmGroup_ne_zero G₁ G₂ (Subgroup.relIndex_eq_zero_of_le_right hSpm h0)
  have hcomm : Subgroup.Commensurable S Γ := ⟨hSΓ, hΓS⟩
  rwa [← Subgroup.Commensurable.eq hcomm]

end Commensurator

end OrbicurveCores.U2
