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
import OrbicurveCores.GroupCanLift
import OrbicurveCores.U2.S1

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

section FixX

/-- The first coordinate of a uniformisation is holomorphic on `ℍ`. -/
theorem holH_fst {W : WeierstrassCurve ℂ} {G₁ G₂ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}
    (h : IsUniformization W G₁ G₂ π) : Unif.HolH fun τ : ℍ ↦ (π τ).1 := by
  intro z hz
  have hd : DifferentiableAt ℂ π z := (h.holo ⟨z, hz⟩).1
  refine (hd.fst.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]

/-- The second coordinate of a uniformisation is holomorphic on `ℍ`. -/
theorem holH_snd {W : WeierstrassCurve ℂ} {G₁ G₂ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}
    (h : IsUniformization W G₁ G₂ π) : Unif.HolH fun τ : ℍ ↦ (π τ).2 := by
  intro z hz
  have hd : DifferentiableAt ℂ π z := (h.holo ⟨z, hz⟩).1
  refine (hd.snd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

/-- The `x`-coordinate of `E ∖ {0}`. -/
noncomputable def xP : (AffOrbicurve.punctured E).A := puncturedRingEquiv E (FEt.xA E)

variable {B : Type*} [CommRing B] [Algebra ℂ B]
  [Algebra (AffOrbicurve.punctured E).A B] [IsScalarTower ℂ (AffOrbicurve.punctured E).A B]
  [IsDedekindDomain B] [Module.Finite (AffOrbicurve.punctured E).A B]
  [FaithfulSMul (AffOrbicurve.punctured E).A B]

set_option maxHeartbeats 1000000 in
-- assembling the analytic hypotheses of `FEt.exists_mobius` is slow
/-- **Theorem G, analytic form.** For a finite étale cover `B` of `E ∖ {0}` with non-exceptional
`j`, every `ℂ`-automorphism of `B` fixes the `x`-coordinate. -/
theorem fixes_xP (hj : ∀ c ∈ AffOrbicurve.excJ, E.j ≠ (c : ℂ))
    (het : ∀ w : Ideal B, w.IsMaximal → w.ramificationIdx (AffOrbicurve.punctured E).A = 1)
    (σ : B ≃ₐ[ℂ] B) :
    σ (algebraMap (AffOrbicurve.punctured E).A B (xP E)) =
      algebraMap (AffOrbicurve.punctured E).A B (xP E) := by
  classical
  set A := (AffOrbicurve.punctured E).A
  haveI : Algebra.FiniteType ℂ B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  obtain ⟨t, ht⟩ := Heights.modularJ_surjective E.j
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (Heights.latticeWeierstrassCurve t) E (by rw [Heights.latticeWeierstrassCurve_j, ht])
  obtain ⟨htr, htrA, h3, h4, h5, h6⟩ := uniformization_of_variableChange t E C hC
  have h : IsUniformization E _ _ (uniformizationMap t C) := ⟨h3, h4, h5, h6⟩
  set π := uniformizationMap t C
  set e : A ≃ₐ[ℂ] E.toAffine.CoordinateRing := ((puncturedRingEquiv E).restrictScalars ℂ).symm
  set ι₀ : A →ₐ[ℂ] (ℍ → ℂ) :=
    (FEt.coordFun E (fun τ ↦ (π τ).1) (fun τ ↦ (π τ).2) h.mem).comp e.toAlgHom
  have hinj : Function.Injective ι₀ :=
    (FEt.coordFun_injective h.mem fun x₀ y₀ hE ↦ by
      obtain ⟨τ, hτ⟩ := h.surj x₀ y₀ hE
      exact ⟨τ, congrArg Prod.fst hτ, congrArg Prod.snd hτ⟩).comp e.injective
  have he : ∀ a, e (puncturedRingEquiv E a) = a := fun a ↦ (puncturedRingEquiv E).symm_apply_apply a
  set yP : A := puncturedRingEquiv E (FEt.yA E)
  have hx : ∀ τ : ℍ, ι₀ (xP E) τ = (π τ).1 := fun τ ↦ by
    simp only [ι₀, xP, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom, he]
    exact FEt.coordFun_xA h.mem τ
  have hy : ∀ τ : ℍ, ι₀ yP τ = (π τ).2 := fun τ ↦ by
    simp only [ι₀, yP, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom, he]
    exact FEt.coordFun_yA h.mem τ
  have hxy : ∀ χ χ' : A →ₐ[ℂ] ℂ, χ (xP E) = χ' (xP E) → χ yP = χ' yP → χ = χ' := by
    intro χ χ' h1 h2
    have := FEt.algHom_ext_coord (χ := χ.comp e.symm.toAlgHom) (χ' := χ'.comp e.symm.toAlgHom)
      h1 h2
    ext a
    have := congrArg (fun φ : E.toAffine.CoordinateRing →ₐ[ℂ] ℂ ↦ φ (e a)) this
    simpa using this
  have hW : ∀ χ : A →ₐ[ℂ] ℂ, E.toAffine.Equation (χ (xP E)) (χ yP) := fun χ ↦
    FEt.equation_coord (χ.comp e.symm.toAlgHom)
  have hhol : ∀ a, Unif.HolH (ι₀ a) := fun a ↦
    FEt.holH_coordFun h.mem (holH_fst h) (holH_snd h) (e a)
  set n := Module.finrank A B
  have hcount : ∀ τ, Nat.card (FEt.Over B (FEt.pt ι₀ τ)) = n := fun τ ↦
    card_points_over het (FEt.pt ι₀ τ)
  have hloc : ∀ τ, LocPres ι₀ (B := B) n τ := fun τ ↦
    exists_locPres (AffOrbicurve.punctured E).not_isField het (FEt.pt ι₀ τ)
  have hgrowth : ∀ a, FEt.PolyBdd (fun τ ↦ (π τ).1) fun τ ↦ ‖ι₀ a τ‖ := fun a ↦
    FEt.polyBdd_coordFun h.mem (e a)
  have hpoly : ∀ g : ℍ → ℂ, Unif.HolH g →
      (∀ γ ∈ Subgroup.closure
          {Generators.A (unifOf (Generators.Lt t)), Generators.B (unifOf (Generators.Lt t))},
        ∀ τ, g (γ • τ) = g τ) →
      FEt.PolyBdd (fun τ ↦ (π τ).1) (fun τ ↦ ‖g τ‖) → ∃ a, ∀ τ, ι₀ a τ = g τ := by
    intro g hg hinv hb
    obtain ⟨a, ha⟩ := FEt.exists_coord_of_invariant hC hg hinv hb
    exact ⟨e.symm a, fun τ ↦ by simpa [ι₀] using ha τ⟩
  have hn : 0 < n := Module.finrank_pos
  have hne : Nonempty (FEt.Over B (FEt.pt ι₀ UpperHalfPlane.I)) := by
    exact (Nat.card_pos_iff.mp (by rw [hcount]; exact hn)).1
  obtain ⟨ψ₀⟩ := hne
  obtain ⟨ι, hι, -, hιh⟩ := FEt.exists_isLift hhol hcount hloc UpperHalfPlane.I ψ₀
  obtain ⟨g, hg⟩ := FEt.exists_mobius h hx hy hxy hW hhol hcount hloc hgrowth hpoly hinj σ hι hιh
  have hgc := mobius_mem_commensurator h hx hy hxy hhol hcount hloc σ hι hg
  have hcore : AdmitsCore (Subgroup.closure
      {Generators.A (unifOf (Generators.Lt t)), Generators.B (unifOf (Generators.Lt t))}) := by
    by_contra hno
    exact s1NonExceptional E _ _ ⟨π, h3, h4, h5, h6⟩ hj
      ((canLift27_group_unconditional htr htrA).mp hno)
  rcases r3 h hcore with hr | hr | hr
  · refine sub_eq_zero.mp (FEt.IsLift.eq_zero hinj hι fun τ ↦ ?_)
    obtain ⟨ψ, hψ⟩ := hι.pt τ
    rw [← hψ, map_sub, hψ, hg, hι.apply_algebraMap, hι.apply_algebraMap, hx, hx]
    exact sub_eq_zero.mpr (hr g hgc τ)
  · exact absurd hr (hj 0 (by simp [AffOrbicurve.excJ]) |> fun h ↦ by simpa using h)
  · exact absurd hr (hj 1728 (by simp [AffOrbicurve.excJ]) |> fun h ↦ by simpa using h)

end FixX

end OrbicurveCores.U2
