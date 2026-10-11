/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.SpreadHom
import OrbicurveCores.Genuine.Transfer.Descent
import OrbicurveCores.Genuine.Assembly
import OrbicurveCores.Genuine.Descent

/-!
# T3: rigidity over every field of characteristic `0`

* `hemiRigid_subfield`: over a subfield `k₀ ⊆ ℂ`, rigidity and descent follow from the core
  property over `ℂ` (T3a, `hemiRigid_of_isCoreOf_baseChange`);
* `hemiRigid_of_complex`: spreading out `E`, `Z`, `p`, `φ` to a subfield of `ℂ` (T1b) gives
  rigidity over every field of characteristic `0`.
-/

open TensorProduct AffOrbicurve Polynomial

universe u v

namespace OrbicurveCores.Transfer

/-- Weierstrass curves with coefficients in the image of `k₀` come from `k₀`. -/
lemma exists_weierstrass_model {k₀ k : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    (E : WeierstrassCurve k)
    (h : ({E.a₁, E.a₂, E.a₃, E.a₄, E.a₆} : Set k) ⊆ Set.range (algebraMap k₀ k)) :
    ∃ E₀ : WeierstrassCurve k₀, E₀.baseChange k = E := by
  obtain ⟨b₁, h₁⟩ := h (show E.a₁ ∈ _ by simp)
  obtain ⟨b₂, h₂⟩ := h (show E.a₂ ∈ _ by simp)
  obtain ⟨b₃, h₃⟩ := h (show E.a₃ ∈ _ by simp)
  obtain ⟨b₄, h₄⟩ := h (show E.a₄ ∈ _ by simp)
  obtain ⟨b₆, h₆⟩ := h (show E.a₆ ∈ _ by simp)
  exact ⟨⟨b₁, b₂, b₃, b₄, b₆⟩, by
    ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, h₁, h₂, h₃, h₄, h₆]⟩

lemma isElliptic_of_baseChange {k₀ k : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    (E₀ : WeierstrassCurve k₀) (h : (E₀.baseChange k).IsElliptic) : E₀.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff] at h ⊢
  change IsUnit (E₀.map (algebraMap k₀ k)).Δ at h
  rw [WeierstrassCurve.map_Δ] at h
  exact isUnit_iff_ne_zero.mpr fun h0 ↦ (isUnit_iff_ne_zero.mp h) (by rw [h0, map_zero])

lemma j_ne_of_baseChange {k₀ k : Type*} [Field k₀] [Field k] [CharZero k₀] [CharZero k]
    [Algebra k₀ k] (E₀ : WeierstrassCurve k₀) [E₀.IsElliptic] (c : ℚ)
    (h : (E₀.map (algebraMap k₀ k)).j ≠ (c : k)) : E₀.j ≠ (c : k₀) := by
  intro h0
  apply h
  rw [WeierstrassCurve.map_j, h0, map_ratCast]

/-- **Rigidity and descent over subfields of `ℂ`**, from the complex case (T3a). -/
theorem hemiRigid_subfield (h : HemiCoreComplexNonExc) (k₀ : Subfield ℂ)
    (E₀ : WeierstrassCurve k₀) [E₀.IsElliptic] (hj : ∀ c ∈ excJ, E₀.j ≠ (c : k₀)) :
    Genuine.HemiRigid E₀ ∧ Genuine.HemiDescends E₀ := by
  haveI : (E₀.baseChange ℂ).IsElliptic := inferInstanceAs (E₀.map (algebraMap k₀ ℂ)).IsElliptic
  have hcore := h (E₀.baseChange ℂ) fun c hc h' ↦ hj c hc (by
    apply (algebraMap k₀ ℂ).injective
    rw [map_ratCast, ← h']
    exact (WeierstrassCurve.map_j E₀ (algebraMap k₀ ℂ)).symm)
  exact ⟨hemiRigid_of_isCoreOf_baseChange hcore, hemiDescends_of_isCoreOf_baseChange hcore⟩

/-- Trivial multiplicities are defined over every model. -/
lemma multDefinedOver_of_forall {k₀ : Type u} [Field k₀] {k : Type (max u v)} [Field k]
    [Algebra k₀ k] {Z : AffOrbicurve k} {A₀ : Type u} [CommRing A₀] [Algebra k₀ A₀] [Algebra.FiniteType k₀ A₀]
    (e : k ⊗[k₀] A₀ ≃ₐ[k] Z.A) (h : ∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1) :
    MultDefinedOver Z e :=
  ⟨fun w w' hw hw' _ ↦ (h w hw).trans (h w' hw').symm, fun w hw _ ↦ h w hw⟩

/-- **Rigidity over every field of characteristic `0`** (T3, rigidity half). -/
theorem hemiRigid_of_complex (h : HemiCoreComplexNonExc) {k : Type u} [Field k] [CharZero k]
    (E : WeierstrassCurve k) [E.IsElliptic] (hj : ∀ c ∈ excJ, E.j ≠ (c : k)) :
    Genuine.HemiRigid E := by
  intro Z p φ
  let s : Fin 3 → Z.A := ![p.f (Genuine.hemiMap E X), p.f (yA E), φ.f X]
  obtain ⟨m, r, P, hP⟩ := exists_presentation (k := k) s
  let S : Set k := P.coeffs ∪ {E.a₁, E.a₂, E.a₃, E.a₄, E.a₆}
  have hS : S.Finite := P.finite_coeffs.union (by simp)
  obtain ⟨k₀, ι, hι⟩ := exists_subfield_complex S hS
  letI : Algebra k₀ k := ι.toAlgebra
  obtain ⟨E₀, rfl⟩ := exists_weierstrass_model (k₀ := k₀) E
    (fun x hx ↦ hι (Set.mem_union_right _ hx))
  haveI : E₀.IsElliptic := isElliptic_of_baseChange (k := k) E₀ inferInstance
  obtain ⟨hR, -⟩ := hemiRigid_subfield h k₀ E₀ fun c hc ↦ j_ne_of_baseChange E₀ c (hj c hc)
  obtain ⟨A₀, _, _, _, e, hgen, -⟩ :=
    exists_model.{0, u} (k₀ := k₀) P fun x hx ↦ hι (Set.mem_union_left _ hx)
  obtain ⟨x₀, hx₀⟩ := hgen (Fin.castAdd m 0)
  obtain ⟨y₀, hy₀⟩ := hgen (Fin.castAdd m 1)
  obtain ⟨f₀, hf₀⟩ := hgen (Fin.castAdd m 2)
  rw [hP] at hx₀ hy₀ hf₀
  have hZ : MultDefinedOver Z e := multDefinedOver_of_forall.{0, u} e (Genuine.mult_eq_one_of_hom _ p)
  have h₀ := hR _ (modelPunctured (k := k) E₀ e hZ p x₀ y₀ hx₀ hy₀)
    (modelHemi (k := k) E₀ e hZ φ f₀ hf₀)
  have h₁ := congrArg (rhoM Z e) h₀
  rw [rhoM_modelHemi_X, rhoM_modelPunctured_x] at h₁
  exact h₁

end OrbicurveCores.Transfer
