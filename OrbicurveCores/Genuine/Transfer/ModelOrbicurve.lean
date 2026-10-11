/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Transfer.ModelHom

/-!
# T1b: models of affine orbicurves

Let `Z` be an affine orbicurve over `k` and `A₀` a model of its coordinate ring over a subfield
`k₀` (`e : k ⊗_{k₀} A₀ ≅ A_Z`). If the multiplicities of `Z` are *defined over `k₀`*
(maximal ideals with the same contraction to `A₀` have the same multiplicity, and maximal ideals
contracting to `0` have multiplicity `1`), then `A₀` with the induced multiplicities is an affine
orbicurve `modelOrbicurve` over `k₀`, and `k ⊗ A₀ ≅ A_Z` is an isomorphism of affine orbicurves
`iotaModel : Hom (k ⊗ Z₀) Z`.
-/

open TensorProduct AffOrbicurve

universe u v

namespace OrbicurveCores.Transfer

variable {k₀ : Type u} [Field k₀] [CharZero k₀] {k : Type (max u v)} [Field k] [Algebra k₀ k]
  (Z : AffOrbicurve k) {A₀ : Type u} [CommRing A₀] [Algebra k₀ A₀] [Algebra.FiniteType k₀ A₀]
  (e : k ⊗[k₀] A₀ ≃ₐ[k] Z.A)

/-- The model map `A₀ → A_Z`. -/
noncomputable abbrev rhoM : A₀ →+* Z.A := modelMap e.toRingEquiv

omit [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
lemma rhoM_apply (a : A₀) : rhoM Z e a = e ((1 : k) ⊗ₜ a) := rfl

/-- Multiplicities defined over `k₀`. -/
def MultDefinedOver : Prop :=
  (∀ w w' : Ideal Z.A, w.IsMaximal → w'.IsMaximal → w.comap (rhoM Z e) = w'.comap (rhoM Z e) →
    Z.mult w = Z.mult w') ∧
  ∀ w : Ideal Z.A, w.IsMaximal → w.comap (rhoM Z e) = ⊥ → Z.mult w = 1

omit [CharZero k₀] in
include e in
lemma isDedekindDomain_model : IsDedekindDomain A₀ := by
  haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing k₀ A₀
  exact isDedekindDomain_of_model e.toRingEquiv

omit [CharZero k₀] in
/-- Lying over for maximal ideals of models. -/
lemma exists_isMaximal_comap_eq (w₀ : Ideal A₀) (hw₀ : w₀.IsMaximal) :
    ∃ w : Ideal Z.A, w.IsMaximal ∧ w.comap (rhoM Z e) = w₀ := by
  haveI := isDedekindDomain_model Z e
  letI := Algebra.TensorProduct.rightAlgebra (R := k₀) (A := k) (B := A₀)
  haveI := faithfullyFlat_tensor (k := k) (A₀ := A₀) (k₀ := k₀)
  obtain ⟨W, hW, hlo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat
    (B := k ⊗[k₀] A₀) w₀
  have hWu : w₀ = W.under A₀ := hlo.over
  refine ⟨W.map e, ?_, ?_⟩
  · have hP : (W.map e).IsPrime := Ideal.map_isPrime_of_equiv e
    refine hP.isMaximal fun h ↦ ?_
    have hW0 : W = ⊥ := by
      have := congrArg (Ideal.comap e) h
      rwa [Ideal.comap_map_of_bijective e e.bijective, Ideal.comap_bot_of_injective e e.injective]
        at this
    apply Ring.ne_bot_of_isMaximal_of_not_isField hw₀ (not_isField_of_model e.toRingEquiv
      Z.not_isField)
    rw [hWu, hW0]
    ext a
    simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h ↦ includeRight_injective' (k := k) (h.trans (map_zero _).symm),
      fun h ↦ by rw [h, map_zero]⟩
  · rw [hWu]
    ext a
    simp only [Ideal.mem_comap, Ideal.under, rhoM_apply]
    rw [Ideal.mem_map_of_equiv]
    refine ⟨fun ⟨b, hb, hbe⟩ ↦ ?_, fun h ↦ ⟨_, h, rfl⟩⟩
    have := e.injective hbe
    subst this
    exact hb

omit [CharZero k₀] in
/-- The multiplicities of the model. -/
noncomputable def modelMult (w₀ : Ideal A₀) : ℕ :=
  open Classical in
  if h : ∃ w : Ideal Z.A, w.IsMaximal ∧ w.comap (rhoM Z e) = w₀ then Z.mult h.choose else 1

omit [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
lemma modelMult_comap (hZ : MultDefinedOver Z e) (w : Ideal Z.A) (hw : w.IsMaximal) :
    modelMult Z e (w.comap (rhoM Z e)) = Z.mult w := by
  have h : ∃ w' : Ideal Z.A, w'.IsMaximal ∧ w'.comap (rhoM Z e) = w.comap (rhoM Z e) :=
    ⟨w, hw, rfl⟩
  rw [modelMult, dif_pos h]
  exact hZ.1 _ _ h.choose_spec.1 hw h.choose_spec.2

omit [CharZero k₀] in
/-- **The model of an affine orbicurve** whose multiplicities are defined over `k₀`. -/
noncomputable def modelOrbicurve (hZ : MultDefinedOver Z e) : AffOrbicurve k₀ where
  A := A₀
  isDomain := (isDedekindDomain_model Z e).toIsDomain
  isDedekindDomain := isDedekindDomain_model Z e
  not_isField := not_isField_of_model e.toRingEquiv Z.not_isField
  mult := modelMult Z e
  mult_pos w₀ hw₀ := by
    obtain ⟨w, hw, rfl⟩ := exists_isMaximal_comap_eq Z e w₀ hw₀
    rw [modelMult_comap Z e hZ w hw]
    exact Z.mult_pos w hw
  finite_mult := by
    refine (Z.finite_mult.image (Ideal.comap (rhoM Z e))).subset ?_
    rintro w₀ ⟨hw₀, h1⟩
    obtain ⟨w, hw, rfl⟩ := exists_isMaximal_comap_eq Z e w₀ hw₀
    rw [modelMult_comap Z e hZ w hw] at h1
    exact ⟨w, ⟨hw, h1⟩, rfl⟩

omit [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
include e in
lemma isDomain_tensor_model : IsDomain (k ⊗[k₀] A₀) :=
  e.toRingEquiv.toMulEquiv.isDomain

variable (hZ : MultDefinedOver Z e)

omit [CharZero k₀] in
lemma bot_mem_minimalPrimes_model :
    (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Z e hZ).A)) ∈
      minimalPrimes (k ⊗[k₀] (modelOrbicurve Z e hZ).A) :=
  @bot_mem_minimalPrimes_of_isDomain _ _ (isDomain_tensor_model Z e)

/-- The map `A_Z → k ⊗ A₀` of the model, as a map to the component. -/
noncomputable def alphaModel :
    Z.A →ₐ[k] (bcComp k (modelOrbicurve Z e hZ) ⊥ (bot_mem_minimalPrimes_model Z e hZ)).A :=
  (Ideal.Quotient.mkₐ k (⊥ : Ideal (k ⊗[k₀] A₀))).comp e.symm.toAlgHom

lemma alphaModel_bijective : Function.Bijective (alphaModel Z e hZ) := by
  change Function.Bijective ((Ideal.Quotient.mk (⊥ : Ideal (k ⊗[k₀] A₀))) ∘ e.symm)
  exact Function.Bijective.comp ⟨mk_bot_injective _, Ideal.Quotient.mk_surjective⟩
    e.symm.bijective

lemma alphaModel_rhoM (a : A₀) :
    alphaModel Z e hZ (rhoM Z e a) = Ideal.Quotient.mk ⊥ ((1 : k) ⊗ₜ[k₀] a) := by
  change Ideal.Quotient.mk ⊥ (e.symm (e _)) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- **`k ⊗ Z₀ ≅ Z`**, as a finite étale morphism of affine orbicurves. -/
noncomputable def iotaModel :
    Hom (bcComp k (modelOrbicurve Z e hZ) ⊥ (bot_mem_minimalPrimes_model Z e hZ)) Z where
  f := alphaModel Z e hZ
  injective := (alphaModel_bijective Z e hZ).1
  isIntegral := RingHom.isIntegral_of_surjective _ (alphaModel_bijective Z e hZ).2
  etale W hW := by
    haveI := hW.isPrime
    rw [ramificationIdx_eq_one_of_bijective _ (alphaModel_bijective Z e hZ) W, one_mul]
    have hc : (W.comap (Ideal.Quotient.mk ⊥)).comap
        (Algebra.TensorProduct.includeRight : A₀ →ₐ[k₀] k ⊗[k₀] A₀) =
        (W.comap (alphaModel Z e hZ)).comap (rhoM Z e) := by
      ext a
      simp only [Ideal.mem_comap]
      rw [alphaModel_rhoM]
      rfl
    have hWm : (W.comap (alphaModel Z e hZ)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ (alphaModel_bijective Z e hZ).2
    change compMult k (modelOrbicurve Z e hZ) ⊥ W = _
    unfold compMult
    split_ifs with h
    · exact (hZ.2 _ hWm (hc.symm.trans h)).symm
    · change modelMult Z e _ = _
      exact (congrArg (modelMult Z e) hc).trans (modelMult_comap Z e hZ _ hWm)

end OrbicurveCores.Transfer
