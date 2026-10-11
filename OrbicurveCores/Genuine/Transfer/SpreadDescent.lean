/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.SpreadRigid

/-!
# T1b/T3: models of morphisms `q : Z → Y`, and descent over every field of characteristic `0`

* `modelHom`: a finite étale `q : Z → Y` with `q(ρ_Y(B₀)) ⊆ ρ_Z(A₀)` descends to the models;
* `multDefinedOver_of_gens`: multiplicities are defined over a model containing generators of
  the special maximal ideals;
* `hemiDescends_of_complex`: descent over every field of characteristic `0`.
-/

open TensorProduct AffOrbicurve Polynomial

universe u v

namespace OrbicurveCores.Transfer

section ModelHom

variable {k₀ : Type u} [Field k₀] {k : Type (max u v)} [Field k] [Algebra k₀ k]
  {Z Y : AffOrbicurve k} {A₀ B₀ : Type u} [CommRing A₀] [Algebra k₀ A₀]
  [Algebra.FiniteType k₀ A₀] [CommRing B₀] [Algebra k₀ B₀] [Algebra.FiniteType k₀ B₀]
  (eZ : k ⊗[k₀] A₀ ≃ₐ[k] Z.A) (eY : k ⊗[k₀] B₀ ≃ₐ[k] Y.A)

omit [Algebra.FiniteType k₀ A₀] in
/-- `k`-algebra maps out of `A_Z` agreeing on `ρ(A₀)` agree. -/
lemma eq_of_eq_rhoM {D : Type*} [Ring D] [Algebra k D] (F₁ F₂ : Z.A →ₐ[k] D)
    (h : ∀ a, F₁ (rhoM Z eZ a) = F₂ (rhoM Z eZ a)) (z : Z.A) : F₁ z = F₂ z := by
  obtain ⟨t, rfl⟩ := eZ.surjective z
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c a =>
    have hc : c ⊗ₜ[k₀] a = c • ((1 : k) ⊗ₜ[k₀] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
    rw [hc, map_smul, map_smul, map_smul]
    exact congrArg (c • ·) (h a)
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]

variable (q : Hom Z Y) (h : ∀ b, ∃ a, rhoM Z eZ a = q.f (rhoM Y eY b))

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] in
include h in
lemma rhoM_choose (b : B₀) : rhoM Z eZ (h b).choose = q.f (rhoM Y eY b) := (h b).choose_spec

/-- The model `B₀ → A₀` of `q`. -/
noncomputable def liftModel : B₀ →ₐ[k₀] A₀ where
  toFun b := (h b).choose
  map_one' := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ 1
    rw [rhoM_choose, map_one, map_one, map_one])
  map_mul' a b := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ (_ * _)
    rw [rhoM_choose, map_mul (rhoM Z eZ), rhoM_choose, rhoM_choose, map_mul, map_mul])
  map_zero' := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ 0
    rw [rhoM_choose, map_zero, map_zero, map_zero])
  map_add' a b := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ (_ + _)
    rw [rhoM_choose, map_add (rhoM Z eZ), rhoM_choose, rhoM_choose, map_add, map_add])
  commutes' c := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ _
    rw [rhoM_choose, rhoM_algebraMap, rhoM_algebraMap, q.f.commutes])

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] in
lemma rhoM_liftModel (b : B₀) : rhoM Z eZ (liftModel eZ eY q h b) = q.f (rhoM Y eY b) :=
  rhoM_choose eZ eY q h b

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] in
lemma liftModel_injective : Function.Injective (liftModel eZ eY q h) := by
  intro a b hab
  have := congrArg (rhoM Z eZ) hab
  rw [rhoM_liftModel, rhoM_liftModel] at this
  exact modelMap_injective eY.toRingEquiv (q.injective this)

variable [CharZero k₀] (hZ : MultDefinedOver Z eZ) (hY : MultDefinedOver Y eY)

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] [CharZero k₀] in
lemma comap_bcMap_liftModel :
    (⊥ : Ideal (k ⊗[k₀] A₀)).comap (bcMap k (liftModel eZ eY q h)) = ⊥ := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨fun h' ↦ bcMap_injective _ (liftModel_injective eZ eY q h)
    (h'.trans (map_zero _).symm), fun h' ↦ by rw [h', map_zero]⟩

lemma hsq_model (hle : (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Y eY hY).A)) ≤
      (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Z eZ hZ).A)).comap
        (bcMap k (liftModel eZ eY q h)))
    (y : Y.A) : (iotaModel Z eZ hZ).f (q.f y) =
      Ideal.quotientMapₐ ⊥ (bcMap k (liftModel eZ eY q h)) hle ((iotaModel Y eY hY).f y) := by
  refine eq_of_eq_rhoM eY ((alphaModel Z eZ hZ).comp q.f)
    ((Ideal.quotientMapₐ ⊥ (bcMap k (liftModel eZ eY q h)) hle).comp (alphaModel Y eY hY))
    (fun b ↦ ?_) y
  change alphaModel Z eZ hZ (q.f (rhoM Y eY b)) =
    Ideal.quotientMapₐ ⊥ (bcMap k (liftModel eZ eY q h)) hle (alphaModel Y eY hY (rhoM Y eY b))
  rw [← rhoM_liftModel eZ eY q h, alphaModel_rhoM, alphaModel_rhoM]
  change _ = Ideal.Quotient.mk _ (bcMap k (liftModel eZ eY q h) ((1 : k) ⊗ₜ[k₀] b))
  rw [bcMap_tmul]

/-- **The model of `q : Z → Y`.** -/
noncomputable def modelHom : Hom (modelOrbicurve Z eZ hZ) (modelOrbicurve Y eY hY) :=
  haveI : IsDomain (k ⊗[k₀] (modelOrbicurve Z eZ hZ).A) := isDomain_tensor_model Z eZ
  homOfModels' q (liftModel eZ eY q h) ⊥ (bot_mem_minimalPrimes_model Y eY hY)
    (comap_bcMap_liftModel eZ eY q h) (iotaModel Z eZ hZ) (iotaModel Y eY hY)
    (alphaModel_bijective Z eZ hZ) (alphaModel_bijective Y eY hY)
    (hsq_model eZ eY q h hZ hY _) (liftModel_injective eZ eY q h) (lie_model eZ)

lemma rhoM_modelHom (b : B₀) :
    rhoM Z eZ ((modelHom eZ eY q h hZ hY).f b) = q.f (rhoM Y eY b) := by
  rw [modelHom, homOfModels'_f]
  exact rhoM_liftModel eZ eY q h b

end ModelHom

end OrbicurveCores.Transfer
