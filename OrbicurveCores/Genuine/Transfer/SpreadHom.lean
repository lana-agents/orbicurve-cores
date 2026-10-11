/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.Spread
import OrbicurveCores.Genuine.Transfer.EllipticHom

/-!
# T1b: models of the morphisms `x ∘ p`, `φ`, `q`

Let `E₀` be an elliptic curve over `k₀ ⊆ k`, `Z` an affine orbicurve over `k` with a model
`A₀` (`e : k ⊗ A₀ ≅ A_Z`, multiplicities defined over `k₀`), `Z₀` the model orbicurve.

* `modelHemi`: a finite étale `φ : Z → (E_k ∖ 0)/±1` with `φ(x) ∈ ρ(A₀)` descends to
  `φ₀ : Z₀ → (E₀ ∖ 0)/±1`.
-/

open TensorProduct AffOrbicurve Polynomial

universe u v

namespace OrbicurveCores.Transfer

variable {k₀ : Type u} [Field k₀] [CharZero k₀] {k : Type (max u v)} [Field k] [CharZero k]
  [Algebra k₀ k] (E₀ : WeierstrassCurve k₀) [E₀.IsElliptic]
  {Z : AffOrbicurve k} {A₀ : Type u} [CommRing A₀] [Algebra k₀ A₀] [Algebra.FiniteType k₀ A₀]
  (e : k ⊗[k₀] A₀ ≃ₐ[k] Z.A) (hZ : MultDefinedOver Z e)

omit [CharZero k₀] [CharZero k] in
include e in
/-- Lying over for the model, in the form used by `homOfModels`. -/
lemma lie_model (w₀ : Ideal A₀) (hw₀ : w₀.IsMaximal) :
    ∃ W : Ideal (k ⊗[k₀] A₀), W.IsMaximal ∧
      W.comap (Algebra.TensorProduct.includeRight : A₀ →ₐ[k₀] k ⊗[k₀] A₀) = w₀ := by
  obtain ⟨w, hw, hww⟩ := exists_isMaximal_comap_eq Z e w₀ hw₀
  refine ⟨w.comap e, Ideal.comap_isMaximal_of_surjective _ e.surjective, ?_⟩
  rw [← hww]
  rfl

section Hemi

variable (φ : Hom Z (hemi (E₀.baseChange k))) (f₀ : A₀)
  (hf₀ : rhoM Z e f₀ = φ.f X)

/-- The model of `φ`: `x ↦ f₀`. -/
noncomputable def gHemi : (hemi E₀).A →ₐ[k₀] (modelOrbicurve Z e hZ).A :=
  (Polynomial.aeval f₀ : k₀[X] →ₐ[k₀] A₀)

omit [E₀.IsElliptic] in
include hf₀ in
lemma rhoM_gHemi (p : k₀[X]) :
    rhoM Z e (gHemi E₀ e hZ f₀ p) = φ.f (p.map (algebraMap k₀ k)) := by
  have h : (rhoM Z e).comp (Polynomial.aeval f₀ : k₀[X] →ₐ[k₀] A₀).toRingHom =
      (φ.f : (hemi (E₀.baseChange k)).A →+* Z.A).comp
        (Polynomial.mapRingHom (algebraMap k₀ k)) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change e ((1 : k) ⊗ₜ[k₀] Polynomial.aeval f₀ (C c)) =
        φ.f (Polynomial.map (algebraMap k₀ k) (C c))
      rw [Polynomial.aeval_C, Polynomial.map_C, Algebra.algebraMap_eq_smul_one,
        ← TensorProduct.smul_tmul]
      have h1 : ((c • (1 : k)) ⊗ₜ[k₀] (1 : A₀)) =
          algebraMap k (k ⊗[k₀] A₀) (algebraMap k₀ k c) := by
        rw [Algebra.algebraMap_eq_smul_one c]; rfl
      rw [h1, AlgEquiv.commutes]
      exact (φ.f.commutes (algebraMap k₀ k c)).symm
    · change e ((1 : k) ⊗ₜ[k₀] Polynomial.aeval f₀ X) = φ.f (Polynomial.map _ X)
      rw [Polynomial.aeval_X, Polynomial.map_X]
      exact hf₀
  exact congrArg (fun f ↦ f p) h

omit [E₀.IsElliptic] in
include hf₀ in
lemma gHemi_injective : Function.Injective (gHemi E₀ e hZ f₀) := by
  intro p₁ p₂ h
  have := congrArg (rhoM Z e) h
  rw [rhoM_gHemi E₀ e hZ φ f₀ hf₀, rhoM_gHemi E₀ e hZ φ f₀ hf₀] at this
  exact Polynomial.map_injective _ (algebraMap k₀ k).injective (φ.injective this)

omit [E₀.IsElliptic] [CharZero k] in
lemma isDomain_tensor_hemi : IsDomain (k ⊗[k₀] (hemi E₀).A) :=
  (polyEquivTensor' k₀ k).symm.toMulEquiv.isDomain

omit [E₀.IsElliptic] [CharZero k] in
lemma bot_mem_minimalPrimes_hemi :
    (⊥ : Ideal (k ⊗[k₀] (hemi E₀).A)) ∈ minimalPrimes (k ⊗[k₀] (hemi E₀).A) :=
  @bot_mem_minimalPrimes_of_isDomain _ _ (isDomain_tensor_hemi E₀)

omit [E₀.IsElliptic] in
include hf₀ in
lemma comap_bcMap_gHemi :
    (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Z e hZ).A)).comap (bcMap k (gHemi E₀ e hZ f₀)) = ⊥ := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨fun h ↦ bcMap_injective _ (gHemi_injective E₀ e hZ φ f₀ hf₀) (h.trans (map_zero _).symm),
    fun h ↦ by rw [h, map_zero]⟩

include hf₀ in
lemma hsq_hemi (h𝔮le : (⊥ : Ideal (k ⊗[k₀] (hemi E₀).A)) ≤
      (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Z e hZ).A)).comap (bcMap k (gHemi E₀ e hZ f₀)))
    (y : (hemi (E₀.baseChange k)).A) :
    (iotaModel Z e hZ).f (φ.f y) = Ideal.quotientMapₐ ⊥ (bcMap k (gHemi E₀ e hZ f₀)) h𝔮le
      ((iotaH E₀ ⊥ (bot_mem_minimalPrimes_hemi E₀)).f y) := by
  have h : ((iotaModel Z e hZ).f.comp φ.f : k[X] →ₐ[k]
      (bcComp k (modelOrbicurve Z e hZ) ⊥ (bot_mem_minimalPrimes_model Z e hZ)).A) =
      ((Ideal.quotientMapₐ ⊥ (bcMap k (gHemi E₀ e hZ f₀)) h𝔮le).comp
        (iotaH E₀ ⊥ (bot_mem_minimalPrimes_hemi E₀)).f : k[X] →ₐ[k] _) := by
    apply Polynomial.algHom_ext
    change alphaModel Z e hZ (φ.f X) =
      Ideal.quotientMapₐ ⊥ (bcMap k (gHemi E₀ e hZ f₀)) h𝔮le
        (alphaH E₀ ⊥ (bot_mem_minimalPrimes_hemi E₀) X)
    rw [← hf₀, alphaModel_rhoM, alphaH_X, Ideal.quotient_map_mkₐ, bcMap_tmul]
    change _ = Ideal.Quotient.mk _ ((1 : k) ⊗ₜ[k₀] Polynomial.aeval f₀ X)
    rw [Polynomial.aeval_X]
  exact congrArg (fun f ↦ f y) h

/-- **The model of `φ : Z → (E_k ∖ 0)/±1`.** -/
noncomputable def modelHemi : Hom (modelOrbicurve Z e hZ) (hemi E₀) :=
  haveI : IsDomain (k ⊗[k₀] (modelOrbicurve Z e hZ).A) := isDomain_tensor_model Z e
  homOfModels' φ (gHemi E₀ e hZ f₀) ⊥ (bot_mem_minimalPrimes_hemi E₀)
    (comap_bcMap_gHemi E₀ e hZ φ f₀ hf₀) (iotaModel Z e hZ)
    (iotaH E₀ ⊥ (bot_mem_minimalPrimes_hemi E₀)) (alphaModel_bijective Z e hZ)
    (alphaH_bijective E₀ ⊥ (bot_mem_minimalPrimes_hemi E₀))
    (hsq_hemi E₀ e hZ φ f₀ hf₀ _) (gHemi_injective E₀ e hZ φ f₀ hf₀) (lie_model e)

lemma rhoM_modelHemi_X : rhoM Z e ((modelHemi E₀ e hZ φ f₀ hf₀).f X) = φ.f X := by
  rw [modelHemi, homOfModels'_f]
  change rhoM Z e (Polynomial.aeval f₀ X) = _
  rw [Polynomial.aeval_X, hf₀]

end Hemi

end OrbicurveCores.Transfer
