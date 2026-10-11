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

section Theta

variable {k₀' k' : Type*} [Field k₀'] [Field k'] [Algebra k₀' k'] (E₀' : WeierstrassCurve k₀')

/-- The map of Weierstrass coordinate rings `k₀'[E₀'] → k[E_k]`. -/
noncomputable abbrev coordMap :
    E₀'.toAffine.CoordinateRing →+* (E₀'.baseChange k').toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.map E₀' (algebraMap k₀' k')

lemma coordMap_injective : Function.Injective (coordMap (k' := k') E₀') :=
  WeierstrassCurve.Affine.CoordinateRing.map_injective (algebraMap k₀' k').injective

/-- The map of function fields `k₀'(E₀') → k(E_k)`. -/
noncomputable def fmap :
    E₀'.toAffine.FunctionField →+* (E₀'.baseChange k').toAffine.FunctionField :=
  IsFractionRing.map (coordMap_injective (k' := k') E₀')

lemma fmap_algebraMap (c : E₀'.toAffine.CoordinateRing) :
    fmap (k' := k') E₀' (algebraMap _ _ c) = algebraMap _ _ (coordMap (k' := k') E₀' c) := by
  unfold fmap IsFractionRing.map
  exact IsLocalization.map_eq _ c

lemma fmap_algebraMap_poly (g : k₀'[X]) :
    fmap (k' := k') E₀' (algebraMap k₀'[X] _ g) =
      algebraMap k'[X] _ (g.map (algebraMap k₀' k')) := by
  rw [IsScalarTower.algebraMap_apply k₀'[X] E₀'.toAffine.CoordinateRing,
    fmap_algebraMap, IsScalarTower.algebraMap_apply k'[X]
      (E₀'.baseChange k').toAffine.CoordinateRing]
  congr 1
  change WeierstrassCurve.Affine.CoordinateRing.map E₀' _ (AdjoinRoot.of _ g) = AdjoinRoot.of _ _
  rw [← AdjoinRoot.mk_C]
  change WeierstrassCurve.Affine.CoordinateRing.map E₀' _
    (WeierstrassCurve.Affine.CoordinateRing.mk E₀' (C g)) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_C]
  rfl

lemma isIntegral_fmap (a : puncturedRing E₀') :
    IsIntegral k'[X] (fmap (k' := k') E₀' (a : E₀'.toAffine.FunctionField)) := by
  obtain ⟨p, hp, hpa⟩ := a.2
  refine ⟨p.map (Polynomial.mapRingHom (algebraMap k₀' k')), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]
  rw [Polynomial.eval₂_eq_sum_range] at hpa
  have := congrArg (fmap (k' := k') E₀') hpa
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, RingHom.comp_apply, fmap_algebraMap_poly]
  rfl

/-- The map `k₀'[E₀' ∖ 0] → k[E_k ∖ 0]`. -/
noncomputable def theta : puncturedRing E₀' →+* puncturedRing (E₀'.baseChange k') where
  toFun a := ⟨fmap (k' := k') E₀' a, isIntegral_fmap E₀' a⟩
  map_one' := Subtype.ext (RingHom.map_one _)
  map_mul' a b := Subtype.ext (RingHom.map_mul (fmap (k' := k') E₀') a b)
  map_zero' := Subtype.ext (RingHom.map_zero _)
  map_add' a b := Subtype.ext (RingHom.map_add (fmap (k' := k') E₀') a b)

lemma theta_coe (a : puncturedRing E₀') :
    ((theta (k' := k') E₀' a : puncturedRing (E₀'.baseChange k')) :
      (E₀'.baseChange k').toAffine.FunctionField) = fmap E₀' (a : E₀'.toAffine.FunctionField) := rfl

lemma theta_injective : Function.Injective (theta (k' := k') E₀') := by
  intro a b h
  have := congrArg (fun z : puncturedRing (E₀'.baseChange k') ↦
    (z : (E₀'.baseChange k').toAffine.FunctionField)) h
  simp only [theta_coe] at this
  exact Subtype.ext ((fmap (k' := k') E₀').injective this)

lemma theta_kappa (c : E₀'.toAffine.CoordinateRing) :
    theta (k' := k') E₀' (kappa E₀' c) = kappa (E₀'.baseChange k') (coordMap (k' := k') E₀' c) := by
  apply Subtype.ext
  rw [theta_coe]
  change fmap (k' := k') E₀' (algebraMap _ _ (kappa E₀' c)) =
    algebraMap _ _ (kappa (E₀'.baseChange k') _)
  rw [algebraMap_kappa, algebraMap_kappa, fmap_algebraMap]

/-- Ring maps out of `k[E ∖ 0]` into a domain, injective, agreeing on the Weierstrass coordinate
ring, agree. -/
lemma eq_of_eq_kappa {D : Type*} [CommRing D] [IsDomain D] (f₁ f₂ : puncturedRing E₀' →+* D)
    (hf₁ : Function.Injective f₁) (h : ∀ c, f₁ (kappa E₀' c) = f₂ (kappa E₀' c))
    (y : puncturedRing E₀') : f₁ y = f₂ y := by
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective
    (A := E₀'.toAffine.CoordinateRing) (y : E₀'.toAffine.FunctionField)
  have hκ := kappa_eq_mul E₀' hd hcd
  have hd0 : f₁ (kappa E₀' d) ≠ 0 := by
    intro h0
    have h1 : kappa E₀' d = 0 := hf₁ (h0.trans (map_zero f₁).symm)
    have h2 := congrArg (fun z : puncturedRing E₀' ↦ (z : E₀'.toAffine.FunctionField)) h1
    simp only [ZeroMemClass.coe_zero] at h2
    change algebraMap _ _ (kappa E₀' d) = 0 at h2
    rw [algebraMap_kappa] at h2
    exact nonZeroDivisors.ne_zero hd
      ((IsFractionRing.injective _ E₀'.toAffine.FunctionField) (h2.trans (map_zero _).symm))
  apply mul_left_cancel₀ hd0
  have e1 := congrArg f₁ hκ
  have e2 := congrArg f₂ hκ
  rw [map_mul] at e1 e2
  rw [← e1, h c, e2, h d]

end Theta

section Punctured
variable (p : Hom Z (punctured (E₀.baseChange k))) (x₀ y₀ : A₀)
  (hx₀ : rhoM Z e x₀ = p.f (Genuine.hemiMap (E₀.baseChange k) X))
  (hy₀ : rhoM Z e y₀ = p.f (yA (E₀.baseChange k)))

include hx₀ in
omit [E₀.IsElliptic] [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
lemma rhoM_aeval_x (g : k₀[X]) :
    rhoM Z e (Polynomial.aeval x₀ g) =
      p.f (algebraMap k[X] (puncturedRing (E₀.baseChange k)) (g.map (algebraMap k₀ k))) := by
  induction g using Polynomial.induction_on with
  | C c =>
    rw [Polynomial.aeval_C, Polynomial.map_C, rhoM_apply, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul]
    have h1 : ((c • (1 : k)) ⊗ₜ[k₀] (1 : A₀)) =
        algebraMap k (k ⊗[k₀] A₀) (algebraMap k₀ k c) := by
      rw [Algebra.algebraMap_eq_smul_one c]; rfl
    rw [h1, AlgEquiv.commutes]
    exact (p.f.commutes (algebraMap k₀ k c)).symm
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, Polynomial.map_add, map_add]
    exact (map_add p.f _ _).symm
  | monomial n c h =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, h, Polynomial.aeval_X, hx₀,
      Polynomial.map_mul (p := C c * X ^ n), Polynomial.map_X, map_mul]
    exact (map_mul p.f _ _).symm

include hx₀ hy₀ in
omit [E₀.IsElliptic] [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
lemma rhoM_eval₂ (q : k₀[X][X]) :
    rhoM Z e (q.eval₂ (Polynomial.aeval x₀ : k₀[X] →ₐ[k₀] A₀).toRingHom y₀) =
      p.f ((q.map (Polynomial.mapRingHom (algebraMap k₀ k))).eval₂
        (algebraMap k[X] (puncturedRing (E₀.baseChange k))) (yA (E₀.baseChange k))) := by
  induction q using Polynomial.induction_on with
  | C g =>
    rw [Polynomial.eval₂_C, Polynomial.map_C, Polynomial.eval₂_C]
    exact rhoM_aeval_x E₀ e p x₀ hx₀ g
  | add f g hf hg =>
    rw [Polynomial.eval₂_add, map_add, hf, hg, Polynomial.map_add, Polynomial.eval₂_add]
    exact (map_add p.f _ _).symm
  | monomial n g h =>
    rw [pow_succ, ← mul_assoc, Polynomial.eval₂_mul, map_mul, h, Polynomial.eval₂_X, hy₀,
      Polynomial.map_mul (p := C g * X ^ n), Polynomial.map_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_X]
    exact (map_mul p.f _ _).symm

include hx₀ hy₀ in
omit [E₀.IsElliptic] [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
lemma eval₂_x₀_y₀ :
    E₀.toAffine.polynomial.eval₂ (Polynomial.aeval x₀ : k₀[X] →ₐ[k₀] A₀).toRingHom y₀ = 0 := by
  have hinj := modelMap_injective e.toRingEquiv
  apply hinj
  change rhoM Z e _ = rhoM Z e 0
  rw [rhoM_eval₂ E₀ e p x₀ y₀ hx₀ hy₀, map_zero]
  have hW : E₀.toAffine.polynomial.map (Polynomial.mapRingHom (algebraMap k₀ k)) =
      (E₀.baseChange k).toAffine.polynomial :=
    (WeierstrassCurve.Affine.map_polynomial (W := E₀) (f := algebraMap k₀ k)).symm
  rw [hW]
  have h0 := eval₂_yA (E₀.baseChange k)
  convert map_zero p.f using 2
  exact h0

/-- `k₀[E₀] → A₀`, `x ↦ x₀`, `y ↦ y₀`. -/
noncomputable def psi₀ : E₀.toAffine.CoordinateRing →+* A₀ :=
  AdjoinRoot.lift (Polynomial.aeval x₀ : k₀[X] →ₐ[k₀] A₀).toRingHom y₀
    (eval₂_x₀_y₀ E₀ e p x₀ y₀ hx₀ hy₀)

omit [E₀.IsElliptic] [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
lemma rhoM_psi₀ (c : E₀.toAffine.CoordinateRing) :
    rhoM Z e (psi₀ E₀ e p x₀ y₀ hx₀ hy₀ c) =
      p.f (kappa (E₀.baseChange k) (coordMap (k' := k) E₀ c)) := by
  induction c using AdjoinRoot.induction_on with
  | ih q =>
    rw [psi₀, AdjoinRoot.lift_mk, rhoM_eval₂ E₀ e p x₀ y₀ hx₀ hy₀]
    congr 1
    change _ = kappa (E₀.baseChange k) (WeierstrassCurve.Affine.CoordinateRing.map E₀ _
      (WeierstrassCurve.Affine.CoordinateRing.mk E₀ q))
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
    change _ = kappa (E₀.baseChange k) (AdjoinRoot.mk _ _)
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply]
    rfl

omit [E₀.IsElliptic] [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
include hx₀ hy₀ in
/-- **The values of `p ∘ θ` are defined over `k₀`.** -/
lemma mem_range_theta (a : puncturedRing E₀) :
    p.f (theta (k' := k) E₀ a) ∈ (rhoM Z e).range := by
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective
    (A := E₀.toAffine.CoordinateRing) (a : E₀.toAffine.FunctionField)
  have hκ := kappa_eq_mul E₀ hd hcd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hw : psi₀ E₀ e p x₀ y₀ hx₀ hy₀ d ≠ 0 := by
    intro h0
    have := rhoM_psi₀ E₀ e p x₀ y₀ hx₀ hy₀ d
    rw [h0, map_zero] at this
    have h1 : kappa (E₀.baseChange k) (coordMap (k' := k) E₀ d) = 0 :=
      p.injective (this.symm.trans (map_zero p.f).symm)
    have h2 := congrArg (fun z : puncturedRing (E₀.baseChange k) ↦
      (z : (E₀.baseChange k).toAffine.FunctionField)) h1
    simp only [ZeroMemClass.coe_zero] at h2
    change algebraMap _ _ (kappa (E₀.baseChange k) _) = 0 at h2
    rw [algebraMap_kappa] at h2
    have h3 : coordMap (k' := k) E₀ d = 0 :=
      (IsFractionRing.injective _ _) (h2.trans (map_zero _).symm)
    exact hd0 (coordMap_injective E₀ (h3.trans (map_zero _).symm))
  refine mem_range_of_mul_mem_range e.toRingEquiv hw ⟨psi₀ E₀ e p x₀ y₀ hx₀ hy₀ c, ?_⟩
  change rhoM Z e _ = _ * rhoM Z e _
  rw [rhoM_psi₀, rhoM_psi₀, ← theta_kappa, ← theta_kappa, hκ, map_mul, mul_comm]
  exact map_mul p.f _ _

/-- The model of `p`, as a ring map: `ρ⁻¹ ∘ p ∘ θ`. -/
noncomputable def gPunctR : puncturedRing E₀ →+* A₀ :=
  (RingEquiv.ofBijective (rhoM Z e).rangeRestrict
      ⟨fun _ _ h ↦ modelMap_injective e.toRingEquiv (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩).symm.toRingHom.comp
    ((p.f.toRingHom.comp (theta (k' := k) E₀)).codRestrict _
      (mem_range_theta E₀ e p x₀ y₀ hx₀ hy₀))

omit [E₀.IsElliptic] [CharZero k₀] [Algebra.FiniteType k₀ A₀] in
lemma rhoM_gPunctR (a : puncturedRing E₀) :
    rhoM Z e (gPunctR E₀ e p x₀ y₀ hx₀ hy₀ a) = p.f (theta (k' := k) E₀ a) := by
  set G := RingEquiv.ofBijective (rhoM Z e).rangeRestrict
      ⟨fun _ _ h ↦ modelMap_injective e.toRingEquiv (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  have h := G.apply_symm_apply ⟨p.f (theta (k' := k) E₀ a), mem_range_theta E₀ e p x₀ y₀ hx₀ hy₀ a⟩
  exact congrArg Subtype.val h

omit [CharZero k₀] [CharZero k] [Algebra.FiniteType k₀ A₀] in
/-- `ρ ∘ (k₀ → A₀) = (k → A_Z) ∘ (k₀ → k)`. -/
lemma rhoM_algebraMap (c : k₀) :
    rhoM Z e (algebraMap k₀ A₀ c) = algebraMap k Z.A (algebraMap k₀ k c) := by
  rw [rhoM_apply, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
  have h1 : ((c • (1 : k)) ⊗ₜ[k₀] (1 : A₀)) =
      algebraMap k (k ⊗[k₀] A₀) (algebraMap k₀ k c) := by
    rw [Algebra.algebraMap_eq_smul_one c]; rfl
  rw [h1, AlgEquiv.commutes]

omit [CharZero k₀] [CharZero k] [E₀.IsElliptic] in
lemma theta_algebraMap (c : k₀) :
    theta (k' := k) E₀ (algebraMap k₀ (puncturedRing E₀) c) =
      algebraMap k (puncturedRing (E₀.baseChange k)) (algebraMap k₀ k c) := by
  apply Subtype.ext
  rw [theta_coe]
  change fmap (k' := k) E₀ (algebraMap k₀ E₀.toAffine.FunctionField c) =
    algebraMap k (E₀.baseChange k).toAffine.FunctionField (algebraMap k₀ k c)
  rw [IsScalarTower.algebraMap_apply k₀ k₀[X] E₀.toAffine.FunctionField, fmap_algebraMap_poly,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Polynomial.map_C]
  change algebraMap k[X] _ (algebraMap k k[X] _) = _
  rw [← IsScalarTower.algebraMap_apply]

omit [E₀.IsElliptic] in
lemma theta_hemiMap (g : k₀[X]) :
    theta (k' := k) E₀ (Genuine.hemiMap E₀ g) =
      Genuine.hemiMap (E₀.baseChange k) (g.map (algebraMap k₀ k)) := by
  apply Subtype.ext
  rw [theta_coe]
  exact fmap_algebraMap_poly E₀ g

/-- **The model of `p : Z → E_k ∖ 0`**, as a `k₀`-algebra map. -/
noncomputable def gPunct : (punctured E₀).A →ₐ[k₀] (modelOrbicurve Z e hZ).A :=
  AlgHom.mk (gPunctR E₀ e p x₀ y₀ hx₀ hy₀) fun c ↦ modelMap_injective e.toRingEquiv (by
    rw [← (Genuine.hemiMap E₀).commutes c]
    change rhoM Z e (gPunctR E₀ e p x₀ y₀ hx₀ hy₀ (Genuine.hemiMap E₀ (algebraMap k₀ k₀[X] c))) =
      rhoM Z e (algebraMap k₀ A₀ c)
    rw [rhoM_gPunctR]
    refine (congrArg p.f (theta_hemiMap E₀ (algebraMap k₀ k₀[X] c))).trans ?_
    rw [rhoM_algebraMap, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Polynomial.map_C]
    exact (congrArg p.f ((Genuine.hemiMap (E₀.baseChange k)).commutes (algebraMap k₀ k c))).trans
      (p.f.commutes _))

omit [E₀.IsElliptic] in
lemma rhoM_gPunct (a : puncturedRing E₀) :
    rhoM Z e (gPunct E₀ e hZ p x₀ y₀ hx₀ hy₀ a) = p.f (theta (k' := k) E₀ a) :=
  rhoM_gPunctR E₀ e p x₀ y₀ hx₀ hy₀ a

omit [E₀.IsElliptic] in
lemma gPunct_injective : Function.Injective (gPunct E₀ e hZ p x₀ y₀ hx₀ hy₀) := by
  intro a b h
  have := congrArg (rhoM Z e) h
  rw [rhoM_gPunct, rhoM_gPunct] at this
  exact theta_injective E₀ (p.injective this)

omit [E₀.IsElliptic] in
include e hZ p x₀ y₀ hx₀ hy₀ in
lemma isDomain_tensor_punctured : IsDomain (k ⊗[k₀] (punctured E₀).A) := by
  haveI : IsDomain (k ⊗[k₀] (modelOrbicurve Z e hZ).A) := isDomain_tensor_model Z e
  exact Function.Injective.isDomain (bcMap k (gPunct E₀ e hZ p x₀ y₀ hx₀ hy₀)).toRingHom
    (bcMap_injective _ (gPunct_injective E₀ e hZ p x₀ y₀ hx₀ hy₀))

omit [E₀.IsElliptic] in
include e hZ p x₀ y₀ hx₀ hy₀ in
lemma bot_mem_minimalPrimes_punctured :
    (⊥ : Ideal (k ⊗[k₀] (punctured E₀).A)) ∈ minimalPrimes (k ⊗[k₀] (punctured E₀).A) :=
  @bot_mem_minimalPrimes_of_isDomain _ _ (isDomain_tensor_punctured E₀ e hZ p x₀ y₀ hx₀ hy₀)

omit [E₀.IsElliptic] in
lemma comap_bcMap_gPunct :
    (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Z e hZ).A)).comap
      (bcMap k (gPunct E₀ e hZ p x₀ y₀ hx₀ hy₀)) = ⊥ := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨fun h ↦ bcMap_injective _ (gPunct_injective E₀ e hZ p x₀ y₀ hx₀ hy₀)
    (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩

omit [E₀.IsElliptic] in
lemma gPunct_x : gPunct E₀ e hZ p x₀ y₀ hx₀ hy₀ (Genuine.hemiMap E₀ X) = x₀ := by
  apply modelMap_injective e.toRingEquiv
  change rhoM Z e _ = rhoM Z e x₀
  rw [rhoM_gPunct, hx₀]
  refine congrArg p.f ((theta_hemiMap E₀ X).trans ?_)
  rw [Polynomial.map_X]

omit [E₀.IsElliptic] in
lemma gPunct_y : gPunct E₀ e hZ p x₀ y₀ hx₀ hy₀ (yA E₀) = y₀ := by
  apply modelMap_injective e.toRingEquiv
  change rhoM Z e _ = rhoM Z e y₀
  rw [rhoM_gPunct, hy₀]
  refine congrArg p.f ((theta_kappa E₀ _).trans ?_)
  change kappa _ (WeierstrassCurve.Affine.CoordinateRing.map E₀ _
    (WeierstrassCurve.Affine.CoordinateRing.mk E₀ X)) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X]
  rfl

end Punctured

end OrbicurveCores.Transfer
