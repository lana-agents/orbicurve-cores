/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# T1b: models over subfields

Let `k₀ → k` be a field extension, `A` a `k`-algebra and `A₀` a `k₀`-algebra with
`A₀ ⊗_{k₀} k ≅ A` (a *model* of `A`), `ρ : A₀ → A` the induced map. Then:

* `ρ` is injective, and an element `z ∈ A` with `z ρ(w) ∈ ρ(A₀)` for some `w ≠ 0` lies in
  `ρ(A₀)` (`mem_range_of_mul_mem_range`; descent of `v ∈ w A` along the faithfully flat
  `k₀ → k`);
* if `A` is a Dedekind domain which is not a field, so is `A₀` (`isDedekindDomain_of_model`):
  integral closedness descends by the previous point, dimension `≤ 1` by going down and lying
  over along the faithfully flat `A₀ → A₀ ⊗ k`.
-/

open TensorProduct

namespace OrbicurveCores.Transfer

section Linear

/-- Descent of membership in the image along a field extension, `rTensor` version. -/
lemma mem_range_of_tmul_one_mem_range {k₀ K M N : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    [AddCommGroup M] [Module k₀ M] [AddCommGroup N] [Module k₀ N] (f : M →ₗ[k₀] N) {n : N}
    (h : n ⊗ₜ[k₀] (1 : K) ∈ LinearMap.range (LinearMap.rTensor K f)) : n ∈ LinearMap.range f := by
  refine mem_range_of_one_tmul_mem_range (K := K) f ?_
  obtain ⟨t, ht⟩ := h
  refine ⟨TensorProduct.comm k₀ M K t, ?_⟩
  have : LinearMap.lTensor K f ∘ₗ (TensorProduct.comm k₀ M K).toLinearMap =
      (TensorProduct.comm k₀ N K).toLinearMap ∘ₗ LinearMap.rTensor K f := by
    ext m c; rfl
  have h2 := congrArg (fun φ : M ⊗[k₀] K →ₗ[k₀] K ⊗[k₀] N ↦ φ t) this
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h2
  rw [h2, ht]
  rfl

end Linear

section Model

variable {k₀ k : Type*} [Field k₀] [Field k] [Algebra k₀ k]
  {A₀ A : Type*} [CommRing A₀] [Algebra k₀ A₀] [CommRing A] (φ : k ⊗[k₀] A₀ ≃+* A)

/-- The map `A₀ → A` of a model. -/
noncomputable def modelMap : A₀ →+* A :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[k₀] k ⊗[k₀] A₀).toRingHom

lemma modelMap_apply (a : A₀) : modelMap φ a = φ ((1 : k) ⊗ₜ a) := rfl

omit [CommRing A] in
lemma includeRight_injective' :
    Function.Injective (Algebra.TensorProduct.includeRight : A₀ →ₐ[k₀] k ⊗[k₀] A₀) := by
  have : ⇑(Algebra.TensorProduct.includeRight : A₀ →ₐ[k₀] k ⊗[k₀] A₀) =
      (LinearMap.rTensor A₀ (Algebra.linearMap k₀ k)) ∘ (TensorProduct.lid k₀ A₀).symm := by
    ext a; simp
  rw [this]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap k₀ k).injective).comp (TensorProduct.lid k₀ A₀).symm.injective

lemma modelMap_injective : Function.Injective (modelMap φ) :=
  φ.injective.comp (includeRight_injective' (k := k))

/-- **Fraction closure of a model**: if `z ρ(w) ∈ ρ(A₀)` with `w ≠ 0` and `A` a domain, then
`z ∈ ρ(A₀)`. -/
lemma mem_range_of_mul_mem_range [IsDomain A] {z : A} {w : A₀} (hw : w ≠ 0)
    (h : z * modelMap φ w ∈ (modelMap φ).range) : z ∈ (modelMap φ).range := by
  obtain ⟨v, hv⟩ := h
  set t := φ.symm z
  have ht : LinearMap.lTensor k (LinearMap.mulLeft k₀ w) t = (1 : k) ⊗ₜ[k₀] v := by
    apply φ.injective
    have : LinearMap.lTensor k (LinearMap.mulLeft k₀ w) t = t * ((1 : k) ⊗ₜ[k₀] w) := by
      induction t with
      | zero => simp
      | tmul c a => simp [mul_comm]
      | add x y hx hy => rw [map_add, hx, hy, add_mul]
    rw [this, map_mul, RingEquiv.apply_symm_apply]
    exact hv.symm
  obtain ⟨z₀, hz₀⟩ := mem_range_of_one_tmul_mem_range (K := k) (LinearMap.mulLeft k₀ w)
    ⟨t, ht⟩
  refine ⟨z₀, ?_⟩
  have hw' : modelMap φ w ≠ 0 := fun h0 ↦ hw (modelMap_injective φ (h0.trans (map_zero _).symm))
  apply mul_right_cancel₀ hw'
  rw [← hv, ← hz₀, LinearMap.mulLeft_apply, map_mul, mul_comm]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [CommRing A] in
lemma faithfullyFlat_tensor : Module.FaithfullyFlat A₀ (k ⊗[k₀] A₀) := by
  let e : k ⊗[k₀] A₀ ≃ₐ[A₀] A₀ ⊗[k₀] k :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  exact Module.FaithfullyFlat.of_linearEquiv A₀ (A₀ ⊗[k₀] k) e.toLinearEquiv

include φ in
lemma isDomain_of_model [IsDomain A] : IsDomain A₀ :=
  (modelMap_injective φ).isDomain

include φ in
/-- Integral closedness descends to models. -/
lemma isIntegrallyClosed_of_model [IsDomain A] [IsIntegrallyClosed A] :
    @IsIntegrallyClosed A₀ _ := by
  haveI := isDomain_of_model φ
  rw [isIntegrallyClosed_iff (FractionRing A₀)]
  intro x hx
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp (modelMap φ)) :=
    (IsFractionRing.injective A (FractionRing A)).comp (modelMap_injective φ)
  let rh : FractionRing A₀ →+* FractionRing A := IsFractionRing.lift hinj
  have hrh : ∀ a : A₀, rh (algebraMap A₀ _ a) = algebraMap A _ (modelMap φ a) :=
    fun a ↦ IsFractionRing.lift_algebraMap hinj a
  obtain ⟨p, hp, hpx⟩ := hx
  have hint : IsIntegral A (rh x) := by
    refine ⟨p.map (modelMap φ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap A (FractionRing A)).comp (modelMap φ) = rh.comp (algebraMap A₀ _) := by
      ext a; exact (hrh a).symm
    rw [this, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hint
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A₀) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hzb : z * modelMap φ b = modelMap φ a := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, hz, ← hrh, ← hrh, ← map_mul, div_mul_cancel₀]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨z₀, hz₀⟩ := mem_range_of_mul_mem_range φ hb0 ⟨a, hzb.symm⟩
  refine ⟨z₀, ?_⟩
  apply rh.injective
  rw [hrh, hz₀, hz]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
include φ in
/-- Dimension `≤ 1` descends to models (going down and lying over along `A₀ → k ⊗ A₀`). -/
lemma dimensionLEOne_of_model [IsDomain A] [Ring.DimensionLEOne A] : Ring.DimensionLEOne A₀ := by
  haveI := faithfullyFlat_tensor (k := k) (A₀ := A₀) (k₀ := k₀)
  refine ⟨fun {P} hP0 hP ↦ ?_⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  by_contra hnm
  obtain ⟨M', hM', hlo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat
    (B := k ⊗[k₀] A₀) M
  obtain ⟨P', hP'M', hP', hlo'⟩ := Ideal.exists_ideal_le_liesOver_of_le M' hPM
  have hPu : P = P'.under A₀ := hlo'.over
  have hMu : M = M'.under A₀ := hlo.over
  have hP'0 : P' ≠ ⊥ := by
    intro h
    apply hP0
    rw [hPu, h]
    ext a
    simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h ↦ includeRight_injective' (k := k) (h.trans (map_zero _).symm),
      fun h ↦ by rw [h, map_zero]⟩
  have hQ : (P'.map φ).IsPrime := Ideal.map_isPrime_of_equiv φ
  have hQ0 : P'.map φ ≠ ⊥ := by
    intro h
    apply hP'0
    have := congrArg (Ideal.comap φ) h
    rwa [Ideal.comap_map_of_bijective φ φ.bijective, Ideal.comap_bot_of_injective φ φ.injective]
      at this
  have hQmax := Ring.DimensionLEOne.maximalOfPrime hQ0 hQ
  have hM'p : (M'.map φ).IsPrime := Ideal.map_isPrime_of_equiv φ
  have heq : P'.map φ = M'.map φ := hQmax.eq_of_le hM'p.ne_top (Ideal.map_mono hP'M')
  have : P' = M' := by
    have := congrArg (Ideal.comap φ) heq
    rwa [Ideal.comap_map_of_bijective φ φ.bijective, Ideal.comap_map_of_bijective φ φ.bijective]
      at this
  apply hnm
  rw [hPu, this, ← hMu]
  exact hM

include φ in
/-- Models of non-fields are not fields. -/
lemma not_isField_of_model [IsDomain A] [Algebra.FiniteType k₀ A₀] (hA : ¬ IsField A) :
    ¬ IsField A₀ := by
  intro hF
  letI := hF.toField
  haveI : Module.Finite k₀ A₀ := finite_of_finite_type_of_isJacobsonRing k₀ A₀
  haveI : IsDomain (k ⊗[k₀] A₀) := φ.toMulEquiv.isDomain
  have : IsField (k ⊗[k₀] A₀) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k (k ⊗[k₀] A₀)).injective).mp
      (Field.toIsField k)
  exact hA (φ.symm.toMulEquiv.isField this)

include φ in
/-- **Models of Dedekind domains are Dedekind domains.** -/
theorem isDedekindDomain_of_model [IsDedekindDomain A] [IsNoetherianRing A₀] :
    IsDedekindDomain A₀ := by
  haveI := isDomain_of_model φ
  haveI := isIntegrallyClosed_of_model φ
  haveI := dimensionLEOne_of_model φ
  exact (isDedekindDomain_iff A₀ (FractionRing A₀)).mpr ⟨inferInstance, inferInstance,
    inferInstance, fun {_} ↦ (isIntegrallyClosed_iff (FractionRing A₀)).mp inferInstance⟩

end Model

section IntegralDescent

variable {k₀ k R₀ B₀ : Type*} [Field k₀] [Field k] [Algebra k₀ k] [CommRing R₀] [CommRing B₀]
  [Algebra k₀ R₀] [Algebra k₀ B₀]

/-- **Integrality descends along field extensions**: if `1 ⊗ z` is integral over `k ⊗ R₀`, then
`z` is integral over `R₀` (apply a `k₀`-linear retraction `k → k₀` to an equation). -/
lemma isIntegral_of_isIntegral_tensor (g : R₀ →ₐ[k₀] B₀) {z : B₀}
    (h : (letI := (bcMap k g).toRingHom.toAlgebra; IsIntegral (k ⊗[k₀] R₀) ((1 : k) ⊗ₜ[k₀] z))) :
    (letI := g.toRingHom.toAlgebra; IsIntegral R₀ z) := by
  letI := g.toRingHom.toAlgebra
  letI := (bcMap k g).toRingHom.toAlgebra
  obtain ⟨lam, hlam⟩ := (Algebra.linearMap k₀ k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k₀ k).injective)
  have hlam1 : lam 1 = 1 := by
    have := congrArg (fun f ↦ f 1) hlam
    simpa using this
  let LR : k ⊗[k₀] R₀ →ₗ[k₀] R₀ := (TensorProduct.lid k₀ R₀).toLinearMap ∘ₗ LinearMap.rTensor R₀ lam
  let LB : k ⊗[k₀] B₀ →ₗ[k₀] B₀ := (TensorProduct.lid k₀ B₀).toLinearMap ∘ₗ LinearMap.rTensor B₀ lam
  have key : ∀ (c : k ⊗[k₀] R₀) (b : B₀),
      LB (bcMap k g c * ((1 : k) ⊗ₜ[k₀] b)) = g (LR c) * b := by
    intro c b
    induction c with
    | zero => simp
    | tmul t r =>
      simp [LB, LR, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, add_mul, map_add, hx, hy, map_add, map_add, add_mul]
  obtain ⟨p, hp, hpz⟩ := h
  set n := p.natDegree
  refine ⟨Polynomial.X ^ n + ∑ i : Fin n,
    Polynomial.C (LR (p.coeff i)) * Polynomial.X ^ (i : ℕ), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  · rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum] at hpz
    simp only [Polynomial.eval₂_X_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hpz
    have h2 := congrArg LB hpz
    rw [map_zero, map_add, map_sum] at h2
    rw [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
    convert h2 using 2
    · rw [Algebra.TensorProduct.tmul_pow, one_pow]
      simp [LB, hlam1, n]
    · rw [← Finset.sum_range (fun i ↦ algebraMap R₀ B₀ (LR (p.coeff i)) * z ^ i)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      exact (key _ _).symm

end IntegralDescent

end OrbicurveCores.Transfer
