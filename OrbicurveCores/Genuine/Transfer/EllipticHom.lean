/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.Elliptic

/-!
# T2e: comparison morphisms for `E ∖ 0` and `(E ∖ 0)/±1` under base change

For an elliptic curve `E₀` over `k₀` (characteristic `0`), a field extension `K / k₀` and a
component `P` of `K ⊗ k₀[E₀ ∖ 0]` (over the component `Q` of `K ⊗ k₀[x]`):

* `iotaX : Hom P (E_K ∖ 0)`, an isomorphism of coordinate rings (`alphaX`);
* `iotaH : Hom Q ((E_K ∖ 0)/±1)`, an isomorphism of coordinate rings `K[x] ≅ Q`; its étale
  condition (equality of multiplicities) follows from the étale conditions of the two `x`-coordinate
  maps and the invariance of ramification indices under isomorphisms;
* `iotaX ∘ x = x ∘ iotaH`.
-/

open TensorProduct AffOrbicurve Polynomial

universe u v

namespace OrbicurveCores.Transfer

variable {k₀ : Type u} [Field k₀] [CharZero k₀] (E₀ : WeierstrassCurve k₀) [E₀.IsElliptic]
  {K : Type (max u v)} [Field K] [CharZero K] [Algebra k₀ K]
  (𝔭 : Ideal (K ⊗[k₀] (punctured E₀).A)) (h𝔭 : 𝔭 ∈ minimalPrimes (K ⊗[k₀] (punctured E₀).A))

/-- The quotient map onto the component. -/
noncomputable def rhoX : K ⊗[k₀] puncturedRing E₀ →ₐ[K] (bcComp K (punctured E₀) 𝔭 h𝔭).A :=
  Ideal.Quotient.mkₐ K 𝔭

omit [E₀.IsElliptic] [CharZero K] in
lemma rhoX_surjective : Function.Surjective (rhoX E₀ 𝔭 h𝔭) := Ideal.Quotient.mkₐ_surjective K 𝔭

omit [E₀.IsElliptic] [CharZero K] in
lemma ker_rhoX : RingHom.ker (rhoX E₀ 𝔭 h𝔭) ∈ minimalPrimes (K ⊗[k₀] puncturedRing E₀) := by
  have : RingHom.ker (rhoX E₀ 𝔭 h𝔭) = 𝔭 := Ideal.Quotient.mkₐ_ker K 𝔭
  rw [this]
  exact h𝔭

omit [CharZero K] in
/-- The isomorphism `K[E_K ∖ 0] ≅ P`, as a ring map. -/
noncomputable def alphaXR : puncturedRing (E₀.baseChange K) →+* (bcComp K (punctured E₀) 𝔭 h𝔭).A :=
  alphaX E₀ (rhoX E₀ 𝔭 h𝔭) (ker_rhoX E₀ 𝔭 h𝔭) (rhoX_surjective E₀ 𝔭 h𝔭)

omit [CharZero K] in
lemma alphaXR_commutes (c : K) :
    alphaXR E₀ 𝔭 h𝔭 (algebraMap K (puncturedRing (E₀.baseChange K)) c) =
      algebraMap K (bcComp K (punctured E₀) 𝔭 h𝔭).A c := by
  have : algebraMap K (puncturedRing (E₀.baseChange K)) c =
      algebraMap K[X] (puncturedRing (E₀.baseChange K)) (C c) := rfl
  rw [this, alphaXR, alphaX_algebraMap, psiPoly, Polynomial.aeval_C]

/-- The isomorphism `K[E_K ∖ 0] ≅ P`, as a `K`-algebra map. -/
noncomputable def alphaXK :
    (punctured (E₀.baseChange K)).A →ₐ[K] (bcComp K (punctured E₀) 𝔭 h𝔭).A :=
  AlgHom.mk (alphaXR E₀ 𝔭 h𝔭) (alphaXR_commutes E₀ 𝔭 h𝔭)

lemma alphaXK_bijective : Function.Bijective (alphaXK E₀ 𝔭 h𝔭) :=
  ⟨alphaX_injective E₀ _ _ (rhoX_surjective E₀ 𝔭 h𝔭),
    alphaX_surjective E₀ _ _ (rhoX_surjective E₀ 𝔭 h𝔭)⟩

omit [CharZero K] [E₀.IsElliptic] in
lemma compMult_punctured (w : Ideal (bcComp K (punctured E₀) 𝔭 h𝔭).A) :
    (bcComp K (punctured E₀) 𝔭 h𝔭).mult w = 1 := by
  change compMult K (punctured E₀) 𝔭 w = 1
  unfold compMult
  split_ifs <;> rfl

/-- **`P → E_K ∖ 0`**: the comparison isomorphism, as a finite étale morphism. -/
noncomputable def iotaX : Hom (bcComp K (punctured E₀) 𝔭 h𝔭) (punctured (E₀.baseChange K)) where
  f := alphaXK E₀ 𝔭 h𝔭
  injective := (alphaXK_bijective E₀ 𝔭 h𝔭).1
  isIntegral := RingHom.isIntegral_of_surjective _ (alphaXK_bijective E₀ 𝔭 h𝔭).2
  etale w hw := by
    haveI := hw.isPrime
    have h1 := ramificationIdx_eq_one_of_bijective (alphaXK E₀ 𝔭 h𝔭).toRingHom
      (alphaXK_bijective E₀ 𝔭 h𝔭) w
    rw [compMult_punctured, mul_one, Genuine.punctured_mult]
    exact h1

section Hemi

local notation "𝔮" => Ideal.comap (bcMap K (AffOrbicurve.Hom.f (Genuine.hemiHom E₀))) 𝔭

/-- The component of `K ⊗ k₀[x]` below `P`. -/
noncomputable abbrev compH : AffOrbicurve K :=
  bcComp K (hemi E₀) 𝔮 (comap_bcHom_mem (Genuine.hemiHom E₀) h𝔭)

omit [CharZero K] [E₀.IsElliptic] in
include h𝔭 in
lemma comap_hemi_eq_bot : 𝔮 = ⊥ := by
  have hmin := comap_bcHom_mem (K := K) (Genuine.hemiHom E₀) h𝔭
  have : IsDomain (K ⊗[k₀] k₀[X]) :=
    (polyEquivTensor' k₀ K).symm.toMulEquiv.isDomain
  have : IsDomain (K ⊗[k₀] (hemi E₀).A) := this
  exact le_antisymm (hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le) bot_le

/-- `K[x] ≅ Q`. -/
noncomputable def alphaH : (hemi (E₀.baseChange K)).A →ₐ[K] (compH E₀ 𝔭 h𝔭).A :=
  (Ideal.Quotient.mkₐ K 𝔮).comp (polyEquivTensor' k₀ K).toAlgHom

omit [E₀.IsElliptic] in
lemma alphaH_X : alphaH E₀ 𝔭 h𝔭 X = Ideal.Quotient.mk 𝔮 ((1 : K) ⊗ₜ[k₀] (X : k₀[X])) := by
  change Ideal.Quotient.mk 𝔮 (polyEquivTensor k₀ K X) = _
  rw [polyEquivTensor_apply, eval₂_X]
  rfl

omit [E₀.IsElliptic] in
lemma alphaH_bijective : Function.Bijective (alphaH E₀ 𝔭 h𝔭) := by
  have hmk : Function.Bijective (Ideal.Quotient.mk 𝔮) := by
    refine ⟨?_, Ideal.Quotient.mk_surjective⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ 𝔮 := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rwa [comap_hemi_eq_bot E₀ 𝔭 h𝔭, Ideal.mem_bot] at this
  exact hmk.comp (polyEquivTensor' k₀ K).bijective

/-- The square `alphaX ∘ x = β ∘ alphaH` commutes, `β` the base change of `x : E₀ ∖ 0 → H₀`. -/
lemma alpha_comm :
    (alphaXK E₀ 𝔭 h𝔭).comp (Genuine.hemiMap (E₀.baseChange K)) =
      (bcHom (Genuine.hemiHom E₀) 𝔭 h𝔭).f.comp (alphaH E₀ 𝔭 h𝔭) := by
  show ((alphaXK E₀ 𝔭 h𝔭).comp (Genuine.hemiMap (E₀.baseChange K)) :
      K[X] →ₐ[K] (bcComp K (punctured E₀) 𝔭 h𝔭).A) =
    ((bcHom (Genuine.hemiHom E₀) 𝔭 h𝔭).f.comp (alphaH E₀ 𝔭 h𝔭) :
      K[X] →ₐ[K] (bcComp K (punctured E₀) 𝔭 h𝔭).A)
  apply Polynomial.algHom_ext
  change alphaXR E₀ 𝔭 h𝔭 (algebraMap K[X] (puncturedRing (E₀.baseChange K)) X) =
    compMap K (Genuine.hemiHom E₀).f 𝔭 (alphaH E₀ 𝔭 h𝔭 X)
  rw [alphaH_X, compMap_mk, alphaXR, alphaX_algebraMap, psiPoly, Polynomial.aeval_X, bcMap_tmul]
  rfl

/-- **`Q → (E_K ∖ 0)/±1`**: the comparison isomorphism, as a finite étale morphism. -/
noncomputable def iotaH : Hom (compH E₀ 𝔭 h𝔭) (hemi (E₀.baseChange K)) where
  f := alphaH E₀ 𝔭 h𝔭
  injective := (alphaH_bijective E₀ 𝔭 h𝔭).1
  isIntegral := RingHom.isIntegral_of_surjective _ (alphaH_bijective E₀ 𝔭 h𝔭).2
  etale v hv := by
    haveI := hv.isPrime
    have h1 := ramificationIdx_eq_one_of_bijective (alphaH E₀ 𝔭 h𝔭).toRingHom
      (alphaH_bijective E₀ 𝔭 h𝔭) v
    rw [h1, one_mul]
    set β := bcHom (Genuine.hemiHom E₀) 𝔭 h𝔭
    letI := β.f.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (compH E₀ 𝔭 h𝔭).A (bcComp K (punctured E₀) 𝔭 h𝔭).A :=
      ⟨β.isIntegral⟩
    obtain ⟨W, hWmax, hW⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S :=
      (bcComp K (punctured E₀) 𝔭 h𝔭).A) v (by
        intro x hx
        rw [RingHom.mem_ker] at hx
        rw [β.injective (hx.trans (map_zero _).symm)]
        exact v.zero_mem)
    have hβ := β.etale W hWmax
    rw [compMult_punctured, mul_one] at hβ
    change _ = compMult K (hemi E₀) _ (W.comap β.f) at hβ
    have hWv : W.comap β.f = v := hW
    subst hWv
    have hsq := ramificationIdx_eq_of_comm_square β.f (alphaXK E₀ 𝔭 h𝔭) (alphaH E₀ 𝔭 h𝔭)
      (Genuine.hemiMap (E₀.baseChange K)) β.injective (alphaXK_bijective E₀ 𝔭 h𝔭)
      (alphaH_bijective E₀ 𝔭 h𝔭) (alpha_comm E₀ 𝔭 h𝔭) W
    have hW' : (W.comap (alphaXK E₀ 𝔭 h𝔭)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ (alphaXK_bijective E₀ 𝔭 h𝔭).2
    have hh := (Genuine.hemiHom (E₀.baseChange K)).etale _ hW'
    rw [Genuine.punctured_mult, mul_one] at hh
    refine hβ.symm.trans (hsq.trans (hh.trans ?_))
    congr 1
    ext x
    simp only [Ideal.mem_comap]
    have := congrArg (fun φ ↦ φ x) (alpha_comm E₀ 𝔭 h𝔭)
    simp only [AlgHom.comp_apply] at this
    change alphaXK E₀ 𝔭 h𝔭 (Genuine.hemiMap _ x) ∈ W ↔ _
    rw [this]

end Hemi

end OrbicurveCores.Transfer
