/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.Ramification

/-!
# T2d: ramification indices on components of base changes

Let `f : A → B` be an injective finite map of Dedekind domains of finite type over a field `k` of
characteristic `0`, neither a field, and `K / k` a field extension. For a minimal prime `𝔓` of
`K ⊗ B`, its contraction `𝔮` to `K ⊗ A` is a minimal prime (`comap_bcMap_mem_minimalPrimes`),
and for a maximal ideal `w̃` of the component `C = (K ⊗ B)/𝔓` over `D = (K ⊗ A)/𝔮`
(`comp_ramificationIdx`):

  `e(w̃ | D) = e(w | A)` if `w = w̃ ∩ B ≠ 0`, and `e(w̃ | D) = 1` otherwise.
-/

open IsLocalRing TensorProduct

namespace OrbicurveCores.Transfer

variable {T : Type*} [CommRing T]

/-- In a ring all of whose local rings at maximal ideals are DVRs, every prime is minimal or
maximal. -/
lemma LocallyDVR.mem_minimalPrimes_or_isMaximal (h : LocallyDVR T) (Q : Ideal T) [Q.IsPrime] :
    Q ∈ minimalPrimes T ∨ Q.IsMaximal := by
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨_, _⟩ := h M
  have hdisj : Disjoint (M.primeCompl : Set T) Q := by
    rw [Set.disjoint_left]
    intro x hx hxQ
    exact hx (hQM hxQ)
  have hmp := IsLocalization.isPrime_of_isPrime_disjoint M.primeCompl
    (Localization.AtPrime M) Q ‹_› hdisj
  have hcm := IsLocalization.under_map_of_isPrime_disjoint M.primeCompl
    (Localization.AtPrime M) ‹Q.IsPrime› hdisj
  by_cases h0 : Q.map (algebraMap T (Localization.AtPrime M)) = ⊥
  · left
    obtain ⟨𝔭, h𝔭, h𝔭Q⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ Q)
    have hk := minimal_eq_ker h𝔭 (h𝔭Q.trans hQM)
    have hQ𝔭 : Q ≤ 𝔭 := by
      intro x hx
      have h2 : x ∈ RingHom.ker (algebraMap T (Localization.AtPrime M)) := by
        have : x ∈ (Q.map (algebraMap T (Localization.AtPrime M))).under T := hcm.symm ▸ hx
        rw [h0] at this
        simpa [Ideal.under] using this
      exact (SetLike.ext_iff.mp hk x).mpr h2
    rwa [le_antisymm hQ𝔭 h𝔭Q]
  · right
    have huniq := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime M)).mp inferInstance).2
    have hmax : Q.map (algebraMap T (Localization.AtPrime M)) =
        maximalIdeal (Localization.AtPrime M) :=
      huniq.unique ⟨h0, hmp⟩ ⟨IsDiscreteValuationRing.not_a_field _, inferInstance⟩
    rw [← hcm, hmax, Localization.AtPrime.under_maximalIdeal]
    exact hM

section Comp

variable {k K A B : Type*} [Field k] [Field K] [Algebra k K] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] (f : A →ₐ[k] B)

variable (K) in
/-- The map of components `(K ⊗ A)/(𝔓 ∩ (K ⊗ A)) → (K ⊗ B)/𝔓`. -/
noncomputable def compMap (𝔓 : Ideal (K ⊗[k] B)) :
    (K ⊗[k] A) ⧸ 𝔓.comap (bcMap K f) →ₐ[K] (K ⊗[k] B) ⧸ 𝔓 :=
  Ideal.quotientMapₐ 𝔓 (bcMap K f) le_rfl

@[simp] lemma compMap_mk (𝔓 : Ideal (K ⊗[k] B)) (x : K ⊗[k] A) :
    compMap K f 𝔓 (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk 𝔓 (bcMap K f x) := rfl

lemma compMap_injective (𝔓 : Ideal (K ⊗[k] B)) : Function.Injective (compMap K f 𝔓) :=
  Ideal.quotientMap_injective

lemma compMap_finite (hfin : f.toRingHom.Finite) (𝔓 : Ideal (K ⊗[k] B)) :
    (compMap K f 𝔓).toRingHom.Finite := by
  refine RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (𝔓.comap (bcMap K f))) ?_
  have : (compMap K f 𝔓).toRingHom.comp (Ideal.Quotient.mk (𝔓.comap (bcMap K f))) =
      (Ideal.Quotient.mk 𝔓).comp (bcMap K f).toRingHom := rfl
  rw [this]
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
    (bcMap_finite f hfin)

variable [CharZero k] [IsDedekindDomain A] [IsDedekindDomain B] [Algebra.FiniteType k A]
  [Algebra.FiniteType k B]

/-- The contraction of a minimal prime of `K ⊗ B` to `K ⊗ A` is a minimal prime. -/
lemma comap_bcMap_mem_minimalPrimes (hfin : f.toRingHom.Finite) (hA : ¬ IsField A)
    (hB : ¬ IsField B) {𝔓 : Ideal (K ⊗[k] B)} (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] B)) :
    𝔓.comap (bcMap K f) ∈ minimalPrimes (K ⊗[k] A) := by
  have : 𝔓.IsPrime := h𝔓.1.1
  have hQ : (𝔓.comap (bcMap K f)).IsPrime := Ideal.comap_isPrime _ _
  refine ((locallyDVR_tensor (K := K) hA).mem_minimalPrimes_or_isMaximal _).resolve_right ?_
  intro hmax
  apply (locallyDVR_tensor (K := K) hB).not_isField_quotient h𝔓
  have hF := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax
  letI := (compMap K f 𝔓).toRingHom.toAlgebra
  have : Algebra.IsIntegral ((K ⊗[k] A) ⧸ 𝔓.comap (bcMap K f)) ((K ⊗[k] B) ⧸ 𝔓) :=
    ⟨(compMap_finite f hfin 𝔓).to_isIntegral⟩
  exact isField_of_isIntegral_of_isField' hF

local notation "ιB" => (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B)

/-- **Ramification indices on components** (T2d): for a maximal ideal `w̃` of the component
`C = (K ⊗ B)/𝔓` over `D = (K ⊗ A)/(𝔓 ∩ (K ⊗ A))`, `e(w̃ | D) = e(w | A)` where
`w = w̃ ∩ B`, if `w ≠ 0`, and `e(w̃ | D) = 1` otherwise. -/
theorem comp_ramificationIdx (hf : Function.Injective f) (hfin : f.toRingHom.Finite)
    (hA : ¬ IsField A) (hB : ¬ IsField B) {𝔓 : Ideal (K ⊗[k] B)}
    (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] B)) (w : Ideal ((K ⊗[k] B) ⧸ 𝔓)) [w.IsMaximal] :
    (letI := (compMap K f 𝔓).toRingHom.toAlgebra;
      w.ramificationIdx ((K ⊗[k] A) ⧸ 𝔓.comap (bcMap K f))) =
      if (w.comap (Ideal.Quotient.mk 𝔓)).comap ιB = ⊥ then 1 else
        (letI := f.toRingHom.toAlgebra;
          ((w.comap (Ideal.Quotient.mk 𝔓)).comap ιB).ramificationIdx A) := by
  letI := (compMap K f 𝔓).toRingHom.toAlgebra
  set C := (K ⊗[k] B) ⧸ 𝔓
  set D := (K ⊗[k] A) ⧸ 𝔓.comap (bcMap K f)
  set L := Localization.AtPrime w
  have : 𝔓.IsPrime := h𝔓.1.1
  have : IsNoetherianRing (K ⊗[k] B) := Algebra.FiniteType.isNoetherianRing K _
  have : IsDedekindDomain C := (locallyDVR_tensor (K := K) hB).isDedekindDomain_quotient h𝔓
  set W := w.comap (Ideal.Quotient.mk 𝔓)
  have : W.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_›
    ((locallyDVR_tensor (K := K) hB).not_isField_quotient h𝔓)
  have : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hw0 L
  have hDC : ∀ x : K ⊗[k] A, algebraMap D L (Ideal.Quotient.mk _ x) =
      algebraMap C L (Ideal.Quotient.mk 𝔓 (bcMap K f x)) := fun x ↦ by
    rw [IsScalarTower.algebraMap_apply D C L]; rfl
  have pushW : ∀ {π : K ⊗[k] B}, (∀ x ∈ W, ∃ s ∉ W, ∃ y, s * x = π * y) →
      ∀ x ∈ w, ∃ s ∉ w, ∃ y, s * x = Ideal.Quotient.mk 𝔓 π * y := by
    intro π hπ x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs, y, hsy⟩ := hπ x hx
    exact ⟨Ideal.Quotient.mk 𝔓 s, hs, Ideal.Quotient.mk 𝔓 y, by rw [← map_mul, hsy, map_mul]⟩
  have pushV : ∀ {h : K ⊗[k] A}, (∀ x ∈ W.comap (bcMap K f), ∃ s ∉ W.comap (bcMap K f), ∃ y,
      s * x = h * y) → ∀ d ∈ w.under D, ∃ s, IsUnit (algebraMap D L s) ∧
        ∃ y, s * d = Ideal.Quotient.mk _ h * y := by
    intro h hh d hd
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨s, hs, y, hsy⟩ := hh x hd
    refine ⟨Ideal.Quotient.mk _ s, ?_, Ideal.Quotient.mk _ y, by rw [← map_mul, hsy, map_mul]⟩
    rw [hDC]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff L w _).mpr hs
  split_ifs with hw
  · obtain ⟨h, hhV, hV, hW⟩ := generic_data f hf hfin hA W hw
    have hmax := maximalIdeal_eq_span_of_forall w (π := Ideal.Quotient.mk 𝔓 (bcMap K f h))
      hhV (pushW hW)
    have hhV' : Ideal.Quotient.mk (𝔓.comap (bcMap K f)) h ∈ w.under D := hhV
    have hv := map_eq_span_of_forall_isUnit (R := D) (S := L) (algebraMap D L) hhV' fun d hd ↦ by
      obtain ⟨s, hs, y, hy⟩ := pushV hV d hd
      exact ⟨s, hs, y, hy⟩
    refine ramificationIdx_eq_of_map_eq_span_pow w hmax 1 ?_
    rw [hv, hDC, pow_one]
  · obtain ⟨π, ϖ, hπV, hV, hϖW, hW, s, hs, b, hb, hsb⟩ := closed_data f hf hfin W hw
    have hmax := maximalIdeal_eq_span_of_forall w (π := Ideal.Quotient.mk 𝔓 ((1 : K) ⊗ₜ[k] ϖ))
      hϖW (pushW hW)
    have hπV' : Ideal.Quotient.mk (𝔓.comap (bcMap K f)) ((1 : K) ⊗ₜ[k] π) ∈ w.under D := hπV
    have hv := map_eq_span_of_forall_isUnit (R := D) (S := L) (algebraMap D L) hπV' fun d hd ↦ by
      obtain ⟨s, hs, y, hy⟩ := pushV hV d hd
      exact ⟨s, hs, y, hy⟩
    refine ramificationIdx_eq_of_map_eq_span_pow w hmax _ ?_
    rw [hv, hDC, bcMap_tmul]
    have hus : IsUnit (algebraMap C L (Ideal.Quotient.mk 𝔓 s)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff L w _).mpr hs
    have hub : IsUnit (algebraMap C L (Ideal.Quotient.mk 𝔓 b)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff L w _).mpr hb
    have heq := congrArg (fun x ↦ algebraMap C L (Ideal.Quotient.mk 𝔓 x)) hsb
    simp only [map_mul, map_pow] at heq
    rw [← Ideal.span_singleton_mul_left_unit hus, heq, Ideal.span_singleton_mul_left_unit hub]

end Comp

end OrbicurveCores.Transfer
