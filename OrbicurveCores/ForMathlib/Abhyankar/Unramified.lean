/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.ForMathlib.Abhyankar.Fibre

/-!
# Abhyankar's lemma: unramifiedness from a simple root, and Kummer generators

* `ramificationIdx_eq_one_of_aeval_derivative`: if `L_S = L_R(θ)` for `θ ∈ S` integral over `R`
  and `P'(θ) ∉ 𝔓` (`P` the minimal polynomial of `θ` over `R`), then `𝔓` is unramified over `R`
  (`P'(θ)` lies in the different);
* `ramificationIdx_eq_one_of_pow_eq`: a Kummer generator `θ^m = c` with `c ∉ w` gives an
  extension unramified over `w`.
-/

open Polynomial

namespace OrbicurveCores.Abhyankar

attribute [local instance] FractionRing.liftAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Algebra.IsIntegral R S] [Module.Finite R S] [FaithfulSMul R S] [CharZero R]

/-- **Unramifiedness from the derivative of the minimal polynomial.** -/
theorem ramificationIdx_eq_one_of_aeval_derivative {KR KS : Type*} [Field KR] [Field KS]
    [Algebra R KR] [IsFractionRing R KR] [Algebra S KS] [IsFractionRing S KS] [Algebra KR KS]
    [Algebra R KS] [IsScalarTower R KR KS] [IsScalarTower R S KS] [FiniteDimensional KR KS]
    {θ : S} (hgen : Algebra.adjoin KR {algebraMap S KS θ} = ⊤) {P : Ideal S} [P.IsMaximal]
    (hP : aeval θ (derivative (minpoly R θ)) ∉ P) : P.ramificationIdx R = 1 := by
  haveI : CharZero KR := charZero_of_injective_algebraMap (IsFractionRing.injective R KR)
  haveI : Algebra.IsSeparable KR KS := Algebra.IsSeparable.of_integral _ _
  haveI : IsIntegralClosure S R KS := IsIntegralClosure.of_isIntegrallyClosed S R KS
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    finiteDimensional_fractionRing (R := R) (S := S)
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_integral _ _
  have hd := aeval_derivative_mem_differentIdeal R KR KS θ hgen
  have hndvd : ¬ P ∣ differentIdeal R S := fun h ↦ hP (Ideal.dvd_iff_le.mp h hd)
  rw [not_dvd_differentIdeal_iff] at hndvd
  exact Ideal.ramificationIdx_eq_one P R

/-- **Kummer generators are unramified**: if `L_S = L_R(θ)` with `θ ^ m = c ∈ R`, `c ∉ P`, then
`P` is unramified over `R`. -/
theorem ramificationIdx_eq_one_of_pow_eq [Algebra ℂ R] {KR KS : Type*} [Field KR] [Field KS]
    [Algebra R KR] [IsFractionRing R KR] [Algebra S KS] [IsFractionRing S KS] [Algebra KR KS]
    [Algebra R KS] [IsScalarTower R KR KS] [IsScalarTower R S KS] [FiniteDimensional KR KS]
    {θ : S} (hgen : Algebra.adjoin KR {algebraMap S KS θ} = ⊤) {m : ℕ} (hm : m ≠ 0) {c : R}
    (hθ : θ ^ m = algebraMap R S c) {P : Ideal S} [hP : P.IsMaximal] (hc : algebraMap R S c ∉ P) :
    P.ramificationIdx R = 1 := by
  refine ramificationIdx_eq_one_of_aeval_derivative hgen fun hd ↦ hc ?_
  have hint : IsIntegral R θ := Algebra.IsIntegral.isIntegral θ
  have hroot : aeval θ (X ^ m - C c : R[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hθ, sub_self]
  obtain ⟨Q, hQ⟩ := minpoly.isIntegrallyClosed_dvd hint hroot
  have hder := congrArg (fun f : R[X] ↦ aeval θ (derivative f)) hQ
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, derivative_mul,
    map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at hder
  -- `m θ^(m-1) = P'(θ) Q(θ) ∈ P`
  have h1 : aeval θ (C (m : R)) * aeval θ (X ^ (m - 1) : R[X]) ∈ P := by
    rw [hder]; exact P.mul_mem_right _ hd
  rw [aeval_C, map_pow, aeval_X] at h1
  have hmR : IsUnit (m : R) := by
    have := (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hm : (m : ℂ) ≠ 0)).map
      (algebraMap ℂ R)
    rwa [map_natCast] at this
  have hmu : IsUnit (algebraMap R S (m : R)) := hmR.map _
  have h2 : θ ^ (m - 1) ∈ P := (hP.isPrime.mem_or_mem h1).resolve_left fun h ↦
    hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h hmu)
  have h3 : θ ∈ P := by
    rcases Nat.eq_zero_or_pos (m - 1) with h0 | hpos
    · rw [h0, pow_zero] at h2; exact absurd (Ideal.eq_top_of_isUnit_mem _ h2 isUnit_one) hP.ne_top
    · exact hP.isPrime.mem_of_pow_mem _ h2
  rw [← hθ]
  exact P.pow_mem_of_mem h3 m (Nat.pos_of_ne_zero hm)

end OrbicurveCores.Abhyankar
