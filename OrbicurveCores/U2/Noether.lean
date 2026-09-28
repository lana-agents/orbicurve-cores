/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# Noether normalization for affine curves

A Dedekind domain `A`, finitely generated over a field `k` and not a field, is integral over
`k[c]` for some `c ∈ A` transcendental over `k` (`U2.exists_transcendental_isIntegral`): Noether
normalization gives `k[X₀, …, X_{s-1}] ⊆ A` integral; `s = 0` would make `A` a field, and `s ≥ 2`
would give a chain `0 ⊊ P₁ ⊊ P₂` of primes of `A` over `0 ⊊ (X₀) ⊊ (X₀, X₁)` (lying over and
going up), impossible in a Dedekind domain.
-/

open Polynomial

namespace OrbicurveCores.U2

variable {k A : Type*} [Field k] [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

omit [IsDomain A] in
theorem exists_transcendental_isIntegral (hA : ¬ IsField A) :
    ∃ c : A, Transcendental k c ∧ ∀ a : A, IsIntegral (Algebra.adjoin k {c}) a := by
  classical
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  set R := MvPolynomial (Fin s) k
  letI : Algebra R A := g.toRingHom.toAlgebra
  have hmap : algebraMap R A = g.toRingHom := rfl
  haveI : Algebra.IsIntegral R A := ⟨fun a ↦ hint a⟩
  rcases Nat.lt_or_ge s 2 with hs | hs
  · rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · -- `A` would be a field
      exfalso
      apply hA
      have hR : IsField R :=
        (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toMulEquiv.isField (Field.toIsField k)
      exact isField_of_isIntegral_of_isField' hR
    · set c := g (MvPolynomial.X 0)
      have hmem : ∀ r : R, g r ∈ Algebra.adjoin k {c} := by
        intro r
        have h1 : r ∈ Algebra.adjoin k (Set.range (MvPolynomial.X : Fin 1 → R)) := by
          rw [MvPolynomial.adjoin_range_X]; trivial
        have h2 : g r ∈ (Algebra.adjoin k (Set.range (MvPolynomial.X : Fin 1 → R))).map g :=
          Subalgebra.mem_map.mpr ⟨r, h1, rfl⟩
        rwa [← Algebra.adjoin_image, Set.range_unique, Set.image_singleton] at h2
      refine ⟨c, fun halg ↦ ?_, fun a ↦ ?_⟩
      · exact MvPolynomial.transcendental_X k (0 : Fin 1) ((isAlgebraic_algHom_iff g hinj).mp halg)
      · obtain ⟨p, hpm, hp⟩ := hint a
        set f : R →+* Algebra.adjoin k {c} := g.toRingHom.codRestrict _ hmem
        refine ⟨p.map f, hpm.map f, ?_⟩
        rw [eval₂_map]
        exact hp
  · exfalso
    set i0 : Fin s := ⟨0, by omega⟩
    set i1 : Fin s := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    set ρ₁ : R →ₐ[k] R := MvPolynomial.aeval fun i ↦ if i = i0 then 0 else MvPolynomial.X i
    set ρ₂ : R →ₐ[k] R :=
      MvPolynomial.aeval fun i ↦ if i = i0 ∨ i = i1 then 0 else MvPolynomial.X i
    set q₁ := RingHom.ker ρ₁
    set q₂ := RingHom.ker ρ₂
    haveI : q₁.IsPrime := RingHom.ker_isPrime _
    haveI : q₂.IsPrime := RingHom.ker_isPrime _
    have hρ : ρ₂.comp ρ₁ = ρ₂ := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, ρ₁, ρ₂, MvPolynomial.aeval_X]
      by_cases h0 : i = i0
      · simp [h0]
      · rw [if_neg h0, MvPolynomial.aeval_X]
    have hq : q₁ ≤ q₂ := fun r hr ↦ by
      simp only [q₁, q₂, RingHom.mem_ker] at hr ⊢
      rw [← hρ, AlgHom.comp_apply]
      rw [show ρ₁ r = 0 from hr, map_zero]
    have hX1 : MvPolynomial.X i1 ∉ q₁ := by
      rw [RingHom.mem_ker]
      change ¬ (MvPolynomial.aeval _) (MvPolynomial.X i1) = 0
      rw [MvPolynomial.aeval_X, if_neg h01.symm]
      exact MvPolynomial.X_ne_zero i1
    have hX1' : MvPolynomial.X i1 ∈ q₂ := by
      rw [RingHom.mem_ker]
      change (MvPolynomial.aeval _) (MvPolynomial.X i1) = 0
      rw [MvPolynomial.aeval_X, if_pos (Or.inr rfl)]
    have hX0 : MvPolynomial.X i0 ∈ q₁ := by
      rw [RingHom.mem_ker]
      change (MvPolynomial.aeval _) (MvPolynomial.X i0) = 0
      rw [MvPolynomial.aeval_X, if_pos rfl]
    have hker : RingHom.ker (algebraMap R A) ≤ q₁ := by
      intro r hr
      rw [RingHom.mem_ker, hmap] at hr
      rw [show r = 0 from hinj (hr.trans (map_zero g).symm)]
      exact zero_mem _
    obtain ⟨P₁, hP₁, hP₁q⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain q₁ hker
    obtain ⟨P₂, hP₁₂, hP₂, hP₂q⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime q₂ P₁ (hP₁q ▸ hq)
    have hP₁0 : P₁ ≠ ⊥ := by
      intro h0
      apply MvPolynomial.X_ne_zero (R := k) i0
      have : MvPolynomial.X i0 ∈ Ideal.comap (algebraMap R A) P₁ := hP₁q ▸ hX0
      rw [h0, Ideal.mem_comap, Ideal.mem_bot, hmap] at this
      exact hinj (this.trans (map_zero g).symm)
    have hmax : P₁.IsMaximal := hP₁.isMaximal hP₁0
    have heq : P₁ = P₂ := hmax.eq_of_le hP₂.ne_top hP₁₂
    apply hX1
    rw [← hP₁q, heq, hP₂q]
    exact hX1'

end OrbicurveCores.U2
