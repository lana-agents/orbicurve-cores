/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Noether normalization for affine curves

A Dedekind domain `A` of finite type over a field `k` which is not a field is finite over a
polynomial ring `k[t]` in one variable (`exists_finite_polynomial`): Noether normalization gives
`k[t₁, …, t_s] ⊆ A` finite; `s = 0` would make `A` a field, and for `s ≥ 2` the non-maximal
nonzero prime `ker(t₁ ↦ 0, tᵢ ↦ t)` would lie under a maximal ideal of `A`.
-/

open Polynomial

namespace OrbicurveCores.Transfer

/-- **Noether normalization for curves.** -/
theorem exists_finite_polynomial (k A : Type*) [Field k] [CommRing A] [IsDedekindDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (hA : ¬ IsField A) :
    ∃ t : k[X] →ₐ[k] A, Function.Injective t ∧ t.Finite := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have hint : Algebra.IsIntegral (MvPolynomial (Fin s) k) A :=
    ⟨fun x ↦ (hfin.to_isIntegral) x⟩
  -- `s = 1`
  have hs1 : s = 1 := by
    rcases Nat.lt_trichotomy s 1 with hs | hs | hs
    · exfalso
      obtain rfl : s = 0 := by omega
      apply hA
      have hF : IsField (MvPolynomial (Fin 0) k) :=
        (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toMulEquiv.isField (Field.toIsField k)
      exact (Algebra.IsIntegral.isField_iff_isField hinj).mp hF
    · exact hs
    · exfalso
      let i₀ : Fin s := ⟨0, by omega⟩
      let i₁ : Fin s := ⟨1, hs⟩
      have h0 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
      let φ : MvPolynomial (Fin s) k →ₐ[k] k[X] :=
        MvPolynomial.aeval fun i ↦ if i = i₀ then 0 else X
      have hφ : Function.Surjective φ := by
        rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X, Algebra.adjoin_le_iff,
          Set.singleton_subset_iff]
        exact ⟨MvPolynomial.X i₁, by simp [φ, h0]⟩
      let p := RingHom.ker φ
      have hp : p.IsPrime := RingHom.ker_isPrime _
      have hp0 : p ≠ ⊥ := by
        intro h
        have : MvPolynomial.X (R := k) i₀ ∈ p := by simp [p, φ]
        rw [h, Ideal.mem_bot] at this
        exact MvPolynomial.X_ne_zero _ this
      have hpmax : ¬ p.IsMaximal := by
        intro hmax
        apply Polynomial.not_isField k
        have := (Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp hmax
        exact (RingHom.quotientKerEquivOfSurjective hφ).symm.toMulEquiv.isField this
      obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := A) p ⊥ (by
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_bot] at hx
        rw [hinj (hx.trans (map_zero g).symm)]
        exact p.zero_mem)
      have hQ0 : Q ≠ ⊥ := by
        rintro rfl
        apply hp0
        rw [← hQc]
        ext x
        simp only [Ideal.mem_comap, Ideal.mem_bot]
        exact ⟨fun hx ↦ hinj (hx.trans (map_zero g).symm), fun hx ↦ by
          rw [hx]; exact map_zero _⟩
      have : Q.IsMaximal := hQ.isMaximal hQ0
      apply hpmax
      rw [← hQc]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  subst hs1
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] k[X] := MvPolynomial.uniqueAlgEquiv k (Fin 1)
  refine ⟨g.comp e.symm.toAlgHom, hinj.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.symm.surjective)

end OrbicurveCores.Transfer
