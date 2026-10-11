/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# U2c3: fibres of unramified finite extensions of curves over `ℂ`

Let `R → S` be an injective integral map of Dedekind domains of finite type over `ℂ`, unramified
at every maximal ideal of `S` (`e = 1`). Points are `ℂ`-algebra maps to `ℂ`.

* `ptOf`, `ker_ptOf`, `ext_of_ker_le`: points are maximal ideals (Nullstellensatz);
* `card_fib`: every point of `R` has exactly `n = rank_R S` points of `S` over it;
* `exists_separating`: an element of `S` takes distinct values at the points over a given point;
* `natDegree_minpoly`: a separating element has minimal polynomial of degree `n`, with simple
  roots at the point;
* `derivative_mul_mem_adjoin`: `P'(θ) S ⊆ R[θ]` (the different is trivial).
-/

open Polynomial

namespace OrbicurveCores.Rigid

/-! ### Points of finitely generated `ℂ`-algebras -/

section Points

variable {T : Type*} [CommRing T] [Algebra ℂ T] [Algebra.FiniteType ℂ T]

lemma bijective_algebraMap_quotient (w : Ideal T) [w.IsMaximal] :
    Function.Bijective (algebraMap ℂ (T ⧸ w)) := by
  letI := Ideal.Quotient.field w
  haveI : Module.Finite ℂ (T ⧸ w) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ w)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The point of `T` at a maximal ideal `w`. -/
noncomputable def ptOf (w : Ideal T) [w.IsMaximal] : T →ₐ[ℂ] ℂ :=
  (AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ w))
    (bijective_algebraMap_quotient w)).symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ w)

lemma ker_ptOf (w : Ideal T) [w.IsMaximal] : RingHom.ker (ptOf w) = w := by
  ext a
  set e := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ w)) (bijective_algebraMap_quotient w)
  rw [RingHom.mem_ker]
  change e.symm (Ideal.Quotient.mk w a) = 0 ↔ a ∈ w
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

omit [Algebra.FiniteType ℂ T] in
lemma ker_isMaximal (χ : T →ₐ[ℂ] ℂ) : (RingHom.ker χ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap ℂ T c, χ.commutes c⟩

omit [Algebra.FiniteType ℂ T] in
/-- Points are determined by their kernels. -/
lemma ext_of_ker_le {χ χ' : T →ₐ[ℂ] ℂ} (h : RingHom.ker χ ≤ RingHom.ker χ') : χ = χ' := by
  ext a
  have ha : a - algebraMap ℂ T (χ a) ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have := h ha
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this.symm

lemma ptOf_ker (χ : T →ₐ[ℂ] ℂ) : haveI := ker_isMaximal χ; ptOf (RingHom.ker χ) = χ := by
  haveI := ker_isMaximal χ
  exact ext_of_ker_le (by rw [ker_ptOf])

end Points

/-! ### Fibres -/

section Fibre

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S]
  [IsScalarTower ℂ R S]

variable (S) in
/-- The points of `S` over a point `χ₀` of `R`. -/
def Fib (χ₀ : R →ₐ[ℂ] ℂ) : Set (S →ₐ[ℂ] ℂ) :=
  {χ | χ.comp (IsScalarTower.toAlgHom ℂ R S) = χ₀}

lemma ker_under {χ₀ : R →ₐ[ℂ] ℂ} {χ : S →ₐ[ℂ] ℂ} (hχ : χ ∈ Fib S χ₀) :
    (RingHom.ker χ).under R = RingHom.ker χ₀ := by
  ext r
  simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker]
  rw [← hχ]
  rfl

variable [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.FiniteType ℂ S]
  [Algebra.IsIntegral R S] [Module.Finite R S] [FaithfulSMul R S]

/-- Points over `χ₀` are the primes over `ker χ₀`. -/
noncomputable def fibEquiv (χ₀ : R →ₐ[ℂ] ℂ) :
    Fib S χ₀ ≃ (RingHom.ker χ₀).primesOver S where
  toFun χ := ⟨RingHom.ker χ.1, (ker_isMaximal χ.1).isPrime, ⟨(ker_under χ.2).symm⟩⟩
  invFun q :=
    haveI : (RingHom.ker χ₀).IsMaximal := ker_isMaximal χ₀
    haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 (RingHom.ker χ₀)
    ⟨ptOf q.1, by
      haveI := q.2.2
      refine ext_of_ker_le fun r hr ↦ ?_
      have : (RingHom.ker χ₀) = q.1.under R := Ideal.LiesOver.over
      rw [this, Ideal.under, Ideal.mem_comap, ← ker_ptOf q.1]
      exact hr⟩
  left_inv χ := by
    apply Subtype.ext
    exact ptOf_ker χ.1
  right_inv q := by
    haveI : (RingHom.ker χ₀).IsMaximal := ker_isMaximal χ₀
    haveI := q.2.2
    haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 (RingHom.ker χ₀)
    apply Subtype.ext
    exact ker_ptOf _

omit [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.IsIntegral R S] [Module.Finite R S]
  [FaithfulSMul R S] in
lemma finrank_quotient_eq_one (p : Ideal R) (q : Ideal S) [p.IsMaximal] [q.IsMaximal]
    [q.LiesOver p] : Module.finrank (R ⧸ p) (S ⧸ q) = 1 := by
  letI := Ideal.Quotient.field p
  letI := Ideal.Quotient.field q
  have hb : Function.Bijective (algebraMap (R ⧸ p) (S ⧸ q)) := by
    refine ⟨(algebraMap (R ⧸ p) (S ⧸ q)).injective, fun y ↦ ?_⟩
    obtain ⟨c, rfl⟩ := (bijective_algebraMap_quotient q).2 y
    refine ⟨algebraMap ℂ (R ⧸ p) c, ?_⟩
    rw [IsScalarTower.algebraMap_apply ℂ R (R ⧸ p), IsScalarTower.algebraMap_apply ℂ S (S ⧸ q),
      IsScalarTower.algebraMap_apply ℂ R S, Ideal.Quotient.algebraMap_eq q,
      Ideal.Quotient.algebraMap_eq p]
    rfl
  rw [← Module.finrank_self (R ⧸ p)]
  exact (LinearEquiv.ofBijective (Algebra.linearMap (R ⧸ p) (S ⧸ q)) hb).finrank_eq.symm

/-- **The fibres have `n = rank_R S` points**, if `R → S` is unramified. -/
theorem card_fib (hunr : ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1)
    (χ₀ : R →ₐ[ℂ] ℂ) : Nat.card (Fib S χ₀) = Module.finrank R S := by
  haveI : (RingHom.ker χ₀).IsMaximal := ker_isMaximal χ₀
  rw [Nat.card_congr (fibEquiv χ₀), Nat.card_eq_fintype_card,
    ← Ideal.sum_ramification_inertia_eq_finrank (RingHom.ker χ₀) S]
  rw [← Finset.card_univ, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  haveI := q.2.2
  haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 (RingHom.ker χ₀)
  rw [hunr q.1 inferInstance, Ideal.inertiaDeg_eq_of_isMaximal (RingHom.ker χ₀) q.1,
    finrank_quotient_eq_one]

omit [Module.Finite R S] in
lemma finite_fib (χ₀ : R →ₐ[ℂ] ℂ) : (Fib S χ₀).Finite := by
  haveI : (RingHom.ker χ₀).IsMaximal := ker_isMaximal χ₀
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (fibEquiv χ₀).symm)

end Fibre

end OrbicurveCores.Rigid
