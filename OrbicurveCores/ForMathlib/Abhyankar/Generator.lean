/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.ForMathlib.Abhyankar.Fibre
import OrbicurveCores.ForMathlib.Abhyankar.Unramified

/-!
# Abhyankar's lemma: local generators with a simple root

Let `R → S` be a finite extension of Dedekind domains of finite type over `ℂ`, unramified over a
maximal ideal `p₀` of `R`.

* `exists_generator`: there is `θ ∈ S` whose minimal polynomial over `R` has degree `rank_R S`
  and whose derivative at `θ` lies outside a given prime `q₀` over `p₀`;
* `finrank_eq_of_isFractionRing`: `rank_R S = [K_S : K_R]`;
* `adjoin_eq_top_of_natDegree`: such a `θ` generates `K_S` over `K_R`;
* `aeval_derivative_minpoly_notMem`: the minimal polynomial over a larger integrally closed ring
  divides, so its derivative at `θ` is still outside the prime.
-/

open Polynomial

namespace OrbicurveCores.Abhyankar

section Generator

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S]
  [IsScalarTower ℂ R S] [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.FiniteType ℂ R]
  [Algebra.FiniteType ℂ S] [Algebra.IsIntegral R S] [Module.Finite R S] [FaithfulSMul R S]

/-- **A generator with a simple root at `q₀`.** -/
theorem exists_generator (p₀ : Ideal R) [p₀.IsMaximal]
    (hunr : ∀ q : Ideal S, q.IsMaximal → q.under R = p₀ → q.ramificationIdx R = 1)
    (q₀ : Ideal S) [q₀.IsMaximal] (hq₀ : q₀.under R = p₀) :
    ∃ θ : S, (minpoly R θ).natDegree = Module.finrank R S ∧
      aeval θ (derivative (minpoly R θ)) ∉ q₀ := by
  set χ₀ := ptOf p₀
  have hker : RingHom.ker χ₀ = p₀ := ker_ptOf p₀
  obtain ⟨θ, hθ⟩ := exists_separating (S := S) χ₀
  obtain ⟨hdeg, hsimple⟩ := minpoly_of_separating' χ₀ (by rwa [hker]) hθ
  refine ⟨θ, hdeg, fun hmem ↦ ?_⟩
  set χ := ptOf q₀
  have hχ : χ ∈ Fib S χ₀ := by
    refine ext_of_ker_le fun r hr ↦ ?_
    rw [hker, ← hq₀]
    rw [RingHom.mem_ker, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← RingHom.mem_ker,
      ker_ptOf] at hr
    exact hr
  apply hsimple χ hχ
  rw [derivative_map, eval_map_of_mem_fib hχ, ← RingHom.mem_ker, ker_ptOf]
  exact hmem

end Generator

section Fields

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
  [Algebra.IsIntegral R S] [FaithfulSMul R S]
  {KR KS : Type*} [Field KR] [Field KS] [Algebra R KR] [IsFractionRing R KR] [Algebra S KS]
  [IsFractionRing S KS] [Algebra KR KS] [Algebra R KS] [IsScalarTower R KR KS]
  [IsScalarTower R S KS]

include KR in
/-- `rank_R S = [K_S : K_R]`. -/
lemma finrank_eq_of_isFractionRing : Module.finrank R S = Module.finrank KR KS := by
  haveI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  haveI := AffOrbicurve.isLocalization_algebraMapSubmonoid_of_isAlgebraic R S KS
  have h1 : IsLocalizedModule (nonZeroDivisors R)
      (IsScalarTower.toAlgHom R S KS).toLinearMap := inferInstance
  exact (((isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) KR _).mp
    h1).finrank_eq).symm

/-- **Generation**: an element whose minimal polynomial has degree `rank_R S` generates. -/
lemma adjoin_eq_top_of_natDegree [IsIntegrallyClosed R] [FiniteDimensional KR KS] {θ : S}
    (hdeg : (minpoly R θ).natDegree = Module.finrank R S) :
    Algebra.adjoin KR {algebraMap S KS θ} = ⊤ := by
  have hint : IsIntegral R θ := Algebra.IsIntegral.isIntegral θ
  have hint' : IsIntegral R (algebraMap S KS θ) := hint.algebraMap
  have hmin : minpoly KR (algebraMap S KS θ) =
      (minpoly R (algebraMap S KS θ)).map (algebraMap R KR) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' KR hint'
  have h2 : minpoly R (algebraMap S KS θ) = minpoly R θ :=
    minpoly.algebraMap_eq (IsFractionRing.injective S KS) θ
  have hintK : IsIntegral KR (algebraMap S KS θ) := hint'.tower_top
  have hfr : Module.finrank KR (IntermediateField.adjoin KR {algebraMap S KS θ}) =
      Module.finrank KR KS := by
    rw [IntermediateField.adjoin.finrank hintK, hmin, h2,
      (minpoly.monic hint).natDegree_map, hdeg, finrank_eq_of_isFractionRing (KR := KR) (KS := KS)]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintK.isAlgebraic |>.symm]
  have htop : IntermediateField.adjoin KR {algebraMap S KS θ} = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top (hfr.trans IntermediateField.finrank_top'.symm)
  rw [htop, IntermediateField.top_toSubalgebra]

end Fields

/-- **Derivatives of minimal polynomials over larger rings**: if `P(θ) = 0` and `P'(θ) ∉ Q`, then
the minimal polynomial `μ` of `θ` over an integrally closed `R` has `μ'(θ) ∉ Q`. -/
lemma aeval_derivative_minpoly_notMem {R S : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [IsIntegrallyClosed R] [Algebra R S] [Module.IsTorsionFree R S] {θ : S}
    (hint : IsIntegral R θ) {P : R[X]} (hP : aeval θ P = 0) {Q : Ideal S} [Q.IsPrime]
    (hd : aeval θ (derivative P) ∉ Q) : aeval θ (derivative (minpoly R θ)) ∉ Q := by
  obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hint hP
  intro hmem
  apply hd
  rw [hg, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  exact Q.mul_mem_right _ hmem

end OrbicurveCores.Abhyankar
