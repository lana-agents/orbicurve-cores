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
import Mathlib.LinearAlgebra.Dimension.Localization
import Pi1.Orbicurve.IntegralClosure

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

omit [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.FiniteType ℂ S] [Algebra.IsIntegral R S]
  [Module.Finite R S] [FaithfulSMul R S] in
lemma eval_map_of_mem_fib {χ₀ : R →ₐ[ℂ] ℂ} {χ : S →ₐ[ℂ] ℂ} (hχ : χ ∈ Fib S χ₀) (P : R[X])
    (θ : S) : (P.map (χ₀ : R →+* ℂ)).eval (χ θ) = χ (aeval θ P) := by
  have h : (χ : S →+* ℂ).comp (algebraMap R S) = (χ₀ : R →+* ℂ) := by
    ext r; exact AlgHom.congr_fun hχ r
  rw [eval_map, aeval_def]
  change _ = (χ : S →+* ℂ) (eval₂ (algebraMap R S) θ P)
  rw [Polynomial.hom_eval₂, h]
  rfl

omit [Module.Finite R S] in
/-- **A separating element**: an element of `S` taking distinct values at the points of `S` over a
given point of `R` (Chinese remainder theorem). -/
theorem exists_separating (χ₀ : R →ₐ[ℂ] ℂ) :
    ∃ θ : S, Set.InjOn (fun χ : S →ₐ[ℂ] ℂ ↦ χ θ) (Fib S χ₀) := by
  haveI := (finite_fib (S := S) χ₀).to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (Fib S χ₀)
  set I : Fib S χ₀ → Ideal S := fun χ ↦ RingHom.ker χ.1
  have hI : Pairwise (Function.onFun IsCoprime I) := by
    intro χ χ' hne
    haveI := ker_isMaximal χ.1
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne inferInstance (ker_isMaximal χ'.1) fun h ↦ hne ?_
    exact Subtype.ext (ext_of_ker_le h.le)
  obtain ⟨θ, hθ⟩ := Ideal.exists_forall_sub_mem_ideal hI
    (fun χ ↦ algebraMap ℂ S ((e χ : ℕ) : ℂ))
  have hval : ∀ χ : Fib S χ₀, χ.1 θ = ((e χ : ℕ) : ℂ) := fun χ ↦ by
    have := hθ χ
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_eq_zero] at this
    exact this
  refine ⟨θ, fun χ hχ χ' hχ' h ↦ ?_⟩
  have h' := (hval ⟨χ, hχ⟩).symm.trans (h.trans (hval ⟨χ', hχ'⟩))
  have := e.injective (Fin.ext (Nat.cast_injective h'))
  exact congrArg Subtype.val this

attribute [local instance] FractionRing.liftAlgebra

omit [Algebra ℂ R] [Algebra ℂ S] [IsScalarTower ℂ R S] [Algebra.FiniteType ℂ S]
  [Module.Finite R S] in
/-- `[Frac S : Frac R] = rank_R S`. -/
lemma finrank_fractionRing :
    Module.finrank (FractionRing R) (FractionRing S) = Module.finrank R S := by
  haveI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  haveI := AffOrbicurve.isLocalization_algebraMapSubmonoid_of_isAlgebraic R S (FractionRing S)
  have h1 : IsLocalizedModule (nonZeroDivisors R)
      (IsScalarTower.toAlgHom R S (FractionRing S)).toLinearMap := inferInstance
  exact ((isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) (FractionRing R) _).mp
    h1).finrank_eq

omit [Algebra ℂ R] [Algebra ℂ S] [IsScalarTower ℂ R S] [Algebra.FiniteType ℂ S]
  [Algebra.IsIntegral R S] in
lemma finiteDimensional_fractionRing :
    FiniteDimensional (FractionRing R) (FractionRing S) :=
  .of_isLocalization R S (nonZeroDivisors R)

omit [Algebra ℂ R] [Algebra ℂ S] [IsScalarTower ℂ R S] [Algebra.FiniteType ℂ S] in
lemma natDegree_minpoly_le (θ : S) : (minpoly R θ).natDegree ≤ Module.finrank R S := by
  haveI := finiteDimensional_fractionRing (R := R) (S := S)
  have hθ : IsIntegral R θ := Algebra.IsIntegral.isIntegral θ
  rw [← finrank_fractionRing (R := R) (S := S)]
  have hθ' : IsIntegral R (algebraMap S (FractionRing S) θ) := hθ.algebraMap
  have h : minpoly (FractionRing R) (algebraMap S (FractionRing S) θ) =
      (minpoly R (algebraMap S (FractionRing S) θ)).map (algebraMap R (FractionRing R)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) hθ'
  have h2 : minpoly R (algebraMap S (FractionRing S) θ) = minpoly R θ :=
    minpoly.algebraMap_eq (IsFractionRing.injective S (FractionRing S)) θ
  rw [← h2, ← (minpoly.monic hθ').natDegree_map (algebraMap R (FractionRing R)), ← h]
  exact minpoly.natDegree_le _

/-- **Minimal polynomial of a separating element**: it has degree `n = rank_R S`, and its
reduction at the point has simple roots at the values of `θ`. -/
theorem minpoly_of_separating (hunr : ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1)
    (χ₀ : R →ₐ[ℂ] ℂ) {θ : S} (hθ : Set.InjOn (fun χ : S →ₐ[ℂ] ℂ ↦ χ θ) (Fib S χ₀)) :
    (minpoly R θ).natDegree = Module.finrank R S ∧
      ∀ χ ∈ Fib S χ₀, ((minpoly R θ).map (χ₀ : R →+* ℂ)).derivative.eval (χ θ) ≠ 0 := by
  classical
  have hint : IsIntegral R θ := Algebra.IsIntegral.isIntegral θ
  set P := minpoly R θ
  set Q := P.map (χ₀ : R →+* ℂ)
  have hQm : Q.Monic := (minpoly.monic hint).map _
  have hQdeg : Q.natDegree = P.natDegree := (minpoly.monic hint).natDegree_map _
  haveI := (finite_fib (S := S) χ₀).to_subtype
  have hroot : ∀ χ ∈ Fib S χ₀, Q.IsRoot (χ θ) := fun χ hχ ↦ by
    rw [IsRoot, eval_map_of_mem_fib hχ, minpoly.aeval, map_zero]
  -- `n` distinct roots
  set T := (finite_fib (S := S) χ₀).toFinset.image fun χ ↦ χ θ
  have hTcard : T.card = Module.finrank R S := by
    rw [Finset.card_image_of_injOn (by simpa using hθ), ← card_fib hunr χ₀,
      Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (finite_fib χ₀)]
  have hTsub : T ⊆ Q.roots.toFinset := fun r hr ↦ by
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hr
    exact Multiset.mem_toFinset.mpr ((mem_roots hQm.ne_zero).mpr
      (hroot χ ((Set.Finite.mem_toFinset _).mp hχ)))
  have hle : Module.finrank R S ≤ Q.roots.toFinset.card := hTcard ▸ Finset.card_le_card hTsub
  have hdeg : P.natDegree = Module.finrank R S := by
    refine le_antisymm (natDegree_minpoly_le θ) ?_
    rw [← hQdeg]
    exact hle.trans ((Multiset.toFinset_card_le _).trans (card_roots' Q))
  refine ⟨hdeg, fun χ hχ ↦ ?_⟩
  -- `Q` has `deg Q` distinct roots, so it is separable
  have hnd : Q.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    refine le_antisymm (Multiset.toFinset_card_le _) ?_
    rw [IsAlgClosed.card_roots_eq_natDegree, hQdeg, hdeg]
    exact hle
  have hsep : Q.Separable :=
    (nodup_roots_iff_of_splits hQm.ne_zero (IsAlgClosed.splits Q)).mp hnd
  exact hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (hroot χ hχ)

omit [Algebra ℂ S] [IsScalarTower ℂ R S] [Algebra.FiniteType ℂ S] in
/-- **The different of an unramified extension is trivial.** -/
theorem differentIdeal_eq_top (hunr : ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1) :
    differentIdeal R S = ⊤ := by
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℂ R).injective
  haveI := finiteDimensional_fractionRing (R := R) (S := S)
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_integral _ _
  by_contra h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
  have hdvd : P ∣ differentIdeal R S := Ideal.dvd_iff_le.mpr hle
  rw [dvd_differentIdeal_iff] at hdvd
  apply hdvd
  haveI : CharZero (P.under R).ResidueField :=
    charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  exact (Ideal.ramificationIdx_eq_one_iff (q := P) (R := R)).mp (hunr P hP)

omit [Algebra ℂ S] [IsScalarTower ℂ R S] [Algebra.FiniteType ℂ S] in
/-- **`P'(θ) S ⊆ R[θ]`** for a primitive `θ` of an unramified extension (the conductor of `R[θ]`
is `(P'(θ))` since the different is trivial). -/
theorem derivative_mul_mem_adjoin
    (hunr : ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1) {θ : S}
    (hdeg : (minpoly R θ).natDegree = Module.finrank R S) (a : S) :
    aeval θ (derivative (minpoly R θ)) * a ∈ Algebra.adjoin R {θ} := by
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℂ R).injective
  haveI := finiteDimensional_fractionRing (R := R) (S := S)
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_integral _ _
  haveI : IsIntegralClosure S R (FractionRing S) :=
    IsIntegralClosure.of_isIntegrallyClosed S R (FractionRing S)
  set x := algebraMap S (FractionRing S) θ
  have hθ : IsIntegral R θ := Algebra.IsIntegral.isIntegral θ
  have hx : IsIntegral (FractionRing R) x :=
    (hθ.algebraMap).tower_top
  have hxdeg : (minpoly (FractionRing R) x).natDegree =
      Module.finrank (FractionRing R) (FractionRing S) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) hθ.algebraMap,
      (minpoly.monic hθ.algebraMap).natDegree_map,
      minpoly.algebraMap_eq (IsFractionRing.injective S (FractionRing S)), hdeg,
      finrank_fractionRing]
  have htop : Algebra.adjoin (FractionRing R) {x} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hx.isAlgebraic]
    have h1 : Module.finrank (FractionRing R) (IntermediateField.adjoin (FractionRing R) {x}) =
        Module.finrank (FractionRing R) (FractionRing S) := by
      rw [IntermediateField.adjoin.finrank hx, hxdeg]
    have h2 := Submodule.eq_top_of_finrank_eq (S := Subalgebra.toSubmodule
      ((IntermediateField.adjoin (FractionRing R) {x}).toSubalgebra)) (by
        rw [← h1]; rfl)
    exact Subalgebra.toSubmodule_injective (h2.trans Algebra.top_toSubmodule.symm)
  have hc := conductor_mul_differentIdeal R (FractionRing R) (FractionRing S) θ htop
  rw [differentIdeal_eq_top hunr, Ideal.mul_top] at hc
  have hmem : aeval θ (derivative (minpoly R θ)) ∈ conductor R θ := by
    rw [hc]; exact Ideal.mem_span_singleton_self _
  exact (mem_conductor_iff.mp hmem) a

end Fibre

end OrbicurveCores.Rigid
