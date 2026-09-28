/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.U2.CoreMap
import OrbicurveCores.U2.HemiUnique

/-!
# U2: assembly of [CanLift] Prop. 2.7 over `ℂ`

* `Hom.descend`: a map of coordinate rings `C → Y` through which a finite étale `Z → C`
  factors via a finite étale `Z → Y` is finite étale.
* ramification of polynomial maps `A¹ → A¹` (`ramificationIdx_aeval`) and of the double cover
  `E ∖ {0} → A¹` (`ramificationIdx_punctured`);
* `canLift27C_of_s1`: [CanLift] Prop. 2.7 over `ℂ`.
-/

open Polynomial Ideal AffOrbicurve

namespace OrbicurveCores.U2

section Descend

variable {k : Type*} [Field k]

/-- **Descent of finite étale maps.** If `χ : Z → C` factors as `Z → Y → C` through a finite
étale `ψ : Z → Y`, the map `Y → C` is finite étale. -/
def Hom.descend {Z Y C : AffOrbicurve k} (ψ : Hom Z Y) (χ : Hom Z C) (g : C.A →ₐ[k] Y.A)
    (hg : ψ.f.comp g = χ.f) : Hom Y C where
  f := g
  injective a b h := χ.injective (by rw [← hg]; simp [h])
  isIntegral a := by
    obtain ⟨p, hpm, hp⟩ := χ.isIntegral (ψ.f a)
    refine ⟨p, hpm, ψ.injective ?_⟩
    rw [map_zero, ← hp]
    change ψ.f.toRingHom (eval₂ g.toRingHom a p) = _
    rw [Polynomial.hom_eval₂, ← hg]
    rfl
  etale w hw := by
    letI := ψ.f.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral Y.A Z.A := ⟨ψ.isIntegral⟩
    obtain ⟨w', hw', hww'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := Z.A) w (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [ψ.injective (hx.trans (map_zero _).symm)]
      exact w.zero_mem)
    have hcomp : ψ.f.toRingHom.comp g.toRingHom = χ.f.toRingHom := by rw [← hg]; rfl
    have h1 := ramificationIdx_comp g.toRingHom ψ.f.toRingHom ψ.injective w'
    have h1' := (ramificationIdx_congr hcomp w').symm.trans h1
    have h2 := χ.etale w' hw'
    have h3 := ψ.etale w' hw'
    have hw'w : w'.comap ψ.f.toRingHom = w := hww'
    have hc : w'.comap χ.f.toRingHom = (w.comap g.toRingHom) := by
      rw [← hw'w, Ideal.comap_comap, hcomp]
    rw [h1', mul_assoc, h3] at h2
    change _ = C.mult (w'.comap χ.f.toRingHom) at h2
    rw [hc] at h2
    change _ * Y.mult (w'.comap ψ.f.toRingHom) = _ at h2
    rw [hw'w] at h2
    exact h2

@[simp] lemma Hom.descend_f {Z Y C : AffOrbicurve k} (ψ : Hom Z Y) (χ : Hom Z C)
    (g : C.A →ₐ[k] Y.A) (hg : ψ.f.comp g = χ.f) : (Hom.descend ψ χ g hg).f = g := rfl

end Descend

section Poly

/-- Ramification indices along an injective ring map, as the classical ramification index. -/
theorem ramificationIdx_toAlgebra {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDedekindDomain S] (f : R →+* S) (hf : Function.Injective f) (q : Ideal S) [q.IsPrime]
    (hq : q.comap f ≠ ⊥) :
    (letI := f.toAlgebra; q.ramificationIdx R) =
      (letI := f.toAlgebra; (q.comap f).ramificationIdx' q) := by
  letI := f.toAlgebra
  haveI : Module.IsTorsionFree R S := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hf
  haveI : q.LiesOver (q.comap f) := ⟨rfl⟩
  exact (ramificationIdx'_eq_ramificationIdx _ _ hq).symm

theorem comap_aeval_span (p : ℂ[X]) (w : ℂ) :
    (span {X - C w} : Ideal ℂ[X]).comap (aeval (R := ℂ) p).toRingHom = span {X - C (p.eval w)} := by
  ext q
  simp only [mem_comap, mem_span_singleton, dvd_iff_isRoot, IsRoot.def]
  change eval w (aeval p q) = 0 ↔ _
  rw [← comp_eq_aeval, eval_comp]

theorem aeval_injective_of_natDegree_pos {p : ℂ[X]} (hp : 0 < p.natDegree) :
    Function.Injective (aeval (R := ℂ) p).toRingHom := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  change aeval p q = 0 at hq
  rw [← comp_eq_aeval, comp_eq_zero_iff] at hq
  rcases hq with hq | ⟨-, hq⟩
  · exact hq
  · exfalso
    have := congrArg natDegree hq
    rw [natDegree_C] at this
    omega

theorem sub_C_ne_zero_of_natDegree_pos {p : ℂ[X]} (hp : 0 < p.natDegree) (c : ℂ) : p - C c ≠ 0 :=
  fun h ↦ by
    have := congrArg natDegree h
    rw [natDegree_sub_C, natDegree_zero] at this
    omega

/-- **Ramification of a polynomial map `A¹ → A¹`**: `e(w) = ord_w (p - p(w))`. -/
theorem ramificationIdx_aeval {p : ℂ[X]} (hp : 0 < p.natDegree) (w : ℂ) :
    (letI := (aeval (R := ℂ) p).toRingHom.toAlgebra;
      (span {X - C w} : Ideal ℂ[X]).ramificationIdx ℂ[X]) = Uniformization.RatFuncPoly.ramIdx p w := by
  have hinj := aeval_injective_of_natDegree_pos hp
  haveI : (span {X - C w} : Ideal ℂ[X]).IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero w)).mpr (prime_X_sub_C w)
  have hq : (span {X - C w} : Ideal ℂ[X]).comap (aeval (R := ℂ) p).toRingHom ≠ ⊥ := by
    rw [comap_aeval_span, Ne, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero _
  rw [ramificationIdx_toAlgebra _ hinj _ hq, comap_aeval_span]
  letI := (aeval (R := ℂ) p).toRingHom.toAlgebra
  have hmap : (span {X - C (p.eval w)} : Ideal ℂ[X]).map (algebraMap ℂ[X] ℂ[X]) =
      span {p - C (p.eval w)} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change aeval (R := ℂ) p (X - C (p.eval w)) = _
    simp
  have hne := sub_C_ne_zero_of_natDegree_pos hp (p.eval w)
  apply Ideal.ramificationIdx'_spec
  · rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact pow_rootMultiplicity_dvd _ _
  · rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact pow_rootMultiplicity_not_dvd hne _

end Poly

end OrbicurveCores.U2
