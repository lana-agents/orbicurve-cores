/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.HomComp
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus

/-!
# Ramification indices of isomorphisms

A bijective ring map has ramification index `1` everywhere (`ramificationIdx_eq_one_of_bijective`;
it is formally unramified). With the multiplicativity of ramification indices in towers
(`Hom.ramificationIdx_comp`), ramification indices of affine orbicurves are invariant under
isomorphisms of coordinate rings (`ramificationIdx_eq_of_comm_square`).
-/

open AffOrbicurve

namespace OrbicurveCores.Transfer

/-- A bijective ring map has ramification index `1` at every prime. -/
lemma ramificationIdx_eq_one_of_bijective {S T : Type*} [CommRing S] [CommRing T] (h : S →+* T)
    (hb : Function.Bijective h) (w : Ideal T) [w.IsPrime] :
    (letI := h.toAlgebra; w.ramificationIdx S) = 1 := by
  letI := h.toAlgebra
  have : Algebra.FormallyUnramified S T :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId S T) hb.2
  have : Algebra.FiniteType S T := Algebra.FiniteType.of_surjective (Algebra.ofId S T) hb.2
  have : Algebra.FormallyUnramified S (Localization.AtPrime w) :=
    Algebra.FormallyUnramified.comp S T _
  have : Algebra.EssFiniteType S (Localization.AtPrime w) :=
    Algebra.EssFiniteType.comp S T _
  exact Ideal.ramificationIdx_eq_one w S

/-- **Invariance of ramification indices under isomorphisms**: in a commutative square
`αX ∘ h = β ∘ αH` of coordinate rings of affine orbicurves with `αX`, `αH` bijective,
`e_β(W) = e_h(αX⁻¹ W)`. -/
lemma ramificationIdx_eq_of_comm_square {k : Type*} [Field k] {P Q X H : AffOrbicurve k}
    (β : Q.A →ₐ[k] P.A) (αX : X.A →ₐ[k] P.A) (αH : H.A →ₐ[k] Q.A) (h : H.A →ₐ[k] X.A)
    (hβ : Function.Injective β) (hαX : Function.Bijective αX) (hαH : Function.Bijective αH)
    (hcomm : αX.comp h = β.comp αH) (W : Ideal P.A) [W.IsPrime] :
    (letI := β.toRingHom.toAlgebra; W.ramificationIdx Q.A) =
      (letI := h.toRingHom.toAlgebra; (W.comap αX).ramificationIdx H.A) := by
  have t1 := Hom.ramificationIdx_comp (Z := P) (Y := Q) (C := H) αH β hβ W
  have t2 := Hom.ramificationIdx_comp (Z := P) (Y := X) (C := H) h αX hαX.1 W
  have : (W.comap β).IsPrime := Ideal.comap_isPrime _ _
  have e1 := ramificationIdx_eq_one_of_bijective αH.toRingHom hαH (W.comap β)
  have e2 := ramificationIdx_eq_one_of_bijective αX.toRingHom hαX W
  rw [hcomm] at t2
  rw [e1, one_mul] at t1
  rw [e2, mul_one] at t2
  exact t1.symm.trans t2

end OrbicurveCores.Transfer
