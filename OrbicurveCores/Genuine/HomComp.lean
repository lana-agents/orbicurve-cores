/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Pi1.Orbicurve.Core
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Composition of finite étale morphisms of affine orbicurves

For pi1's `AffOrbicurve.Hom` (a finite injective map of coordinate rings satisfying
`e(w | v) · m_Y(w) = m_C(v)`), this file proves that ramification indices are multiplicative in
towers (the coordinate rings are Dedekind domains, so the extensions are flat), and hence that
finite étale morphisms compose.

* `Hom.ramIdx φ w`: the ramification index of `φ : Y → C` at a prime `w` of `Y`;
* `Hom.ramIdx_comp`: `e_{ψ ∘ φ}(w) = e_ψ(φ(w)) · e_φ(w)`;
* `Hom.comp`: the composite of finite étale morphisms.
-/

universe u

open Ideal

namespace AffOrbicurve.Hom

variable {k : Type u} [Field k]

/-- The ramification index of `φ : Y → C` at a prime `w` of the coordinate ring of `Y`. -/
noncomputable def ramIdx {Y C : AffOrbicurve k} (φ : Hom Y C) (w : Ideal Y.A) : ℕ :=
  letI := φ.f.toRingHom.toAlgebra
  w.ramificationIdx C.A

lemma ramIdx_mul_mult {Y C : AffOrbicurve k} (φ : Hom Y C) (w : Ideal Y.A) (hw : w.IsMaximal) :
    φ.ramIdx w * Y.mult w = C.mult (w.comap φ.f) :=
  φ.etale w hw

/-- Ramification indices are multiplicative along `Z → Y → C`, for injective maps of coordinate
rings of affine orbicurves. -/
lemma ramificationIdx_comp {Z Y C : AffOrbicurve k} (g : C.A →ₐ[k] Y.A) (h : Y.A →ₐ[k] Z.A)
    (hh : Function.Injective h) (w : Ideal Z.A) :
    (letI := ((h.comp g).toRingHom).toAlgebra; w.ramificationIdx C.A) =
      (letI := g.toRingHom.toAlgebra; (w.comap h).ramificationIdx C.A) *
        (letI := h.toRingHom.toAlgebra; w.ramificationIdx Y.A) := by
  letI : Algebra C.A Y.A := g.toRingHom.toAlgebra
  letI : Algebra Y.A Z.A := h.toRingHom.toAlgebra
  letI : Algebra C.A Z.A := ((h.comp g).toRingHom).toAlgebra
  haveI : IsScalarTower C.A Y.A Z.A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.IsTorsionFree Y.A Z.A :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hh
  haveI : w.LiesOver (w.comap h) := ⟨rfl⟩
  exact Ideal.ramificationIdx_tower (R := C.A) (S := Y.A) (T := Z.A) (w.comap h) w

/-- Ramification indices are multiplicative along `Z → Y → C`. -/
lemma ramIdx_comp {Z Y C : AffOrbicurve k} (φ : Hom Z Y) (ψ : Hom Y C) (w : Ideal Z.A) :
    (letI := ((φ.f.comp ψ.f).toRingHom).toAlgebra; w.ramificationIdx C.A) =
      ψ.ramIdx (w.comap φ.f) * φ.ramIdx w :=
  ramificationIdx_comp ψ.f φ.f φ.injective w

/-- The composite `Z → Y → C` of finite étale morphisms is finite étale. -/
noncomputable def comp {Z Y C : AffOrbicurve k} (φ : Hom Z Y) (ψ : Hom Y C) : Hom Z C where
  f := φ.f.comp ψ.f
  injective := φ.injective.comp ψ.injective
  isIntegral := RingHom.IsIntegral.trans _ _ ψ.isIntegral φ.isIntegral
  etale w hw := by
    rw [ramIdx_comp, mul_assoc, ramIdx_mul_mult φ w hw]
    have hw' : (w.comap φ.f).IsMaximal := by
      letI : Algebra Y.A Z.A := φ.f.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral Y.A Z.A := ⟨φ.isIntegral⟩
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := Y.A) w
    exact ramIdx_mul_mult ψ _ hw'

@[simp]
lemma comp_f {Z Y C : AffOrbicurve k} (φ : Hom Z Y) (ψ : Hom Y C) : (φ.comp ψ).f = φ.f.comp ψ.f :=
  rfl

end AffOrbicurve.Hom
