/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Pi1.Orbicurve.Elliptic

/-!
# U2a: the hemi-elliptic quotient belongs to `\overline{Loc}_k(E ∖ 0)`

Let `k` be a field of characteristic `0` and `E / k` an elliptic curve. The function field
`L = k(E)` is a quadratic, hence Galois, extension of `K = k(x)`, so the Galois group acts
transitively on the primes of the coordinate ring of `E ∖ {0}` (the integral closure of `k[x]` in
`L`) over a given prime of `k[x]`, and all of them have the same ramification index. Hence the
`x`-coordinate `E ∖ {0} → A¹` is a finite étale morphism onto the punctured hemi-elliptic
orbicurve `(E ∖ {0}) / ±1` in the sense of pi1's `AffOrbicurve.Hom`.

* `finrank_functionField`: `[k(E) : k(x)] = 2`;
* `isGalois_functionField`: `k(E) / k(x)` is Galois;
* `hemiHom`: the finite étale morphism `E ∖ {0} → (E ∖ {0}) / ±1`;
* `homId`: the identity morphism of an affine orbicurve;
* `locBar_hemi`: `(E ∖ {0}) / ±1 ∈ \overline{Loc}_k(E ∖ {0})`.
-/

universe u

open Polynomial Ideal

namespace OrbicurveCores.Genuine

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] FractionRing.liftAlgebra

instance : Algebra.IsIntegral k[X] E.toAffine.CoordinateRing := inferInstance

instance : IsLocalization
    (Algebra.algebraMapSubmonoid E.toAffine.CoordinateRing (nonZeroDivisors k[X]))
    E.toAffine.FunctionField :=
  AffOrbicurve.isLocalization_algebraMapSubmonoid_of_isAlgebraic k[X]
    E.toAffine.CoordinateRing E.toAffine.FunctionField

omit [CharZero k] [E.IsElliptic] in
/-- `[k(E) : k(x)] = 2`. -/
lemma finrank_functionField :
    Module.finrank (FractionRing k[X]) E.toAffine.FunctionField = 2 := by
  have b := (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine).localizationLocalization
    (FractionRing k[X]) (nonZeroDivisors k[X]) E.toAffine.FunctionField
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

instance : Algebra.IsQuadraticExtension (FractionRing k[X]) E.toAffine.FunctionField :=
  ⟨finrank_functionField E⟩

/-- `k(E) / k(x)` is Galois. -/
instance isGalois_functionField :
    IsGalois (FractionRing k[X]) E.toAffine.FunctionField := inferInstance

local notation "K" => FractionRing k[X]
local notation "L" => E.toAffine.FunctionField
local notation "Gal" => (E.toAffine.FunctionField ≃ₐ[FractionRing k[X]] E.toAffine.FunctionField)

instance : SMulCommClass Gal k[X] L where
  smul_comm g a b := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', IsScalarTower.algebraMap_apply k[X] K L,
      AlgEquiv.smul_def, AlgEquiv.commutes]

instance : IsFractionRing (AffOrbicurve.puncturedRing E) L :=
  integralClosure.isFractionRing_of_finite_extension K L

/-- The Galois group of `k(E) / k(x)` is a Galois group of the coordinate ring of `E ∖ {0}` over
`k[x]`. -/
instance isGaloisGroup_puncturedRing : IsGaloisGroup Gal k[X] (AffOrbicurve.puncturedRing E) :=
  IsGaloisGroup.of_isFractionRing Gal k[X] (AffOrbicurve.puncturedRing E) K L

omit [E.IsElliptic] in
/-- All primes of `E ∖ {0}` over a prime `v` of `k[x]` have ramification index
`ramificationIdxIn v`. -/
lemma ramificationIdxIn_under (w : Ideal (AffOrbicurve.puncturedRing E)) [w.IsPrime] :
    (w.under k[X]).ramificationIdxIn (AffOrbicurve.puncturedRing E) = w.ramificationIdx k[X] :=
  Ideal.ramificationIdxIn_eq_ramificationIdx (w.under k[X]) w Gal

omit [CharZero k] [E.IsElliptic] in
lemma toAlgebra_eq :
    (IsScalarTower.toAlgHom k k[X] (AffOrbicurve.puncturedRing E)).toRingHom.toAlgebra =
      (inferInstance : Algebra k[X] (AffOrbicurve.puncturedRing E)) :=
  Algebra.algebra_ext _ _ fun _ ↦ rfl

omit [CharZero k] [E.IsElliptic] in
lemma comap_eq (w : Ideal (AffOrbicurve.puncturedRing E)) :
    w.comap (IsScalarTower.toAlgHom k k[X] (AffOrbicurve.puncturedRing E)) = w.under k[X] :=
  rfl

omit [E.IsElliptic] in
lemma punctured_mult (w : Ideal (AffOrbicurve.punctured E).A) :
    (AffOrbicurve.punctured E).mult w = 1 := rfl

omit [E.IsElliptic] in
lemma hemi_mult (v : Ideal (AffOrbicurve.hemi E).A) :
    (AffOrbicurve.hemi E).mult v = (show Ideal k[X] from v).ramificationIdxIn
      (AffOrbicurve.puncturedRing E) := rfl

/-- The `x`-coordinate, as a map of coordinate rings `k[x] → k[E ∖ 0]`. -/
noncomputable def hemiMap : (AffOrbicurve.hemi E).A →ₐ[k] (AffOrbicurve.punctured E).A :=
  IsScalarTower.toAlgHom k k[X] (AffOrbicurve.puncturedRing E)

omit [E.IsElliptic] in
lemma ramIdx_eq (w : Ideal (AffOrbicurve.punctured E).A) :
    (letI := (hemiMap E).toRingHom.toAlgebra
     w.ramificationIdx (AffOrbicurve.hemi E).A) =
      (show Ideal (AffOrbicurve.puncturedRing E) from w).ramificationIdx k[X] := by
  have h : (hemiMap E).toRingHom.toAlgebra =
      (inferInstance : Algebra k[X] (AffOrbicurve.puncturedRing E)) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  rw [h]
  rfl

/-- **The `x`-coordinate `E ∖ {0} → (E ∖ {0}) / ±1`** is a finite étale morphism of affine
orbicurves. -/
noncomputable def hemiHom : AffOrbicurve.Hom (AffOrbicurve.punctured E) (AffOrbicurve.hemi E) where
  f := hemiMap E
  injective := FaithfulSMul.algebraMap_injective k[X] (AffOrbicurve.puncturedRing E)
  isIntegral := Algebra.IsIntegral.isIntegral (R := k[X]) (A := AffOrbicurve.puncturedRing E)
  etale w hw := by
    rw [ramIdx_eq, punctured_mult, hemi_mult, mul_one]
    obtain ⟨w', rfl⟩ : ∃ w' : Ideal (AffOrbicurve.puncturedRing E), w' = w := ⟨w, rfl⟩
    have : w'.IsPrime := hw.isPrime
    exact (ramificationIdxIn_under E w').symm

omit [CharZero k] in
/-- The identity morphism of an affine orbicurve. -/
noncomputable def homId (Y : AffOrbicurve k) : AffOrbicurve.Hom Y Y where
  f := AlgHom.id k Y.A
  injective := Function.injective_id
  isIntegral := (Algebra.IsIntegral.isIntegral (R := Y.A) (A := Y.A) : ∀ _, _)
  etale w hw := by
    have h : (AlgHom.id k Y.A).toRingHom.toAlgebra = Algebra.id Y.A :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    have : w.IsPrime := hw.isPrime
    have hc : comap (AlgHom.id k Y.A) w = w := Ideal.ext fun _ ↦ Iff.rfl
    rw [h, hc, Ideal.ramificationIdx_eq_one w Y.A, one_mul]

omit [E.IsElliptic] in
/-- **U2a.** The punctured hemi-elliptic orbicurve `(E ∖ {0}) / ±1` belongs to
`\overline{Loc}_k(E ∖ {0})`. -/
theorem locBar_hemi : AffOrbicurve.LocBar (AffOrbicurve.punctured E) (AffOrbicurve.hemi E) :=
  ⟨AffOrbicurve.punctured E, ⟨homId _⟩, ⟨hemiHom E⟩⟩

end OrbicurveCores.Genuine
