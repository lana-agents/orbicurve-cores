/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Abhyankar.Unramified
import OrbicurveCores.Genuine.HomComp
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Pi1.Orbicurve.IntegralClosure

/-!
# U2f (part): towers of integral closures inside an algebraic closure

Let `B` be a Dedekind domain of finite type over `ℂ` with fraction field `K`, and `Ω` an algebraic
closure of `K`. For a finite intermediate field `K ⊆ F ⊆ Ω`, `IC F` is the integral closure of
`B` in `F` (a Dedekind domain of finite type over `ℂ` with fraction field `F`); for `F ≤ F'`,
`icMap : IC F → IC F'` is the inclusion.

* `ramIdx`: the ramification index of a maximal ideal of `IC F'` over `IC F`;
* `ramIdx_trans`: ramification indices are multiplicative in towers.
-/

open Polynomial

namespace OrbicurveCores.Abhyankar

noncomputable section

variable (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra ℂ B]

local notation "K" => FractionRing B
local notation "Ω" => AlgebraicClosure (FractionRing B)

instance charZero_B : CharZero B := charZero_of_injective_algebraMap (algebraMap ℂ B).injective

instance isSeparable_intermediateField (F : IntermediateField K Ω) : Algebra.IsSeparable K F := by
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective B K)
  exact Algebra.IsSeparable.of_integral _ _

/-- The integral closure of `B` in `F`. -/
abbrev IC (F : IntermediateField K Ω) := integralClosure B F

variable {B}

instance isDedekindDomain_IC (F : IntermediateField K Ω) [FiniteDimensional K F] :
    IsDedekindDomain (IC B F) :=
  integralClosure.isDedekindDomain B K F

instance isFractionRing_IC (F : IntermediateField K Ω) [FiniteDimensional K F] :
    IsFractionRing (IC B F) F :=
  integralClosure.isFractionRing_of_finite_extension K F

instance algebraComplex_IC (F : IntermediateField K Ω) : Algebra ℂ (IC B F) :=
  ((algebraMap B (IC B F)).comp (algebraMap ℂ B)).toAlgebra

instance isScalarTower_IC (F : IntermediateField K Ω) : IsScalarTower ℂ B (IC B F) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance finiteType_IC [Algebra.FiniteType ℂ B] (F : IntermediateField K Ω)
    [FiniteDimensional K F] :
    Algebra.FiniteType ℂ (IC B F) := by
  haveI : Module.Finite B (IC B F) := AffOrbicurve.integralClosure_finite B K F
  exact Algebra.FiniteType.trans (S := B) inferInstance inferInstance

instance finite_IC (F : IntermediateField K Ω) [FiniteDimensional K F] :
    Module.Finite B (IC B F) := AffOrbicurve.integralClosure_finite B K F

omit [Algebra ℂ B] in
lemma algebraMap_IC_injective (F : IntermediateField K Ω) :
    Function.Injective (algebraMap B (IC B F)) := by
  intro a b hab
  have h : algebraMap B Ω a = algebraMap B Ω b :=
    congrArg (fun x : IC B F ↦ ((x : F) : Ω)) hab
  rw [IsScalarTower.algebraMap_apply B K Ω, IsScalarTower.algebraMap_apply B K Ω] at h
  exact IsFractionRing.injective B K ((algebraMap K Ω).injective h)

instance isTorsionFree_IC (F : IntermediateField K Ω) : Module.IsTorsionFree B (IC B F) :=
  (Module.isTorsionFree_iff_algebraMap_injective).mpr (algebraMap_IC_injective F)

/-- `IC F → Ω`. -/
def icVal (F : IntermediateField K Ω) : IC B F →+* Ω :=
  (IntermediateField.val F).toRingHom.comp (Subalgebra.val (IC B F)).toRingHom

omit [Algebra ℂ B] in
lemma icVal_injective (F : IntermediateField K Ω) : Function.Injective (icVal (B := B) F) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext h)

omit [Algebra ℂ B] in
@[simp] lemma icVal_algebraMap (F : IntermediateField K Ω) (b : B) :
    icVal F (algebraMap B (IC B F) b) = algebraMap B Ω b := rfl

/-- The inclusion `IC F → IC F'` for `F ≤ F'`. -/
def icMap {F F' : IntermediateField K Ω} (h : F ≤ F') : IC B F →ₐ[B] IC B F' where
  toFun x := ⟨IntermediateField.inclusion h x.1,
    x.2.map ((IntermediateField.inclusion h).restrictScalars B)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Algebra ℂ B] in
@[simp] lemma coe_icMap {F F' : IntermediateField K Ω} (h : F ≤ F') (x : IC B F) :
    ((icMap h x : F') : Ω) = ((x : F) : Ω) := rfl

omit [Algebra ℂ B] in
lemma icMap_injective {F F' : IntermediateField K Ω} (h : F ≤ F') :
    Function.Injective (icMap (B := B) h) := fun x y hxy ↦ by
  have := congrArg (fun z : IC B F' ↦ ((z : F') : Ω)) hxy
  exact Subtype.ext (Subtype.ext this)

omit [Algebra ℂ B] in
@[simp] lemma icVal_icMap {F F' : IntermediateField K Ω} (h : F ≤ F') (x : IC B F) :
    icVal F' (icMap h x) = icVal F x := rfl

omit [Algebra ℂ B] in
lemma icMap_comp {F F' F'' : IntermediateField K Ω} (h : F ≤ F') (h' : F' ≤ F'') :
    (icMap (B := B) h').comp (icMap h) = icMap (h.trans h') := rfl

/-- The ramification index of a prime of `IC F'` over `IC F`. -/
def ramIC {F F' : IntermediateField K Ω} (h : F ≤ F') (P : Ideal (IC B F')) : ℕ :=
  letI := (icMap (B := B) h).toRingHom.toAlgebra
  P.ramificationIdx (IC B F)

/-- Ramification indices are multiplicative along injective maps of Dedekind domains. -/
lemma ramificationIdx_comp' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsDedekindDomain S] [IsDomain T] (f : R →+* S) (g : S →+* T)
    (hg : Function.Injective g) (P : Ideal T) :
    (letI := (g.comp f).toAlgebra; P.ramificationIdx R) =
      (letI := f.toAlgebra; (P.comap g).ramificationIdx R) *
        (letI := g.toAlgebra; P.ramificationIdx S) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra R T := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.IsTorsionFree S T := (Module.isTorsionFree_iff_algebraMap_injective).mpr hg
  haveI : P.LiesOver (P.comap g) := ⟨rfl⟩
  exact Ideal.ramificationIdx_tower (R := R) (S := S) (T := T) (P.comap g) P

/-- The ramification index does not depend on how the algebra structure is presented. -/
lemma ramificationIdx_congr {R S : Type*} [CommRing R] [CommRing S] {i₁ i₂ : Algebra R S}
    (h : @algebraMap R S _ _ i₁ = @algebraMap R S _ _ i₂) (P : Ideal S) :
    (letI := i₁; P.ramificationIdx R) = (letI := i₂; P.ramificationIdx R) := by
  have : i₁ = i₂ := Algebra.algebra_ext _ _ fun r ↦ congrFun (congrArg DFunLike.coe h) r
  rw [this]

/-- `e(P | B) = e(P ∩ IC F | B) · e(P | IC F)`. -/
lemma ramificationIdx_B_eq {F F' : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K F'] (h : F ≤ F') (P : Ideal (IC B F')) :
    P.ramificationIdx B = (P.comap (icMap h)).ramificationIdx B * ramIC h P := by
  have := ramificationIdx_comp' (algebraMap B (IC B F)) (icMap (B := B) h).toRingHom
    (icMap_injective h) P
  rw [ramificationIdx_congr (i₁ := (((icMap (B := B) h).toRingHom).comp
    (algebraMap B (IC B F))).toAlgebra) (i₂ := inferInstance) (by ext; rfl) P,
    ramificationIdx_congr (i₁ := (algebraMap B (IC B F)).toAlgebra) (i₂ := inferInstance)
      (by ext; rfl)] at this
  exact this

/-- `e(P | IC F) = e(P ∩ IC F' | IC F) · e(P | IC F')`. -/
lemma ramIC_trans {F F' F'' : IntermediateField K Ω} [FiniteDimensional K F']
    (h : F ≤ F') (h' : F' ≤ F'') (P : Ideal (IC B F'')) :
    ramIC (h.trans h') P = ramIC h (P.comap (icMap h')) * ramIC h' P := by
  have := ramificationIdx_comp' (icMap (B := B) h).toRingHom (icMap (B := B) h').toRingHom
    (icMap_injective h') P
  exact this

/-- The algebra structure of `F'` over `F` for `F ≤ F'`. -/
abbrev inclAlg {F F' : IntermediateField K Ω} (h : F ≤ F') : Algebra F F' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

omit [Algebra ℂ B] in
/-- **Generation.** If `F' ⊆ F(θ)` inside `Ω`, then `F' = F[θ]`. -/
lemma adjoin_eq_top_of_le {F F' : IntermediateField K Ω} (h : F ≤ F') (θ : F')
    (hle : F' ≤ (IntermediateField.adjoin F {(θ : Ω)}).restrictScalars K) :
    letI := inclAlg h; Algebra.adjoin F {θ} = ⊤ := by
  letI := inclAlg h
  let ι : F' →ₐ[F] Ω :=
    { toRingHom := F'.val.toRingHom
      commutes' := fun _ ↦ rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have halg : IsAlgebraic F (θ : Ω) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := K) (θ : Ω)).tower_top F
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hx : (x : Ω) ∈ IntermediateField.adjoin F {(θ : Ω)} := hle x.2
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg] at hx
  have hmap : (Algebra.adjoin F {θ}).map ι = Algebra.adjoin F {(θ : Ω)} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [hι hyx] at hy

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through towers of integral closures is slow
/-- **Unramifiedness in a tower from the derivative of a minimal polynomial.** -/
theorem ramIC_eq_one_of_aeval_derivative {F F' : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K F'] (h : F ≤ F') {θ : IC B F'}
    (hgen : F' ≤ (IntermediateField.adjoin F {((θ : F') : Ω)}).restrictScalars K)
    {P : Ideal (IC B F')} [P.IsMaximal]
    (hP : letI := (icMap (B := B) h).toRingHom.toAlgebra
      aeval θ (derivative (minpoly (IC B F) θ)) ∉ P) : ramIC h P = 1 := by
  letI i₁ : Algebra (IC B F) (IC B F') := (icMap (B := B) h).toRingHom.toAlgebra
  letI : SMul (IC B F) (IC B F') := i₁.toSMul
  letI : Module (IC B F) (IC B F') := i₁.toModule
  letI i₂ : Algebra F F' := inclAlg h
  letI : SMul F F' := i₂.toSMul
  letI : Module F F' := i₂.toModule
  letI i₃ : Algebra (IC B F) F' := ((algebraMap F F').comp (algebraMap (IC B F) F)).toAlgebra
  letI : SMul (IC B F) F' := i₃.toSMul
  haveI : IsScalarTower (IC B F) F F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (IC B F) (IC B F') F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower B (IC B F) (IC B F') :=
    IsScalarTower.of_algebraMap_eq fun b ↦ ((icMap (B := B) h).commutes b).symm
  haveI : IsScalarTower K F F' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ((IntermediateField.inclusion h).commutes x).symm
  haveI : FaithfulSMul (IC B F) (IC B F') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (icMap_injective h)
  haveI : Algebra.IsIntegral (IC B F) (IC B F') :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := B) x).tower_top⟩
  haveI : Module.Finite (IC B F) (IC B F') := Module.Finite.of_restrictScalars_finite B _ _
  haveI : FiniteDimensional F F' := FiniteDimensional.right K F F'
  have hgen' : Algebra.adjoin F {algebraMap (IC B F') F' θ} = ⊤ := adjoin_eq_top_of_le h _ hgen
  haveI : CharZero (IC B F) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (IC B F)).injective
  exact Abhyankar.ramificationIdx_eq_one_of_aeval_derivative (KR := F) (KS := F') hgen' hP


set_option synthInstance.maxHeartbeats 200000 in
-- instance search through towers of integral closures is slow
/-- **Kummer generators in a tower are unramified.** -/
theorem ramIC_eq_one_of_pow_eq {F F' : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K F'] (h : F ≤ F') {θ : IC B F'}
    (hgen : F' ≤ (IntermediateField.adjoin F {((θ : F') : Ω)}).restrictScalars K)
    {m : ℕ} (hm : m ≠ 0) {c : IC B F} (hθ : θ ^ m = icMap h c) {P : Ideal (IC B F')}
    [P.IsMaximal] (hc : icMap h c ∉ P) : ramIC h P = 1 := by
  letI i₁ : Algebra (IC B F) (IC B F') := (icMap (B := B) h).toRingHom.toAlgebra
  letI : SMul (IC B F) (IC B F') := i₁.toSMul
  letI : Module (IC B F) (IC B F') := i₁.toModule
  letI i₂ : Algebra F F' := inclAlg h
  letI : SMul F F' := i₂.toSMul
  letI : Module F F' := i₂.toModule
  letI i₃ : Algebra (IC B F) F' := ((algebraMap F F').comp (algebraMap (IC B F) F)).toAlgebra
  letI : SMul (IC B F) F' := i₃.toSMul
  haveI : IsScalarTower (IC B F) F F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (IC B F) (IC B F') F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower B (IC B F) (IC B F') :=
    IsScalarTower.of_algebraMap_eq fun b ↦ ((icMap (B := B) h).commutes b).symm
  haveI : IsScalarTower K F F' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ((IntermediateField.inclusion h).commutes x).symm
  haveI : FaithfulSMul (IC B F) (IC B F') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (icMap_injective h)
  haveI : Algebra.IsIntegral (IC B F) (IC B F') :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := B) x).tower_top⟩
  haveI : Module.Finite (IC B F) (IC B F') := Module.Finite.of_restrictScalars_finite B _ _
  haveI : FiniteDimensional F F' := FiniteDimensional.right K F F'
  have hgen' : Algebra.adjoin F {algebraMap (IC B F') F' θ} = ⊤ := adjoin_eq_top_of_le h _ hgen
  haveI : CharZero (IC B F) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (IC B F)).injective
  exact Abhyankar.ramificationIdx_eq_one_of_pow_eq (KR := F) (KS := F') hgen' hm hθ hc

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through towers of integral closures is slow
omit [Algebra ℂ B] in
lemma isIntegral_icMap {F F' : IntermediateField K Ω} (h : F ≤ F') :
    (icMap (B := B) h).toRingHom.IsIntegral := by
  letI i₁ : Algebra (IC B F) (IC B F') := (icMap (B := B) h).toRingHom.toAlgebra
  letI : SMul (IC B F) (IC B F') := i₁.toSMul
  haveI : IsScalarTower B (IC B F) (IC B F') :=
    IsScalarTower.of_algebraMap_eq fun b ↦ ((icMap (B := B) h).commutes b).symm
  exact fun x ↦ (Algebra.IsIntegral.isIntegral (R := B) x).tower_top

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through towers of integral closures is slow
omit [Algebra ℂ B] in
/-- The contraction of a maximal ideal along `icMap` is maximal. -/
lemma isMaximal_comap_icMap {F F' : IntermediateField K Ω} (h : F ≤ F') (Q : Ideal (IC B F'))
    [Q.IsMaximal] : (Q.comap (icMap (B := B) h)).IsMaximal := by
  letI i₁ : Algebra (IC B F) (IC B F') := (icMap (B := B) h).toRingHom.toAlgebra
  letI : SMul (IC B F) (IC B F') := i₁.toSMul
  haveI : Algebra.IsIntegral (IC B F) (IC B F') := ⟨isIntegral_icMap h⟩
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := IC B F) Q

omit [Algebra ℂ B] in
lemma under_comap_icMap {F F' : IntermediateField K Ω} (h : F ≤ F') (Q : Ideal (IC B F')) :
    (Q.comap (icMap (B := B) h)).under B = Q.under B := by
  ext b
  simp only [Ideal.under, Ideal.mem_comap]
  rw [← (icMap (B := B) h).commutes b]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through towers of integral closures is slow
omit [Algebra ℂ B] in
/-- Going up along `icMap`. -/
lemma exists_comap_icMap_eq {F F' : IntermediateField K Ω} (h : F ≤ F') (w : Ideal (IC B F))
    [w.IsMaximal] : ∃ Q : Ideal (IC B F'), Q.IsMaximal ∧ Q.comap (icMap (B := B) h) = w := by
  letI i₁ : Algebra (IC B F) (IC B F') := (icMap (B := B) h).toRingHom.toAlgebra
  letI : SMul (IC B F) (IC B F') := i₁.toSMul
  haveI : Algebra.IsIntegral (IC B F) (IC B F') := ⟨isIntegral_icMap h⟩
  obtain ⟨Q, hQ, hQw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := IC B F') w (by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (IC B F) (IC B F'))).mp
      (icMap_injective h)]
    exact bot_le)
  exact ⟨Q, hQ, hQw⟩

end

end OrbicurveCores.Abhyankar
