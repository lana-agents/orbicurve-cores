/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Abhyankar.Tower
import Mathlib.FieldTheory.Galois.Infinite

/-!
# U2f (part): finite extensions of `B` inside `Ω`

Let `A` be an integrally closed domain, finite (integral and of finite type) over `B`.

* `embA : A →ₐ[B] Ω`, an embedding over `B`;
* `fieldA : IntermediateField K Ω`, the image of the fraction field of `A` (finite over `K`);
* `equivA : A ≃ₐ[B] IC B (fieldA)`;
* `exists_algEquiv_ne`: an element of `Ω ∖ K` is moved by some `σ ∈ Gal(Ω/K)` (char. zero);
* `icEquivMap`: the isomorphism `IC F ≃ IC σ(F)` induced by `σ`.
-/

open Polynomial

namespace OrbicurveCores.Abhyankar

noncomputable section

variable {B : Type} [CommRing B] [IsDedekindDomain B]

local notation "K" => FractionRing B
local notation "Ω" => AlgebraicClosure (FractionRing B)

/-- `B`-integrality inside an intermediate field is integrality in `Ω`. -/
lemma isIntegral_iff_val (F : IntermediateField K Ω) (x : F) :
    IsIntegral B x ↔ IsIntegral B (x : Ω) := by
  let f : F →ₐ[B] Ω := { F.val.toRingHom with commutes' := fun _ ↦ rfl }
  exact (isIntegral_algHom_iff f Subtype.val_injective).symm

variable (A : Type) [CommRing A] [IsDomain A] [Algebra B A] [Algebra.IsIntegral B A]
  [Module.IsTorsionFree B A]

instance isTorsionFree_Ω : Module.IsTorsionFree B Ω :=
  (Module.isTorsionFree_iff_algebraMap_injective).mpr (by
    rw [IsScalarTower.algebraMap_eq B K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective B K))

/-- An embedding of `A` into `Ω` over `B`. -/
def embA : A →ₐ[B] Ω := IsAlgClosed.lift

lemma embA_injective : Function.Injective (embA A (B := B)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (embA A (B := B)).toRingHom = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := B)
    ext b
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    change embA A (algebraMap B A b) = 0 ↔ _
    rw [AlgHom.commutes]
    exact ⟨fun h ↦ (FaithfulSMul.algebraMap_injective B Ω) (h.trans (map_zero _).symm),
      fun h ↦ by rw [h, map_zero]⟩
  have : a ∈ RingHom.ker (embA A (B := B)).toRingHom := ha
  rwa [hker] at this

/-- The embedding of the fraction field of `A`. -/
def jA : FractionRing A →+* Ω := IsFractionRing.lift (embA_injective A (B := B))

lemma jA_algebraMap (a : A) : jA A (B := B) (algebraMap A (FractionRing A) a) = embA A a :=
  IsFractionRing.lift_algebraMap _ a

/-- The image of the fraction field of `A` in `Ω`. -/
def fieldA : IntermediateField K Ω :=
  (jA A (B := B)).fieldRange.toIntermediateField fun k ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← (embA A (B := B)).commutes, ← (embA A (B := B)).commutes, ← jA_algebraMap,
      ← jA_algebraMap]
    exact div_mem ⟨_, rfl⟩ ⟨_, rfl⟩

lemma embA_mem (a : A) : embA A (B := B) a ∈ fieldA A :=
  ⟨algebraMap A (FractionRing A) a, jA_algebraMap A a⟩

instance finiteDimensional_fieldA [Algebra.FiniteType B A] :
    FiniteDimensional K (fieldA A (B := B)) := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra B A).FG)
  set E := IntermediateField.adjoin K ((embA A (B := B)) '' (s : Set A))
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
    obtain ⟨a, -, rfl⟩ := hx
    exact ((Algebra.IsIntegral.isIntegral (R := B) a).map (embA A)).tower_top
  have hle : ∀ a : A, embA A (B := B) a ∈ E := fun a ↦ by
    have ha : a ∈ Algebra.adjoin B (s : Set A) := by rw [hs]; trivial
    have : embA A (B := B) a ∈ Algebra.adjoin B ((embA A (B := B)) '' (s : Set A)) := by
      rw [← AlgHom.map_adjoin]; exact ⟨a, ha, rfl⟩
    refine Algebra.adjoin_le (S := E.toSubalgebra.restrictScalars B) ?_ this
    exact IntermediateField.subset_adjoin K _
  have hFE : fieldA A (B := B) ≤ E := by
    rintro x ⟨u, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) u
    rw [map_div₀, jA_algebraMap, jA_algebraMap]
    exact div_mem (hle a) (hle b)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hFE).toLinearMap
    (IntermediateField.inclusion hFE).injective

/-- `A → IC (fieldA)`. -/
def phiA : A →ₐ[B] IC B (fieldA A (B := B)) where
  toFun a := ⟨⟨embA A a, embA_mem A a⟩, (isIntegral_iff_val _ _).mpr
    ((Algebra.IsIntegral.isIntegral (R := B) a).map (embA A))⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  commutes' _ := by ext; simp; rfl

lemma icVal_phiA (a : A) : icVal _ (phiA A (B := B) a) = embA A a := rfl

lemma phiA_bijective [IsIntegrallyClosed A] : Function.Bijective (phiA A (B := B)) := by
  refine ⟨fun a b h ↦ embA_injective A (congrArg (icVal _) h), fun x ↦ ?_⟩
  obtain ⟨u, hu⟩ := (x : fieldA A (B := B)).2
  have hint : IsIntegral B (jA A (B := B) u) := by
    rw [hu]; exact (isIntegral_iff_val _ _).mp x.2
  let jB : FractionRing A →ₐ[B] Ω :=
    { jA A (B := B) with
      commutes' := fun b ↦ by
        change jA A (algebraMap B (FractionRing A) b) = _
        rw [IsScalarTower.algebraMap_apply B A (FractionRing A), jA_algebraMap,
          AlgHom.commutes] }
  have hu' : IsIntegral B u := (isIntegral_algHom_iff jB (jA A (B := B)).injective).mp hint
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hu'.tower_top (A := A))
  refine ⟨a, ?_⟩
  apply icVal_injective
  rw [icVal_phiA, ← jA_algebraMap, hu]
  rfl

/-- `A ≃ IC (fieldA)`. -/
def equivA [IsIntegrallyClosed A] : A ≃ₐ[B] IC B (fieldA A (B := B)) :=
  AlgEquiv.ofBijective (phiA A) (phiA_bijective A)

lemma icVal_equivA [IsIntegrallyClosed A] (a : A) :
    icVal _ (equivA A (B := B) a) = embA A a := rfl

/-- **Galois theory of `Ω / K`**: elements outside `K` are moved by automorphisms. -/
lemma exists_algEquiv_ne [CharZero B] {x : Ω} (hx : x ∉ Set.range (algebraMap K Ω)) :
    ∃ σ : Ω ≃ₐ[K] Ω, σ x ≠ x := by
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective B K)
  by_contra h
  push Not at h
  exact hx (IntermediateField.mem_bot.mp ((InfiniteGalois.mem_bot_iff_fixed x).mpr h))

/-- `σ` as a `B`-algebra map. -/
def algB (σ : Ω ≃ₐ[K] Ω) : Ω →ₐ[B] Ω := (σ : Ω →ₐ[K] Ω).restrictScalars B

/-- The map `IC F → IC σ(F)` induced by `σ`. -/
def icMapEquiv (F : IntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω) :
    IC B F →ₐ[B] IC B (F.map (σ : Ω →ₐ[K] Ω)) where
  toFun x := ⟨⟨σ (x : F), ⟨_, (x : F).2, rfl⟩⟩,
    (isIntegral_iff_val _ _).mpr (((isIntegral_iff_val _ _).mp x.2).map (algB σ))⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  commutes' b := by
    ext
    change σ (algebraMap B Ω b) = algebraMap B Ω b
    exact (algB σ).commutes b

lemma icVal_icMapEquiv (F : IntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω) (x : IC B F) :
    icVal _ (icMapEquiv F σ x) = σ (icVal F x) := rfl

lemma icMapEquiv_bijective (F : IntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω) :
    Function.Bijective (icMapEquiv (B := B) F σ) := by
  refine ⟨fun x y h ↦ icVal_injective F (σ.injective (congrArg (icVal _) h)), fun y ↦ ?_⟩
  obtain ⟨x, hxF, hx⟩ := (y : F.map (σ : Ω →ₐ[K] Ω)).2
  have hint : IsIntegral B (algB σ x) := by
    have hx' : σ x = ((y : F.map (σ : Ω →ₐ[K] Ω)) : Ω) := hx
    change IsIntegral B (σ x)
    rw [hx']; exact (isIntegral_iff_val _ _).mp y.2
  have hint' : IsIntegral B x := (isIntegral_algHom_iff (algB σ) σ.injective).mp hint
  refine ⟨⟨⟨x, hxF⟩, (isIntegral_iff_val _ _).mpr hint'⟩, ?_⟩
  apply icVal_injective
  exact hx

/-- `IC F ≃ IC σ(F)`. -/
def icEquiv (F : IntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω) :
    IC B F ≃ₐ[B] IC B (F.map (σ : Ω →ₐ[K] Ω)) :=
  AlgEquiv.ofBijective (icMapEquiv F σ) (icMapEquiv_bijective F σ)

lemma icVal_icEquiv (F : IntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω) (x : IC B F) :
    icVal _ (icEquiv F σ x) = σ (icVal F x) := rfl

end

end OrbicurveCores.Abhyankar
