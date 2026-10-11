/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Abhyankar.Tower
import OrbicurveCores.Genuine.Abhyankar.Generator

/-!
# U2f (part): composita of unramified extensions

Inside `Ω`, let `K' ≤ L₁, L₂ ≤ N ≤ L₁ ⊔ L₂`. If `L₂ / K'` is unramified over the prime `y'` of
`IC K'`, then `N / L₁` is unramified at every prime over `y'` (`ramIC_compositum`).
-/

open Polynomial

namespace OrbicurveCores.Abhyankar

noncomputable section

variable {B : Type} [CommRing B] [IsDedekindDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]

local notation "K" => FractionRing B
local notation "Ω" => AlgebraicClosure (FractionRing B)

set_option synthInstance.maxHeartbeats 200000 in
/-- **A generator with a simple root at a given prime.** -/
theorem exists_generator_IC {F F' : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K F'] (h : F ≤ F') (p₀ : Ideal (IC B F)) [p₀.IsMaximal]
    (hunr : ∀ q : Ideal (IC B F'), q.IsMaximal → q.comap (icMap h) = p₀ → ramIC h q = 1)
    (q₀ : Ideal (IC B F')) [q₀.IsMaximal] (hq₀ : q₀.comap (icMap h) = p₀) :
    ∃ θ : IC B F', F' ≤ (IntermediateField.adjoin F {((θ : F') : Ω)}).restrictScalars K ∧
      (letI := (icMap (B := B) h).toRingHom.toAlgebra;
        aeval θ (derivative (minpoly (IC B F) θ)) ∉ q₀) := by
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
  haveI : IsScalarTower ℂ (IC B F) (IC B F') :=
    IsScalarTower.of_algebraMap_eq fun b ↦ ((icMap (B := B) h).commutes _).symm
  haveI : IsScalarTower K F F' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ((IntermediateField.inclusion h).commutes x).symm
  haveI : FaithfulSMul (IC B F) (IC B F') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (icMap_injective h)
  haveI : Algebra.IsIntegral (IC B F) (IC B F') :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := B) x).tower_top⟩
  haveI : Module.Finite (IC B F) (IC B F') := Module.Finite.of_restrictScalars_finite B _ _
  haveI : FiniteDimensional F F' := FiniteDimensional.right K F F'
  obtain ⟨θ, hdeg, hder⟩ := exists_generator (R := IC B F) (S := IC B F') p₀ hunr q₀ hq₀
  refine ⟨θ, fun x hx ↦ ?_, hder⟩
  have htop := adjoin_eq_top_of_natDegree (R := IC B F) (S := IC B F') (KR := F) (KS := F') hdeg
  have hx' : (⟨x, hx⟩ : F') ∈ Algebra.adjoin F {algebraMap (IC B F') F' θ} := by
    rw [htop]; trivial
  let ι : F' →ₐ[F] Ω :=
    { toRingHom := F'.val.toRingHom
      commutes' := fun _ ↦ rfl }
  have hmap : (Algebra.adjoin F {algebraMap (IC B F') F' θ}).map ι =
      Algebra.adjoin F {((θ : F') : Ω)} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
  have hx'' : x ∈ Algebra.adjoin F {((θ : F') : Ω)} := by
    rw [← hmap]; exact ⟨_, hx', rfl⟩
  exact IntermediateField.algebra_adjoin_le_adjoin F _ hx''

omit [Algebra ℂ B] [Algebra.FiniteType ℂ B] in
lemma adjoin_mono_base {F F' : IntermediateField K Ω} (h : F ≤ F') (x : Ω) :
    (IntermediateField.adjoin F {x}).restrictScalars K ≤
      (IntermediateField.adjoin F' {x}).restrictScalars K := by
  rw [IntermediateField.restrictScalars_adjoin, IntermediateField.restrictScalars_adjoin]
  exact IntermediateField.adjoin.mono _ _ _ (Set.union_subset_union_left _ h)

omit [Algebra ℂ B] [Algebra.FiniteType ℂ B] in
/-- Evaluation commutes with the inclusions in a commutative square of fields. -/
lemma eval₂_icMap {K' L₁ L₂ N : IntermediateField K Ω} (h₁ : K' ≤ L₁) (h₂ : K' ≤ L₂)
    (hN₁ : L₁ ≤ N) (hN₂ : L₂ ≤ N) (θ : IC B L₂) (μ : (IC B K')[X]) :
    eval₂ (icMap (B := B) hN₁).toRingHom (icMap hN₂ θ) (μ.map (icMap (B := B) h₁).toRingHom) =
      icMap hN₂ (eval₂ (icMap (B := B) h₂).toRingHom θ μ) := by
  rw [eval₂_map]
  have : (icMap (B := B) hN₁).toRingHom.comp (icMap (B := B) h₁).toRingHom =
      (icMap (B := B) hN₂).toRingHom.comp (icMap (B := B) h₂).toRingHom := by
    ext x; rfl
  rw [this]
  exact (hom_eval₂ _ _ _ _).symm

set_option synthInstance.maxHeartbeats 200000 in
/-- **Composita of unramified extensions are unramified.** -/
theorem ramIC_compositum {K' L₁ L₂ N : IntermediateField K Ω} [FiniteDimensional K K']
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [FiniteDimensional K N]
    (h₁ : K' ≤ L₁) (h₂ : K' ≤ L₂) (hN₁ : L₁ ≤ N) (hN₂ : L₂ ≤ N) (hN : N ≤ L₁ ⊔ L₂)
    (Q : Ideal (IC B N)) [Q.IsMaximal]
    (hunr : ∀ q : Ideal (IC B L₂), q.IsMaximal →
      q.comap (icMap h₂) = Q.comap (icMap (h₂.trans hN₂)) → ramIC h₂ q = 1) :
    ramIC hN₁ Q = 1 := by
  set p₀ := Q.comap (icMap (B := B) (h₂.trans hN₂))
  haveI : p₀.IsMaximal := isMaximal_comap_icMap _ Q
  set q₀ := Q.comap (icMap (B := B) hN₂)
  haveI : q₀.IsMaximal := isMaximal_comap_icMap _ Q
  have hq₀ : q₀.comap (icMap h₂) = p₀ := by ext x; exact Iff.rfl
  obtain ⟨θ, hgen₂, hder⟩ := exists_generator_IC h₂ p₀ hunr q₀ hq₀
  refine ramIC_eq_one_of_aeval_derivative hN₁ (θ := icMap hN₂ θ) ?_ ?_
  · refine hN.trans (sup_le (fun x hx ↦ ?_) (hgen₂.trans (adjoin_mono_base h₁ _)))
    exact (IntermediateField.adjoin L₁ {((icMap hN₂ θ : N) : Ω)}).algebraMap_mem ⟨x, hx⟩
  letI i₁ : Algebra (IC B L₁) (IC B N) := (icMap (B := B) hN₁).toRingHom.toAlgebra
  letI : SMul (IC B L₁) (IC B N) := i₁.toSMul
  haveI : Module.IsTorsionFree (IC B L₁) (IC B N) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr (icMap_injective hN₁)
  have hint : IsIntegral (IC B L₁) (icMap hN₂ θ) := isIntegral_icMap hN₁ _
  letI : Algebra (IC B K') (IC B L₂) := (icMap (B := B) h₂).toRingHom.toAlgebra
  refine aeval_derivative_minpoly_notMem hint
    (P := (minpoly (IC B K') θ).map (icMap (B := B) h₁).toRingHom) ?_ ?_
  · rw [aeval_def]
    change eval₂ (icMap (B := B) hN₁).toRingHom _ _ = 0
    rw [eval₂_icMap h₁ h₂ hN₁ hN₂]
    have := minpoly.aeval (IC B K') θ
    rw [aeval_def] at this
    exact (congrArg (icMap (B := B) hN₂) this).trans (map_zero _)
  · rw [aeval_def, derivative_map]
    change eval₂ (icMap (B := B) hN₁).toRingHom _ _ ∉ Q
    rw [eval₂_icMap h₁ h₂ hN₁ hN₂]
    exact hder

end

end OrbicurveCores.Abhyankar
