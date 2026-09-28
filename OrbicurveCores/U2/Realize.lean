/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.U2.Noether
import Pi1.Orbicurve.Embed
import Pi1.Orbicurve.Pullback
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Realizing a finite étale cover of affine orbicurves over `ℂ` inside a fixed field

Let `φ : Z → C` be a finite étale morphism of affine orbicurves over `ℂ`. With `Ω` an algebraic
closure of `ℂ(t)` and `c₀ ∈ ℂ[C]` a Noether normalization parameter, `ℂ[C] ≅ coordRing F` and
`ℂ[Z] ≅ coordRing L` for intermediate fields `ℂ(t) ⊆ F ⊆ L ⊆ Ω`, compatibly with `φ`
(`U2.exists_realization`), in the framework of `Pi1.Orbicurve.Subfield`.
-/

open Polynomial IntermediateField
open IntermediateField.algebraAdjoinAdjoin

namespace OrbicurveCores.U2

open AffOrbicurve

/-- The ambient field: an algebraic closure of `ℂ(t)`. -/
abbrev Ωt : Type := AlgebraicClosure (RatFunc ℂ)

/-- The transcendental `t ∈ Ω`. -/
noncomputable def tΩ : Ωt := algebraMap (RatFunc ℂ) Ωt RatFunc.X

theorem transcendental_tΩ : Transcendental ℂ tΩ := by
  have h := RatFunc.transcendental_X (K := ℂ)
  unfold tΩ
  intro halg
  apply h
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) Ωt)
    (algebraMap (RatFunc ℂ) Ωt).injective).mp halg

/-- `k[t] → coordRing ⊥` is bijective. -/
theorem bijective_algebraMap_bot :
    Function.Bijective (algebraMap (A₀ ℂ tΩ) (coordRing ℂ tΩ (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt))) := by
  refine ⟨fun a b h ↦ Subtype.ext (congrArg (fun c : coordRing ℂ tΩ
    (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt) ↦ ((c : (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt)) : Ωt)) h),
    fun b ↦ ?_⟩
  have hb : ((b : (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt)) : Ωt) ∈
      (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt) := (b : (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt)).2
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hb
  haveI := isPrincipalIdealRing_A₀ transcendental_tΩ
  have hzint : IsIntegral (A₀ ℂ tΩ) z := by
    have h1 := isIntegral_of_mem_coordRing tΩ b
    rw [← hz] at h1
    haveI : IsScalarTower (A₀ ℂ tΩ) (K₀ ℂ tΩ) Ωt := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact (isIntegral_algebraMap_iff (algebraMap (K₀ ℂ tΩ) Ωt).injective).mp h1
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A₀ ℂ tΩ) (K := K₀ ℂ tΩ)).mp hzint
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  rw [← hz, ← ha]
  rfl

/-- `k[t] ≅ coordRing ⊥`. -/
noncomputable def eBot : A₀ ℂ tΩ ≃ₐ[ℂ] coordRing ℂ tΩ (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt) :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℂ (A₀ ℂ tΩ) _) bijective_algebraMap_bot

/-- The map `coordRing ⊥ = ℂ[t] → A`, `t ↦ c₀`. -/
noncomputable def gBase {A : Type} [CommRing A] [Algebra ℂ A] (c₀ : A) :
    coordRing ℂ tΩ (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt) →ₐ[ℂ] A :=
  (aeval c₀).comp ((Polynomial.algEquivOfTranscendental ℂ tΩ transcendental_tΩ).symm.toAlgHom.comp
    eBot.symm.toAlgHom)

theorem gBase_injective {A : Type} [CommRing A] [Algebra ℂ A] {c₀ : A} (hc : Transcendental ℂ c₀) :
    Function.Injective (gBase c₀) := by
  have h1 : Function.Injective (aeval c₀ : ℂ[X] →ₐ[ℂ] A) := transcendental_iff_injective.mp hc
  exact h1.comp ((Polynomial.algEquivOfTranscendental ℂ tΩ transcendental_tΩ).symm.injective.comp
    eBot.symm.injective)

theorem gBase_range {A : Type} [CommRing A] [Algebra ℂ A] (c₀ : A) (a : A)
    (ha : a ∈ Algebra.adjoin ℂ {c₀}) : ∃ b, gBase c₀ b = a := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨p, rfl⟩ := ha
  refine ⟨eBot (Polynomial.algEquivOfTranscendental ℂ tΩ transcendental_tΩ p), ?_⟩
  simp [gBase]

theorem gBase_isIntegral {A : Type} [CommRing A] [Nontrivial A] [Algebra ℂ A] {c₀ : A}
    (hint : ∀ a : A, IsIntegral (Algebra.adjoin ℂ {c₀}) a) : (gBase c₀).toRingHom.IsIntegral := by
  classical
  intro a
  obtain ⟨q, hqm, hq⟩ := hint a
  -- lift the coefficients of `q`
  set S := Algebra.adjoin ℂ {c₀}
  have hsurj : ∀ s : S, ∃ b, gBase c₀ b = s := fun s ↦ gBase_range c₀ s s.2
  choose lift hlift using hsurj
  set σ : coordRing ℂ tΩ (⊥ : IntermediateField (K₀ ℂ tΩ) Ωt) →+* S :=
    (gBase c₀).toRingHom.codRestrict S.toSubring fun b ↦ aeval_mem_adjoin_singleton ℂ c₀
  have hσ : Function.Surjective σ := fun s ↦ ⟨lift s, Subtype.ext (hlift s)⟩
  obtain ⟨p, hpq, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts q |>.mpr fun n ↦ hσ (q.coeff n)) hqm
  refine ⟨p, hpm, ?_⟩
  have : (gBase c₀).toRingHom = (algebraMap S A).comp σ := rfl
  rw [this, ← eval₂_map, hpq]
  exact hq

/-- **Realization** of a finite étale morphism `Z → C` inside `Ω`. -/
theorem exists_realization {C Z : AffOrbicurve ℂ} (φ : Hom Z C) :
    ∃ (F L : IntermediateField (K₀ ℂ tΩ) Ωt) (_ : FiniteDimensional (K₀ ℂ tΩ) F)
      (_ : FiniteDimensional (K₀ ℂ tΩ) L) (hFL : F ≤ L) (ψC : C.A ≃ₐ[ℂ] coordRing ℂ tΩ F)
      (ψZ : Z.A ≃ₐ[ℂ] coordRing ℂ tΩ L), ∀ a, ψZ (φ.f a) = ringMap tΩ hFL (ψC a) := by
  obtain ⟨c₀, hc₀, hint⟩ := exists_transcendental_isIntegral (k := ℂ) (A := C.A) C.not_isField
  obtain ⟨F, hFfin, -, ψC, -⟩ := exists_algEquiv_coordRing tΩ (B := ⊥) C.A (gBase c₀)
    (gBase_injective hc₀) (gBase_isIntegral hint)
  set g₂ : coordRing ℂ tΩ F →ₐ[ℂ] Z.A := φ.f.comp ψC.symm.toAlgHom
  have hg₂ : Function.Injective g₂ := φ.injective.comp ψC.symm.injective
  have hg₂i : g₂.toRingHom.IsIntegral := by
    intro z
    obtain ⟨p, hpm, hp⟩ := φ.isIntegral z
    refine ⟨p.map ψC.toRingEquiv.toRingHom, hpm.map _, ?_⟩
    rw [eval₂_map]
    convert hp using 2
    ext a
    simp [g₂]
  obtain ⟨L, hLfin, hFL, ψZ, hψZ⟩ := exists_algEquiv_coordRing tΩ (B := F) Z.A g₂ hg₂ hg₂i
  refine ⟨F, L, hFfin, hLfin, hFL, ψC, ψZ, fun a ↦ ?_⟩
  have := hψZ (ψC a)
  simp only [g₂, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] at this
  exact this

end OrbicurveCores.U2
