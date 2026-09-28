/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.U2.TheoremG

/-!
# Theorem G: the `x`-coordinate descends to every object of `\overline{Loc}(E ∖ {0})`

For finite étale `φ : Z → E ∖ {0}` and `ψ : Z → Y` over `ℂ` (non-exceptional `j`), the pullback
`φ^* x` of the `x`-coordinate lies in `ψ^* ℂ[Y]` (`U2.theoremG`).

Proof: realize `Z → Y` inside `Ω = \overline{ℂ(t)}` as `F ⊆ L`; let `M` be the Galois closure of
`L / F` inside a finite Galois `N ⊇ L`. The coordinate ring `B` of `M` is unramified over `ℂ[Z]`
(`ramificationIdx_closure_eq_one`), hence over `ℂ[E ∖ 0]`; by `fixes_xP` every `σ ∈ Gal(N/F)`,
restricted to `B`, fixes `x`, so `x ∈ F`.
-/

open Polynomial Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin AffOrbicurve

namespace OrbicurveCores.U2

/-- The ramification index along a surjective ring map is `1`. -/
theorem ramificationIdx_of_surjective {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (hf : Function.Surjective f) (w : Ideal T) [w.IsPrime] :
    (letI := f.toAlgebra; w.ramificationIdx S) = 1 := by
  letI := f.toAlgebra
  haveI : Algebra.FormallyUnramified S T :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId S T) hf
  haveI : Algebra.FiniteType S T := Algebra.FiniteType.of_surjective (Algebra.ofId S T) hf
  haveI : Algebra.FormallyUnramified S (Localization.AtPrime w) :=
    Algebra.FormallyUnramified.comp S T _
  exact Ideal.ramificationIdx_eq_one w S

/-- Composing with an isomorphism on the right does not change ramification indices. -/
theorem ramificationIdx_comp_equiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain B] [IsDomain C] (g : A →+* B) (e : B ≃+* C) (w : Ideal C) [w.IsPrime] :
    (letI := ((e : B →+* C).comp g).toAlgebra; w.ramificationIdx A) =
      (letI := g.toAlgebra; (w.comap (e : B →+* C)).ramificationIdx A) := by
  rw [ramificationIdx_comp g (e : B →+* C) e.injective w,
    ramificationIdx_of_surjective (e : B →+* C) e.surjective w, mul_one]

/-- Composing with an isomorphism on the left does not change ramification indices. -/
theorem ramificationIdx_equiv_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain B] [IsDomain C] (e : A ≃+* B) (f : B →+* C) (hf : Function.Injective f)
    (w : Ideal C) [w.IsPrime] :
    (letI := (f.comp (e : A →+* B)).toAlgebra; w.ramificationIdx A) =
      (letI := f.toAlgebra; w.ramificationIdx B) := by
  rw [ramificationIdx_comp (e : A →+* B) f hf w, ramificationIdx_of_surjective _ e.surjective,
    one_mul]

/-- `ℂ(t) ⊆ K₀`. -/
theorem algebraMap_ratFunc_mem (f : RatFunc ℂ) : algebraMap (RatFunc ℂ) Ωt f ∈ K₀ ℂ tΩ := by
  have hp : ∀ p : Polynomial ℂ, algebraMap (RatFunc ℂ) Ωt (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      ∈ K₀ ℂ tΩ := fun p ↦ by
    have e : algebraMap (RatFunc ℂ) Ωt (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
        Polynomial.aeval tΩ p := by
      rw [← RatFunc.aeval_X_left_eq_algebraMap, tΩ]
      exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) Ωt)
        RatFunc.X p).symm
    rw [e]
    exact IntermediateField.algebra_adjoin_le_adjoin ℂ _
      (Polynomial.aeval_mem_adjoin_singleton ℂ tΩ)
  rw [← RatFunc.num_div_denom f, map_div₀]
  exact div_mem (hp _) (hp _)

/-- `Ω` is normal over `K₀`. -/
instance normal_Ωt : Normal (K₀ ℂ tΩ) Ωt := by
  haveI : Algebra.IsAlgebraic (K₀ ℂ tΩ) Ωt := ⟨fun x ↦ by
    have hx : IsAlgebraic (RatFunc ℂ) x := Algebra.IsAlgebraic.isAlgebraic x
    obtain ⟨p, hp0, hp⟩ := hx
    let ρ : RatFunc ℂ →+* K₀ ℂ tΩ :=
      (algebraMap (RatFunc ℂ) Ωt).codRestrict (K₀ ℂ tΩ).toSubring algebraMap_ratFunc_mem
    refine ⟨p.map ρ, (Polynomial.map_ne_zero_iff ρ.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact hp⟩
  exact { splits' := fun x ↦ IsAlgClosed.splits _ }

/-- Ramification indices along equal ring maps agree. -/
theorem ramificationIdx_congr {R S : Type*} [CommRing R] [CommRing S] {f g : R →+* S} (h : f = g)
    (w : Ideal S) :
    (letI := f.toAlgebra; w.ramificationIdx R) = (letI := g.toAlgebra; w.ramificationIdx R) := by
  subst h; rfl

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

omit [E.IsElliptic] in
/-- Finite étale covers of `E ∖ {0}` are schemes, unramified over `E ∖ {0}`. -/
theorem etale_punctured {Z : AffOrbicurve ℂ} (φ : Hom Z (punctured E)) (w : Ideal Z.A)
    (hw : w.IsMaximal) :
    (letI := φ.f.toRingHom.toAlgebra; w.ramificationIdx (punctured E).A) = 1 ∧ Z.mult w = 1 :=
  mul_eq_one.mp (φ.etale w hw)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Theorem G.** For finite étale `φ : Z → E ∖ {0}` and `ψ : Z → Y` (non-exceptional `j`),
`φ^* x ∈ ψ^* ℂ[Y]`. -/
theorem theoremG (hj : ∀ c ∈ excJ, E.j ≠ (c : ℂ)) {Y Z : AffOrbicurve ℂ}
    (φ : Hom Z (punctured E)) (ψ : Hom Z Y) : ∃ y : Y.A, ψ.f y = φ.f (xP E) := by
  classical
  obtain ⟨F, L, hF, hL, hFL, ψY, ψZ, hψ⟩ := exists_realization ψ
  set N : IntermediateField (K₀ ℂ tΩ) Ωt := normalClosure (K₀ ℂ tΩ) L Ωt
  haveI : FiniteDimensional (K₀ ℂ tΩ) N := inferInstance
  haveI : IsGalois (K₀ ℂ tΩ) N := by
    haveI : Algebra.IsSeparable (K₀ ℂ tΩ) N := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.mk
  have hLN : L ≤ N := IntermediateField.le_normalClosure L
  set M := closure tΩ F L (N := N)
  have hLM : L ≤ M := le_closure tΩ F L hLN
  have hMN : M ≤ N := closure_le tΩ F L
  have hFN : F ≤ N := hFL.trans hLN
  haveI : FiniteDimensional (K₀ ℂ tΩ) M := Module.Finite.of_injective (IntermediateField.inclusion hMN).toLinearMap
    (IntermediateField.inclusion hMN).injective
  have ht := transcendental_tΩ
  set B := coordRing ℂ tΩ M
  haveI : IsDedekindDomain B := isDedekindDomain_ring tΩ ht M
  haveI : Algebra.FiniteType ℂ B := finiteType_ring tΩ ht M
  haveI hLD : IsDedekindDomain (coordRing ℂ tΩ L) := isDedekindDomain_ring tΩ ht L
  set A := (punctured E).A
  set fB : A →ₐ[ℂ] B := (ringMap tΩ hLM).comp (ψZ.toAlgHom.comp φ.f)
  letI : Algebra A B := fB.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c ↦ (fB.commutes c).symm
  have hfB_inj : Function.Injective fB :=
    (ringMap_injective tΩ hLM).comp (ψZ.injective.comp φ.injective)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hfB_inj
  haveI : Algebra.IsIntegral A B := ⟨by
    have h1 : (ψZ.toAlgHom.comp φ.f).toRingHom.IsIntegral :=
      RingHom.IsIntegral.trans _ _ φ.isIntegral
        (RingHom.isIntegral_of_surjective _ ψZ.surjective)
    exact RingHom.IsIntegral.trans _ _ h1 (ringMap_isIntegral tΩ hLM)⟩
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ A B
  haveI : Module.Finite A B := Algebra.IsIntegral.finite
  -- `B` is unramified over `A`
  have hmaxL : ∀ w : Ideal B, w.IsMaximal → (w.comap (ringMap tΩ hLM)).IsMaximal := by
    intro w hw
    letI := algRing tΩ hLM
    haveI : Algebra.IsIntegral (coordRing ℂ tΩ L) B := ⟨ringMap_isIntegral tΩ hLM⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := coordRing ℂ tΩ L) w
  have hmaxZ : ∀ w : Ideal (coordRing ℂ tΩ L), w.IsMaximal →
      (w.comap ψZ.toRingEquiv.toRingHom).IsMaximal := fun w hw ↦
    Ideal.comap_isMaximal_of_surjective _ ψZ.surjective
  -- `L → F` is étale for the multiplicities of `Y`
  have hcomp : (ringMap tΩ hFL).toRingHom.comp ψY.toRingEquiv.toRingHom =
      ψZ.toRingEquiv.toRingHom.comp ψ.f.toRingHom := RingHom.ext fun a ↦ (hψ a).symm
  set mF : Ideal (coordRing ℂ tΩ F) → ℕ := fun v ↦ Y.mult (v.comap ψY.toRingEquiv.toRingHom)
  have hm : ∀ w : Ideal (coordRing ℂ tΩ L), w.IsMaximal →
      (letI := algRing tΩ hFL; w.ramificationIdx (coordRing ℂ tΩ F)) =
        mF (w.comap (ringMap tΩ hFL)) := by
    intro w hw
    haveI : IsDedekindDomain (coordRing ℂ tΩ F) := isDedekindDomain_ring tΩ ht F
    have h1 := ramificationIdx_equiv_comp ψY.toRingEquiv (ringMap tΩ hFL).toRingHom
      (ringMap_injective tΩ hFL) w
    have h1' := (ramificationIdx_congr hcomp w).symm.trans h1
    have h4 := ramificationIdx_comp_equiv ψ.f.toRingHom ψZ.toRingEquiv w
    have h2 := ψ.etale _ (hmaxZ w hw)
    have h3 := (etale_punctured E φ _ (hmaxZ w hw)).2
    rw [h3, mul_one] at h2
    have e : (w.comap (ringMap tΩ hFL).toRingHom).comap ψY.toRingEquiv.toRingHom =
        (w.comap ψZ.toRingEquiv.toRingHom).comap ψ.f.toRingHom := by
      rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
    change _ = Y.mult ((w.comap (ringMap tΩ hFL).toRingHom).comap ψY.toRingEquiv.toRingHom)
    rw [e]
    exact h1'.symm.trans (h4.trans h2)
  have het : ∀ w : Ideal B, w.IsMaximal → w.ramificationIdx A = 1 := by
    intro w hw
    have h1 := ramificationIdx_comp (ψZ.toAlgHom.comp φ.f).toRingHom (ringMap tΩ hLM).toRingHom
      (ringMap_injective tΩ hLM) w
    have h2 := ramificationIdx_comp_equiv φ.f.toRingHom ψZ.toRingEquiv
      (w.comap (ringMap tΩ hLM).toRingHom)
    have h3 := (etale_punctured E φ _ (hmaxZ _ (hmaxL w hw))).1
    -- a maximal ideal of `N` over `w`
    obtain ⟨u, hu, hwu⟩ : ∃ u : Ideal (coordRing ℂ tΩ N), u.IsMaximal ∧
        u.comap (ringMap tΩ hMN).toRingHom = w := by
      letI := algRing tΩ hMN
      haveI : Algebra.IsIntegral B (coordRing ℂ tΩ N) := ⟨ringMap_isIntegral tΩ hMN⟩
      exact Ideal.exists_ideal_over_maximal_of_isIntegral w (by
        intro x hx
        rw [RingHom.mem_ker] at hx
        rw [ringMap_injective tΩ hMN (hx.trans (map_zero _).symm)]
        exact w.zero_mem)
    have hu0 : u ≠ ⊥ := by
      rintro rfl
      apply not_isField_ring tΩ ht M
      rw [Ring.isField_iff_maximal_bot]
      have hb : w = ⊥ := by
        rw [← hwu]
        ext x
        simp only [Ideal.mem_comap, Ideal.mem_bot]
        exact ⟨fun h ↦ ringMap_injective tΩ hMN (h.trans (map_zero _).symm),
          fun h ↦ by rw [h, map_zero]⟩
      exact hb ▸ hw
    have h4 := ramificationIdx_closure_eq_one tΩ ht hFL hLN mF hm u hu0
    subst hwu
    refine h1.trans ?_
    exact (congrArg₂ (· * ·) (h2.trans h3) h4 : _ = 1 * 1)
  -- every `σ ∈ Gal(N/F)` fixes `x`
  set b := fB (xP E)
  have hfix : ∀ σ ∈ fixSub tΩ N F, σ (toN tΩ b) = toN tΩ b := by
    intro σ hσ
    rw [← toN_restrictClosureEquiv tΩ σ hσ]
    exact congrArg (toN tΩ) (fixes_xP E hj het (restrictClosureEquiv tΩ σ hσ))
  have hbF : ((toN tΩ b : N) : Ωt) ∈ F := mem_of_forall_fixSub tΩ hFN hfix
  set z := ψZ (φ.f (xP E))
  have hzF : ((z : L) : Ωt) ∈ F := hbF
  set zF : coordRing ℂ tΩ F := ⟨⟨_, hzF⟩, mem_coordRing_of_isIntegral tΩ hzF
    (isIntegral_of_mem_coordRing tΩ z)⟩
  refine ⟨ψY.symm zF, ψZ.injective ?_⟩
  rw [hψ, AlgEquiv.apply_symm_apply]
  exact Subtype.ext (Subtype.ext rfl)

end OrbicurveCores.U2
