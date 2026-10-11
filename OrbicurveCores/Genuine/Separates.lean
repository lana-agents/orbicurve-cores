/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.ForMathlib.Abhyankar.Steps
import OrbicurveCores.ForMathlib.Abhyankar.Embed
import OrbicurveCores.Genuine.Descent

/-!
# U2f: fibre products separate functions

`compositumSeparates : Genuine.CompositumSeparates ℂ`. Given a finite étale `q : Z → Y` with
`Z` scheme-like and `c ∈ A_Z ∖ A_Y`, embed `A_Z` into an algebraic closure `Ω` of `k(Y)` (with
image field `F`), choose `σ ∈ Gal(Ω / k(Y))` moving `c`, and let `W` be the normalisation of `Y`
in `G = F ⊔ σ(F)`. Both inclusions `F, σ(F) → G` are unramified by Abhyankar's lemma, so they
give finite étale `r₁, r₂ : W → Z` with `q r₁ = q r₂` and `r₁^* c ≠ r₂^* c`.
-/

open Polynomial AffOrbicurve

namespace OrbicurveCores.Abhyankar

section Iso

/-- Ramification indices over `R` are invariant under `R`-algebra isomorphisms. -/
lemma ramificationIdx_comap_algEquiv {R S S₁ : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDedekindDomain S] [CommRing S₁] [IsDedekindDomain S₁] [Algebra R S] [Algebra R S₁]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree R S₁] (e : S ≃ₐ[R] S₁) (P : Ideal S₁)
    [P.IsPrime] (hp : P.under R ≠ ⊥) :
    (P.comap e).ramificationIdx R = P.ramificationIdx R := by
  have hu : (P.comap e).under R = P.under R := by
    ext r
    simp only [Ideal.under, Ideal.mem_comap]
    rw [e.commutes r]
  haveI : P.LiesOver (P.under R) := ⟨rfl⟩
  haveI : (P.comap e).LiesOver (P.under R) := ⟨hu.symm⟩
  haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (P.under R) P hp,
    ← Ideal.ramificationIdx'_eq_ramificationIdx (P.under R) (P.comap e) hp,
    Ideal.ramificationIdx'_comap_eq]

/-- Isomorphisms are unramified. -/
lemma ramificationIdx_ringEquiv {S S₁ : Type*} [CommRing S] [CommRing S₁] [IsDedekindDomain S₁]
    (e : S ≃+* S₁) (P : Ideal S₁) [P.IsMaximal] (hP : P ≠ ⊥) :
    (letI := (e : S →+* S₁).toAlgebra; P.ramificationIdx S) = 1 := by
  letI := (e : S →+* S₁).toAlgebra
  set p := P.comap (e : S →+* S₁)
  haveI : P.LiesOver p := ⟨rfl⟩
  have hmap : Ideal.map (algebraMap S S₁) p = P := Ideal.map_comap_of_surjective _ e.surjective P
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx' p P (by rw [hmap]; exact hP)]
  refine Ideal.ramificationIdx'_spec (by rw [hmap, pow_one]) fun h ↦ ?_
  rw [hmap] at h
  obtain ⟨g, hg, hg2⟩ := exists_uniformizer hP
  exact hg2 (h hg)

/-- Algebra maps into integral extensions are integral. -/
lemma isIntegral_of_algHom {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A]
    [Algebra R S] [Algebra.IsIntegral R S] (φ : A →ₐ[R] S) : φ.toRingHom.IsIntegral := by
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  exact fun x ↦ (Algebra.IsIntegral.isIntegral (R := R) x).tower_top

end Iso

section Main

variable {B : Type} [CommRing B] [IsDedekindDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]

local notation "K" => FractionRing B
local notation "Ω" => AlgebraicClosure (FractionRing B)

omit [Algebra.FiniteType ℂ B] in
/-- Maximal ideals of integral closures lie over nonzero primes of `B`. -/
lemma under_ne_bot (hB : ¬ IsField B) {F : IntermediateField K Ω} [FiniteDimensional K F]
    (w : Ideal (IC B F)) [w.IsMaximal] : w.under B ≠ ⊥ := by
  haveI : (w.under B).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w
  exact Ring.ne_bot_of_isMaximal_of_not_isField inferInstance hB

/-- The normalisation of `B` in `G`, as an affine orbicurve with trivial stabilisers. -/
noncomputable def normalisation (hB : ¬ IsField B) (G : IntermediateField K Ω)
    [FiniteDimensional K G] : AffOrbicurve ℂ where
  A := IC B G
  not_isField := integralClosure_not_isField B K G hB
  mult := fun _ ↦ 1
  mult_pos := fun _ _ ↦ Nat.one_pos
  finite_mult := by simp

omit [Algebra.FiniteType ℂ B] in
/-- Ramification over `A ≅ IC F'` of primes of `IC G`. -/
lemma ramificationIdx_icMap_comp (hB : ¬ IsField B) {A : Type} [CommRing A]
    {F' G : IntermediateField K Ω} [FiniteDimensional K F'] [FiniteDimensional K G]
    (h : F' ≤ G) (e : A ≃+* IC B F') (w : Ideal (IC B G)) [w.IsMaximal] :
    (letI := ((icMap (B := B) h).toRingHom.comp (e : A →+* IC B F')).toAlgebra;
      w.ramificationIdx A) = ramIC h w := by
  have := ramificationIdx_comp' (e : A →+* IC B F') (icMap (B := B) h).toRingHom
    (icMap_injective h) w
  rw [this]
  haveI := isMaximal_comap_icMap (B := B) h w
  have hne : w.comap (icMap (B := B) h) ≠ ⊥ := fun h0 ↦ by
    have := under_ne_bot hB (w.comap (icMap (B := B) h))
    rw [h0] at this
    exact this (by ext; simp [Ideal.under])
  have h1 : (letI := (e : A →+* IC B F').toAlgebra;
      (w.comap (icMap (B := B) h).toRingHom).ramificationIdx A) = 1 := by
    haveI : (w.comap (icMap (B := B) h).toRingHom).IsMaximal := this
    exact ramificationIdx_ringEquiv e _ hne
  rw [h1, one_mul]
  rfl

end Main

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through towers of integral closures is slow
/-- **U2f. Fibre products separate functions** (via Abhyankar's lemma). -/
theorem compositumSeparates : Genuine.CompositumSeparates ℂ := by
  intro Z Y q hZ c hc
  letI : Algebra Y.A Z.A := q.f.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ Y.A Z.A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (q.f.commutes x).symm
  haveI : Algebra.IsIntegral Y.A Z.A := ⟨q.isIntegral⟩
  haveI : Module.IsTorsionFree Y.A Z.A :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr q.injective
  haveI : Algebra.FiniteType Y.A Z.A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ Y.A Z.A
  set F := fieldA (B := Y.A) Z.A
  set eA := equivA (B := Y.A) Z.A
  -- `c` is not in `K`
  have hx : embA (B := Y.A) Z.A c ∉ Set.range (algebraMap (FractionRing Y.A)
      (AlgebraicClosure (FractionRing Y.A))) := by
    rintro ⟨k, hk⟩
    have hint : IsIntegral Y.A (embA (B := Y.A) Z.A c) :=
      (Algebra.IsIntegral.isIntegral (R := Y.A) c).map (embA Z.A)
    let ιK : FractionRing Y.A →ₐ[Y.A] AlgebraicClosure (FractionRing Y.A) :=
      IsScalarTower.toAlgHom _ _ _
    rw [← hk] at hint
    have hιK : Function.Injective ιK :=
      (algebraMap (FractionRing Y.A) (AlgebraicClosure (FractionRing Y.A))).injective
    have hk' : IsIntegral Y.A k := (isIntegral_algHom_iff ιK hιK).mp hint
    obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk'
    apply hc
    refine ⟨b, embA_injective (B := Y.A) Z.A ?_⟩
    rw [← hk]
    change embA Z.A (algebraMap Y.A Z.A b) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply Y.A (FractionRing Y.A)]
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne hx
  set F₂ := F.map (σ : AlgebraicClosure (FractionRing Y.A) →ₐ[FractionRing Y.A]
    AlgebraicClosure (FractionRing Y.A))
  set eσ := icEquiv (B := Y.A) F σ
  set G := F ⊔ F₂
  have hG₁ : F ≤ G := le_sup_left
  have hG₂ : F₂ ≤ G := le_sup_right
  -- ramification of `F` and `F₂` over `B`
  have hF₁ : ∀ w : Ideal (IC Y.A F), w.IsMaximal →
      w.ramificationIdx Y.A = Y.mult (w.under Y.A) := by
    intro w hw
    have hz : (w.comap eA).IsMaximal := Ideal.comap_isMaximal_of_surjective _ eA.surjective
    have h := q.etale (w.comap eA) hz
    rw [hZ _ hz, mul_one] at h
    rw [← ramificationIdx_comap_algEquiv eA w (under_ne_bot Y.not_isField w)]
    refine h.trans (congrArg Y.mult ?_)
    ext b
    change eA (algebraMap Y.A Z.A b) ∈ w ↔ _
    rw [AlgEquiv.commutes]
    rfl
  have hF₂ : ∀ w : Ideal (IC Y.A F₂), w.IsMaximal →
      w.ramificationIdx Y.A = Y.mult (w.under Y.A) := by
    intro w hw
    have hz : (w.comap eσ).IsMaximal := Ideal.comap_isMaximal_of_surjective _ eσ.surjective
    rw [← ramificationIdx_comap_algEquiv eσ w (under_ne_bot Y.not_isField w), hF₁ _ hz]
    refine congrArg Y.mult ?_
    ext b
    change eσ (algebraMap Y.A _ b) ∈ w ↔ _
    rw [AlgEquiv.commutes]
    rfl
  -- unramifiedness of `G / F` and `G / F₂`
  have hab₁ : ∀ w : Ideal (IC Y.A G), w.IsMaximal → ramIC hG₁ w = 1 := by
    intro w hw
    have hy0 := under_ne_bot Y.not_isField w
    haveI : (w.under Y.A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w
    exact abhyankar hy0 (Y.mult_pos _ inferInstance).ne'
      (fun w' hw' hw'y ↦ hw'y ▸ hF₁ w' hw') (fun w' hw' hw'y ↦ hw'y ▸ hF₂ w' hw') hG₁ hG₂ le_rfl
      w rfl
  have hab₂ : ∀ w : Ideal (IC Y.A G), w.IsMaximal → ramIC hG₂ w = 1 := by
    intro w hw
    have hy0 := under_ne_bot Y.not_isField w
    haveI : (w.under Y.A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w
    exact abhyankar hy0 (Y.mult_pos _ inferInstance).ne'
      (fun w' hw' hw'y ↦ hw'y ▸ hF₂ w' hw') (fun w' hw' hw'y ↦ hw'y ▸ hF₁ w' hw') hG₂ hG₁
      (le_of_eq (sup_comm _ _)) w rfl
  -- the normalisation `W` and the two maps `W → Z`
  let W := normalisation Y.not_isField G
  let f₁ : Z.A →ₐ[Y.A] IC Y.A G := (icMap hG₁).comp eA.toAlgHom
  let f₂ : Z.A →ₐ[Y.A] IC Y.A G := (icMap hG₂).comp (eA.trans eσ).toAlgHom
  have hmax : ∀ (f : Z.A →ₐ[Y.A] IC Y.A G) (w : Ideal (IC Y.A G)), w.IsMaximal →
      (w.comap f).IsMaximal := fun f w _ ↦ by
    letI := f.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral Z.A (IC Y.A G) := ⟨isIntegral_of_algHom f⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := Z.A) w
  let r₁ : Hom W Z :=
    { f := f₁.restrictScalars ℂ
      injective := (icMap_injective hG₁).comp eA.injective
      isIntegral := isIntegral_of_algHom f₁
      etale := fun w hw ↦ by
        let w' : Ideal (IC Y.A G) := w
        haveI : w'.IsMaximal := hw
        have h1 := ramificationIdx_icMap_comp Y.not_isField hG₁ eA.toRingEquiv w'
        rw [hab₁ w' hw] at h1
        have hz : Z.mult (w.comap f₁) = 1 := hZ _ (hmax f₁ w hw)
        exact (mul_one _).trans (h1.trans hz.symm) }
  let r₂ : Hom W Z :=
    { f := f₂.restrictScalars ℂ
      injective := (icMap_injective hG₂).comp (eA.trans eσ).injective
      isIntegral := isIntegral_of_algHom f₂
      etale := fun w hw ↦ by
        let w' : Ideal (IC Y.A G) := w
        haveI : w'.IsMaximal := hw
        have h1 := ramificationIdx_icMap_comp Y.not_isField hG₂ (eA.trans eσ).toRingEquiv w'
        rw [hab₂ w' hw] at h1
        have hz : Z.mult (w.comap f₂) = 1 := hZ _ (hmax f₂ w hw)
        exact (mul_one _).trans (h1.trans hz.symm) }
  refine ⟨W, r₁, r₂, AlgHom.ext fun b ↦ ?_, fun h ↦ hσ ?_⟩
  · change f₁ (algebraMap Y.A Z.A b) = f₂ (algebraMap Y.A Z.A b)
    rw [f₁.commutes, f₂.commutes]
  · have h' := congrArg (icVal G) h
    exact h'.symm

end OrbicurveCores.Abhyankar
