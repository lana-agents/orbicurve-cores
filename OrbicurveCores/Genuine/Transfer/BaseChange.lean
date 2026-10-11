/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Orbicurve.Core
import OrbicurveCores.Genuine.Transfer.CompRamification
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# T2e: base change of affine orbicurves

Let `k` be a field of characteristic `0` and `K / k` a field extension. For an affine orbicurve
`Y` over `k` and a minimal prime `𝔭` of `K ⊗_k A_Y`, the component `(K ⊗_k A_Y)/𝔭` is a Dedekind
domain of finite type over `K` (T2c–T2d); with the multiplicity of a maximal ideal `w̃` pulled
back from `w̃ ∩ A_Y` (and `1` if `w̃ ∩ A_Y = 0`) it is an affine orbicurve `bcComp Y 𝔭` over `K`.
A finite étale `q : Z → Y` induces finite étale morphisms of components `bcHom q 𝔓`
(ramification indices: `comp_ramificationIdx`).
-/

open TensorProduct AffOrbicurve

universe u v

namespace OrbicurveCores.Transfer

variable {k : Type u} [Field k] [CharZero k] {K : Type (max u v)} [Field K] [Algebra k K]

/-- In a Dedekind domain, only finitely many maximal ideals contain a nonzero ideal. -/
lemma finite_setOf_isMaximal_le {C : Type*} [CommRing C] [IsDedekindDomain C] {I : Ideal C}
    (hI : I ≠ ⊥) : {w : Ideal C | w.IsMaximal ∧ I ≤ w}.Finite := by
  refine (I.finite_minimalPrimes_of_isNoetherianRing).subset fun w ⟨hw, hIw⟩ ↦
    ⟨⟨hw.isPrime, hIw⟩, fun q ⟨hq, hIq⟩ hqw ↦ ?_⟩
  have hq0 : q ≠ ⊥ := fun h ↦ hI (le_bot_iff.mp (h ▸ hIq))
  exact (hq.isMaximal hq0).eq_of_le hw.ne_top hqw ▸ le_rfl

variable (K)

/-- The multiplicity on a component of a base change, pulled back from `Y`. -/
noncomputable def compMult (Y : AffOrbicurve k) (𝔭 : Ideal (K ⊗[k] Y.A))
    (w : Ideal ((K ⊗[k] Y.A) ⧸ 𝔭)) : ℕ :=
  open Classical in
  if (w.comap (Ideal.Quotient.mk 𝔭)).comap
      (Algebra.TensorProduct.includeRight : Y.A →ₐ[k] K ⊗[k] Y.A) = ⊥ then 1
  else Y.mult ((w.comap (Ideal.Quotient.mk 𝔭)).comap
      (Algebra.TensorProduct.includeRight : Y.A →ₐ[k] K ⊗[k] Y.A))

/-- **Base change of an affine orbicurve** (a component): `(K ⊗_k A_Y)/𝔭` for a minimal prime
`𝔭`, with multiplicities pulled back from `Y`. -/
noncomputable def bcComp (Y : AffOrbicurve k) (𝔭 : Ideal (K ⊗[k] Y.A))
    (h𝔭 : 𝔭 ∈ minimalPrimes (K ⊗[k] Y.A)) : AffOrbicurve K where
  A := (K ⊗[k] Y.A) ⧸ 𝔭
  isDomain := by haveI := h𝔭.1.1; infer_instance
  isDedekindDomain := by
    have : IsNoetherianRing (K ⊗[k] Y.A) := Algebra.FiniteType.isNoetherianRing K _
    exact (locallyDVR_tensor Y.not_isField).isDedekindDomain_quotient h𝔭
  not_isField := (locallyDVR_tensor Y.not_isField).not_isField_quotient h𝔭
  mult := compMult K Y 𝔭
  mult_pos w hw := by
    unfold compMult
    split_ifs with h
    · exact one_pos
    · haveI : ((w.comap (Ideal.Quotient.mk 𝔭)).comap
          (Algebra.TensorProduct.includeRight : Y.A →ₐ[k] K ⊗[k] Y.A)).IsPrime :=
        Ideal.comap_isPrime _ _
      exact Y.mult_pos _ (Ideal.IsPrime.isMaximal inferInstance h)
  finite_mult := by
    haveI : 𝔭.IsPrime := h𝔭.1.1
    have : IsNoetherianRing (K ⊗[k] Y.A) := Algebra.FiniteType.isNoetherianRing K _
    haveI := (locallyDVR_tensor (K := K) Y.not_isField).isDedekindDomain_quotient h𝔭
    set ι : Y.A →ₐ[k] K ⊗[k] Y.A := Algebra.TensorProduct.includeRight
    let φ : Y.A →+* (K ⊗[k] Y.A) ⧸ 𝔭 := (Ideal.Quotient.mk 𝔭).comp ι.toRingHom
    refine (Y.finite_mult.biUnion fun v hv ↦ finite_setOf_isMaximal_le (I := v.map φ) ?_).subset ?_
    · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (Ring.ne_bot_of_isMaximal_of_not_isField hv.1 Y.not_isField)
      intro h
      have hφa : φ a = 0 := by
        have : φ a ∈ v.map φ := Ideal.mem_map_of_mem φ ha
        rwa [h, Ideal.mem_bot] at this
      have h1 : (1 : K) ⊗ₜ[k] a ∈ 𝔭 := Ideal.Quotient.eq_zero_iff_mem.mp hφa
      exact (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔭).ne_of_mem h1
        (one_tmul_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)) rfl
    · rintro w ⟨hw, hw1⟩
      simp only [compMult] at hw1
      split_ifs at hw1 with h
      · exact absurd rfl hw1
      · have : (w.comap φ).IsPrime := Ideal.comap_isPrime _ _
        refine Set.mem_biUnion (x := w.comap φ) ⟨Ideal.IsPrime.isMaximal inferInstance h, hw1⟩
          ⟨hw, Ideal.map_le_iff_le_comap.mpr le_rfl⟩

variable {K}

omit [CharZero k] in
/-- The map of coordinate rings of a finite étale morphism is finite. -/
lemma hom_finite {Z Y : AffOrbicurve k} (q : Hom Z Y) : q.f.toRingHom.Finite := by
  letI := q.f.toRingHom.toAlgebra
  haveI : IsScalarTower k Y.A Z.A := IsScalarTower.of_algebraMap_eq fun c ↦ (q.f.commutes c).symm
  haveI : Algebra.FiniteType Y.A Z.A := Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  haveI : Algebra.IsIntegral Y.A Z.A := ⟨q.isIntegral⟩
  exact Algebra.IsIntegral.finite

lemma comap_bcHom_mem {Z Y : AffOrbicurve k} (q : Hom Z Y) {𝔓 : Ideal (K ⊗[k] Z.A)}
    (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] Z.A)) :
    𝔓.comap (bcMap K q.f) ∈ minimalPrimes (K ⊗[k] Y.A) :=
  comap_bcMap_mem_minimalPrimes q.f (hom_finite q) Y.not_isField Z.not_isField h𝔓

/-- The étale condition for base changes of finite étale morphisms on components. -/
lemma bcHom_etale {Z Y : AffOrbicurve k} (q : Hom Z Y) {𝔓 : Ideal (K ⊗[k] Z.A)}
    (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] Z.A)) (w : Ideal ((K ⊗[k] Z.A) ⧸ 𝔓)) [w.IsMaximal] :
    (letI := (compMap K q.f 𝔓).toRingHom.toAlgebra;
      w.ramificationIdx ((K ⊗[k] Y.A) ⧸ 𝔓.comap (bcMap K q.f))) * compMult K Z 𝔓 w =
      compMult K Y (𝔓.comap (bcMap K q.f)) (w.comap (compMap K q.f 𝔓)) := by
  rw [comp_ramificationIdx (K := K) q.f q.injective (hom_finite q) Y.not_isField
      Z.not_isField h𝔓 w]
  set wZ := (w.comap (Ideal.Quotient.mk 𝔓)).comap
    (Algebra.TensorProduct.includeRight : Z.A →ₐ[k] K ⊗[k] Z.A) with hwZ
  have hcc : ((w.comap (compMap K q.f 𝔓)).comap (Ideal.Quotient.mk _)).comap
      (Algebra.TensorProduct.includeRight : Y.A →ₐ[k] K ⊗[k] Y.A) = wZ.comap q.f := by
    ext a
    exact Iff.rfl
  have hP : wZ.IsPrime := Ideal.comap_isPrime _ _
  simp only [compMult, hcc, ← hwZ]
  by_cases h1 : wZ = ⊥
  · have h2 : wZ.comap q.f = ⊥ := by
      rw [h1]; ext a; simp [map_eq_zero_iff _ q.injective]
    rw [if_pos h1, if_pos h1, if_pos h2]
  · have h2 : wZ.comap q.f ≠ ⊥ := by
      letI := q.f.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral Y.A Z.A := ⟨q.isIntegral⟩
      exact fun h ↦ h1 (Ideal.eq_bot_of_comap_eq_bot h)
    rw [if_neg h1, if_neg h1, if_neg h2]
    exact q.etale _ (Ideal.IsPrime.isMaximal inferInstance h1)

/-- **Base change of a finite étale morphism**, on components. -/
noncomputable def bcHom {Z Y : AffOrbicurve k} (q : Hom Z Y) (𝔓 : Ideal (K ⊗[k] Z.A))
    (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] Z.A)) :
    Hom (bcComp K Z 𝔓 h𝔓) (bcComp K Y (𝔓.comap (bcMap K q.f)) (comap_bcHom_mem q h𝔓)) where
  f := compMap K q.f 𝔓
  injective := compMap_injective q.f 𝔓
  isIntegral := (compMap_finite q.f (hom_finite q) 𝔓).to_isIntegral
  etale w hw := by
    have := @bcHom_etale _ _ _ K _ _ Z Y q 𝔓 h𝔓 w hw
    exact this

@[simp] lemma bcHom_f {Z Y : AffOrbicurve k} (q : Hom Z Y) (𝔓 : Ideal (K ⊗[k] Z.A))
    (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] Z.A)) : (bcHom q 𝔓 h𝔓).f = compMap K q.f 𝔓 := rfl

/-- Base change of a finite étale morphism into a prescribed component `𝔮` of the target (equal
to the contraction of `𝔓`). -/
noncomputable def bcHom' {Z Y : AffOrbicurve k} (q : Hom Z Y) (𝔓 : Ideal (K ⊗[k] Z.A))
    (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] Z.A)) (𝔮 : Ideal (K ⊗[k] Y.A))
    (h𝔮 : 𝔮 ∈ minimalPrimes (K ⊗[k] Y.A)) (heq : 𝔓.comap (bcMap K q.f) = 𝔮) :
    Hom (bcComp K Z 𝔓 h𝔓) (bcComp K Y 𝔮 h𝔮) := by
  subst heq
  exact bcHom q 𝔓 h𝔓

lemma bcHom'_f_mk {Z Y : AffOrbicurve k} (q : Hom Z Y) (𝔓 : Ideal (K ⊗[k] Z.A))
    (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k] Z.A)) (𝔮 : Ideal (K ⊗[k] Y.A))
    (h𝔮 : 𝔮 ∈ minimalPrimes (K ⊗[k] Y.A)) (heq : 𝔓.comap (bcMap K q.f) = 𝔮)
    (y : K ⊗[k] Y.A) :
    (bcHom' q 𝔓 h𝔓 𝔮 h𝔮 heq).f (Ideal.Quotient.mk 𝔮 y) =
      Ideal.Quotient.mk 𝔓 (bcMap K q.f y) := by
  subst heq
  rfl

end OrbicurveCores.Transfer
