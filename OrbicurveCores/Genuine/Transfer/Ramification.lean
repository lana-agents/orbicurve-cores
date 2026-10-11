/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Transfer.LocalGen
import OrbicurveCores.Genuine.Transfer.LocalGeneric
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# T2d: ramification indices under base change

Let `f : A → B` be an injective integral map of Dedekind domains of finite type over a field `k`
of characteristic `0`, and `K / k` a field extension. For a maximal ideal `W` of `K ⊗ B`, with
`w = W ∩ B` and `V = W ∩ (K ⊗ A)`:

* if `w ≠ 0`, uniformizers `π` of `A` at `v = w ∩ A` and `ϖ` of `B` at `w` generate `V` and `W`
  locally, and `f(π) = u ϖ ^ e(w | v)` with `u` a unit at `w` (`exists_mul_eq_mul_pow`);
* if `w = 0`, a single element of `V` generates both `V` and `W` locally (generic case).

These elementwise statements pass to the components of `K ⊗ A` and `K ⊗ B`.
-/

open IsLocalRing TensorProduct Polynomial

namespace OrbicurveCores.Transfer

section Dedekind

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain B]

/-- In a Dedekind extension, the image of a local uniformizer `π` of `A` at `v = w ∩ A` is a
unit times `ϖ ^ e(w | v)`, `ϖ` a local uniformizer of `B` at `w`, elementwise. -/
lemma exists_mul_eq_mul_pow (f : A →+* B) (hf : Function.Injective f) (w : Ideal B) [w.IsPrime]
    (hw : w ≠ ⊥) {π : A} (hπ0 : π ≠ 0) (hπ : π ∈ w.comap f)
    (hπloc : ∀ a ∈ w.comap f, ∃ s ∉ w.comap f, ∃ y, s * a = π * y) {ϖ : B} (hϖ : ϖ ∈ w)
    (hϖloc : ∀ x ∈ w, ∃ s ∉ w, ∃ y, s * x = ϖ * y) :
    ∃ s ∉ w, ∃ b ∉ w, s * f π = b * ϖ ^ (letI := f.toAlgebra; w.ramificationIdx A) := by
  letI := f.toAlgebra
  set S := Localization.AtPrime w
  have : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hw S
  have hmax : maximalIdeal S = Ideal.span {algebraMap B S ϖ} :=
    maximalIdeal_eq_span_of_forall w hϖ hϖloc
  have hv : (w.under A).map (algebraMap A S) = Ideal.span {algebraMap B S (f π)} := by
    have := map_eq_span_of_forall_isUnit (algebraMap A S) (I := w.under A) hπ fun a ha ↦ by
      obtain ⟨s, hs, y, hsy⟩ := hπloc a ha
      refine ⟨s, ?_, y, hsy⟩
      rw [IsScalarTower.algebraMap_apply A B S]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff S w _).mpr hs
    rw [this, IsScalarTower.algebraMap_apply A B S]
    rfl
  have hne : algebraMap B S (f π) ≠ 0 := by
    rw [Ne, IsLocalization.to_map_eq_zero_iff S w.primeCompl_le_nonZeroDivisors]
    exact fun h ↦ hπ0 (hf (h.trans (map_zero f).symm))
  obtain ⟨n, u, hu⟩ := exists_unit_mul_pow_of_maximalIdeal_eq hmax hne
  have hspan : Ideal.span {algebraMap B S (f π)} = Ideal.span {algebraMap B S ϖ ^ n} := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit]
  have he : w.ramificationIdx A = n :=
    ramificationIdx_eq_of_map_eq_span_pow w hmax n (hv.trans hspan)
  rw [he]
  obtain ⟨⟨b, ⟨s, hs⟩⟩, hbs⟩ := IsLocalization.mk'_surjective w.primeCompl (u : S)
  dsimp only at hbs
  have hb : b ∉ w := by
    intro hb
    have : (u : S) ∈ maximalIdeal S := by
      rw [← hbs, IsLocalization.AtPrime.mk'_mem_maximal_iff S w]; exact hb
    exact (maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ this u.isUnit)
  have hsp := IsLocalization.mk'_spec' S b (⟨s, hs⟩ : w.primeCompl)
  have heq : algebraMap B S (s * f π) = algebraMap B S (b * ϖ ^ n) := by
    rw [map_mul, map_mul, hu, map_pow, ← hbs]
    linear_combination (algebraMap B S ϖ ^ n) * hsp
  obtain ⟨⟨t, ht⟩, htx⟩ := (IsLocalization.eq_iff_exists w.primeCompl S).mp heq
  dsimp only at htx
  refine ⟨t * s, fun h ↦ (‹w.IsPrime›.mem_or_mem h).elim ht hs, t * b,
    fun h ↦ (‹w.IsPrime›.mem_or_mem h).elim ht hb, ?_⟩
  calc t * s * f π = t * (s * f π) := by ring
    _ = t * (b * ϖ ^ n) := htx
    _ = t * b * ϖ ^ n := by ring

end Dedekind

section Tensor

variable {k K A B : Type*} [Field k] [Field K] [Algebra k K] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

variable (K) in
/-- The base change `K ⊗ A → K ⊗ B` of `f : A → B`. -/
noncomputable abbrev bcMap (f : A →ₐ[k] B) : K ⊗[k] A →ₐ[K] K ⊗[k] B :=
  Algebra.TensorProduct.map (AlgHom.id K K) f

@[simp] lemma bcMap_tmul (f : A →ₐ[k] B) (c : K) (a : A) :
    bcMap K f (c ⊗ₜ a) = c ⊗ₜ f a := rfl

lemma bcMap_comp_includeRight (f : A →ₐ[k] B) :
    (bcMap K f).toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).toRingHom.comp f.toRingHom := by
  ext a; simp

lemma bcMap_injective (f : A →ₐ[k] B) (hf : Function.Injective f) :
    Function.Injective (bcMap K f) := by
  have : ⇑(bcMap K f) = LinearMap.lTensor K f.toLinearMap := by
    ext x; induction x with
    | zero => simp
    | tmul c a => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hf

lemma bcMap_finite (f : A →ₐ[k] B) (hfin : f.toRingHom.Finite) :
    (bcMap K f).toRingHom.Finite := by
  classical
  letI := f.toRingHom.toAlgebra
  letI := (bcMap K f).toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
  refine ⟨⟨S.image fun b ↦ (1 : K) ⊗ₜ[k] b, ?_⟩⟩
  rw [eq_top_iff]
  intro x hx
  clear hx
  set N := Submodule.span (K ⊗[k] A) (↑(S.image fun b ↦ (1 : K) ⊗ₜ[k] b) : Set (K ⊗[k] B))
  have key : ∀ b : B, ∀ c : K, c ⊗ₜ[k] b ∈ N := by
    intro b
    have hb : b ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      intro c
      have : c ⊗ₜ[k] b = (c ⊗ₜ[k] (1 : A)) • ((1 : K) ⊗ₜ[k] b) := by
        rw [Algebra.smul_def]
        change c ⊗ₜ[k] b = (c ⊗ₜ[k] f 1) * _
        rw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact N.smul_mem _ (Submodule.subset_span (Finset.mem_image_of_mem _ hb))
    | zero => intro c; rw [tmul_zero]; exact N.zero_mem
    | add x y _ _ hx hy => intro c; rw [tmul_add]; exact N.add_mem (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      have : c ⊗ₜ[k] (a • x) = ((1 : K) ⊗ₜ[k] a) • (c ⊗ₜ[k] x) := by
        rw [Algebra.smul_def, Algebra.smul_def]
        change c ⊗ₜ[k] (f a * x) = ((1 : K) ⊗ₜ[k] f a) * _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this]
      exact N.smul_mem _ (hx c)
  induction x with
  | zero => exact N.zero_mem
  | tmul c b => exact key b c
  | add x y hx hy => exact N.add_mem hx hy

section Data

variable (f : A →ₐ[k] B) (hf : Function.Injective f) (hfin : f.toRingHom.Finite)

local notation "ιA" => (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
local notation "ιB" => (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B)

include hfin in
lemma isMaximal_comap_bcMap (W : Ideal (K ⊗[k] B)) [W.IsMaximal] :
    (W.comap (bcMap K f)).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (bcMap K f).toRingHom
    (bcMap_finite f hfin).to_isIntegral W

lemma comap_comap_bcMap (W : Ideal (K ⊗[k] B)) :
    (W.comap (bcMap K f)).comap ιA = (W.comap ιB).comap f := by
  ext a
  simp [Ideal.mem_comap]

include hf hfin in
/-- **Closed points** (T2d): local uniformizers `π` of `A` and `ϖ` of `B` generate
`V = W ∩ (K ⊗ A)` and `W` locally, and `f(π) = u ϖ ^ e(w | v)` with `u` a unit at `W`. -/
theorem closed_data [CharZero k] [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] (W : Ideal (K ⊗[k] B)) [W.IsMaximal]
    (hw : W.comap ιB ≠ ⊥) :
    ∃ (π : A) (ϖ : B), (1 : K) ⊗ₜ[k] π ∈ W.comap (bcMap K f) ∧
      (∀ x ∈ W.comap (bcMap K f), ∃ s ∉ W.comap (bcMap K f), ∃ y,
        s * x = ((1 : K) ⊗ₜ[k] π) * y) ∧
      (1 : K) ⊗ₜ[k] ϖ ∈ W ∧ (∀ x ∈ W, ∃ s ∉ W, ∃ y, s * x = ((1 : K) ⊗ₜ[k] ϖ) * y) ∧
      ∃ s ∉ W, ∃ b ∉ W, s * ((1 : K) ⊗ₜ[k] f π) =
        b * ((1 : K) ⊗ₜ[k] ϖ) ^
          (letI := f.toRingHom.toAlgebra; (W.comap ιB).ramificationIdx A) := by
  set w := W.comap ιB with hwdef
  set V := W.comap (bcMap K f) with hVdef
  have hV : V.IsMaximal := isMaximal_comap_bcMap f hfin W
  have hvw : V.comap ιA = w.comap f := comap_comap_bcMap f W
  have hv : V.comap ιA ≠ ⊥ := by
    rw [hvw]
    intro h
    letI := f.toRingHom.toAlgebra
    have : Algebra.IsIntegral A B := ⟨hfin.to_isIntegral⟩
    exact hw (Ideal.eq_bot_of_comap_eq_bot h)
  have : (V.comap ιA).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨π, hπ0, hπv, hπ⟩ := exists_local_uniformizer _ hv
  obtain ⟨ϖ, -, hϖw, hϖ⟩ := exists_local_uniformizer w hw
  have hVmax := maximalIdeal_eq_span_closed_of V hv hπv hπ
  have hWmax := maximalIdeal_eq_span_closed_of W hw hϖw hϖ
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hVmax hWmax
  have hrel := exists_mul_eq_mul_pow f.toRingHom hf w hw hπ0 (hvw ▸ hπv)
    (fun a ha ↦ hπ a (hvw ▸ ha)) hϖw hϖ
  obtain ⟨s, hs, b, hb, hsb⟩ := hrel
  refine ⟨π, ϖ, hπv, forall_of_map_eq_span V hVmax, hϖw, forall_of_map_eq_span W hWmax,
    ιB s, hs, ιB b, hb, ?_⟩
  have := congrArg ιB hsb
  simp only [map_mul, map_pow] at this
  exact this

attribute [local instance] algPolyTensor algPolyTensor' Polynomial.algebra in
include hf hfin in
/-- **Generic points** (T2d): if `W ∩ B = 0`, a single element `h` of `V = W ∩ (K ⊗ A)` generates
`V` and `W` locally (an equation of `V ∩ K[t]` for a Noether normalization `k[t] ⊆ A`). -/
theorem generic_data [CharZero k] [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra.FiniteType k A] (hA : ¬ IsField A) (W : Ideal (K ⊗[k] B)) [W.IsMaximal]
    (hw : W.comap ιB = ⊥) :
    ∃ h : K ⊗[k] A, h ∈ W.comap (bcMap K f) ∧
      (∀ x ∈ W.comap (bcMap K f), ∃ s ∉ W.comap (bcMap K f), ∃ y, s * x = h * y) ∧
      (∀ x ∈ W, ∃ s ∉ W, ∃ y, s * x = bcMap K f h * y) := by
  obtain ⟨t, ht, htfin⟩ := exists_finite_polynomial k A hA
  set V := W.comap (bcMap K f) with hVdef
  have hV : V.IsMaximal := isMaximal_comap_bcMap f hfin W
  have hVA : V.comap ιA = ⊥ := by
    rw [comap_comap_bcMap f W, hw]
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h ↦ hf (h.trans (map_zero f).symm), fun h ↦ by rw [h, map_zero]⟩
  letI instA : Algebra k[X] A := t.toRingHom.toAlgebra
  haveI : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = t (Polynomial.C c)
    rw [← Polynomial.algebraMap_eq, AlgHom.commutes]
  haveI : Module.Finite k[X] A := htfin
  haveI : FaithfulSMul k[X] A := (faithfulSMul_iff_algebraMap_injective _ _).mpr ht
  letI instB : Algebra k[X] B := (f.comp t).toRingHom.toAlgebra
  haveI : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change _ = f (t (Polynomial.C c))
    rw [← Polynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
  haveI : Module.Finite k[X] B := RingHom.Finite.comp hfin htfin
  haveI : FaithfulSMul k[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr (hf.comp ht)
  have hmaxA := map_comap_eq_maximalIdeal_generic (K := K) V hVA
  have hmaxB := map_comap_eq_maximalIdeal_generic (K := K) W hw
  have hcomp : algebraMap K[X] (K ⊗[k] B) =
      (bcMap K f).toRingHom.comp (algebraMap K[X] (K ⊗[k] A)) := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change Polynomial.aeval _ (Polynomial.C c) = bcMap K f (Polynomial.aeval _ (Polynomial.C c))
      rw [Polynomial.aeval_C, Polynomial.aeval_C, AlgHom.commutes]
    · change Polynomial.aeval _ Polynomial.X = bcMap K f (Polynomial.aeval _ Polynomial.X)
      rw [Polynomial.aeval_X, Polynomial.aeval_X, bcMap_tmul]
      rfl
  have h𝔫 : W.comap (algebraMap K[X] (K ⊗[k] B)) = V.comap (algebraMap K[X] (K ⊗[k] A)) := by
    rw [hcomp, ← Ideal.comap_comap]
    rfl
  set 𝔫 := V.comap (algebraMap K[X] (K ⊗[k] A))
  set g := Submodule.IsPrincipal.generator 𝔫
  have hspan : Ideal.span {g} = 𝔫 := Ideal.span_singleton_generator 𝔫
  refine ⟨algebraMap K[X] (K ⊗[k] A) g, ?_, ?_, ?_⟩
  · have : g ∈ 𝔫 := hspan ▸ Ideal.mem_span_singleton_self g
    exact this
  · rw [← hspan, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply K[X] (K ⊗[k] A) (Localization.AtPrime V),
      ← Localization.AtPrime.map_eq_maximalIdeal] at hmaxA
    exact forall_of_map_eq_span V hmaxA.symm
  · rw [h𝔫, ← hspan, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply K[X] (K ⊗[k] B) (Localization.AtPrime W),
      ← Localization.AtPrime.map_eq_maximalIdeal, hcomp] at hmaxB
    exact forall_of_map_eq_span W hmaxB.symm

end Data

end Tensor

end OrbicurveCores.Transfer
