/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.EllipticHom
import OrbicurveCores.Genuine.HemiCore

/-!
# T3a: rigidity and descent come down from a field extension

Let `E₀` be an elliptic curve over `k₀` (characteristic `0`) and `K / k₀` a field extension such
that `(E_K ∖ 0)/±1` is the `K`-core of `E_K ∖ 0`. Then `HemiRigid E₀` and `HemiDescends E₀`
hold over `k₀`, hence `(E₀ ∖ 0)/±1` is the `k₀`-core of `E₀ ∖ 0`.

Proof: for finite étale `p : Z → E₀ ∖ 0`, every component `C` of `K ⊗ A_Z` is finite étale over
`E_K ∖ 0` (`bcHom`, `iotaX`), so it lies in `\overline{Loc}_K(E_K ∖ 0)`, and the two morphisms
`C → (E_K ∖ 0)/±1` built from `φ` and from `x ∘ p` agree. Evaluating at `x` shows that
`1 ⊗ (φ(x) - p(x))` lies in every minimal prime of the reduced ring `K ⊗ A_Z`, hence vanishes.
-/

open TensorProduct AffOrbicurve Polynomial

universe u v

namespace OrbicurveCores.Transfer

variable {k₀ : Type u} [Field k₀] [CharZero k₀] (E₀ : WeierstrassCurve k₀) [E₀.IsElliptic]
  {K : Type (max u v)} [Field K] [CharZero K] [Algebra k₀ K]

/-- The value of the comparison isomorphism at the coordinate `x`. -/
lemma iotaX_f_x (𝔭 : Ideal (K ⊗[k₀] (punctured E₀).A))
    (h𝔭 : 𝔭 ∈ minimalPrimes (K ⊗[k₀] (punctured E₀).A)) :
    (iotaX E₀ 𝔭 h𝔭).f (Genuine.hemiMap (E₀.baseChange K) X) =
      Ideal.Quotient.mk 𝔭 ((1 : K) ⊗ₜ[k₀] Genuine.hemiMap E₀ X) := by
  change alphaXR E₀ 𝔭 h𝔭 (algebraMap K[X] (puncturedRing (E₀.baseChange K)) X) = _
  rw [alphaXR, alphaX_algebraMap, psiPoly, Polynomial.aeval_X]
  rfl

lemma iotaH_f_x (𝔮 : Ideal (K ⊗[k₀] (hemi E₀).A)) (h𝔮 : 𝔮 ∈ minimalPrimes (K ⊗[k₀] (hemi E₀).A)) :
    (iotaH E₀ 𝔮 h𝔮).f X = Ideal.Quotient.mk 𝔮 ((1 : K) ⊗ₜ[k₀] (X : k₀[X])) :=
  alphaH_X E₀ 𝔮 h𝔮

section General

/-- In a reduced ring, elements agreeing modulo every minimal prime are equal. -/
lemma eq_of_forall_minimalPrimes {T : Type*} [CommRing T] [IsReduced T] {x y : T}
    (h : ∀ 𝔓 ∈ minimalPrimes T, Ideal.Quotient.mk 𝔓 x = Ideal.Quotient.mk 𝔓 y) : x = y := by
  rw [← sub_eq_zero]
  have hmem : x - y ∈ sInf (minimalPrimes T) := by
    rw [Submodule.mem_sInf]
    intro 𝔓 h𝔓
    exact Ideal.Quotient.eq.mp (h 𝔓 h𝔓)
  have h0 : sInf (minimalPrimes T) = ⊥ := by
    rw [minimalPrimes, Ideal.sInf_minimalPrimes]
    exact nilradical_eq_zero T
  rw [h0] at hmem
  exact hmem

/-- Descent of membership in the image along a field extension. -/
lemma mem_range_of_one_tmul_mem_range {k₀ K M N : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    [AddCommGroup M] [Module k₀ M] [AddCommGroup N] [Module k₀ N] (f : M →ₗ[k₀] N) {n : N}
    (h : (1 : K) ⊗ₜ[k₀] n ∈ LinearMap.range (LinearMap.lTensor K f)) : n ∈ LinearMap.range f := by
  set π := (LinearMap.range f).mkQ
  have hex := lTensor_exact K (LinearMap.exact_subtype_mkQ (LinearMap.range f))
    (Submodule.mkQ_surjective _)
  have h1 : LinearMap.lTensor K π ((1 : K) ⊗ₜ[k₀] n) = 0 := by
    obtain ⟨t, ht⟩ := h
    rw [← ht]
    have : LinearMap.range (LinearMap.lTensor K f) ≤
        LinearMap.ker (LinearMap.lTensor K π) := by
      rw [hex.linearMap_ker_eq]
      rintro _ ⟨t, rfl⟩
      induction t with
      | zero => exact ⟨0, by simp⟩
      | tmul c m => exact ⟨c ⊗ₜ ⟨f m, m, rfl⟩, by simp⟩
      | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    exact this ⟨t, rfl⟩
  rw [LinearMap.lTensor_tmul] at h1
  have hinj : Function.Injective (LinearMap.rTensor (N ⧸ LinearMap.range f)
      (Algebra.linearMap k₀ K)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap k₀ K).injective
  have h2 : LinearMap.rTensor (N ⧸ LinearMap.range f) (Algebra.linearMap k₀ K)
      ((1 : k₀) ⊗ₜ[k₀] π n) = 0 := by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact h1
  rw [← map_zero (LinearMap.rTensor (N ⧸ LinearMap.range f) (Algebra.linearMap k₀ K))] at h2
  have h3 := hinj h2
  have h4 : π n = 0 := by
    have := congrArg (TensorProduct.lid k₀ (N ⧸ LinearMap.range f)) h3
    simpa using this
  exact (Submodule.Quotient.mk_eq_zero _).mp h4

end General

variable {E₀}

/-- **Component computation**: if `(E_K ∖ 0)/±1` is the `K`-core of `E_K ∖ 0`, then for finite
étale `p : Z → E₀ ∖ 0`, `φ : Z → (E₀ ∖ 0)/±1` and every component `𝔓` of `K ⊗ A_Z`,
`1 ⊗ φ(x) ≡ 1 ⊗ p(x) mod 𝔓`. -/
lemma mk_phi_eq_mk_p (hcore : IsCoreOf (punctured (E₀.baseChange K)) (hemi (E₀.baseChange K)))
    {Z : AffOrbicurve k₀} (p : Hom Z (punctured E₀)) (φ : Hom Z (hemi E₀))
    (𝔓 : Ideal (K ⊗[k₀] Z.A)) (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k₀] Z.A)) :
    Ideal.Quotient.mk 𝔓 ((1 : K) ⊗ₜ[k₀] φ.f X) =
      Ideal.Quotient.mk 𝔓 ((1 : K) ⊗ₜ[k₀] p.f (Genuine.hemiMap E₀ X)) := by
  have h𝔭 := comap_bcHom_mem p h𝔓
  have h𝔮 := comap_bcHom_mem φ h𝔓
  let pC : Hom (bcComp K Z 𝔓 h𝔓) (punctured (E₀.baseChange K)) :=
    (bcHom p 𝔓 h𝔓).comp (iotaX E₀ _ h𝔭)
  let φC : Hom (bcComp K Z 𝔓 h𝔓) (hemi (E₀.baseChange K)) :=
    (bcHom φ 𝔓 h𝔓).comp (iotaH E₀ _ h𝔮)
  let ψC : Hom (bcComp K Z 𝔓 h𝔓) (hemi (E₀.baseChange K)) :=
    pC.comp (Genuine.hemiHom (E₀.baseChange K))
  have hLoc : LocBar (punctured (E₀.baseChange K)) (bcComp K Z 𝔓 h𝔓) :=
    ⟨_, ⟨pC⟩, ⟨Genuine.homId _⟩⟩
  haveI := (hcore.2 _ hLoc).2
  have h := congrArg (fun φ ↦ φ.f X) (Subsingleton.elim φC ψC)
  simp only [φC, ψC, pC, Hom.comp_f, AlgHom.comp_apply, Genuine.hemiHom_f] at h
  rw [iotaH_f_x, iotaX_f_x] at h
  change compMap K φ.f 𝔓 _ = compMap K p.f 𝔓 _ at h
  rw [compMap_mk, compMap_mk, bcMap_tmul, bcMap_tmul] at h
  exact h

omit [CharZero K] [CharZero k₀] in
lemma includeRight_injective (A : Type*) [CommRing A] [Algebra k₀ A] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[k₀] K ⊗[k₀] A) := by
  have : ⇑(Algebra.TensorProduct.includeRight : A →ₐ[k₀] K ⊗[k₀] A) =
      (LinearMap.rTensor A (Algebra.linearMap k₀ K)) ∘ (TensorProduct.lid k₀ A).symm := by
    ext a; simp
  rw [this]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap k₀ K).injective).comp (TensorProduct.lid k₀ A).symm.injective

/-- **Rigidity descends** from `K` to `k₀`. -/
theorem hemiRigid_of_isCoreOf_baseChange
    (hcore : IsCoreOf (punctured (E₀.baseChange K)) (hemi (E₀.baseChange K))) :
    Genuine.HemiRigid E₀ := by
  intro Z p φ
  have : IsReduced (K ⊗[k₀] Z.A) := (locallyDVR_tensor Z.not_isField).isReduced
  apply includeRight_injective (k₀ := k₀) (K := K) Z.A
  exact eq_of_forall_minimalPrimes fun 𝔓 h𝔓 ↦ mk_phi_eq_mk_p hcore p φ 𝔓 h𝔓

omit [CharZero K] [CharZero k₀] in
/-- Every component of `K ⊗ A_Y` lies under a component of `K ⊗ A_Z`, for finite étale `Z → Y`. -/
lemma exists_minimalPrimes_comap_eq {Z Y : AffOrbicurve k₀} (q : Hom Z Y)
    {𝔇 : Ideal (K ⊗[k₀] Y.A)} (h𝔇 : 𝔇 ∈ minimalPrimes (K ⊗[k₀] Y.A)) :
    ∃ 𝔓 ∈ minimalPrimes (K ⊗[k₀] Z.A), 𝔓.comap (bcMap K q.f) = 𝔇 := by
  letI := (bcMap K q.f).toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (K ⊗[k₀] Y.A) (K ⊗[k₀] Z.A) :=
    ⟨(bcMap_finite q.f (hom_finite q)).to_isIntegral⟩
  have : 𝔇.IsPrime := h𝔇.1.1
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := K ⊗[k₀] Z.A) 𝔇 ⊥
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [bcMap_injective q.f q.injective (hx.trans (map_zero _).symm)]
      exact 𝔇.zero_mem)
  obtain ⟨𝔓, h𝔓, h𝔓Q⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ Q)
  refine ⟨𝔓, h𝔓, le_antisymm ?_ ?_⟩
  · exact (Ideal.comap_mono h𝔓Q).trans hQc.le
  · haveI : 𝔓.IsPrime := h𝔓.1.1
    have : (𝔓.comap (bcMap K q.f)).IsPrime := Ideal.comap_isPrime _ _
    exact h𝔇.2 ⟨this, bot_le⟩ ((Ideal.comap_mono h𝔓Q).trans hQc.le)

/-- **Component computation for descent**: with the core over `K`, for finite étale
`p : Z → E₀ ∖ 0`, `q : Z → Y`, a component `𝔇` of `K ⊗ A_Y` and a lift `y` of `ψ(x)`, `ψ` the
morphism from the component to `(E_K ∖ 0)/±1`, `q(y) ≡ 1 ⊗ p(x)` modulo every component of
`K ⊗ A_Z` over `𝔇`. -/
lemma exists_lift_descent
    (hcore : IsCoreOf (punctured (E₀.baseChange K)) (hemi (E₀.baseChange K)))
    {Z Y : AffOrbicurve k₀} (p : Hom Z (punctured E₀)) (q : Hom Z Y)
    {𝔇 : Ideal (K ⊗[k₀] Y.A)} (h𝔇 : 𝔇 ∈ minimalPrimes (K ⊗[k₀] Y.A)) :
    ∃ y : K ⊗[k₀] Y.A, ∀ 𝔓 ∈ minimalPrimes (K ⊗[k₀] Z.A),
      𝔓.comap (bcMap K q.f) = 𝔇 →
      Ideal.Quotient.mk 𝔓 (bcMap K q.f y) =
        Ideal.Quotient.mk 𝔓 ((1 : K) ⊗ₜ[k₀] p.f (Genuine.hemiMap E₀ X)) := by
  have pC : ∀ 𝔓 (h𝔓 : 𝔓 ∈ minimalPrimes (K ⊗[k₀] Z.A)),
      Hom (bcComp K Z 𝔓 h𝔓) (punctured (E₀.baseChange K)) := fun 𝔓 h𝔓 ↦
    (bcHom p 𝔓 h𝔓).comp (iotaX E₀ _ (comap_bcHom_mem p h𝔓))
  obtain ⟨𝔓₀, h𝔓₀, heq₀⟩ := exists_minimalPrimes_comap_eq (K := K) q h𝔇
  have hLoc : LocBar (punctured (E₀.baseChange K)) (bcComp K Y 𝔇 h𝔇) :=
    ⟨_, ⟨pC 𝔓₀ h𝔓₀⟩, ⟨bcHom' q 𝔓₀ h𝔓₀ 𝔇 h𝔇 heq₀⟩⟩
  obtain ⟨ψ⟩ := (hcore.2 _ hLoc).1
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := 𝔇) (ψ.f X)
  refine ⟨y, fun 𝔓 h𝔓 heq ↦ ?_⟩
  have hLocC : LocBar (punctured (E₀.baseChange K)) (bcComp K Z 𝔓 h𝔓) :=
    ⟨_, ⟨(bcHom p 𝔓 h𝔓).comp (iotaX E₀ _ (comap_bcHom_mem p h𝔓))⟩, ⟨Genuine.homId _⟩⟩
  haveI := (hcore.2 _ hLocC).2
  have h := congrArg (fun φ ↦ φ.f X) (Subsingleton.elim ((bcHom' q 𝔓 h𝔓 𝔇 h𝔇 heq).comp ψ)
    (((bcHom p 𝔓 h𝔓).comp (iotaX E₀ _ (comap_bcHom_mem p h𝔓))).comp
      (Genuine.hemiHom (E₀.baseChange K))))
  simp only [Hom.comp_f, AlgHom.comp_apply, Genuine.hemiHom_f] at h
  rw [iotaX_f_x] at h
  change _ = compMap K p.f 𝔓 _ at h
  rw [compMap_mk, bcMap_tmul, ← hy, bcHom'_f_mk] at h
  exact h

omit [CharZero K] [CharZero k₀] in
lemma bcMap_eq_lTensor {A B : Type*} [CommRing A] [CommRing B] [Algebra k₀ A] [Algebra k₀ B]
    (f : A →ₐ[k₀] B) (x : K ⊗[k₀] A) :
    bcMap K f x = LinearMap.lTensor K f.toLinearMap x := by
  induction x with
  | zero => simp
  | tmul c a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Descent descends** from `K` to `k₀`. -/
theorem hemiDescends_of_isCoreOf_baseChange
    (hcore : IsCoreOf (punctured (E₀.baseChange K)) (hemi (E₀.baseChange K))) :
    Genuine.HemiDescends E₀ := by
  intro Z Y p q
  have hY : LocallyDVR (K ⊗[k₀] Y.A) := locallyDVR_tensor Y.not_isField
  have hZ : LocallyDVR (K ⊗[k₀] Z.A) := locallyDVR_tensor Z.not_isField
  have : IsReduced (K ⊗[k₀] Z.A) := hZ.isReduced
  have : IsNoetherianRing (K ⊗[k₀] Y.A) := Algebra.FiniteType.isNoetherianRing K _
  choose y hy using fun (𝔇 : minimalPrimes (K ⊗[k₀] Y.A)) ↦ exists_lift_descent hcore p q 𝔇.2
  have : Finite (minimalPrimes (K ⊗[k₀] Y.A)) := minimalPrimes.finite_of_isNoetherianRing _
  have hcop : Pairwise (Function.onFun IsCoprime
      fun 𝔇 : minimalPrimes (K ⊗[k₀] Y.A) ↦ 𝔇.1) := by
    intro 𝔇 𝔇' hne
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact hY.sup_eq_top 𝔇.2 𝔇'.2 fun h ↦ hne (Subtype.ext h)
  obtain ⟨y', hy'⟩ := Ideal.pi_quotient_surjective hcop fun 𝔇 ↦ Ideal.Quotient.mk _ (y 𝔇)
  have hkey : bcMap K q.f y' = (1 : K) ⊗ₜ[k₀] p.f (Genuine.hemiMap E₀ X) := by
    refine eq_of_forall_minimalPrimes fun 𝔓 h𝔓 ↦ ?_
    set 𝔇 : minimalPrimes (K ⊗[k₀] Y.A) := ⟨_, comap_bcHom_mem q h𝔓⟩
    rw [← hy 𝔇 𝔓 h𝔓 rfl]
    rw [Ideal.Quotient.eq]
    have h1 : y' - y 𝔇 ∈ 𝔇.1 := Ideal.Quotient.eq.mp (hy' 𝔇)
    have h2 : bcMap K q.f (y' - y 𝔇) ∈ 𝔓 := h1
    rwa [map_sub] at h2
  have hmem : (1 : K) ⊗ₜ[k₀] p.f (Genuine.hemiMap E₀ X) ∈
      LinearMap.range (LinearMap.lTensor K q.f.toLinearMap) :=
    ⟨y', by rw [← bcMap_eq_lTensor, hkey]⟩
  obtain ⟨f, hf⟩ := mem_range_of_one_tmul_mem_range q.f.toLinearMap hmem
  exact ⟨f, hf⟩

/-- **The core comes down from a field extension**: if `(E_K ∖ 0)/±1` is the `K`-core of
`E_K ∖ 0`, then `(E₀ ∖ 0)/±1` is the `k₀`-core of `E₀ ∖ 0`. -/
theorem isCoreOf_hemi_of_baseChange
    (hcore : IsCoreOf (punctured (E₀.baseChange K)) (hemi (E₀.baseChange K))) :
    IsCoreOf (punctured E₀) (hemi E₀) :=
  Genuine.isCoreOf_hemi_of E₀ (hemiDescends_of_isCoreOf_baseChange hcore)
    (hemiRigid_of_isCoreOf_baseChange hcore)

end OrbicurveCores.Transfer
