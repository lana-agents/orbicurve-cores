/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Pi1.Orbicurve.Pullback

/-!
# The Galois closure of a finite étale cover of an orbicurve is étale over the cover

In the framework of `Pi1.Orbicurve.Subfield`: let `F ⊆ L ⊆ N` with `N / K₀` finite Galois, and
suppose the ramification index `e(w | F)` of the maximal ideals `w` of the coordinate ring of `L`
depends only on the prime under `w` (`L → (F, m)` is finite étale for a scheme `L`). Let
`M ⊆ N` be the Galois closure of `L / F` (the fixed field of the core
`⋂_{σ ∈ Gal(N/F)} σ Gal(N/L) σ⁻¹`). Then the coordinate ring of `M` is unramified over that of
`L` (`U2.ramificationIdx_closure_eq_one`).

Proof: for a maximal ideal `u` of the coordinate ring of `N` with (cyclic, tame) inertia group
`I`, `e(u ∩ L | F) · |I ∩ Gal(N/L)| = |I ∩ Gal(N/F)|`. The same holds for `σ⁻¹ u`, `σ ∈ Gal(N/F)`,
with the same `e`; conjugating, `|I ∩ σ Gal(N/L) σ⁻¹| = |I ∩ Gal(N/L)|`. In the cyclic group `I`
subgroups of equal order coincide, so `I ∩ Gal(N/L)` lies in the core, which is `Gal(N/M)`.
-/

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin
open scoped Pointwise

namespace OrbicurveCores.U2

open AffOrbicurve

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

section Core

variable {N : IntermediateField (K₀ k t) Ω} (F L : IntermediateField (K₀ k t) Ω)

/-- The core `⋂_{σ ∈ Gal(N/F)} σ Gal(N/L) σ⁻¹`. -/
def coreSub : Subgroup (N ≃ₐ[K₀ k t] N) :=
  ⨅ σ : fixSub t N F, (fixSub t N L).map (MulAut.conj (σ : N ≃ₐ[K₀ k t] N)).toMonoidHom

theorem coreSub_le : coreSub t F L ≤ fixSub t N L := by
  intro τ hτ
  have := Subgroup.mem_iInf.mp hτ 1
  simpa using this

theorem mem_coreSub {τ : N ≃ₐ[K₀ k t] N} :
    τ ∈ coreSub t F L ↔ ∀ σ ∈ fixSub t N F, σ⁻¹ * τ * σ ∈ fixSub t N L := by
  simp only [coreSub, Subgroup.mem_iInf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro h σ hσ
    obtain ⟨ρ, hρ, hρτ⟩ := h ⟨σ, hσ⟩
    rw [← hρτ]; simpa [mul_assoc] using hρ
  · intro h σ
    refine ⟨σ⁻¹ * τ * σ, h σ σ.2, ?_⟩
    simp [mul_assoc]

/-- The Galois closure of `L / F` inside `N`. -/
def closure : IntermediateField (K₀ k t) Ω :=
  (IntermediateField.fixedField (coreSub t F L (N := N))).map N.val

theorem closure_le : closure t F L (N := N) ≤ N := by
  rintro _ ⟨x, -, rfl⟩; exact x.2

theorem le_closure (hLN : L ≤ N) : L ≤ closure t F L (N := N) := by
  intro y hy
  refine ⟨⟨y, hLN hy⟩, ?_, rfl⟩
  rintro ⟨τ, hτ⟩
  exact coreSub_le t F L hτ ⟨y, hLN hy⟩ hy

variable [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N]

omit [IsGalois (K₀ k t) N] in
theorem fixSub_closure : fixSub t N (closure t F L (N := N)) = coreSub t F L := by
  rw [fixSub_eq_fixingSubgroup t (closure_le t F L)]
  have : IntermediateField.restrict (closure_le t F L (N := N)) =
      IntermediateField.fixedField (coreSub t F L (N := N)) := by
    ext x
    rw [IntermediateField.mem_restrict]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [this, IntermediateField.fixingSubgroup_fixedField]

end Core

section Cyclic

/-- In a finite cyclic group, subgroups of equal order are equal. -/
theorem le_of_card_eq_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H₁ H₂ : Subgroup C} (h : Nat.card H₁ = Nat.card H₂) : H₁ ≤ H₂ := by
  have hi : H₁.index = H₂.index := by
    have e1 := H₁.card_mul_index
    have e2 := H₂.card_mul_index
    rw [h] at e1
    have hpos : 0 < Nat.card H₂ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
  have h1 : (H₁ ⊓ H₂).index ∣ H₁.index := index_inf_dvd_of_isCyclic dvd_rfl (hi ▸ dvd_rfl)
  have h2 : H₁.index ∣ (H₁ ⊓ H₂).index := Subgroup.index_dvd_of_le inf_le_left
  have heq : (H₁ ⊓ H₂).index = H₁.index := Nat.dvd_antisymm h1 h2
  have hc : Nat.card (H₁ ⊓ H₂ : Subgroup C) = Nat.card H₁ := by
    have e1 := (H₁ ⊓ H₂).card_mul_index
    have e2 := H₁.card_mul_index
    rw [heq] at e1
    have hpos : 0 < H₁.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
    exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)
  have := Subgroup.eq_of_le_of_card_ge inf_le_left hc.ge
  exact this ▸ inf_le_right

end Cyclic

section Conj

variable {N : IntermediateField (K₀ k t) Ω}

set_option maxHeartbeats 1000000 in
-- instance search on coordinate rings of intermediate fields is slow
set_option synthInstance.maxHeartbeats 400000 in
/-- Conjugating the inertia group. -/
theorem card_inertia_inf_map_conj (σ : N ≃ₐ[K₀ k t] N) (H : Subgroup (N ≃ₐ[K₀ k t] N))
    (u : Ideal (coordRing k t N)) :
    Nat.card (((σ • u).inertia (N ≃ₐ[K₀ k t] N)) ⊓
      H.map (MulAut.conj σ).toMonoidHom : Subgroup _) =
      Nat.card ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ H : Subgroup _) := by
  let c := (MulAut.conj σ).toMonoidHom
  have hinj : Function.Injective c := (MulAut.conj σ).injective
  rw [← Subgroup.card_map_of_injective (f := c) (K := ((u.inertia (N ≃ₐ[K₀ k t] N)) ⊓ H :
    Subgroup (N ≃ₐ[K₀ k t] N))) hinj]
  congr 2
  ext τ
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, c]
  constructor
  · rintro ⟨hτ, ρ, hρH, rfl⟩
    refine ⟨ρ, ⟨?_, hρH⟩, rfl⟩
    simp only [Ideal.inertia, AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup] at hτ ⊢
    intro x
    have := hτ (σ • x)
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at this
    have e : ρ • x - x = σ⁻¹ • ((σ * ρ * σ⁻¹) • (σ • x) - σ • x) := by
      simp only [smul_sub, mul_smul, inv_smul_smul]
    rw [e]; exact this
  · rintro ⟨ρ, ⟨hρ, hρH⟩, rfl⟩
    refine ⟨?_, ρ, hρH, rfl⟩
    simp only [Ideal.inertia, AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup] at hρ ⊢
    intro x
    have := hρ (σ⁻¹ • x)
    have e : (σ * ρ * σ⁻¹) • x - x = σ • (ρ • (σ⁻¹ • x) - σ⁻¹ • x) := by
      rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
    rw [e]
    exact Ideal.smul_mem_pointwise_smul σ _ _ this

end Conj

section Ramification

variable {N : IntermediateField (K₀ k t) Ω} {F L : IntermediateField (K₀ k t) Ω}
  [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N] [CharZero k]

omit [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N] [CharZero k] in
theorem isMaximal_smul (σ : N ≃ₐ[K₀ k t] N) (u : Ideal (coordRing k t N)) [u.IsMaximal] :
    (σ • u).IsMaximal := by
  rw [Ideal.pointwise_smul_def]
  exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ σ)

set_option maxHeartbeats 2000000 in
-- instance search on coordinate rings of intermediate fields is slow
set_option synthInstance.maxHeartbeats 400000 in
/-- **The Galois closure is unramified over `L`** when `L → F` is unramified relative to the
multiplicities of `F`. -/
theorem ramificationIdx_closure_eq_one (ht : Transcendental k t) (hFL : F ≤ L) (hLN : L ≤ N)
    (mF : Ideal (coordRing k t F) → ℕ)
    (hm : ∀ w : Ideal (coordRing k t L), w.IsMaximal →
      (letI := algRing t hFL; w.ramificationIdx (coordRing k t F)) = mF (w.comap (ringMap t hFL)))
    (u : Ideal (coordRing k t N)) [hu : u.IsMaximal] (hu0 : u ≠ ⊥) :
    (letI := algRing t (le_closure t F L hLN);
      (u.comap (ringMap t (closure_le t F L (N := N)))).ramificationIdx (coordRing k t L)) = 1 := by
  classical
  set M := closure t F L (N := N)
  have hLM : L ≤ M := le_closure t F L hLN
  have hMN : M ≤ N := closure_le t F L
  have hFN : F ≤ N := hFL.trans hLN
  set G := N ≃ₐ[K₀ k t] N
  set HL := fixSub t N L
  set HF := fixSub t N F
  set I := u.inertia G
  haveI := isCyclic_inertia_coordRing t N ht u hu0
  have hcomap : ∀ v : Ideal (coordRing k t N),
      (v.comap (ringMap t hLN)).comap (ringMap t hFL) = v.comap (ringMap t hFN) := fun v ↦ rfl
  -- the key inclusion
  have key : I ⊓ HL ≤ fixSub t N M := by
    rw [fixSub_closure]
    rintro τ ⟨hτI, hτL⟩
    rw [mem_coreSub]
    intro σ hσ
    set u' := σ⁻¹ • u
    haveI : u'.IsMaximal := isMaximal_smul t σ⁻¹ u
    -- `u'` lies over the same prime of `F`
    have hover : u'.comap (ringMap t hFN) = u.comap (ringMap t hFN) := by
      ext x
      simp only [Ideal.mem_comap, u', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      have : σ • (ringMap t hFN x) = ringMap t hFN x := by
        apply Subtype.ext
        exact (mem_fixSub t).mp hσ _ (by simp)
      rw [this]
    -- equal ramification indices over `F`
    have he : (letI := algRing t hFL; (u'.comap (ringMap t hLN)).ramificationIdx
        (coordRing k t F)) = (letI := algRing t hFL; (u.comap (ringMap t hLN)).ramificationIdx
        (coordRing k t F)) := by
      haveI : (u'.comap (ringMap t hLN)).IsMaximal := by
        letI := algRing t hLN
        haveI : Algebra.IsIntegral (coordRing k t L) (coordRing k t N) :=
          ⟨ringMap_isIntegral t hLN⟩
        exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal u'
      haveI : (u.comap (ringMap t hLN)).IsMaximal := by
        letI := algRing t hLN
        haveI : Algebra.IsIntegral (coordRing k t L) (coordRing k t N) := ⟨ringMap_isIntegral t hLN⟩
        exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal u
      rw [hm _ inferInstance, hm _ inferInstance, hcomap, hcomap, hover]
    have E1 := ramificationIdx_mul_card t ht hFL hLN u
    have E1' := ramificationIdx_mul_card t ht hFL hLN u'
    rw [he] at E1'
    have hcF := card_inertia_inf_conj t σ⁻¹ HF
      (fun τ hτ ↦ HF.mul_mem (HF.mul_mem (HF.inv_mem hσ) hτ) (by simpa using hσ))
      (fun τ hτ ↦ HF.mul_mem (HF.mul_mem (by simpa using hσ) hτ) (HF.inv_mem hσ)) u
    rw [← hcF] at E1'
    have hpos : 0 < Nat.card (I ⊓ HF : Subgroup G) := Nat.card_pos
    have hcardL : Nat.card ((u'.inertia G) ⊓ HL : Subgroup G) = Nat.card (I ⊓ HL : Subgroup G) := by
      have h1 : (letI := algRing t hFL; (u.comap (ringMap t hLN)).ramificationIdx
          (coordRing k t F)) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at E1; exact hpos.ne' E1.symm
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) (E1'.trans E1.symm)
    -- conjugate back
    have hconj := card_inertia_inf_map_conj t σ HL u'
    have hσu : σ • u' = u := by simp [u']
    rw [hσu, hcardL] at hconj
    -- equal subgroups of the cyclic group `I`
    set J := HL.map (MulAut.conj σ).toMonoidHom
    have hle := le_of_card_eq_of_isCyclic (C := I) (H₁ := (I ⊓ HL).subgroupOf I)
      (H₂ := (I ⊓ J).subgroupOf I) (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hconj])
    have hτJ : τ ∈ J := by
      have := hle (show (⟨τ, hτI⟩ : I) ∈ (I ⊓ HL).subgroupOf I from
        Subgroup.mem_subgroupOf.mpr ⟨hτI, hτL⟩)
      exact (Subgroup.mem_subgroupOf.mp this).2
    obtain ⟨ρ, hρ, hρτ⟩ := hτJ
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hρτ
    rw [← hρτ]
    simpa [mul_assoc] using hρ
  -- conclusion
  have E2 := ramificationIdx_mul_card t ht hLM hMN u
  have heq : (I ⊓ fixSub t N M : Subgroup G) = I ⊓ HL := le_antisymm
    (inf_le_inf_left _ (fixSub_antitone t hLM)) (le_inf inf_le_left key)
  rw [heq] at E2
  have hpos : 0 < Nat.card (I ⊓ HL : Subgroup G) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (E2.trans (one_mul _).symm)

end Ramification

section Automorphisms

variable {N : IntermediateField (K₀ k t) Ω} {F L : IntermediateField (K₀ k t) Ω}

theorem conj_mem_coreSub {σ τ : N ≃ₐ[K₀ k t] N} (hσ : σ ∈ fixSub t N F)
    (hτ : τ ∈ coreSub t F L) : σ⁻¹ * τ * σ ∈ coreSub t F L := by
  rw [mem_coreSub] at hτ ⊢
  intro ρ hρ
  have := hτ (σ * ρ) ((fixSub t N F).mul_mem hσ hρ)
  simpa [mul_assoc] using this

theorem mem_closure_iff {y : Ω} (hy : y ∈ N) :
    y ∈ closure t F L (N := N) ↔ ∀ τ ∈ coreSub t F L, τ ⟨y, hy⟩ = ⟨y, hy⟩ := by
  constructor
  · rintro ⟨z, hz, hzy⟩ τ hτ
    rw [show (⟨y, hy⟩ : N) = z from Subtype.ext hzy.symm]
    exact (IntermediateField.mem_fixedField_iff _ _).mp hz τ hτ
  · intro h
    exact ⟨⟨y, hy⟩, (IntermediateField.mem_fixedField_iff _ _).mpr h, rfl⟩

/-- `Gal(N/F)` preserves the Galois closure. -/
theorem smul_mem_closure {σ : N ≃ₐ[K₀ k t] N} (hσ : σ ∈ fixSub t N F) {y : N}
    (hy : (y : Ω) ∈ closure t F L (N := N)) : ((σ y : N) : Ω) ∈ closure t F L (N := N) := by
  rw [mem_closure_iff t (σ y).2]
  rw [mem_closure_iff t y.2] at hy
  intro τ hτ
  have := hy (σ⁻¹ * τ * σ) (conj_mem_coreSub t hσ hτ)
  have e : τ (σ y) = σ ((σ⁻¹ * τ * σ) y) := by simp [AlgEquiv.mul_apply]
  change τ (σ y) = σ y
  rw [e, show (σ⁻¹ * τ * σ) y = y from this]

variable [FiniteDimensional (K₀ k t) N] [IsGalois (K₀ k t) N]

/-- Elements of `N` fixed by `Gal(N/F)` lie in `F`. -/
theorem mem_of_forall_fixSub (hFN : F ≤ N) {y : N} (hy : ∀ σ ∈ fixSub t N F, σ y = y) :
    (y : Ω) ∈ F := by
  have h1 : y ∈ IntermediateField.fixedField (fixSub t N F) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr hy
  rw [fixSub_eq_fixingSubgroup t hFN, IsGalois.fixedField_fixingSubgroup] at h1
  exact (IntermediateField.mem_restrict hFN y).mp h1

end Automorphisms

section Restrict

variable {N : IntermediateField (K₀ k t) Ω} {F L : IntermediateField (K₀ k t) Ω}

/-- The value in `N` of an element of the coordinate ring of the closure. -/
def toN (b : coordRing k t (closure t F L (N := N))) : N :=
  ⟨((b : closure t F L (N := N)) : Ω), closure_le t F L (b : closure t F L (N := N)).2⟩

theorem isIntegral_smul_toN (σ : N ≃ₐ[K₀ k t] N) (b : coordRing k t (closure t F L (N := N))) :
    IsIntegral (A₀ k t) ((σ (toN t b) : N) : Ω) := by
  have h1 := isIntegral_of_mem_coordRing t b
  haveI : IsScalarTower (A₀ k t) N Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 : IsIntegral (A₀ k t) (toN t b) :=
    (isIntegral_algebraMap_iff (A := N) (B := Ω) (algebraMap N Ω).injective).mp h1
  have h3 := h2.map ((σ : N →ₐ[K₀ k t] N).restrictScalars (A₀ k t))
  exact (isIntegral_algebraMap_iff (A := N) (B := Ω) (algebraMap N Ω).injective).mpr h3

theorem toN_injective : Function.Injective (toN t (F := F) (L := L) (N := N)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg (fun n : N ↦ (n : Ω)) h))

theorem toN_one : toN t (1 : coordRing k t (closure t F L (N := N))) = 1 := rfl
theorem toN_zero : toN t (0 : coordRing k t (closure t F L (N := N))) = 0 := rfl
theorem toN_mul (a b : coordRing k t (closure t F L (N := N))) :
    toN t (a * b) = toN t a * toN t b := rfl
theorem toN_add (a b : coordRing k t (closure t F L (N := N))) :
    toN t (a + b) = toN t a + toN t b := rfl
theorem toN_algebraMap (c : k) :
    toN t (algebraMap k (coordRing k t (closure t F L (N := N))) c) =
      algebraMap (K₀ k t) N (algebraMap k (K₀ k t) c) := rfl

/-- The restriction of `σ ∈ Gal(N/F)` to the coordinate ring of the Galois closure. -/
noncomputable def restrictClosure (σ : N ≃ₐ[K₀ k t] N) (hσ : σ ∈ fixSub t N F) :
    coordRing k t (closure t F L (N := N)) →ₐ[k] coordRing k t (closure t F L (N := N)) where
  toFun b := ⟨⟨((σ (toN t b) : N) : Ω),
      smul_mem_closure t hσ (y := toN t b) ((b : closure t F L (N := N))).2⟩,
    mem_coordRing_of_isIntegral t _ (isIntegral_smul_toN t σ b)⟩
  map_one' := toN_injective t (by
    change σ (toN t 1) = toN t 1
    rw [toN_one, map_one])
  map_mul' a b := toN_injective t (by
    change σ (toN t (a * b)) = σ (toN t a) * σ (toN t b)
    rw [toN_mul, map_mul])
  map_zero' := toN_injective t (by
    change σ (toN t 0) = toN t 0
    rw [toN_zero, map_zero])
  map_add' a b := toN_injective t (by
    change σ (toN t (a + b)) = σ (toN t a) + σ (toN t b)
    rw [toN_add, map_add])
  commutes' c := toN_injective t (by
    change σ (toN t (algebraMap k _ c)) = toN t (algebraMap k _ c)
    rw [toN_algebraMap, AlgEquiv.commutes])

theorem toN_restrictClosure (σ : N ≃ₐ[K₀ k t] N) (hσ : σ ∈ fixSub t N F)
    (b : coordRing k t (closure t F L (N := N))) :
    toN t (restrictClosure t σ hσ b) = σ (toN t b) := rfl

/-- As an automorphism. -/
noncomputable def restrictClosureEquiv (σ : N ≃ₐ[K₀ k t] N) (hσ : σ ∈ fixSub t N F) :
    coordRing k t (closure t F L (N := N)) ≃ₐ[k] coordRing k t (closure t F L (N := N)) :=
  AlgEquiv.ofAlgHom (restrictClosure t σ hσ) (restrictClosure t σ⁻¹ ((fixSub t N F).inv_mem hσ))
    (AlgHom.ext fun b ↦ toN_injective t (by
      simp only [AlgHom.coe_comp, Function.comp_apply, toN_restrictClosure, AlgHom.coe_id, id]
      exact σ.apply_symm_apply _))
    (AlgHom.ext fun b ↦ toN_injective t (by
      simp only [AlgHom.coe_comp, Function.comp_apply, toN_restrictClosure, AlgHom.coe_id, id]
      exact σ.symm_apply_apply _))

theorem toN_restrictClosureEquiv (σ : N ≃ₐ[K₀ k t] N) (hσ : σ ∈ fixSub t N F)
    (b : coordRing k t (closure t F L (N := N))) :
    toN t (restrictClosureEquiv t σ hσ b) = σ (toN t b) := rfl

end Restrict

end OrbicurveCores.U2
