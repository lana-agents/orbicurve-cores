/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.Model

/-!
# T1b: finite étale morphisms descend to models

Let `k₀ → k` be a field extension (characteristic `0`), `Z₀`, `Y₀` affine orbicurves over `k₀`
and `q : Z → Y` a finite étale morphism over `k`. Suppose `k ⊗ A_{Z₀}` is a domain and the
components `P = k ⊗ A_{Z₀}`, `Q` (below it) of the base changes come with isomorphisms of affine
orbicurves `P ≅ Z`, `Q ≅ Y` (finite étale morphisms with bijective maps of coordinate rings)
compatible with `q` and with an injective `g : A_{Y₀} → A_{Z₀}`. Then `g` is a finite étale
morphism `Z₀ → Y₀` (`homOfModels`): integrality descends (`isIntegral_of_isIntegral_tensor`) and
ramification indices are computed after base change (`comp_ramificationIdx`), where they agree
with those of `q` by invariance under isomorphisms.
-/

open TensorProduct AffOrbicurve

universe u v

namespace OrbicurveCores.Transfer

variable {k₀ : Type u} [Field k₀] [CharZero k₀] {k : Type (max u v)} [Field k] [Algebra k₀ k]

section IntegralElem

variable {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']

lemma isIntegralElem_comp_of_surjective (h : R →+* R') (hs : Function.Surjective h)
    (f : R' →+* S) {x : S} (hx : f.IsIntegralElem x) : (f.comp h).IsIntegralElem x := by
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨p', h1, -, h3⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts p).mpr fun n ↦ hs _) hp
  refine ⟨p', h3, ?_⟩
  rw [← Polynomial.eval₂_map, h1, hpx]

lemma isIntegralElem_of_comp (h : R →+* R') (f : R' →+* S) {x : S}
    (hx : (f.comp h).IsIntegralElem x) : f.IsIntegralElem x := by
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p.map h, hp.map h, by rwa [Polynomial.eval₂_map]⟩

lemma isIntegralElem_map (f : R →+* S) (j : S →+* S') {x : S} (hx : f.IsIntegralElem x) :
    (j.comp f).IsIntegralElem (j x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, hpx, map_zero]⟩

lemma isIntegralElem_of_map_injective (f : R →+* S) (j : S →+* S') (hj : Function.Injective j)
    {x : S} (hx : (j.comp f).IsIntegralElem (j x)) : f.IsIntegralElem x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p, hp, hj ?_⟩
  rw [Polynomial.hom_eval₂, hpx, map_zero]

end IntegralElem

section HomOfModels

variable {Z₀ Y₀ : AffOrbicurve k₀} {Z Y : AffOrbicurve k} (q : Hom Z Y)
  [IsDomain (k ⊗[k₀] Z₀.A)] (g : Y₀.A →ₐ[k₀] Z₀.A)

omit [CharZero k₀] in
lemma bot_mem_minimalPrimes_of_isDomain (T : Type*) [CommRing T] [IsDomain T] :
    (⊥ : Ideal T) ∈ minimalPrimes T :=
  ⟨⟨Ideal.isPrime_bot, le_rfl⟩, fun _ _ _ ↦ bot_le⟩

variable (hQ : (⊥ : Ideal (k ⊗[k₀] Z₀.A)).comap (bcMap k g) ∈ minimalPrimes (k ⊗[k₀] Y₀.A))
  (ιZ : Hom (bcComp k Z₀ ⊥ (bot_mem_minimalPrimes_of_isDomain _)) Z)
  (ιY : Hom (bcComp k Y₀ _ hQ) Y)
  (hιZ : Function.Bijective ιZ.f) (hιY : Function.Bijective ιY.f)
  (hsq : ∀ y : Y.A, ιZ.f (q.f y) = compMap k g ⊥ (ιY.f y))

omit [CharZero k₀] in
lemma mk_bot_injective (T : Type*) [CommRing T] :
    Function.Injective (Ideal.Quotient.mk (⊥ : Ideal T)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hx

include hsq hιZ in
/-- Integrality of `g` descends from that of `q`. -/
lemma isIntegral_of_models (z : Z₀.A) :
    (letI := g.toRingHom.toAlgebra; IsIntegral Y₀.A z) := by
  apply isIntegral_of_isIntegral_tensor (k := k) g
  obtain ⟨z', hz'⟩ := hιZ.2 (Ideal.Quotient.mk ⊥ ((1 : k) ⊗ₜ[k₀] z))
  obtain ⟨p, hp, hpz⟩ := q.isIntegral z'
  choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (I := (⊥ : Ideal (k ⊗[k₀] Z₀.A)).comap
    (bcMap k g)) (ιY.f (p.coeff i))
  set n := p.natDegree
  refine ⟨Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  apply mk_bot_injective
  rw [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow, map_zero, map_add,
    map_sum, map_pow]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul,
    map_pow]
  letI := (bcMap k g).toRingHom.toAlgebra
  have hcoe : ∀ i : ℕ, Ideal.Quotient.mk (⊥ : Ideal (k ⊗[k₀] Z₀.A))
      (algebraMap (k ⊗[k₀] Y₀.A) (k ⊗[k₀] Z₀.A) (c i)) = ιZ.f (q.f (p.coeff i)) := by
    intro i
    rw [hsq, ← hc]
    rfl
  simp only [hcoe, ← hz']
  rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow]
    at hpz
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hpz
  have := congrArg ιZ.f hpz
  rw [map_add, map_sum, map_zero, map_pow] at this
  simp only [map_mul, map_pow] at this
  rw [Finset.sum_range] at this
  exact this

variable (hg : Function.Injective g)
  (hlie : ∀ w₀ : Ideal Z₀.A, w₀.IsMaximal → ∃ W : Ideal (k ⊗[k₀] Z₀.A), W.IsMaximal ∧
    W.comap (Algebra.TensorProduct.includeRight : Z₀.A →ₐ[k₀] k ⊗[k₀] Z₀.A) = w₀)

include hsq hιZ hιY hg hlie in
lemma etale_of_models (w₀ : Ideal Z₀.A) (hw₀ : w₀.IsMaximal) :
    (letI := g.toRingHom.toAlgebra; w₀.ramificationIdx Y₀.A) * Z₀.mult w₀ =
      Y₀.mult (w₀.comap g) := by
  have hfin : g.toRingHom.Finite := by
    letI := g.toRingHom.toAlgebra
    haveI : IsScalarTower k₀ Y₀.A Z₀.A :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
    haveI : Algebra.FiniteType Y₀.A Z₀.A := Algebra.FiniteType.of_restrictScalars_finiteType k₀ _ _
    haveI : Algebra.IsIntegral Y₀.A Z₀.A :=
      ⟨fun z ↦ isIntegral_of_models q g hQ ιZ ιY hιZ hsq z⟩
    exact Algebra.IsIntegral.finite
  obtain ⟨W, hW, hWw⟩ := hlie w₀ hw₀
  have hb := bot_mem_minimalPrimes_of_isDomain (k ⊗[k₀] Z₀.A)
  set Wq : Ideal ((k ⊗[k₀] Z₀.A) ⧸ (⊥ : Ideal (k ⊗[k₀] Z₀.A))) := W.map (Ideal.Quotient.mk ⊥)
  have hWqc : Wq.comap (Ideal.Quotient.mk ⊥) = W := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_bot_eq]
  have hWq : Wq.IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      hW).resolve_left fun h ↦ hW.ne_top ?_
    have h' : Wq = ⊤ := h
    rw [← hWqc, h', Ideal.comap_top]
  have hw0 : w₀ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw₀ Z₀.not_isField
  have hcomp := comp_ramificationIdx (K := k) g hg hfin Y₀.not_isField Z₀.not_isField hb Wq
  rw [hWqc, hWw, if_neg hw0] at hcomp
  -- the same ideal, in the affine orbicurve `P`
  let Wb : Ideal (bcComp k Z₀ ⊥ hb).A := Wq
  haveI hWb : Wb.IsMaximal := hWq
  let β : (bcComp k Y₀ _ hQ).A →ₐ[k] (bcComp k Z₀ ⊥ hb).A := compMap k g ⊥
  have hcomm : ιZ.f.comp q.f = β.comp ιY.f := AlgHom.ext hsq
  haveI : Wb.IsPrime := hWb.isPrime
  have hsq' := ramificationIdx_eq_of_comm_square β ιZ.f ιY.f q.f (compMap_injective g ⊥)
    hιZ hιY hcomm Wb
  -- the étale conditions of `q`, `ιZ`, `ιY`
  set W' := Wb.comap ιZ.f
  have hW' : W'.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hιZ.2
  have hq := q.etale W' hW'
  have hZ := ιZ.etale Wb hWb
  rw [ramificationIdx_eq_one_of_bijective _ hιZ Wb, one_mul] at hZ
  set V := Wb.comap β
  have hV : V.IsMaximal := by
    letI := β.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (bcComp k Y₀ _ hQ).A (bcComp k Z₀ ⊥ hb).A :=
      ⟨(compMap_finite g hfin ⊥).to_isIntegral⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Wb
  have hY := ιY.etale V hV
  haveI : V.IsPrime := hV.isPrime
  rw [ramificationIdx_eq_one_of_bijective _ hιY V, one_mul] at hY
  have h1 : (letI := g.toRingHom.toAlgebra; w₀.ramificationIdx Y₀.A) =
      (letI := q.f.toRingHom.toAlgebra; W'.ramificationIdx Y.A) := hcomp.symm.trans hsq'
  have hPW : (Wb.comap (Ideal.Quotient.mk ⊥)).comap
      (Algebra.TensorProduct.includeRight : Z₀.A →ₐ[k₀] k ⊗[k₀] Z₀.A) = w₀ := by
    rw [← hWw, ← hWqc]; rfl
  have h2 : (bcComp k Z₀ ⊥ hb).mult Wb = Z₀.mult w₀ := by
    change compMult k Z₀ ⊥ Wb = _
    unfold compMult
    split_ifs with h
    · exact absurd (hPW.symm.trans h) hw0
    · exact congrArg Z₀.mult hPW
  have hVc : (V.comap (Ideal.Quotient.mk _)).comap
      (Algebra.TensorProduct.includeRight : Y₀.A →ₐ[k₀] k ⊗[k₀] Y₀.A) = w₀.comap g := by
    rw [← hPW]
    ext a
    exact Iff.rfl
  have hv0 : w₀.comap g ≠ ⊥ := by
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral Y₀.A Z₀.A := ⟨hfin.to_isIntegral⟩
    exact fun h ↦ hw0 (Ideal.eq_bot_of_comap_eq_bot h)
  have h3 : (bcComp k Y₀ _ hQ).mult V = Y₀.mult (w₀.comap g) := by
    change compMult k Y₀ _ V = _
    unfold compMult
    split_ifs with h
    · exact absurd (hVc.symm.trans h) hv0
    · exact congrArg Y₀.mult hVc
  have h4 : V.comap ιY.f = W'.comap q.f := by
    ext y
    change ιY.f y ∈ V ↔ q.f y ∈ W'
    change β (ιY.f y) ∈ Wb ↔ ιZ.f (q.f y) ∈ Wb
    rw [hsq]
    exact Iff.rfl
  rw [h1, ← h2, hZ, hq, ← h4, ← hY, h3]


/-- **Finite étale morphisms descend to models.** -/
noncomputable def homOfModels : Hom Z₀ Y₀ where
  f := g
  injective := hg
  isIntegral z := isIntegral_of_models q g hQ ιZ ιY hιZ hsq z
  etale w₀ hw₀ := etale_of_models q g hQ ιZ ιY hιZ hιY hsq hg hlie w₀ hw₀

end HomOfModels

end OrbicurveCores.Transfer
