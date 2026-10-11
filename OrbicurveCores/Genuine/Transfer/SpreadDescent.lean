/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Transfer.SpreadRigid

/-!
# T1b/T3: models of morphisms `q : Z → Y`, and descent over every field of characteristic `0`

* `modelHom`: a finite étale `q : Z → Y` with `q(ρ_Y(B₀)) ⊆ ρ_Z(A₀)` descends to the models;
* `multDefinedOver_of_gens`: multiplicities are defined over a model containing generators of
  the special maximal ideals;
* `hemiDescends_of_complex`: descent over every field of characteristic `0`.
-/

open TensorProduct AffOrbicurve Polynomial

universe u v

namespace OrbicurveCores.Transfer

section ModelHom

variable {k₀ : Type u} [Field k₀] {k : Type (max u v)} [Field k] [Algebra k₀ k]
  {Z Y : AffOrbicurve k} {A₀ B₀ : Type u} [CommRing A₀] [Algebra k₀ A₀]
  [Algebra.FiniteType k₀ A₀] [CommRing B₀] [Algebra k₀ B₀] [Algebra.FiniteType k₀ B₀]
  (eZ : k ⊗[k₀] A₀ ≃ₐ[k] Z.A) (eY : k ⊗[k₀] B₀ ≃ₐ[k] Y.A)

omit [Algebra.FiniteType k₀ A₀] in
/-- `k`-algebra maps out of `A_Z` agreeing on `ρ(A₀)` agree. -/
lemma eq_of_eq_rhoM {D : Type*} [Ring D] [Algebra k D] (F₁ F₂ : Z.A →ₐ[k] D)
    (h : ∀ a, F₁ (rhoM Z eZ a) = F₂ (rhoM Z eZ a)) (z : Z.A) : F₁ z = F₂ z := by
  obtain ⟨t, rfl⟩ := eZ.surjective z
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c a =>
    have hc : c ⊗ₜ[k₀] a = c • ((1 : k) ⊗ₜ[k₀] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
    rw [hc, map_smul, map_smul, map_smul]
    exact congrArg (c • ·) (h a)
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]

variable (q : Hom Z Y) (h : ∀ b, ∃ a, rhoM Z eZ a = q.f (rhoM Y eY b))

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] in
include h in
lemma rhoM_choose (b : B₀) : rhoM Z eZ (h b).choose = q.f (rhoM Y eY b) := (h b).choose_spec

/-- The model `B₀ → A₀` of `q`. -/
noncomputable def liftModel : B₀ →ₐ[k₀] A₀ where
  toFun b := (h b).choose
  map_one' := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ 1
    rw [rhoM_choose, map_one, map_one, map_one])
  map_mul' a b := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ (_ * _)
    rw [rhoM_choose, map_mul (rhoM Z eZ), rhoM_choose, rhoM_choose, map_mul, map_mul])
  map_zero' := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ 0
    rw [rhoM_choose, map_zero, map_zero, map_zero])
  map_add' a b := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ (_ + _)
    rw [rhoM_choose, map_add (rhoM Z eZ), rhoM_choose, rhoM_choose, map_add, map_add])
  commutes' c := modelMap_injective eZ.toRingEquiv (by
    change rhoM Z eZ _ = rhoM Z eZ _
    rw [rhoM_choose, rhoM_algebraMap, rhoM_algebraMap, q.f.commutes])

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] in
lemma rhoM_liftModel (b : B₀) : rhoM Z eZ (liftModel eZ eY q h b) = q.f (rhoM Y eY b) :=
  rhoM_choose eZ eY q h b

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] in
lemma liftModel_injective : Function.Injective (liftModel eZ eY q h) := by
  intro a b hab
  have := congrArg (rhoM Z eZ) hab
  rw [rhoM_liftModel, rhoM_liftModel] at this
  exact modelMap_injective eY.toRingEquiv (q.injective this)

variable [CharZero k₀] (hZ : MultDefinedOver Z eZ) (hY : MultDefinedOver Y eY)

omit [Algebra.FiniteType k₀ A₀] [Algebra.FiniteType k₀ B₀] [CharZero k₀] in
lemma comap_bcMap_liftModel :
    (⊥ : Ideal (k ⊗[k₀] A₀)).comap (bcMap k (liftModel eZ eY q h)) = ⊥ := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨fun h' ↦ bcMap_injective _ (liftModel_injective eZ eY q h)
    (h'.trans (map_zero _).symm), fun h' ↦ by rw [h', map_zero]⟩

lemma hsq_model (hle : (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Y eY hY).A)) ≤
      (⊥ : Ideal (k ⊗[k₀] (modelOrbicurve Z eZ hZ).A)).comap
        (bcMap k (liftModel eZ eY q h)))
    (y : Y.A) : (iotaModel Z eZ hZ).f (q.f y) =
      Ideal.quotientMapₐ ⊥ (bcMap k (liftModel eZ eY q h)) hle ((iotaModel Y eY hY).f y) := by
  refine eq_of_eq_rhoM eY ((alphaModel Z eZ hZ).comp q.f)
    ((Ideal.quotientMapₐ ⊥ (bcMap k (liftModel eZ eY q h)) hle).comp (alphaModel Y eY hY))
    (fun b ↦ ?_) y
  change alphaModel Z eZ hZ (q.f (rhoM Y eY b)) =
    Ideal.quotientMapₐ ⊥ (bcMap k (liftModel eZ eY q h)) hle (alphaModel Y eY hY (rhoM Y eY b))
  rw [← rhoM_liftModel eZ eY q h, alphaModel_rhoM, alphaModel_rhoM]
  change _ = Ideal.Quotient.mk _ (bcMap k (liftModel eZ eY q h) ((1 : k) ⊗ₜ[k₀] b))
  rw [bcMap_tmul]

/-- **The model of `q : Z → Y`.** -/
noncomputable def modelHom : Hom (modelOrbicurve Z eZ hZ) (modelOrbicurve Y eY hY) :=
  haveI : IsDomain (k ⊗[k₀] (modelOrbicurve Z eZ hZ).A) := isDomain_tensor_model Z eZ
  homOfModels' q (liftModel eZ eY q h) ⊥ (bot_mem_minimalPrimes_model Y eY hY)
    (comap_bcMap_liftModel eZ eY q h) (iotaModel Z eZ hZ) (iotaModel Y eY hY)
    (alphaModel_bijective Z eZ hZ) (alphaModel_bijective Y eY hY)
    (hsq_model eZ eY q h hZ hY _) (liftModel_injective eZ eY q h) (lie_model eZ)

lemma rhoM_modelHom (b : B₀) :
    rhoM Z eZ ((modelHom eZ eY q h hZ hY).f b) = q.f (rhoM Y eY b) := by
  rw [modelHom, homOfModels'_f]
  exact rhoM_liftModel eZ eY q h b

end ModelHom

section Mult

variable {k₀ : Type u} [Field k₀] {k : Type (max u v)} [Field k] [Algebra k₀ k]
  {Y : AffOrbicurve k} {B₀ : Type u} [CommRing B₀] [Algebra k₀ B₀] [Algebra.FiniteType k₀ B₀]
  (eY : k ⊗[k₀] B₀ ≃ₐ[k] Y.A)

omit [Algebra.FiniteType k₀ B₀] in
lemma le_of_gens {w w' : Ideal Y.A} {G : Set Y.A} (hG : w = Ideal.span G)
    (hGr : G ⊆ Set.range (rhoM Y eY)) (hc : w.comap (rhoM Y eY) ≤ w'.comap (rhoM Y eY)) :
    w ≤ w' := by
  rw [hG, Ideal.span_le]
  intro x hx
  obtain ⟨b, rfl⟩ := hGr hx
  exact hc (show rhoM Y eY b ∈ w from hG ▸ Ideal.subset_span hx)

omit [Algebra.FiniteType k₀ B₀] in
/-- **Multiplicities are defined over a model containing generators of the special maximal
ideals.** -/
lemma multDefinedOver_of_gens (h : ∀ w : Ideal Y.A, w.IsMaximal → Y.mult w ≠ 1 →
      ∃ G : Set Y.A, w = Ideal.span G ∧ G ⊆ Set.range (rhoM Y eY)) :
    MultDefinedOver Y eY := by
  refine ⟨fun w w' hw hw' hc ↦ ?_, fun w hw hc ↦ ?_⟩
  · by_contra hne
    by_cases h1 : Y.mult w = 1
    · obtain ⟨G, hG, hGr⟩ := h w' hw' (fun h2 ↦ hne (h1.trans h2.symm))
      have := hw'.eq_of_le hw.ne_top (le_of_gens eY hG hGr hc.symm.le)
      exact hne (congrArg Y.mult this.symm)
    · obtain ⟨G, hG, hGr⟩ := h w hw h1
      have := hw.eq_of_le hw'.ne_top (le_of_gens eY hG hGr hc.le)
      exact hne (congrArg Y.mult this)
  · by_contra h1
    obtain ⟨G, hG, hGr⟩ := h w hw h1
    have hle := le_of_gens eY (w' := ⊥) hG hGr (by
      rw [hc]
      intro x hx
      rw [Ideal.mem_bot] at hx
      rw [Ideal.mem_comap, hx, map_zero]
      exact Ideal.zero_mem _)
    have hbot : w = ⊥ := le_bot_iff.mp hle
    rw [hbot] at hw
    exact Y.not_isField (Ring.isField_iff_maximal_bot.mpr hw)

omit [Algebra.FiniteType k₀ B₀] in
/-- Polynomials over `k₀` in elements of `ρ(B₀)` lie in `ρ(B₀)`. -/
lemma eval₂_mem_range {σ : Type*} (v : σ → Y.A) (hv : ∀ i, v i ∈ Set.range (rhoM Y eY))
    (f : MvPolynomial σ k₀) :
    MvPolynomial.eval₂ ((algebraMap k Y.A).comp (algebraMap k₀ k)) v f ∈
      Set.range (rhoM Y eY) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C]
    exact ⟨algebraMap k₀ B₀ a, rhoM_algebraMap eY a⟩
  | add f₁ f₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := h₂
    exact ⟨a₁ + a₂, by rw [map_add, ha₁, ha₂, MvPolynomial.eval₂_add]⟩
  | mul_X f₁ i h₁ =>
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := hv i
    exact ⟨a₁ * a₂, by rw [map_mul, ha₁, ha₂, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]⟩

end Mult

/-- **Descent over every field of characteristic `0`** (T3, descent half). -/
theorem hemiDescends_of_complex (h : CanLift27C) {k : Type u} [Field k] [CharZero k]
    (E : WeierstrassCurve k) [E.IsElliptic] (hj : ∀ c ∈ excJ, E.j ≠ (c : k)) :
    Genuine.HemiDescends E := by
  classical
  intro Z Y p q
  -- generators of the special maximal ideals of `Y`
  have hgens : ∀ w : Ideal Y.A, ∃ F : Finset Y.A, w = Ideal.span F := fun w ↦
    let ⟨F, hF⟩ := (IsNoetherian.noetherian w : w.FG)
    ⟨F, hF.symm⟩
  choose F hF using hgens
  let T := {w : Ideal Y.A | w.IsMaximal ∧ Y.mult w ≠ 1}
  let G : Set Y.A := ⋃ w ∈ T, (F w : Set Y.A)
  have hG : G.Finite := Y.finite_mult.biUnion fun w _ ↦ (F w).finite_toSet
  let tY : Fin hG.toFinset.card → Y.A := fun i ↦ (hG.toFinset.equivFin.symm i : Y.A)
  obtain ⟨mY, rY, PY, hPY⟩ := exists_presentation (k := k) tY
  let s : Fin (2 + (hG.toFinset.card + mY)) → Z.A :=
    Fin.append ![p.f (Genuine.hemiMap E X), p.f (yA E)] fun i ↦ q.f (PY.val i)
  obtain ⟨mZ, rZ, PZ, hPZ⟩ := exists_presentation (k := k) s
  let S : Set k := PZ.coeffs ∪ PY.coeffs ∪ {E.a₁, E.a₂, E.a₃, E.a₄, E.a₆}
  have hS : S.Finite := (PZ.finite_coeffs.union PY.finite_coeffs).union (by simp)
  obtain ⟨k₀, ι, hι⟩ := exists_subfield_complex S hS
  letI : Algebra k₀ k := ι.toAlgebra
  obtain ⟨E₀, rfl⟩ := exists_weierstrass_model (k₀ := k₀) E
    (fun x hx ↦ hι (Set.mem_union_right _ hx))
  haveI : E₀.IsElliptic := isElliptic_of_baseChange (k := k) E₀ inferInstance
  obtain ⟨-, hD⟩ := hemiRigid_subfield h k₀ E₀ fun c hc ↦ j_ne_of_baseChange E₀ c (hj c hc)
  obtain ⟨A₀, _, _, _, eZ, hgenZ, -⟩ := exists_model.{0, u} (k₀ := k₀) PZ
    fun x hx ↦ hι (Set.mem_union_left _ (Set.mem_union_left _ hx))
  obtain ⟨B₀, _, _, _, eY, hgenY, hpolyY⟩ := exists_model.{0, u} (k₀ := k₀) PY
    fun x hx ↦ hι (Set.mem_union_left _ (Set.mem_union_right _ hx))
  obtain ⟨x₀, hx₀⟩ := hgenZ (Fin.castAdd mZ (Fin.castAdd _ 0))
  obtain ⟨y₀, hy₀⟩ := hgenZ (Fin.castAdd mZ (Fin.castAdd _ 1))
  rw [hPZ] at hx₀ hy₀
  simp only [s, Fin.append_left] at hx₀ hy₀
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at hx₀ hy₀
  have hZ : MultDefinedOver Z eZ :=
    multDefinedOver_of_forall.{0, u} eZ (Genuine.mult_eq_one_of_hom _ p)
  have hY : MultDefinedOver Y eY := multDefinedOver_of_gens.{0, u} eY fun w hw hm ↦
    ⟨F w, hF w, fun x hx ↦ by
      have hxG : x ∈ hG.toFinset := hG.mem_toFinset.mpr (Set.mem_biUnion ⟨hw, hm⟩ hx)
      obtain ⟨b, hb⟩ := hgenY (Fin.castAdd mY (hG.toFinset.equivFin ⟨x, hxG⟩))
      refine ⟨b, hb.trans ?_⟩
      rw [hPY]
      simp [tY]⟩
  have hq : ∀ b, ∃ a, rhoM Z eZ a = q.f (rhoM Y eY b) := by
    intro b
    obtain ⟨f, hf⟩ := hpolyY b
    rw [rhoM_apply, hf]
    have h1 : q.f (MvPolynomial.eval₂ ((algebraMap k Y.A).comp (algebraMap k₀ k)) PY.val f) =
        MvPolynomial.eval₂ ((algebraMap k Z.A).comp (algebraMap k₀ k)) (fun i ↦ q.f (PY.val i))
          f := by
      refine (MvPolynomial.hom_eval₂ f _ q.f.toRingHom PY.val).trans ?_
      congr 1
      exact RingHom.ext fun c ↦ q.f.commutes _
    rw [h1]
    refine eval₂_mem_range.{0, u} eZ _ (fun i ↦ ?_) f
    obtain ⟨a, ha⟩ := hgenZ (Fin.castAdd mZ (Fin.natAdd 2 i))
    rw [hPZ] at ha
    simp only [s, Fin.append_right] at ha
    exact ⟨a, ha⟩
  obtain ⟨f₀, hf₀⟩ := hD _ _ (modelPunctured (k := k) E₀ eZ hZ p x₀ y₀ hx₀ hy₀)
    (modelHom eZ eY q hq hZ hY)
  refine ⟨rhoM Y eY f₀, ?_⟩
  rw [← rhoM_modelHom eZ eY q hq hZ hY, hf₀, rhoM_modelPunctured_x]

end OrbicurveCores.Transfer

namespace OrbicurveCores

/-- **Transfer** ([CanLift] Prop. 2.3(i),(ii) and the Lefschetz principle, [Corr] Lemma 4.1):
the statement "the hemi-elliptic quotient is the core" passes from `ℂ` to every field of
characteristic `0`, in every universe. -/
def HemiCoreTransfer : Prop :=
  CanLift27C → AffOrbicurve.CanLift27.{u}

/-- **T. Transfer**: the core property of the punctured hemi-elliptic orbicurve passes from `ℂ`
to every field of characteristic `0` ([CanLift] Prop. 2.3 and the Lefschetz principle). -/
theorem hemiCoreTransfer : HemiCoreTransfer.{u} := fun h _ _ _ E _ hj ↦
  Genuine.isCoreOf_hemi_of E (Transfer.hemiDescends_of_complex h E hj)
    (Transfer.hemiRigid_of_complex h E hj)

end OrbicurveCores
