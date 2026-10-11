/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.CoordRing
import OrbicurveCores.Genuine.Rigid.Deck

/-!
# U2c2: evaluating functions on `E ∖ 0` along the uniformisation

* `coordEquiv`: the coordinate ring of `E ∖ 0` (pi1's integral closure) is `ℂ[x, y] / (W)`;
* `evP x y h`: evaluation at an affine point `(x, y)` of `E`;
* `sigmaX hπ`: the `ℂ`-algebra map `A_X → (ℂ → ℂ)`, `a ↦ (z ↦ a(π z))` (through `ofComplex`, so
  that it is defined everywhere), with holomorphic values (`differentiableOn_sigmaX`), invariant
  under `Γ` (`sigmaX_mob`), and `sigmaX (x) = π₁` (`sigmaX_hemiMap`).
-/

open Polynomial UpperHalfPlane Set
open scoped MatrixGroups Polynomial.Bivariate
open OrbicurveCores.S1 (upper)

namespace OrbicurveCores.Rigid

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

local notation "CR" => E.toAffine.CoordinateRing

/-- `ℂ[x, y] / (W) → A_X`. -/
noncomputable def toPR : CR →ₐ[ℂ[X]] AffOrbicurve.puncturedRing E :=
  (IsScalarTower.toAlgHom ℂ[X] CR E.toAffine.FunctionField).codRestrict
    (integralClosure ℂ[X] E.toAffine.FunctionField) fun g ↦
      (Algebra.IsIntegral.isIntegral (R := ℂ[X]) g).map
        (IsScalarTower.toAlgHom ℂ[X] CR E.toAffine.FunctionField)

lemma toPR_bijective : Function.Bijective (toPR E) := by
  refine ⟨fun a b h ↦ IsFractionRing.injective CR E.toAffine.FunctionField
    (by simpa [toPR] using congrArg Subtype.val h), fun ⟨f, hf⟩ ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_eq_of_isIntegral E f hf
  exact ⟨g, Subtype.ext (by simpa [toPR] using hg)⟩

/-- **The coordinate ring of `E ∖ 0` is `ℂ[x, y] / (W)`.** -/
noncomputable def coordEquiv : CR ≃ₐ[ℂ[X]] AffOrbicurve.puncturedRing E :=
  AlgEquiv.ofBijective (toPR E) (toPR_bijective E)

omit [E.IsElliptic] in
/-- Evaluation at an affine point of `E`, as a ring map. -/
noncomputable def liftEv (x y : ℂ) (h : E.toAffine.Equation x y) : CR →+* ℂ :=
  AdjoinRoot.lift (evalRingHom x) y (by rw [eval₂_evalRingHom]; exact h)

omit [E.IsElliptic] in
lemma liftEv_mk (x y : ℂ) (h : E.toAffine.Equation x y) (p : ℂ[X][Y]) :
    liftEv E x y h (AdjoinRoot.mk _ p) = p.evalEval x y := by
  rw [liftEv, AdjoinRoot.lift_mk, eval₂_evalRingHom]

omit [E.IsElliptic] in
/-- Evaluation at an affine point of `E`. -/
noncomputable def evP (x y : ℂ) (h : E.toAffine.Equation x y) : CR →ₐ[ℂ] ℂ where
  __ := liftEv E x y h
  commutes' c := by
    change liftEv E x y h (algebraMap ℂ CR c) = c
    rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] CR, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
      liftEv_mk, evalEval_C]
    simp

omit [E.IsElliptic] in
lemma evP_mk (x y : ℂ) (h : E.toAffine.Equation x y) (p : ℂ[X][Y]) :
    evP E x y h (AdjoinRoot.mk _ p) = p.evalEval x y :=
  liftEv_mk E x y h p

omit [E.IsElliptic] in
lemma evP_algebraMap (x y : ℂ) (h : E.toAffine.Equation x y) (q : ℂ[X]) :
    evP E x y h (algebraMap ℂ[X] CR q) = q.eval x := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, evP_mk, evalEval_C]

/-- A two-variable polynomial in holomorphic functions is holomorphic. -/
lemma differentiableOn_evalEval {f g : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) (p : ℂ[X][Y]) :
    DifferentiableOn ℂ (fun z ↦ p.evalEval (f z) (g z)) U := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [evalEval_add] using hp.fun_add hq
  | monomial n q =>
    have : (fun z ↦ (monomial n q).evalEval (f z) (g z)) = fun z ↦ q.eval (f z) * g z ^ n := by
      funext z; simp [evalEval, eval_monomial]
    rw [this]
    exact ((q.differentiable.comp_differentiableOn hf)).mul (hg.pow n)

variable {E} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- `π` through `ofComplex`, defined on all of `ℂ`. -/
noncomputable def piC (π : ℂ → ℂ × ℂ) (y : ℂ) : ℂ × ℂ := π (ofComplex y : ℂ)

omit [E.IsElliptic] in
lemma UnifProps.eqn_piC (hπ : UnifProps E A B π) (y : ℂ) :
    E.toAffine.Equation (piC π y).1 (piC π y).2 := hπ.eqn _

/-- **`σ_X`**: functions on `E ∖ 0` pulled back along `π`. -/
noncomputable def sigmaX (hπ : UnifProps E A B π) :
    AffOrbicurve.puncturedRing E →ₐ[ℂ] (ℂ → ℂ) :=
  AlgHom.pi fun y ↦ (evP E (piC π y).1 (piC π y).2 (hπ.eqn_piC y)).comp
    ((coordEquiv E).symm.restrictScalars ℂ).toAlgHom

lemma sigmaX_apply (hπ : UnifProps E A B π) (a : AffOrbicurve.puncturedRing E) (y : ℂ) :
    sigmaX hπ a y = evP E (piC π y).1 (piC π y).2 (hπ.eqn_piC y) ((coordEquiv E).symm a) := rfl

lemma piC_of_mem {y : ℂ} (hy : y ∈ upper) : piC π y = π y := by
  rw [piC, ofComplex_apply_of_im_pos hy]

/-- The values of `σ_X` are holomorphic on `ℍ`. -/
lemma differentiableOn_sigmaX (hπ : UnifProps E A B π) (a : AffOrbicurve.puncturedRing E) :
    DifferentiableOn ℂ (sigmaX hπ a) upper := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective ((coordEquiv E).symm a)
  have h1 : DifferentiableOn ℂ (fun y ↦ p.evalEval (π y).1 (π y).2) upper :=
    differentiableOn_evalEval (fun y hy ↦ ((hπ.diff ⟨y, hy⟩).1.fst).differentiableWithinAt)
      (fun y hy ↦ ((hπ.diff ⟨y, hy⟩).1.snd).differentiableWithinAt) p
  refine h1.congr fun y hy ↦ ?_
  rw [sigmaX_apply, ← hp, evP_mk, piC_of_mem hy]

/-- `σ_X (x) = π₁`. -/
lemma sigmaX_hemiMap (hπ : UnifProps E A B π) (y : ℂ) :
    sigmaX hπ (Genuine.hemiMap E Polynomial.X) y = (piC π y).1 := by
  rw [sigmaX_apply]
  have : (coordEquiv E).symm (Genuine.hemiMap E Polynomial.X) = algebraMap ℂ[X] CR X := by
    rw [AlgEquiv.symm_apply_eq]
    exact ((coordEquiv E).commutes X).symm
  rw [this, evP_algebraMap, eval_X]

/-- `σ_X` is `Γ`-invariant. -/
lemma sigmaX_mob (hπ : UnifProps E A B π) {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {A, B})
    (a : AffOrbicurve.puncturedRing E) (y : ℂ) : sigmaX hπ a (mob γ y) = sigmaX hπ a y := by
  have h : piC π (mob γ y) = piC π y := by
    rw [piC, ofComplex_mob, piC]
    exact ((hπ.fib _ _).mpr ⟨γ, hγ, rfl⟩).symm
  simp only [sigmaX_apply]
  congr 1; simp [h]

end OrbicurveCores.Rigid
