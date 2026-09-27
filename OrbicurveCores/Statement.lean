/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.JValues

/-!
# The statement of [CanLift] Proposition 2.7 / [EstIUT] Proposition 2.1

> Let `K` be a field of characteristic zero and `E / K` an elliptic curve. If the once-punctured
> curve `X = E ∖ {0}` fails to admit a `K`-core, then
> `j(E) ∈ {0, 1728, 2¹⁴·31³/5³, 2²·73³/3⁴}`.

## The notion of core used here

Mochizuki's definition ([CanLift] Def. 2.1, Rem. 2.1.1) asks for a terminal object in the
category `\overline{Loc}_K(X)` of generically scheme-like algebraic stacks finite étale over, or
finite étale quotients of, covers of `X`. Mathlib has no algebraic stacks, so we use a
characterisation in terms of schemes. It is equivalent to Mochizuki's notion but that
equivalence is not formalised here (see `Blueprint.md`, §1.2):

* An **étale self-correspondence** of a `K̄`-scheme `X` is a pair of finite étale `K̄`-morphisms
  `α, β : C ⟶ X` from an irreducible scheme `C`. Its **support** is the image of the generic
  point of `C` in `X ×_{K̄} X`, i.e. the generic point of the irreducible curve `(α, β)(C)`.
* `X` **admits a core** iff the set of supports is **finite**.

Over `ℂ`, with `X = Γ \ ℍ`, supports correspond to double cosets `Γ δ Γ` for `δ ∈ Comm(Γ)`.
Since `[Comm(Γ) : Γ] = Σ_{ΓδΓ} [Γ : Γ ∩ δ⁻¹Γδ]`, finiteness of the set of supports is equivalent
to `[Comm(Γ) : Γ] < ∞`. That in turn is equivalent to the existence of the core `[Comm(Γ) \ ℍ]`
([Corr] §3, [CanLift] Rem. 2.1.2). Admitting a `K`-core depends only on `X_{K̄}`
([CanLift] Prop. 2.3), so we base change to `K̄ = AlgebraicClosure K`.

The group-theoretic counterpart of this definition is `OrbicurveCores.AdmitsCore` in
`OrbicurveCores.Core`, where the group-level form of the proposition (`canLift27_group`) is
proved conditionally on Margulis' theorem.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace OrbicurveCores

/-- The supports of the étale self-correspondences of an `S`-scheme `p : X ⟶ S`: the images in
`X ×_S X` of the generic points of irreducible schemes `C` with two finite étale `S`-morphisms
`C ⟶ X`. -/
def correspondenceSupports {S X : Scheme.{u}} (p : X ⟶ S) : Set (pullback p p : Scheme.{u}) :=
  {z | ∃ (C : Scheme.{u}) (_ : IrreducibleSpace C) (α β : C ⟶ X) (h : α ≫ p = β ≫ p),
    IsFinite α ∧ Etale α ∧ IsFinite β ∧ Etale β ∧ z = pullback.lift α β h (genericPoint C)}

/-- An `S`-scheme `X` (in practice: a hyperbolic curve over an algebraically closed field `S`)
*admits a core* if it has only finitely many irreducible étale self-correspondences. -/
def SchemeAdmitsCore {S X : Scheme.{u}} (p : X ⟶ S) : Prop :=
  (correspondenceSupports p).Finite

variable {K : Type u} [Field K]

/-- The once-punctured curve `E ∖ {0}` of a Weierstrass curve, base changed to `K̄`: the spectrum
of the affine coordinate ring of `W_{K̄}`. -/
noncomputable abbrev oncePuncturedBar (W : WeierstrassCurve K) : Scheme.{u} :=
  Spec (CommRingCat.of (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing)

/-- The structure morphism `E_{K̄} ∖ {0} ⟶ Spec K̄`. -/
noncomputable abbrev oncePuncturedBarStructure (W : WeierstrassCurve K) :
    oncePuncturedBar W ⟶ Spec (CommRingCat.of (AlgebraicClosure K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure K)
    (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing))

/-- The once-punctured elliptic curve `E ∖ {0}` admits a `K`-core. By [CanLift] Prop. 2.3 this is
the geometric condition that `E_{K̄} ∖ {0}` has finitely many étale self-correspondences. -/
def OncePuncturedAdmitsCore (W : WeierstrassCurve K) : Prop :=
  SchemeAdmitsCore (oncePuncturedBarStructure W)

/-- **[CanLift] Proposition 2.7, in the form of [EstIUT] Proposition 2.1** (statement only).
For every field `K` of characteristic zero and every elliptic curve `E / K`: if `E ∖ {0}` does
not admit a `K`-core, then `j(E) ∈ {0, 1728, 2¹⁴·31³/5³, 2²·73³/3⁴}`.

This is **not proved** in this repository. What is proved is the group-theoretic core of the
argument (`OrbicurveCores.canLift27_group`, conditional on Margulis' theorem), together with
Takeuchi's classification (`OrbicurveCores.takeuchi_one_infty`). See `Blueprint.md` for the
remaining pieces: uniformisation, algebraic ↔ analytic correspondences, and the identification
of the four curves. -/
def CanLift27 : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) [W.IsElliptic],
    ¬ OncePuncturedAdmitsCore W → IsExceptionalJ W.j

end OrbicurveCores
