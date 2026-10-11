/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Hemi
import OrbicurveCores.Genuine.HomComp

/-!
# U2: when is `(E ∖ 0)/±1` the core of `E ∖ 0`? Reduction to descent and rigidity

Let `X = E ∖ {0}` and `H = (E ∖ {0})/±1` over a field `k` of characteristic `0`, with the
`x`-coordinate `X → H` (`hemiHom`). An object `Y` of `\overline{Loc}_k(X)` comes with finite étale
`p : Z → X` and `q : Z → Y`. This file shows, purely algebraically, that `H` is the `k`-core of
`X` (`isCoreOf_hemi_of`) as soon as

* **descent** (`HemiDescends E`): for all such `p, q`, the function `x ∘ p` on `Z` descends along
  `q`, i.e. `x ∘ p = q^*(f)` for some `f` in the coordinate ring of `Y`;
* **rigidity** (`HemiRigid E`): every finite étale `Z → H` from a finite étale cover `p : Z → X`
  is `x ∘ p`.

Given descent, `f` defines a finite étale `Y → H`: ramification indices are multiplicative
(`Hom.ramIdx_comp`), `p` is unramified with trivial multiplicities on `Z`, and `q` has
ramification `m_Y`. Uniqueness follows from rigidity and the injectivity of `q^*`.

Over `ℂ` both statements are analytic (Blueprint §2.6, U2b–U2e): descent uses that the fibres
of `Z(ℂ) → Y(ℂ)` lie in orbits of `Comm(Γ) = Γ⁺`, rigidity that a finite étale `Z → H` lifts to
a Möbius transformation commensurating `Γ`.
-/

universe u

open Polynomial AffOrbicurve

namespace OrbicurveCores.Genuine

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k)

/-- **Descent**: for finite étale `p : Z → X = E ∖ 0` and `q : Z → Y`, the function `x ∘ p`
descends along `q`. -/
def HemiDescends : Prop :=
  ∀ (Z Y : AffOrbicurve k) (p : Hom Z (punctured E)) (q : Hom Z Y),
    ∃ f : Y.A, q.f f = p.f (hemiMap E X)

/-- **Rigidity**: every finite étale morphism `Z → (E ∖ 0)/±1` from a finite étale cover
`p : Z → E ∖ 0` is `x ∘ p`. -/
def HemiRigid : Prop :=
  ∀ (Z : AffOrbicurve k) (p : Hom Z (punctured E)) (φ : Hom Z (hemi E)),
    φ.f X = p.f (hemiMap E X)

/-- Morphisms to `H` are determined by the image of `x`. -/
lemma hom_hemi_ext {Y : AffOrbicurve k} {φ ψ : Hom Y (hemi E)} (h : φ.f X = ψ.f X) : φ = ψ :=
  Hom.ext (Polynomial.algHom_ext h)

/-- **Existence**: a descended function `f` with `q^* f = p^* x` defines a finite étale
morphism `Y → H`. -/
noncomputable def homOfDescent {Z Y : AffOrbicurve k} (p : Hom Z (punctured E)) (q : Hom Z Y)
    (f : Y.A) (hf : q.f f = p.f (hemiMap E X)) : Hom Y (hemi E) := by
  let φf : (hemi E).A →ₐ[k] Y.A := aeval f
  have heq : q.f.comp φf = p.f.comp (hemiMap E) :=
    Polynomial.algHom_ext (by change q.f (aeval f X) = p.f (hemiMap E X); rw [aeval_X]; exact hf)
  have hinj : Function.Injective φf := by
    intro a b hab
    have h2 : (p.f.comp (hemiMap E)) a = (p.f.comp (hemiMap E)) b := by
      rw [← heq, AlgHom.comp_apply, AlgHom.comp_apply, hab]
    exact (hemiHom E).injective (p.injective h2)
  refine
    { f := φf
      injective := hinj
      isIntegral := ?_
      etale := ?_ }
  · intro a
    letI : Algebra (hemi E).A Y.A := φf.toRingHom.toAlgebra
    letI : Algebra (hemi E).A Z.A := ((q.f.comp φf).toRingHom).toAlgebra
    let qa : Y.A →ₐ[(hemi E).A] Z.A := { q.f.toRingHom with commutes' := fun _ ↦ rfl }
    have hint : IsIntegral (hemi E).A (q.f a) := by
      have h := (p.comp (hemiHom E)).isIntegral (q.f a)
      rw [Hom.comp_f, hemiHom_f, ← heq] at h
      exact h
    exact (isIntegral_algHom_iff qa q.injective).mp hint
  · intro w hw
    -- a maximal ideal `w'` of `Z` over `w`
    obtain ⟨w', hw'max, hw'⟩ : ∃ w' : Ideal Z.A, w'.IsMaximal ∧ w'.comap q.f = w := by
      letI : Algebra Y.A Z.A := q.f.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral Y.A Z.A := ⟨q.isIntegral⟩
      refine Ideal.exists_ideal_over_maximal_of_isIntegral (S := Z.A) w ?_
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap Y.A Z.A)).mp q.injective]
      exact bot_le
    have hu : (w'.comap p.f).IsMaximal := by
      letI : Algebra (punctured E).A Z.A := p.f.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (punctured E).A Z.A := ⟨p.isIntegral⟩
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := (punctured E).A) w'
    have hp := p.etale w' hw'max
    have hq := q.etale w' hw'max
    have hH := (hemiHom E).etale _ hu
    rw [punctured_mult] at hp hH
    rw [mul_one] at hH
    have hp1 := Nat.eq_one_of_mul_eq_one_right hp
    have hZ1 := Nat.eq_one_of_mul_eq_one_left hp
    rw [hZ1, mul_one] at hq
    have h1 := Hom.ramificationIdx_comp φf q.f q.injective w'
    have h2 := Hom.ramificationIdx_comp (hemiMap E) p.f p.injective w'
    rw [heq, h2, hp1, mul_one] at h1
    rw [hw'] at h1 hq
    rw [← hq, ← h1, ← hw']
    refine Eq.trans hH ?_
    congr 1
    change Ideal.comap (p.f.comp (hemiMap E)) w' = Ideal.comap (q.f.comp φf) w'
    rw [heq]

/-- **`(E ∖ 0)/±1` is the `k`-core of `E ∖ 0`**, given descent and rigidity. -/
theorem isCoreOf_hemi_of (hD : HemiDescends E) (hR : HemiRigid E) :
    IsCoreOf (punctured E) (hemi E) := by
  refine ⟨locBar_hemi E, fun Y ⟨Z, ⟨p⟩, ⟨q⟩⟩ ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf⟩ := hD Z Y p q
    exact ⟨homOfDescent E p q f hf⟩
  · refine ⟨fun φ ψ ↦ hom_hemi_ext E (q.injective ?_)⟩
    have h1 := hR Z p (q.comp φ)
    have h2 := hR Z p (q.comp ψ)
    simp only [Hom.comp_f, AlgHom.comp_apply] at h1 h2
    rw [h1, h2]

end OrbicurveCores.Genuine
