/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.HemiCore

/-!
# U2b: descent from rigidity

Let `X = E ∖ {0}` and `H = (E ∖ {0})/±1`. Descent (`HemiDescends E`: for finite étale
`p : Z → X`, `q : Z → Y`, the function `x ∘ p` descends along `q`) follows from rigidity
(`HemiRigid E`) and a purely algebraic statement about fibre products, `CompositumSeparates k`:

* if `Z` has trivial stabilisers and `c ∈ A_Z` does not come from `A_Y` along a finite étale
  `q : Z → Y`, then there are two finite étale maps `r₁, r₂ : W → Z` with `q r₁ = q r₂` and
  `r₁^* c ≠ r₂^* c`.

(Proof outline, Blueprint §2.6 U2f: `c ∉ k(Y)` since `A_Y` is integrally closed, so some
`k(Y)`-embedding `ε` of `k(Z)` into an algebraic closure moves `c`; take `W` the normalisation of
`Y` in the compositum `k(Z) · ε(k(Z))`. By Abhyankar's lemma (all ramification indices of
`Z → Y` over `y` equal `m_Y(y)`), `W → Z` is unramified for both embeddings.)

Indeed, rigidity applied to `W` with the cover `p ∘ r₁` shows that the finite étale
`x ∘ p ∘ r₂ : W → H` is `x ∘ p ∘ r₁`, i.e. `r₂^*(p^* x) = r₁^*(p^* x)`.

* `hemiDescends_of`: `HemiRigid E → CompositumSeparates k → HemiDescends E`.
-/

universe u

open AffOrbicurve Polynomial

namespace OrbicurveCores.Genuine

/-- **Fibre products separate functions** (Abhyankar's lemma): if `Z` has trivial stabilisers
and `c ∈ A_Z` does not come from `A_Y` along a finite étale `q : Z → Y`, then two finite étale
maps `r₁, r₂ : W → Z` with `q ∘ r₁ = q ∘ r₂` separate `c`. -/
def CompositumSeparates (k : Type u) [Field k] : Prop :=
  ∀ (Z Y : AffOrbicurve k) (q : Hom Z Y), (∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1) →
    ∀ c : Z.A, c ∉ Set.range q.f →
      ∃ (W : AffOrbicurve k) (r₁ r₂ : Hom W Z), r₁.f.comp q.f = r₂.f.comp q.f ∧ r₁.f c ≠ r₂.f c

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k)

/-- A finite étale cover of `E ∖ 0` has trivial stabilisers. -/
lemma mult_eq_one_of_hom {Z : AffOrbicurve k} (p : Hom Z (punctured E)) (w : Ideal Z.A)
    (hw : w.IsMaximal) : Z.mult w = 1 := by
  have h := p.etale w hw
  rw [punctured_mult] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- **U2b. Descent from rigidity** and the separation of functions by fibre products. -/
theorem hemiDescends_of (hR : HemiRigid E) (hC : CompositumSeparates k) : HemiDescends E := by
  intro Z Y p q
  by_contra h
  simp only [not_exists] at h
  obtain ⟨W, r₁, r₂, -, hne⟩ := hC Z Y q (mult_eq_one_of_hom E p) (p.f (hemiMap E X))
    (by rintro ⟨f, hf⟩; exact h f hf)
  have h' := hR W (r₁.comp p) ((r₂.comp p).comp (hemiHom E))
  simp only [Hom.comp_f, AlgHom.comp_apply, hemiHom_f] at h'
  exact hne h'.symm

end OrbicurveCores.Genuine
