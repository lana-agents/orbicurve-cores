/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.TripleNull
import OrbicurveCores.M2.Furstenberg
import OrbicurveCores.M2.Ergodic
import OrbicurveCores.M2.GoodLattice

/-!
# M2: commensurator superrigidity for lattices in `SL(2, ℝ)`

**Theorem** (`commensurator_superrigidity`, Margulis, specialised). Let `k` be a proper
nontrivially normed field (e.g. `ℂ` or `ℚ_p`). Let `Γ ≤ SL(2, ℝ)` be a good lattice, and let
`Γ ≤ Δ ≤ Comm(Γ)` with `Δ` dense. Let `a : Δ → PGL(2, k)` be an action on `ℙ¹(k)`, given by
matrices, such that:

* no finite-index subgroup of `Γ` fixes a point of `ℙ¹(k)`;
* `a(Γ)` is unbounded.

Then the action extends to a homomorphism `Φ : SL(2, ℝ) → PGL(2, k)` with `g ↦ Φ(g) y`
continuous for every `y`.

The proof strings together the parts of `Blueprint.md` §2.3b: the Furstenberg map (F), the
exclusion of three or more support points (`triple_null_of_unbounded`), the reduction to a point
map (`exists_pointMap_of_triple_null`), non-constancy, commensurator equivariance, and extension
(S).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology OnePoint.Proj
open scoped MatrixGroups

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]
  [MeasurableSpace k] [BorelSpace k]

/-- The action of `Γ` on `ℙ¹(k)` as a homomorphism to homeomorphisms. -/
noncomputable def actHom {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k}
    (hact : ActsOn Γ a) : Γ →* (OnePoint k ≃ₜ OnePoint k) where
  toFun γ :=
    { toEquiv := MulAction.toPerm (a γ)
      continuous_toFun := continuous_gl_smul _
      continuous_invFun := continuous_gl_smul _ }
  map_one' := by
    ext y
    exact hact.one y
  map_mul' g h := by
    ext y
    exact hact _ g.2 _ h.2 y

/-- **Commensurator superrigidity.** -/
theorem commensurator_superrigidity {Γ Δ : Subgroup SL(2, ℝ)} (hΓ : GoodLattice Γ)
    (hΓΔ : Γ ≤ Δ) (hΔ : Δ ≤ Subgroup.Commensurable.commensurator Γ)
    (hdense : Dense (Δ : Set SL(2, ℝ))) {a : SL(2, ℝ) → GL (Fin 2) k} (hact : ActsOn Δ a)
    (hne : NonElem Γ a) (hunb : Unbounded Γ a) :
    ∃ Φ : SL(2, ℝ) → GL (Fin 2) k,
      (∀ g h : SL(2, ℝ), ∀ y : OnePoint k, Φ (g * h) • y = Φ g • Φ h • y) ∧
      (∀ δ ∈ Δ, ∀ y : OnePoint k, Φ δ • y = a δ • y) ∧
      (∀ y : OnePoint k, Continuous fun g ↦ Φ g • y) := by
  haveI := hΓ.discrete
  haveI : Countable Γ := Fuchsian.countable_of_discrete Γ
  have hErg : ∀ Γ' : Subgroup SL(2, ℝ), Γ' ≤ Γ → Γ'.relIndex Γ ≠ 0 → IsDoublyErgodic Γ' :=
    fun Γ' hle hfi ↦ (hΓ.of_le hle hfi).isDoublyErgodic
  have hΓe : IsDoublyErgodic Γ := hΓ.isDoublyErgodic
  have hactΓ : ActsOn Γ a := hact.mono hΓΔ
  obtain ⟨κ, hκ, hκeq⟩ := hΓ.exists_boundaryKernel (actHom hactΓ)
  have heq : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, κ (γ • x) = (κ x).map (fun y ↦ a γ • y) := by
    intro γ hγ
    exact hκeq ⟨γ, hγ⟩
  have hT := triple_null_of_unbounded κ hΓe hunb heq
  obtain ⟨ψ, hψ, hψeq⟩ := exists_pointMap_of_triple_null hΓe hactΓ hne κ heq hT
  have hψne := ae_ne_of_equivariant hΓe hne hψ hψeq
  have hψΔ := equivariant_commensurator hΓΔ hΔ hErg hne hact hψ hψeq
  exact exists_extension hdense hψ hψΔ hψne

end OrbicurveCores.M2
