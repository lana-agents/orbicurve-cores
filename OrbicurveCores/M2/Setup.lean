/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fuchsian.Covolume

/-!
# M2: common setup

The shared definitions for the superrigidity part of M2 (see `Blueprint.md`, §2.3b):

* the boundary `B = ℙ¹(ℝ) = OnePoint ℝ`, with the Borel structure, the Möbius action of
  `SL(2, ℝ)` (through `GL(2, ℝ)`), and the Lebesgue-class measure `bdry`;
* `GoodLattice Γ`: `Γ` is discrete and has a measurable fundamental set of finite area and finite
  multiplicity;
* `IsDoublyErgodic Γ`: every `Γ`-invariant measurable subset of `B × B` is null or conull.
-/

open MeasureTheory Matrix Matrix.SpecialLinearGroup UpperHalfPlane OnePoint
open scoped MatrixGroups

namespace OrbicurveCores.M2

/-- The Borel structure on a one-point compactification. -/
instance instMeasurableSpaceOnePoint {X : Type*} [TopologicalSpace X] :
    MeasurableSpace (OnePoint X) := borel _

instance {X : Type*} [TopologicalSpace X] : BorelSpace (OnePoint X) := ⟨rfl⟩

/-- `SL(2, ℝ)` acts on the boundary `OnePoint ℝ` by Möbius transformations. -/
noncomputable instance instMulActionBdry : MulAction SL(2, ℝ) (OnePoint ℝ) :=
  MulAction.compHom _ Matrix.SpecialLinearGroup.toGL

lemma sl_smul_bdry (g : SL(2, ℝ)) (x : OnePoint ℝ) : g • x = toGL g • x := rfl

/-- The boundary measure: Lebesgue measure on `ℝ ⊆ OnePoint ℝ` (the point `∞` is null). -/
noncomputable def bdry : Measure (OnePoint ℝ) := (volume : Measure ℝ).map ((↑) : ℝ → OnePoint ℝ)

/-- `Γ` is discrete and has a measurable fundamental set `F ⊆ ℍ` of finite hyperbolic area,
meeting every orbit, with finite multiplicity. -/
structure GoodLattice (Γ : Subgroup SL(2, ℝ)) : Prop where
  discrete : DiscreteTopology Γ
  exists_fund : ∃ F : Set ℍ, MeasurableSet F ∧ volume F < ⊤ ∧ (∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F) ∧
    ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite

/-- `Γ` acts ergodically on `B × B` (diagonal action, Lebesgue class). -/
def IsDoublyErgodic (Γ : Subgroup SL(2, ℝ)) : Prop :=
  ∀ E : Set (OnePoint ℝ × OnePoint ℝ), MeasurableSet E →
    (∀ γ ∈ Γ, (fun p : OnePoint ℝ × OnePoint ℝ ↦ (γ • p.1, γ • p.2)) ⁻¹' E = E) →
      (bdry.prod bdry) E = 0 ∨ (bdry.prod bdry) Eᶜ = 0

end OrbicurveCores.M2
