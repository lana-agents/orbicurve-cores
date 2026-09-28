/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fuchsian.DenseCriterion
import OrbicurveCores.Fuchsian.Covolume
import OrbicurveCores.Core

/-!
# M1: infinite commensurator index implies dense commensurator

`OrbicurveCores.Fuchsian.commensurator_dense`: let `Γ ≤ SL(2, ℝ)` have finite covolume and contain
a hyperbolic `A` and an element `B` with `tr [A, B] ≠ 2` and `tr B ≠ 0`. If `[Comm(Γ) : Γ] = ∞`,
then `Comm(Γ)` is dense in `SL(2, ℝ)`. If `Comm(Γ)` were discrete, it would contain `Γ` with finite
index by the covolume bound; and a non-discrete overgroup of `Γ` is dense by the density criterion.

This splits `MargulisOneInfty` (`Core.lean`) into:

* `MargulisDenseOneInfty`: Margulis' commensurator theorem in its standard form (dense commensurator
  ⇒ arithmetic), for once-punctured torus groups;
* `OneInftyFiniteCovolume`: once-punctured torus groups have finite covolume (Fricke–Poincaré,
  still to be formalised);

(`margulisOneInfty_of_dense`).
-/

open Matrix Filter Topology
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores

namespace Fuchsian

lemma le_commensurator (Γ : Subgroup SL(2, ℝ)) : Γ ≤ commensurator Γ := by
  intro γ hγ
  rw [Subgroup.Commensurable.commensurator_mem_iff,
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hγ)]

/-- If `1` is isolated in a subgroup, the subgroup is discrete. -/
lemma discreteTopology_of_nhdsWithin_eq_bot {H : Subgroup SL(2, ℝ)}
    (h : 𝓝[(H : Set SL(2, ℝ)) \ {1}] (1 : SL(2, ℝ)) = ⊥) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  have hmem : (∅ : Set SL(2, ℝ)) ∈ 𝓝[(H : Set SL(2, ℝ)) \ {1}] (1 : SL(2, ℝ)) := by
    rw [h]; exact Filter.mem_bot
  obtain ⟨U, hUo, h1U, hU⟩ := mem_nhdsWithin.mp hmem
  refine isOpen_induced_iff.mpr ⟨U, hUo, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have : (x : SL(2, ℝ)) ∈ U ∩ ((H : Set SL(2, ℝ)) \ {1}) :=
      ⟨hx, x.2, fun h ↦ hne (Subtype.ext h)⟩
    exact hU this
  · rintro rfl; exact h1U

/-- **M1.** A group of finite covolume containing a hyperbolic `A` and some `B` with
`tr [A, B] ≠ 2`, `tr B ≠ 0`, which has infinite index in its commensurator, has a dense
commensurator. -/
theorem commensurator_dense {Γ : Subgroup SL(2, ℝ)} (hΓ : HasFiniteCovolume Γ) {A B : SL(2, ℝ)}
    (hA : A ∈ Γ) (hB : B ∈ Γ) (hx : 4 < tr A ^ 2) (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2)
    (hy : tr B ≠ 0) (hno : ¬ AdmitsCore Γ) : Dense (commensurator Γ : Set SL(2, ℝ)) := by
  refine SL2R.dense_of_not_discrete (le_commensurator Γ hA) (le_commensurator Γ hB) hx hc hy ?_
  rw [Filter.neBot_iff]
  intro h
  haveI := discreteTopology_of_nhdsWithin_eq_bot h
  exact hno (relIndex_ne_zero_of_discrete (le_commensurator Γ) hΓ)

end Fuchsian

/-- On the Fricke surface `x² + y² + z² = xyz`, a nonzero coordinate has square `> 4`. -/
lemma four_lt_sq_of_fricke {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (hx : x ≠ 0) :
    4 < x ^ 2 := by
  by_contra hle
  push Not at hle
  have hax : |x| ≤ 2 := by
    rw [← Real.sqrt_sq_eq_abs]; calc Real.sqrt (x ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hle
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : x * y * z ≤ |x| * |y| * |z| := by
    rw [← abs_mul, ← abs_mul]; exact le_abs_self _
  have h2 : |x| * |y| * |z| ≤ 2 * (|y| * |z|) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hax (by positivity)
  have h3 : 2 * (|y| * |z|) ≤ y ^ 2 + z ^ 2 := by
    nlinarith [sq_nonneg (|y| - |z|), sq_abs y, sq_abs z]
  have : x ^ 2 ≤ 0 := by linarith
  exact hx (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg x)))

/-- Once-punctured torus groups have finite covolume (Fricke–Poincaré; not yet proved here). -/
def OneInftyFiniteCovolume : Prop :=
  ∀ A B : SL(2, ℝ), tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 →
    Fuchsian.HasFiniteCovolume (Subgroup.closure {A, B})

/-- **Margulis' commensurator theorem** ([Marg] IX, [Zim] 6.2.5) in its standard form, for
once-punctured torus groups: a dense commensurator forces arithmeticity. Not proved here. -/
def MargulisDenseOneInfty : Prop :=
  ∀ A B : SL(2, ℝ), tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 →
    Dense (commensurator (Subgroup.closure {A, B}) : Set SL(2, ℝ)) →
      IsArithmeticSL (Subgroup.closure {A, B})

/-- The two remaining inputs imply `MargulisOneInfty`. -/
theorem margulisOneInfty_of_dense (hM : MargulisDenseOneInfty) (hL : OneInftyFiniteCovolume) :
    MargulisOneInfty := by
  intro A B hcomm hA hno
  have hrel := (tr_commutator_eq_neg_two_iff A B).mp hcomm
  have hy : tr B ≠ 0 := by
    intro h0
    rw [h0] at hrel
    exact hA (by nlinarith [sq_nonneg (tr A), sq_nonneg (tr (A * B))])
  have hx : 4 < tr A ^ 2 := four_lt_sq_of_fricke hrel hA
  refine hM A B hcomm hA (Fuchsian.commensurator_dense (hL A B hcomm hA)
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hx
    (by rw [hcomm]; norm_num) hy hno)

end OrbicurveCores
