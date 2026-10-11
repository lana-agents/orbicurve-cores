/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Fuchsian.PingPong
import OrbicurveCores.Fuchsian.OneInftyLattice
import OrbicurveCores.Fuchsian.DenseSubgroup
import OrbicurveCores.Core
import OrbicurveCores.Fuchsian.Commensurator

/-!
# R3a: the elliptic involution of a once-punctured torus group

Let `Γ = ⟨A₀, B₀⟩` be a once-punctured torus group in Fricke normal form (traces `x, y, z > 0`,
`x² + y² + z² = xyz`). The matrix `ι = [[0, -1/z], [z, 0]]` (rotation by `π` about `i/z`) satisfies

* `ι² = -1`, `ι A₀ ι⁻¹ = A₀⁻¹`, `ι B₀ ι⁻¹ = B₀⁻¹` (it lifts the elliptic involution `[-1]` of the
  punctured torus);
* `A₀ B₀ ι = -u₁` (translation `z ↦ z + 1`), while the commutator is `-u₂`.

Since `Γ` acts freely on the ping-pong quadrilateral, `-1 ∉ Γ` and `ι ∉ ±Γ`. Hence the
*hemi-elliptic group* `Γ⁺ = ±Γ ∪ ±Γ ι` is a subgroup of the commensurator of `Γ` containing `Γ`
with index `4` (`relIndex_nHemi`).

Main results:

* `nI`, `nI_mul_self`, `nI_conj_nA`, `nI_conj_nB`, `nA_mul_nB_mul_nI`;
* `neg_one_notMem`, `sq_ne_neg_one` (from the ping-pong freeness);
* `pmGroup`, `hemiGroup`, `nHemi`: `±Γ` and `Γ⁺`;
* `nHemi_le_commensurator`, `relIndex_nHemi : Γ.relIndex Γ⁺ = 4`, `uU_one_mem_nHemi`.
-/

open Matrix UpperHalfPlane
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores.Fuchsian

section involution

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The lift `ι = [[0, -1/z], [z, 0]]` of the elliptic involution (Fricke normal form). -/
noncomputable def nI : SL(2, ℝ) :=
  ⟨!![0, -1 / z; z, 0], by rw [det_fin_two_of]; field_simp; ring⟩

lemma coe_nI : ((nI hz : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1 / z; z, 0] := rfl

lemma nI_mul_self : nI hz * nI hz = -1 := by
  ext i j
  have hz0 : z ≠ 0 := hz.ne'
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_nI] <;> field_simp

lemma nI_inv : (nI hz)⁻¹ = -nI hz := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [mul_neg, nI_mul_self, neg_neg]

lemma nI_conj_nA : nI hz * nA hz hrel * (nI hz)⁻¹ = (nA hz hrel)⁻¹ := by
  rw [nI_inv]
  ext i j
  have hz0 : z ≠ 0 := hz.ne'
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_nI, coe_nA,
      adjugate_fin_two] <;> field_simp

lemma nI_conj_nB : nI hz * nB hz hrel * (nI hz)⁻¹ = (nB hz hrel)⁻¹ := by
  rw [nI_inv]
  ext i j
  have hz0 : z ≠ 0 := hz.ne'
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_nI, coe_nB,
      adjugate_fin_two] <;> field_simp

/-- `A₀ B₀ ι = -u₁`: the hemi-elliptic group contains the translation `z ↦ z + 1`. -/
lemma nA_mul_nB_mul_nI : nA hz hrel * nB hz hrel * nI hz = -SL2R.uU 1 := by
  ext i j
  have hz0 : z ≠ 0 := hz.ne'
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_nAnB, coe_nI]
  fin_cases i <;> fin_cases j <;>
    simp [SL2R.uU] <;> field_simp

include hx hy in
/-- An element of `Γ` fixing a point of the open ping-pong quadrilateral is trivial. -/
lemma eq_one_of_smul_eq {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) {w : ℍ}
    (hw : w ∈ ppQ x y z) (hfix : γ • w = w) : γ = 1 := by
  rw [← range_lift_normal] at hγ
  obtain ⟨g, rfl⟩ := hγ
  by_contra hne
  have hg : g ≠ 1 := by rintro rfl; exact hne (map_one _)
  have hmem := Set.smul_mem_smul_set (a := FreeGroup.lift (ppF hz hrel) g) hw
  rw [hfix] at hmem
  exact Set.disjoint_left.mp (pp_disjoint hx hy hz hrel hg) hmem hw

include hx hy in
/-- An element of `Γ` acting trivially on `ℍ` is trivial. -/
lemma eq_one_of_forall_smul_eq {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel})
    (hfix : ∀ w : ℍ, γ • w = w) : γ = 1 := by
  obtain ⟨w, hw⟩ := ppQ_nonempty hx hy hz
  exact eq_one_of_smul_eq hx hy hz hrel hγ hw (hfix w)

include hx hy in
/-- `-1 ∉ Γ`. -/
lemma neg_one_notMem : (-1 : SL(2, ℝ)) ∉ Subgroup.closure {nA hz hrel, nB hz hrel} := fun h ↦ by
  have := eq_one_of_forall_smul_eq hx hy hz hrel h fun w ↦ by
    rw [neg_smul_SL, one_smul]
  exact absurd (congrArg (fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) this)
    (by norm_num)

include hx hy in
/-- No element of `Γ` squares to `-1`. -/
lemma sq_ne_neg_one {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) :
    γ * γ ≠ -1 := fun h ↦ neg_one_notMem hx hy hz hrel (h ▸ mul_mem hγ hγ)

/-- Conjugation by `ι` preserves `Γ`. -/
lemma nI_conj_mem {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) :
    nI hz * γ * (nI hz)⁻¹ ∈ Subgroup.closure {nA hz hrel, nB hz hrel} := by
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · rw [nI_conj_nA]; exact inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))
    · rw [nI_conj_nB]
      exact inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  | one => simp
  | mul g h _ _ hg hh =>
    have e : nI hz * (g * h) * (nI hz)⁻¹ = (nI hz * g * (nI hz)⁻¹) * (nI hz * h * (nI hz)⁻¹) := by
      group
    rw [e]; exact mul_mem hg hh
  | inv g _ hg =>
    have e : nI hz * g⁻¹ * (nI hz)⁻¹ = (nI hz * g * (nI hz)⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hg

/-- Conjugation by `ι⁻¹ = -ι` preserves `Γ`. -/
lemma nI_inv_conj_mem {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) :
    (nI hz)⁻¹ * γ * nI hz ∈ Subgroup.closure {nA hz hrel, nB hz hrel} := by
  have e : (nI hz)⁻¹ * γ * nI hz = nI hz * γ * (nI hz)⁻¹ := by
    rw [nI_inv, neg_mul, neg_mul, mul_neg]
  rw [e]; exact nI_conj_mem hz hrel hγ

end involution

section groups

/-- `±Γ = Γ ∪ -Γ`. -/
def pmGroup (Γ : Subgroup SL(2, ℝ)) : Subgroup SL(2, ℝ) where
  carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr (by simpa using mul_mem ha hb)
    · exact Or.inr (by simpa using mul_mem ha hb)
    · exact Or.inl (by simpa using mul_mem ha hb)
  one_mem' := Or.inl Γ.one_mem
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (inv_mem ha)
    · exact Or.inr (by simpa using inv_mem ha)

lemma mem_pmGroup {Γ : Subgroup SL(2, ℝ)} {g : SL(2, ℝ)} : g ∈ pmGroup Γ ↔ g ∈ Γ ∨ -g ∈ Γ :=
  Iff.rfl

lemma le_pmGroup (Γ : Subgroup SL(2, ℝ)) : Γ ≤ pmGroup Γ := fun _ h ↦ Or.inl h

lemma neg_one_mem_pmGroup (Γ : Subgroup SL(2, ℝ)) : (-1 : SL(2, ℝ)) ∈ pmGroup Γ :=
  Or.inr (by simp)

lemma neg_mem_pmGroup {Γ : Subgroup SL(2, ℝ)} {g : SL(2, ℝ)} (h : g ∈ pmGroup Γ) :
    -g ∈ pmGroup Γ := by
  rcases h with h | h
  · exact Or.inr (by simpa using h)
  · exact Or.inl h

lemma conj_mem_pmGroup {Γ : Subgroup SL(2, ℝ)} {t : SL(2, ℝ)} (ht : ∀ g ∈ Γ, t * g * t⁻¹ ∈ Γ)
    {g : SL(2, ℝ)} (hg : g ∈ pmGroup Γ) :
    t * g * t⁻¹ ∈ pmGroup Γ := by
  rcases hg with hg | hg
  · exact Or.inl (ht g hg)
  · exact Or.inr (by simpa using ht _ hg)

/-- The group `±Γ ∪ ±Γ t` generated by `Γ` and an element `t` normalising `Γ` with `t² = -1`. -/
def hemiGroup (Γ : Subgroup SL(2, ℝ)) (t : SL(2, ℝ)) (ht : ∀ g ∈ Γ, t * g * t⁻¹ ∈ Γ)
    (ht' : ∀ g ∈ Γ, t⁻¹ * g * t ∈ Γ) (ht2 : t * t = -1) : Subgroup SL(2, ℝ) where
  carrier := {g | g ∈ pmGroup Γ ∨ g * t ∈ pmGroup Γ}
  mul_mem' := by
    have hP' : ∀ g ∈ pmGroup Γ, t⁻¹ * g * t⁻¹⁻¹ ∈ pmGroup Γ := fun g hg ↦
      conj_mem_pmGroup (t := t⁻¹) (by simpa using ht') hg
    have hti : t⁻¹ = -t := by
      rw [inv_eq_of_mul_eq_one_right]; rw [mul_neg, ht2, neg_neg]
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem ha hb)
    · refine Or.inr ?_
      have e : a * b * t = a * t * (t⁻¹ * b * t) := by group
      rw [e]
      exact mul_mem ha (by simpa using hP' b hb)
    · refine Or.inl ?_
      have e : a * b = a * t * (t⁻¹ * (b * t) * t⁻¹⁻¹) * (t⁻¹ * t⁻¹) := by group
      have e2 : t⁻¹ * t⁻¹ = -1 := by rw [hti, neg_mul, mul_neg, neg_neg, ht2]
      rw [e, e2]
      exact mul_mem (mul_mem ha (hP' _ hb)) (neg_one_mem_pmGroup Γ)
  one_mem' := Or.inl (pmGroup Γ).one_mem
  inv_mem' := by
    have hP : ∀ g ∈ pmGroup Γ, t * g * t⁻¹ ∈ pmGroup Γ := fun g hg ↦ conj_mem_pmGroup ht hg
    rintro a (ha | ha)
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ?_
      have e : a⁻¹ * t = t * (a * t)⁻¹ * t⁻¹ * (t * t) := by group
      rw [e, ht2]
      exact mul_mem (hP _ (inv_mem ha)) (neg_one_mem_pmGroup Γ)

/-- If `H ≤ K` and some `a ∈ K` satisfies `b a ∈ H ⊻ b ∈ H` for `b ∈ K`, then `[K : H] = 2`. -/
lemma relIndex_eq_two {G : Type*} [Group G] {H K : Subgroup G} {a : G} (ha : a ∈ K)
    (h : ∀ b ∈ K, Xor (b * a ∈ H) (b ∈ H)) : H.relIndex K = 2 :=
  Subgroup.index_eq_two_iff.mpr ⟨⟨a, ha⟩, fun b ↦ by
    simpa [Subgroup.mem_subgroupOf] using h b b.2⟩

lemma le_hemiGroup (Γ : Subgroup SL(2, ℝ)) (t : SL(2, ℝ)) (ht ht' ht2) :
    pmGroup Γ ≤ hemiGroup Γ t ht ht' ht2 := fun _ h ↦ Or.inl h

end groups

section hemi

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- **The hemi-elliptic group** `Γ⁺ = ±Γ ∪ ±Γ ι` of the normal form. -/
noncomputable def nHemi : Subgroup SL(2, ℝ) :=
  hemiGroup (Subgroup.closure {nA hz hrel, nB hz hrel}) (nI hz)
    (fun _ hg ↦ nI_conj_mem hz hrel hg) (fun _ hg ↦ nI_inv_conj_mem hz hrel hg) (nI_mul_self hz)

lemma pmGroup_le_nHemi : pmGroup (Subgroup.closure {nA hz hrel, nB hz hrel}) ≤ nHemi hz hrel :=
  le_hemiGroup _ _ _ _ _

lemma le_nHemi : Subgroup.closure {nA hz hrel, nB hz hrel} ≤ nHemi hz hrel :=
  (le_pmGroup _).trans (pmGroup_le_nHemi hz hrel)

lemma nI_mem_nHemi : nI hz ∈ nHemi hz hrel :=
  Or.inr (by rw [nI_mul_self]; exact neg_one_mem_pmGroup _)

lemma neg_one_mem_nHemi : (-1 : SL(2, ℝ)) ∈ nHemi hz hrel :=
  pmGroup_le_nHemi hz hrel (neg_one_mem_pmGroup _)

/-- The translation `z ↦ z + 1` lies in `Γ⁺`. -/
lemma uU_one_mem_nHemi : SL2R.uU 1 ∈ nHemi hz hrel := by
  have h : -SL2R.uU 1 ∈ nHemi hz hrel := by
    rw [← nA_mul_nB_mul_nI hz hrel]
    refine mul_mem (mul_mem ?_ ?_) (nI_mem_nHemi hz hrel)
    · exact le_nHemi hz hrel (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact le_nHemi hz hrel (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  simpa using mul_mem h (neg_one_mem_nHemi hz hrel)

include hx hy in
lemma relIndex_pmGroup :
    (Subgroup.closure {nA hz hrel, nB hz hrel}).relIndex
      (pmGroup (Subgroup.closure {nA hz hrel, nB hz hrel})) = 2 := by
  have h1 := neg_one_notMem hx hy hz hrel
  refine relIndex_eq_two (a := -1) (neg_one_mem_pmGroup _) fun b hb ↦ ?_
  rw [mul_neg_one]
  rcases hb with hb | hb
  · refine Or.inr ⟨hb, fun h ↦ h1 ?_⟩
    simpa using mul_mem (inv_mem hb) h
  · refine Or.inl ⟨hb, fun h ↦ h1 ?_⟩
    simpa using mul_mem (inv_mem h) hb

include hx hy in
lemma relIndex_pmGroup_nHemi :
    (pmGroup (Subgroup.closure {nA hz hrel, nB hz hrel})).relIndex (nHemi hz hrel) = 2 := by
  have hI : nI hz ∉ pmGroup (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
    rintro (h | h)
    · exact sq_ne_neg_one hx hy hz hrel h (nI_mul_self hz)
    · exact sq_ne_neg_one hx hy hz hrel h (by rw [neg_mul_neg, nI_mul_self])
  refine relIndex_eq_two (a := nI hz) (nI_mem_nHemi hz hrel) fun b hb ↦ ?_
  rcases hb with hb | hb
  · refine Or.inr ⟨hb, fun h ↦ hI ?_⟩
    simpa using mul_mem (inv_mem hb) h
  · refine Or.inl ⟨hb, fun h ↦ hI ?_⟩
    simpa using mul_mem (inv_mem h) hb

include hx hy in
/-- **R3a.** `[Γ⁺ : Γ] = 4`. -/
theorem relIndex_nHemi :
    (Subgroup.closure {nA hz hrel, nB hz hrel}).relIndex (nHemi hz hrel) = 4 := by
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (le_pmGroup _) (pmGroup_le_nHemi hz hrel),
    relIndex_pmGroup hx hy hz hrel, relIndex_pmGroup_nHemi hx hy hz hrel]

/-- `ι` normalises `Γ`, so it commensurates it. -/
lemma nI_mem_commensurator :
    nI hz ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct (nI hz) • Subgroup.closure {nA hz hrel, nB hz hrel} =
      Subgroup.closure {nA hz hrel, nB hz hrel} := by
    ext g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
    simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro h
      have := nI_conj_mem hz hrel h
      simpa [mul_assoc] using this
    · intro h
      exact nI_inv_conj_mem hz hrel h
  rw [this]

lemma neg_one_mem_commensurator' (Γ : Subgroup SL(2, ℝ)) : (-1 : SL(2, ℝ)) ∈ commensurator Γ := by
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct (-1 : SL(2, ℝ)) • Γ = Γ := by
    ext g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
    simp
  rw [this]

/-- `Γ⁺ ≤ Comm(Γ)`. -/
theorem nHemi_le_commensurator :
    nHemi hz hrel ≤ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  have hpm : pmGroup (Subgroup.closure {nA hz hrel, nB hz hrel}) ≤
      commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
    rintro g (h | h)
    · exact le_commensurator _ h
    · have := mul_mem (le_commensurator _ h)
        (neg_one_mem_commensurator' (Subgroup.closure {nA hz hrel, nB hz hrel}))
      simpa using this
  rintro g (h | h)
  · exact hpm h
  · have := mul_mem (hpm h) (inv_mem (nI_mem_commensurator hz hrel))
    simpa using this

end hemi

end OrbicurveCores.Fuchsian
