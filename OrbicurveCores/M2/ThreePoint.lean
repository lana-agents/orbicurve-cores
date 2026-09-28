/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.ForMathlib.ProjectiveLine

/-!
# M2: triples and relative positions

`G s t = h(s) h(t)⁻¹ (0, 1, ∞)` for distinct triples `s`, `t`. Then:

* `G t' (rel t t') = t`;
* `G (g t) t = g (0, 1, ∞)`;
* `G` is continuous on pairs of distinct triples and takes distinct values.
-/

open Topology Set Filter OnePoint OnePoint.Proj

namespace OrbicurveCores.M2

variable {k : Type*} [Field k] [DecidableEq k]

/-- The standard triple `(0, 1, ∞)`. -/
def e₃ : Triple k := (((0 : k) : OnePoint k), ((1 : k) : OnePoint k), ∞)

omit [DecidableEq k] in
lemma distinct3_e₃ : Distinct3 (e₃ (k := k)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [e₃]

/-- Apply a Möbius matrix to a triple. -/
def mob3 (M : Matrix (Fin 2) (Fin 2) k) (t : Triple k) : Triple k :=
  (mob M t.1, mob M t.2.1, mob M t.2.2)

/-- `G s t = h(s) h(t)⁻¹ (0, 1, ∞)`. -/
def G3 (s t : Triple k) : Triple k := mob3 (tri s) (mob3 (tri t).adjugate e₃)

lemma mob3_tri {t : Triple k} (ht : Distinct3 t) : mob3 (tri t) e₃ = t := by
  simp only [mob3, e₃, mob_tri_zero ht, mob_tri_one ht, mob_tri_infty ht]

lemma rel_eq_mob3 (t t' : Triple k) : rel t t' = mob3 (tri t).adjugate t' := rfl

lemma distinct3_mob3 {M : Matrix (Fin 2) (Fin 2) k} (hM : M.det ≠ 0) {t : Triple k}
    (ht : Distinct3 t) : Distinct3 (mob3 M t) := by
  have inj : ∀ x y, mob M x = mob M y → x = y := by
    intro x y h
    have hM' : M.adjugate.det ≠ 0 := by rw [Matrix.det_adjugate]; simpa using hM
    rw [← mob_adjugate_mul hM x, h, mob_adjugate_mul hM y]
  exact ⟨fun h ↦ ht.1 (inj _ _ h), fun h ↦ ht.2.1 (inj _ _ h), fun h ↦ ht.2.2 (inj _ _ h)⟩

lemma distinct3_rel {t t' : Triple k} (ht : Distinct3 t) (ht' : Distinct3 t') :
    Distinct3 (rel t t') :=
  distinct3_mob3 (det_adjugate_tri_ne_zero ht) ht'

lemma distinct3_G3 {s t : Triple k} (hs : Distinct3 s) (ht : Distinct3 t) :
    Distinct3 (G3 s t) :=
  distinct3_mob3 (det_tri_ne_zero hs) (distinct3_mob3 (det_adjugate_tri_ne_zero ht) distinct3_e₃)

/-- `G t' (rel t t') = t`. -/
lemma G3_rel {t t' : Triple k} (ht : Distinct3 t) (ht' : Distinct3 t') :
    G3 t' (rel t t') = t := by
  set τ := rel t t'
  have hτ : Distinct3 τ := distinct3_rel ht ht'
  -- `h(t') h(τ)⁻¹` and `h(t)` agree on `τ`
  have key : ∀ y, mob (tri t') (mob (tri τ).adjugate y) = mob (tri t) y := by
    intro y
    rw [← mob_mul (det_adjugate_tri_ne_zero hτ)]
    have hd : (tri t' * (tri τ).adjugate).det ≠ 0 := by
      rw [Matrix.det_mul]; exact mul_ne_zero (det_tri_ne_zero ht') (det_adjugate_tri_ne_zero hτ)
    refine mob_eq_of_three hd (det_tri_ne_zero ht) hτ.1 hτ.2.1 hτ.2.2 ?_ ?_ ?_ y
    · rw [mob_mul (det_adjugate_tri_ne_zero hτ), mob_adjugate_tri_fst hτ, mob_tri_zero ht',
        show τ.1 = mob (tri t).adjugate t'.1 from rfl, mob_mul_adjugate (det_tri_ne_zero ht)]
    · rw [mob_mul (det_adjugate_tri_ne_zero hτ), mob_adjugate_tri_snd hτ, mob_tri_one ht',
        show τ.2.1 = mob (tri t).adjugate t'.2.1 from rfl, mob_mul_adjugate (det_tri_ne_zero ht)]
    · rw [mob_mul (det_adjugate_tri_ne_zero hτ), mob_adjugate_tri_thd hτ, mob_tri_infty ht',
        show τ.2.2 = mob (tri t).adjugate t'.2.2 from rfl, mob_mul_adjugate (det_tri_ne_zero ht)]
  rw [show G3 t' τ = (mob (tri t') (mob (tri τ).adjugate e₃.1),
    mob (tri t') (mob (tri τ).adjugate e₃.2.1), mob (tri t') (mob (tri τ).adjugate e₃.2.2))
    from rfl, key, key, key]
  exact mob3_tri ht

/-- `G (g t) t = g (0, 1, ∞)`. -/
lemma G3_smul3 (g : GL (Fin 2) k) {t : Triple k} (ht : Distinct3 t) :
    G3 (smul3 g t) t = smul3 g e₃ := by
  exact Prod.ext (smul_eq_mob_tri g ht _).symm
    (Prod.ext (smul_eq_mob_tri g ht _).symm (smul_eq_mob_tri g ht _).symm)

section topology

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

lemma continuousOn_G3 : ContinuousOn (fun p : Triple k × Triple k ↦ G3 p.1 p.2)
    {p | Distinct3 p.1 ∧ Distinct3 p.2} := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  have c1 : ∀ y, ContinuousAt (fun q : Triple k × Triple k ↦
      mob (tri q.1) (mob (tri q.2).adjugate y)) p := by
    intro y
    have hA := continuousAt_mobAdj hp.2 y
    have hB := continuousAt_mobTri hp.1 (mob (tri p.2).adjugate y)
    have h1 : ContinuousAt (fun q : Triple k × Triple k ↦ mob (tri q.2).adjugate y) p :=
      hA.comp (f := fun q : Triple k × Triple k ↦ (q.2, y)) (by fun_prop)
    exact hB.comp (f := fun q : Triple k × Triple k ↦ (q.1, mob (tri q.2).adjugate y))
      (continuousAt_fst.prodMk h1)
  simp only [G3, mob3]
  exact (c1 _).prodMk ((c1 _).prodMk (c1 _))

lemma continuousOn_rel : ContinuousOn (fun p : Triple k × Triple k ↦ rel p.1 p.2)
    {p | Distinct3 p.1} := fun p hp ↦
  (continuousAt_rel (t' := p.2) hp).continuousWithinAt

omit [DecidableEq k] in
lemma isOpen_distinct3 : IsOpen {t : Triple k | Distinct3 t} := by
  have e : {t : Triple k | Distinct3 t} =
      {y | y.1 ≠ y.2.1} ∩ {y | y.1 ≠ y.2.2} ∩ {y | y.2.1 ≠ y.2.2} := by
    ext; simp [Distinct3, and_assoc]
  rw [e]
  refine ((isOpen_ne_fun (f := fun t : Triple k ↦ t.1) (g := fun t ↦ t.2.1) (by fun_prop)
    (by fun_prop)).inter (isOpen_ne_fun (f := fun t : Triple k ↦ t.1) (g := fun t ↦ t.2.2)
    (by fun_prop) (by fun_prop))).inter (isOpen_ne_fun (f := fun t : Triple k ↦ t.2.1)
    (g := fun t ↦ t.2.2) (by fun_prop) (by fun_prop))

end topology

end OrbicurveCores.M2
