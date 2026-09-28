/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# The projective line `OnePoint k` over a locally compact field

Generic material (candidate for upstreaming to Mathlib):

* `OnePoint.secondCountableTopology`: the one-point compactification of a second countable,
  locally compact Hausdorff space is second countable (hence metrizable).
* Homogeneous coordinates for `ℙ¹(k) = OnePoint k`: `proj`, `lift`, the bracket `br`.
* Möbius maps of matrices, `mob`, compatible with the `GL(2, k)`-action (`gl_smul_eq_mob`).
* A Möbius map with three distinct fixed points is trivial (`scalar_of_three_fixed`), and
  **sharp 3-transitivity** (`smul_eq_mob_tri`): `g x = h(g t) (h(t)⁻¹ x)` for a distinct triple
  `t`, where `h(t) = mob (tri t)` sends `0, 1, ∞` to `t`.
* The relative position `rel t t' = h(t)⁻¹ t'` is `GL(2, k)`-invariant (`rel_smul3`).
* Topology, for `k` a proper nontrivially normed field (e.g. `ℂ`, `ℚ_p`): `proj` is continuous
  on nonzero vectors, `(t, x) ↦ h(t)^{±1} x` is continuous on distinct triples, the action is
  continuous (`continuous_gl_smul`), and `rel` is continuous (`continuousAt_rel`).
-/

open Topology Set TopologicalSpace


namespace OnePoint
variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
  [T2Space X]

/-- The one-point compactification of a second countable locally compact Hausdorff space is
second countable. -/
instance secondCountableTopology : SecondCountableTopology (OnePoint X) := by
  obtain ⟨b, hbc, -, hb⟩ := exists_countable_basis X
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let s : Set (Set (OnePoint X)) :=
    ((fun u ↦ ((↑) : X → OnePoint X) '' u) '' b) ∪
      range fun n : ℕ ↦ (((↑) : X → OnePoint X) '' K n)ᶜ
  refine (isTopologicalBasis_of_isOpen_of_nhds (s := s) ?_ ?_).secondCountableTopology ?_
  · rintro u (⟨v, hv, rfl⟩ | ⟨n, rfl⟩)
    · exact isOpen_image_coe.2 (hb.isOpen hv)
    · exact isOpen_compl_image_coe.2 ⟨(K.isCompact n).isClosed, K.isCompact n⟩
  · intro a u ha hu
    induction a using OnePoint.rec with
    | infty =>
      obtain ⟨-, hc⟩ := (isOpen_iff_of_mem ha).1 hu
      obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hc
      refine ⟨_, Or.inr ⟨n, rfl⟩, infty_notMem_image_coe, ?_⟩
      intro y hy
      induction y using OnePoint.rec with
      | infty => exact ha
      | coe y =>
        by_contra hyu
        exact hy ⟨y, hn hyu, rfl⟩
    | coe a =>
      have ho : IsOpen (((↑) : X → OnePoint X) ⁻¹' u) := hu.preimage continuous_coe
      obtain ⟨v, hv, hav, hvu⟩ := hb.exists_subset_of_mem_open ha ho
      exact ⟨_, Or.inl ⟨v, hv, rfl⟩, ⟨a, hav, rfl⟩, by
        rintro _ ⟨y, hy, rfl⟩; exact hvu hy⟩
  · exact (hbc.image _).union (countable_range _)

end OnePoint

open Topology Set Filter OnePoint

namespace OnePoint.Proj
variable {k : Type*} [Field k]

/-- A chosen homogeneous coordinate vector of a point of `ℙ¹(k) = OnePoint k`. -/
def lift : OnePoint k → k × k
  | ∞ => (1, 0)
  | (a : k) => (a, 1)

/-- The determinant bracket `[v, w]`. -/
def br (v w : k × k) : k := v.1 * w.2 - v.2 * w.1

@[simp] lemma lift_infty : lift (∞ : OnePoint k) = (1, 0) := rfl
@[simp] lemma lift_coe (a : k) : lift (a : OnePoint k) = (a, 1) := rfl

lemma lift_ne_zero (x : OnePoint k) : lift x ≠ 0 := by
  cases x <;> simp [Prod.ext_iff]

variable [DecidableEq k]

/-- The point of `ℙ¹(k) = OnePoint k` with homogeneous coordinates `[a : b]`. -/
def proj (v : k × k) : OnePoint k := if v.2 = 0 then ∞ else ((v.1 / v.2 : k) : OnePoint k)

@[simp] lemma proj_lift (x : OnePoint k) : proj (lift x) = x := by
  cases x <;> simp [proj]

lemma proj_smul {c : k} (hc : c ≠ 0) (v : k × k) : proj (c • v) = proj v := by
  unfold proj
  simp only [Prod.smul_snd, smul_eq_mul, mul_eq_zero, hc, false_or]
  split_ifs with h
  · rfl
  · rw [Prod.smul_fst, smul_eq_mul, mul_div_mul_left _ _ hc]

lemma lift_proj {v : k × k} (hv : v ≠ 0) : ∃ c : k, c ≠ 0 ∧ lift (proj v) = c • v := by
  unfold proj
  split_ifs with h
  · have h1 : v.1 ≠ 0 := fun h1 ↦ hv (Prod.ext h1 h)
    exact ⟨v.1⁻¹, inv_ne_zero h1, by simp [Prod.ext_iff, h, h1]⟩
  · exact ⟨v.2⁻¹, inv_ne_zero h, by simp [Prod.ext_iff, h, div_eq_inv_mul]⟩

lemma proj_eq_proj_iff {v w : k × k} (hv : v ≠ 0) (hw : w ≠ 0) :
    proj v = proj w ↔ br v w = 0 := by
  unfold proj br
  have hv' : v.2 = 0 → v.1 ≠ 0 := fun h h1 ↦ hv (Prod.ext h1 h)
  have hw' : w.2 = 0 → w.1 ≠ 0 := fun h h1 ↦ hw (Prod.ext h1 h)
  split_ifs with h1 h2 h2
  · simp [h1, h2]
  · simp only [OnePoint.infty_ne_coe, false_iff, h1, zero_mul, sub_zero]
    exact mul_ne_zero (hv' h1) h2
  · simp only [OnePoint.coe_ne_infty, false_iff, h2, mul_zero, zero_sub, neg_eq_zero]
    exact mul_ne_zero h1 (hw' h2)
  · rw [OnePoint.coe_eq_coe, div_eq_div_iff h1 h2, sub_eq_zero, mul_comm w.1]

omit [DecidableEq k] in
lemma br_lift_eq_zero_iff {x y : OnePoint k} : br (lift x) (lift y) = 0 ↔ x = y := by
  classical
  rw [← proj_eq_proj_iff (lift_ne_zero x) (lift_ne_zero y), proj_lift, proj_lift]


/-! ### Möbius maps given by matrices -/

/-- A `2 × 2` matrix acting on `k × k`. -/
def mv (M : Matrix (Fin 2) (Fin 2) k) (v : k × k) : k × k :=
  (M 0 0 * v.1 + M 0 1 * v.2, M 1 0 * v.1 + M 1 1 * v.2)

/-- The Möbius map of a matrix. -/
def mob (M : Matrix (Fin 2) (Fin 2) k) (x : OnePoint k) : OnePoint k := proj (mv M (lift x))

omit [DecidableEq k] in
lemma mv_smul (M : Matrix (Fin 2) (Fin 2) k) (c : k) (v : k × k) : mv M (c • v) = c • mv M v := by
  simp only [mv, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

omit [DecidableEq k] in
lemma mv_mul (M N : Matrix (Fin 2) (Fin 2) k) (v : k × k) : mv (M * N) v = mv M (mv N v) := by
  simp only [mv, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq]
  constructor <;> ring

omit [DecidableEq k] in
lemma mv_ne_zero {M : Matrix (Fin 2) (Fin 2) k} (hM : M.det ≠ 0) {v : k × k} (hv : v ≠ 0) :
    mv M v ≠ 0 := by
  intro h
  simp only [mv, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
  rw [Matrix.det_fin_two] at hM
  apply hv
  have e1 : (M 0 0 * M 1 1 - M 0 1 * M 1 0) * v.1 = 0 := by
    linear_combination M 1 1 * h.1 - M 0 1 * h.2
  have e2 : (M 0 0 * M 1 1 - M 0 1 * M 1 0) * v.2 = 0 := by
    linear_combination M 0 0 * h.2 - M 1 0 * h.1
  exact Prod.ext ((mul_eq_zero.mp e1).resolve_left hM) ((mul_eq_zero.mp e2).resolve_left hM)

lemma mob_proj (M : Matrix (Fin 2) (Fin 2) k) {v : k × k} (hv : v ≠ 0) :
    mob M (proj v) = proj (mv M v) := by
  obtain ⟨c, hc, e⟩ := lift_proj hv
  rw [mob, e, mv_smul, proj_smul hc]

lemma mob_mul {M N : Matrix (Fin 2) (Fin 2) k} (hN : N.det ≠ 0) (x : OnePoint k) :
    mob (M * N) x = mob M (mob N x) := by
  rw [show mob N x = proj (mv N (lift x)) from rfl,
    mob_proj M (mv_ne_zero hN (lift_ne_zero x)), mob, mv_mul]

lemma gl_smul_eq_mob (g : GL (Fin 2) k) (x : OnePoint k) :
    g • x = mob (g : Matrix (Fin 2) (Fin 2) k) x := by
  cases x with
  | infty => simp [smul_infty_eq_ite, mob, mv, proj]
  | coe a => simp [smul_some_eq_ite, mob, mv, proj]

lemma mob_smul_matrix {c : k} (hc : c ≠ 0) (M : Matrix (Fin 2) (Fin 2) k) (x : OnePoint k) :
    mob (c • M) x = mob M x := by
  have : mv (c • M) (lift x) = c • mv M (lift x) := by
    simp only [mv, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [mob, this, proj_smul hc, mob]

lemma mob_one (x : OnePoint k) : mob (1 : Matrix (Fin 2) (Fin 2) k) x = x := by
  have : mv (1 : Matrix (Fin 2) (Fin 2) k) (lift x) = lift x := by
    simp [mv]
  rw [mob, this, proj_lift]

lemma mob_adjugate_mul {N : Matrix (Fin 2) (Fin 2) k} (hN : N.det ≠ 0) (x : OnePoint k) :
    mob N.adjugate (mob N x) = x := by
  rw [← mob_mul hN, Matrix.adjugate_mul, mob_smul_matrix hN, mob_one]

lemma mob_mul_adjugate {N : Matrix (Fin 2) (Fin 2) k} (hN : N.det ≠ 0) (x : OnePoint k) :
    mob N (mob N.adjugate x) = x := by
  have hN' : N.adjugate.det ≠ 0 := by
    rw [Matrix.det_adjugate]; simpa using hN
  rw [← mob_mul hN', Matrix.mul_adjugate, mob_smul_matrix hN, mob_one]

omit [DecidableEq k] in
/-- A binary quadratic form vanishing at three distinct points of `ℙ¹` is zero. -/
lemma quad_eq_zero_aux {A B C a₁ a₂ a₃ : k} (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (e₁ : A * a₁ ^ 2 + B * a₁ + C = 0) (e₂ : A * a₂ ^ 2 + B * a₂ + C = 0)
    (e₃ : A * a₃ ^ 2 + B * a₃ + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have f₁ : A * (a₁ + a₂) + B = 0 := by
    have : (a₁ - a₂) * (A * (a₁ + a₂) + B) = 0 := by linear_combination e₁ - e₂
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h12)
  have f₂ : A * (a₁ + a₃) + B = 0 := by
    have : (a₁ - a₃) * (A * (a₁ + a₃) + B) = 0 := by linear_combination e₁ - e₃
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h13)
  have hA : A = 0 := by
    have : A * (a₂ - a₃) = 0 := by linear_combination f₁ - f₂
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h23)
  have hB : B = 0 := by rw [hA] at f₁; linear_combination f₁
  refine ⟨hA, hB, ?_⟩
  rw [hA, hB] at e₁; linear_combination e₁

omit [DecidableEq k] in
lemma quad_eq_zero_aux' {A B C a₂ a₃ : k} (h23 : a₂ ≠ a₃) (e₁ : A = 0)
    (e₂ : A * a₂ ^ 2 + B * a₂ + C = 0) (e₃ : A * a₃ ^ 2 + B * a₃ + C = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  subst e₁
  have hB : B = 0 := by
    have : B * (a₂ - a₃) = 0 := by linear_combination e₂ - e₃
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h23)
  refine ⟨rfl, hB, ?_⟩
  rw [hB] at e₂; linear_combination e₂

/-- The binary quadratic form `A a² + B a b + C b²`. -/
def quad (A B C : k) (v : k × k) : k := A * v.1 ^ 2 + B * v.1 * v.2 + C * v.2 ^ 2

omit [DecidableEq k] in
lemma quad_eq_zero {A B C : k} {x y z : OnePoint k} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ex : quad A B C (lift x) = 0) (ey : quad A B C (lift y) = 0)
    (ez : quad A B C (lift z) = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  cases x with
  | infty =>
    cases y with
    | infty => exact absurd rfl hxy
    | coe b =>
      cases z with
      | infty => exact absurd rfl hxz
      | coe c =>
        simp only [quad, lift_infty, lift_coe] at ex ey ez
        exact quad_eq_zero_aux' (fun h ↦ hyz (congrArg _ h)) (by simpa using ex)
          (by simpa using ey) (by simpa using ez)
  | coe a =>
    cases y with
    | infty =>
      cases z with
      | infty => exact absurd rfl hyz
      | coe c =>
        simp only [quad, lift_infty, lift_coe] at ex ey ez
        exact quad_eq_zero_aux' (fun h ↦ hxz (congrArg _ h)) (by simpa using ey)
          (by simpa using ex) (by simpa using ez)
    | coe b =>
      cases z with
      | infty =>
        simp only [quad, lift_infty, lift_coe] at ex ey ez
        exact quad_eq_zero_aux' (fun h ↦ hxy (congrArg _ h)) (by simpa using ez)
          (by simpa using ex) (by simpa using ey)
      | coe c =>
        simp only [quad, lift_coe] at ex ey ez
        exact quad_eq_zero_aux (fun h ↦ hxy (congrArg _ h)) (fun h ↦ hxz (congrArg _ h))
          (fun h ↦ hyz (congrArg _ h)) (by simpa using ex) (by simpa using ey) (by simpa using ez)

omit [DecidableEq k] in
lemma br_mv_self (P : Matrix (Fin 2) (Fin 2) k) (v : k × k) :
    br (mv P v) v = quad (-P 1 0) (P 0 0 - P 1 1) (P 0 1) v := by
  simp only [br, mv, quad]; ring

/-- A Möbius map with three distinct fixed points is the identity (its matrix is scalar). -/
lemma scalar_of_three_fixed {P : Matrix (Fin 2) (Fin 2) k} (hP : P.det ≠ 0)
    {x y z : OnePoint k} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : mob P x = x)
    (hy : mob P y = y) (hz : mob P z = z) : P = P 0 0 • (1 : Matrix (Fin 2) (Fin 2) k) := by
  have key : ∀ w : OnePoint k, mob P w = w →
      quad (-P 1 0) (P 0 0 - P 1 1) (P 0 1) (lift w) = 0 := by
    intro w hw
    rw [← br_mv_self, ← proj_eq_proj_iff (mv_ne_zero hP (lift_ne_zero w)) (lift_ne_zero w),
      proj_lift]
    exact hw
  obtain ⟨h1, h2, h3⟩ := quad_eq_zero hxy hxz hyz (key x hx) (key y hy) (key z hz)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
      Matrix.one_apply_ne, mul_zero, one_ne_zero] <;>
    first | rfl | linear_combination h3 | linear_combination -h1 | linear_combination -h2


/-- Two Möbius maps agreeing at three distinct points agree everywhere. -/
lemma mob_eq_of_three {M N : Matrix (Fin 2) (Fin 2) k} (hM : M.det ≠ 0) (hN : N.det ≠ 0)
    {x y z : OnePoint k} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : mob M x = mob N x)
    (hy : mob M y = mob N y) (hz : mob M z = mob N z) (w : OnePoint k) : mob M w = mob N w := by
  set P := N.adjugate * M
  have hP : P.det ≠ 0 := by
    simp only [P, Matrix.det_mul, Matrix.det_adjugate]
    exact mul_ne_zero (by simpa using hN) hM
  have fix : ∀ u, mob M u = mob N u → mob P u = u := by
    intro u hu
    rw [mob_mul hM, hu, mob_adjugate_mul hN]
  have hs := scalar_of_three_fixed hP hxy hxz hyz (fix x hx) (fix y hy) (fix z hz)
  have h00 : P 0 0 ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hs; rw [hs, Matrix.det_zero] at hP
    exact hP rfl
  calc mob M w = mob (N * P) w := by
        rw [show N * P = N.det • M by simp only [P, ← Matrix.mul_assoc, Matrix.mul_adjugate,
          Matrix.smul_mul, Matrix.one_mul], mob_smul_matrix hN]
    _ = mob N (mob P w) := mob_mul hP w
    _ = mob N w := by rw [hs, mob_smul_matrix h00, mob_one]

/-- Triples of points of `ℙ¹`. -/
abbrev Triple (k : Type*) := OnePoint k × OnePoint k × OnePoint k

/-- Three pairwise distinct points. -/
def Distinct3 (t : OnePoint k × OnePoint k × OnePoint k) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

omit [DecidableEq k] in
/-- The Plücker identity `[u,v] w + [v,w] u + [w,u] v = 0` in `k²`. -/
lemma plucker (u v w : k × k) : br u v • w + br v w • u + br w u • v = 0 := by
  simp only [br, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.ext_iff, Prod.fst_add,
    Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
  constructor <;> ring

/-- The matrix sending `[0:1], [1:1], [1:0]` to multiples of `u₁, u₂, u₃`. -/
def triV (u₁ u₂ u₃ : k × k) : Matrix (Fin 2) (Fin 2) k :=
  !![br u₁ u₂ * u₃.1, br u₂ u₃ * u₁.1; br u₁ u₂ * u₃.2, br u₂ u₃ * u₁.2]

omit [DecidableEq k] in
lemma triV_smul (c₁ c₂ c₃ : k) (u₁ u₂ u₃ : k × k) :
    triV (c₁ • u₁) (c₂ • u₂) (c₃ • u₃) = (c₁ * c₂ * c₃) • triV u₁ u₂ u₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triV, br] <;> ring

/-- The matrix of the Möbius map sending `0, 1, ∞` to `t₁, t₂, t₃`. -/
def tri (t : OnePoint k × OnePoint k × OnePoint k) : Matrix (Fin 2) (Fin 2) k :=
  triV (lift t.1) (lift t.2.1) (lift t.2.2)

omit [DecidableEq k] in
lemma det_tri (t : OnePoint k × OnePoint k × OnePoint k) :
    (tri t).det = br (lift t.1) (lift t.2.1) * br (lift t.2.1) (lift t.2.2) *
      br (lift t.2.2) (lift t.1) := by
  simp only [tri, triV, Matrix.det_fin_two_of, br]; ring

omit [DecidableEq k] in
lemma det_tri_ne_zero {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    (tri t).det ≠ 0 := by
  classical
  rw [det_tri]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> rw [Ne, br_lift_eq_zero_iff]
  exacts [ht.1, ht.2.2, fun h ↦ ht.2.1 h.symm]

lemma mob_tri_zero {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    mob (tri t) ((0 : k) : OnePoint k) = t.1 := by
  have hb : br (lift t.2.1) (lift t.2.2) ≠ 0 := by rw [Ne, br_lift_eq_zero_iff]; exact ht.2.2
  have : mv (tri t) (lift ((0 : k) : OnePoint k)) = br (lift t.2.1) (lift t.2.2) • lift t.1 := by
    ext <;> simp [mv, tri, triV]
  rw [mob, this, proj_smul hb, proj_lift]

lemma mob_tri_infty {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    mob (tri t) ∞ = t.2.2 := by
  have hb : br (lift t.1) (lift t.2.1) ≠ 0 := by rw [Ne, br_lift_eq_zero_iff]; exact ht.1
  have : mv (tri t) (lift (∞ : OnePoint k)) = br (lift t.1) (lift t.2.1) • lift t.2.2 := by
    ext <;> simp [mv, tri, triV]
  rw [mob, this, proj_smul hb, proj_lift]

lemma mob_tri_one {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    mob (tri t) ((1 : k) : OnePoint k) = t.2.1 := by
  have hb : br (lift t.1) (lift t.2.2) ≠ 0 := by rw [Ne, br_lift_eq_zero_iff]; exact ht.2.1
  have hp := plucker (lift t.1) (lift t.2.1) (lift t.2.2)
  have : mv (tri t) (lift ((1 : k) : OnePoint k)) = br (lift t.1) (lift t.2.2) • lift t.2.1 := by
    have e := congrArg Prod.fst hp; have f := congrArg Prod.snd hp
    simp only [br, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_zero, Prod.snd_zero] at e f
    ext
    · simp only [mv, tri, triV, lift_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, br, Prod.smul_fst,
        smul_eq_mul]
      linear_combination e
    · simp only [mv, tri, triV, lift_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, br, Prod.smul_snd,
        smul_eq_mul]
      linear_combination f
  rw [mob, this, proj_smul hb, proj_lift]


/-- `GL(2, k)` acting on triples. -/
def smul3 (g : GL (Fin 2) k) (t : OnePoint k × OnePoint k × OnePoint k) :
    OnePoint k × OnePoint k × OnePoint k := (g • t.1, g • t.2.1, g • t.2.2)

lemma distinct3_smul3 (g : GL (Fin 2) k) {t : OnePoint k × OnePoint k × OnePoint k}
    (ht : Distinct3 t) : Distinct3 (smul3 g t) := by
  simp only [Distinct3, smul3, ne_eq, smul_left_cancel_iff]
  exact ht

lemma mob_adjugate_tri_fst {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    mob (tri t).adjugate t.1 = ((0 : k) : OnePoint k) := by
  conv_lhs => rw [← mob_tri_zero ht]
  exact mob_adjugate_mul (det_tri_ne_zero ht) _

lemma mob_adjugate_tri_snd {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    mob (tri t).adjugate t.2.1 = ((1 : k) : OnePoint k) := by
  conv_lhs => rw [← mob_tri_one ht]
  exact mob_adjugate_mul (det_tri_ne_zero ht) _

lemma mob_adjugate_tri_thd {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    mob (tri t).adjugate t.2.2 = ∞ := by
  conv_lhs => rw [← mob_tri_infty ht]
  exact mob_adjugate_mul (det_tri_ne_zero ht) _

omit [DecidableEq k] in
lemma det_adjugate_tri_ne_zero {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    (tri t).adjugate.det ≠ 0 := by
  classical
  rw [Matrix.det_adjugate]; simpa using det_tri_ne_zero ht

/-- **Sharp 3-transitivity.** A Möbius map is determined by the images of three distinct
points: `g x = h(g t) (h(t)⁻¹ x)`. -/
lemma smul_eq_mob_tri (g : GL (Fin 2) k) {t : OnePoint k × OnePoint k × OnePoint k}
    (ht : Distinct3 t) (x : OnePoint k) :
    g • x = mob (tri (smul3 g t)) (mob (tri t).adjugate x) := by
  have hgt := distinct3_smul3 g ht
  rw [gl_smul_eq_mob, ← mob_mul (det_adjugate_tri_ne_zero ht)]
  have hg : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := by
    exact g.det_ne_zero
  have hd : (tri (smul3 g t) * (tri t).adjugate).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero (det_tri_ne_zero hgt) (det_adjugate_tri_ne_zero ht)
  refine mob_eq_of_three hg hd ht.1 ht.2.1 ht.2.2 ?_ ?_ ?_ x
  · rw [mob_mul (det_adjugate_tri_ne_zero ht), mob_adjugate_tri_fst ht, mob_tri_zero hgt,
      ← gl_smul_eq_mob]; rfl
  · rw [mob_mul (det_adjugate_tri_ne_zero ht), mob_adjugate_tri_snd ht, mob_tri_one hgt,
      ← gl_smul_eq_mob]; rfl
  · rw [mob_mul (det_adjugate_tri_ne_zero ht), mob_adjugate_tri_thd ht, mob_tri_infty hgt,
      ← gl_smul_eq_mob]; rfl

/-- The relative position of `t'` with respect to `t`: `h(t)⁻¹ t'`. -/
def rel (t t' : OnePoint k × OnePoint k × OnePoint k) : OnePoint k × OnePoint k × OnePoint k :=
  (mob (tri t).adjugate t'.1, mob (tri t).adjugate t'.2.1, mob (tri t).adjugate t'.2.2)

lemma rel_smul3 (g : GL (Fin 2) k) {t : OnePoint k × OnePoint k × OnePoint k}
    (ht : Distinct3 t) (t' : OnePoint k × OnePoint k × OnePoint k) :
    rel (smul3 g t) (smul3 g t') = rel t t' := by
  have hgt := distinct3_smul3 g ht
  have e : ∀ y, mob (tri (smul3 g t)).adjugate (g • y) = mob (tri t).adjugate y := by
    intro y; rw [smul_eq_mob_tri g ht, mob_adjugate_mul (det_tri_ne_zero hgt)]
  simp only [rel]
  exact Prod.ext (e _) (Prod.ext (e _) (e _))


section topology

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

omit [DecidableEq k] in
/-- Points of large norm are close to `∞`. -/
lemma exists_norm_ge_mem {U : Set (OnePoint k)} (hU : U ∈ 𝓝 (∞ : OnePoint k)) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : k, R ≤ ‖a‖ → (a : OnePoint k) ∈ U := by
  have h1 : Tendsto ((↑) : k → OnePoint k) (Bornology.cobounded k) (𝓝 ∞) := by
    rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact]
    exact tendsto_coe_infty
  have h2 := h1 hU
  rw [Filter.mem_map, ← comap_norm_atTop, mem_comap] at h2
  obtain ⟨t, ht, hts⟩ := h2
  obtain ⟨R, hR⟩ := mem_atTop_sets.mp ht
  refine ⟨max R 1, by positivity, fun a ha ↦ hts (hR _ (le_trans (le_max_left _ _) ha))⟩

lemma continuousAt_proj {v : k × k} (hv : v ≠ 0) : ContinuousAt proj v := by
  by_cases h2 : v.2 = 0
  · have h1 : v.1 ≠ 0 := fun h1 ↦ hv (Prod.ext h1 h2)
    have hpv : proj v = ∞ := by simp [proj, h2]
    rw [ContinuousAt, hpv]
    intro U hU
    rw [Filter.mem_map]
    obtain ⟨R, hR, hRU⟩ := exists_norm_ge_mem hU
    have hm : 0 < ‖v.1‖ / 2 := by have := norm_pos_iff.mpr h1; positivity
    have e1 : ∀ᶠ w : k × k in 𝓝 v, ‖v.1‖ / 2 < ‖w.1‖ := by
      have := (continuous_norm.comp continuous_fst).continuousAt (x := v)
      exact this.eventually (lt_mem_nhds (show ‖v.1‖ / 2 < ‖v.1‖ by linarith))
    have e2 : ∀ᶠ w : k × k in 𝓝 v, ‖w.2‖ < ‖v.1‖ / 2 / R := by
      have := (continuous_norm.comp continuous_snd).continuousAt (x := v)
      exact this.eventually (gt_mem_nhds (by
        simp only [Function.comp_apply, h2, norm_zero]; positivity))
    filter_upwards [e1, e2] with w hw1 hw2
    simp only [mem_preimage, proj]
    split_ifs with hw
    · exact mem_of_mem_nhds hU
    · apply hRU
      rw [norm_div, le_div_iff₀ (norm_pos_iff.mpr hw)]
      have := (lt_div_iff₀ hR).mp hw2
      nlinarith [norm_nonneg w.2]
  · have hc : ContinuousAt (fun w : k × k ↦ ((w.1 / w.2 : k) : OnePoint k)) v :=
      continuous_coe.continuousAt.comp (continuousAt_fst.div continuousAt_snd h2)
    refine hc.congr ?_
    filter_upwards [(continuous_snd.continuousAt (x := v)).eventually_ne h2] with w hw
    simp [proj, hw]

/-- A second local coordinate vector, continuous near `∞`. -/
def secInf : OnePoint k → k × k
  | ∞ => (1, 0)
  | (a : k) => if a = 0 then (0, 1) else (1, a⁻¹)

omit [ProperSpace k] in
lemma secInf_eq (y : OnePoint k) : ∃ c : k, c ≠ 0 ∧ secInf y = c • lift y := by
  cases y with
  | infty => exact ⟨1, one_ne_zero, by simp [secInf]⟩
  | coe a =>
    by_cases ha : a = 0
    · exact ⟨1, one_ne_zero, by simp [secInf, ha]⟩
    · exact ⟨a⁻¹, inv_ne_zero ha, by simp [secInf, ha]⟩

omit [ProperSpace k] [DecidableEq k] in
lemma continuousAt_lift_coe (a : k) : ContinuousAt lift (a : OnePoint k) := by
  rw [← isOpenEmbedding_coe.continuousAt_iff]
  exact (continuous_id.prodMk continuous_const).continuousAt

lemma continuousAt_secInf : ContinuousAt secInf (∞ : OnePoint k) := by
  rw [continuousAt_infty', coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  have h0 : ∀ᶠ a : k in Bornology.cobounded k, a ≠ 0 := by
    have := (tendsto_norm_cobounded_atTop (E := k)).eventually_gt_atTop 0
    filter_upwards [this] with a ha using norm_pos_iff.mp ha
  have hlim : Tendsto (fun a : k ↦ ((1 : k), a⁻¹)) (Bornology.cobounded k) (𝓝 ((1 : k), (0 : k))) :=
    tendsto_const_nhds.prodMk_nhds Filter.tendsto_inv₀_cobounded
  refine hlim.congr' ?_
  filter_upwards [h0] with a ha
  simp [secInf, ha]

omit [DecidableEq k] in
/-- Every point has a coordinate vector depending continuously on the point nearby. -/
lemma exists_sec (x₀ : OnePoint k) : ∃ s : OnePoint k → k × k, ContinuousAt s x₀ ∧
    ∀ y, ∃ c : k, c ≠ 0 ∧ s y = c • lift y := by
  classical
  cases x₀ with
  | infty => exact ⟨secInf, continuousAt_secInf, secInf_eq⟩
  | coe a => exact ⟨lift, continuousAt_lift_coe a, fun y ↦ ⟨1, one_ne_zero, (one_smul _ _).symm⟩⟩


omit [ProperSpace k] in
lemma mob_eq_proj_of_sec {M : Matrix (Fin 2) (Fin 2) k} {x : OnePoint k} {v : k × k} {c : k}
    (hc : c ≠ 0) (hv : v = c • lift x) : mob M x = proj (mv M v) := by
  rw [hv, mv_smul, proj_smul hc, mob]

lemma continuousAt_mob_tri {t₀ : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t₀)
    (x₀ : OnePoint k) (adj : Bool) :
    ContinuousAt (fun p : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k ↦
      mob (if adj then (tri p.1).adjugate else tri p.1) p.2) (t₀, x₀) := by
  obtain ⟨s₁, hs₁, e₁⟩ := exists_sec t₀.1
  obtain ⟨s₂, hs₂, e₂⟩ := exists_sec t₀.2.1
  obtain ⟨s₃, hs₃, e₃⟩ := exists_sec t₀.2.2
  obtain ⟨s₀, hs₀, e₀⟩ := exists_sec x₀
  let T : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k → Matrix (Fin 2) (Fin 2) k :=
    fun p ↦ (if adj then (triV (s₁ p.1.1) (s₂ p.1.2.1) (s₃ p.1.2.2)).adjugate
      else triV (s₁ p.1.1) (s₂ p.1.2.1) (s₃ p.1.2.2))
  have key : ∀ p : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k,
      mob (if adj then (tri p.1).adjugate else tri p.1) p.2 = proj (mv (T p) (s₀ p.2)) := by
    intro p
    obtain ⟨c₁, hc₁, f₁⟩ := e₁ p.1.1
    obtain ⟨c₂, hc₂, f₂⟩ := e₂ p.1.2.1
    obtain ⟨c₃, hc₃, f₃⟩ := e₃ p.1.2.2
    obtain ⟨c₀, hc₀, f₀⟩ := e₀ p.2
    have hc : c₁ * c₂ * c₃ ≠ 0 := mul_ne_zero (mul_ne_zero hc₁ hc₂) hc₃
    simp only [T, f₁, f₂, f₃, triV_smul]
    rw [mob_eq_proj_of_sec hc₀ f₀]
    cases adj
    · simp only [Bool.false_eq_true, ↓reduceIte, tri]
      rw [show mv ((c₁ * c₂ * c₃) • triV (lift p.1.1) (lift p.1.2.1) (lift p.1.2.2)) (s₀ p.2)
        = (c₁ * c₂ * c₃) • mv (triV (lift p.1.1) (lift p.1.2.1) (lift p.1.2.2)) (s₀ p.2) by
          simp only [mv, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk.injEq]
          constructor <;> ring, proj_smul hc]
    · simp only [↓reduceIte, tri, Matrix.adjugate_smul, Fintype.card_fin]
      rw [show mv ((c₁ * c₂ * c₃) ^ (2 - 1) •
          (triV (lift p.1.1) (lift p.1.2.1) (lift p.1.2.2)).adjugate) (s₀ p.2)
        = (c₁ * c₂ * c₃) • mv (triV (lift p.1.1) (lift p.1.2.1) (lift p.1.2.2)).adjugate
          (s₀ p.2) by
          simp only [mv, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk.injEq]
          constructor <;> ring, proj_smul hc]
  simp_rw [key]
  have h1 : ContinuousAt (fun p : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k ↦
      s₁ p.1.1) (t₀, x₀) := hs₁.comp_of_eq (by fun_prop) rfl
  have h2 : ContinuousAt (fun p : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k ↦
      s₂ p.1.2.1) (t₀, x₀) := hs₂.comp_of_eq (by fun_prop) rfl
  have h3 : ContinuousAt (fun p : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k ↦
      s₃ p.1.2.2) (t₀, x₀) := hs₃.comp_of_eq (by fun_prop) rfl
  have h0 : ContinuousAt (fun p : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k ↦
      s₀ p.2) (t₀, x₀) := hs₀.comp_of_eq (by fun_prop) rfl
  have hne : mv (T (t₀, x₀)) (s₀ x₀) ≠ 0 := by
    obtain ⟨c₁, hc₁, f₁⟩ := e₁ t₀.1
    obtain ⟨c₂, hc₂, f₂⟩ := e₂ t₀.2.1
    obtain ⟨c₃, hc₃, f₃⟩ := e₃ t₀.2.2
    obtain ⟨c₀, hc₀, f₀⟩ := e₀ x₀
    have hc : c₁ * c₂ * c₃ ≠ 0 := mul_ne_zero (mul_ne_zero hc₁ hc₂) hc₃
    have hdet : (triV (s₁ t₀.1) (s₂ t₀.2.1) (s₃ t₀.2.2)).det ≠ 0 := by
      rw [f₁, f₂, f₃, triV_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hc) (det_tri_ne_zero ht)
    refine mv_ne_zero ?_ (by rw [f₀]; exact smul_ne_zero hc₀ (lift_ne_zero x₀))
    cases adj
    · exact hdet
    · simpa [T, Matrix.det_adjugate] using hdet
  refine (continuousAt_proj hne).comp_of_eq ?_ rfl
  cases adj
  · simp only [T, mv, triV, br, Bool.false_eq_true, ↓reduceIte, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    fun_prop
  · simp only [T, mv, triV, br, ↓reduceIte, Matrix.adjugate_fin_two_of, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    fun_prop

/-- `(t, x) ↦ h(t) x`. -/
def mobTri (q : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k) : OnePoint k :=
  mob (tri q.1) q.2

/-- `(t, x) ↦ h(t)⁻¹ x`. -/
def mobAdj (q : (OnePoint k × OnePoint k × OnePoint k) × OnePoint k) : OnePoint k :=
  mob (tri q.1).adjugate q.2

lemma continuousAt_mobTri {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t)
    (x : OnePoint k) : ContinuousAt mobTri (t, x) := by
  have h := continuousAt_mob_tri ht x false
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact h

lemma continuousAt_mobAdj {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t)
    (x : OnePoint k) : ContinuousAt mobAdj (t, x) := by
  have h := continuousAt_mob_tri ht x true
  simp only [↓reduceIte] at h
  exact h

lemma continuous_mob_tri {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    Continuous (mob (tri t)) :=
  continuous_iff_continuousAt.2 fun x ↦
    (continuousAt_mobTri ht x).comp (Continuous.prodMk_right t).continuousAt

lemma continuous_mob_adjugate_tri {t : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    Continuous (mob (tri t).adjugate) :=
  continuous_iff_continuousAt.2 fun x ↦
    (continuousAt_mobAdj ht x).comp (Continuous.prodMk_right t).continuousAt

/-- `GL(2, k)` acts by homeomorphisms. -/
lemma continuous_gl_smul (g : GL (Fin 2) k) : Continuous fun x : OnePoint k ↦ g • x := by
  have ht : Distinct3 (((0 : k) : OnePoint k), ((1 : k) : OnePoint k), (∞ : OnePoint k)) :=
    ⟨by simp, by simp, by simp⟩
  simp_rw [smul_eq_mob_tri g ht]
  exact (continuous_mob_tri (distinct3_smul3 g ht)).comp (continuous_mob_adjugate_tri ht)

omit [ProperSpace k] in
lemma rel_eq (t t' : OnePoint k × OnePoint k × OnePoint k) :
    rel t t' = (mobAdj (t, t'.1), mobAdj (t, t'.2.1), mobAdj (t, t'.2.2)) := rfl

lemma continuousAt_rel {t t' : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) :
    ContinuousAt (fun p : (OnePoint k × OnePoint k × OnePoint k) ×
      (OnePoint k × OnePoint k × OnePoint k) ↦ rel p.1 p.2) (t, t') := by
  simp_rw [rel_eq]
  refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_)
  · exact (continuousAt_mobAdj ht t'.1).comp (x := (t, t'))
      (f := fun p : Triple k × Triple k ↦ (p.1, p.2.1)) (by fun_prop)
  · exact (continuousAt_mobAdj ht t'.2.1).comp (x := (t, t'))
      (f := fun p : Triple k × Triple k ↦ (p.1, p.2.2.1)) (by fun_prop)
  · exact (continuousAt_mobAdj ht t'.2.2).comp (x := (t, t'))
      (f := fun p : Triple k × Triple k ↦ (p.1, p.2.2.2)) (by fun_prop)

end topology

end OnePoint.Proj
