/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Takeuchi

/-!
# Cores of Fuchsian groups, and [CanLift] Prop. 2.7 at the level of groups

For a Fuchsian group `Γ ⊆ SL(2, ℝ)` uniformising a hyperbolic curve `X = Γ \ ℍ`, the curve admits
a (hyperbolic) core iff `Γ` has finite index in its commensurator `Comm(Γ)`. The core is then
`[Comm(Γ) \ ℍ]` ([Corr] §3, [CanLift] Rem. 2.1.2). This file:

* defines `OrbicurveCores.AdmitsCore Γ :⇔ [Comm(Γ) : Γ] < ∞`;
* proves that **arithmetic groups admit no core** (`IsArithmeticSL.not_admitsCore`). If
  `Γ` is conjugate to a group commensurable with `SL(2, ℤ)`, then `Comm(Γ)` contains a conjugate of
  `diag(√2, 1/√2)`, and no positive power of it lies in `Γ` because its squared trace
  `2ⁿ + 2 + 2⁻ⁿ` is not an integer (`IsArithmeticSL.sq_tr_int`);
* states **Margulis' commensurator theorem** in the special case needed (`MargulisOneInfty`):
  a `(1;∞)`-group with infinite index in its commensurator is arithmetic. This is
  [Marg] Ch. IX Thm. (B) (with [Corr] Thm. 2.5) restricted to once-punctured torus groups. It is
  **not** proved here (see `Blueprint.md`, items M1–M2);
* assembles the group-theoretic form of [CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1
  (`canLift27_group`): assuming `MargulisOneInfty`, a `(1;∞)`-group without core has, up to Nielsen
  equivalence, one of Takeuchi's four trace triples.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores

/-- A subgroup `Γ` *admits a core* if it has finite index in its commensurator. For a Fuchsian
group `Γ ⊆ SL(2, ℝ)` this is equivalent to the existence of a hyperbolic core of `Γ \ ℍ`
([Corr] §3, [CanLift] Rem. 2.1.2); the core is `[Comm(Γ) \ ℍ]`. -/
def AdmitsCore {G : Type*} [Group G] (Γ : Subgroup G) : Prop :=
  Γ.relIndex (commensurator Γ) ≠ 0

/-- If `Γ` admits a core, then every element of the commensurator has a positive power in `Γ`. -/
lemma AdmitsCore.exists_pow_mem {G : Type*} [Group G] {Γ : Subgroup G} (h : AdmitsCore Γ)
    {σ : G} (hσ : σ ∈ commensurator Γ) : ∃ n : ℕ, 0 < n ∧ σ ^ n ∈ Γ := by
  obtain ⟨n, hn, -, hmem⟩ := exists_pow_mem_of_relIndex_ne_zero h hσ
  exact ⟨n, hn, hmem.1⟩

section conj

variable {G H : Type*} [Group G] [Group H]

/-- Conjugation commutes with taking images. -/
lemma map_conjAct_smul (f : G →* H) (x : G) (K : Subgroup G) :
    (ConjAct.toConjAct x • K).map f = ConjAct.toConjAct (f x) • K.map f := by
  ext y
  simp only [mem_map, mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x⁻¹ * z * x, hz, by simp [mul_assoc]⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨x * z * x⁻¹, by simpa [mul_assoc] using hz, ?_⟩
    rw [map_mul, map_mul, hzy, map_inv]
    group

/-- Commensurators are transported along injective homomorphisms. -/
lemma mem_commensurator_map_iff {f : G →* H} (hf : Function.Injective f) {x : G}
    {K : Subgroup G} : f x ∈ commensurator (K.map f) ↔ x ∈ commensurator K := by
  simp only [Commensurable.commensurator_mem_iff, Commensurable, ← map_conjAct_smul,
    relIndex_map_map_of_injective _ _ hf]

end conj

/-- Two elements of `GL(2, ℝ)` differing by a nonzero scalar act identically by conjugation. -/
lemma conjAct_smul_eq_of_scalar {a b : GL (Fin 2) ℝ} {c : ℝ} (hc : c ≠ 0)
    (hab : (a : Matrix (Fin 2) (Fin 2) ℝ) = c • (b : Matrix (Fin 2) (Fin 2) ℝ))
    (K : Subgroup (GL (Fin 2) ℝ)) :
    ConjAct.toConjAct a • K = ConjAct.toConjAct b • K := by
  have hinv : ((a⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      c⁻¹ • ((b⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    have h1 : (a : Matrix (Fin 2) (Fin 2) ℝ) * (c⁻¹ • ((b⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)) = 1 := by
      rw [hab, smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    calc ((a⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = ((a⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (a * (c⁻¹ •
          ((b⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  ext y
  simp only [mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv]
  have : a⁻¹ * y * a = b⁻¹ * y * b := by
    ext1
    simp only [Units.val_mul, hinv, hab, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc, one_smul]
  rw [this]

/-- The rational matrix `diag(2, 1)`. -/
noncomputable def diagTwo : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, 0; 0, 1] (by simp [det_fin_two])

lemma diagTwo_map_coe :
    ((diagTwo.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![2, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTwo, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The squared trace `2ⁿ + 2 + 2⁻ⁿ` is not an integer for `n ≥ 1`. -/
lemma not_int_two_pow {n : ℕ} (hn : 0 < n) (m : ℤ) :
    ((2 : ℝ) ^ n + 1) ^ 2 / 2 ^ n ≠ m := by
  intro h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hsplit : ((2 : ℝ) ^ n + 1) ^ 2 / 2 ^ n = 2 ^ n + 2 + 1 / 2 ^ n := by
    field_simp
    ring
  rw [hsplit] at h
  have hlt : (1 : ℝ) / 2 ^ n < 1 := by
    rw [div_lt_one h2]
    exact one_lt_pow₀ (by norm_num) hn.ne'
  have hpos : (0 : ℝ) < 1 / 2 ^ n := by positivity
  -- `1 / 2ⁿ = m - 2ⁿ - 2` is an integer strictly between `0` and `1`
  have hk : (1 : ℝ) / 2 ^ n = ((m - 2 ^ n - 2 : ℤ) : ℝ) := by push_cast; linarith
  rw [hk] at hlt hpos
  have h1 : (0 : ℤ) < m - 2 ^ n - 2 := by exact_mod_cast hpos
  have h2' : m - 2 ^ n - 2 < (1 : ℤ) := by exact_mod_cast hlt
  lia

/-- **Arithmetic groups admit no core**: an arithmetic `Γ ⊆ SL(2, ℝ)` has infinite index in its
commensurator. -/
theorem IsArithmeticSL.not_admitsCore {Γ : Subgroup SL(2, ℝ)} (hΓ : IsArithmeticSL Γ) :
    ¬ AdmitsCore Γ := by
  intro hcore
  obtain ⟨g, hΓ'⟩ := id hΓ
  set ΓGL := Γ.map toGL
  set Γ' := ConjAct.toConjAct g • ΓGL
  set r : GL (Fin 2) ℝ := diagTwo.map (Rat.castHom ℝ)
  set s : GL (Fin 2) ℝ := g⁻¹ * r * g with hs
  -- `r` commensurates `Γ'`
  have hr : Commensurable (ConjAct.toConjAct r • Γ') Γ' :=
    (Subgroup.IsArithmetic.conj (𝒢 := Γ') diagTwo).is_commensurable.trans
      hΓ'.is_commensurable.symm
  -- `s = g⁻¹ r g` commensurates `Γ.map toGL`
  have hsC : Commensurable (ConjAct.toConjAct s • ΓGL) ΓGL := by
    rw [Commensurable.commensurable_conj (ConjAct.toConjAct g)]
    have e : ConjAct.toConjAct g • ConjAct.toConjAct s • ΓGL = ConjAct.toConjAct r • Γ' := by
      simp only [Γ', ← mul_smul, ← map_mul, hs]
      congr 2
      group
    rw [e]
    exact hr
  -- the element `σ = s / √2 ∈ SL(2, ℝ)`
  set c : ℝ := (Real.sqrt 2)⁻¹ with hc
  have hc0 : c ≠ 0 := by positivity
  have hc2 : c ^ 2 = 1 / 2 := by
    rw [hc, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hdets : det (s : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
    simp only [hs, Units.val_mul, det_mul, r, diagTwo_map_coe]
    rw [mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      det_one, one_mul]
    simp [det_fin_two]
  let σ : SL(2, ℝ) := ⟨c • (s : Matrix (Fin 2) (Fin 2) ℝ), by
    rw [det_smul, hdets, Fintype.card_fin, hc2]; norm_num⟩
  have hσs : ((toGL σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      c • (s : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  have hσC : σ ∈ commensurator Γ := by
    rw [← mem_commensurator_map_iff (f := toGL) toGL_injective,
      Commensurable.commensurator_mem_iff, conjAct_smul_eq_of_scalar hc0 hσs]
    exact hsC
  -- no positive power of `σ` lies in `Γ`
  obtain ⟨n, hn, hσn⟩ := hcore.exists_pow_mem hσC
  obtain ⟨m, hm⟩ := hΓ.sq_tr_int hσn
  have htr : tr (σ ^ n) = c ^ n * (2 ^ n + 1) := by
    set h : Matrix (Fin 2) (Fin 2) ℝ := ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    set G : Matrix (Fin 2) (Fin 2) ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ)
    have hGh : G * h = 1 := by simp [G, h]
    have hhG : h * G = 1 := by simp [G, h]
    have e : ∀ k : ℕ, ((σ ^ k : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        c ^ k • (h * !![2 ^ k, 0; 0, 1] * G) := by
      intro k
      induction k with
      | zero =>
        rw [pow_zero, Matrix.SpecialLinearGroup.coe_one, pow_zero, one_smul]
        rw [show (!![(2 : ℝ) ^ 0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 1 by
          rw [pow_zero, Matrix.one_fin_two], mul_one, hhG]
      | succ k ih =>
        rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
        change _ * (c • (s : Matrix (Fin 2) (Fin 2) ℝ)) = _
        have hs' : (s : Matrix (Fin 2) (Fin 2) ℝ) = h * !![2, 0; 0, 1] * G := by
          simp only [hs, Units.val_mul, r, diagTwo_map_coe, h, G]
        rw [hs', smul_mul_smul_comm, pow_succ]
        congr 1
        have hD : (!![(2 : ℝ) ^ k, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![2, 0; 0, 1] =
            !![2 ^ (k + 1), 0; 0, 1] := by
          rw [Matrix.mul_fin_two]; simp [pow_succ]
        rw [← hD]
        simp only [mul_assoc]
        rw [← mul_assoc G h, hGh, one_mul]
    rw [tr, e n, trace_smul, trace_mul_cycle, hGh, one_mul]
    simp [trace_fin_two]
  have : tr (σ ^ n) ^ 2 = ((2 : ℝ) ^ n + 1) ^ 2 / 2 ^ n := by
    rw [htr, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, hc2]
    rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]
  exact not_int_two_pow hn m (this ▸ hm)

/-- **Margulis' commensurator theorem for once-punctured torus groups** (statement only).
If `A, B ∈ SL(2, ℝ)` with `tr [A, B] = -2` and `tr A ≠ 0` (so `⟨A, B⟩` is a Fuchsian group of
signature `(1;∞)`: Fricke, see Goldman, *Geom. Topol.* 7 (2003)) and `⟨A, B⟩` has infinite index in
its commensurator, then `⟨A, B⟩` is arithmetic.

This is [Marg] Ch. IX Thm. (B) (see also [Zim] Thm. 6.2.5 and [Corr] Thm. 2.5), combined with
the fact that a non-cocompact arithmetic Fuchsian group is commensurable with a conjugate of
`SL(2, ℤ)`. It is **not proved** in this repository; it is the input M1+M2 of `Blueprint.md`. -/
def MargulisOneInfty : Prop :=
  ∀ A B : SL(2, ℝ), tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 →
    ¬ AdmitsCore (Subgroup.closure {A, B}) → IsArithmeticSL (Subgroup.closure {A, B})

/-- Modulo Margulis, a `(1;∞)`-group admits a core iff it is not arithmetic. The implication
"arithmetic ⇒ no core" is unconditional (`IsArithmeticSL.not_admitsCore`). -/
theorem admitsCore_iff_not_isArithmeticSL (hM : MargulisOneInfty) {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0) :
    AdmitsCore (Subgroup.closure {A, B}) ↔ ¬ IsArithmeticSL (Subgroup.closure {A, B}) :=
  ⟨fun hc ha ↦ ha.not_admitsCore hc, fun ha ↦ by_contra fun hc ↦ ha (hM A B hcomm hA hc)⟩

/-- **[CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1, group-theoretic form, conditional on
Margulis.** A `(1;∞)`-group `⟨A, B⟩ ⊆ SL(2, ℝ)` which does not admit a core is generated by a
Nielsen-equivalent pair `(A', B')` whose squared trace triple is one of Takeuchi's four:
`(9,9,9)`, `(8,8,16)`, `(5,20,25)`, `(6,12,18)`. These are the groups uniformising the
once-punctured elliptic curves with `j = 0`, `1728`, `2¹⁴·31³/5³`, `2²·73³/3⁴` respectively
([Sijs] Tables 1 and 4). -/
theorem canLift27_group (hM : MargulisOneInfty) {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0)
    (hno : ¬ AdmitsCore (Subgroup.closure {A, B})) :
    ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
      TakeuchiSq (tr A') (tr B') (tr (A' * B')) :=
  takeuchi_one_infty hcomm (hM A B hcomm hA hno)

end OrbicurveCores
