/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.CuspStructure
import OrbicurveCores.M2.Final

/-!
# R3b–R3c: reduction of `CommIndexFour` to the translation case

Let `Γ₀ = ⟨A₀, B₀⟩` be a once-punctured torus group in Fricke normal form (with the triangle
inequalities) which admits a core, and `Δ = Comm(Γ₀)`. Write `N = [Δ : Γ₀]!`, so that `δ ^ N ∈ Γ₀`
for every `δ ∈ Δ` (`pow_factorial_relIndex_mem`).

* For `δ ∈ Δ`, `δ u_{4N} δ⁻¹ = (δ u₄ δ⁻¹) ^ N ∈ Γ₀`, so by the one-cusp lemma
  (`exists_mem_lowerLeft_eq_zero`) some `γ δ` (`γ ∈ Γ₀`) is upper triangular.
* Upper triangular elements `u ∈ Δ` are `±uU s`: `u ^ N ∈ Γ₀` has diagonal `±1`
  (`upper_mem_commensurator`).
* The translations `{s | uU s ∈ Δ}` form a discrete subgroup of `ℝ` (if `uU s ∈ Δ` then
  `uU (N s) ∈ Γ₀`) containing `1` (`uU_one_mem_nHemi`), hence equal `(1/m) ℤ`, `m ≥ 1`
  (`exists_transl_commensurator`).
* If `m = 1`, then `Δ ≤ Γ⁺ = nHemi`, so `[Δ : Γ₀] = 4`; otherwise `uU (1/m) ∈ Δ` with `m ≥ 2`
  (`relIndex_commensurator_normal_or`).

The remaining case is `TranslationCase` (R3d, proved in `Genuine/TranslationCase.lean`).
Finally the index `[Comm(Γ) : Γ]` is transported from the normal form to arbitrary once-punctured
torus groups: it is invariant under
`GL(2, ℝ)`-conjugation (`relIndex_commensurator_map`) and under sign changes of the generators
(`relIndex_commensurator_signs`; both groups miss `-1` by freeness of the normal form).

Main result: `commIndexFour_of_translationCase : TranslationCase → CommIndexFour`.
-/

open Matrix UpperHalfPlane
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace OrbicurveCores.Fuchsian

/-- If `[K : H] ≠ 0`, then `a ^ [K : H]! ∈ H` for all `a ∈ K`. -/
lemma pow_factorial_relIndex_mem {G : Type*} [Group G] {H K : Subgroup G}
    (h : H.relIndex K ≠ 0) {a : G} (ha : a ∈ K) : a ^ (H.relIndex K).factorial ∈ H := by
  obtain ⟨n, hn, hle, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h ha
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hn hle
  rw [hk, pow_mul]; exact pow_mem hmem.1 k

section normal

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

include hx hy in
/-- Upper triangular elements of `Comm(Γ₀)` are `±` translations. -/
lemma upper_mem_commensurator (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel}))
    {u : SL(2, ℝ)} (hu : u ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}))
    (hu10 : u 1 0 = 0) : ∃ s, u = SL2R.uU s ∨ u = -SL2R.uU s := by
  haveI := discreteTopology_normal hx hy hz hrel
  set N := ((Subgroup.closure {nA hz hrel, nB hz hrel}).relIndex
    (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}))).factorial
  have hN : 0 < N := Nat.factorial_pos _
  have hmem := pow_factorial_relIndex_mem hcore hu
  have hD := lowerRight_eq_one_or_neg_one (by norm_num : (4 : ℝ) ≠ 0) (uU_four_mem hz hrel) hmem
    (upper_pow hu10 N).1
  rw [(upper_pow hu10 N).2] at hD
  have habs : |u 1 1| = 1 := by
    have : |u 1 1| ^ N = 1 := by
      rw [← abs_pow]; rcases hD with h | h <;> simp [h]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hN.ne').mp this
  have hdet := det_upper hu10
  rcases (abs_eq zero_le_one).mp habs with h | h
  · refine ⟨u 0 1, Or.inl ?_⟩
    have h00 : u 0 0 = 1 := by rw [h] at hdet; linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h, hu10]
  · refine ⟨-u 0 1, Or.inr ?_⟩
    have h00 : u 0 0 = -1 := by rw [h] at hdet; linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h, hu10]

include hx hy in
/-- Every `δ ∈ Comm(Γ₀)` is, up to `Γ₀` on the left, `± uU s` with `uU s ∈ Comm(Γ₀)`. -/
lemma exists_mul_eq_uU (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})) {δ : SL(2, ℝ)}
    (hδ : δ ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) :
    ∃ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}, ∃ s,
      SL2R.uU s ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) ∧
        (γ * δ = SL2R.uU s ∨ γ * δ = -SL2R.uU s) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  set N := (Γ.relIndex (commensurator Γ)).factorial
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos _
  have hu4 : SL2R.uU 4 ∈ commensurator Γ := le_commensurator _ (uU_four_mem hz hrel)
  have hc : δ * SL2R.uU (N * 4) * δ⁻¹ ∈ Γ := by
    have := pow_factorial_relIndex_mem hcore (mul_mem (mul_mem hδ hu4) (inv_mem hδ))
    rwa [conj_pow, uU_pow_eq] at this
  obtain ⟨γ, hγ, h0⟩ := exists_mem_lowerLeft_eq_zero hx hy hz hrel h1 h2 h3
    (by positivity : (N : ℝ) * 4 ≠ 0) hc
  have hγδ : γ * δ ∈ commensurator Γ := mul_mem (le_commensurator _ hγ) hδ
  obtain ⟨s, hs⟩ := upper_mem_commensurator hx hy hz hrel hcore hγδ h0
  refine ⟨γ, hγ, s, ?_, hs⟩
  rcases hs with hs | hs
  · rwa [← hs]
  · have := mul_mem hγδ (neg_one_mem_commensurator' Γ)
    rw [hs] at this
    simpa using this

include hx hy in
/-- The translations in `Comm(Γ₀)` are `(1/m) ℤ` for some `m ≥ 1`. -/
lemma exists_transl_commensurator
    (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})) :
    ∃ m : ℕ, 0 < m ∧ transl (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) =
      AddSubgroup.zmultiples (1 / (m : ℝ)) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  haveI := discreteTopology_normal hx hy hz hrel
  obtain ⟨ε, hε, hb⟩ := exists_transl_bound Γ
  set N := (Γ.relIndex (commensurator Γ)).factorial
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos _
  have h1 : (1 : ℝ) ∈ transl (commensurator Γ) :=
    nHemi_le_commensurator hz hrel (uU_one_mem_nHemi hz hrel)
  rcases (transl (commensurator Γ)).dense_or_cyclic with hd | ⟨a, ha⟩
  · exfalso
    obtain ⟨s, hs, hs0, hsε⟩ := hd.exists_between (show (0 : ℝ) < ε / N by positivity)
    have hmem : SL2R.uU (N * s) ∈ Γ := by
      rw [← uU_pow_eq]; exact pow_factorial_relIndex_mem hcore hs
    rw [lt_div_iff₀ hN] at hsε
    have := hb _ hmem (by rw [abs_of_pos (by positivity)]; linarith)
    exact (mul_pos hN hs0).ne' this
  · rw [← AddSubgroup.zmultiples_eq_closure] at ha
    rw [ha] at h1 ⊢
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp h1
    have hja : (j : ℝ) * a = 1 := by simpa [zsmul_eq_mul] using hj
    have hj0 : j ≠ 0 := by rintro rfl; simp at hja
    refine ⟨j.natAbs, Int.natAbs_pos.mpr hj0, ?_⟩
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj0
    have ha' : a = 1 / j := by field_simp; linarith
    rcases le_or_gt 0 j with hpos | hneg
    · have : ((j.natAbs : ℕ) : ℝ) = j := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hpos)]
      rw [this, ha']
    · have : ((j.natAbs : ℕ) : ℝ) = -j := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
      rw [this, ha', ← AddSubgroup.zmultiples_neg]
      congr 1; ring

include hx hy in
/-- **R3c (normal form).** If `Γ₀` admits a core, then either `[Comm(Γ₀) : Γ₀] = 4`, or
`Comm(Γ₀)` contains the translation `z ↦ z + 1/m` for some `m ≥ 2`. -/
theorem relIndex_commensurator_normal_or (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (hcore : AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})) :
    (Subgroup.closure {nA hz hrel, nB hz hrel}).relIndex
        (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) = 4 ∨
      ∃ m : ℕ, 2 ≤ m ∧
        SL2R.uU (1 / m) ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  obtain ⟨m, hm, hS⟩ := exists_transl_commensurator hx hy hz hrel hcore
  by_cases hm1 : m = 1
  · left
    subst hm1
    have hle : commensurator Γ ≤ nHemi hz hrel := by
      intro δ hδ
      obtain ⟨γ, hγ, s, hs, hγδ⟩ := exists_mul_eq_uU hx hy hz hrel h1 h2 h3 hcore hδ
      have hsZ : s ∈ AddSubgroup.zmultiples (1 / ((1 : ℕ) : ℝ)) := hS ▸ hs
      have hsH : SL2R.uU s ∈ nHemi hz hrel := by
        have hZ : AddSubgroup.zmultiples (1 / ((1 : ℕ) : ℝ)) ≤ transl (nHemi hz hrel) := by
          rw [AddSubgroup.zmultiples_le]
          simpa [mem_transl] using uU_one_mem_nHemi hz hrel
        exact hZ hsZ
      have hγδ' : γ * δ ∈ nHemi hz hrel := by
        rcases hγδ with e | e
        · rw [e]; exact hsH
        · rw [e]; simpa using mul_mem (neg_one_mem_nHemi hz hrel) hsH
      simpa using mul_mem (inv_mem (le_nHemi hz hrel hγ)) hγδ'
    have : commensurator Γ = nHemi hz hrel := le_antisymm hle (nHemi_le_commensurator hz hrel)
    rw [this]; exact relIndex_nHemi hx hy hz hrel
  · right
    refine ⟨m, by omega, ?_⟩
    have : (1 / (m : ℝ)) ∈ transl (commensurator Γ) := by
      rw [hS]; exact AddSubgroup.mem_zmultiples _
    exact this

end normal

/-! ### Transport: signs and conjugation -/

section transport

lemma range_lift_pair (A B : SL(2, ℝ)) :
    (FreeGroup.lift ![A, B]).range = Subgroup.closure {A, B} := by
  rw [FreeGroup.range_lift_eq_closure]
  congr 1
  ext g
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma pm_bot_comm {g : SL(2, ℝ)} (hg : g ∈ pmGroup ⊥) (h : SL(2, ℝ)) : g * h = h * g := by
  rcases hg with hg | hg
  · rw [Subgroup.mem_bot] at hg; rw [hg, one_mul, mul_one]
  · rw [Subgroup.mem_bot] at hg; rw [← neg_neg g, hg]; simp

lemma neg_one_ne_one_SL : (-1 : SL(2, ℝ)) ≠ 1 := fun h ↦ by
  have := congrArg (fun g : SL(2, ℝ) ↦ g 0 0) h
  norm_num at this

lemma mem_pmGroup_bot_of_signs {A A' : SL(2, ℝ)} (hA : A' ∈ ({A, -A} : Set SL(2, ℝ))) :
    A' * A⁻¹ ∈ pmGroup ⊥ := by
  rcases hA with rfl | rfl
  · left; simp
  · right; simp

/-- Changing the signs of a free basis of a group missing `-1` does not create `-1`. -/
lemma neg_one_notMem_signs {A B A' B' : SL(2, ℝ)} (hA : A' ∈ ({A, -A} : Set SL(2, ℝ)))
    (hB : B' ∈ ({B, -B} : Set SL(2, ℝ))) (hinj : Function.Injective (FreeGroup.lift ![A, B]))
    (hneg : (-1 : SL(2, ℝ)) ∉ Subgroup.closure {A, B}) :
    (-1 : SL(2, ℝ)) ∉ Subgroup.closure {A', B'} := by
  set χ := FreeGroup.lift ![A' * A⁻¹, B' * B⁻¹]
  have hχ : ∀ w, χ w ∈ pmGroup ⊥ := by
    intro w
    have : χ w ∈ χ.range := ⟨w, rfl⟩
    rw [range_lift_pair] at this
    refine (Subgroup.closure_le _).mpr ?_ this
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mem_pmGroup_bot_of_signs hA, mem_pmGroup_bot_of_signs hB⟩
  have key : ∀ w, FreeGroup.lift ![A', B'] w = χ w * FreeGroup.lift ![A, B] w := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of i => fin_cases i <;> simp [χ]
    | inv_of i ih =>
      rw [map_inv, map_inv, map_inv, ih, _root_.mul_inv_rev,
        pm_bot_comm (inv_mem (hχ (FreeGroup.of i)))]
    | mul a b ha hb =>
      rw [map_mul, map_mul, map_mul, ha, hb, mul_assoc, ← mul_assoc _ (χ b),
        ← pm_bot_comm (hχ b)]
      simp only [mul_assoc]
  intro hmem
  rw [← range_lift_pair] at hmem
  obtain ⟨w, hw⟩ := hmem
  rw [key] at hw
  rcases hχ w with h | h
  · rw [Subgroup.mem_bot] at h
    rw [h, one_mul] at hw
    exact hneg (by rw [← range_lift_pair]; exact ⟨w, hw⟩)
  · rw [Subgroup.mem_bot] at h
    have hc : χ w = -1 := by rw [← neg_neg (χ w), h]
    rw [hc] at hw
    have h1 : FreeGroup.lift ![A, B] w = 1 := by
      have := congrArg Neg.neg hw
      simpa using this
    have hw1 : w = 1 := hinj (by rw [h1, map_one])
    rw [hw1, map_one] at hc
    exact neg_one_ne_one_SL hc.symm

lemma relIndex_pmGroup_eq_two {Γ : Subgroup SL(2, ℝ)} (h1 : (-1 : SL(2, ℝ)) ∉ Γ) :
    Γ.relIndex (pmGroup Γ) = 2 := by
  refine relIndex_eq_two (a := -1) (neg_one_mem_pmGroup _) fun b hb ↦ ?_
  rw [mul_neg_one]
  rcases hb with hb | hb
  · refine Or.inr ⟨hb, fun h ↦ h1 ?_⟩
    simpa using mul_mem (inv_mem hb) h
  · refine Or.inl ⟨hb, fun h ↦ h1 ?_⟩
    simpa using mul_mem (inv_mem h) hb

lemma pmGroup_le_commensurator (Γ : Subgroup SL(2, ℝ)) : pmGroup Γ ≤ commensurator Γ := by
  rintro g (h | h)
  · exact le_commensurator _ h
  · simpa using mul_mem (le_commensurator _ h) (neg_one_mem_commensurator' Γ)

lemma commensurable_pmGroup {Γ : Subgroup SL(2, ℝ)} (h : (-1 : SL(2, ℝ)) ∉ Γ) :
    Subgroup.Commensurable Γ (pmGroup Γ) :=
  ⟨by rw [relIndex_pmGroup_eq_two h]; norm_num,
    by rw [Subgroup.relIndex_eq_one.mpr (le_pmGroup Γ)]; norm_num⟩

/-- Two groups missing `-1` with the same `±`-group have the same commensurator index. -/
lemma relIndex_commensurator_eq_of_pm {Γ Γ' : Subgroup SL(2, ℝ)}
    (h : (-1 : SL(2, ℝ)) ∉ Γ) (h' : (-1 : SL(2, ℝ)) ∉ Γ') (hpm : pmGroup Γ = pmGroup Γ') :
    Γ.relIndex (commensurator Γ) = Γ'.relIndex (commensurator Γ') := by
  have hc : commensurator Γ = commensurator Γ' := by
    rw [Subgroup.Commensurable.eq (commensurable_pmGroup h), hpm,
      ← Subgroup.Commensurable.eq (commensurable_pmGroup h')]
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (le_pmGroup Γ) (pmGroup_le_commensurator Γ),
    ← Subgroup.relIndex_mul_relIndex _ _ _ (le_pmGroup Γ') (pmGroup_le_commensurator Γ'),
    relIndex_pmGroup_eq_two h, relIndex_pmGroup_eq_two h', hpm, hc]

lemma pmGroup_le_of {Γ Γ' : Subgroup SL(2, ℝ)} (h : ∀ g ∈ Γ, g ∈ Γ' ∨ -g ∈ Γ') :
    pmGroup Γ ≤ pmGroup Γ' := by
  rintro g (hg | hg)
  · exact h g hg
  · rcases h _ hg with h' | h'
    · exact Or.inr h'
    · exact Or.inl (by simpa using h')

lemma pmGroup_closure_signs {A B A₁ B₁ : SL(2, ℝ)} (hA : A₁ ∈ ({A, -A} : Set SL(2, ℝ)))
    (hB : B₁ ∈ ({B, -B} : Set SL(2, ℝ))) :
    pmGroup (Subgroup.closure {A, B}) = pmGroup (Subgroup.closure {A₁, B₁}) := by
  have hA' : A ∈ ({A₁, -A₁} : Set SL(2, ℝ)) := by rcases hA with rfl | rfl <;> simp
  have hB' : B ∈ ({B₁, -B₁} : Set SL(2, ℝ)) := by rcases hB with rfl | rfl <;> simp
  exact le_antisymm (pmGroup_le_of fun _ hg ↦ M2.mem_or_neg_mem_of_signs hA hB hg)
    (pmGroup_le_of fun _ hg ↦ M2.mem_or_neg_mem_of_signs hA' hB' hg)

/-- The commensurator index is invariant under automorphisms. -/
lemma relIndex_commensurator_map {Γ : Subgroup SL(2, ℝ)} (φ : SL(2, ℝ) →* SL(2, ℝ))
    (hinj : Function.Injective φ) (hsurj : Function.Surjective φ) :
    (Γ.map φ).relIndex (commensurator (Γ.map φ)) = Γ.relIndex (commensurator Γ) := by
  have : commensurator (Γ.map φ) = (commensurator Γ).map φ := by
    ext w
    obtain ⟨v, rfl⟩ := hsurj w
    rw [mem_commensurator_map_iff hinj, Subgroup.mem_map_iff_mem hinj]
  rw [this, Subgroup.relIndex_map_map_of_injective _ _ hinj]

end transport

end OrbicurveCores.Fuchsian

namespace OrbicurveCores

open Fuchsian

/-- **R3** ([CanLift] Prop. 2.7, Riemann–Hurwitz step, group form): a once-punctured torus group
that admits a core has index `4` in its commensurator in `SL(2, ℝ)`: the commensurator is
generated by `Γ`, `-1` and a lift `ι` of the elliptic involution. Proved as `commIndexFour`
(`Genuine/TranslationCase.lean`). -/
def CommIndexFour : Prop :=
  ∀ A B : SL(2, ℝ), tr (A * B * A⁻¹ * B⁻¹) = -2 → tr A ≠ 0 →
    AdmitsCore (Subgroup.closure {A, B}) →
      (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) = 4

/-- **R3d** (proved as `translationCase`, `Genuine/TranslationCase.lean`): a normal-form
once-punctured torus group whose commensurator contains the translation `z ↦ z + 1/m` with
`m ≥ 2` admits no core. -/
def TranslationCase : Prop :=
  ∀ (x y z : ℝ), 0 < x → 0 < y → ∀ (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z),
    x < y + z → y < x + z → z < x + y → ∀ m : ℕ, 2 ≤ m →
      SL2R.uU (1 / m) ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) →
        ¬ AdmitsCore (Subgroup.closure {nA hz hrel, nB hz hrel})

/-- **R3b–R3c.** `CommIndexFour` follows from the translation case R3d. -/
theorem commIndexFour_of_translationCase (hT : TranslationCase) : CommIndexFour := by
  intro A B hcomm hA hcore
  obtain ⟨x, y, z, hx, hy, hz, hrel, ⟨t1, t2, t3⟩, A', B', hcl, A₁, hA₁, B₁, hB₁, g, hgA,
    hgB⟩ := exists_normal_form hcomm hA
  rw [← hcl] at hcore ⊢
  set H₁ := Subgroup.closure {A₁, B₁}
  set Γ₀ := Subgroup.closure {nA hz hrel, nB hz hrel}
  -- conjugation
  set P : Matrix (Fin 2) (Fin 2) ℝ := g.1
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set φ := SL2R.conjMat P hP
  have hφA : φ A₁ = nA hz hrel := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    have := congrArg Units.val hgA
    simpa [P, Matrix.coe_units_inv] using this
  have hφB : φ B₁ = nB hz hrel := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    have := congrArg Units.val hgB
    simpa [P, Matrix.coe_units_inv] using this
  have hΓ₀ : Γ₀ = H₁.map φ := by
    rw [MonoidHom.map_closure, Set.image_pair, hφA, hφB]
  have hφinj : Function.Injective φ := (SL2R.conjHomeo P hP).injective
  have hφsurj : Function.Surjective φ := (SL2R.conjHomeo P hP).surjective
  have hidx₀ : Γ₀.relIndex (commensurator Γ₀) = H₁.relIndex (commensurator H₁) := by
    rw [hΓ₀]; exact relIndex_commensurator_map φ hφinj hφsurj
  -- `-1 ∉ ⟨A₁, B₁⟩`, and `(A₁, B₁)` is a free basis
  have hφneg : φ (-1) = -1 := by
    apply Subtype.ext
    rw [SL2R.coe_conjMat]
    simp [Matrix.SpecialLinearGroup.coe_neg, mul_nonsing_inv _ hP]
  have hneg₁ : (-1 : SL(2, ℝ)) ∉ H₁ := fun h ↦ by
    have := Subgroup.mem_map_of_mem φ h
    rw [← hΓ₀, hφneg] at this
    exact neg_one_notMem hx hy hz hrel this
  have hinj₁ : Function.Injective (FreeGroup.lift ![A₁, B₁]) := by
    have hcomp : φ.comp (FreeGroup.lift ![A₁, B₁]) = FreeGroup.lift (ppF hz hrel) := by
      refine FreeGroup.ext_hom _ _ fun i ↦ ?_
      fin_cases i <;> simp [ppF, hφA, hφB]
    have := injective_lift_normal hx hy hz hrel
    rw [← hcomp, MonoidHom.coe_comp] at this
    exact this.of_comp
  -- signs
  have hA' : A' ∈ ({A₁, -A₁} : Set SL(2, ℝ)) := by rcases hA₁ with rfl | rfl <;> simp
  have hB' : B' ∈ ({B₁, -B₁} : Set SL(2, ℝ)) := by rcases hB₁ with rfl | rfl <;> simp
  have hneg' := neg_one_notMem_signs hA' hB' hinj₁ hneg₁
  have hidx := relIndex_commensurator_eq_of_pm hneg' hneg₁ (pmGroup_closure_signs hA₁ hB₁)
  rw [hidx, ← hidx₀]
  have hcore₀ : AdmitsCore Γ₀ := by
    unfold AdmitsCore; rw [hidx₀, ← hidx]; exact hcore
  rcases relIndex_commensurator_normal_or hx hy hz hrel t1 t2 t3 hcore₀ with h | ⟨m, hm, hmem⟩
  · exact h
  · exact absurd hcore₀ (hT x y z hx hy hz hrel t1 t2 t3 m hm hmem)

end OrbicurveCores
