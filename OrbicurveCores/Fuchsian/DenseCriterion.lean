/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fuchsian.DenseSubgroup
import OrbicurveCores.FrickeRigidity

/-!
# A density criterion for subgroups of `SL(2, ℝ)`

`OrbicurveCores.SL2R.dense_of_not_discrete`: let `H ⊆ SL(2, ℝ)` be a subgroup containing a
hyperbolic `A` (`(tr A)² > 4`) and an element `B` with `tr [A, B] ≠ 2` and `tr B ≠ 0`. If `1` is
not isolated in `H`, then `H` is dense in `SL(2, ℝ)`.

This is the dichotomy "discrete or dense" for overgroups of such a pair. It is used to show that
the commensurator of a `(1;∞)`-group is dense as soon as it is not discrete (step M1 of
`Blueprint.md`).
-/

open Matrix Filter Topology
open scoped MatrixGroups

namespace OrbicurveCores.SL2R

section conjMat

variable (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : IsUnit P.det)

/-- Conjugation by an invertible real matrix, as an endomorphism of `SL(2, ℝ)`. -/
noncomputable def conjMat : SL(2, ℝ) →* SL(2, ℝ) where
  toFun x := ⟨P * x * P⁻¹, by
    rw [det_mul, det_mul, x.det_coe, mul_one, ← det_mul, mul_nonsing_inv P hP, det_one]⟩
  map_one' := by ext1; simp [mul_nonsing_inv P hP]
  map_mul' x y := by
    ext1
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [show P * (↑x * ↑y) * P⁻¹ = P * ↑x * (P⁻¹ * P) * ↑y * P⁻¹ by
      rw [nonsing_inv_mul P hP]; simp [mul_assoc]]
    simp [mul_assoc]

lemma coe_conjMat (x : SL(2, ℝ)) :
    ((conjMat P hP x : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = P * x * P⁻¹ := rfl

lemma continuous_conjMat : Continuous (conjMat P hP) := by
  apply Continuous.subtype_mk
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

lemma conjMat_inv_conjMat (x : SL(2, ℝ)) :
    conjMat P⁻¹ (isUnit_nonsing_inv_det P hP) (conjMat P hP x) = x := by
  ext1
  simp only [coe_conjMat, nonsing_inv_nonsing_inv P hP]
  rw [show P⁻¹ * (P * ↑x * P⁻¹) * P = (P⁻¹ * P) * ↑x * (P⁻¹ * P) by simp [mul_assoc],
    nonsing_inv_mul P hP]
  simp

lemma conjMat_conjMat_inv (x : SL(2, ℝ)) :
    conjMat P hP (conjMat P⁻¹ (isUnit_nonsing_inv_det P hP) x) = x := by
  ext1
  simp only [coe_conjMat, nonsing_inv_nonsing_inv P hP]
  rw [show P * (P⁻¹ * ↑x * P) * P⁻¹ = (P * P⁻¹) * ↑x * (P * P⁻¹) by simp [mul_assoc],
    mul_nonsing_inv P hP]
  simp

/-- Conjugation as a homeomorphism. -/
noncomputable def conjHomeo : SL(2, ℝ) ≃ₜ SL(2, ℝ) where
  toFun := conjMat P hP
  invFun := conjMat P⁻¹ (isUnit_nonsing_inv_det P hP)
  left_inv := conjMat_inv_conjMat P hP
  right_inv := conjMat_conjMat_inv P hP
  continuous_toFun := continuous_conjMat P hP
  continuous_invFun := continuous_conjMat _ _

lemma tr_conjMat (x : SL(2, ℝ)) : tr (conjMat P hP x) = tr x := by
  simp only [tr, coe_conjMat]
  rw [trace_mul_cycle, nonsing_inv_mul P hP, one_mul]

end conjMat

/-- **Density criterion.** A subgroup of `SL(2, ℝ)` containing a hyperbolic `A` and an element
`B` with `tr [A, B] ≠ 2`, `tr B ≠ 0`, in which `1` is not isolated, is dense. -/
theorem dense_of_not_discrete {H : Subgroup SL(2, ℝ)} {A B : SL(2, ℝ)} (hA : A ∈ H)
    (hB : B ∈ H) (hx : 4 < tr A ^ 2) (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2) (hy : tr B ≠ 0)
    (hnd : (𝓝[(H : Set SL(2, ℝ)) \ {1}] (1 : SL(2, ℝ))).NeBot) :
    Dense (H : Set SL(2, ℝ)) := by
  -- diagonalise `A`
  obtain ⟨P, hP0, hPA⟩ := exists_diagonalize (A := (A : Matrix (Fin 2) (Fin 2) ℝ)) A.det_coe hx
  have hP : IsUnit P.det := isUnit_iff_ne_zero.mpr hP0
  set l := eigBig (A : Matrix (Fin 2) (Fin 2) ℝ).trace
  set m := eigSmall (A : Matrix (Fin 2) (Fin 2) ℝ).trace
  have hprod : l * m = 1 := eig_prod hx
  have hlm : l - m ≠ 0 := (eig_sub_pos hx).ne'
  set f := conjMat P hP
  have hfA : ((f A : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, m] := by
    rw [coe_conjMat, hPA, mul_assoc, mul_nonsing_inv P hP, mul_one]
  set C := f B
  have hdetC := C.det_coe
  rw [det_fin_two] at hdetC
  -- `bc ≠ 0` and `a + d ≠ 0`
  have htrC : C 0 0 + C 1 1 = tr B := by rw [← tr_conjMat P hP B, tr_def]
  have htrAC : l * C 0 0 + m * C 1 1 = tr (A * B) := by
    rw [← tr_conjMat P hP (A * B), map_mul, tr, Matrix.SpecialLinearGroup.coe_mul, hfA,
      eta_fin_two (C : Matrix (Fin 2) (Fin 2) ℝ)]
    simp [trace_fin_two]
  have htrA : l + m = tr A := eig_sum
  have hbc : C 0 1 * C 1 0 ≠ 0 := by
    intro h0
    apply hc
    have hf := fricke_normal (b := C 0 1) (c := C 1 0) hprod hdetC
    rw [h0, htrA, htrC, htrAC] at hf
    rw [tr_commutator]
    linarith
  have hb : C 0 1 ≠ 0 := left_ne_zero_of_mul hbc
  have hcc : C 1 0 ≠ 0 := right_ne_zero_of_mul hbc
  have had : C 0 0 ≠ 0 ∨ C 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    rw [← htrC, h.1, h.2, add_zero]
  -- the transported group and its closure
  let H' := H.map f
  let K := H'.topologicalClosure
  have hKc : IsClosed (K : Set SL(2, ℝ)) := H'.isClosed_topologicalClosure
  have hH'K : ∀ {x}, x ∈ H' → x ∈ K := fun hx ↦ H'.le_topologicalClosure hx
  have hfK : ∀ {x}, x ∈ H → f x ∈ K := fun hx ↦ hH'K ⟨_, hx, rfl⟩
  -- a diagonal element `diag(L, L⁻¹)` with `L > 1`
  have hml : m ≠ l := fun h ↦ hlm (by rw [h, sub_self])
  have hl2 : l ^ 2 ≠ 1 := by
    intro h
    apply hml
    linear_combination (-m) * h + l * hprod
  have hm0 : m ≠ 0 := right_ne_zero_of_mul (by rw [hprod]; exact one_ne_zero)
  have hl0 : l ≠ 0 := left_ne_zero_of_mul (by rw [hprod]; exact one_ne_zero)
  have hAA : ((f (A * A) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![l ^ 2, 0; 0, m ^ 2] := by
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hfA]
    simp [sq]
  have hAiAi : ((f (A⁻¹ * A⁻¹) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![m ^ 2, 0; 0, l ^ 2] := by
    rw [map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      hfA]
    simp [adjugate_fin_two, sq]
  have hm2 : m ^ 2 = (l ^ 2)⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right hprod, inv_pow]
  obtain ⟨D, L, hL, hD, hDK⟩ : ∃ (D : SL(2, ℝ)) (L : ℝ), 1 < L ∧
      (D : Matrix (Fin 2) (Fin 2) ℝ) = !![L, 0; 0, L⁻¹] ∧ D ∈ K := by
    rcases hl2.lt_or_gt with hlt | hgt
    · refine ⟨f (A⁻¹ * A⁻¹), m ^ 2, ?_, ?_, hfK (mul_mem (inv_mem hA) (inv_mem hA))⟩
      · rw [hm2]; exact (one_lt_inv₀ (by positivity)).mpr hlt
      · rw [hAiAi, hm2, inv_inv]
    · exact ⟨f (A * A), l ^ 2, hgt, by rw [hAA, hm2], hfK (mul_mem hA hA)⟩
  -- a sequence tending to `1`
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : FirstCountableTopology SL(2, ℝ) :=
    TopologicalSpace.firstCountableTopology_induced _ (Matrix (Fin 2) (Fin 2) ℝ) Subtype.val
  obtain ⟨u, hu⟩ := exists_seq_tendsto (𝓝[(H : Set SL(2, ℝ)) \ {1}] (1 : SL(2, ℝ)))
  rw [tendsto_nhdsWithin_iff] at hu
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu.2
  set g : ℕ → SL(2, ℝ) := fun n ↦ f (u (n + N))
  have hgK : ∀ n, g n ∈ K := fun n ↦ hfK (hN (n + N) (by lia)).1
  have hg1 : ∀ n, g n ≠ 1 := fun n h ↦ (hN (n + N) (by lia)).2
    (by rw [← map_one f] at h; exact (conjHomeo P hP).injective h)
  have hglim : Tendsto g atTop (𝓝 1) := by
    have h1 := hu.1.comp (tendsto_add_atTop_nat N)
    have := ((continuous_conjMat P hP).tendsto 1).comp h1
    simpa [Function.comp_def, g] using this
  have key : ∀ {g : ℕ → SL(2, ℝ)}, (∀ n, g n ∈ K) → Tendsto g atTop (𝓝 1) →
      ((∃ᶠ n in atTop, (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0) ∨
        (∃ᶠ n in atTop, (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0)) → K = ⊤ := by
    intro g hg hlim h
    rcases h with h | h
    · obtain ⟨φ, hφ, hφ'⟩ := extraction_of_frequently_atTop h
      exact eq_top_of_seq hKc hL hD hDK (hfK hB) hb hcc (fun n ↦ hg (φ n))
        (hlim.comp hφ.tendsto_atTop) (Or.inl hφ')
    · obtain ⟨φ, hφ, hφ'⟩ := extraction_of_frequently_atTop h
      exact eq_top_of_seq hKc hL hD hDK (hfK hB) hb hcc (fun n ↦ hg (φ n))
        (hlim.comp hφ.tendsto_atTop) (Or.inr hφ')
  have hKtop : K = ⊤ := by
    by_cases h1 : ∃ᶠ n in atTop, (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0
    · exact key hgK hglim (Or.inl h1)
    by_cases h2 : ∃ᶠ n in atTop, (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0
    · exact key hgK hglim (Or.inr h2)
    rw [not_frequently] at h1 h2
    simp only [ne_eq, not_not] at h1 h2
    -- `g n` is eventually diagonal and different from `±1`
    have h00 : ∀ᶠ n in atTop, 0 < (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
      have := tendsto_entry hglim 0 0
      simp only [Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at this
      exact this.eventually (lt_mem_nhds (by norm_num))
    set g' : ℕ → SL(2, ℝ) := fun n ↦ C * g n * C⁻¹
    have hg'K : ∀ n, g' n ∈ K := fun n ↦ mul_mem (mul_mem (hfK hB) (hgK n)) (inv_mem (hfK hB))
    have hg'lim : Tendsto g' atTop (𝓝 1) := by
      have := ((continuous_conj C).tendsto 1).comp hglim
      simpa [Function.comp_def, g'] using this
    have hdiag : ∀ᶠ n in atTop, (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ≠
        (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
      filter_upwards [h1, h2, h00] with n e1 e2 e3
      intro heq
      have hdet := (g n).det_coe
      rw [det_fin_two, e1, e2, ← heq] at hdet
      have hμ : (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by nlinarith
      apply hg1 n
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e1, e2, ← heq, hμ]
    have entries : ∀ n, (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 →
        (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 →
        ((g' n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = C 0 0 * C 0 1 *
            ((g n : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (g n : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ∧
        ((g' n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = C 1 0 * C 1 1 *
            ((g n : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
      intro n e1 e2
      simp only [g', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        adjugate_fin_two]
      rw [eta_fin_two (C : Matrix (Fin 2) (Fin 2) ℝ), eta_fin_two (g n : Matrix (Fin 2) (Fin 2) ℝ)]
      simp only [Matrix.mul_fin_two, e1, e2]
      constructor <;> simp <;> ring
    apply key hg'K hg'lim
    rcases had with ha | hd
    · left
      refine Eventually.frequently ((h1.and (h2.and hdiag)).mono fun n ⟨e1, e2, e3⟩ ↦ ?_)
      rw [(entries n e1 e2).1]
      exact mul_ne_zero (mul_ne_zero ha hb) (sub_ne_zero.mpr (Ne.symm e3))
    · right
      refine Eventually.frequently ((h1.and (h2.and hdiag)).mono fun n ⟨e1, e2, e3⟩ ↦ ?_)
      rw [(entries n e1 e2).2]
      exact mul_ne_zero (mul_ne_zero hcc hd) (sub_ne_zero.mpr e3)
  -- conclude
  have hclos : closure (f '' (H : Set SL(2, ℝ))) = Set.univ := by
    have : (K : Set SL(2, ℝ)) = Set.univ := by rw [hKtop]; rfl
    rwa [Subgroup.topologicalClosure_coe, Subgroup.coe_map] at this
  have hdense : Dense (conjHomeo P hP '' (H : Set SL(2, ℝ))) := dense_iff_closure_eq.mpr hclos
  exact (conjHomeo P hP).isDenseEmbedding.dense_image.mp hdense

end OrbicurveCores.SL2R
