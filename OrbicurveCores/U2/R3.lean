/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Oka.Uniformization.R3
import Oka.Uniformization.Uniqueness
import OrbicurveCores.S1.LatticeUnif

/-!
# R3 for a uniformised curve

oka's R3 (`Uniformization.Peripheral.le_pmDeck_or`) is stated for the `±`-deck group `Γ̃ = pmDeck`
of the lattice uniformisation `ψ : ℍ → ℂ ∖ Λ` and the invariants `g₂, g₃` of `Λ`. This file
transports it to an arbitrary uniformisation `(A, B, π)` of an elliptic curve `W / ℂ`
(`Uniformization.IsUniformization`) and to `W.j`:

**Theorem** (`r3`). If `⟨A, B⟩` admits a core (finite index in its commensurator), then every
element `δ` of the commensurator preserves the `x`-coordinate of `π`: `x(π(δ z)) = x(π z)`,
unless `j(W) = 0` or `j(W) = 1728`.

Proof: `W ≅ E_τ` (`C • E_τ = W`), and `piU τ C = T ∘ (℘, ℘'/2) ∘ ψ` uniformises `W` with the
edge pairings of `ψ`. By uniqueness (`IsUniformization.unique`) `π = piU ∘ g` and
`g (±⟨A, B⟩) g⁻¹ = ±⟨A_ψ, B_ψ⟩ = Γ` (the deck group of `ψ`). Finite index in the commensurator
passes along commensurability and conjugation to `Γ̃ ⊇ Γ`. By R3, `Comm Γ̃ = Γ̃` unless
`g₃ = 0` or `g₂ = 0`, i.e. `j = 1728` or `j = 0`; and `Γ̃` preserves `℘ ∘ ψ`, hence the
`x`-coordinate `u⁻² (℘ ∘ ψ − r)` of `piU`.
-/

open Complex Set Uniformization Uniformization.Generators Subgroup.Commensurable
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Pointwise

namespace OrbicurveCores.U2

variable {G : Type*} [Group G]

lemma commensurator_smul (g : G) (H : Subgroup G) :
    commensurator (ConjAct.toConjAct g • H) = ConjAct.toConjAct g • commensurator H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, commensurator_mem_iff, commensurator_mem_iff,
    commensurable_conj (ConjAct.toConjAct g)⁻¹, inv_smul_smul]
  have e : (ConjAct.toConjAct g)⁻¹ • x = g⁻¹ * x * g := by
    rw [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [e, map_mul, map_mul, map_inv, mul_smul, mul_smul]

lemma relIndex_commensurator_of_le {H K : Subgroup G} (hHK : H ≤ K) (hi : H.relIndex K ≠ 0)
    (h : H.relIndex (commensurator H) ≠ 0) : K.relIndex (commensurator K) ≠ 0 := by
  have hc : Subgroup.Commensurable H K := by
    refine ⟨?_, ?_⟩ <;>
      first | exact hi | (rw [Subgroup.relIndex_eq_one.mpr hHK]; exact one_ne_zero)
  rw [← eq hc]
  exact fun h0 ↦ h (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left _ hHK))

lemma relIndex_closure_pmGroup_ne_zero (A B : SL(2, ℝ)) :
    (Subgroup.closure {A, B}).relIndex (IsUniformization.pmGroup A B) ≠ 0 := by
  classical
  set Γ := Subgroup.closure {A, B}
  set P := IsUniformization.pmGroup A B
  -- `P = Γ ∪ -Γ`
  have hP : ∀ γ ∈ P, γ ∈ Γ ∨ -γ ∈ Γ := by
    intro γ hγ
    induction hγ using Subgroup.closure_induction with
    | mem g hg =>
      simp only [mem_insert_iff, mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact Or.inl (Subgroup.subset_closure (by simp))
      · exact Or.inl (Subgroup.subset_closure (by simp))
      · exact Or.inr (by simp)
    | one => exact Or.inl (one_mem _)
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (mul_mem hx hy)
      · exact Or.inr (by simpa using mul_mem hx hy)
      · exact Or.inr (by simpa using mul_mem hx hy)
      · exact Or.inl (by simpa using mul_mem hx hy)
    | inv x _ hx =>
      rcases hx with hx | hx
      · exact Or.inl (inv_mem hx)
      · exact Or.inr (by simpa using inv_mem hx)
  refine Subgroup.index_ne_zero_of_finite (hH := ?_)
  refine Finite.of_surjective (fun b : Bool ↦ if b then (QuotientGroup.mk (1 : P) :
    P ⧸ Γ.subgroupOf P) else QuotientGroup.mk ⟨-1, IsUniformization.neg_one_mem_pmGroup A B⟩) ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    rcases hP g g.2 with h | h
    · refine ⟨true, ?_⟩
      simp only [if_true]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h

variable {W : WeierstrassCurve ℂ} [W.IsElliptic]

lemma j_eq_of_g₂ {τ : ℍ} (C : WeierstrassCurve.VariableChange ℂ)
    (hC : C • Heights.latticeWeierstrassCurve τ = W)
    (h : (Heights.periodPairOfUpperHalfPlane τ).g₂ = 0) : W.j = 0 := by
  subst hC
  rw [WeierstrassCurve.variableChange_j]
  simp [WeierstrassCurve.j, Heights.latticeWeierstrassCurve, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, h]

lemma j_eq_of_g₃ {τ : ℍ} (C : WeierstrassCurve.VariableChange ℂ)
    (hC : C • Heights.latticeWeierstrassCurve τ = W)
    (h : (Heights.periodPairOfUpperHalfPlane τ).g₃ = 0) : W.j = 1728 := by
  have hΔ := Heights.periodPair_invariant_discriminant_ne_zero τ
  have hg₂ : (Heights.periodPairOfUpperHalfPlane τ).g₂ ≠ 0 := by
    intro h2; apply hΔ; rw [h, h2]; ring
  subst hC
  rw [WeierstrassCurve.variableChange_j, WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ']
  simp only [Heights.latticeWeierstrassCurve, WeierstrassCurve.c₄, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, h]
  have hne : (Heights.periodPairOfUpperHalfPlane τ).g₂ ^ 3 ≠ 0 := pow_ne_zero _ hg₂
  field_simp
  ring

/-- **R3 for a uniformised curve.** If `⟨A, B⟩` admits a core, every element of its
commensurator preserves the `x`-coordinate of the uniformisation, unless `j ∈ {0, 1728}`. -/
theorem r3 {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ} (hπ : IsUniformization W A B π)
    (hcore : AdmitsCore (Subgroup.closure {A, B})) :
    (∀ δ ∈ commensurator (Subgroup.closure {A, B}), ∀ z : ℍ,
      (π ((δ • z : ℍ) : ℂ)).1 = (π z).1) ∨ W.j = 0 ∨ W.j = 1728 := by
  obtain ⟨τ₀, hτ₀⟩ := Heights.modularJ_surjective W.j
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (Heights.latticeWeierstrassCurve τ₀) W (by rw [Heights.latticeWeierstrassCurve_j, hτ₀])
  set U := unifOf (Lt τ₀)
  obtain ⟨h1, h2, h3, h4⟩ := S1.uniformizes_piU τ₀ C
  rw [hC] at h2 h3
  have hπ₀ : IsUniformization W (Generators.A U) (Generators.B U) (S1.piU τ₀ C) := ⟨h1, h2, h3, h4⟩
  obtain ⟨g, hπg, hconj⟩ := hπ₀.unique hπ
  -- `±⟨A, B⟩` is conjugate to the deck group
  set P := IsUniformization.pmGroup A B
  have hPU : IsUniformization.pmGroup (Generators.A U) (Generators.B U) = U.deckGroup := by
    refine le_antisymm ?_ (deckGroup_le U)
    rw [IsUniformization.pmGroup, Subgroup.closure_le]
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [A_mem U, B_mem U, neg_one_mem_deckGroup U]
  have hD : U.deckGroup = ConjAct.toConjAct g • P := by
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, ← hPU]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, (hconj _).mpr (by simpa [mul_assoc] using hx), ?_⟩
      rw [ConjAct.toConjAct_smul]; group
    · rintro ⟨y, hy, rfl⟩
      rw [ConjAct.toConjAct_smul]; exact (hconj y).mp hy
  -- finite index passes to `Γ̃`
  have hP : P.relIndex (commensurator P) ≠ 0 :=
    relIndex_commensurator_of_le (IsUniformization.closure_le_pmGroup A B)
      (relIndex_closure_pmGroup_ne_zero A B) hcore
  have hDfin : U.deckGroup.relIndex (commensurator U.deckGroup) ≠ 0 := by
    rw [hD, commensurator_smul, Subgroup.relIndex_pointwise_smul]; exact hP
  have hQfin : U.pmDeck.relIndex (commensurator U.pmDeck) ≠ 0 := by
    rw [U.commensurator_pmDeck]
    exact fun h0 ↦ hDfin (Nat.eq_zero_of_zero_dvd
      (h0 ▸ Subgroup.relIndex_dvd_of_le_left _ U.deckGroup_le_pmDeck))
  rcases Peripheral.commensurator_eq_pmDeck_or hQfin with hR | hR | hR
  · left
    intro δ hδ z
    -- `g δ g⁻¹ ∈ Comm Γ = Comm Γ̃ = Γ̃`
    have hcommP : commensurator (Subgroup.closure {A, B}) = commensurator P := by
      refine eq ⟨?_, ?_⟩ <;>
        first | exact relIndex_closure_pmGroup_ne_zero A B |
          (rw [Subgroup.relIndex_eq_one.mpr (IsUniformization.closure_le_pmGroup A B)];
            exact one_ne_zero)
    have hmem : g * δ * g⁻¹ ∈ U.pmDeck := by
      rw [← hR, U.commensurator_pmDeck, hD, commensurator_smul,
        Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨δ, hcommP ▸ hδ, ?_⟩
      rw [ConjAct.toConjAct_smul]
    have hw := U.wp_ψ_smul_pm hmem (g • z)
    rw [mul_smul, mul_smul, inv_smul_smul] at hw
    rw [hπg, hπg, ← mul_smul]
    simp only [S1.piU, S1.vcT, wpt]
    change (C.u : ℂ)⁻¹ ^ 2 * ((Lt τ₀).weierstrassP (U.ψ ((g * δ) • z)) - C.r) =
      (C.u : ℂ)⁻¹ ^ 2 * ((Lt τ₀).weierstrassP (U.ψ (g • z)) - C.r)
    rw [mul_smul, hw]
  · exact Or.inr (Or.inr (j_eq_of_g₃ C hC hR))
  · exact Or.inr (Or.inl (j_eq_of_g₂ C hC hR))

end OrbicurveCores.U2
