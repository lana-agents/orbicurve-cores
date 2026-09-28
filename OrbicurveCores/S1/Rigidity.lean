/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Rigidity.Transfer

/-!
# S1: rigidity of the uniformised curve

**Theorem** (`rigidityStatement`). If `Uniformizes W A B` and `Uniformizes W' A B` for elliptic
curves `W, W'` over `ℂ`, then `j(W) = j(W')`.

Proof (Blueprint §2.3c, item 6):
1. `uniformizes_lattice`: replace `W, W'` by lattice curves `E_τ, E_τ'` with the same `j`.
2. `exists_isLatticeLift`: lift the uniformisations to `σ : ℍ → ℂ ∖ Λ`, `σ' : ℍ → ℂ ∖ Λ'`; both
   have fibres mod the lattice equal to the `⟨A, B⟩`-orbits, so they have the same fibres.
3. `exists_homothety`: then `Λ' = a Λ` (a Liouville argument on the induced map `ℂ / Λ → ℂ / Λ'`).
4. `modularJ_eq_of_homothety`: homothetic lattices have the same `g₂³ / (g₂³ - 27 g₃²)`.
-/

open UpperHalfPlane

namespace OrbicurveCores.S1

namespace Rigidity

lemma mem_periodPairScale_lattice {a : ℂ} (ha : a ≠ 0) (L : PeriodPair) {y : ℂ} :
    y ∈ (Heights.periodPairScale a ha L).lattice ↔ a⁻¹ * y ∈ L.lattice := by
  constructor
  · intro hy
    exact ((Heights.periodPairScaleLatticeEquiv a ha L).symm ⟨y, hy⟩).2
  · intro hy
    have := ((Heights.periodPairScaleLatticeEquiv a ha L) ⟨a⁻¹ * y, hy⟩).2
    rwa [Heights.periodPairScaleLatticeEquiv_coe, ← mul_assoc, mul_inv_cancel₀ ha,
      one_mul] at this

lemma G_eq_of_lattice_eq {L M : PeriodPair} (h : L.lattice = M.lattice) (n : ℕ) :
    L.G n = M.G n := by
  unfold PeriodPair.G
  rw [h]

/-- **Homothetic lattices have the same `j`-invariant.** -/
theorem modularJ_eq_of_homothety {τ τ' : ℍ} {a : ℂ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ (Lt τ).lattice ↔ a * x ∈ (Lt τ').lattice) :
    Heights.modularJ τ = Heights.modularJ τ' := by
  have hlat : (Heights.periodPairScale a ha (Lt τ)).lattice = (Lt τ').lattice := by
    ext y
    rw [mem_periodPairScale_lattice, h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hg₂ : (Lt τ').g₂ = a⁻¹ ^ 4 * (Lt τ).g₂ := by
    rw [← Heights.periodPairScale_g₂ a ha, PeriodPair.g₂, PeriodPair.g₂,
      G_eq_of_lattice_eq hlat]
  have hg₃ : (Lt τ').g₃ = a⁻¹ ^ 6 * (Lt τ).g₃ := by
    rw [← Heights.periodPairScale_g₃ a ha, PeriodPair.g₃, PeriodPair.g₃,
      G_eq_of_lattice_eq hlat]
  have hΔ := Heights.periodPair_invariant_discriminant_ne_zero τ
  rw [← Heights.latticeWeierstrassCurve_j, ← Heights.latticeWeierstrassCurve_j,
    WeierstrassCurve.j, WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', WeierstrassCurve.coe_Δ',
    Heights.latticeWeierstrassCurve_discriminant, Heights.latticeWeierstrassCurve_discriminant,
    Heights.latticeWeierstrassCurve_c4, Heights.latticeWeierstrassCurve_c4]
  change _ = ((Lt τ').g₂ ^ 3 - 27 * (Lt τ').g₃ ^ 2)⁻¹ * (12 * (Lt τ').g₂) ^ 3
  rw [hg₂, hg₃, show (a⁻¹ ^ 4 * (Lt τ).g₂) ^ 3 - 27 * (a⁻¹ ^ 6 * (Lt τ).g₃) ^ 2 =
    a⁻¹ ^ 12 * ((Lt τ).g₂ ^ 3 - 27 * (Lt τ).g₃ ^ 2) by ring]
  field_simp

end Rigidity

open Rigidity

/-- **Rigidity (S1).** Two elliptic curves over `ℂ` whose once-punctured curves are uniformised
by the same pair `A, B` have the same `j`-invariant. -/
theorem rigidityStatement : RigidityStatement := by
  intro W W' _ _ A B hW hW'
  obtain ⟨τ, hj, hU⟩ := uniformizes_lattice hW
  obtain ⟨τ', hj', hU'⟩ := uniformizes_lattice hW'
  obtain ⟨σ, hσ, hσrel⟩ := exists_isLatticeLift hU
  obtain ⟨σ', hσ', hσrel'⟩ := exists_isLatticeLift hU'
  have hrel : SameFibres τ τ' σ σ' := fun z w hz hw ↦
    (hσrel ⟨z, hz⟩ ⟨w, hw⟩).trans (hσrel' ⟨z, hz⟩ ⟨w, hw⟩).symm
  obtain ⟨a, ha, hlat⟩ := exists_homothety hσ hσ' hrel
  rw [hj, hj', modularJ_eq_of_homothety ha hlat]

end OrbicurveCores.S1
