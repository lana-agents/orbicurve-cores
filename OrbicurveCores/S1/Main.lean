/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Belyi
import OrbicurveCores.S1.Certificates
import OrbicurveCores.S1.JOrb
import OrbicurveCores.S1.Rigidity
import OrbicurveCores.S1.Transport
import OrbicurveCores.Reconcile

/-!
# S1: a curve uniformised by a Takeuchi group has exceptional `j`

**Theorem** (`exceptional_of_takeuchi`). If `E ∖ O` (`E` an elliptic curve over `ℂ`) is uniformised
by a Takeuchi group, then `j(E) ∈ {0, 1728, 2¹⁴·31³/5³, 2²·73³/3⁴}`.

Proof (Blueprint §2.3c, item 8): each of the four model curves `C_k` has a Belyi certificate
(`S1/Certificates.lean`), so it is uniformised by a Takeuchi group (`exists_takeuchi`), which after
transport is one of the four explicit pairs, of class `c k` (`Uniformizes.exists_takeuchiPair`;
the `C_k` are defined over `ℚ`, so complex conjugation fixes them). By rigidity
(`rigidityStatement`) and since the `j(C_k)` are distinct, `c` is injective, hence bijective.
So a curve uniformised by a Takeuchi pair of class `i = c k` has the `j`-invariant of `C_k` or
its complex conjugate, and these are equal.
-/

open Complex Polynomial
open scoped MatrixGroups ComplexConjugate

namespace OrbicurveCores.S1

/-- The four model curves over `ℚ`: `y² = x(x² + 44x − 16)`, `y² = (x − 24)(x + 8)(x + 12)`,
`y² = x(x² − 16)`, `y² = x³ − 1728`. -/
def qcurve : Fin 4 → WeierstrassCurve ℚ
  | 0 => ⟨0, 44, 0, -16, 0⟩
  | 1 => ⟨0, -4, 0, -384, -2304⟩
  | 2 => ⟨0, 0, 0, -16, 0⟩
  | 3 => ⟨0, 0, 0, 0, -1728⟩

/-- Their `j`-invariants. -/
def qj : Fin 4 → ℚ
  | 0 => 488095744 / 125
  | 1 => 1556068 / 81
  | 2 => 1728
  | 3 => 0

instance (k : Fin 4) : (qcurve k).IsElliptic := by
  refine ⟨?_⟩
  rw [isUnit_iff_ne_zero]
  fin_cases k <;>
    simp [qcurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;>
    norm_num

lemma qcurve_j (k : Fin 4) : (qcurve k).j = qj k := by
  fin_cases k <;>
    simp [WeierstrassCurve.j, qcurve, qj, WeierstrassCurve.Δ, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;>
    norm_num

lemma qj_mem (k : Fin 4) : qj k ∈ AffOrbicurve.excJ := by
  fin_cases k <;> simp [qj, AffOrbicurve.excJ]

lemma qj_injective : Function.Injective qj := by
  intro k k' h
  fin_cases k <;> fin_cases k' <;> first | rfl | (simp only [qj] at h; norm_num at h)

/-- The model curves over `ℂ`. -/
noncomputable def ccurve (k : Fin 4) : WeierstrassCurve ℂ := (qcurve k).map (algebraMap ℚ ℂ)

instance (k : Fin 4) : (ccurve k).IsElliptic := by unfold ccurve; infer_instance

lemma ccurve_j (k : Fin 4) : (ccurve k).j = (qj k : ℂ) := by
  unfold ccurve; rw [WeierstrassCurve.map_j, qcurve_j]; simp

lemma ccurve_conj (k : Fin 4) : (ccurve k).map (starRingEnd ℂ) = ccurve k := by
  unfold ccurve; rw [WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext_rat _ _

/-- Each model curve is uniformised by a Takeuchi group. -/
lemma exists_uniformizes_ccurve (k : Fin 4) :
    ∃ A B : SL(2, ℝ), Uniformizes (ccurve k) A B ∧ IsTakeuchiConj A B := by
  fin_cases k
  · refine exists_takeuchi jOrbStatement certI _ (by simp [ccurve, qcurve])
      (by simp [ccurve, qcurve]) fun x ↦ ?_
    simp [fI, ccurve, qcurve]; ring
  · refine exists_takeuchi jOrbStatement certII _ (by simp [ccurve, qcurve])
      (by simp [ccurve, qcurve]) fun x ↦ ?_
    simp [fII, ccurve, qcurve]; ring
  · refine exists_takeuchi jOrbStatement certIII _ (by simp [ccurve, qcurve])
      (by simp [ccurve, qcurve]) fun x ↦ ?_
    simp [fIII, ccurve, qcurve]; ring
  · refine exists_takeuchi jOrbStatement certIV _ (by simp [ccurve, qcurve])
      (by simp [ccurve, qcurve]) fun x ↦ ?_
    simp [fIV, ccurve, qcurve]; ring

/-- **S1.** A once-punctured elliptic curve over `ℂ` uniformised by a Takeuchi group has one of
the four exceptional `j`-invariants. -/
theorem exceptional_of_takeuchi (W : WeierstrassCurve ℂ) [W.IsElliptic] {A B : SL(2, ℝ)}
    (hU : Uniformizes W A B) (hT : IsTakeuchiConj A B) :
    ∃ c ∈ AffOrbicurve.excJ, W.j = (c : ℂ) := by
  have key : ∀ k, ∃ i : Fin 4, Uniformizes (ccurve k) (takeuchiPair i).1 (takeuchiPair i).2 := by
    intro k
    obtain ⟨A', B', hU', hT'⟩ := exists_uniformizes_ccurve k
    obtain ⟨i, h | h⟩ := Uniformizes.exists_takeuchiPair hU' hT'
    · exact ⟨i, h⟩
    · rw [ccurve_conj] at h; exact ⟨i, h⟩
  choose c hc using key
  have hinj : Function.Injective c := by
    intro k k' hkk'
    have h' : Uniformizes (ccurve k') (takeuchiPair (c k)).1 (takeuchiPair (c k)).2 := by
      rw [hkk']; exact hc k'
    have := rigidityStatement (ccurve k) (ccurve k') _ _ (hc k) h'
    rw [ccurve_j, ccurve_j] at this
    exact qj_injective (by exact_mod_cast this)
  have hsurj := Finite.surjective_of_injective hinj
  obtain ⟨i, h | h⟩ := Uniformizes.exists_takeuchiPair hU hT
  · obtain ⟨k, rfl⟩ := hsurj i
    have := rigidityStatement W (ccurve k) _ _ h (hc k)
    exact ⟨qj k, qj_mem k, by rw [this, ccurve_j]⟩
  · obtain ⟨k, rfl⟩ := hsurj i
    have := rigidityStatement (W.map (starRingEnd ℂ)) (ccurve k) _ _ h (hc k)
    rw [WeierstrassCurve.map_j, ccurve_j] at this
    refine ⟨qj k, qj_mem k, ?_⟩
    have := congrArg (starRingEnd ℂ) this
    rwa [conj_conj, map_ratCast] at this

/-- **S1, in the form used by U2**: a once-punctured elliptic curve over `ℂ` with
non-exceptional `j` is not uniformised by a Takeuchi group. -/
theorem not_takeuchi_of_nonExceptional (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (A B : SL(2, ℝ)) (hU : Uniformizes W A B)
    (hj : ∀ c ∈ AffOrbicurve.excJ, W.j ≠ (c : ℂ)) : ¬ IsTakeuchiConj A B := fun hT ↦ by
  obtain ⟨c, hc, h⟩ := exceptional_of_takeuchi W hU hT
  exact hj c hc h

end OrbicurveCores.S1
