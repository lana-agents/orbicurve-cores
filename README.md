# orbicurve-cores

Once-punctured elliptic curves failing to admit a core.

## Goals

Formalise Proposition 2.7 of Mochizuki, *The Absolute Anabelian Geometry of Canonical Curves* (<https://www.kurims.kyoto-u.ac.jp/~motizuki/Canonical%20Liftings.pdf>):

> If the once-punctured elliptic curve associated to `E_F` fails to admit an "`F`-core", then there are only four possibilities for the `j`-invariant of `E_F`.

## Status (branch `wp-canlift27`)

See `Blueprint.md` for the full plan, sources and status table. In short:

* **Statement.** `OrbicurveCores.CanLift27Genuine` (`Reconcile.lean`) states [EstIUT] Prop. 2.1 =
  [CanLift] Prop. 2.7 over any field of characteristic 0, with the genuine `k`-cores of
  `lana-agents/pi1` ([CanLift] Def. 2.1). The four exceptional values
  `{0, 1728, 2¹⁴·31³/5³, 2²·73³/3⁴}` are `OrbicurveCores.exceptionalJ` (`JValues.lean`, checked
  against Sijsling's models). This statement is **not proved**.
* **Proved (no `sorry`, standard axioms only)**, at the level of Fuchsian groups:
  * Takeuchi's classification of arithmetic `(1;∞)`-groups, necessity half
    (`takeuchi_one_infty`, `takeuchi_one_infty_conj`): Fricke identities, trace integrality in
    arithmetic groups, Nielsen descent, the Diophantine lemma, and Fricke rigidity up to
    `GL(2,ℝ)`-conjugacy;
  * arithmetic groups admit no core (`IsArithmeticSL.not_admitsCore`);
  * sharpness: the four explicit groups are arithmetic (certified coset enumeration), so Takeuchi's
    theorem holds as an iff (`isArithmeticSL_iff_isTakeuchiConj`);
  * the group-level CanLift 2.7, `not_admitsCore_iff_isTakeuchiConj`: a `(1;∞)`-group has no core
    iff it is one of the four (`GroupMain.lean`, `canLift27_group_iff`). The direction `→` is
    **conditional on** `MargulisDenseOneInfty` (Margulis' commensurator theorem in its standard
    form: dense commensurator ⇒ arithmetic, for once-punctured torus groups);
  * once-punctured torus groups are free, discrete lattices (`oneInftyFiniteCovolume`,
    `oneInfty_discrete`), and infinite index in the commensurator forces a dense commensurator
    (M1, `commensurator_dense`).
* **Missing** (research-scale): Margulis' theorem (M2, in progress under `OrbicurveCores/M2/`),
  uniformisation of `E ∖ 0` (U1), the
  algebraic ↔ analytic comparison of cores (U2), identification of the four uniformised curves
  (S1).

## Dependencies

Mathlib, and `lana-agents/pi1` (branch `wp-orbicurve-pi1`, pinned) for the genuine
`k`-cores of affine orbicurves. `Reconcile.lean` links the two notions of the statement (see
`Blueprint.md` §4). No Θ-data or `iut` dependency is needed.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
Library sources live under `OrbicurveCores/`, and every file must be imported from
the root module `OrbicurveCores.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib OrbicurveCores --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#10](https://taxis.lana.merten.dev/issues/10)
