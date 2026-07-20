# orbicurve-cores

Once-punctured elliptic curves failing to admit a core.

## Goals

Formalise Proposition 2.7 of Mochizuki, *The Absolute Anabelian Geometry of Canonical Curves* (<https://www.kurims.kyoto-u.ac.jp/~motizuki/Canonical%20Liftings.pdf>):

> If the once-punctured elliptic curve associated to `E_F` fails to admit an "`F`-core", then there are only four possibilities for the `j`-invariant of `E_F`.

## Open question on dependencies

As filed, the tracker has this project depending on the initial-Θ-data issue that introduces `ℓ`-torsion orbicurves, the `K`-core and the distinguished cusp — which lives in `iut`. That direction is suspect: the mathematical content here is a standalone anabelian result and should not need Θ-data.

The likely resolution is that only the **`K`-core / orbicurve definitions** are needed, in which case those should be factored out into a repository that both this project and `iut` can depend on. Resolve this before building much on top of the current dependency direction.

## Related repositories

Currently depends on core/orbicurve definitions that live in `iut`; see the note above.

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
