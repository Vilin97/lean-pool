# Import failed: OSforGFF could not be made to build under v4.30.0-rc2

The OSforGFF formalization (with its transitive external dependencies — `bochner`,
`gaussian-field`, `kolmogorov_extension4`) has been vendored into `LeanPool/OSforGFF/` and the
mechanical migration has been done (lean-pool headers, stripped `set_option`/diagnostics, remapped
imports, directory index files, `projects.yml` entry, regenerated `LeanPool.lean`), and a number of
v4.30 bump errors have been fixed (the `WeakDual` import move, new doc-string spacing rules,
`linter.style.emptyLine`, `LinearPMap.mkSpanSingleton` type ascription, splitting
`L2_process_covariance_fubini_integrable`).

However, **`lake build LeanPool` does not succeed**, and the import cannot be completed in this
session. The blocking issue is documented in `IMPORT_NOTES.md`:

- `LeanPool/OSforGFF/Bochner/Main.lean` fails with `(deterministic) timeout at isDefEq` (200000
  heartbeats) in the `bochner_theorem` proof chain. Upstream (and Mathlib's own
  `CharacteristicFunction/Basic.lean`, and `OSforGFF/Measure/Construct.lean`) handle this class of
  v4.30 slowdown with `set_option backward.isDefEq.respectTransparency false in`, which lean-pool
  forbids (`set_option` is not allowed in committed files and `lakefile.toml` may not be edited).
  Splitting the proof into ~7 lemmas, replacing `Measurable.comp` with `fun_prop`,
  `Classical.indefiniteDescription`-based construction, `@[reducible]`/`@[irreducible]` on
  `gaussianRegularize`, and several `refine`/`exact`/`change` rewordings were all tried without
  success. Because `Bochner/Main.lean` is imported (transitively) by `Minlos/*`, `Measure/*`,
  `OS/*` and the master theorem, this blocks the whole library.

Beyond that, ~800 `linter.style.*`/`linter.flexible` warnings remain (these are enforced for
downstream files via `weak.linter.mathlibStandardSet`), ~12 further stripped `set_option
maxHeartbeats` proofs were not yet reached/repaired, ~8 proof bodies exceed the 200-line cap, and
~9 `def Foo.bar` declarations inside `namespace N` blocks need rewrapping for `quality.py`'s axiom
audit. See `IMPORT_NOTES.md` for the full inventory.

The vendored content and partial fixes are committed so the work is not lost.
