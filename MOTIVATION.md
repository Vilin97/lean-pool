<img width="1586" height="661" alt="image" src="https://github.com/user-attachments/assets/ea9dde0c-73a0-41bf-8efd-3e75d888e8fc" />

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and [`merely-true`](https://github.com/merely-true/merely-true), preserving Lean 4 formalizations that don't fit mathlib's scope. Instead of mathlib's high-quality human review, Lean Pool relies on deterministic linters and LLM judgment, so it can grow faster while staying `sorry`-free and pinned to the latest Mathlib. It depends on Mathlib.

Lean Pool serves several purposes:

1. **One-off formalizations get maintained** — and can be depended upon, instead of bit-rotting in abandoned repositories.
2. **A relief valve for mathlib** — large or niche AI- and human-generated formalizations that don't fit mathlib's scope get a home, where strict CI and LLM review still enforce a quality bar.
3. **A PR target** for medium-quality, large-scale formalization projects.

To keep the bar high, Lean Pool only accepts serious, finished projects that are `sorry`-free and introduce no axioms beyond Lean's standard `Classical.choice`, `propext`, and `Quot.sound`.

The monorepo design — as opposed to a Reservoir-style registry of separate packages — is intentional: mathematics is interconnected, and several Lean Pool projects may be needed together at the same Lean version, without namespace clashes.

In the long run, Lean Pool (or something like it) could grow into a large mathematical library quickly — like arXiv, but for formal mathematics.
