# Challenges

Open *statements* — theorems written in Mathlib vocabulary and left as `sorry` — that
Lean Pool is asking someone to prove. One module per challenge, each registered in
[`challenges.yml`](challenges.yml) alongside the English statement it is supposed to say.

This is the only place in the repository where `sorry` is allowed, and only as the whole
proof body of a declaration the registry lists. Everything else in a statement file must be
closed, and imports must come from `Mathlib.*` so that reading a challenge never means
auditing pool code. Browse the board with `make challenges`.

A statement never changes once merged: it is the text every solution is judged against.
Answers go in [`../Solution/`](../Solution) and are checked by
[`leanprover/comparator`](https://github.com/leanprover/comparator).

See [Challenge mode](../CONTRIBUTING.md#challenge-mode) for how to propose one, and
[`../.github/CHALLENGE_REVIEW_RULES.md`](../.github/CHALLENGE_REVIEW_RULES.md) for what the
review asks of it.
