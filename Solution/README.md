# Solutions

Answers to the challenges in [`../Challenge/`](../Challenge) live here, one module per
solved challenge, named after the challenge it answers.

A solution **restates** its challenge's statement under the same fully qualified name and
proves it. It must *not* import the challenge module:
[`leanprover/comparator`](https://github.com/leanprover/comparator) exports the two
environments separately and checks that the statements agree, which is what makes the
verdict independent of the statement file. A gate enforces this, and
[`challenge-verify.yml`](../.github/workflows/challenge-verify.yml) runs comparator over
every solved challenge on every relevant push.

A solution that needs real work should prove it in a pooled project under
[`../LeanPool/`](../LeanPool) and leave a thin bridge module here.

See [Solving a challenge](../CONTRIBUTING.md#solving-a-challenge).
