/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import LeanPool.Polytopes.MainTheorem

/-!
# The main theorem of polytopes

Source: url:https://github.com/Jun2M/Main-theorem-of-polytopes
Authors: Jun Kwon
Status: verified
Main declarations: `MainTheoremOfPolytopes`
Tags: convex-geometry, discrete-geometry, polytopes
MSC: 52B11, 52A20
-/

/-!
## Mathematical overview

A formalization of the **main theorem of polytopes** (the Minkowski–Weyl
theorem): in a finite-dimensional real vector space, a set is a `Vpolytope`
(the convex hull of a finite point set) if and only if it is a bounded
`Hpolytope` (a finite intersection of half-spaces).

- `MainTheoremOfPolytopes`: the two-way equivalence of V- and H-polytopes.
- Supporting results include `Vpolytope_of_Hpolytope` and
  `Hpolytope_of_Vpolytope_subsingleton`, built on a development of half-spaces,
  polar duality, and cut-spaces.

## References

The Minkowski–Weyl theorem — the equivalence of the vertex (V-) and halfspace
(H-) descriptions of a polytope — is classical; see G. M. Ziegler, *Lectures on
Polytopes*, Graduate Texts in Mathematics 152, Springer, 1995, Theorem 1.1, and
A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, §7.2.
-/
