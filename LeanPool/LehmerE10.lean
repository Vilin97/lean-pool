/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.Defs
import LeanPool.LehmerE10.Main

/-!
# Lehmer's Polynomial and the E10 Coxeter Element

Source: url:https://github.com/dillon-11/lehmer-E10
Authors: Dillon Ryan
Status: verified
Main declarations: `LehmerE10.main_theorem`
Tags: number-theory, mahler-measure, salem-numbers, coxeter-groups
MSC: 11R06, 11C08, 20F55
-/

/-!
# Lehmer's polynomial and the E10 Coxeter element

The root module: `LehmerE10.main_theorem` — Lehmer's polynomial is
irreducible over ℤ, and it is the characteristic polynomial of a Coxeter
element of the E₁₀ Weyl group.
-/

namespace LehmerE10

/-- **The claim.**  (i) Lehmer's polynomial is irreducible over ℤ, and (ii) the
characteristic polynomial of a Coxeter element of the E₁₀ Weyl group is Lehmer's
polynomial (McMullen, *Coxeter groups, Salem numbers and the Hilbert metric*,
Publ. Math. IHÉS 95, 2002). -/
theorem main_theorem :
    Irreducible lehmerPolynomial ∧ coxeterE10.charpoly = lehmerPolynomial :=
  ⟨lehmer_irreducible, coxeter_charpoly_lehmer⟩

end LehmerE10
