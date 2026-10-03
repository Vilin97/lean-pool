/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.CenteredMaximal.Numerics
public import LeanPool.CenteredMaximal.UpperBound
public import LeanPool.CenteredMaximal.Lattice.LowerBound

/-!
# Bounds for the centered Hardy-Littlewood maximal constant

Source: url:https://github.com/CoolRmal/centered-maximal-constant
Authors: Yongxi Lin
Status: verified
Main declarations: `LeanPool.CenteredMaximal.ofReal_phi_le_weakTypeConstant_two`
Tags: harmonic-analysis, maximal-functions, weak-type-inequalities, lattice-constructions
MSC: 42B25, 26D15
-/

/-!
# Centered maximal-operator bounds

Imported from https://github.com/CoolRmal/centered-maximal-constant at
`c6a8cb29e8ecce9ac4614a8c7e4bf6938366f986` (Apache-2.0).
The full mathematical development and all four upstream result endpoints are retained.
Original proofs and the weighted configuration were generated with Claude under Yongxi Lin's
direction. The public completion commit is `06a726f113241d445903f0c0eae1ebe40d8b539f`
(2026-09-18). Port changes adapt module paths and namespaces, simplify numerical inequalities,
and retain upstream copyright notices.

The lower-bound argument is documented in upstream `docs/PROOF.md`. It adapts the smearing
method of J. M. Aldaz, *A remark on the centered n-dimensional Hardy-Littlewood maximal
function*, Czechoslovak Mathematical Journal 50 (2000), Lemma 1.1. The upper-bound covering
argument follows Terence Tao's *245A, Notes 5: Differentiation theorems*, Exercise 42.
The exact minimal-polynomial degree, optimality, and an exact level-set area are not claims
of the formal results.
-/

public section

open scoped ENNReal

namespace LeanPool.CenteredMaximal

/-- `1.685 < Φ`. -/
theorem lt_phi : (1685 / 1000 : ℝ) < phi :=
  phi_mem_Ioo.1

/-- `Φ < 1.686`. -/
theorem phi_lt : phi < 1686 / 1000 :=
  phi_mem_Ioo.2

/-- **Upper bound.** In every dimension `d`, `c_d ≤ 2ᵈ`: the Vitali covering argument, which for
centred cubes only needs to cover the centres, gives the factor `2ᵈ` instead of `3ᵈ`. -/
theorem weakTypeConstant_le_two_pow (d : ℕ) : weakTypeConstant d ≤ 2 ^ d :=
  weakTypeConstant_le (isWeakTypeBound_two_pow d)

/-- **Lower bound.** `Φ ≤ c₂`. The previously published lower bound was
`c₂ ≥ 3/4 - √2/4 + √6/2 = 1.62119…` (Aldaz, 2000, Proposition 1.4 with `n = 2`). -/
theorem ofReal_phi_le_weakTypeConstant_two : ENNReal.ofReal phi ≤ weakTypeConstant 2 :=
  le_weakTypeConstant fun _ hC => Lattice.ofReal_phi_le hC

end LeanPool.CenteredMaximal
