/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.TauBound
public import LeanPool.Zeta5Irrational.Construction
public import LeanPool.Zeta5Irrational.SimplePoles
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

/-! # The functional `τ_X` on rational functions with simple integer poles

For a numerator `A ∈ ℚ[x]` and a finite set `Pl ⊆ ℤ` of poles, `g = A / ∏_{r ∈ Pl} (x - r)`:

* `polyPart A Pl = A /ₘ ∏ (x - r)` (the polynomial part);
* `resP A Pl r = A(r) / ∏_{s ≠ r} (r - s)` (the residues);
* `tauX A Pl = τ(polyPart) + ∑_r res_r (H⁽⁵⁾_{d(r)} - X) ∈ ℚ[X]`, with `d(r) = r` for `r ≥ 0` and
  `d(r) = -r - 1` for `r < 0`.

`partial_fractions` : `A = P Π + ∑_r res_r ∏_{s ≠ r} (x - s)`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

/-- The harmonic index `d(r)`. -/
@[expose] def dd (r : ℤ) : ℕ :=
  if 0 ≤ r then r.toNat else (-r - 1).toNat

/-- The functional `τ_X`. -/
@[expose] noncomputable def tauX (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] :=
  C (tau (polyPart A Pl)) + ∑ r ∈ Pl, C (resP A Pl r) * (C (H5 (dd r)) - X)


end Zeta5Irrational
