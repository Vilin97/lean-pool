/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Definitions

Square-difference-free sets and their maximum cardinality inside the finite space of
polynomials over the field with three elements. These definitions retain the semantics
of the upstream statements.
-/

/-
Original source: https://github.com/JD-Jones-ASES/ns-lean
Commit: 035e9b0c147630e35631e4401433660f695d1fba
The upstream MIT notice is retained below; Lean Pool adaptations use Apache 2.0.

MIT License

Copyright (c) 2026 JD Jones

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

namespace NaslundCounterexample

/-- A finite set of polynomials over `F_3` is *square-difference-free*: no two of its elements
differ by a nonzero square. -/
def SquareDifferenceFree (A : Finset (Polynomial (ZMod 3))) : Prop :=
  ∀ f ∈ A, ∀ g ∈ A, ∀ z : Polynomial (ZMod 3), g - f = z ^ 2 → z = 0

/-- Every element of `A` has degree below `n`. For `n ≥ 1` this says `A ⊆ P_{3,n}`, the
polynomials of degree less than `n` (the zero polynomial has `natDegree 0`). -/
def DegreeBelow (n : ℕ) (A : Finset (Polynomial (ZMod 3))) : Prop :=
  ∀ f ∈ A, f.natDegree < n

/-- The polynomials of degree below `n` over `F_3`, as a finite set: the image of the coefficient
vectors `Fin n → ZMod 3` under `c ↦ Σ c_i T^i`. -/
noncomputable def polynomialsBelow (n : ℕ) : Finset (Polynomial (ZMod 3)) :=
  open scoped Classical in
  (Finset.univ : Finset (Fin n → ZMod 3)).image
    (fun c => ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))

/-- `maximumCardinality n`: the largest size of a square-difference-free set of polynomials of
degree below `n` over `F_3`. -/
noncomputable def maximumCardinality (n : ℕ) : ℕ :=
  open scoped Classical in
  ((polynomialsBelow n).powerset.filter SquareDifferenceFree).sup Finset.card

end NaslundCounterexample
