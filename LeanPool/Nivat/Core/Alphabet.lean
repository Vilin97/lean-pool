/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import LeanPool.Nivat.Core.Patterns
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Rat.Cast.Order

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

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

/-!
# Rational labels for a finite alphabet

The reduction in Section 1.1, used in Section 6 to prove Theorem 1.1 (`thm:main`).
`exists_rational_model` preserves all pattern counts and all individual periods.
-/

namespace Nivat

/-- An injective rational labeling of a finite alphabet (Section 1.1). -/
noncomputable def rationalLabel (A : Type*) [Finite A] : A ↪ ℚ := by
  letI := Fintype.ofFinite A
  exact
    { toFun := fun a => ((Fintype.equivFin A a).val : ℚ)
      inj' := fun a b h => (Fintype.equivFin A).injective
        (Fin.ext (Nat.cast_injective h)) }

/-- The rational alphabet reduction in Section 1.1 and the proof of Theorem 1.1
in Section 6: the labeling preserves every pattern count and every period vector. -/
theorem exists_rational_model {A : Type*} [Finite A] (c : Configuration A) :
    ∃ d : Configuration ℚ, FiniteRange d ∧
      (∀ D : Finset Lattice, complexity d D = complexity c D) ∧
      (∀ h : Lattice, IsPeriod d h ↔ IsPeriod c h) := by
  refine ⟨rationalLabel A ∘ c, (finiteRange_of_finite c).map _, ?_, ?_⟩
  · intro D
    exact complexity_map c (rationalLabel A).injective D
  · intro h
    exact isPeriod_map_iff c (rationalLabel A).injective h

end Nivat
