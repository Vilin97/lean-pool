/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Main

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
# Proof of the independent Nivat statement

This module is compiled separately from `Challenge`. Its theorem has the same
fully expanded statement and is proved by the public finite-alphabet theorem.
It does not import the Challenge or its deliberate proof hole.
-/

public section

namespace NivatSubmission

universe u

/-- Theorem 1.1 (`thm:main`) of `paper/nivat.tex`, proved from `Nivat.nivat`: the
corresponding proof of the independent Challenge statement on the full integer
lattice. -/
theorem nivat {A : Type u} [Finite A] (c : (ℤ × ℤ) → A)
    (hlow : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      (Set.range (fun t : ℤ × ℤ =>
        fun z : (Finset.Ico (0 : ℤ) (m : ℤ)).product
          (Finset.Ico (0 : ℤ) (n : ℤ)) =>
            c (z.1 + t))).ncard ≤ m * n) :
    ∃ h : ℤ × ℤ, h ≠ (0, 0) ∧
      ∀ z : ℤ × ℤ, c (z + h) = c z := by
  obtain ⟨m, n, hm, hn, hcomplexity⟩ := hlow
  exact Nivat.nivat c m n hm hn hcomplexity

end NivatSubmission
