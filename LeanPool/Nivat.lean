/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Main
public import LeanPool.Nivat.Statement

/-!
# Nivat's conjecture

Source: url:https://github.com/boonsuan/nivat
Authors: Boon Suan Ho
Status: verified
Main declarations: `Nivat.nivat`, `NivatSubmission.nivat`
Tags: symbolic-dynamics, pattern-complexity, periodicity, Nivat-conjecture, Laurent-polynomials
MSC: 37B10, 37B51, 68R15
-/

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

/-
# Pattern complexity and Nivat's conjecture

Public entry point for the formalization of the proof of Nivat's conjecture in
`paper/nivat.tex` of the upstream repository.

* `Nivat.nivat`: Theorem 1.1, for every finite alphabet on the full integer lattice.
* `NivatSubmission.nivat`: the same statement in Mathlib vocabulary only, as
  registered with Palomar (PALOMAR-2026-09-14-000003).
* `Nivat.nivat_rational`: the finite-range rational induction statement.
* `Nivat.two_factors`: Theorem 5.1, the two-factor theorem.

The import graph follows mathematical dependencies. The two-factor theorem is
proved entirely within `LeanPool.Nivat.Core` and `LeanPool.Nivat.TwoFactors`.
-/
