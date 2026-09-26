/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.Counterexamples
public import LeanPool.GaussianMomentsCounterexamples.GeneratingFunctions
public import LeanPool.GaussianMomentsCounterexamples.CoefficientContraction
public import LeanPool.GaussianMomentsCounterexamples.MomentDetails
public import LeanPool.GaussianMomentsCounterexamples.RadialMoments
public import LeanPool.GaussianMomentsCounterexamples.RealCoefficients
public import LeanPool.GaussianMomentsCounterexamples.CoordinatesProperties

/-!
# Gaussian Moments Conjecture counterexamples

Source: arxiv:2607.18186, url:https://github.com/long-mathematics/gaussian-moments-counterexamples
Authors: Christopher D. Long
Status: verified
Main declarations: `GaussianMomentsCounterexamples.not_GMC_of_three_le`
Tags: gaussian-measure, polynomial-moments, counterexamples, formal-power-series
MSC: 60E05, 13F20
-/

public section

/-
Upstream: https://github.com/long-mathematics/gaussian-moments-counterexamples
Commit: c31bb63aaa7cfccf1191893f8e7d04fa71bae025
First completed Lean release: 2026-09-17T15:47:31Z (upstream pull request 2).
The 18 mathematical modules preserve their upstream file names; JacobianMap.lean
and RouteArithmetic.lean are excluded. This import preserves the completed Gaussian
core and related moment results, not the manuscript's general reduction/inversion claims.

Christopher D. Long directed the upstream project. The imported development includes
Codex-authored porting and optimization. Upstream Lean authorship is inferred from the
public codex/lean-formalization branch; the upstream proof-authoring model and extent
of human editing are unreported. The manuscript's separate AI discovery credits do
not identify the Lean authoring model.

The original MIT notice follows. Apache 2.0 covers the Lean Pool adaptations and does
not replace these original copyright and permission terms.

MIT License

Copyright (c) 2026 long-mathematics

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
