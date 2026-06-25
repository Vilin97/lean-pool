/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.LimitTheorems.Basic
import LeanPool.HighDimProb.Concentration.Chebyshev
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Weak law of large numbers statement layer

This module records typed weak-law targets backed by the current sample-mean,
tail, variance, and convergence-in-measure vocabulary. The statements are
specifications only; independence, iid, and variance-of-sum infrastructure are
not available yet.

Verified Wikipedia references:
* Law of large numbers: https://en.wikipedia.org/wiki/Law_of_large_numbers
* Chebyshev inequality route: https://en.wikipedia.org/wiki/Chebyshev%27s_inequality
-/

namespace HighDimProb

open MeasureTheory Filter
open scoped Topology

noncomputable section

/--
Typed target for the Chebyshev route to a finite-variance weak law.

Formula reference: this records the Chebyshev-style finite-sample bound
`P(|sampleMean - mu| >= eps) <= sigmaSq / (n * eps^2)`; see
https://en.wikipedia.org/wiki/Chebyshev%27s_inequality

The hypotheses are intentionally explicit proof obligations: future stages
should prove the displayed bound from finite variance plus independence and
covariance assumptions, rather than fake iid infrastructure here.
-/
abbrev weakLawChebyshevBoundStatement {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) {n : Nat}
    (X : Fin n -> RealRandomVariable Omega) (mu sigmaSq eps : Real) : Prop :=
  0 < eps ->
    MemLpRealRandomVariable P (sampleMean X) 2 ->
      mean P (sampleMean X) = mu ->
        variance P (sampleMean X) <= sigmaSq / (n : Real) ->
          absTailProb P (sampleMeanCentered X mu) eps <=
            ENNReal.ofReal (sigmaSq / ((n : Real) * eps ^ 2))

/--
Typed target for finite-variance weak convergence in probability of sample means.

Formula reference: the weak law asserts convergence in probability of sample
means to the mean under suitable independence/finite-variance hypotheses; see
https://en.wikipedia.org/wiki/Law_of_large_numbers

This uses Mathlib's `TendstoInMeasure` as the current convergence-in-probability
vocabulary. A proof is deferred until the project has sequence-level sample
families, independence/iid wrappers, and variance-of-sum facts.
-/
abbrev weakLawFiniteVarianceStatement {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X : (n : Nat) -> Fin n -> RealRandomVariable Omega) (mu : Real) : Prop :=
  TendstoInMeasure P (fun n => sampleMean (X n)) Filter.atTop (fun _ => mu)

end

end HighDimProb
