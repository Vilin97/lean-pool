/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.KernelSemigroup
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


/-!
# Intrinsic Kolmogorov moment bounds for a transition semigroup

Kolmogorov's continuity criterion is usually imposed on an already constructed coordinate
process.  This file states the same criterion directly on the transition semigroup: the
`p`-th moment of the displacement accumulated over a time step `h` is at most `M * h ^ q`,
uniformly in the starting point.

The predicate is purely a moment bound on the transition kernels.  It makes no path-space,
continuity, or stochastic-process claim; the transport of this bound to the canonical
dense-time coordinate process is proved elsewhere.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]

/-- A uniform `p`-th moment bound on the displacement of `P` over time `h`, of order `h ^ q`.

The exponents are constrained by `0 < p` and `1 < q`, exactly the range in which the
Kolmogorov--Chentsov threshold `(q - 1) / p` is a positive Hölder exponent.
The bound is demanded for every time `h ≥ 0`, not only
for small `h`; this is stronger than the local criterion the Kolmogorov--Chentsov theorem
needs, and it is what the bridge to `KolmogorovRegular` consumes. -/
def HasKolmogorovMoments (P : SubMarkovKernelSemigroup alpha) (p q : ℝ) (M : ℝ≥0) : Prop :=
  0 < p ∧ 1 < q ∧
    ∀ (h : ℝ≥0) (y : alpha), ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q

namespace HasKolmogorovMoments

variable {P : SubMarkovKernelSemigroup alpha} {p q : ℝ} {M : ℝ≥0}

/-- The moment exponent of a Kolmogorov moment bound is positive. -/
theorem p_pos (hmom : P.HasKolmogorovMoments p q M) : 0 < p :=
  hmom.1

/-- The time exponent of a Kolmogorov moment bound is strictly larger than one. -/
theorem one_lt_q (hmom : P.HasKolmogorovMoments p q M) : 1 < q :=
  hmom.2.1

/-- The time exponent of a Kolmogorov moment bound is positive. -/
theorem q_pos (hmom : P.HasKolmogorovMoments p q M) : 0 < q :=
  lt_trans zero_lt_one hmom.one_lt_q

/-- The displacement moment estimate carried by a Kolmogorov moment bound. -/
theorem lintegral_edist_le (hmom : P.HasKolmogorovMoments p q M) (h : ℝ≥0) (y : alpha) :
    ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q :=
  hmom.2.2 h y

/-- A Kolmogorov moment bound admits a strictly positive Hölder exponent below the
Kolmogorov--Chentsov threshold `(q - 1) / p`; the witness `(q - 1) / (2 * p)` is used. -/
theorem exists_holderExponent (hmom : P.HasKolmogorovMoments p q M) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < (q - 1) / p := by
  have hp : 0 < p := hmom.p_pos
  have hq : 0 < q - 1 := by linarith only [hmom.one_lt_q]
  refine ⟨(q - 1) / (2 * p), div_pos hq (by linarith only [hp]), ?_⟩
  exact div_lt_div_of_pos_left hq hp (by linarith only [hp])

end HasKolmogorovMoments

end SubMarkovKernelSemigroup

end MarkovProcess
