/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Expectation
import LeanPool.HighDimProb.Orlicz
import LeanPool.HighDimProb.Tail

/-!
# SubExponential predicate forms

This file records separate real-valued subExponential predicate forms. It does
not define a canonical `SubExponential` predicate and does not prove equivalence
between formulations.

Verified Wikipedia references:
* Heavy-tailed/subExponential context: https://en.wikipedia.org/wiki/Heavy-tailed_distribution
* Orlicz space: https://en.wikipedia.org/wiki/Orlicz_space
-/

namespace HighDimProb

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

/--
Two-sided exponential tail decay with scale `K`.

Formula reference: subExponential tails are modeled here by
`P(|X| >= t) <= 2 * exp(-t/K)`; wiki.md maps this tail context to
https://en.wikipedia.org/wiki/Heavy-tailed_distribution
-/
def SubExponentialTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ t : ℝ, 0 ≤ t →
      absTailProb P X t ≤ ENNReal.ofReal (2 * Real.exp (-(t / K)))

/--
Moment-growth subExponential predicate.

Formula reference: linear-in-`p` moment growth is a standard subExponential
predicate form paired with exponential tails; see
https://en.wikipedia.org/wiki/Heavy-tailed_distribution

The exponent is kept in Mathlib's `ENNReal` form to match `realLpNorm`.
-/
def SubExponentialMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ p : ENNReal, 1 ≤ p → p ≠ ∞ →
      realLpNorm P X p ≤ ENNReal.ofReal (K * ENNReal.toReal p)

/--
Centered local-MGF subExponential predicate.

Formula reference: local exponential-moment control is an MGF form for
subExponential concentration; see
https://en.wikipedia.org/wiki/Moment-generating_function

Centering and integrability are not proved here; this is only the predicate
interface for later theorem work.
-/
def CenteredSubExponentialMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ lam : ℝ, |lam| ≤ 1 / K →
      expect P (fun ω => Real.exp (lam * X ω)) ≤ Real.exp (K ^ 2 * lam ^ 2)

/--
The Orlicz `psi_1` formulation, exposed under subExponential vocabulary.

Formula reference: `psi_1` is the exponential-linear Orlicz formulation; see
https://en.wikipedia.org/wiki/Orlicz_space
-/
abbrev SubExponentialOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  Psi1Bound P X K

/-- Finite `psi_1` Orlicz size, exposed under subExponential vocabulary. -/
abbrev HasSubExponentialOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  HasFinitePsi1 P X

@[simp]
theorem subExponentialOrlicz_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) :
    SubExponentialOrlicz P X K ↔ Psi1Bound P X K :=
  Iff.rfl

theorem hasSubExponentialOrlicz_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    HasSubExponentialOrlicz P X ↔ HasFinitePsi1 P X :=
  Iff.rfl

end

end HighDimProb
