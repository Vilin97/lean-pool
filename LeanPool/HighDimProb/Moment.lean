/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Lp

/-!
# Moment vocabulary

Early moment infrastructure is intentionally phrased through Mathlib `MemLp`.

Verified Wikipedia references:
* Moment: https://en.wikipedia.org/wiki/Moment_(mathematics)
* Lp space: https://en.wikipedia.org/wiki/Lp_space
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/--
A real random variable has finite `p`-moment when it belongs to `L^p(P)`.

Formula reference: finite moments correspond to integrability of powers such
as `E[|X|^p]`; see https://en.wikipedia.org/wiki/Moment_(mathematics)
-/
abbrev HasFiniteMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) : Prop :=
  MemLpRealRandomVariable P X p

/--
Moment-size vocabulary reusing Mathlib's extended `L^p` seminorm.

Formula reference: `L^p` seminorms measure p-th power integrability; see
https://en.wikipedia.org/wiki/Lp_space
-/
abbrev momentSeminorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) : ENNReal :=
  realLpNorm P X p

theorem hasFiniteMoment_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) :
    HasFiniteMoment P X p ↔ MemLp X p P :=
  Iff.rfl

theorem momentSeminorm_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) :
    momentSeminorm P X p = eLpNorm X p P :=
  rfl

end

end HighDimProb
