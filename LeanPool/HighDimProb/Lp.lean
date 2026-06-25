/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVariable

/-!
# Lp vocabulary

This file exposes Mathlib `MemLp`, `eLpNorm`, and `Integrable` under
HighDimProb-oriented names.

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Lp_space
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/--
A random variable belongs to `L^p(P)`.

Formula reference: `L^p` spaces collect functions with finite p-th power
integral; see https://en.wikipedia.org/wiki/Lp_space
-/
abbrev MemLpRandomVariable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : RandomVariable Ω E) (p : ENNReal) : Prop :=
  MemLp X p P

/-- A real-valued random variable belongs to `L^p(P)`. -/
abbrev MemLpRealRandomVariable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) : Prop :=
  MemLpRandomVariable P X p

/--
The Mathlib extended `L^p` seminorm of a random variable.

Formula reference: the `L^p` norm is based on integrating `|f|^p`; see
https://en.wikipedia.org/wiki/Lp_space
-/
abbrev lpNormRandomVariable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : RandomVariable Ω E) (p : ENNReal) : ENNReal :=
  eLpNorm X p P

/-- The Mathlib extended `L^p` seminorm of a real-valued random variable. -/
abbrev realLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) : ENNReal :=
  lpNormRandomVariable P X p

/-- A random variable is integrable under `P`. -/
abbrev IntegrableRandomVariable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : RandomVariable Ω E) : Prop :=
  Integrable X P

/-- A real-valued random variable is integrable under `P`. -/
abbrev IntegrableRealRandomVariable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  IntegrableRandomVariable P X

@[simp]
theorem memLpRandomVariable_iff {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : RandomVariable Ω E) (p : ENNReal) :
    MemLpRandomVariable P X p ↔ MemLp X p P :=
  Iff.rfl

theorem memLpRealRandomVariable_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) :
    MemLpRealRandomVariable P X p ↔ MemLp X p P :=
  Iff.rfl

@[simp]
theorem lpNormRandomVariable_def {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : RandomVariable Ω E) (p : ENNReal) :
    lpNormRandomVariable P X p = eLpNorm X p P :=
  rfl

theorem realLpNorm_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (p : ENNReal) :
    realLpNorm P X p = eLpNorm X p P :=
  rfl

@[simp]
theorem integrableRandomVariable_iff {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (X : RandomVariable Ω E) :
    IntegrableRandomVariable P X ↔ Integrable X P :=
  Iff.rfl

theorem integrableRealRandomVariable_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    IntegrableRealRandomVariable P X ↔ Integrable X P :=
  Iff.rfl

end

end HighDimProb
