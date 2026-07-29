/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A discriminant factor used in the Odlyzko-bound argument. -/
def CompletedZeta.discriminantFactor (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)

/-- An archimedean factor used in the Odlyzko-bound argument. -/
def CompletedZeta.archimedeanFactor (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ nrRealPlaces K * (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K

/-- A completed used in the Odlyzko-bound argument. -/
def CompletedZeta.completed (s : ℂ) : ℂ :=
  CompletedZeta.discriminantFactor K s * CompletedZeta.archimedeanFactor K s * dedekindZeta K s

theorem discr_abs_pos : 0 < |(discr K : ℝ)| := by
  exact abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

theorem dedekindDiscriminantFactor_ne_zero (s : ℂ) :
    CompletedZeta.discriminantFactor K s ≠ 0 := by
  rw [CompletedZeta.discriminantFactor, cpow_ne_zero_iff]
  exact Or.inl (ofReal_ne_zero.mpr (discr_abs_pos K).ne')

theorem differentiable_dedekindDiscriminantFactor :
    Differentiable ℂ (CompletedZeta.discriminantFactor K) := by
  unfold CompletedZeta.discriminantFactor
  exact (differentiable_id.div_const _).const_cpow <|
    Or.inl (ofReal_ne_zero.mpr (discr_abs_pos K).ne')

end NumberField.Odlyzko
