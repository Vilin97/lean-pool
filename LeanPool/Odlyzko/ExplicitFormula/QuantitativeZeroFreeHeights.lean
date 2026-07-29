/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaRectangle
public import LeanPool.Odlyzko.ExplicitFormula.FiniteSetAvoidance

/-!
# Quantitative Zero Free Heights

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- Absolute ordinates, in prescribed bands, of zeros of the completed Dedekind zeta function. -/
noncomputable def completedDedekindZetaZeroAbsoluteOrdinatesInBands
    (a b U V : ℝ) : Finset ℝ :=
  ((completedDedekindZetaZerosInClosedRectangle K a b (-V) V).filter
      fun z ↦ U ≤ |z.im|).image fun z ↦ |z.im|

open Classical in
theorem exists_completedZeta_height_separated_from_zeros_in_bands
    (a b U : ℝ) {A L V : ℝ} (hA : 0 ≤ A) (hL : 0 < L) :
    ∃ T : ℝ, A < T ∧ T < A + L ∧
      ∀ z : ℂ,
        z.re ∈ Icc a b →
        |z.im| ∈ Icc U V →
        poleClearedCompletedDedekindZetaContinuation K z = 0 →
        finiteSetAvoidanceRadiusOnLength L
            (completedDedekindZetaZeroAbsoluteOrdinatesInBands K a b U V) ≤
          |T - z.im| ∧
        finiteSetAvoidanceRadiusOnLength L
            (completedDedekindZetaZeroAbsoluteOrdinatesInBands K a b U V) ≤
          |-T - z.im| := by
  let S := completedDedekindZetaZeroAbsoluteOrdinatesInBands K a b U V
  obtain ⟨T, hT, hsep⟩ :=
    exists_mem_Ioo_abs_sub_ge_finiteSetAvoidanceRadiusOnLength S A hL
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro z hzre hzim hzzero
  have hzrect :
      z ∈ completedDedekindZetaZerosInClosedRectangle K a b (-V) V := by
    apply (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mpr
    refine ⟨⟨hzre, ?_⟩,
      mem_completedDedekindZetaZeroDivisor_support_of_eq_zero K hzzero⟩
    grind
  have hzS : |z.im| ∈ S := by
    apply Finset.mem_image.mpr
    grind
  grind

end NumberField.Odlyzko
