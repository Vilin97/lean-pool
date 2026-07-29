/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ShapeMellinTranslation
public import LeanPool.Odlyzko.CompletedZeta.UnitSlabRadialIntegral

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units Set
  dirichletUnitTheorem

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
theorem integrableOn_positive_logarithmicMellinWeight
    {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (logarithmicMellinWeight K s)
      (positiveUnitFundamentalParamSet (K := K)) := by
  have hfin : 0 < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have ha : (((Module.finrank ℚ K : ℂ) * s).re) < 0 := by
    norm_num [Complex.mul_re]
    exact mul_neg_of_pos_of_neg hfin hs
  have hradial :=
    integrableOn_positiveUnitFundamentalParamSet_radial (K := K)
      (integrableOn_exp_mul_complex_Ioi ha 0)
  apply IntegrableOn.congr_fun hradial _ measurableSet_positiveUnitFundamentalParamSet
  intro y _
  rw [logarithmicMellinWeight_apply]
  push_cast
  ring_nf

omit [IsTotallyComplex K] in
open Classical in
theorem setIntegral_positive_logarithmicMellinWeight
    {s : ℂ} (hs : s.re < 0) :
    (∫ y in positiveUnitFundamentalParamSet (K := K),
      logarithmicMellinWeight K s y) =
        -1 / ((Module.finrank ℚ K : ℂ) * s) := by
  simp_rw [logarithmicMellinWeight_apply]
  rw [setIntegral_positiveUnitFundamentalParamSet_radial
    (K := K) (fun t ↦ Complex.exp
      ((((t * (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s)))]
  have hfin : 0 < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have ha : (((Module.finrank ℚ K : ℂ) * s).re) < 0 := by
    norm_num [Complex.mul_re]
    exact mul_neg_of_pos_of_neg hfin hs
  calc
    (∫ t in Ioi (0 : ℝ),
        Complex.exp ((((t * (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s))) =
        ∫ t in Ioi (0 : ℝ),
          Complex.exp (((Module.finrank ℚ K : ℂ) * s) * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      push_cast
      ring_nf
    _ = -1 / ((Module.finrank ℚ K : ℂ) * s) := by
      simpa using
        integral_exp_mul_complex_Ioi
          (a := (Module.finrank ℚ K : ℂ) * s) ha 0

omit [IsTotallyComplex K] in
open Classical in
theorem setIntegral_positive_logarithmicMellinWeight_neg
    {s : ℂ} (hs : 0 < s.re) :
    (∫ y in positiveUnitFundamentalParamSet (K := K),
      logarithmicMellinWeight K s (-y)) =
        1 / ((Module.finrank ℚ K : ℂ) * s) := by
  have hneg : (-s).re < 0 := by simpa using hs
  calc
    (∫ y in positiveUnitFundamentalParamSet (K := K),
        logarithmicMellinWeight K s (-y)) =
        ∫ y in positiveUnitFundamentalParamSet (K := K),
          logarithmicMellinWeight K (-s) y := by simp
    _ = -1 / ((Module.finrank ℚ K : ℂ) * (-s)) :=
      setIntegral_positive_logarithmicMellinWeight K hneg
    _ = 1 / ((Module.finrank ℚ K : ℂ) * s) := by ring

omit [IsTotallyComplex K] in
open Classical in
theorem integrableOn_positive_logarithmicMellinWeight_neg
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y ↦ logarithmicMellinWeight K s (-y))
      (positiveUnitFundamentalParamSet (K := K)) := by
  have hneg : (-s).re < 0 := by simpa using hs
  apply IntegrableOn.congr_fun
    (integrableOn_positive_logarithmicMellinWeight K hneg)
    _ measurableSet_positiveUnitFundamentalParamSet
  intro y _
  change logarithmicMellinWeight K (-s) y =
    logarithmicMellinWeight K s (-y)
  rw [logarithmicMellinWeight_apply, logarithmicMellinWeight_apply]
  simp only [Pi.neg_apply]
  push_cast
  ring_nf

end NumberField.Odlyzko
