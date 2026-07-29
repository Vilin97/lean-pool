/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.Degree
public import LeanPool.Odlyzko.Numerics.CompactCertificate
public import LeanPool.Odlyzko.Numerics.Integrability
public import LeanPool.Odlyzko.TestFunction.Bounds

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

theorem abs_archimedeanIntegrand_odlyzkoScale_le_exp {x : ℝ} (hx : 4 ≤ x) :
    |archimedeanIntegrand odlyzkoScale x| ≤
      37 * ((8 / 3 : ℝ) * Real.exp (-x)) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
  have harg : 1 ≤ |odlyzkoScale * x| := by
    rw [abs_of_pos (mul_pos odlyzkoScale_pos hx0)]
    rw [odlyzkoScale]
    grind
  have htest0 := tartarTestFunction_nonneg (odlyzkoScale * x)
  have htest36 := tartarTestFunction_le_thirty_six harg
  have : |1 - Tartar.testFunction (odlyzkoScale * x)| ≤ 37 := by grind
  rw [archimedeanIntegrand, abs_div, abs_of_pos hs]
  calc
    |1 - Tartar.testFunction (odlyzkoScale * x)| / Real.sinh x
        ≤ 37 * (1 / Real.sinh x) := by
          rw [div_eq_mul_inv]
          simp_all
    _ ≤ 37 * ((8 / 3 : ℝ) * Real.exp (-x)) := by
      gcongr
      exact one_div_sinh_le_exp_tail (by linarith)

theorem integrableOn_archimedeanIntegrand_odlyzkoScale_Ioi_four :
    MeasureTheory.IntegrableOn (archimedeanIntegrand odlyzkoScale) (Set.Ioi 4) := by
  have hmajor :
      MeasureTheory.IntegrableOn
        (fun x : ℝ ↦ 37 * ((8 / 3 : ℝ) * Real.exp (-x))) (Set.Ioi 4) :=
    ((integrableOn_exp_neg_Ioi 4).const_mul (8 / 3 : ℝ)).const_mul 37
  apply MeasureTheory.Integrable.mono' hmajor
  · exact (((measurable_const.sub
      (tartarTestFunction_measurable.comp (measurable_const.mul measurable_id))).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact abs_archimedeanIntegrand_odlyzkoScale_le_exp hx.le

theorem NumericalCertificate.odlyzkoScale_tail_lt :
    (∫ x in Set.Ioi (4 : ℝ), archimedeanIntegrand odlyzkoScale x) < 1 / 25 :=
  NumericalCertificate.integral_archimedeanIntegrand_Ioi_four_lt
    integrableOn_archimedeanIntegrand_odlyzkoScale_Ioi_four

theorem NumericalCertificate.archimedeanIntegral_le_of_compact_bound
    (hcompactInt :
      MeasureTheory.IntegrableOn (archimedeanIntegrand odlyzkoScale) (Set.Ioc 0 4))
    (hcompact :
      (∫ x in Set.Ioc (0 : ℝ) 4, archimedeanIntegrand odlyzkoScale x) ≤ 9 / 25) :
    archimedeanIntegral odlyzkoScale ≤ 2 / 5 := by
  have hunion : Set.Ioc (0 : ℝ) 4 ∪ Set.Ioi 4 = Set.Ioi 0 := by simp
  have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) 4) (Set.Ioi 4) := by simp
  rw [archimedeanIntegral, ← hunion,
    MeasureTheory.setIntegral_union hdisjoint measurableSet_Ioi hcompactInt
      integrableOn_archimedeanIntegrand_odlyzkoScale_Ioi_four]
  linarith [NumericalCertificate.odlyzkoScale_tail_lt]

theorem NumericalCertificate.archimedeanIntegral_le :
    archimedeanIntegral odlyzkoScale ≤ 2 / 5 :=
  NumericalCertificate.archimedeanIntegral_le_of_compact_bound
    ((integrableOn_archimedeanIntegrand_Ioi odlyzkoScale).mono_set <| by
      grind)
    integral_archimedean_odlyzkoScale_Ioc_zero_four_le

end NumberField.Odlyzko
