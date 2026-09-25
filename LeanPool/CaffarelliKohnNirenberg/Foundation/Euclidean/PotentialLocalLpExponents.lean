/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.NewtonianDerivativeLocalLp

/-!
# Potential Local Lp Exponents

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- Hölder on a finite-measure support: a function vanishing off a measurable set `s` has its
`L^p` size controlled by its `L^q` size for `p ≤ q`, with the explicit factor
`volume s ^ (1 / p - 1 / q)`. -/
theorem eLpNorm_le_eLpNorm_mul_rpow_measure_of_support {G : Vec3 → ℝ} {s : Set Vec3}
    (hs : MeasurableSet s) {p q : ℝ≥0∞} (hpq : p ≤ q)
    (hmeas : AEStronglyMeasurable G volume)
    (hzero : ∀ y, y ∉ s → G y = 0) :
    eLpNorm G p volume ≤
      eLpNorm G q volume * volume s ^ (1 / p.toReal - 1 / q.toReal) := by
  have hind : s.indicator G = G :=
    Set.indicator_eq_self.2 (Function.support_subset_iff'.2 hzero)
  have hp : eLpNorm G p volume = eLpNorm G p (volume.restrict s) := by
    have h1 := eLpNorm_indicator_eq_eLpNorm_restrict (f := G) (p := p) (μ := volume) hs
    rwa [hind] at h1
  rw [hp]
  calc eLpNorm G p (volume.restrict s)
      ≤ eLpNorm G q (volume.restrict s) *
          (volume.restrict s) Set.univ ^ (1 / p.toReal - 1 / q.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hmeas.restrict
    _ = eLpNorm G q (volume.restrict s) *
          volume s ^ (1 / p.toReal - 1 / q.toReal) := by
        rw [Measure.restrict_apply_univ]
    _ ≤ eLpNorm G q volume * volume s ^ (1 / p.toReal - 1 / q.toReal) :=
        mul_le_mul_left (eLpNorm_mono_measure G Measure.restrict_le_self) _

/-- Data supported in a closed ball and of class `L^q` is of class `L^p` for every `p ≤ q`. -/
theorem memLp_of_memLp_of_support_closedBall {G : Vec3 → ℝ} {R : ℝ} {p q : ℝ≥0∞}
    (hpq : p ≤ q) (hG : MemLp G q volume)
    (hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → G y = 0) :
    MemLp G p volume :=
  hG.mono_exponent_of_measure_support_ne_top hzero measure_closedBall_lt_top.ne hpq

/-- The `L^(6/5)` instance used by the Young estimate for the Newtonian potential: compactly
supported data of class `L^q` with `6 / 5 ≤ q` is of class `L^(6/5)`. -/
theorem memLp_six_fifths_of_memLp_ofReal {G : Vec3 → ℝ} {R q : ℝ} (hq : 6 / 5 ≤ q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → G y = 0) :
    MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
  memLp_of_memLp_of_support_closedBall
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (q := ENNReal.ofReal q)
    (ENNReal.ofReal_le_ofReal hq) hG hzero

/-- Compactly supported data of class `L^q` with `1 ≤ q` is integrable. -/
theorem integrable_of_memLp_ofReal_of_support {G : Vec3 → ℝ} {R q : ℝ} (hq : 1 ≤ q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → G y = 0) :
    Integrable G volume :=
  memLp_one_iff_integrable.1
    (memLp_of_memLp_of_support_closedBall (p := (1 : ℝ≥0∞)) (q := ENNReal.ofReal q)
      (ENNReal.one_le_ofReal.2 hq) hG hzero)

end CKN.Foundation.Euclidean
