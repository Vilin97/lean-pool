/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.MetricSpace.Lipschitz
import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointExtension
import LeanPool.MarkovProcess.MarkovProcess.Main

/-!
# Kolmogorov bounds on a one-point compactification

This file provides a compatible metric on the one-point compactification and a local-time form of
the intrinsic Kolmogorov moment criterion. It transports whole-space distance tails, including
the cemetery point, to that local criterion by the weighted layer-cake formula.

Main results: `OnePoint.exhaustionMetricSpace`,
`SubMarkovKernelSemigroup.HasLocalKolmogorovMoments.toHasKolmogorovMoments`, and
`SubMarkovKernelSemigroup.HasOnePointTailBounds.kolmogorovRegular`.

The tail bounds and their scalar integral budget remain hypotheses for the consumer; no analytic
estimate for a particular semigroup is asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace OnePoint

variable {X : Type*} [MetricSpace X]

/-- The explicit distance on the one-point compactification associated with a positive
exhaustion function. -/
def exhaustionDist (rho : X → ℝ) : OnePoint X → OnePoint X → ℝ
  | ∞, ∞ => 0
  | ∞, (y : X) => rho y
  | (x : X), ∞ => rho x
  | (x : X), (y : X) => min (dist x y) (rho x + rho y)

/-- The exhaustion distance from the added point to itself vanishes. -/
@[simp] theorem exhaustionDist_infty_infty (rho : X → ℝ) :
    exhaustionDist rho (∞ : OnePoint X) ∞ = 0 := rfl

/-- The exhaustion distance from the added point to a live point is the exhaustion level there. -/
@[simp] theorem exhaustionDist_infty_coe (rho : X → ℝ) (y : X) :
    exhaustionDist rho ∞ (y : OnePoint X) = rho y := rfl

/-- The exhaustion distance from a live point to the added point is its exhaustion level. -/
@[simp] theorem exhaustionDist_coe_infty (rho : X → ℝ) (x : X) :
    exhaustionDist rho (x : OnePoint X) ∞ = rho x := rfl

/-- Between live points the exhaustion distance is the live distance capped by the sum of the
two exhaustion levels. -/
@[simp] theorem exhaustionDist_coe_coe (rho : X → ℝ) (x y : X) :
    exhaustionDist rho (x : OnePoint X) (y : OnePoint X) =
      min (dist x y) (rho x + rho y) := rfl

private theorem exhaustionDist_self (rho : X → ℝ) (hrho_pos : ∀ x, 0 < rho x)
    (z : OnePoint X) :
    exhaustionDist rho z z = 0 := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
      rw [exhaustionDist_coe_coe, dist_self, min_eq_left]
      exact add_nonneg (hrho_pos x).le (hrho_pos x).le

private theorem exhaustionDist_comm (rho : X → ℝ) (z w : OnePoint X) :
    exhaustionDist rho z w = exhaustionDist rho w z := by
  induction z using OnePoint.rec with
  | infty => induction w using OnePoint.rec <;> rfl
  | coe x =>
      induction w using OnePoint.rec with
      | infty => rfl
      | coe y => simp only [exhaustionDist_coe_coe, dist_comm, add_comm]

private theorem exhaustionDist_triangle (rho : X → ℝ) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho) (z w u : OnePoint X) :
    exhaustionDist rho z u ≤ exhaustionDist rho z w + exhaustionDist rho w u := by
  induction z using OnePoint.rec with
  | infty =>
      induction w using OnePoint.rec with
      | infty => simp only [exhaustionDist_infty_infty, zero_add, le_rfl]
      | coe y =>
          induction u using OnePoint.rec with
          | infty =>
              simp only [exhaustionDist_infty_infty, exhaustionDist_infty_coe,
                exhaustionDist_coe_infty]
              exact add_nonneg (hrho_pos y).le (hrho_pos y).le
          | coe x =>
              simp only [exhaustionDist_infty_coe, exhaustionDist_coe_coe]
              rcases min_choice (dist y x) (rho y + rho x) with hmin | hmin
              · rw [hmin]
                simpa only [NNReal.coe_one, one_mul, dist_comm] using
                  LipschitzWith.le_add_mul hrho_lipschitz x y
              · rw [hmin]
                linarith only [(hrho_pos y).le]
  | coe x =>
      induction w using OnePoint.rec with
      | infty =>
          induction u using OnePoint.rec with
          | infty =>
              simp only [exhaustionDist_coe_infty, exhaustionDist_infty_infty, add_zero,
                le_rfl]
          | coe y =>
              simp only [exhaustionDist_coe_coe, exhaustionDist_coe_infty,
                exhaustionDist_infty_coe]
              exact min_le_right _ _
      | coe y =>
          induction u using OnePoint.rec with
          | infty =>
              simp only [exhaustionDist_coe_infty, exhaustionDist_coe_coe]
              rcases min_choice (dist x y) (rho x + rho y) with hmin | hmin
              · rw [hmin]
                simpa only [NNReal.coe_one, one_mul, add_comm] using
                  LipschitzWith.le_add_mul hrho_lipschitz x y
              · rw [hmin]
                linarith only [(hrho_pos y).le]
          | coe u =>
              simp only [exhaustionDist_coe_coe]
              rcases min_choice (dist x y) (rho x + rho y) with hxy | hxy <;>
                rcases min_choice (dist y u) (rho y + rho u) with hyu | hyu
              · rw [hxy, hyu]
                exact (min_le_left _ _).trans (dist_triangle x y u)
              · rw [hxy, hyu]
                calc
                  min (dist x u) (rho x + rho u) ≤ rho x + rho u := min_le_right _ _
                  _ ≤ (rho y + dist x y) + rho u := add_le_add (by
                    simpa only [NNReal.coe_one, one_mul] using
                      LipschitzWith.le_add_mul hrho_lipschitz x y) le_rfl
                  _ = dist x y + (rho y + rho u) := by ring
              · rw [hxy, hyu]
                calc
                  min (dist x u) (rho x + rho u) ≤ rho x + rho u := min_le_right _ _
                  _ ≤ rho x + (rho y + dist u y) := add_le_add le_rfl (by
                    simpa only [NNReal.coe_one, one_mul] using
                      LipschitzWith.le_add_mul hrho_lipschitz u y)
                  _ = (rho x + rho y) + dist y u := by rw [dist_comm u y]; ring
              · rw [hxy, hyu]
                calc
                  min (dist x u) (rho x + rho u) ≤ rho x + rho u := min_le_right _ _
                  _ ≤ (rho x + rho y) + (rho y + rho u) := by
                    linarith only [(hrho_pos y).le]

private theorem exhaustionDist_eq_zero (rho : X → ℝ) (hrho_pos : ∀ x, 0 < rho x)
    (z w : OnePoint X) (hzw : exhaustionDist rho z w = 0) : z = w := by
  induction z using OnePoint.rec with
  | infty =>
      induction w using OnePoint.rec with
      | infty => rfl
      | coe y =>
          change rho y = 0 at hzw
          exact (ne_of_gt (hrho_pos y) hzw).elim
  | coe x =>
      induction w using OnePoint.rec with
      | infty =>
          change rho x = 0 at hzw
          exact (ne_of_gt (hrho_pos x) hzw).elim
      | coe y =>
          rcases le_total (dist x y) (rho x + rho y) with hle | hle
          · rw [exhaustionDist_coe_coe, min_eq_left hle] at hzw
            exact congrArg ((↑) : X → OnePoint X) (dist_eq_zero.mp hzw)
          · rw [exhaustionDist_coe_coe, min_eq_right hle] at hzw
            exact (ne_of_gt (add_pos (hrho_pos x) (hrho_pos y)) hzw).elim

private theorem isOpen_iff_exhaustionDist {rho : X → ℝ} (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (s : Set (OnePoint X)) :
    IsOpen s ↔ ∀ z ∈ s, ∃ epsilon > 0, ∀ w, exhaustionDist rho z w < epsilon → w ∈ s := by
  constructor
  · intro hs z hzs
    induction z using OnePoint.rec with
    | infty =>
        let K : Set X := ((↑) ⁻¹' s : Set X)ᶜ
        have hK : IsCompact K := (OnePoint.isOpen_def.mp hs).1 hzs
        obtain ⟨epsilon, hepsilon, hepsilonK⟩ :=
          hK.exists_forall_le' hrho_cont.continuousOn fun x _hx ↦ hrho_pos x
        refine ⟨epsilon, hepsilon, fun w hw ↦ ?_⟩
        induction w using OnePoint.rec with
        | infty => exact hzs
        | coe y =>
            have hyK : y ∉ K := fun hyK ↦ (not_lt_of_ge (hepsilonK y hyK)) hw
            exact not_not.mp hyK
    | coe x =>
        have hsX : IsOpen ((↑) ⁻¹' s : Set X) := (OnePoint.isOpen_def.mp hs).2
        obtain ⟨epsilon, hepsilon, hepsilon_ball⟩ :=
          Metric.isOpen_iff.mp hsX x hzs
        refine ⟨min epsilon (rho x), lt_min hepsilon (hrho_pos x), fun w hw ↦ ?_⟩
        induction w using OnePoint.rec with
        | infty =>
            exact (not_lt_of_ge (min_le_right epsilon (rho x))) hw |>.elim
        | coe y =>
            apply hepsilon_ball
            rcases min_lt_iff.mp hw with hdist | hrho
            · rw [Metric.mem_ball, dist_comm]
              exact lt_of_lt_of_le hdist (min_le_left epsilon (rho x))
            · exact (not_lt_of_ge
                ((min_le_right epsilon (rho x)).trans (le_add_of_nonneg_right
                  (hrho_pos y).le)) hrho).elim
  · intro hmetric
    have hsX : IsOpen ((↑) ⁻¹' s : Set X) := Metric.isOpen_iff.mpr fun x hx ↦ by
      obtain ⟨epsilon, hepsilon, hepsilon_ball⟩ := hmetric (x : OnePoint X) hx
      refine ⟨epsilon, hepsilon, fun y hy ↦ ?_⟩
      apply hepsilon_ball (y : OnePoint X)
      rw [Metric.mem_ball, dist_comm] at hy
      exact (min_le_left (dist x y) (rho x + rho y)).trans_lt hy
    refine OnePoint.isOpen_def.mpr ⟨?_, hsX⟩
    intro hinfty
    obtain ⟨epsilon, hepsilon, hepsilon_ball⟩ := hmetric OnePoint.infty hinfty
    apply IsCompact.of_isClosed_subset (hrho_compact epsilon hepsilon) hsX.isClosed_compl
    intro x hx
    change epsilon ≤ rho x
    by_contra hnot
    have hrho : rho x < epsilon := lt_of_not_ge hnot
    exact hx (hepsilon_ball (x : OnePoint X) hrho)

/-- The explicit metric on the one-point compactification determined by a positive Lipschitz
exhaustion function with compact positive superlevel sets. -/
noncomputable def exhaustionMetricSpace (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) :
    MetricSpace (OnePoint X) :=
  MetricSpace.ofDistTopology (exhaustionDist rho) (exhaustionDist_self rho hrho_pos)
    (exhaustionDist_comm rho) (exhaustionDist_triangle rho hrho_pos hrho_lipschitz)
    (isOpen_iff_exhaustionDist hrho_cont hrho_pos hrho_compact)
    (exhaustionDist_eq_zero rho hrho_pos)

/-- The exhaustion metric has definitionally the canonical one-point topology. -/
theorem exhaustionMetricSpace_toTopologicalSpace (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) :
    (exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      OnePoint.instTopologicalSpace := rfl

/-- The exhaustion distance between live points is at most their original distance. -/
theorem exhaustionDist_coe_coe_le (rho : X → ℝ) (x y : X) :
    exhaustionDist rho (x : OnePoint X) (y : OnePoint X) ≤ dist x y :=
  min_le_left _ _

/-- Under the explicit metric, the distance between live points is the displayed exhaustion
formula. -/
theorem exhaustionMetricSpace_dist_coe_coe (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) (x y : X) :
    letI := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    dist (x : OnePoint X) (y : OnePoint X) = min (dist x y) (rho x + rho y) := rfl

/-- Under the explicit metric, live-point distance is bounded by the original distance. -/
theorem exhaustionMetricSpace_dist_coe_coe_le (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) (x y : X) :
    letI := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    dist (x : OnePoint X) (y : OnePoint X) ≤ dist x y := by
  let := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  exact min_le_left _ _

/-- Under the explicit metric, a live point's distance to infinity is its exhaustion value. -/
theorem exhaustionMetricSpace_dist_coe_infty (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) (x : X) :
    letI := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    dist (x : OnePoint X) OnePoint.infty = rho x := rfl

/-- A live exhaustion-metric tail is contained in the corresponding tail for the original
metric. -/
theorem exhaustionMetricSpace_live_tail_subset (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) (x : X) (r : ℝ) :
    letI := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    {y : X | r < dist (y : OnePoint X) (x : OnePoint X)} ⊆ {y | r < dist y x} := by
  let := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  intro y hy
  exact hy.trans_le (exhaustionMetricSpace_dist_coe_coe_le rho hrho_cont hrho_pos
    hrho_lipschitz hrho_compact y x)

end OnePoint

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]

/-- A Kolmogorov moment estimate required only for time increments at most one, together with a
uniform bound for all displacements. On a compact metric space the latter bound is automatic. -/
def HasLocalKolmogorovMoments (P : SubMarkovKernelSemigroup alpha)
    (p q : ℝ) (M B : ℝ≥0) : Prop :=
  0 < p ∧ 1 < q ∧
    (∀ (h : ℝ≥0), h ≤ 1 → ∀ y : alpha,
      ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q) ∧
    ∀ y z : alpha, edist z y ^ p ≤ B

namespace HasLocalKolmogorovMoments

variable {P : SubMarkovKernelSemigroup alpha} {p q : ℝ} {M B : ℝ≥0}

/-- A local-time moment estimate plus a global displacement bound gives the library's global
moment criterion, with constant `M + B`. -/
theorem toHasKolmogorovMoments (hP : P.IsConservative)
    (hmom : P.HasLocalKolmogorovMoments p q M B) :
    P.HasKolmogorovMoments p q (M + B) := by
  refine ⟨hmom.1, hmom.2.1, fun h y ↦ ?_⟩
  by_cases hh : h ≤ 1
  · calc
      ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q := hmom.2.2.1 h hh y
      _ ≤ (M + B) * (h : ℝ≥0∞) ^ q := by gcongr; exact le_add_right le_rfl
  · have hh1 : (1 : ℝ≥0∞) ≤ h := by
      exact_mod_cast (le_of_not_ge hh)
    have hq : 0 < q := lt_trans zero_lt_one hmom.2.1
    calc
      ∫⁻ z, edist z y ^ p ∂(P h y) ≤ ∫⁻ _z, (B : ℝ≥0∞) ∂(P h y) :=
        lintegral_mono fun z ↦ hmom.2.2.2 y z
      _ = B := by rw [lintegral_const, hP h y, mul_one]
      _ ≤ (M + B) * 1 := by
        rw [mul_one]
        exact le_add_left le_rfl
      _ ≤ (M + B) * (h : ℝ≥0∞) ^ q := by
        gcongr
        exact ENNReal.one_le_rpow hh1 hq

end HasLocalKolmogorovMoments

section OnePointTails

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] (rho : X → ℝ) (hrho_cont : Continuous rho)
  (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
  (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The one-point compactification is complete under the exhaustion metric, since it is
compact under that metric's (canonical) topology. This is a typeclass-search cache: it lets
`letI := OnePoint.exhaustionMetricSpace …` discharge the ambient `[CompleteSpace (OnePoint X)]`
hypothesis of `KolmogorovRegular` without re-deriving compactness at each call site. -/
private instance instCompleteSpaceOnePointExhaustion :
    @CompleteSpace (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace := by
  have hCompact : @CompactSpace (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
    infer_instance
  exact @complete_of_compact (OnePoint X)
    (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
      hrho_compact).toPseudoMetricSpace.toUniformSpace
    hCompact

/-- The one-point compactification is a Borel space under the exhaustion metric: its
`MeasurableSpace` (the canonical Borel structure fixed at `OnePoint.instMeasurableSpace`) agrees
with the exhaustion metric's Borel sets, since the two topologies coincide. This is a
typeclass-search cache in the same spirit as `instCompleteSpaceOnePointExhaustion`. -/
private instance instBorelSpaceOnePointExhaustion :
    @BorelSpace (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      OnePoint.instMeasurableSpace := by
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  exact OnePoint.instBorelSpace

/-- The one-point compactification is second countable under the exhaustion metric's topology,
since that topology coincides with the canonical one. Typeclass-search cache, as above. -/
private instance instSecondCountableTopologyOnePointExhaustion :
    @SecondCountableTopology (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  exact OnePoint.instSecondCountableTopology

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- Kernel-level Markov inequality for a nonnegative `C₀` majorant of an exhaustion-metric tail
set. A semigroup comparison bound on the integral becomes the advertised exponential tail
bound. -/
theorem measure_gt_le_of_le_c0 (P : SubMarkovKernelSemigroup (OnePoint X))
    (rho : X → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (h : ℝ≥0) (x : X) (r A theta : ℝ) (v : C₀(OnePoint X, ℝ))
    (hA : 0 < A) (hv_nonneg : ∀ z, 0 ≤ v z)
    (hmajorant : ∀ z, r < OnePoint.exhaustionDist rho z (x : OnePoint X) → A ≤ v z)
    (hintegral : ∫ z, v z ∂P h (x : OnePoint X) ≤
      Real.exp (theta * (h : ℝ)) * v (x : OnePoint X)) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    P h (x : OnePoint X) {z | r < dist z (x : OnePoint X)} ≤
      ENNReal.ofReal (Real.exp (theta * (h : ℝ)) * v (x : OnePoint X) / A) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let mu := P h (x : OnePoint X)
  let : IsFiniteMeasure mu :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one h (x : OnePoint X)) ENNReal.one_lt_top⟩
  have hv_integrable : Integrable v mu := v.toBCF.integrable mu
  have hmajorant' :
      {z : OnePoint X | r < dist z (x : OnePoint X)} ⊆
        {z | ENNReal.ofReal A ≤ ENNReal.ofReal (v z)} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal (hmajorant z hz)
  calc
    mu {z | r < dist z (x : OnePoint X)} ≤
        mu {z | ENNReal.ofReal A ≤ ENNReal.ofReal (v z)} := measure_mono hmajorant'
    _ ≤ (∫⁻ z, ENNReal.ofReal (v z) ∂mu) / ENNReal.ofReal A := by
      apply meas_ge_le_lintegral_div
      · exact (ENNReal.measurable_ofReal.comp v.continuous.measurable).aemeasurable
      · exact (ENNReal.ofReal_pos.mpr hA).ne'
      · exact ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (∫ z, v z ∂mu) / ENNReal.ofReal A := by
      rw [ofReal_integral_eq_lintegral_ofReal hv_integrable
        (Eventually.of_forall hv_nonneg)]
    _ ≤ ENNReal.ofReal (Real.exp (theta * (h : ℝ)) * v (x : OnePoint X)) /
        ENNReal.ofReal A := by
      gcongr
    _ = ENNReal.ofReal (Real.exp (theta * (h : ℝ)) * v (x : OnePoint X) / A) := by
      rw [ENNReal.ofReal_div_of_pos hA]

/-- Whole-space distance-tail estimates and their weighted scalar layer-cake budget, which imply
a local Kolmogorov moment estimate on the one-point compactification. The tail set includes the
point at infinity whenever its distance from the live starting point exceeds the radius. -/
def HasOnePointTailBounds (P : SubMarkovKernelSemigroup (OnePoint X))
    (p q : ℝ) (M B : ℝ≥0)
    (phi : ℝ≥0 → X → ℝ → ℝ≥0∞) : Prop :=
  letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  (∀ x, rho x ≤ 1) ∧ 0 < p ∧ 1 < q ∧
    (∀ (h : ℝ≥0), h ≤ 1 → ∀ (x : X) (r : ℝ),
      0 < r → P h (x : OnePoint X) {z | r < dist z (x : OnePoint X)} ≤ phi h x r) ∧
    (∀ (h : ℝ≥0), h ≤ 1 → ∀ x : X,
      ENNReal.ofReal p *
          ∫⁻ r in Set.Ioi (0 : ℝ),
            phi h x r * ENNReal.ofReal (r ^ (p - 1)) ≤
        M * (h : ℝ≥0∞) ^ q) ∧
    ∀ z w : OnePoint X, edist w z ^ p ≤ B

namespace HasOnePointTailBounds

variable {rho : X → ℝ} {hrho_cont : Continuous rho} {hrho_pos : ∀ x, 0 < rho x}
  {hrho_lipschitz : LipschitzWith 1 rho}
  {hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}}
variable {P : SubMarkovKernelSemigroup (OnePoint X)} {p q : ℝ} {M B : ℝ≥0}
  {phi : ℝ≥0 → X → ℝ → ℝ≥0∞}

/-- Whole-space distance tails and their weighted budget imply the local moment criterion. -/
theorem hasLocalKolmogorovMoments
    (htail : P.HasOnePointTailBounds rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      p q M B phi)
    (hAbsorb : ∀ h, P h OnePoint.infty = Measure.dirac OnePoint.infty) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    P.HasLocalKolmogorovMoments p q M B := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  refine ⟨htail.2.1, htail.2.2.1, ?_, htail.2.2.2.2.2⟩
  intro h hh z
  induction z using OnePoint.rec with
  | infty =>
      rw [hAbsorb h, lintegral_dirac]
      simp only [edist_self, ENNReal.zero_rpow_of_pos htail.2.1]
      exact zero_le
  | coe x =>
      let mu := P h (x : OnePoint X)
      have hBorel : BorelSpace (OnePoint X) := OnePoint.instBorelSpace
      have hSecondCountable : SecondCountableTopology (OnePoint X) :=
        OnePoint.instSecondCountableTopology
      have hdist_meas : Measurable (fun z : OnePoint X ↦ dist z (x : OnePoint X)) :=
        measurable_dist.comp (measurable_id.prodMk measurable_const)
      rw [show (∫⁻ z, edist z (x : OnePoint X) ^ p ∂mu) =
          ∫⁻ z, ENNReal.ofReal (dist z (x : OnePoint X) ^ p) ∂mu by
        apply lintegral_congr
        intro z
        rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg htail.2.1.le]]
      rw [lintegral_rpow_eq_lintegral_meas_lt_mul mu
        (Eventually.of_forall fun _z ↦ dist_nonneg)
        hdist_meas.aemeasurable htail.2.1]
      calc
        ENNReal.ofReal p *
            ∫⁻ r in Set.Ioi (0 : ℝ),
              mu {z | r < dist z (x : OnePoint X)} * ENNReal.ofReal (r ^ (p - 1)) ≤
          ENNReal.ofReal p *
            ∫⁻ r in Set.Ioi (0 : ℝ),
              phi h x r * ENNReal.ofReal (r ^ (p - 1)) := by
          apply mul_le_mul_right
          apply setLIntegral_mono' measurableSet_Ioi
          intro r hr
          gcongr
          exact htail.2.2.2.1 h hh x r hr
        _ ≤ M * (h : ℝ≥0∞) ^ q := htail.2.2.2.2.1 h hh x

/-- Whole-space tail bounds yield the global intrinsic moment criterion. -/
theorem hasKolmogorovMoments (hP : P.IsConservative)
    (htail : P.HasOnePointTailBounds rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      p q M B phi)
    (hAbsorb : ∀ h, P h OnePoint.infty = Measure.dirac OnePoint.infty) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    P.HasKolmogorovMoments p q (M + B) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  exact
  (htail.hasLocalKolmogorovMoments hAbsorb).toHasKolmogorovMoments hP

/-- Whole-space tail bounds yield the regularity needed for the continuous-path process. -/
theorem kolmogorovRegular (hP : P.IsConservative)
    (htail : P.HasOnePointTailBounds rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      p q M B phi)
    (hAbsorb : ∀ h, P h OnePoint.infty = Measure.dirac OnePoint.infty) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    P.KolmogorovRegular hP := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  exact
  KolmogorovRegular.of_hasKolmogorovMoments P hP (htail.hasKolmogorovMoments hP hAbsorb)

end HasOnePointTailBounds

end OnePointTails

end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Whole-space tail bounds for the compactified semigroup produced by a positive `C₀`-resolvent
give the regularity required to construct its continuous-path process. -/
theorem kolmogorovRegular_onePointKernelSemigroup
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    {p q : ℝ} {M B : ℝ≥0}
    {phi : ℝ≥0 → X → ℝ → ℝ≥0∞}
    (htail : R.onePointKernelSemigroup.HasOnePointTailBounds rho hrho_cont hrho_pos
      hrho_lipschitz hrho_compact p q M B phi) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  exact htail.kolmogorovRegular R.isConservative_onePointKernelSemigroup
    R.onePointKernelSemigroup_absorbing

end MarkovProcess.PositiveC0ContractiveResolvent
