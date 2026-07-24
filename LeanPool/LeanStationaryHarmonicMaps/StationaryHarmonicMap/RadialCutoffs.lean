/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialGeometry

/-!
# Radial cutoff packages

This module packages the scalar radial cutoffs used to test weak stationarity.
It is deliberately independent of the later radial integral identities.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The precise cutoff interface needed by the weak radial identity on `B_R0(0)`.

Concrete cutoff families, such as the smooth approximations of sharp radial
annuli used later in the monotonicity proof, should be proved to satisfy this
structure.  Keeping the interface explicit prevents the downstream weak
identity from depending on the implementation details of a particular cutoff. -/
structure AdmissibleRadialCutoff (n : ℕ) (R0 M0 M1 : ℝ) (phi : ℝ → ℝ) :
    Prop where
  radius_nonneg : 0 ≤ R0
  differentiable : Differentiable ℝ phi
  contDiff : ContDiff ℝ 1 phi
  vectorField_contDiff : ContDiff ℝ 1 (radialVectorField (n := n) phi)
  vectorField_hasCompactSupport : HasCompactSupport (radialVectorField (n := n) phi)
  vectorField_support_subset :
    tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0
  phi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖phi t‖ ≤ M0
  deriv_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1

/-- If a point lies in the topological support of `x ↦ phi(|x|) x`, then its
radius lies in the topological support of `phi`. -/
theorem norm_mem_tsupport_of_mem_radialVectorField_tsupport {n : ℕ}
    {phi : ℝ → ℝ} {x : Domain n}
    (hx : x ∈ tsupport (radialVectorField (n := n) phi)) :
    ‖x‖ ∈ tsupport phi := by
  have hx' : x ∈ tsupport (fun y : Domain n => phi ‖y‖ • y) := hx
  have hxscalar : x ∈ tsupport (fun y : Domain n => phi ‖y‖) :=
    (tsupport_smul_subset_left (fun y : Domain n => phi ‖y‖) (fun y : Domain n => y)) hx'
  have hpre :
      tsupport (fun y : Domain n => phi ‖y‖) ⊆
        (fun y : Domain n => ‖y‖) ⁻¹' tsupport phi := by
    simpa [Function.comp_def] using
      (tsupport_comp_subset_preimage (g := phi) (f := fun y : Domain n => ‖y‖)
        continuous_norm)
  exact hpre hxscalar

/-- If a scalar radial coefficient is topologically supported in `[-R, R]`,
then the vector field `x ↦ phi(|x|) x` is topologically supported in
`closedBall 0 R`. -/
theorem radialVectorField_tsupport_subset_closedBall_of_scalar_tsupport {n : ℕ}
    {phi : ℝ → ℝ} {R : ℝ}
    (hphi : tsupport phi ⊆ Metric.closedBall (0 : ℝ) R) :
    tsupport (radialVectorField (n := n) phi) ⊆ Metric.closedBall (0 : Domain n) R := by
  intro x hx
  have hxnorm_closed : ‖x‖ ∈ Metric.closedBall (0 : ℝ) R :=
    hphi (norm_mem_tsupport_of_mem_radialVectorField_tsupport (n := n) hx)
  have hxnorm_le : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg (norm_nonneg x)]
      using hxnorm_closed
  simpa [Metric.mem_closedBall, dist_zero_right] using hxnorm_le

/-- If the scalar coefficient is supported in `(-∞, R0)`, then the radial
vector field is supported in the ball `B_R0(0)`.  This is the support statement
needed for sharp cutoffs that are allowed to be nonzero near the origin. -/
theorem radialVectorField_tsupport_subset_ball_of_scalar_tsupport_Iio {n : ℕ}
    {phi : ℝ → ℝ} {R0 : ℝ}
    (hphi : tsupport phi ⊆ Iio R0) :
    tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0 := by
  intro x hx
  have hxnorm : ‖x‖ ∈ tsupport phi :=
    norm_mem_tsupport_of_mem_radialVectorField_tsupport (n := n) hx
  have hxlt : ‖x‖ < R0 := hphi hxnorm
  simpa [Metric.mem_ball, dist_zero_right] using hxlt

/-- The same support assumption gives compact support of the radial vector
field, because it is contained in the closed ball of radius `R0`. -/
theorem radialVectorField_hasCompactSupport_of_scalar_tsupport_Iio {n : ℕ}
    {phi : ℝ → ℝ} {R0 : ℝ}
    (hphi : tsupport phi ⊆ Iio R0) :
    HasCompactSupport (radialVectorField (n := n) phi) := by
  have hclosed :
      tsupport (radialVectorField (n := n) phi) ⊆
        Metric.closedBall (0 : Domain n) R0 := by
    intro x hx
    have hxnorm : ‖x‖ ∈ tsupport phi :=
      norm_mem_tsupport_of_mem_radialVectorField_tsupport (n := n) hx
    have hxle : ‖x‖ ≤ R0 := le_of_lt (hphi hxnorm)
    simpa [Metric.mem_closedBall, dist_zero_right] using hxle
  exact (isCompact_closedBall (0 : Domain n) R0).of_isClosed_subset
    (isClosed_tsupport _) hclosed

/-- A one-dimensional `ContDiffBump` controls the support of its radial vector
field by the outer radius of the bump. -/
theorem radialVectorField_tsupport_subset_closedBall_of_contDiffBump {n : ℕ}
    (f : ContDiffBump (0 : ℝ)) :
    tsupport (radialVectorField (n := n) (fun t : ℝ => f t)) ⊆
      Metric.closedBall (0 : Domain n) f.rOut := by
  exact radialVectorField_tsupport_subset_closedBall_of_scalar_tsupport
    (n := n) (phi := fun t : ℝ => f t) (R := f.rOut)
    (by simp [f.tsupport_eq])

/-- Compact support of the radial vector field generated by a one-dimensional
`ContDiffBump`. -/
theorem radialVectorField_hasCompactSupport_of_contDiffBump {n : ℕ}
    (f : ContDiffBump (0 : ℝ)) :
    HasCompactSupport (radialVectorField (n := n) (fun t : ℝ => f t)) := by
  exact (isCompact_closedBall (0 : Domain n) f.rOut).of_isClosed_subset
    (isClosed_tsupport _) (radialVectorField_tsupport_subset_closedBall_of_contDiffBump (n := n) f)

/-- A one-dimensional `ContDiffBump` whose outer radius is strictly below `R0`
has radial vector-field support inside `B_R0(0)`. -/
theorem radialVectorField_tsupport_subset_ball_of_contDiffBump {n : ℕ}
    {R0 : ℝ} (f : ContDiffBump (0 : ℝ)) (hRout : f.rOut < R0) :
    tsupport (radialVectorField (n := n) (fun t : ℝ => f t)) ⊆
      Metric.ball (0 : Domain n) R0 :=
  (radialVectorField_tsupport_subset_closedBall_of_contDiffBump (n := n) f).trans
    (Metric.closedBall_subset_ball hRout)

/-- The derivative of a one-dimensional `ContDiffBump` is bounded on every
closed interval `[0, R0]`.  We keep the bound existential because the later
integrability arguments only need some finite constant. -/
theorem ContDiffBump.exists_deriv_bound_on_Icc (f : ContDiffBump (0 : ℝ)) (R0 : ℝ) :
    ∃ M1 : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv (fun s : ℝ => f s) t‖ ≤ M1 := by
  have hf1 : ContDiff ℝ 1 (fun s : ℝ => f s) := f.contDiff
  have hcont :
      ContinuousOn (fun t : ℝ => ‖deriv (fun s : ℝ => f s) t‖) (Set.Icc 0 R0) :=
    hf1.continuous_deriv_one.norm.continuousOn
  have hbdd :
      BddAbove ((fun t : ℝ => ‖deriv (fun s : ℝ => f s) t‖) '' Set.Icc 0 R0) :=
    isCompact_Icc.bddAbove_image hcont
  rcases hbdd with ⟨M1, hM1⟩
  exact ⟨M1, fun t ht0 htR => hM1 ⟨t, ⟨ht0, htR⟩, rfl⟩⟩

/-- A `C¹` scalar cutoff that is constant near the origin generates a `C¹`
radial vector field.  Away from the origin this is the chain rule for the norm;
at the origin the vector field is locally the linear map `x ↦ phi 0 • x`. -/
theorem radialVectorField_contDiff_of_contDiff_const_near_origin {n : ℕ}
    {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi)
    (hconst : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → phi t = phi 0) :
    ContDiff ℝ 1 (radialVectorField (n := n) phi) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rcases hconst with ⟨ε, hεpos, hε⟩
    have hlocal :
        radialVectorField (n := n) phi =ᶠ[𝓝 (0 : Domain n)]
          (fun y : Domain n => phi 0 • y) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Domain n) hεpos] with y hy
      have hynorm : ‖y‖ < ε := by
        simpa [Metric.mem_ball, dist_zero_right] using hy
      have hphi_y : phi ‖y‖ = phi 0 := hε ‖y‖ (by
        simpa [abs_of_nonneg (norm_nonneg y)] using hynorm)
      simp [radialVectorField, hphi_y]
    have hlinear :
        ContDiffAt ℝ 1 (fun y : Domain n => phi 0 • y) (0 : Domain n) := by
      fun_prop
    exact hlinear.congr_of_eventuallyEq hlocal
  · have hnorm : ContDiffAt ℝ 1 (fun y : Domain n => ‖y‖) x :=
      contDiffAt_norm (𝕜 := ℝ) (n := 1) hx
    have hscalar : ContDiffAt ℝ 1 (fun y : Domain n => phi ‖y‖) x :=
      hphi.contDiffAt.comp x hnorm
    exact hscalar.smul
      (contDiffAt_id (𝕜 := ℝ) (n := (1 : ℕ∞)) (x := x))

/-- A continuous real-valued function is bounded on a compact interval.  The
existential bound is the format needed by the cutoff integrability interface. -/
theorem exists_norm_bound_on_Icc_of_continuous {f : ℝ → ℝ}
    (hf : Continuous f) (a b : ℝ) :
    ∃ M : ℝ, ∀ t : ℝ, a ≤ t → t ≤ b → ‖f t‖ ≤ M := by
  have hcont :
      ContinuousOn (fun t : ℝ => ‖f t‖) (Set.Icc a b) :=
    hf.norm.continuousOn
  have hbdd :
      BddAbove ((fun t : ℝ => ‖f t‖) '' Set.Icc a b) :=
    isCompact_Icc.bddAbove_image hcont
  rcases hbdd with ⟨M, hM⟩
  exact ⟨M, fun t hta htb => hM ⟨t, ⟨hta, htb⟩, rfl⟩⟩

/-- A `C¹` real cutoff has bounded derivative on every compact interval. -/
theorem exists_deriv_bound_on_Icc_of_contDiff {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) (R0 : ℝ) :
    ∃ M1 : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1 := by
  have hcont :
      ContinuousOn (fun t : ℝ => ‖deriv phi t‖) (Set.Icc 0 R0) :=
    hphi.continuous_deriv_one.norm.continuousOn
  have hbdd :
      BddAbove ((fun t : ℝ => ‖deriv phi t‖) '' Set.Icc 0 R0) :=
    isCompact_Icc.bddAbove_image hcont
  rcases hbdd with ⟨M1, hM1⟩
  exact ⟨M1, fun t ht0 htR => hM1 ⟨t, ⟨ht0, htR⟩, rfl⟩⟩

/-- A scalar cutoff is constant in a symmetric neighborhood of the origin.  This
is the exact local regularity needed to make `x ↦ phi ‖x‖ • x` differentiable at
the origin without proving the full general radial-extension theorem. -/
def ConstNearOrigin (phi : ℝ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → phi t = phi 0

/-- A scalar `C¹` cutoff supported before `R0` and flat near the origin gives
the packaged admissible radial cutoff used by the weak stationarity argument. -/
theorem exists_admissibleRadialCutoff_of_contDiff_const_near_origin {n : ℕ}
    {R0 : ℝ} {phi : ℝ → ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hphi_diff : Differentiable ℝ phi)
    (hphi_cont : ContDiff ℝ 1 phi)
    (_hphi_compact : HasCompactSupport phi)
    (hphi_support : tsupport phi ⊆ Iio R0)
    (hconst : ConstNearOrigin phi) :
    ∃ M0 M1 : ℝ, AdmissibleRadialCutoff n R0 M0 M1 phi := by
  rcases exists_norm_bound_on_Icc_of_continuous hphi_cont.continuous 0 R0 with
    ⟨M0, hM0⟩
  rcases exists_deriv_bound_on_Icc_of_contDiff hphi_cont R0 with ⟨M1, hM1⟩
  exact ⟨M0, M1,
    { radius_nonneg := hR0_nonneg
      differentiable := hphi_diff
      contDiff := hphi_cont
      vectorField_contDiff :=
        radialVectorField_contDiff_of_contDiff_const_near_origin
          (n := n) hphi_cont hconst
      vectorField_hasCompactSupport :=
        radialVectorField_hasCompactSupport_of_scalar_tsupport_Iio
          (n := n) (phi := phi) (R0 := R0) hphi_support
      vectorField_support_subset :=
        radialVectorField_tsupport_subset_ball_of_scalar_tsupport_Iio
          (n := n) (phi := phi) (R0 := R0) hphi_support
      phi_bound := hM0
      deriv_bound := hM1 }⟩

/-- A scalar `C¹` cutoff supported before `R0` gives the packaged admissible
radial cutoff once the `C¹` regularity of its radial vector field is supplied
directly.  This is the correct replacement for the too-strong global
flat-at-origin assumption. -/
theorem exists_admissibleRadialCutoff_of_contDiff_and_vectorFieldContDiff {n : ℕ}
    {R0 : ℝ} {phi : ℝ → ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hphi_diff : Differentiable ℝ phi)
    (hphi_cont : ContDiff ℝ 1 phi)
    (_hphi_compact : HasCompactSupport phi)
    (hphi_support : tsupport phi ⊆ Iio R0)
    (hX_cont : ContDiff ℝ 1 (radialVectorField (n := n) phi)) :
    ∃ M0 M1 : ℝ, AdmissibleRadialCutoff n R0 M0 M1 phi := by
  rcases exists_norm_bound_on_Icc_of_continuous hphi_cont.continuous 0 R0 with
    ⟨M0, hM0⟩
  rcases exists_deriv_bound_on_Icc_of_contDiff hphi_cont R0 with ⟨M1, hM1⟩
  exact ⟨M0, M1,
    { radius_nonneg := hR0_nonneg
      differentiable := hphi_diff
      contDiff := hphi_cont
      vectorField_contDiff := hX_cont
      vectorField_hasCompactSupport :=
        radialVectorField_hasCompactSupport_of_scalar_tsupport_Iio
          (n := n) (phi := phi) (R0 := R0) hphi_support
      vectorField_support_subset :=
        radialVectorField_tsupport_subset_ball_of_scalar_tsupport_Iio
          (n := n) (phi := phi) (R0 := R0) hphi_support
      phi_bound := hM0
      deriv_bound := hM1 }⟩

/-- The interval primitive `t ↦ ∫ x in t..b, g x` is `C¹` when `g` is
continuous. -/
theorem contDiff_one_intervalPrimitive_left {g : ℝ → ℝ} (hg : Continuous g) (b : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => ∫ x : ℝ in t..b, g x) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro t
    exact (intervalIntegral.integral_hasDerivAt_left
      (f := g) (a := t) (b := b)
      (hg.intervalIntegrable t b)
      (hg.stronglyMeasurableAtFilter (μ := volume) (l := 𝓝 t))
      hg.continuousAt).differentiableAt
  · have hderiv :
        deriv (fun t : ℝ => ∫ x : ℝ in t..b, g x) = fun t : ℝ => -g t := by
      funext t
      exact intervalIntegral.deriv_integral_left
        (f := g) (a := t) (b := b)
        (hg.intervalIntegrable t b)
        (hg.stronglyMeasurableAtFilter (μ := volume) (l := 𝓝 t))
        hg.continuousAt
    rw [hderiv]
    exact hg.neg

/-- If a compactly supported real function has topological support contained in
`(-∞, R0)`, then the support is contained in `(-∞, U)` for some `U < R0`. -/
theorem exists_tsupport_subset_Iio_lt_of_hasCompactSupport
    {g : ℝ → ℝ} {R0 : ℝ}
    (hg_compact : HasCompactSupport g)
    (hg_support : tsupport g ⊆ Iio R0) :
    ∃ U : ℝ, tsupport g ⊆ Iio U ∧ U < R0 := by
  rcases (tsupport g).eq_empty_or_nonempty with h_empty | hne
  · refine ⟨R0 - 1, ?_, by linarith⟩
    intro x hx
    rw [h_empty] at hx
    exact hx.elim
  · rcases hg_compact.exists_isMaxOn hne continuousOn_id with ⟨x, hx, hxmax⟩
    have hx_lt : x < R0 := hg_support hx
    refine ⟨(x + R0) / 2, ?_, by linarith⟩
    intro y hy
    have hy_le_x : y ≤ x := isMaxOn_iff.mp hxmax y hy
    dsimp [Iio]
    linarith

/-- If a compactly supported real function has topological support contained in
`(0, R0)`, then the support is contained in `(L, ∞)` for some `0 < L`. -/
theorem exists_pos_lt_tsupport_subset_Ioi_of_hasCompactSupport
    {g : ℝ → ℝ} {R0 : ℝ}
    (hg_compact : HasCompactSupport g)
    (hg_support : tsupport g ⊆ Ioo (0 : ℝ) R0) :
    ∃ L : ℝ, 0 < L ∧ tsupport g ⊆ Ioi L := by
  rcases (tsupport g).eq_empty_or_nonempty with h_empty | hne
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    rw [h_empty] at hx
    exact hx.elim
  · rcases hg_compact.exists_isMinOn hne continuousOn_id with ⟨x, hx, hxmin⟩
    have hx_pos : 0 < x := (hg_support hx).1
    refine ⟨x / 2, by linarith, ?_⟩
    intro y hy
    have hx_le_y : x ≤ y := isMinOn_iff.mp hxmin y hy
    dsimp [Ioi]
    linarith

/-- If the support of `g` lies to the left of `U`, then its interval primitive
vanishes on intervals whose endpoints are both to the right of `U`. -/
theorem intervalPrimitive_eq_zero_of_tsupport_subset_Iio
    {g : ℝ → ℝ} {U t b : ℝ}
    (hg_support : tsupport g ⊆ Iio U) (ht : U < t) (hb : U < b) :
    (∫ x : ℝ in t..b, g x) = 0 := by
  have hEq : EqOn g (fun _ : ℝ => 0) (Set.uIcc t b) := by
    intro x hx
    have hxU : U < x := by
      have hmin : U < min t b := lt_min ht hb
      have hx_min : min t b ≤ x := by
        simpa [Set.uIcc] using hx.1
      exact hmin.trans_le hx_min
    have hx_not_support : x ∉ tsupport g := by
      intro hx_support
      exact not_lt_of_ge (le_of_lt hxU) (hg_support hx_support)
    exact image_eq_zero_of_notMem_tsupport hx_not_support
  rw [intervalIntegral.integral_congr hEq]
  exact intervalIntegral.integral_zero

/-- If the support of `g` lies to the right of `L`, then its interval integral
vanishes on intervals whose endpoints are both to the left of `L`. -/
theorem intervalPrimitive_eq_zero_of_tsupport_subset_Ioi
    {g : ℝ → ℝ} {L t b : ℝ}
    (hg_support : tsupport g ⊆ Ioi L) (ht : t < L) (hb : b < L) :
    (∫ x : ℝ in t..b, g x) = 0 := by
  have hEq : EqOn g (fun _ : ℝ => 0) (Set.uIcc t b) := by
    intro x hx
    have hxL : x < L := by
      have hmax : max t b < L := max_lt ht hb
      have hx_max : x ≤ max t b := by
        simpa [Set.uIcc] using hx.2
      exact hx_max.trans_lt hmax
    have hx_not_support : x ∉ tsupport g := by
      intro hx_support
      exact not_lt_of_ge (le_of_lt hxL) (hg_support hx_support)
    exact image_eq_zero_of_notMem_tsupport hx_not_support
  rw [intervalIntegral.integral_congr hEq]
  exact intervalIntegral.integral_zero

/-- If the support of `g` is separated from the origin on the right, then the
left interval primitive `t ↦ ∫ x in t..b, g x` is constant near the origin. -/
theorem intervalPrimitive_eq_intervalPrimitive_zero_of_tsupport_subset_Ioi
    {g : ℝ → ℝ} {L t b : ℝ}
    (hg_cont : Continuous g)
    (hg_support : tsupport g ⊆ Ioi L) (hL_pos : 0 < L) (ht : t < L) :
    (∫ x : ℝ in t..b, g x) = (∫ x : ℝ in (0 : ℝ)..b, g x) := by
  have hzero :
      (∫ x : ℝ in t..(0 : ℝ), g x) = 0 :=
    intervalPrimitive_eq_zero_of_tsupport_subset_Ioi
      (g := g) (L := L) (t := t) (b := 0)
      hg_support ht hL_pos
  have hadd :
      (∫ x : ℝ in t..(0 : ℝ), g x) +
          (∫ x : ℝ in (0 : ℝ)..b, g x) =
        (∫ x : ℝ in t..b, g x) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable t 0)
      (hg_cont.intervalIntegrable 0 b)
  rw [hzero, zero_add] at hadd
  exact hadd.symm

/-- The radial vector field generated by a one-dimensional `ContDiffBump` is
`C¹`.  Away from the origin this is the usual chain rule for the norm; near the
origin the bump is identically `1`, so the vector field is locally the identity. -/
theorem radialVectorField_contDiff_of_contDiffBump {n : ℕ} (f : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ 1 (radialVectorField (n := n) (fun t : ℝ => f t)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hlocal :
        radialVectorField (n := n) (fun t : ℝ => f t) =ᶠ[𝓝 (0 : Domain n)]
          (fun y : Domain n => y) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Domain n) f.rIn_pos] with y hy
      have hy_norm_lt : ‖y‖ < f.rIn := by
        simpa [Metric.mem_ball, dist_zero_right] using hy
      have hy_closed : ‖y‖ ∈ Metric.closedBall (0 : ℝ) f.rIn := by
        rw [Metric.mem_closedBall, Real.dist_eq]
        simpa [abs_of_nonneg (norm_nonneg y)] using le_of_lt hy_norm_lt
      have hfy : f ‖y‖ = 1 := f.one_of_mem_closedBall hy_closed
      simp [radialVectorField, hfy]
    exact (contDiffAt_id (𝕜 := ℝ) (n := (1 : ℕ∞)) (x := (0 : Domain n))).congr_of_eventuallyEq
      hlocal
  · have hnorm : ContDiffAt ℝ 1 (fun y : Domain n => ‖y‖) x :=
      contDiffAt_norm (𝕜 := ℝ) (n := 1) hx
    have hscalar : ContDiffAt ℝ 1 (fun y : Domain n => f ‖y‖) x :=
      (f.contDiff (n := (1 : ℕ∞))).contDiffAt.comp x hnorm
    exact hscalar.smul (contDiffAt_id (𝕜 := ℝ) (n := (1 : ℕ∞)) (x := x))

/-- Build the admissible-cutoff package from a one-dimensional `ContDiffBump`,
once the derivative bound on `[0, R0]` is supplied. -/
theorem ContDiffBump.admissibleRadialCutoff {n : ℕ} {R0 M1 : ℝ}
    (f : ContDiffBump (0 : ℝ)) (hRout : f.rOut < R0)
    (hderiv_bound :
      ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv (fun s : ℝ => f s) t‖ ≤ M1) :
    AdmissibleRadialCutoff n R0 1 M1 (fun t : ℝ => f t) where
  radius_nonneg := (le_of_lt f.rOut_pos).trans (le_of_lt hRout)
  differentiable := (f.contDiff (n := (1 : ℕ∞))).differentiable_one
  contDiff := f.contDiff
  vectorField_contDiff := radialVectorField_contDiff_of_contDiffBump (n := n) f
  vectorField_hasCompactSupport := radialVectorField_hasCompactSupport_of_contDiffBump (n := n) f
  vectorField_support_subset :=
    radialVectorField_tsupport_subset_ball_of_contDiffBump (n := n) f hRout
  phi_bound := by
    intro t _ht0 _htR
    rw [Real.norm_eq_abs, abs_of_nonneg (f.nonneg' t)]
    exact f.le_one
  deriv_bound := hderiv_bound

/-- A one-dimensional `ContDiffBump` whose outer radius is below `R0` gives an
admissible radial cutoff for some derivative-bound constant `M1`. -/
theorem ContDiffBump.exists_admissibleRadialCutoff {n : ℕ} {R0 : ℝ}
    (f : ContDiffBump (0 : ℝ)) (hRout : f.rOut < R0) :
    ∃ M1 : ℝ, AdmissibleRadialCutoff n R0 1 M1 (fun t : ℝ => f t) := by
  rcases ContDiffBump.exists_deriv_bound_on_Icc f R0 with ⟨M1, hM1⟩
  exact ⟨M1, ContDiffBump.admissibleRadialCutoff (n := n) f hRout hM1⟩

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
