/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.BoundaryBasics

/-!
# Primitive cutoff realization

This module contains the primitive cutoff realization and the abstract
one-dimensional sharp-cutoff inputs.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The purely one-dimensional sharp-cutoff approximation step. -/
def WeakOneDimensionalSharpCutoffStep {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakRadialOneDimensionalIdentity Du R0 →
    WeakSharpCutoffLimitIdentity Du (0 : Domain n) R0

/-- Intermediate distributional form of the one-dimensional sharp-cutoff
argument. -/
def WeakOneDimensionalToDistributionStep {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakRadialOneDimensionalIdentity Du R0 →
    WeakSharpCutoffDistributionIdentity Du (0 : Domain n) R0

/-- After the one-dimensional radial identity is integrated by parts, the defect
pairs to zero against derivatives of compactly supported radial cutoffs. -/
def WeakOneDimensionalDefectDerivativeIdentity {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            (∫ rho in Ioo (0 : ℝ) R0,
              (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho) = 0

/-- The primitive-cutoff family needed in the one-dimensional sharp-cutoff
argument.  It says every smooth compactly supported test function in `(0, R0)`
can be represented, for pairing with the defect, as `-phi'` for an admissible
radial cutoff primitive. -/
def WeakOneDimensionalPrimitiveTestFamily {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ g : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g →
        tsupport g ⊆ Ioo (0 : ℝ) R0 →
          ∃ phi : ℝ → ℝ,
            Differentiable ℝ phi ∧
              ContDiff ℝ 1 phi ∧
                HasCompactSupport phi ∧
                  tsupport phi ⊆ Iio R0 ∧
                    (∫ rho : ℝ,
                        g rho • weakSharpCutoffDefect Du (0 : Domain n) rho)
                      =
                    (∫ rho in Ioo (0 : ℝ) R0,
                        (-deriv phi rho) *
                          weakSharpCutoffDefect Du (0 : Domain n) rho)

/-- A concrete primitive-cutoff realization: every smooth compactly supported
test function in `(0, R0)` is the negative derivative, on `(0, R0)`, of a
compactly supported radial cutoff.  This predicate contains only the
one-dimensional construction, independent of the map `Du`. -/
def WeakPrimitiveCutoffRealization (R0 : ℝ) : Prop :=
  ∀ g : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g →
        tsupport g ⊆ Ioo (0 : ℝ) R0 →
          ∃ phi : ℝ → ℝ,
            Differentiable ℝ phi ∧
              ContDiff ℝ 1 phi ∧
                HasCompactSupport phi ∧
                  tsupport phi ⊆ Iio R0 ∧
                    ConstNearOrigin phi ∧
                      (∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0),
                        -deriv phi rho = g rho)

/-- Construction of the primitive cutoff using the interval primitive
`t ↦ ∫ x in t..R0, g x` and a smooth bump on the left. -/
theorem weakPrimitiveCutoffRealization (R0 : ℝ) :
    WeakPrimitiveCutoffRealization R0 := by
  intro g hg_smooth hg_compact hg_support
  rcases (tsupport g).eq_empty_or_nonempty with h_empty | hne
  · have hg_zero_fun : g = 0 := tsupport_eq_empty_iff.mp h_empty
    refine ⟨0, differentiable_const (c := (0 : ℝ)), contDiff_const,
      HasCompactSupport.zero, ?_, ?_, ?_⟩
    · intro x hx
      simp at hx
    · exact ⟨1, by norm_num, by simp⟩
    · filter_upwards with rho
      simp [hg_zero_fun]
  · have hg_support_Iio : tsupport g ⊆ Iio R0 := fun x hx => (hg_support hx).2
    rcases exists_tsupport_subset_Iio_lt_of_hasCompactSupport
        hg_compact hg_support_Iio with
      ⟨U, hU_support, hU_lt_R0⟩
    rcases exists_pos_lt_tsupport_subset_Ioi_of_hasCompactSupport
        hg_compact hg_support with
      ⟨L, hL_pos, hL_support⟩
    rcases hne with ⟨z, hz⟩
    have hU_pos : 0 < U := (hg_support hz).1.trans (hU_support hz)
    let rIn : ℝ := (U + R0) / 2
    have hU_lt_rIn : U < rIn := by dsimp [rIn]; linarith
    have hrIn_lt_R0 : rIn < R0 := by dsimp [rIn]; linarith
    have hrIn_pos : 0 < rIn := hU_pos.trans hU_lt_rIn
    let rOut : ℝ := (rIn + R0) / 2
    have hrIn_lt_rOut : rIn < rOut := by dsimp [rOut]; linarith
    have hrOut_lt_R0 : rOut < R0 := by dsimp [rOut]; linarith
    let bump : ContDiffBump (0 : ℝ) :=
      { rIn := rIn
        rOut := rOut
        rIn_pos := hrIn_pos
        rIn_lt_rOut := hrIn_lt_rOut }
    let F : ℝ → ℝ := fun t => ∫ x : ℝ in t..R0, g x
    let phi : ℝ → ℝ := fun t => bump t * F t
    have hg_cont : Continuous g := hg_smooth.continuous
    have hF_c1 : ContDiff ℝ 1 F := by
      simpa [F] using contDiff_one_intervalPrimitive_left hg_cont R0
    have hbump_c1 : ContDiff ℝ 1 (fun t : ℝ => bump t) := bump.contDiff
    have hphi_c1 : ContDiff ℝ 1 phi := by
      simpa [phi] using hbump_c1.mul hF_c1
    have hphi_diff : Differentiable ℝ phi := hphi_c1.differentiable_one
    have hbump_compact : HasCompactSupport (fun t : ℝ => bump t) := bump.hasCompactSupport
    have hphi_compact : HasCompactSupport phi := by
      exact hbump_compact.mul_right (f' := F)
    have hphi_support : tsupport phi ⊆ Iio R0 := by
      intro x hx
      have hx_bump : x ∈ tsupport (fun t : ℝ => bump t) := by
        exact (tsupport_mul_subset_left
          (f := fun t : ℝ => bump t) (g := F)) (by simpa [phi] using hx)
      have hx_closed : x ∈ Metric.closedBall (0 : ℝ) rOut := by
        simpa [bump, ContDiffBump.tsupport_eq] using hx_bump
      have hx_abs_le : |x| ≤ rOut := by
        simpa [Metric.mem_closedBall, Real.dist_eq] using hx_closed
      have hx_le_abs : x ≤ |x| := le_abs_self x
      exact lt_of_le_of_lt (hx_le_abs.trans hx_abs_le) hrOut_lt_R0
    have hphi_const : ConstNearOrigin phi := by
      refine ⟨min L rIn, lt_min hL_pos hrIn_pos, ?_⟩
      intro t ht
      have ht_lt_L : t < L := by
        have ht_abs_lt_L : |t| < L := lt_of_lt_of_le ht (min_le_left L rIn)
        exact (le_abs_self t).trans_lt ht_abs_lt_L
      have ht_abs_lt_rIn : |t| < rIn :=
        lt_of_lt_of_le ht (min_le_right L rIn)
      have hbump_t : bump t = 1 := by
        have ht_closed : t ∈ Metric.closedBall (0 : ℝ) rIn := by
          simpa [Metric.mem_closedBall, Real.dist_eq] using
            (le_of_lt ht_abs_lt_rIn)
        exact bump.one_of_mem_closedBall ht_closed
      have hbump_zero : bump 0 = 1 := by
        have hzero_closed : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) rIn := by
          simp [Metric.mem_closedBall, hrIn_pos.le]
        exact bump.one_of_mem_closedBall hzero_closed
      have hF_t : F t = F 0 := by
        simpa [F] using
          intervalPrimitive_eq_intervalPrimitive_zero_of_tsupport_subset_Ioi
            (g := g) (L := L) (t := t) (b := R0)
            hg_cont hL_support hL_pos ht_lt_L
      simp [phi, hbump_t, hbump_zero, hF_t]
    have hF_deriv : ∀ rho : ℝ, deriv F rho = -g rho := by
      intro rho
      simpa [F] using intervalIntegral.deriv_integral_left
        (f := g) (a := rho) (b := R0)
        (hg_cont.intervalIntegrable rho R0)
        (hg_cont.stronglyMeasurableAtFilter (μ := volume) (l := 𝓝 rho))
        hg_cont.continuousAt
    have hderiv_on :
        ∀ rho : ℝ, rho ∈ Ioo (0 : ℝ) R0 → -deriv phi rho = g rho := by
      intro rho hrho
      by_cases hrho_lt_rIn : rho < rIn
      · have hrho_abs_lt : |rho| < rIn := by
          rw [abs_of_nonneg (le_of_lt hrho.1)]
          exact hrho_lt_rIn
        have hbump_event :
            (fun t : ℝ => bump t) =ᶠ[𝓝 rho] (fun _ : ℝ => 1) := by
          have hrho_ball : rho ∈ Metric.ball (0 : ℝ) rIn := by
            simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hrho_abs_lt
          filter_upwards [Metric.isOpen_ball.mem_nhds hrho_ball] with y hy
          have hy_closed : y ∈ Metric.closedBall (0 : ℝ) rIn :=
            Metric.ball_subset_closedBall hy
          exact bump.one_of_mem_closedBall hy_closed
        have hphi_event : phi =ᶠ[𝓝 rho] F := by
          filter_upwards [hbump_event] with y hy
          simp [phi, hy]
        have hderiv_phi : deriv phi rho = deriv F rho := hphi_event.deriv_eq
        rw [hderiv_phi, hF_deriv]
        ring
      · have hrIn_le_rho : rIn ≤ rho := le_of_not_gt hrho_lt_rIn
        have hU_lt_rho : U < rho := hU_lt_rIn.trans_le hrIn_le_rho
        have hF_event : F =ᶠ[𝓝 rho] (fun _ : ℝ => 0) := by
          have hrad : 0 < (rho - U) / 2 := by linarith
          filter_upwards [Metric.ball_mem_nhds rho hrad] with y hy
          have hy_abs : |y - rho| < (rho - U) / 2 := by
            simpa [Metric.mem_ball, Real.dist_eq] using hy
          have hy_gt_U : U < y := by
            have hsub_le : rho - y ≤ |y - rho| := by
              rw [abs_sub_comm]
              exact le_abs_self (rho - y)
            linarith
          exact intervalPrimitive_eq_zero_of_tsupport_subset_Iio
            (g := g) (U := U) (t := y) (b := R0)
            hU_support hy_gt_U (hU_lt_R0)
        have hphi_event : phi =ᶠ[𝓝 rho] (fun _ : ℝ => 0) := by
          filter_upwards [hF_event] with y hy
          simp [phi, hy]
        have hderiv_phi : deriv phi rho = 0 := by
          simpa using hphi_event.deriv_eq
        have hg_rho : g rho = 0 := by
          have hrho_not_support : rho ∉ tsupport g := by
            intro hrho_support
            exact not_lt_of_ge (le_of_lt hU_lt_rho) (hU_support hrho_support)
          exact image_eq_zero_of_notMem_tsupport hrho_not_support
        simp [hderiv_phi, hg_rho]
    refine ⟨phi, hphi_diff, hphi_c1, hphi_compact, hphi_support, hphi_const, ?_⟩
    exact (ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun rho hrho => hderiv_on rho hrho)

/-- The concrete primitive realization discharges the primitive test-family
interface used by the distributional sharp-cutoff argument. -/
theorem weakOneDimensionalPrimitiveTestFamily_of_realization {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrealize : WeakPrimitiveCutoffRealization R0) :
    WeakOneDimensionalPrimitiveTestFamily Du R0 := by
  intro g hg_smooth hg_compact hg_support
  rcases hrealize g hg_smooth hg_compact hg_support with
    ⟨phi, hphi_diff, hphi_cont, hphi_compact, hphi_support, _hphi_const, hderiv_ae⟩
  refine ⟨phi, hphi_diff, hphi_cont, hphi_compact, hphi_support, ?_⟩
  let defect : ℝ → ℝ := fun rho =>
    weakSharpCutoffDefect Du (0 : Domain n) rho
  have hg_zero :
      ∀ rho : ℝ, rho ∉ Ioo (0 : ℝ) R0 → g rho • defect rho = 0 := by
    intro rho hrho
    have hrho_not_support : rho ∉ tsupport g := by
      intro hrho_support
      exact hrho (hg_support hrho_support)
    have hg_rho : g rho = 0 := image_eq_zero_of_notMem_tsupport hrho_not_support
    simp [defect, hg_rho]
  calc
    (∫ rho : ℝ, g rho • weakSharpCutoffDefect Du (0 : Domain n) rho)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        g rho • weakSharpCutoffDefect Du (0 : Domain n) rho) := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Ioo (0 : ℝ) R0)
          (f := fun rho : ℝ =>
            g rho • weakSharpCutoffDefect Du (0 : Domain n) rho)
          hg_zero
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho) := by
        apply integral_congr_ae
        filter_upwards [hderiv_ae] with rho hderiv
        simp [hderiv, smul_eq_mul]

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
