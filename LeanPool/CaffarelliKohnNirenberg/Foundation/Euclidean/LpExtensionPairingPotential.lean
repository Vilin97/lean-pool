/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2GlobalBounds
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Lp Extension Pairing Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- The Newtonian potential of a smooth compactly supported datum on `ℝ³` lies in
`L⁶(ℝ³)` (paper label: the endpoint `L⁶` membership of the pressure potential used in the
elliptic `L^p` extension estimates). The potential is bounded on the closed ball of radius
`2R` containing the support and decays like `C / ‖x‖` beyond it, so the single bound
`|Φ x| ≤ C / (1 + ‖x‖)` dominates it; since `6 > 3` the profile `(1 + ‖x‖)⁻⁶` is integrable. -/
theorem pressureNewtonianPotential_memLp_six {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    MemLp (pressureNewtonianPotential F) (ENNReal.ofReal (6 : ℝ)) volume := by
  obtain ⟨R, hRpos, hR1, hSupp⟩ := pressure_potential_compact_radius hFc
  have hcont : Continuous (pressureNewtonianPotential F) :=
    (pressureNewtonianPotential_smooth hF hFc).continuous
  -- The total mass of the datum and the associated tail constant.
  set J : ℝ := ∫ y, |F y| with hJdef
  have hJnonneg : 0 ≤ J := by
    rw [hJdef]
    exact integral_nonneg (fun y => abs_nonneg _)
  set A : ℝ := 2 * (4 * Real.pi)⁻¹ * J with hAdef
  have hAnonneg : 0 ≤ A := by
    rw [hAdef]
    positivity
  -- Boundedness on the closed ball of radius `2R`.
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_closedBall (0 : Vec3) (2 * R)).exists_bound_of_continuousOn
      hcont.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hMnonneg : 0 ≤ M := le_max_right _ _
  have hMball : ∀ x ∈ Metric.closedBall (0 : Vec3) (2 * R),
      |pressureNewtonianPotential F x| ≤ M := by
    intro x hx
    have h1 : ‖pressureNewtonianPotential F x‖ ≤ M₀ := hM₀ x hx
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  -- The far-field decay converts to the stated `A / ‖x‖` profile.
  have htail : ∀ x : Vec3, 2 * R ≤ ‖x‖ →
      |pressureNewtonianPotential F x| ≤ A / ‖x‖ := by
    intro x hx
    calc
      |pressureNewtonianPotential F x| ≤
          (2 * (4 * Real.pi)⁻¹ / ‖x‖) * ∫ y, |F y| :=
        pressure_potential_tail_bound hF hFc hRpos hSupp hx
      _ = A / ‖x‖ := by
        rw [hAdef, hJdef, div_mul_eq_mul_div]
  -- A single global bound `|Φ x| ≤ C / (1 + ‖x‖)`.
  set C : ℝ := max (M * (1 + 2 * R)) (2 * A) with hCdef
  have hCnonneg : 0 ≤ C := by
    rw [hCdef]
    exact le_trans (by positivity : 0 ≤ M * (1 + 2 * R)) (le_max_left _ _)
  have hCbound : ∀ x : Vec3,
      |pressureNewtonianPotential F x| ≤ C / (1 + ‖x‖) := by
    intro x
    have hden_pos : 0 < 1 + ‖x‖ := by positivity
    rcases le_total ‖x‖ (2 * R) with hx | hx
    · have hxball : x ∈ Metric.closedBall (0 : Vec3) (2 * R) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx
      have h1 := hMball x hxball
      have h2 : M ≤ C / (1 + ‖x‖) := by
        rw [le_div_iff₀ hden_pos]
        have hstep : M * (1 + ‖x‖) ≤ M * (1 + 2 * R) :=
          mul_le_mul_of_nonneg_left (by linarith only [hx]) hMnonneg
        exact hstep.trans (le_max_left _ _)
      exact h1.trans h2
    · have hxge : 2 * R ≤ ‖x‖ := hx
      have h1 := htail x hxge
      have h2 : A / ‖x‖ ≤ C / (1 + ‖x‖) := by
        have hxpos : 0 < ‖x‖ := by
          have h2R : 0 < 2 * R := by positivity
          linarith only [h2R, hx]
        rw [div_le_div_iff₀ hxpos hden_pos]
        have hxone : 1 ≤ ‖x‖ := by
          have h2R : 2 ≤ 2 * R := by linarith only [hR1]
          linarith only [h2R, hxge]
        have hAC : 2 * A ≤ C := by
          rw [hCdef]
          exact le_max_right _ _
        have hstep1 : A * (1 + ‖x‖) ≤ A * (2 * ‖x‖) :=
          mul_le_mul_of_nonneg_left (by linarith only [hxone]) hAnonneg
        have hstep2 : A * (2 * ‖x‖) ≤ C * ‖x‖ := by
          nlinarith only [hAC, hAnonneg, norm_nonneg x]
        linarith only [hstep1, hstep2]
      exact h1.trans h2
  -- Membership via integrability of the `6`-th power.
  have hp0 : (ENNReal.ofReal (6 : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    norm_num
  have hptop : (ENNReal.ofReal (6 : ℝ)) ≠ ∞ := ENNReal.ofReal_ne_top
  refine (integrable_norm_rpow_iff hcont.aestronglyMeasurable hp0 hptop).mp ?_
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6)]
  have hfin : (Module.finrank ℝ Vec3 : ℝ) < 6 := by
    rw [Module.finrank_fin_fun]
    norm_num
  have hdom : Integrable
      (fun x : Vec3 => C ^ (6 : ℝ) * (1 + ‖x‖) ^ (-(6 : ℝ))) volume := by
    simpa only [smul_eq_mul] using
      (integrable_one_add_norm (μ := volume) (E := Vec3) (r := 6) hfin).const_mul
        (C ^ (6 : ℝ))
  have hmeas : AEStronglyMeasurable
      (fun x : Vec3 => ‖pressureNewtonianPotential F x‖ ^ (6 : ℝ)) volume :=
    (hcont.norm.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 6))).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards [] with x
  have hxden : 0 ≤ 1 + ‖x‖ := by positivity
  have h1 : |pressureNewtonianPotential F x| ^ (6 : ℝ) ≤
      (C / (1 + ‖x‖)) ^ (6 : ℝ) :=
    Real.rpow_le_rpow (abs_nonneg _) (hCbound x) (by norm_num)
  have h2 : (C / (1 + ‖x‖)) ^ (6 : ℝ) =
      C ^ (6 : ℝ) / (1 + ‖x‖) ^ (6 : ℝ) :=
    Real.div_rpow hCnonneg hxden 6
  have h3 : C ^ (6 : ℝ) / (1 + ‖x‖) ^ (6 : ℝ) =
      C ^ (6 : ℝ) * (1 + ‖x‖) ^ (-(6 : ℝ)) := by
    rw [Real.rpow_neg hxden, div_eq_mul_inv]
  have hgnorm : ‖‖pressureNewtonianPotential F x‖ ^ (6 : ℝ)‖ =
      |pressureNewtonianPotential F x| ^ (6 : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) (6 : ℝ)), Real.norm_eq_abs]
  rw [hgnorm]
  exact h1.trans (le_of_eq (h2.trans h3))

end CKN.Foundation.Euclidean
