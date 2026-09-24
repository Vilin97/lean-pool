/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Cylinder
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Admissibility

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

/-- The globally defined product used for the backward heat test. -/
def backwardHeatCutoff (η : Vec3 × ℝ → ℝ) (x₀ : Vec3) (t₀ r : ℝ)
    (z : Vec3 × ℝ) : ℝ :=
  η z * if z.2 - t₀ < r ^ 2 then
    backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) else 0

private lemma backwardHeat_cutoff_contDiff
    (η : Vec3 × ℝ → ℝ) (x₀ : Vec3) (t₀ r : ℝ) (_ : 0 < r)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηtime : tsupport η ⊆ {z : Vec3 × ℝ | z.2 < t₀ + r ^ 2}) :
    ContDiff ℝ (⊤ : ℕ∞) (backwardHeatCutoff η x₀ t₀ r) := by
  let s : Set (Vec3 × ℝ) := {z | z.2 - t₀ < r ^ 2}
  have hs : IsOpen s := by
    exact isOpen_lt (continuous_snd.sub continuous_const) continuous_const
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (z.1 - x₀, r ^ 2 - (z.2 - t₀))) := by
    fun_prop
  have hheat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ =>
        heatKernel (z.1 - x₀) (r ^ 2 - (z.2 - t₀))) s := by
    have hcomp := heatKernel_contDiffOn_pos.comp
      (show ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun z : Vec3 × ℝ => (z.1 - x₀, r ^ 2 - (z.2 - t₀))) s by
        fun_prop) (by
      intro z hz
      change z.2 - t₀ < r ^ 2 at hz
      exact ⟨mem_univ _, sub_pos.mpr hz⟩)
    have hcomp' := hcomp.of_le (show (⊤ : ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
    simpa only [Function.comp_def] using hcomp'
  have hψ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ =>
        backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀)) s := by
    have hconst : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 × ℝ => r ^ 2) := contDiff_const
    have hconstOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Vec3 × ℝ => r ^ 2) s :=
      hconst.contDiffOn
    have hmul := hconstOn.mul hheat
    simpa only [backwardHeatTestFunction, Function.comp_apply] using hmul
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ s
  · have hprod : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : Vec3 × ℝ =>
          η y * backwardHeatTestFunction r (y.1 - x₀) (y.2 - t₀)) z :=
      hη.contDiffAt.mul ((hψ z hz).contDiffAt (hs.mem_nhds hz))
    apply hprod.congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hz] with y hy
    change y.2 - t₀ < r ^ 2 at hy
    simp [backwardHeatCutoff, hy]
  · have hznot : z ∉ tsupport η := by
      intro hzη
      have hle : r ^ 2 ≤ z.2 - t₀ := le_of_not_gt hz
      have hlt : z.2 < t₀ + r ^ 2 := hηtime hzη
      linarith only [hle, hlt]
    have hηzero : ∀ᶠ y in 𝓝 z, η y = 0 := by
      filter_upwards [isClosed_tsupport η |>.isOpen_compl.mem_nhds hznot] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
    filter_upwards [hηzero] with y hy
    simp only [backwardHeatCutoff, hy, zero_mul]

/-- The truncated backward heat product is an admissible nonnegative test function.

The hypotheses expose the cutoff properties supplied by the space-time cutoff
construction: compact support, location in the domain, time support at or before
`t₀`, and nonnegativity. -/
theorem backwardHeat_cutoff_testFunction
    {Ω : Set Vec3} {I : Set ℝ} (η : Vec3 × ℝ → ℝ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηΩI : tsupport η ⊆ spaceTimeSet Ω I)
    (hηtime : tsupport η ⊆ {z : Vec3 × ℝ | z.2 < t₀ + r ^ 2})
    (hηnonneg : ∀ z, 0 ≤ η z) :
    backwardHeatCutoff η x₀ t₀ r ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
      (∀ z, 0 ≤ backwardHeatCutoff η x₀ t₀ r z) := by
  have hcont := backwardHeat_cutoff_contDiff η x₀ t₀ r hr hη hηtime
  have hts : tsupport (backwardHeatCutoff η x₀ t₀ r) ⊆ tsupport η := by
    exact tsupport_mul_subset_left
  have hcompact : HasCompactSupport (backwardHeatCutoff η x₀ t₀ r) :=
    hηc.mono' (subset_tsupport _ |>.trans hts)
  have htest : backwardHeatCutoff η x₀ t₀ r ∈
      spaceTimeTestFunction (V := ℝ) Ω I := ⟨hcont, hcompact, hts.trans hηΩI⟩
  refine ⟨htest, ?_⟩
  intro z
  unfold backwardHeatCutoff
  split_ifs with hz
  · exact mul_nonneg (hηnonneg z) (backwardHeatTestFunction_nonneg hr hz)
  · simp

end CKN
