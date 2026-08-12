/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Dbar.PlanarPoU
import LeanPool.JacobianDiffgeo.Dbar.SolveDisk

/-!
# Planar Cousin: cocycle splittings (`Jacobian/Dbar/PlanarCousin.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` §4.5, §7.2). Mathlib-only, planar,
project-independent (design D10).

`exists_smooth_splitting`: `H¹(finite cover of open `V`, sheaf of smooth functions) = 0`
(Forster 12.6, planar) — PoU-weighted average splits any smooth additive cocycle.
`exists_holo_splitting_ball`: Forster 13.4 (disk Cousin I) — correct the smooth splitting by a
`dbar`-solution (13.2/`SolveDisk`) to make it holomorphic.

Cocycle convention matched to cech's `d0` (`(d0 h)_{ij} = h_j − h_i`) and `Z1.rel_res`
(`f_{jk} − f_{ik} + f_{ij} = 0`, i.e. `f i k = f i j + f j k`).
-/

noncomputable section

open scoped ContDiff
open Set Filter Topology

namespace RS

variable {n : ℕ} {W : Fin n → Set ℂ} {f : Fin n → Fin n → ℂ → ℂ}

/-- Smooth splitting: `H¹(finite cover of open `V`, ℰ) = 0` (Forster 12.6 planar). -/
theorem exists_smooth_splitting {V : Set ℂ} (hV : IsOpen V) (hWo : ∀ i, IsOpen (W i))
    (hWV : ∀ i, W i ⊆ V) (hcov : V ⊆ ⋃ i, W i)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (f i j) (W i ∩ W j))
    (hcoc : ∀ i j k, ∀ z ∈ W i ∩ W j ∩ W k, f i k z = f i j z + f j k z) :
    ∃ h : Fin n → ℂ → ℂ, (∀ i, ContDiffOn ℝ ∞ (h i) (W i)) ∧
      ∀ i j, ∀ z ∈ W i ∩ W j, f i j z = h j z - h i z := by
  obtain ⟨ψ, hψ_cd, _hψ_nonneg, hψ_sum, hψ_supp, hψ_van⟩ :=
    exists_smooth_partition_of_finite_cover hV hWo hWV hcov
  refine ⟨fun i z => ∑ k, (W k).indicator (fun z => ψ k z • f k i z) z, ?_, ?_⟩
  · intro i
    apply ContDiffOn.sum
    intro k _
    exact contDiffOn_indicator_smul_of_eventually_zero (hWo i) (hWo k) (hWV i)
      (hψ_cd k) ((Set.inter_comm (W i) (W k)) ▸ hf k i) (fun z hz => hψ_van k z (hWV i hz))
  · intro i j z hz
    change f i j z = ∑ k, (W k).indicator (fun z => ψ k z • f k j z) z -
        ∑ k, (W k).indicator (fun z => ψ k z • f k i z) z
    have hstep : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        (W k).indicator (fun z => ψ k z • f k j z) z -
          (W k).indicator (fun z => ψ k z • f k i z) z = ψ k z • f i j z := by
      intro k _
      by_cases hk : z ∈ W k
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
        have hcoc' := hcoc k i j z ⟨⟨hk, hz.1⟩, hz.2⟩
        rw [hcoc']
        module
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]
        have hψk0 : ψ k z = 0 := by
          by_contra hne
          exact hk (hψ_supp k (by simpa [Function.mem_support] using hne))
        simp [hψk0]
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hstep, ← Finset.sum_smul,
      hψ_sum z (hWV i hz.1), one_smul]

/-- Holomorphic splitting on a ball (Forster 13.4, planar core; = disk Cousin I). -/
theorem exists_holo_splitting_ball {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hWo : ∀ i, IsOpen (W i)) (hWb : ∀ i, W i ⊆ Metric.ball c R)
    (hcov : Metric.ball c R ⊆ ⋃ i, W i)
    (hf : ∀ i j, DifferentiableOn ℂ (f i j) (W i ∩ W j))
    (hcoc : ∀ i j k, ∀ z ∈ W i ∩ W j ∩ W k, f i k z = f i j z + f j k z) :
    ∃ u : Fin n → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (u i) (W i)) ∧
      ∀ i j, ∀ z ∈ W i ∩ W j, f i j z = u j z - u i z := by
  classical
  have hf_cd : ∀ i j, ContDiffOn ℝ ∞ (f i j) (W i ∩ W j) := fun i j =>
    (((hf i j).analyticOnNhd ((hWo i).inter (hWo j))).contDiffOn
      (((hWo i).inter (hWo j)).uniqueDiffOn)).restrict_scalars ℝ
  obtain ⟨hsplit, hsplit_cd, hsplit_diff⟩ :=
    exists_smooth_splitting Metric.isOpen_ball hWo hWb hcov hf_cd hcoc
  -- The `wirtingerDbar` of the smooth splitting is well-defined across overlaps.
  have hagree : ∀ i j, ∀ z ∈ W i ∩ W j,
      wirtingerDbar (hsplit i) z = wirtingerDbar (hsplit j) z := by
    intro i j z hz
    have hi_diff : DifferentiableAt ℝ (hsplit i) z :=
      ((hsplit_cd i).contDiffAt ((hWo i).mem_nhds hz.1)).differentiableAt (by norm_num)
    have hj_diff : DifferentiableAt ℝ (hsplit j) z :=
      ((hsplit_cd j).contDiffAt ((hWo j).mem_nhds hz.2)).differentiableAt (by norm_num)
    have hdiff : DifferentiableAt ℂ (hsplit j - hsplit i) z := by
      apply DifferentiableOn.differentiableAt _ (((hWo i).inter (hWo j)).mem_nhds hz)
      apply DifferentiableOn.congr (hf i j)
      intro w hw
      show (hsplit j - hsplit i) w = f i j w
      rw [Pi.sub_apply]
      exact (hsplit_diff i j w hw).symm
    have hzero : wirtingerDbar (hsplit j - hsplit i) z = 0 :=
      wirtingerDbar_eq_zero_of_differentiableAt _ z hdiff
    rw [wirtingerDbar_sub _ _ z hj_diff hi_diff] at hzero
    linear_combination -hzero
  set H : ℂ → ℂ := fun z =>
    if h : ∃ i, z ∈ W i then wirtingerDbar (hsplit h.choose) z else 0 with hH_def
  have hH_eq : ∀ j, ∀ z ∈ W j, H z = wirtingerDbar (hsplit j) z := by
    intro j z hz
    have hex : ∃ i, z ∈ W i := ⟨j, hz⟩
    rw [hH_def]
    simp only [dite_eq_left hex]
    exact hagree hex.choose j z ⟨hex.choose_spec, hz⟩
  have hH_cd : ContDiffOn ℝ ∞ H (Metric.ball c R) := by
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hz)
    have hcdOn : ContDiffOn ℝ ∞ (wirtingerDbar (hsplit j)) (W j) :=
      contDiffOn_wirtingerDbar (hsplit j) (hWo j) (hsplit_cd j)
    have hcdAt : ContDiffAt ℝ ∞ (wirtingerDbar (hsplit j)) z :=
      hcdOn.contDiffAt ((hWo j).mem_nhds hj)
    have hHeqAt : H =ᶠ[nhds z] wirtingerDbar (hsplit j) := by
      filter_upwards [(hWo j).mem_nhds hj] with w hw
      exact hH_eq j w hw
    exact (hcdAt.congr_of_eventuallyEq hHeqAt).contDiffWithinAt
  obtain ⟨u₀, hu₀_cd, hu₀_dbar⟩ := exists_dbar_solution_ball H c R hR hH_cd
  refine ⟨fun i z => hsplit i z - u₀ z, ?_, ?_⟩
  · intro i
    have hi_diff : ∀ z ∈ W i, DifferentiableAt ℝ (hsplit i) z := fun z hz =>
      ((hsplit_cd i).contDiffAt ((hWo i).mem_nhds hz)).differentiableAt (by norm_num)
    have hu₀_diff : ∀ z ∈ W i, DifferentiableAt ℝ u₀ z := fun z hz =>
      (hu₀_cd.contDiffAt (Metric.isOpen_ball.mem_nhds (hWb i hz))).differentiableAt (by norm_num)
    have hzero : ∀ z ∈ W i, wirtingerDbar (hsplit i - u₀) z = 0 := by
      intro z hz
      rw [wirtingerDbar_sub _ _ z (hi_diff z hz) (hu₀_diff z hz), hu₀_dbar z (hWb i hz),
        hH_eq i z hz, sub_self]
    have hdiffOn : DifferentiableOn ℂ (hsplit i - u₀) (W i) :=
      differentiableOn_of_wirtingerDbar_eq_zero (hsplit i - u₀) (hWo i)
        (fun z hz => (hi_diff z hz).sub (hu₀_diff z hz)) hzero
    apply hdiffOn.congr
    intro z _
    rfl
  · intro i j z hz
    change f i j z = (hsplit j z - u₀ z) - (hsplit i z - u₀ z)
    have := hsplit_diff i j z hz
    linear_combination this

end RS

end
