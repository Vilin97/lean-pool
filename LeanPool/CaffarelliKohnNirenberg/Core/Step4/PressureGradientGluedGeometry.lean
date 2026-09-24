/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersShift
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Small backward cylinders around an interior space-time point

Around a point of an open Euclidean ball and a time interior to the time set
there is a backward parabolic cylinder with rational radius and rational top
time, centred at a point of any prescribed dense set, whose closure lies in the
product of the ball and the time set, whose half-radius ball still contains the
point and lies in the ball, and whose time window contains the given time.
This is the geometric step that lets one apply a slice estimate on arbitrarily
small cylinders drawn from a fixed countable family.
-/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN.Core.Step4

/-- The triangle inequality for the Euclidean norm on `Vec3`. -/
private lemma norm_sub_triangle (a b c : Vec3) :
    vec3EuclideanNorm (a - c) ≤ vec3EuclideanNorm (a - b) + vec3EuclideanNorm (b - c) := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  have h : WithLp.toLp 2 (a - c) =
      WithLp.toLp 2 (a - b) + WithLp.toLp 2 (b - c) := by
    rw [← WithLp.toLp_add]
    congr 1
    abel
  rw [h]
  exact norm_add_le _ _

/-- Around a point `x` of an open Euclidean ball and a time `s` interior to an open time
set there is a backward parabolic cylinder with rational radius and rational top time,
centred at a point of any prescribed dense set `S`, whose half-radius ball contains `x`
and lies in the original ball, whose closure lies in the product of the ball and the time
set, and whose time window contains `s`. -/
theorem exists_small_cylinder_of_mem
    {x₀ : Vec3} {R : ℝ} {I : Set ℝ} (hI : IsOpen I)
    {S : Set Vec3} (hSd : Dense S)
    {x : Vec3} (hx : x ∈ vec3Ball x₀ R) {s : ℝ} (hs : s ∈ I) :
    ∃ (c : Vec3) (t₀ ρ : ℚ), c ∈ S ∧ 0 < (ρ : ℝ) ∧
      x ∈ vec3Ball c ((ρ : ℝ) / 2) ∧
      vec3Ball c ((ρ : ℝ) / 2) ⊆ vec3Ball x₀ R ∧
      closure (parabolicCylinder c (t₀ : ℝ) (ρ : ℝ)) ⊆ vec3Ball x₀ R ×ˢ I ∧
      s ∈ Set.Ioc ((t₀ : ℝ) - (ρ : ℝ) ^ 2) (t₀ : ℝ) := by
  have hxlt : vec3EuclideanNorm (x - x₀) < R := by
    rwa [mem_vec3Ball] at hx
  -- the distance from `x` to the boundary of the ball
  set d : ℝ := R - vec3EuclideanNorm (x - x₀) with hd
  have hdpos : 0 < d := by
    rw [hd]
    linarith only [hxlt]
  -- a spacing that keeps the cylinder in the ball and its time window in the time set
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hI s hs
  set m : ℝ := min (4 * d / 5) (min 1 δ) with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact lt_min (by linarith only [hdpos]) (lt_min (by norm_num) hδpos)
  obtain ⟨ρ, hρ0, hρm⟩ := exists_rat_btwn hmpos
  have hρ45 : (ρ : ℝ) < 4 * d / 5 := hρm.trans_le (min_le_left _ _)
  have hρ1 : (ρ : ℝ) < 1 :=
    (hρm.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hρδ : (ρ : ℝ) < δ :=
    (hρm.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hρsqpos : 0 < (ρ : ℝ) ^ 2 := pow_pos hρ0 2
  have hρsqδ : (ρ : ℝ) ^ 2 < δ := by
    have hlt : (ρ : ℝ) ^ 2 < (ρ : ℝ) := by
      have h := mul_lt_mul_of_pos_right hρ1 hρ0
      simpa [pow_two] using h
    linarith only [hlt, hρδ]
  -- a rational top time just above `s`
  obtain ⟨t₀, hslt, ht₀lt⟩ :=
    exists_rat_btwn (show s < s + (ρ : ℝ) ^ 2 / 2 by linarith only [hρsqpos])
  -- a centre drawn from the dense set, close to `x`
  have hxmem : x ∈ vec3Ball x ((ρ : ℝ) / 4) := by
    rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    linarith only [hρ0]
  obtain ⟨c, hcball, hcS⟩ :=
    hSd.inter_open_nonempty (vec3Ball x ((ρ : ℝ) / 4))
      (isOpen_vec3Ball x ((ρ : ℝ) / 4)) ⟨x, hxmem⟩
  have hcx : vec3EuclideanNorm (c - x) < (ρ : ℝ) / 4 := by
    rwa [mem_vec3Ball] at hcball
  refine ⟨c, t₀, ρ, hcS, hρ0, ?_, ?_, ?_, ?_⟩
  · -- the point lies in the half-radius ball
    rw [mem_vec3Ball, CKN.Foundation.Heat.vec3EuclideanNorm_sub_comm]
    linarith only [hcx, hρ0]
  · -- the half-radius ball lies in the original ball
    intro y hy
    rw [mem_vec3Ball] at hy ⊢
    have h1 := norm_sub_triangle y c x₀
    have h2 := norm_sub_triangle c x x₀
    have h3 : 3 * (ρ : ℝ) / 4 < d := by linarith only [hρ45, hdpos]
    linarith only [h1, h2, hy, hcx, hd, h3]
  · -- the closed cylinder lies in the product of the ball and the time set
    rintro ⟨y, t⟩ hp
    rw [closure_parabolicCylinder hρ0] at hp
    change vec3EuclideanNorm (y - c) ≤ (ρ : ℝ) ∧
      ((t₀ : ℝ) - (ρ : ℝ) ^ 2 ≤ t ∧ t ≤ (t₀ : ℝ)) at hp
    obtain ⟨hyn, hti₁, hti₂⟩ := hp
    change y ∈ vec3Ball x₀ R ∧ t ∈ I
    refine ⟨?_, ?_⟩
    · rw [mem_vec3Ball]
      have h1 := norm_sub_triangle y c x₀
      have h2 := norm_sub_triangle c x x₀
      have h5 : 5 * (ρ : ℝ) / 4 < d := by linarith only [hρ45]
      linarith only [h1, h2, hyn, hcx, hd, h5]
    · refine hδsub ?_
      rw [Real.ball_eq_Ioo]
      refine ⟨?_, ?_⟩
      · linarith only [hti₁, hslt, hρsqδ]
      · have hhalf : (ρ : ℝ) ^ 2 / 2 < δ := by linarith only [hρsqpos, hρsqδ]
        linarith only [hti₂, ht₀lt, hhalf]
  · -- the given time lies in the time window of the cylinder
    refine ⟨?_, le_of_lt hslt⟩
    linarith only [ht₀lt, hρsqpos]

end CKN.Core.Step4
