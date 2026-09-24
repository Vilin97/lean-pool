/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Cutoff

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set Filter
open scoped Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private theorem vec3_norm_eq_native (v : Vec3) :
    vec3EuclideanNorm v = vecEuclideanNorm v := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

private theorem affine_fderiv (c : ℝ) (x₀ : Vec3) :
    fderiv ℝ (fun x : Vec3 => c • (x - x₀)) =
      fun _ => c • (ContinuousLinearMap.id ℝ Vec3) := by
  funext x
  change fderiv ℝ (c • (fun x : Vec3 => x - x₀)) x = _
  rw [fderiv_const_smul, fderiv_sub_const]
  have hid : fderiv ℝ (fun x : Vec3 => x) =
      fun _ => ContinuousLinearMap.id ℝ Vec3 := by
    funext y
    simp
  rw [hid]
  fun_prop

private theorem affine_iteratedFDeriv_bound (c : ℝ) (x₀ : Vec3)
    (x : Vec3) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y : Vec3 => c • (y - x₀)) x‖ ≤ |c| ^ n := by
  cases n with
  | zero => exact False.elim ((Nat.not_succ_le_zero 0) hn)
  | succ n =>
      cases n with
      | zero =>
          rw [norm_iteratedFDeriv_one, affine_fderiv]
          simp [norm_smul, ContinuousLinearMap.norm_id]
      | succ n =>
          rw [← norm_iteratedFDeriv_fderiv, affine_fderiv,
            iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]
          simp

def fixedCutoff : Vec3 → ℝ :=
  canonicalBallCutoff (0 : Vec3) (13 / 20) (3 / 4)

private theorem fixedCutoff_smooth :
    ContDiff ℝ (⊤ : ℕ∞) fixedCutoff := by
  simpa [fixedCutoff] using
    canonicalBallCutoff_smooth (0 : Vec3) (by norm_num) (by norm_num)

private theorem fixedCutoff_compact : HasCompactSupport fixedCutoff := by
  simpa [fixedCutoff] using
    canonicalBallCutoff_hasCompactSupport (x₀ := (0 : Vec3))
      (r := (13 / 20 : ℝ)) (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)

private theorem fixedCutoff_nonneg (x : Vec3) : 0 ≤ fixedCutoff x := by
  simpa [fixedCutoff] using
    canonicalBallCutoff_nonneg (0 : Vec3) (13 / 20) (3 / 4) x

private theorem fixedCutoff_le_one (x : Vec3) : fixedCutoff x ≤ 1 := by
  simpa [fixedCutoff] using
    canonicalBallCutoff_le_one (0 : Vec3) (13 / 20) (3 / 4) x

private theorem fixedCutoff_eq_one (x : Vec3)
    (hx : vecEuclideanNorm x < 13 / 20) :
    fixedCutoff x = 1 := by
  apply canonicalBallCutoff_eq_one_on_inner (x₀ := (0 : Vec3))
    (r := (13 / 20 : ℝ)) (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  simpa [sub_zero] using hx

private theorem cutoff_profile_bounds :
    ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i fixedCutoff y‖ ≤ B := by
  intro k
  exact fixedCutoff_compact.exists_bound_iteratedFDeriv
    fixedCutoff_smooth k

private theorem cutoff_norm_map (ρ : ℝ) (x₀ x : Vec3) :
    vecEuclideanNorm (ρ⁻¹ • (x - x₀)) =
      |ρ⁻¹| * vecEuclideanNorm (x - x₀) := by
  exact vecEuclideanNorm_smul _ _

private theorem inv_norm_lt_iff {ρ a n : ℝ} (hρ : 0 < ρ) :
    ρ⁻¹ * n < a ↔ n < a * ρ := by
  have hdiv : ρ⁻¹ * n = n / ρ := by
    rw [inv_mul_eq_div]
  rw [hdiv]
  exact div_lt_iff₀ hρ

private theorem cutoff_map_inner {ρ : ℝ} (hρ : 0 < ρ) (x₀ x : Vec3) :
    x ∈ vec3Ball x₀ (13 * ρ / 20) ↔
      ρ⁻¹ • (x - x₀) ∈ euclideanBall (0 : Vec3) (13 / 20) := by
  rw [mem_vec3Ball, mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
  simp only [sub_zero]
  rw [vec3_norm_eq_native, cutoff_norm_map, abs_inv, abs_of_pos hρ]
  convert (inv_norm_lt_iff (ρ := ρ) (a := 13 / 20)
    (n := vecEuclideanNorm (x - x₀)) hρ).symm using 1
  all_goals ring_nf

private theorem cutoff_map_outer {ρ : ℝ} (hρ : 0 < ρ) (x₀ x : Vec3) :
    ρ⁻¹ • (x - x₀) ∈ euclideanBall (0 : Vec3) (3 / 4) ↔
      x ∈ vec3Ball x₀ (3 * ρ / 4) := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num), mem_vec3Ball]
  simp only [sub_zero]
  rw [vec3_norm_eq_native, cutoff_norm_map, abs_inv, abs_of_pos hρ]
  convert inv_norm_lt_iff (ρ := ρ) (a := 3 / 4)
    (n := vecEuclideanNorm (x - x₀)) hρ using 1
  all_goals ring_nf

private theorem cutoff_map_affine_smooth {ρ : ℝ} (_ : 0 < ρ) (x₀ : Vec3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ρ⁻¹ • (x - x₀)) := by
  fun_prop

private theorem vec3_norm_add_le (a b : Vec3) :
    vec3EuclideanNorm (a + b) ≤
      vec3EuclideanNorm a + vec3EuclideanNorm b := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem native_norm_add_le (a b : Vec3) :
    vecEuclideanNorm (a + b) ≤
      vecEuclideanNorm a + vecEuclideanNorm b := by
  rw [← vec3_norm_eq_native, ← vec3_norm_eq_native,
    ← vec3_norm_eq_native]
  exact vec3_norm_add_le _ _

private theorem cutoff_geometry {ρ r : ℝ} (_ : 0 < ρ) (_ : 0 < r)
    (hhalf : r ≤ ρ / 2) (x₀ x y : Vec3)
    (hx : x ∈ vec3Ball x₀ r)
    (hy : y ∈ vec3Ball x₀ (3 * ρ / 4) \ vec3Ball x₀ (13 * ρ / 20)) :
    vec3EuclideanNorm (x - y) ≥ 3 * ρ / 20 := by
  have hxy : vec3EuclideanNorm (x - x₀) < r := mem_vec3Ball.mp hx
  have hyinner : ¬ vec3EuclideanNorm (y - x₀) < 13 * ρ / 20 := by
    simpa only [mem_vec3Ball] using hy.2
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) := by
    calc
      vec3EuclideanNorm (y - x₀) = vecEuclideanNorm (y - x₀) :=
        vec3_norm_eq_native _
      _ = vecEuclideanNorm ((y - x) + (x - x₀)) := by
        congr 1
        abel
      _ ≤ vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) :=
        native_norm_add_le _ _
      _ = vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) := by
        rw [vec3_norm_eq_native, vec3_norm_eq_native]
  have hdist : 3 * ρ / 20 ≤ vec3EuclideanNorm (y - x) := by
    by_contra hn
    have hlt : vec3EuclideanNorm (y - x) < 3 * ρ / 20 := lt_of_not_ge hn
    have hsum := add_lt_add hlt hxy
    have : vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) <
        13 * ρ / 20 := by
      calc
        _ < 3 * ρ / 20 + r := hsum
        _ ≤ 3 * ρ / 20 + ρ / 2 := by gcongr
        _ = 13 * ρ / 20 := by ring
    exact hyinner (lt_of_le_of_lt htri this)
  have hdist' : 3 * ρ / 20 ≤ vecEuclideanNorm (y - x) := by
    simpa only [vec3_norm_eq_native] using hdist
  have hrev : vecEuclideanNorm (y - x) = vecEuclideanNorm (x - y) := by
    unfold vecEuclideanNorm vecNormSq vecDot
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.sub_apply]
    ring
  rw [hrev] at hdist'
  simpa only [vec3_norm_eq_native] using hdist'

theorem exists_cutoff :
    ∃ C₁₀ : ℕ → ℝ, ∀ x₀ : Vec3, ∀ ρ : ℝ, 0 < ρ →
      ∃ η : Vec3 → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) η ∧
        HasCompactSupport η ∧
        (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
        (∀ x ∈ vec3Ball x₀ (13 * ρ / 20), η x = 1) ∧
        tsupport η ⊆ vec3Ball x₀ (3 * ρ / 4) ∧
        (∀ k x, ‖iteratedFDeriv ℝ k η x‖ ≤
          C₁₀ k * ρ ^ (-(k : ℝ))) := by
  choose B hBnonneg hB using cutoff_profile_bounds
  refine ⟨fun k => (k.factorial : ℝ) * B k, ?_⟩
  intro x₀ ρ hρ
  let η : Vec3 → ℝ := fun x => fixedCutoff (ρ⁻¹ • (x - x₀))
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact fixedCutoff_smooth.comp (cutoff_map_affine_smooth hρ x₀)
  have hηsupport : tsupport η ⊆ vec3Ball x₀ (3 * ρ / 4) := by
    change tsupport (fixedCutoff ∘ (fun y : Vec3 => ρ⁻¹ • (y - x₀))) ⊆ _
    intro x hx
    have harg : ρ⁻¹ • (x - x₀) ∈ tsupport fixedCutoff :=
      (tsupport_comp_subset_preimage fixedCutoff
        (cutoff_map_affine_smooth hρ x₀).continuous) hx
    exact (cutoff_map_outer hρ x₀ x).1 (by
      simpa [fixedCutoff] using
        canonicalBallCutoff_tsupport_subset_outer
          (x₀ := (0 : Vec3)) (r := (13 / 20 : ℝ)) (R := (3 / 4 : ℝ))
          (by norm_num) (by norm_num) harg)
  have hηcompact : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanClosedBall x₀ (R := 3 * ρ / 4) (by positivity))
    intro x hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    have hclosed := (mem_vec3Ball.mp
      (hηsupport ((subset_tsupport (f := η)) hx))).le
    simpa only [vec3_norm_eq_native] using hclosed
  refine ⟨η, hηsmooth, hηcompact, ?_, ?_, hηsupport, ?_⟩
  · intro x
    exact ⟨fixedCutoff_nonneg _, fixedCutoff_le_one _⟩
  · intro x hx
    have harg := (cutoff_map_inner hρ x₀ x).1 hx
    exact fixedCutoff_eq_one (ρ⁻¹ • (x - x₀)) (by
      simpa only [sub_zero] using
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 harg)
  · intro k x
    have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 =>
        fixedCutoff (ρ⁻¹ • (y - x₀))) := hηsmooth
    have hbound := norm_iteratedFDeriv_comp_le fixedCutoff_smooth
      (cutoff_map_affine_smooth hρ x₀) (by simp) x
      (C := B k) (D := ρ⁻¹) (fun i hi => hB k i hi _)
      (fun i hi hile => by
        simpa [abs_of_pos (inv_pos.mpr hρ)] using
          affine_iteratedFDeriv_bound ρ⁻¹ x₀ x i hi)
    change ‖iteratedFDeriv ℝ k (fixedCutoff ∘
      (fun y : Vec3 => ρ⁻¹ • (y - x₀))) x‖ ≤ _
    calc
      ‖iteratedFDeriv ℝ k η x‖ ≤
          (k.factorial : ℝ) * B k * (ρ⁻¹) ^ k := hbound
      _ = (k.factorial : ℝ) * B k * ρ ^ (-(k : ℝ)) := by
        have hpow : (ρ⁻¹ : ℝ) ^ k = ρ ^ (-(k : ℝ)) := by
          calc
            (ρ⁻¹ : ℝ) ^ k = (ρ⁻¹ : ℝ) ^ (k : ℝ) :=
              (Real.rpow_natCast (ρ⁻¹) k).symm
            _ = (ρ ^ (k : ℝ))⁻¹ := Real.inv_rpow hρ.le _
            _ = ρ ^ (-(k : ℝ)) := (Real.rpow_neg hρ.le _).symm
        rw [hpow]

theorem cutoff_annulus_separation
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    {x₀ x y : Vec3} (hx : x ∈ vec3Ball x₀ r)
    (hy : y ∈ vec3Ball x₀ (3 * ρ / 4) \ vec3Ball x₀ (13 * ρ / 20)) :
    vec3EuclideanNorm (x - y) ≥ 3 * ρ / 20 :=
  cutoff_geometry hρ hr hhalf x₀ x y hx hy

end CKN
