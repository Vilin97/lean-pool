/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorDisplayBounds

/-!
# Liouville

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Heat

def liouvilleBall (n : ℕ) : Set Vec3 :=
  euclideanBall 0 ((n : ℝ) + 1)

private lemma liouvilleBall_measurable (n : ℕ) :
    MeasurableSet (liouvilleBall n) := by
  dsimp [liouvilleBall]
  exact (isOpen_lt
    (contDiff_euclideanSqDist_left (0 : Vec3)).continuous continuous_const).measurableSet

private lemma liouville_weaklyHarmonicOn_ball
    {H : Vec3 → ℝ} (hweak : WeaklyHarmonicOn Set.univ H)
    {ρ : ℝ} (_ : 0 < ρ) :
    WeaklyHarmonicOn (euclideanBall (0 : Vec3) ρ) H := by
  intro ψ hψ hψc hψU
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [spatialLaplacian_zero_off hψU hx, mul_zero])]
  simpa only [Measure.restrict_univ] using
    hweak ψ hψ hψc (hψU.trans (Set.subset_univ _))

private lemma liouvilleBall_subset (n : ℕ) (k : ℕ) :
    liouvilleBall n ⊆ euclideanBall (0 : Vec3)
      (2 * ((n : ℝ) + (k : ℝ) + 2) / 2) := by
  intro x hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  norm_num [liouvilleBall] at hx' ⊢
  nlinarith only [hx']

private lemma liouvilleRadius_pos (n k : ℕ) :
    0 < 2 * ((n : ℝ) + (k : ℝ) + 2) := by
  positivity

private lemma liouvilleRadius_ge_one (n k : ℕ) :
    1 ≤ 2 * ((n : ℝ) + (k : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith only [hn, hk]

private lemma liouvilleRadius_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => 2 * ((n : ℝ) + (k : ℝ) + 2)) atTop atTop := by
  have hk : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun k : ℕ => (n : ℝ) + (k : ℝ) + 2)
      atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [hk.eventually_ge_atTop (b - (n : ℝ) - 2)] with k hk
    linarith only [hk]
  simpa [mul_comm] using hadd.atTop_mul_const (show (0 : ℝ) < 2 by norm_num)

private lemma liouville_growth_factor_tendsto (n : ℕ) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) :
    Tendsto (fun k : ℕ =>
      K * ((2 * ((n : ℝ) + (k : ℝ) + 2)) ^ 2)⁻¹ *
        (C * (1 + 2 * ((n : ℝ) + (k : ℝ) + 2)))) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun k => 2 * ((n : ℝ) + (k : ℝ) + 2)
  have hR : Tendsto R atTop atTop := by
    exact liouvilleRadius_tendsto n
  have hRinv : Tendsto (fun k => (R k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hR
  have hRnonzero : ∀ k, R k ≠ 0 := by
    intro k
    exact (ne_of_gt (liouvilleRadius_pos n k))
  have hRbound : ∀ k, 1 ≤ R k := by
    intro k
    exact liouvilleRadius_ge_one n k
  have hupper : ∀ k, K * (R k ^ 2)⁻¹ * (C * (1 + R k)) ≤
      (2 * K * C) * (R k)⁻¹ := by
    intro k
    have hRk := hRbound k
    have hRkpos : 0 < R k := (liouvilleRadius_pos n k)
    have hfrac : (R k ^ 2)⁻¹ * (1 + R k) ≤ 2 * (R k)⁻¹ := by
      field_simp [hRnonzero k]
      nlinarith only [hRk, hRkpos]
    calc
      K * (R k ^ 2)⁻¹ * (C * (1 + R k)) =
          (K * C) * ((R k ^ 2)⁻¹ * (1 + R k)) := by ring
      _ ≤ (K * C) * (2 * (R k)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hfrac (mul_nonneg hK hC)
      _ = (2 * K * C) * (R k)⁻¹ := by ring
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have hmajor : Tendsto (fun k : ℕ => (2 * K * C) * (R k)⁻¹)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hRinv :
        Tendsto (fun k : ℕ => (2 * K * C) * (R k)⁻¹)
          atTop (𝓝 ((2 * K * C) * 0)))
  have hresult := squeeze_zero' (f := fun k : ℕ =>
    K * (R k ^ 2)⁻¹ * (C * (1 + R k)))
    (Eventually.of_forall (fun k => by positivity))
    (Eventually.of_forall hupper) hmajor
  simpa only [R] using hresult

private lemma liouville_ball_zero_of_growth
    {H : Vec3 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hweak : WeaklyHarmonicOn Set.univ H)
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ))
    (n : ℕ) :
    H =ᵐ[volume.restrict (liouvilleBall n)] 0 := by
  let R : ℕ → ℝ := fun k => 2 * ((n : ℝ) + (k : ℝ) + 2)
  let G : ℕ → Vec3 → ℝ := fun k => Classical.choose
    (weakly_harmonic_interior_smooth
      (liouvilleRadius_pos n k) (hmem (R k) (liouvilleRadius_pos n k))
      (by
        intro ψ hψ hψc hψsub
        exact liouville_weaklyHarmonicOn_ball hweak
          (liouvilleRadius_pos n k) ψ hψ hψc hψsub))
  have hGspec : ∀ k,
      ContDiffOn ℝ (1 : ℕ∞) (G k)
        (euclideanBall (0 : Vec3) (R k / 2)) ∧
      H =ᵐ[volume.restrict (euclideanBall (0 : Vec3) (R k / 2))] G k ∧
      (∀ x ∈ euclideanBall (0 : Vec3) (R k / 2),
        |G k x| ≤ weakHarmonicInteriorSupConstant *
          (R k ^ 2)⁻¹ * lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) (R k)))) := by
    intro k
    have hs := Classical.choose_spec
      (weakly_harmonic_interior_smooth
        (liouvilleRadius_pos n k) (hmem (R k) (liouvilleRadius_pos n k))
        (by
          intro ψ hψ hψc hψsub
          exact liouville_weaklyHarmonicOn_ball hweak
            (liouvilleRadius_pos n k) ψ hψ hψc hψsub))
    simpa only [G, R] using ⟨hs.1, hs.2.1, hs.2.2.1⟩
  have hbound : ∀ k, ∀ᵐ x ∂volume.restrict (liouvilleBall n),
      |H x| ≤ weakHarmonicInteriorSupConstant * (R k ^ 2)⁻¹ *
        (C * (1 + R k)) := by
    intro k
    have hsub := liouvilleBall_subset n k
    have hEq := ae_restrict_of_ae_restrict_of_subset hsub (hGspec k).2.1
    filter_upwards [hEq, ae_restrict_mem (liouvilleBall_measurable n)] with x hx hxmem
    have hxG := (hGspec k).2.2 x (hsub hxmem)
    rw [← hx] at hxG
    exact hxG.trans (mul_le_mul_of_nonneg_left
      (hgrowth (R k) (liouvilleRadius_pos n k))
      (mul_nonneg weakHarmonicInteriorSupConstant_nonneg (by positivity)))
  have hall : ∀ᵐ x ∂volume.restrict (liouvilleBall n), ∀ k,
      |H x| ≤ weakHarmonicInteriorSupConstant * (R k ^ 2)⁻¹ *
        (C * (1 + R k)) :=
    (ae_all_iff).2 hbound
  filter_upwards [hall] with x hx
  have hlim' : Tendsto (fun k : ℕ =>
      weakHarmonicInteriorSupConstant * (R k ^ 2)⁻¹ *
        (C * (1 + R k))) atTop (𝓝 0) := by
    simpa only [R] using liouville_growth_factor_tendsto n hC
      weakHarmonicInteriorSupConstant_nonneg
  have habs' : |H x| ≤ 0 := ge_of_tendsto hlim'
    (Eventually.of_forall hx)
  exact abs_eq_zero.mp (le_antisymm habs' (abs_nonneg _))

private lemma liouville_balls_cover :
    (⋃ n : ℕ, liouvilleBall n) = (Set.univ : Set Vec3) := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_gt (vec3EuclideanNorm x)
  refine ⟨n, (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2 ?_⟩
  have hn' : vecEuclideanNorm (x - 0) < (n : ℝ) := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two,
      sub_zero] using hn
  have hn1 : (n : ℝ) < (n : ℝ) + 1 := by
    linarith only [show (0 : ℝ) < 1 by norm_num]
  exact hn'.trans hn1

/-- A weakly harmonic function with at most linear local `L^{3/2}` growth is
    zero almost everywhere. The proof uses the smooth local representative and
    its scale-dependent interior sup estimate on expanding balls. -/
theorem weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth
    {H : Vec3 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hweak : WeaklyHarmonicOn Set.univ H)
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    H =ᵐ[volume] 0 := by
  have hlocal : ∀ n : ℕ, H =ᵐ[volume.restrict (liouvilleBall n)] 0 := by
    intro n
    exact liouville_ball_zero_of_growth hC hmem hweak hgrowth n
  rw [show volume = volume.restrict (Set.univ : Set Vec3) by
    simp only [Measure.restrict_univ]]
  rw [← liouville_balls_cover]
  exact (ae_eq_restrict_iUnion_iff (fun n : ℕ => liouvilleBall n)
    H 0).2 hlocal

end CKN.Foundation.Heat
