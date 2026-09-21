/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectProjectedTail
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticProjectionRemainder
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectScaleTails

/-!
# Projection bridge for the direct quadratic scale outputs

This file identifies the literal fixed-scale output in the direct proof with
one convolution of the quadratic scale kernel against the corresponding
assembled input. It also records the pointwise and local-mass estimates for
that assembled input which are needed by the projection-remainder argument.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectProjectionBridge

open KrauseLaceyQuadraticDirectPartition
open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectPositivePairing
open KrauseLaceyQuadraticDirectScaleEnergy
open KrauseLaceyQuadraticDirectScaleTails
open KrauseLaceyQuadraticProjectionRemainder
open KrauseLaceyQuadraticSmoothProjection


noncomputable
section

/-- Classical equality for the interval indices in the projection bridge. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- The input to the genuine quadratic convolution at one fixed output scale.
The ambient family `S` continues to define every smallest selected region. -/
def directScaleInput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (k s : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ A.filter (fun I ↦ scale I = k), offsetGroupedInput S scale f I s x

theorem integrable_directScaleInput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    Integrable (directScaleInput S A scale f k s) := by
  unfold directScaleInput
  apply integrable_finsetSum
  intro I hI
  exact integrable_offsetGroupedInput S scale f I s

theorem memLp_two_directScaleInput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    MemLp (directScaleInput S A scale f k s) 2 volume := by
  unfold directScaleInput
  apply memLp_finsetSum
  intro I hI
  exact memLp_two_offsetGroupedInput S scale f I s

/-- A scale absent from the retained interval family has identically zero
assembled input. This lets later residue estimates ignore absent scales
without imposing the scale-gap hypothesis on them. -/
theorem directScaleInput_eq_zero_of_not_mem_image
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (k s : ℤ) (hk : k ∉ A.image scale) :
    directScaleInput S A scale f k s = 0 := by
  funext x
  unfold directScaleInput
  apply Finset.sum_eq_zero
  intro I hI
  exact (hk (Finset.mem_image.mpr ⟨I, (Finset.mem_filter.mp hI).1,
    (Finset.mem_filter.mp hI).2⟩)).elim

/-- At one fixed scale the literal sum of localized outputs is exactly the
quadratic convolution of the assembled scale input. -/
theorem directScaleOutput_eq_quadraticScaleOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    directScaleOutput S A scale f k s =
      quadraticScaleOutput k (directScaleInput S A scale f k s) := by
  classical
  funext x
  let T := A.filter (fun I ↦ scale I = k)
  let κ : ℝ → ℂ := quadraticScaleKernel ((2 : ℝ) ^ k)
  have hκc : Continuous κ := continuous_quadraticScaleKernel_two_zpow k
  have hκs : HasCompactSupport κ :=
    hasCompactSupport_quadraticScaleKernel_two_zpow k
  have hint (I : RealInterval) (hI : I ∈ T) :
      Integrable (fun t ↦ κ (x - t) * offsetGroupedInput S scale f I s t) :=
    integrable_convolution_row_of_memLp hκc hκs
      (memLp_two_offsetGroupedInput S scale f I s) x
  unfold directScaleOutput
  rw [quadraticScaleOutput_eq_actual_convolution]
  simp only [T] at hint ⊢
  calc
    (∑ I ∈ T, krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x) =
        ∑ I ∈ T, ∫ t, κ (x - t) * offsetGroupedInput S scale f I s t := by
      apply Finset.sum_congr rfl
      intro I hI
      have hIk : scale I = k := (Finset.mem_filter.mp hI).2
      rw [krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hIk]
      have hcentral : I.centralThird.indicator
          (offsetGroupedInput S scale f I s) t =
          offsetGroupedInput S scale f I s t := by
        by_cases ht : t ∈ I.centralThird
        · rw [Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht,
            offsetGroupedInput_eq_zero_of_notMem_centralThird
              S scale f I s ht]
      rw [hcentral]
      exact congrArg (fun z : ℂ ↦ z * offsetGroupedInput S scale f I s t)
        (quadraticScaleKernel_two_zpow k (x - t)).symm
    _ = ∫ t, ∑ I ∈ T, κ (x - t) * offsetGroupedInput S scale f I s t := by
      exact (integral_finsetSum T hint).symm
    _ = ∫ t, κ (x - t) * directScaleInput S A scale f k s t := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [directScaleInput, T, Finset.mul_sum]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact congrArg (fun z : ℂ ↦ z * directScaleInput S A scale f k s t)
        (quadraticScaleKernel_two_zpow k (x - t))

/-- Same-scale central thirds are disjoint, so assembling the scale input
introduces no pointwise multiplicity. -/
theorem norm_directScaleInput_le_smallestScaleInput
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) (k : ℤ) (x : ℝ) :
    ‖directScaleInput S A scale f k s x‖ ≤
      ‖smallestScaleInput S scale f (k - s) x‖ := by
  classical
  let T := A.filter (fun I ↦ scale I = k)
  let b := smallestScaleInput S scale f (k - s)
  have hbridge (I : RealInterval) (hI : I ∈ T) :
      offsetGroupedInput S scale f I s = I.centralThird.indicator b := by
    simpa only [T, b, (Finset.mem_filter.mp hI).2] using
      offsetGroupedInput_eq_indicator_smallestScaleInput
        hlam scale hscale (hA (Finset.mem_filter.mp hI).1) (f : ℝ → ℂ) hs
  have hinput : directScaleInput S A scale f k s x =
      ∑ I ∈ T, I.centralThird.indicator b x := by
    unfold directScaleInput
    apply Finset.sum_congr rfl
    intro I hI
    rw [hbridge I hI]
  rw [hinput]
  by_cases hex : ∃ I ∈ T, x ∈ I.centralThird
  · obtain ⟨I, hI, hxI⟩ := hex
    have hsum : (∑ J ∈ T, J.centralThird.indicator b x) = b x := by
      rw [Finset.sum_eq_single I]
      · rw [Set.indicator_of_mem hxI]
      · intro J hJ hJI
        have hxJ : x ∉ J.centralThird := by
          intro hxJ
          exact Set.disjoint_left.mp
            (outputScale_centralThird_pairwiseDisjoint hA hlam scale hscale k
              hJ hI hJI) hxJ hxI
        rw [Set.indicator_of_notMem hxJ]
      · intro hnot
        exact (hnot hI).elim
    rw [hsum]
  · have hzero : ∀ I ∈ T, I.centralThird.indicator b x = 0 := by
      intro I hI
      rw [Set.indicator_of_notMem]
      intro hxI
      exact hex ⟨I, hI, hxI⟩
    rw [Finset.sum_eq_zero hzero, norm_zero]
    exact norm_nonneg _

/-- The assembled input inherits the paper's unit-window mass estimate at
the lower input scale `k-s`. -/
theorem integral_unitWindow_norm_directScaleInput_le
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {k s : ℤ} (hs : 0 ≤ s) (hgap : 0 ≤ k + 2 - s)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (x : ℝ) :
    (∫ t in Icc (x - 1 / 2) (x + 1 / 2),
        ‖directScaleInput S A scale f k s t‖) ≤
      3 * M * (2 : ℝ) ^ (k + 2 - s) := by
  let m : ℤ := k - s
  let L : ℝ := (2 : ℝ) ^ (m + 2)
  have hmindex : 0 ≤ m + 2 := by
    dsimp [m]
    omega
  have hL : 0 < L := by dsimp [L]; positivity
  have hLone : 1 ≤ L := by
    dsimp [L]
    simpa only [zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmindex
  have hpoint : ∀ t : ℝ,
      ‖directScaleInput S A scale f k s t‖ ≤
        ‖smallestScaleInput S scale f m t‖ := by
    intro t
    simpa only [m] using
      norm_directScaleInput_le_smallestScaleInput hA hlam scale hscale f hs k t
  have hmono :
      (∫ t in Icc (x - 1 / 2) (x + 1 / 2),
          ‖directScaleInput S A scale f k s t‖) ≤
        ∫ t in Icc (x - 1 / 2) (x + 1 / 2),
          ‖smallestScaleInput S scale f m t‖ := by
    apply integral_mono
    · exact (integrable_directScaleInput S A scale f k s).norm.integrableOn
    · exact (integrable_smallestScaleInput S scale f m).norm.integrableOn
    · exact hpoint
  have hwindow :
      (∫ t in Icc (x - 1 / 2) (x + 1 / 2),
          ‖smallestScaleInput S scale f m t‖) ≤
        M * ((x + 1 / 2) - (x - 1 / 2) + 2 * L) := by
    apply integral_window_norm_smallestScaleInput_le hlam scale f m
      (sameScale_carriers_pairwiseDisjoint hlam scale hscale m) hL hM
      (by linarith)
    · intro J hJ
      dsimp [L]
      rw [hscale J (Finset.mem_filter.mp hJ).1,
        (Finset.mem_filter.mp hJ).2]
    · intro J hJ
      exact hmass J (Finset.mem_filter.mp hJ).1
  calc
    (∫ t in Icc (x - 1 / 2) (x + 1 / 2),
        ‖directScaleInput S A scale f k s t‖) ≤
        ∫ t in Icc (x - 1 / 2) (x + 1 / 2),
          ‖smallestScaleInput S scale f m t‖ := hmono
    _ ≤ M * ((x + 1 / 2) - (x - 1 / 2) + 2 * L) := hwindow
    _ ≤ 3 * M * L := by nlinarith
    _ = 3 * M * (2 : ℝ) ^ (k + 2 - s) := by
      dsimp [L, m]
      congr 2
      ring

theorem centeredUnitMass_directScaleInput_le
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {k s : ℤ} (hs : 0 ≤ s) (hgap : 0 ≤ k + 2 - s)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (x : ℝ) :
    centeredUnitMass (directScaleInput S A scale f k s) x ≤
      3 * M * (2 : ℝ) ^ (k + 2 - s) := by
  exact integral_unitWindow_norm_directScaleInput_le
    hA hlam scale hscale f hs hgap hM hmass x

/-- The `L¹` mass of one assembled scale input is bounded by the sum of
the masses of its interval pieces. -/
theorem integral_norm_directScaleInput_le_sum
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    (∫ x, ‖directScaleInput S A scale f k s x‖) ≤
      ∑ I ∈ A.filter (fun I ↦ scale I = k),
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
  let T := A.filter (fun I ↦ scale I = k)
  have hsumInt : Integrable (fun x ↦
      ∑ I ∈ T, ‖offsetGroupedInput S scale f I s x‖) := by
    apply integrable_finsetSum
    intro I hI
    exact (integrable_offsetGroupedInput S scale f I s).norm
  calc
    (∫ x, ‖directScaleInput S A scale f k s x‖) ≤
        ∫ x, ∑ I ∈ T, ‖offsetGroupedInput S scale f I s x‖ := by
      apply integral_mono (integrable_directScaleInput S A scale f k s).norm hsumInt
      intro x
      exact norm_sum_le _ _
    _ = ∑ I ∈ T, ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
      exact integral_finsetSum T
        (fun I hI ↦ (integrable_offsetGroupedInput S scale f I s).norm)
    _ = _ := rfl

/-- Across all actual output scales, the assembled inputs still use at most
the total mass beneath the root interval. -/
theorem sum_integral_norm_directScaleInput_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier) :
    (∑ k ∈ A.image scale, ∫ x, ‖directScaleInput S A scale f k s x‖) ≤
      ∫ x in I₀.carrier, ‖f x‖ := by
  calc
    (∑ k ∈ A.image scale, ∫ x, ‖directScaleInput S A scale f k s x‖) ≤
        ∑ k ∈ A.image scale,
          ∑ I ∈ A.filter (fun I ↦ scale I = k),
            ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact integral_norm_directScaleInput_le_sum S A scale f k s
    _ ≤ ∫ x in I₀.carrier, ‖f x‖ :=
      sum_integral_norm_offsetGroupedInput_allScales_le_root
        hA hlam scale hscale f hs I₀ hsub

/-- Restricting to any finite initial segment of one residue class cannot
increase the total `L¹` input mass beyond the mass under the root interval. -/
theorem sum_range_integral_norm_directScaleInput_residue_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (r : Fin 7) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        ∫ x, ‖directScaleInput S A scale f (residueScale r n) s x‖) ≤
      ∫ x in I₀.carrier, ‖f x‖ := by
  classical
  let K := A.image scale
  let T := (Finset.range N).filter (fun n ↦ residueScale r n ∈ K)
  let F : ℤ → ℝ := fun k ↦ ∫ x, ‖directScaleInput S A scale f k s x‖
  have hzero (n : ℕ) (hn : n ∈ Finset.range N) (hnT : n ∉ T) :
      F (residueScale r n) = 0 := by
    have hnotK : residueScale r n ∉ K := by
      intro hnK
      exact hnT (Finset.mem_filter.mpr ⟨hn, hnK⟩)
    dsimp only [F]
    rw [show directScaleInput S A scale f (residueScale r n) s = 0 by
      exact directScaleInput_eq_zero_of_not_mem_image S A scale f
        (residueScale r n) s hnotK]
    simp
  have hrestrict :
      (∑ n ∈ Finset.range N, F (residueScale r n)) =
        ∑ n ∈ T, F (residueScale r n) := by
    symm
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro n hn hnT
      exact hzero n hn hnT
  have hinj : Set.InjOn (residueScale r) (↑T : Set ℕ) := by
    intro m hm n hn hmn
    unfold residueScale at hmn
    omega
  have himage :
      (∑ n ∈ T, F (residueScale r n)) =
        ∑ k ∈ T.image (residueScale r), F k := by
    symm
    exact Finset.sum_image hinj
  have hsubK : T.image (residueScale r) ⊆ K := by
    intro k hk
    obtain ⟨n, hnT, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hnT).2
  calc
    (∑ n ∈ Finset.range N,
        ∫ x, ‖directScaleInput S A scale f (residueScale r n) s x‖) =
        ∑ n ∈ Finset.range N, F (residueScale r n) := by rfl
    _ = ∑ n ∈ T, F (residueScale r n) := hrestrict
    _ = ∑ k ∈ T.image (residueScale r), F k := himage
    _ ≤ ∑ k ∈ K, F k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubK
      intro k hkK hkT
      exact integral_nonneg fun _ ↦ norm_nonneg _
    _ ≤ ∫ x in I₀.carrier, ‖f x‖ :=
      sum_integral_norm_directScaleInput_le_root
        hA hlam scale hscale f hs I₀ hsub

/-- The canonical `L²` fixed-scale output is the `L²` representative of
the same genuine quadratic convolution used by the remainder theorem. -/
theorem offsetOutputScaleLp_ae_eq_quadraticScaleOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    (fun x ↦ offsetOutputScaleLp S A scale f k s x) =ᵐ[volume]
      quadraticScaleOutput k (directScaleInput S A scale f k s) := by
  filter_upwards [offsetOutputScaleLp_ae_eq S A scale f k s] with x hx
  rw [hx]
  exact congrFun (directScaleOutput_eq_quadraticScaleOutput S A scale f k s) x

/-- Exact `L²` projection-error identity for the actual direct fixed-scale
output. The right side is the explicit convolution by `r_{2^k}`. -/
theorem offsetOutputScaleLp_sub_annularProjectionL2_eq_remainderOutputL2
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    {k : ℤ} (hk : 0 ≤ k) (s : ℤ) :
    offsetOutputScaleLp S A scale f k s -
        KrauseLaceyQuadraticSmoothProjection.annularProjectionL2 k
          (offsetOutputScaleLp S A scale f k s) =
      (memLp_two_quadraticProjectionRemainderOutput hk
        (integrable_directScaleInput S A scale f k s)).toLp
          (quadraticProjectionRemainderOutput k
            (directScaleInput S A scale f k s)) := by
  let w : Lp (α := ℝ) ℂ 2 volume := offsetOutputScaleLp S A scale f k s
  let F : ℝ → ℂ := directScaleInput S A scale f k s
  have hae : (fun x ↦ w x) =ᵐ[volume] quadraticScaleOutput k F := by
    simpa only [w, F] using
      offsetOutputScaleLp_ae_eq_quadraticScaleOutput S A scale f k s
  let hquad₂ : MemLp (quadraticScaleOutput k F) 2 volume :=
    (memLp_congr_ae hae).mp (Lp.memLp w)
  have hw : hquad₂.toLp (quadraticScaleOutput k F) = w := by
    simpa only [Lp.toLp_coeFn] using
      MemLp.toLp_congr hquad₂ (Lp.memLp w) hae.symm
  have hrem :=
    quadraticScaleOutputL2_sub_annularProjectionL2_eq_remainderOutputL2_of_nonneg
      hk (integrable_directScaleInput S A scale f k s) hquad₂
  simpa only [w, F, hw] using hrem


end
end KrauseLaceyQuadraticDirectProjectionBridge
end QuadraticCarleson
