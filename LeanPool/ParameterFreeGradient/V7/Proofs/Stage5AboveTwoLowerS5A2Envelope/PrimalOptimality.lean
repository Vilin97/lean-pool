/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerResume.InfimalAttainment
import LeanPool.ParameterFreeGradient.O3.Stage3Descent

/-!
First-order optimality of an infimal-convolution minimizer gives a supporting inequality.
-/

open scoped BigOperators

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Filter

/-- The first-order relation at an infimal minimizer, proved directly from
minimality, convexity of the nonsmooth objective, and the genuine derivative
of the kernel.  No subgradient oracle for `ell` is assumed. -/
lemma minimizer_supporting_inequality
    (kernel : SmoothingKernelData p d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hgradPhi : O3.IsCoordinateGradient kernel.phi kernel.gradPhi)
    {x v : Point d} (hv : IsInfimalMinimizer kernel chi ell x v) :
    ∀ z : Point d,
      ell (x + v) + O3.pairing (-kernel.gradPhi ((1 / chi) • v))
          (z - (x + v)) ≤ ell z := by
  intro z
  let y : Point d := x + v
  let u : Point d := (1 / chi) • v
  let a : Point d := (1 / chi) • (z - y)
  let linePhi : ℝ → ℝ := O3.Stage3Anchor.objectiveLine kernel.phi u (u + a)
  have hline : HasDerivAt linePhi (O3.pairing (kernel.gradPhi u) a) 0 := by
    have h := O3.Stage3Anchor.hasDerivAt_objectiveLine hgradPhi u (u + a) 0
    simpa [linePhi, O3.Stage3Anchor.objectiveLine] using h
  have htend : Tendsto (slope linePhi 0)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (O3.pairing (kernel.gradPhi u) a)) := by
    exact hline.tendsto_slope.mono_left
      (nhdsWithin_mono _ (by intro t ht; exact ht.ne'))
  have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ell y - ell z ≤ chi * slope linePhi 0 t := by
    have hlt : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Set.Iio 1, Iio_mem_nhds (by norm_num), Set.inter_subset_left⟩
    filter_upwards [hlt, self_mem_nhdsWithin] with t ht1 ht0
    have htpos : 0 < t := ht0
    have htlt : t < 1 := ht1
    have htNonneg : 0 ≤ t := htpos.le
    have hone : 0 ≤ 1 - t := by linarith
    have hsum : (1 - t) + t = 1 := by ring
    have hell := hconv.2 (Set.mem_univ y) (Set.mem_univ z)
      hone htNonneg hsum
    have hpoint : (1 - t) • y + t • z = y + t • (z - y) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hpoint] at hell
    have hell' : ell (y + t • (z - y)) ≤
        (1 - t) * ell y + t * ell z := by
      simpa [smul_eq_mul] using hell
    let w : Point d := v + t • (z - y)
    have hxyw : x + w = y + t • (z - y) := by
      dsimp [w, y]
      module
    have hscaled : (1 / chi) • w = u + t • a := by
      dsimp [w, u, a]
      module
    have hmin := hv w
    unfold smoothingCost at hmin
    rw [hxyw, hscaled] at hmin
    change ell y + chi * kernel.phi u ≤
      ell (y + t • (z - y)) + chi * kernel.phi (u + t • a) at hmin
    have hlineZero : linePhi 0 = kernel.phi u := by
      simp [linePhi, O3.Stage3Anchor.objectiveLine]
    have hlineT : linePhi t = kernel.phi (u + t • a) := by
      simp [linePhi, O3.Stage3Anchor.objectiveLine, AffineMap.lineMap_apply,
        add_comm]
    rw [slope, hlineZero, hlineT]
    simp only [vsub_eq_sub, smul_eq_mul, sub_zero]
    field_simp [htpos.ne']
    nlinarith [hell']
  have hlimit : ell y - ell z ≤
      chi * O3.pairing (kernel.gradPhi u) a := by
    apply ge_of_tendsto (htend.const_mul chi)
    simpa using hevent
  have hscalePair : chi * O3.pairing (kernel.gradPhi u) a =
      O3.pairing (kernel.gradPhi u) (z - y) := by
    dsimp [a]
    rw [O3.Stage2RouteD.pairing_smul_right]
    field_simp [hchi.ne']
  rw [hscalePair] at hlimit
  dsimp [y] at hlimit ⊢
  rw [show O3.pairing (-kernel.gradPhi ((1 / chi) • v)) (z - (x + v)) =
      -O3.pairing (kernel.gradPhi ((1 / chi) • v)) (z - (x + v)) by
    simp [O3.pairing]]
  linarith

end V7.Stage5AboveTwoLowerS5A2Envelope
