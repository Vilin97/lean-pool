/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.KernelConvexity

/-!
Minimizing displacements give global supporting inequalities for the smoothing envelope.
-/

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair

/-- A minimizer supplies a genuine global supporting vector for the literal
infimal value.  The proof combines the locally built nonsmooth optimality
relation with first-order convexity of the smooth kernel. -/
lemma localSmoothingValue_supporting_of_minimizers
    (kernel : SmoothingKernelData p d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hconvPhi : O3.IsConvexObjective kernel.phi)
    (hgradPhi : O3.IsCoordinateGradient kernel.phi kernel.gradPhi)
    {x z v w : Point d}
    (hv : IsInfimalMinimizer kernel chi ell x v)
    (hw : IsInfimalMinimizer kernel chi ell z w) :
    localSmoothingValue kernel chi ell x +
        O3.pairing (-kernel.gradPhi ((1 / chi) • v)) (z - x) ≤
      localSmoothingValue kernel chi ell z := by
  let u : Point d := (1 / chi) • v
  let uw : Point d := (1 / chi) • w
  let g : Point d := -kernel.gradPhi u
  have hell := minimizer_supporting_inequality kernel hchi ell hconv hgradPhi hv
    (z + w)
  have hfirstPhi := O3.Stage3Anchor.firstOrderConvex_of_coordinateGradient
    hconvPhi hgradPhi
  have hphi := hfirstPhi u uw
  have hvValue := localSmoothingValue_eq_of_minimizer kernel chi ell x v hv
  have hwValue := localSmoothingValue_eq_of_minimizer kernel chi ell z w hw
  have hscaleV : v = chi • u := by
    dsimp [u]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hchi.ne']
  have hscaleW : w = chi • uw := by
    dsimp [uw]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hchi.ne']
  have hdisp : z + w - (x + v) = (z - x) + chi • (uw - u) := by
    rw [hscaleV, hscaleW]
    module
  rw [hvValue, hwValue]
  unfold smoothingCost
  change ell (x + v) + chi * kernel.phi u +
      O3.pairing g (z - x) ≤ ell (z + w) + chi * kernel.phi uw
  change ell (x + v) + O3.pairing g (z + w - (x + v)) ≤ ell (z + w) at hell
  rw [hdisp, O3.Stage2RouteD.pairing_add_right,
    O3.Stage2RouteD.pairing_smul_right] at hell
  change kernel.phi u + O3.pairing (kernel.gradPhi u) (uw - u) ≤
    kernel.phi uw at hphi
  dsimp [g] at hell ⊢
  have hneg : O3.pairing (-kernel.gradPhi u) (uw - u) =
      -O3.pairing (kernel.gradPhi u) (uw - u) := by
    simp [O3.pairing]
  rw [hneg] at hell
  nlinarith

end V7.Stage5AboveTwoLowerS5A2Envelope
