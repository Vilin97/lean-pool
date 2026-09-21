/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.EnvelopeSupport

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair

/-- The exact local kernel inequality needed by the primal envelope route.
It is stated only on the unit `ell_p` ball, matching the frozen Hessian
control and the already proved strict interiority of all minimizers. -/
def KernelCocoerciveOnUnit (p M : ℝ) (gradPhi : Point d → Point d) : Prop :=
  ∀ u w : Point d, lpNorm p u ≤ 1 → lpNorm p w ≤ 1 →
    (lpNorm (conjugateExponent p) (gradPhi u - gradPhi w)) ^ (2 : ℕ) ≤
      M * O3.pairing (gradPhi u - gradPhi w) (u - w)

private lemma minimizer_monotonicity_core
    (kernel : SmoothingKernelData p d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hgradPhi : O3.IsCoordinateGradient kernel.phi kernel.gradPhi)
    {x y vx vy : Point d}
    (hvx : IsInfimalMinimizer kernel chi ell x vx)
    (hvy : IsInfimalMinimizer kernel chi ell y vy) :
    chi * O3.pairing
        (kernel.gradPhi ((1 / chi) • vx) -
          kernel.gradPhi ((1 / chi) • vy))
        (((1 / chi) • vx) - ((1 / chi) • vy)) ≤
      O3.pairing
        (kernel.gradPhi ((1 / chi) • vx) -
          kernel.gradPhi ((1 / chi) • vy)) (y - x) := by
  let ux : Point d := (1 / chi) • vx
  let uy : Point d := (1 / chi) • vy
  let D : Point d := kernel.gradPhi ux - kernel.gradPhi uy
  have hx := minimizer_supporting_inequality kernel hchi ell hconv hgradPhi hvx
    (y + vy)
  have hy := minimizer_supporting_inequality kernel hchi ell hconv hgradPhi hvy
    (x + vx)
  have hscaleX : vx = chi • ux := by
    dsimp [ux]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hchi.ne']
  have hscaleY : vy = chi • uy := by
    dsimp [uy]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hchi.ne']
  have hdiff : y + vy - (x + vx) = (y - x) - chi • (ux - uy) := by
    rw [hscaleX, hscaleY]
    module
  change ell (x + vx) + O3.pairing (-kernel.gradPhi ux)
      (y + vy - (x + vx)) ≤ ell (y + vy) at hx
  change ell (y + vy) + O3.pairing (-kernel.gradPhi uy)
      (x + vx - (y + vy)) ≤ ell (x + vx) at hy
  have hsum : O3.pairing (-kernel.gradPhi ux)
        (y + vy - (x + vx)) +
      O3.pairing (-kernel.gradPhi uy)
        (x + vx - (y + vy)) ≤ 0 := by linarith
  have hpair : O3.pairing (-kernel.gradPhi ux)
        (y + vy - (x + vx)) +
      O3.pairing (-kernel.gradPhi uy)
        (x + vx - (y + vy)) =
      -O3.pairing D (y + vy - (x + vx)) := by
    have hrev : x + vx - (y + vy) = -(y + vy - (x + vx)) := by module
    rw [hrev]
    dsimp [D]
    simp only [O3.pairing, Pi.neg_apply, Pi.sub_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hpair, hdiff] at hsum
  have hexpand : -O3.pairing D ((y - x) - chi • (ux - uy)) =
      -O3.pairing D (y - x) + chi * O3.pairing D (ux - uy) := by
    simp only [O3.pairing, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand] at hsum
  dsimp [D, ux, uy] at hsum ⊢
  linarith

/-- Exact minimizer-gradient Lipschitz estimate, conditional only on the local
kernel cocoercivity wheel. -/
lemma minimizer_kernel_gradient_lipschitz
    (kernel : SmoothingKernelData p d) {chi M : ℝ}
    (hp : 1 < p) (hchi : 0 < chi) (hM : 0 ≤ M)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hgradPhi : O3.IsCoordinateGradient kernel.phi kernel.gradPhi)
    (hcoco : KernelCocoerciveOnUnit p M kernel.gradPhi)
    {x y vx vy : Point d}
    (hvx : IsInfimalMinimizer kernel chi ell x vx)
    (hvy : IsInfimalMinimizer kernel chi ell y vy)
    (hux : lpNorm p ((1 / chi) • vx) ≤ 1)
    (huy : lpNorm p ((1 / chi) • vy) ≤ 1) :
    lpNorm (conjugateExponent p)
        (kernel.gradPhi ((1 / chi) • vx) -
          kernel.gradPhi ((1 / chi) • vy)) ≤
      (M / chi) * lpNorm p (x - y) := by
  let D : Point d := kernel.gradPhi ((1 / chi) • vx) -
    kernel.gradPhi ((1 / chi) • vy)
  let G : ℝ := lpNorm (conjugateExponent p) D
  have hG : 0 ≤ G := O3.lpNorm_nonneg _ _
  by_cases hG0 : G = 0
  · rw [show lpNorm (conjugateExponent p)
        (kernel.gradPhi ((1 / chi) • vx) -
          kernel.gradPhi ((1 / chi) • vy)) = 0 by simpa [G, D] using hG0]
    exact mul_nonneg (div_nonneg hM hchi.le) (O3.lpNorm_nonneg p _)
  · have hGpos : 0 < G := lt_of_le_of_ne hG (Ne.symm hG0)
    have hmono := minimizer_monotonicity_core kernel hchi ell hconv hgradPhi
      hvx hvy
    have hc := hcoco ((1 / chi) • vx) ((1 / chi) • vy) hux huy
    have hholder := O3.pairing_le_lpNorm_mul
      (O3.holderConjugate_conjugateExponent hp).symm D (y - x)
    have hnormSymm : lpNorm p (y - x) = lpNorm p (x - y) := by
      rw [show y - x = -(x - y) by module]
      change O3.lpNorm p (-(x - y)) = O3.lpNorm p (x - y)
      simpa using O3.Stage2RouteC.lpNorm_smul hp.le (-1 : ℝ) (x - y)
    change chi * O3.pairing D
      (((1 / chi) • vx) - ((1 / chi) • vy)) ≤
        O3.pairing D (y - x) at hmono
    change G ^ (2 : ℕ) ≤ M * O3.pairing D
      (((1 / chi) • vx) - ((1 / chi) • vy)) at hc
    change O3.pairing D (y - x) ≤ G * lpNorm p (y - x) at hholder
    rw [hnormSymm] at hholder
    change G ≤ (M / chi) * lpNorm p (x - y)
    have hcore : chi * G ^ (2 : ℕ) ≤
        M * G * lpNorm p (x - y) := by
      nlinarith [mul_le_mul_of_nonneg_left hmono hM]
    rw [show G ^ (2 : ℕ) = G * G by ring] at hcore
    have hcore' : G * (chi * G) ≤
        G * (M * lpNorm p (x - y)) := by
      nlinarith
    have hcancel := le_of_mul_le_mul_left hcore' hGpos
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hchi).2
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcancel)

/-- Any two minimizers at the same centre induce exactly the same kernel
gradient. -/
lemma minimizer_kernel_gradient_unique
    (kernel : SmoothingKernelData p d) {chi M : ℝ}
    (hp : 1 < p) (hchi : 0 < chi) (hM : 0 ≤ M)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hgradPhi : O3.IsCoordinateGradient kernel.phi kernel.gradPhi)
    (hcoco : KernelCocoerciveOnUnit p M kernel.gradPhi)
    {x vx vy : Point d}
    (hvx : IsInfimalMinimizer kernel chi ell x vx)
    (hvy : IsInfimalMinimizer kernel chi ell x vy)
    (hux : lpNorm p ((1 / chi) • vx) ≤ 1)
    (huy : lpNorm p ((1 / chi) • vy) ≤ 1) :
    kernel.gradPhi ((1 / chi) • vx) =
      kernel.gradPhi ((1 / chi) • vy) := by
  have h := minimizer_kernel_gradient_lipschitz kernel hp hchi hM ell hconv
    hgradPhi hcoco hvx hvy hux huy
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hzeroP : lpNorm p (x - x) = 0 := by
    change O3.lpNorm p (x - x) = 0
    rw [sub_self, O3.lpNorm_zero hp0]
  rw [hzeroP, mul_zero] at h
  have hz : lpNorm (conjugateExponent p)
      (kernel.gradPhi ((1 / chi) • vx) -
        kernel.gradPhi ((1 / chi) • vy)) = 0 :=
    le_antisymm h (O3.lpNorm_nonneg _ _)
  exact sub_eq_zero.mp ((O3.lpNorm_eq_zero_iff
    (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp))).mp hz)

end V7.Stage5AboveTwoLowerS5A2Envelope
