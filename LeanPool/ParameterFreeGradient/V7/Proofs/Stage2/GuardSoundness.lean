/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03

namespace V7
namespace Stage2

/-- Current-oriented Banach cocoercivity.  The Bregman remainder is based at
`y`, so its linear term uses `gradient y`. -/
theorem cocoercivityGuard_of_scale_ge {p L M : ℝ} (hp : 1 < p)
    (inst : PositiveInstance p d x0) (hLM : L ≤ M) (hL : inst.L = L)
    (x y : Point d) : CocoercivityGuard p M inst.oracle x y := by
  subst L
  let q := conjugateExponent p
  let g := inst.oracle.gradient x - inst.oracle.gradient y
  let G := lpNorm q g
  have hM : 0 < M := lt_of_lt_of_le inst.L_pos hLM
  have hfirst := O3.Stage3Anchor.firstOrderConvex_of_coordinateGradient
    inst.convex inst.coordinateGradient
  have hBnonneg : 0 ≤ BregmanRemainder inst.oracle x y := by
    have hxy := hfirst y x
    dsimp only [BregmanRemainder]
    linarith
  by_cases hGzero : G = 0
  · have hzero : lpNorm (conjugateExponent p)
        (inst.oracle.gradient x - inst.oracle.gradient y) = 0 := by
      simpa only [G, g, q] using hGzero
    dsimp only [CocoercivityGuard]
    rw [hzero]
    norm_num
    exact hBnonneg
  · have hG : 0 < G := lt_of_le_of_ne (O3.lpNorm_nonneg q g) (Ne.symm hGzero)
    let v := normingDirection q g
    let z := x - (G / inst.L) • v
    have hv := normingDirection_correct p hp d g (by simpa only [G, q] using hG)
    have hvnorm : lpNorm p v = 1 := by simpa only [v, q] using hv.1
    have hvpair : pairing g v = G := by simpa only [v, q, G] using hv.2
    have hvnormO3 : O3.lpNorm p v = 1 := hvnorm
    have hvpairO3 : O3.pairing g v = G := hvpair
    have hzsub : z - x = (-(G / inst.L)) • v := by
      funext i
      simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hnorm : lpNorm p (z - x) = G / inst.L := by
      rw [hzsub]
      change O3.lpNorm p ((-(G / inst.L)) • v) = G / inst.L
      have hs := O3.Stage2RouteC.lpNorm_smul hp.le (-(G / inst.L)) v
      rw [hs, hvnormO3]
      rw [abs_of_neg (neg_neg_of_pos (div_pos hG inst.L_pos))]
      ring
    have hpair : pairing g (z - x) = -(G ^ (2 : ℕ) / inst.L) := by
      rw [hzsub]
      change O3.pairing g ((-(G / inst.L)) • v) = _
      rw [O3.Stage2RouteD.pairing_smul_right, hvpairO3]
      field_simp [inst.L_pos.ne']
    have hzy : pairing (inst.oracle.gradient y) (z - y) =
        pairing (inst.oracle.gradient y) (x - y) +
          pairing (inst.oracle.gradient y) (z - x) := by
      change O3.pairing (inst.oracle.gradient y) (z - y) = _
      have hvec : z - y = (x - y) + (z - x) := by module
      rw [hvec, O3.Stage2RouteD.pairing_add_right]
    have hgrad : pairing (inst.oracle.gradient x) (z - x) -
          pairing (inst.oracle.gradient y) (z - x) = pairing g (z - x) := by
      change O3.pairing (inst.oracle.gradient x) (z - x) -
          O3.pairing (inst.oracle.gradient y) (z - x) =
        O3.pairing (inst.oracle.gradient x - inst.oracle.gradient y) (z - x)
      simp only [O3.pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    have hyz := hfirst y z
    have hdesc := O3.Stage3Anchor.smooth_descent_lp hp
      (O3.holderConjugate_conjugateExponent hp)
      inst.coordinateGradient inst.smooth x z
    change inst.oracle.value y + pairing (inst.oracle.gradient y) (z - y) ≤
      inst.oracle.value z at hyz
    change inst.oracle.value z ≤ inst.oracle.value x +
      pairing (inst.oracle.gradient x) (z - x) +
        (inst.L / 2) * (lpNorm p (z - x)) ^ (2 : ℕ) at hdesc
    rw [hzy] at hyz
    rw [hnorm] at hdesc
    have hratio : G ^ (2 : ℕ) / inst.L =
        2 * (G ^ (2 : ℕ) / (2 * inst.L)) := by
      field_simp [inst.L_pos.ne']
    have hquad : (inst.L / 2) * (G / inst.L) ^ (2 : ℕ) =
        G ^ (2 : ℕ) / (2 * inst.L) := by
      field_simp [inst.L_pos.ne']
    rw [hquad] at hdesc
    rw [hratio] at hpair
    have hcore : G ^ (2 : ℕ) / (2 * inst.L) ≤
        BregmanRemainder inst.oracle x y := by
      dsimp only [BregmanRemainder]
      linarith [hyz, hgrad, hpair, hdesc]
    have hfrac : G ^ (2 : ℕ) / (2 * M) ≤
        G ^ (2 : ℕ) / (2 * inst.L) := by
      have hnum : 0 ≤ G ^ (2 : ℕ) := sq_nonneg G
      exact div_le_div_of_nonneg_left hnum
        (mul_pos (by norm_num) inst.L_pos) (by nlinarith)
    dsimp only [CocoercivityGuard]
    change BregmanRemainder inst.oracle x y ≥ G ^ (2 : ℕ) / (2 * M)
    exact hfrac.trans hcore

theorem failed_cocoercivityGuard_lt_trueScale {p L M : ℝ} (hp : 1 < p)
    (inst : PositiveInstance p d x0) (hL : inst.L = L)
    (x y : Point d) (hfail : ¬ CocoercivityGuard p M inst.oracle x y) :
    M < L := by
  by_contra hnot
  exact hfail (cocoercivityGuard_of_scale_ge hp inst
    (le_of_not_gt hnot) hL x y)

end Stage2
end V7
