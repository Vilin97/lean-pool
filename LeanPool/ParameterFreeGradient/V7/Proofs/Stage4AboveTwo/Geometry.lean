/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.AboveTwoStatements
import LeanPool.ParameterFreeGradient.O3.GeometryExperimental
import LeanPool.ParameterFreeGradient.O3.Stage2RouteB

open scoped BigOperators

namespace V7.Stage4AboveTwo

private noncomputable def pairingCLM (g : Point d) : Point d →L[ℝ] ℝ :=
  ∑ i : Fin d, (g i) • ContinuousLinearMap.proj i

@[simp] private lemma pairingCLM_apply (g h : Point d) :
    pairingCLM g h = O3.pairing g h := by
  simp [pairingCLM, O3.pairing]

private lemma conjugate_gt_one {p : ℝ} (hp : 2 < p) :
    1 < conjugateExponent p := O3.one_lt_conjugateExponent (by linarith)

private lemma conjugate_involutive {p : ℝ} (hp : 2 < p) :
    conjugateExponent (conjugateExponent p) = p := by
  change O3.conjugateExponent (O3.conjugateExponent p) = p
  rw [O3.conjugateExponent_eq, O3.conjugateExponent_eq]
  have hne : p - 1 ≠ 0 := by linarith
  field_simp [hne]
  ring

private lemma holder_pair {p : ℝ} (hp : 2 < p) :
    p.HolderConjugate (conjugateExponent p) :=
  O3.holderConjugate_conjugateExponent (by linarith)

private lemma aboveH_eq_regularizer {p : ℝ} (hp : 2 < p) (x : Point d) :
    aboveH p x = O3.uniformRegularizer p 0 x := by
  unfold aboveH O3.uniformRegularizer
  rw [O3.Experimental.lpNorm_rpow_eq_lpPower (by linarith : p ≠ 0)]
  simp only [sub_zero]

private lemma power_map_pairing {r : ℝ} (hr : 1 < r) (x : Point d) :
    pairing (O3.powerDualityMap r x) x = (lpNorm r x) ^ r := by
  change O3.pairing (O3.powerDualityMap r x) x = (O3.lpNorm r x) ^ r
  rw [O3.Stage2RouteB.pairing_powerDualityMap_self hr]
  exact (O3.Experimental.lpNorm_rpow_eq_lpPower (by linarith : r ≠ 0) x).symm

private lemma power_map_norm_power {p : ℝ} (hp : 2 < p) (s : Point d) :
    (lpNorm p (aboveMirrorMap p s)) ^ p =
      (lpNorm (conjugateExponent p) s) ^ (conjugateExponent p) := by
  rw [O3.Experimental.lpNorm_rpow_eq_lpPower (by linarith : p ≠ 0)]
  rw [O3.Experimental.lpNorm_rpow_eq_lpPower
    (by have := conjugate_gt_one hp; linarith : conjugateExponent p ≠ 0)]
  unfold O3.lpPower aboveMirrorMap O3.powerDualityMap
  apply Finset.sum_congr rfl
  intro i _
  let q := conjugateExponent p
  have hq : 1 < q := conjugate_gt_one hp
  by_cases hs : s i = 0
  · rw [hs, abs_zero]
    simp only [mul_zero, abs_zero]
    rw [Real.zero_rpow (by dsimp [q]; linarith : conjugateExponent p ≠ 0)]
    rw [Real.zero_rpow (by linarith : p ≠ 0)]
  · have ha : 0 < |s i| := abs_pos.mpr hs
    have habsmap : |(|s i| ^ (q - 2) * s i)| = |s i| ^ (q - 1) := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le _)]
      rw [← Real.rpow_add_one' ha.le (by linarith : q - 2 + 1 ≠ 0)]
      congr 1
      ring
    change |(|s i| ^ (q - 2) * s i)| ^ p = |s i| ^ q
    rw [habsmap, ← Real.rpow_mul ha.le]
    congr 1
    change (O3.conjugateExponent p - 1) * p = O3.conjugateExponent p
    rw [O3.conjugateExponent_eq]
    field_simp [show p - 1 ≠ 0 by linarith]
    ring

private lemma mirror_pairing {p : ℝ} (hp : 2 < p) (s : Point d) :
    pairing s (aboveMirrorMap p s) =
      (lpNorm (conjugateExponent p) s) ^ (conjugateExponent p) := by
  change O3.pairing s (aboveMirrorMap p s) = _
  rw [O3.pairing_comm]
  exact power_map_pairing (conjugate_gt_one hp) s

private lemma power_map_inverse {p : ℝ} (hp : 2 < p) (s : Point d) :
    O3.powerDualityMap p (aboveMirrorMap p s) = s := by
  unfold aboveMirrorMap O3.powerDualityMap
  funext i
  let q := conjugateExponent p
  have hq : 1 < q := conjugate_gt_one hp
  by_cases hs : s i = 0
  · simp [hs, show p ≠ 0 by linarith, show q ≠ 0 by linarith]
  · have ha : 0 < |s i| := abs_pos.mpr hs
    have hinner : |s i| ^ (q - 2) * s i = |s i| ^ (q - 1) * (s i / |s i|) := by
      calc
        |s i| ^ (q - 2) * s i =
            (|s i| ^ (q - 2) * |s i|) * (s i / |s i|) := by
              field_simp [ha.ne']
        _ = |s i| ^ (q - 1) * (s i / |s i|) := by
              rw [← Real.rpow_add_one' ha.le (by linarith : q - 2 + 1 ≠ 0)]
              congr 2
              ring
    have habsinner : |(|s i| ^ (q - 2) * s i)| = |s i| ^ (q - 1) := by
      rw [hinner, abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le _)]
      rw [abs_div, abs_abs, div_self ha.ne', mul_one]
    change |(|s i| ^ (q - 2) * s i)| ^ (p - 2) *
      (|s i| ^ (q - 2) * s i) = s i
    rw [habsinner, hinner]
    rw [← Real.rpow_mul ha.le]
    rw [← mul_assoc, ← Real.rpow_add ha]
    rw [show (q - 1) * (p - 2) + (q - 1) = 1 by
      change (O3.conjugateExponent p - 1) * (p - 2) +
        (O3.conjugateExponent p - 1) = 1
      rw [O3.conjugateExponent_eq]
      field_simp [show p - 1 ≠ 0 by linarith]
      ring]
    rw [Real.rpow_one]
    field_simp [ha.ne']

private lemma fenchel_attained {p : ℝ} (hp : 2 < p) (s : Point d) :
    pairing s (aboveMirrorMap p s) - aboveH p (aboveMirrorMap p s) =
      aboveHstar p s := by
  rw [mirror_pairing hp, aboveH, aboveHstar, power_map_norm_power hp]
  have hp0 : p ≠ 0 := by linarith
  have hq0 : conjugateExponent p ≠ 0 := by
    have := conjugate_gt_one hp
    linarith
  change _ = (1 / O3.conjugateExponent p) * _
  rw [O3.conjugateExponent_eq]
  field_simp [hp0, show p - 1 ≠ 0 by linarith]

private lemma fenchel_upper {p : ℝ} (hp : 2 < p) (s x : Point d) :
    pairing s x - aboveH p x ≤ aboveHstar p s := by
  have hholder := O3.pairing_le_lpNorm_mul (holder_pair hp).symm s x
  have hyoung := Real.young_inequality_of_nonneg
    (O3.lpNorm_nonneg (conjugateExponent p) s) (O3.lpNorm_nonneg p x)
    (holder_pair hp).symm
  unfold aboveH aboveHstar
  calc
    pairing s x - 1 / p * lpNorm p x ^ p ≤
        (lpNorm (conjugateExponent p) s ^ conjugateExponent p /
          conjugateExponent p + lpNorm p x ^ p / p) -
          1 / p * lpNorm p x ^ p := by linarith
    _ = 1 / conjugateExponent p *
        lpNorm (conjugateExponent p) s ^ conjugateExponent p := by ring

private lemma fenchel_conjugate {p : ℝ} (hp : 2 < p) (s : Point d) :
    FenchelConjugate (aboveH p) s = aboveHstar p s := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · exact ⟨aboveMirrorMap p s, (fenchel_attained hp s).symm⟩
  · intro r hr
    rcases hr with ⟨x, rfl⟩
    exact fenchel_upper hp s x

private lemma hstar_gradient {p : ℝ} (hp : 2 < p) :
    O3.IsCoordinateGradient
      (fun s : Point d => aboveHstar p s)
      (fun s : Point d => aboveMirrorMap p s) := by
  intro s
  let q := conjugateExponent p
  have hq : 1 < q := conjugate_gt_one hp
  have hq0 : q ≠ 0 := by linarith
  let coordDeriv (i : Fin d) : Point d →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ (O3.Experimental.scalarJ q (s i))).comp
      (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ)
  have hcoord (i : Fin d) : HasFDerivAt
      (fun x : Point d => |x i| ^ q / q)
      (coordDeriv i) s := by
    have he := (hasDerivAt_abs_rpow (s i) hq).div_const q
    have he' : HasDerivAt (fun x : ℝ => |x| ^ q / q)
        (O3.Experimental.scalarJ q (s i)) (s i) := by
      apply he.congr_deriv
      unfold O3.Experimental.scalarJ
      field_simp [hq0]
    exact he'.hasFDerivAt.comp s
      (ContinuousLinearMap.proj i : Point d →L[ℝ] ℝ).hasFDerivAt
  have hsum : HasFDerivAt (fun x : Point d => ∑ i, |x i| ^ q / q)
      (pairingCLM (aboveMirrorMap p s)) s := by
    have hraw : HasFDerivAt (fun x : Point d => ∑ i, |x i| ^ q / q)
        (∑ i : Fin d, coordDeriv i) s :=
      HasFDerivAt.fun_sum (fun i _ => hcoord i)
    apply hraw.congr_fderiv
    ext h
    simp [coordDeriv, pairingCLM, aboveMirrorMap, O3.powerDualityMap,
      O3.Experimental.scalarJ, O3.pairing,
      ContinuousLinearMap.toSpanSingleton_apply]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    ring
  have heq : (fun x : Point d => aboveHstar p x) =
      (fun x : Point d => ∑ i, |x i| ^ q / q) := by
    funext x
    unfold aboveHstar
    change (1 / q) * ((∑ i, |x i| ^ q) ^ (1 / q)) ^ q = _
    rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (abs_nonneg _) _)]
    rw [show 1 / q * q = 1 by field_simp [hq0], Real.rpow_one]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  let hfrechet := hsum
  refine ⟨hfrechet.differentiableAt, ?_⟩
  intro h
  rw [hfrechet.fderiv]
  simp [O3.pairing]

private lemma uniform_remainder {p : ℝ} (hp : 2 < p) (x y : Point d) :
    FunctionBregman (aboveH p) (fun z => O3.powerDualityMap p z) x y ≥
      (2 ^ (2 - p) / p) * (lpNorm p (x - y)) ^ p := by
  have h := O3.pUniformConvexity p hp d y x 0
  rw [← aboveH_eq_regularizer hp x, ← aboveH_eq_regularizer hp y] at h
  unfold FunctionBregman
  simp only [sub_zero] at h
  have hsub : x - y = x - y := rfl
  linarith

private lemma bregman_conjugacy {p : ℝ} (hp : 2 < p) (s t : Point d) :
    FunctionBregman (aboveHstar p) (aboveMirrorMap p) s t =
      FunctionBregman (aboveH p) (fun z => O3.powerDualityMap p z)
        (aboveMirrorMap p t) (aboveMirrorMap p s) := by
  have hs := fenchel_attained hp s
  have ht := fenchel_attained hp t
  have hinv := power_map_inverse hp s
  have hsubLeft : pairing (aboveMirrorMap p t) (s - t) =
      pairing (aboveMirrorMap p t) s - pairing (aboveMirrorMap p t) t := by
    simp [O3.pairing, Finset.sum_sub_distrib, mul_sub]
  have hsubRight : pairing s (aboveMirrorMap p t - aboveMirrorMap p s) =
      pairing s (aboveMirrorMap p t) - pairing s (aboveMirrorMap p s) := by
    simp [O3.pairing, Finset.sum_sub_distrib, mul_sub]
  have hcommTS : pairing (aboveMirrorMap p t) s =
      pairing s (aboveMirrorMap p t) := O3.pairing_comm _ _
  have hcommTT : pairing (aboveMirrorMap p t) t =
      pairing t (aboveMirrorMap p t) := O3.pairing_comm _ _
  unfold FunctionBregman
  change aboveHstar p s - aboveHstar p t - pairing (aboveMirrorMap p t) (s - t) =
    aboveH p (aboveMirrorMap p t) - aboveH p (aboveMirrorMap p s) -
      pairing (O3.powerDualityMap p (aboveMirrorMap p s))
        (aboveMirrorMap p t - aboveMirrorMap p s)
  rw [hinv]
  rw [hsubLeft, hsubRight]
  rw [hcommTS, hcommTT]
  linarith

end V7.Stage4AboveTwo

namespace V7

theorem aboveGeometry : AboveGeometryStatement := by
  intro p hp d
  exact ⟨Stage4AboveTwo.fenchel_conjugate hp,
    Stage4AboveTwo.hstar_gradient hp,
    Stage4AboveTwo.uniform_remainder hp,
    Stage4AboveTwo.bregman_conjugacy hp⟩

end V7
