/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Shared
import LeanPool.ParameterFreeGradient.O3.Stage2BelowGeometry
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-!
Conjugacy, gradients, and Bregman geometry of the scaled squared norms below exponent two.
-/

open scoped BigOperators

namespace V7.Stage3BelowTwo

private noncomputable def pairingCLM (g : Point d) : Point d →L[ℝ] ℝ :=
  ∑ i : Fin d, (g i) • ContinuousLinearMap.proj i

@[simp] private lemma pairingCLM_apply (g h : Point d) :
    pairingCLM g h = O3.pairing g h := by
  simp [pairingCLM, O3.pairing]

private lemma conjugateExponent_involutive {p : ℝ} (hp : 1 < p) :
    conjugateExponent (conjugateExponent p) = p := by
  change O3.conjugateExponent (O3.conjugateExponent p) = p
  rw [O3.conjugateExponent_eq, O3.conjugateExponent_eq]
  have hne : p - 1 ≠ 0 := by linarith
  field_simp [hne]
  ring

private lemma belowH_eq_scaled_energy {p : ℝ} (hp : 1 < p) (x : Point d) :
    belowH p x = (1 / (p - 1)) * O3.Stage2RouteB.squaredLpEnergy p x := by
  rw [belowH, O3.Stage2RouteB.squaredLpEnergy_eq_quadraticRegularizer
    (by linarith : 0 < p)]
  simp only [O3.quadraticRegularizer, sub_zero]
  have hne : p - 1 ≠ 0 := by linarith
  field_simp [hne]

private lemma belowHstar_eq_scaled_energy {p : ℝ} (hp : 1 < p) (s : Point d) :
    belowHstar p s = (p - 1) *
      O3.Stage2RouteB.squaredLpEnergy (conjugateExponent p) s := by
  rw [belowHstar, O3.Stage2RouteB.squaredLpEnergy_eq_quadraticRegularizer
    (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp))]
  simp only [O3.quadraticRegularizer, sub_zero]
  ring

private lemma mirrorMap_norm {p : ℝ} (hp : 1 < p) (s : Point d) :
    lpNorm p (belowMirrorMap p s) = (p - 1) * lpNorm (conjugateExponent p) s := by
  rw [belowMirrorMap]
  change O3.lpNorm p ((p - 1) • O3.dualityMap (O3.conjugateExponent p) s) =
    (p - 1) * O3.lpNorm (O3.conjugateExponent p) s
  rw [O3.Stage2RouteC.lpNorm_smul (by linarith : 1 ≤ p)]
  have hq := O3.Stage2RouteB.lpNorm_dualityMap
    (O3.one_lt_conjugateExponent hp) s
  have hinv : O3.conjugateExponent (O3.conjugateExponent p) = p := by
    exact conjugateExponent_involutive hp
  rw [hinv] at hq
  rw [hq, abs_of_pos (by linarith : 0 < p - 1)]

private lemma mirrorMap_pairing {p : ℝ} (hp : 1 < p) (s : Point d) :
    pairing s (belowMirrorMap p s) =
      (p - 1) * (lpNorm (conjugateExponent p) s) ^ (2 : ℕ) := by
  rw [belowMirrorMap]
  change O3.pairing s ((p - 1) • O3.dualityMap (O3.conjugateExponent p) s) =
    (p - 1) * O3.lpNorm (O3.conjugateExponent p) s ^ 2
  rw [O3.Stage2RouteD.pairing_smul_right, O3.pairing_comm]
  rw [O3.Stage2RouteB.pairing_dualityMap_self
    (O3.one_lt_conjugateExponent hp)]

private lemma dualityMap_pos_smul {p a : ℝ} (hp : 1 < p) (ha : 0 < a)
    (x : Point d) :
    O3.dualityMap p (a • x) = a • O3.dualityMap p x := by
  by_cases hx : x = 0
  · subst x
    simp [O3.Stage2RouteB.dualityMap_zero (by linarith : 0 < p)]
  · have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
    have hnx : 0 < O3.lpNorm p x := O3.lpNorm_pos_of_ne_zero hx
    have hnax : 0 < O3.lpNorm p (a • x) := O3.lpNorm_pos_of_ne_zero hax
    rw [O3.dualityMap, ite_eq_right hnax.ne', O3.dualityMap, ite_eq_right hnx.ne']
    have hnorm : O3.lpNorm p (a • x) = a * O3.lpNorm p x := by
      change O3.lpNorm p (fun i ↦ a * x i) = a * O3.lpNorm p x
      rw [O3.Stage2RouteB.lpNorm_scalar_mul (by linarith : 0 < p)]
      rw [abs_of_pos ha]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hnorm, abs_mul, abs_of_pos ha]
    rw [Real.mul_rpow ha.le hnx.le]
    rw [Real.mul_rpow ha.le (abs_nonneg (x i))]
    have haexp : a ^ (2 - p) * a ^ (p - 2) = 1 := by
      rw [← Real.rpow_add ha]
      norm_num
    calc
      a ^ (2 - p) * O3.lpNorm p x ^ (2 - p) *
          (a ^ (p - 2) * |x i| ^ (p - 2) * (a * x i)) =
          (a ^ (2 - p) * a ^ (p - 2)) * a *
            (O3.lpNorm p x ^ (2 - p) * (|x i| ^ (p - 2) * x i)) := by ring
      _ = a * (O3.lpNorm p x ^ (2 - p) * (|x i| ^ (p - 2) * x i)) := by
        rw [haexp]
        ring

private lemma primalGradient_mirrorMap {p : ℝ} (hp : 1 < p) (s : Point d) :
    (1 / (p - 1)) • O3.dualityMap p (belowMirrorMap p s) = s := by
  rw [belowMirrorMap]
  have hpos : 0 < p - 1 := by linarith
  have hhom := dualityMap_pos_smul hp hpos
    (O3.dualityMap (conjugateExponent p) s)
  rw [hhom]
  have hcomp := O3.Stage2RouteB.dualityMap_conjugate_comp
    (O3.one_lt_conjugateExponent hp) s
  have hinv : O3.conjugateExponent (O3.conjugateExponent p) = p := by
    exact conjugateExponent_involutive hp
  rw [hinv] at hcomp
  rw [hcomp]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hpos.ne']

lemma fenchel_upper {p : ℝ} (hp : 1 < p) (s x : Point d) :
    pairing s x - belowH p x ≤ belowHstar p s := by
  let q := conjugateExponent p
  let w : Point d := (p - 1) • s
  have hfy := O3.Stage2RouteB.fenchelYoung_lower hp w x
  have hpos : 0 < p - 1 := by linarith
  have hwenergy := O3.Stage2RouteB.squaredLpEnergy_scalar_mul
    (p := q) (a := p - 1) (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp)) s
  have hpair : O3.pairing w x = (p - 1) * O3.pairing s x := by
    exact O3.Stage2RouteD.pairing_smul_left (p - 1) s x
  change O3.pairing ((p - 1) • s) x -
      O3.Stage2RouteB.squaredLpEnergy q (fun i ↦ (p - 1) * s i) ≤
      O3.Stage2RouteB.squaredLpEnergy p x at hfy
  rw [hpair, hwenergy] at hfy
  rw [belowH_eq_scaled_energy hp, belowHstar_eq_scaled_energy hp]
  have hne : p - 1 ≠ 0 := hpos.ne'
  apply (le_of_mul_le_mul_left (a := p - 1) ?_ hpos)
  field_simp [hne]
  nlinarith

private lemma fenchel_attained {p : ℝ} (hp : 1 < p) (s : Point d) :
    pairing s (belowMirrorMap p s) - belowH p (belowMirrorMap p s) =
      belowHstar p s := by
  rw [mirrorMap_pairing hp, belowH, belowHstar, mirrorMap_norm hp]
  have hpos : 0 < p - 1 := by linarith
  field_simp [hpos.ne']
  ring

private lemma fenchelConjugate_belowH {p : ℝ} (hp : 1 < p) (s : Point d) :
    FenchelConjugate (belowH p) s = belowHstar p s := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · exact ⟨belowMirrorMap p s, (fenchel_attained hp s).symm⟩
  · intro r hr
    rcases hr with ⟨x, rfl⟩
    exact fenchel_upper hp s x

private lemma squaredLpEnergy_remainder_nonneg {q : ℝ} (hq : 1 < q)
    (x h : Point d) :
    0 ≤ O3.Stage2RouteB.squaredLpEnergy q (x + h) -
      O3.Stage2RouteB.squaredLpEnergy q x -
      O3.pairing (O3.dualityMap q x) h := by
  have hfy := O3.Stage2RouteB.fenchelYoung_lower hq
    (O3.dualityMap q x) (x + h)
  rw [O3.Stage2RouteB.squaredLpEnergy_dualityMap hq] at hfy
  have hpair := O3.Stage2RouteB.pairing_dualityMap_self hq x
  have henergy := O3.Stage2RouteB.squaredLpEnergy_eq_quadraticRegularizer
    (by linarith : 0 < q) x
  simp only [O3.quadraticRegularizer, sub_zero] at henergy
  rw [O3.Stage2RouteB.pairing_add_right', hpair] at hfy
  nlinarith

private lemma squaredLpEnergy_hasFDerivAt {q : ℝ} (hq : 2 < q)
    (x : Point d) :
    HasFDerivAt (fun y : Point d ↦ O3.Stage2RouteB.squaredLpEnergy q y)
      (pairingCLM (O3.dualityMap q x)) x := by
  let _ : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ q)⟩
  let T : Point d →L[ℝ]
      PiLp (ENNReal.ofReal q) (fun _ : Fin d ↦ ℝ) :=
    (PiLp.continuousLinearEquiv (ENNReal.ofReal q) ℝ
      (fun _ : Fin d ↦ ℝ)).symm
  let c : ℝ := (q - 1) / 2
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hbound : ∀ h : Point d,
      ‖O3.Stage2RouteB.squaredLpEnergy q (x + h) -
          O3.Stage2RouteB.squaredLpEnergy q x - pairingCLM (O3.dualityMap q x) h‖ ≤
        (c * ‖T‖ ^ (2 : ℕ)) * ‖‖h‖ ^ (2 : ℕ)‖ := by
    intro h
    have hlo := squaredLpEnergy_remainder_nonneg (by linarith : 1 < q) x h
    have hhi := O3.Stage2Closure.squaredLpEnergy_smooth_above_two hq x (x + h)
    have hsub : x + h - x = h := by abel
    rw [hsub] at hhi
    rw [pairingCLM_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg hlo, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖h‖)]
    have hnorm : O3.lpNorm q h = ‖T h‖ := by
      rw [O3.Stage2RouteC.lpNorm_eq_piLpNorm (by linarith : 1 ≤ q)]
      rfl
    have hTop : ‖T h‖ ≤ ‖T‖ * ‖h‖ := T.le_opNorm h
    calc
      O3.Stage2RouteB.squaredLpEnergy q (x + h) -
          O3.Stage2RouteB.squaredLpEnergy q x -
          O3.pairing (O3.dualityMap q x) h ≤
          c * O3.lpNorm q h ^ (2 : ℕ) := by
            dsimp [c]
            linarith
      _ = c * ‖T h‖ ^ (2 : ℕ) := by rw [hnorm]
      _ ≤ c * (‖T‖ * ‖h‖) ^ (2 : ℕ) := by
        gcongr
      _ = (c * ‖T‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by ring
  have hbig :
      (fun h : Point d ↦ O3.Stage2RouteB.squaredLpEnergy q (x + h) -
        O3.Stage2RouteB.squaredLpEnergy q x - pairingCLM (O3.dualityMap q x) h) =O[nhds 0]
        (fun h : Point d ↦ ‖h‖ ^ (2 : ℕ)) :=
    (Asymptotics.isBigOWith_of_le' (nhds 0) hbound).isBigO
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2))

private lemma belowHstar_hasFDerivAt {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (s : Point d) :
    HasFDerivAt (fun t : Point d ↦ belowHstar p t)
      (pairingCLM (belowMirrorMap p s)) s := by
  have hq : 2 < O3.conjugateExponent p := by
    rw [O3.conjugateExponent_eq, lt_div_iff₀ (by linarith : 0 < p - 1)]
    linarith
  have hraw := (squaredLpEnergy_hasFDerivAt hq s).const_mul (p - 1)
  have hfun := hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ belowHstar_eq_scaled_energy hp t)
  apply hfun.congr_fderiv
  ext h
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, pairingCLM_apply]
  rw [belowMirrorMap]
  change (p - 1) * O3.pairing (O3.dualityMap (O3.conjugateExponent p) s) h =
    O3.pairing ((p - 1) • O3.dualityMap (O3.conjugateExponent p) s) h
  exact (O3.Stage2RouteD.pairing_smul_left (p - 1)
    (O3.dualityMap (O3.conjugateExponent p) s) h).symm

private lemma belowHstar_coordinateGradient {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (d : ℕ) :
    O3.IsCoordinateGradient
      (fun s : Point d ↦ belowHstar p s)
      (fun s : Point d ↦ belowMirrorMap p s) := by
  intro s
  have hs := belowHstar_hasFDerivAt hp hp2 s
  refine ⟨hs.differentiableAt, ?_⟩
  intro h
  rw [hs.fderiv]
  exact pairingCLM_apply _ _

private lemma belowH_strong {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (x y : Point d) :
    belowH p y ≥ belowH p x +
      pairing ((1 / (p - 1)) • O3.dualityMap p x) (y - x) +
      (1 / 2) * (lpNorm p (y - x)) ^ (2 : ℕ) := by
  have hold := O3.belowGeometry p hp hp2.le d x y
  rw [← O3.Stage2RouteB.squaredLpEnergy_eq_quadraticRegularizer
      (by linarith : 0 < p) x,
    ← O3.Stage2RouteB.squaredLpEnergy_eq_quadraticRegularizer
      (by linarith : 0 < p) y] at hold
  rw [belowH_eq_scaled_energy hp, belowH_eq_scaled_energy hp]
  change (1 / (p - 1)) * O3.Stage2RouteB.squaredLpEnergy p y ≥
    (1 / (p - 1)) * O3.Stage2RouteB.squaredLpEnergy p x +
      O3.pairing ((1 / (p - 1)) • O3.dualityMap p x) (y - x) +
      (1 / 2) * O3.lpNorm p (y - x) ^ 2
  rw [O3.Stage2RouteD.pairing_smul_left]
  have hpos : 0 < p - 1 := by linarith
  have hne : p - 1 ≠ 0 := hpos.ne'
  have hinv : 0 ≤ 1 / (p - 1) := (one_div_pos.mpr hpos).le
  have hscaled := mul_le_mul_of_nonneg_left hold hinv
  have hcancel : (1 / (p - 1)) * ((p - 1) / 2) = 1 / 2 := by
    field_simp [hne]
  calc
    (1 / (p - 1)) * O3.Stage2RouteB.squaredLpEnergy p y ≥
        (1 / (p - 1)) *
          (O3.Stage2RouteB.squaredLpEnergy p x +
            O3.pairing (O3.dualityMap p x) (y - x) +
            (p - 1) / 2 * O3.lpNorm p (y - x) ^ 2) := hscaled
    _ = (1 / (p - 1)) * O3.Stage2RouteB.squaredLpEnergy p x +
        1 / (p - 1) * O3.pairing (O3.dualityMap p x) (y - x) +
        1 / 2 * O3.lpNorm p (y - x) ^ 2 := by rw [← hcancel]; ring

private lemma bregman_duality {p : ℝ} (hp : 1 < p) (s t : Point d) :
    FunctionBregman (belowHstar p) (belowMirrorMap p) s t =
      FunctionBregman (belowH p)
        (fun x ↦ (1 / (p - 1)) • O3.dualityMap p x)
        (belowMirrorMap p t) (belowMirrorMap p s) := by
  have hs := fenchel_attained hp s
  have ht := fenchel_attained hp t
  have hgrad := primalGradient_mirrorMap hp s
  unfold FunctionBregman
  rw [← hs, ← ht]
  change O3.pairing s (belowMirrorMap p s) - belowH p (belowMirrorMap p s) -
      (O3.pairing t (belowMirrorMap p t) - belowH p (belowMirrorMap p t)) -
      O3.pairing (belowMirrorMap p t) (s - t) =
    belowH p (belowMirrorMap p t) - belowH p (belowMirrorMap p s) -
      O3.pairing ((1 / (p - 1)) • O3.dualityMap p (belowMirrorMap p s))
        (belowMirrorMap p t - belowMirrorMap p s)
  rw [hgrad]
  have hleft : O3.pairing (belowMirrorMap p t) (s - t) =
      O3.pairing (belowMirrorMap p t) s - O3.pairing (belowMirrorMap p t) t := by
    simp only [O3.pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hright : O3.pairing s (belowMirrorMap p t - belowMirrorMap p s) =
      O3.pairing s (belowMirrorMap p t) - O3.pairing s (belowMirrorMap p s) := by
    simp only [O3.pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hleft, hright, O3.pairing_comm (belowMirrorMap p t) s,
    O3.pairing_comm (belowMirrorMap p t) t]
  ring

private lemma bregman_lower {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (s t : Point d) :
    FunctionBregman (belowHstar p) (belowMirrorMap p) s t ≥
      (1 / 2) * (lpNorm p (belowMirrorMap p t - belowMirrorMap p s)) ^ (2 : ℕ) := by
  rw [bregman_duality hp]
  unfold FunctionBregman
  have hstrong := belowH_strong hp hp2 (belowMirrorMap p s) (belowMirrorMap p t)
  linarith

theorem belowGeometry : V7.BelowGeometryStatement := by
  intro p hp hp2 d
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y ↦ belowH_strong hp hp2 x y
  · intro x
    exact ⟨O3.Stage2RouteB.lpNorm_dualityMap hp x,
      O3.Stage2RouteB.pairing_dualityMap_self hp x,
      O3.Stage2RouteB.dualityMap_conjugate_comp hp x⟩
  · exact fun s ↦ fenchelConjugate_belowH hp s
  · exact belowHstar_coordinateGradient hp hp2 d
  · intro s t
    exact ⟨bregman_duality hp s t, bregman_lower hp hp2 s t⟩

end V7.Stage3BelowTwo

namespace V7

theorem belowGeometry : BelowGeometryStatement :=
  Stage3BelowTwo.belowGeometry

end V7
