/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.ResidualAlgebra
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwo.Geometry
public import LeanPool.ParameterFreeGradient.O3.Stage3Descent

/-!
The below-two primal potential identity and terminal objective-gap bound.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage3BelowTwo

open V7.ResidualAlgebra

private noncomputable def primalPotential (p : ℝ) (n : ℕ)
    (data : BelowPrimalData p d n) : ℝ :=
  belowH p data.z -
    data.u 0 * FunctionBregman data.oracle.value data.oracle.gradient
      data.z (data.x 0) -
    (∑ k ∈ Finset.range n,
      data.dw (k + 1) * FunctionBregman data.oracle.value data.oracle.gradient
        data.z (data.x (k + 1))) -
    (∑ k ∈ Finset.range n,
      data.u k *
        (FunctionBregman data.oracle.value data.oracle.gradient
            (data.x k) (data.x (k + 1)) -
          (1 / 2) *
            (lpNorm (conjugateExponent p)
              (data.oracle.gradient (data.x k) -
                data.oracle.gradient (data.x (k + 1)))) ^ (2 : ℕ))) -
    (∑ k ∈ Finset.range n,
      (FunctionBregman (belowHstar p) (belowMirrorMap p)
          (data.s k) (data.s (k + 1)) -
        (1 / 2) * (lpNorm p (data.v k - data.v (k + 1))) ^ (2 : ℕ)))

private noncomputable def primalResidual (p : ℝ) (n : ℕ)
    (data : BelowPrimalData p d n) : ℝ :=
  ∑ k ∈ Finset.range n,
    ((data.u k / 2) *
        (lpNorm (conjugateExponent p)
          (data.oracle.gradient (data.x k) -
            data.oracle.gradient (data.x (k + 1)))) ^ (2 : ℕ) +
      (1 / 2) * (lpNorm p (data.v k - data.v (k + 1))) ^ (2 : ℕ) +
      data.dw k * O3.pairing
        (data.oracle.gradient (data.x k) -
          data.oracle.gradient (data.x (k + 1)))
        (data.v (k + 1) - data.v k))

private lemma belowMirrorMap_zero {p : ℝ} (hp : 1 < p) (d : ℕ) :
    belowMirrorMap p (0 : Point d) = 0 := by
  rw [belowMirrorMap, O3.Stage2RouteB.dualityMap_zero
    (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp))]
  simp

private lemma primalPotential_le (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (n : ℕ) (data : BelowPrimalData p d n)
    (hass : BelowPrimalAssumptions data) :
    primalPotential p n data ≤ belowH p data.z := by
  rcases hass with
    ⟨hdyn, hconv, hgrad, hfstar, hmin, hu0, hun, hdwn, hweights,
      hs0, hv0, hx0, hstep, htrace, hlen, hqueried⟩
  have hn : 1 ≤ n := hdyn.1
  have hfirst := O3.Stage3Anchor.firstOrderConvex_of_coordinateGradient hconv hgrad
  have hv_all : ∀ k ≤ n, data.v k = belowMirrorMap p (data.s k) := by
    intro k hk
    cases k with
    | zero => rw [hv0, hs0, belowMirrorMap_zero hp]
    | succ k => exact (hstep k (by omega)).2.1
  have hu_nonneg : ∀ k < n, 0 ≤ data.u k := by
    intro k hk
    rw [(hweights k hk).1]
    positivity
  have hdw_succ_nonneg : ∀ k < n, 0 ≤ data.dw (k + 1) := by
    intro k hk
    by_cases hkn : k + 1 < n
    · rw [(hweights (k + 1) hkn).2.2.1]
      positivity
    · have heq : k + 1 = n := by omega
      rw [heq, hdwn]
  have hconvB : ∀ a b : Point d,
      0 ≤ FunctionBregman data.oracle.value data.oracle.gradient a b := by
    intro a b
    unfold FunctionBregman
    have h := hfirst b a
    linarith
  have hguard : ∀ k < n,
      0 ≤ FunctionBregman data.oracle.value data.oracle.gradient
          (data.x k) (data.x (k + 1)) -
        (1 / 2) *
          (lpNorm (conjugateExponent p)
            (data.oracle.gradient (data.x k) -
              data.oracle.gradient (data.x (k + 1)))) ^ (2 : ℕ) := by
    intro k hk
    exact sub_nonneg.mpr (hstep k hk).2.2.2
  have hmirror : ∀ k < n,
      0 ≤ FunctionBregman (belowHstar p) (belowMirrorMap p)
          (data.s k) (data.s (k + 1)) -
        (1 / 2) * (lpNorm p (data.v k - data.v (k + 1))) ^ (2 : ℕ) := by
    intro k hk
    have hb := ((V7.belowGeometry p hp hp2 d).2.2.2.2
      (data.s k) (data.s (k + 1))).2
    rw [← hv_all k (by omega), ← hv_all (k + 1) (by omega)] at hb
    have hnorm : lpNorm p (data.v (k + 1) - data.v k) =
        lpNorm p (data.v k - data.v (k + 1)) := by
      rw [show data.v (k + 1) - data.v k = -(data.v k - data.v (k + 1)) by abel,
        show lpNorm p (-(data.v k - data.v (k + 1))) =
          lpNorm p (data.v k - data.v (k + 1)) by
            change O3.lpNorm p (-(data.v k - data.v (k + 1))) =
              O3.lpNorm p (data.v k - data.v (k + 1))
            exact O3.lpNorm_neg p _]
    rw [hnorm] at hb
    exact sub_nonneg.mpr hb
  unfold primalPotential
  have h0 : 0 ≤ data.u 0 *
      FunctionBregman data.oracle.value data.oracle.gradient data.z (data.x 0) :=
    mul_nonneg (show 0 ≤ data.u 0 by rw [hu0]; norm_num)
      (hconvB data.z (data.x 0))
  have hsumZ : 0 ≤ ∑ k ∈ Finset.range n,
      data.dw (k + 1) * FunctionBregman data.oracle.value data.oracle.gradient
        data.z (data.x (k + 1)) := by
    exact Finset.sum_nonneg fun k hk ↦
      mul_nonneg (hdw_succ_nonneg k (Finset.mem_range.mp hk)) (hconvB _ _)
  have hsumG : 0 ≤ ∑ k ∈ Finset.range n,
      data.u k *
        (FunctionBregman data.oracle.value data.oracle.gradient
            (data.x k) (data.x (k + 1)) -
          (1 / 2) *
            (lpNorm (conjugateExponent p)
              (data.oracle.gradient (data.x k) -
                data.oracle.gradient (data.x (k + 1)))) ^ (2 : ℕ)) := by
    exact Finset.sum_nonneg fun k hk ↦
      mul_nonneg (hu_nonneg k (Finset.mem_range.mp hk))
        (hguard k (Finset.mem_range.mp hk))
  have hsumH : 0 ≤ ∑ k ∈ Finset.range n,
      (FunctionBregman (belowHstar p) (belowMirrorMap p)
          (data.s k) (data.s (k + 1)) -
        (1 / 2) * (lpNorm p (data.v k - data.v (k + 1))) ^ (2 : ℕ)) := by
    exact Finset.sum_nonneg fun k hk ↦ hmirror k (Finset.mem_range.mp hk)
  have hall : 0 ≤
      data.u 0 * FunctionBregman data.oracle.value data.oracle.gradient
          data.z (data.x 0) +
        (∑ k ∈ Finset.range n,
          data.dw (k + 1) * FunctionBregman data.oracle.value data.oracle.gradient
            data.z (data.x (k + 1))) +
        (∑ k ∈ Finset.range n,
          data.u k *
            (FunctionBregman data.oracle.value data.oracle.gradient
                (data.x k) (data.x (k + 1)) -
              (1 / 2) *
                (lpNorm (conjugateExponent p)
                  (data.oracle.gradient (data.x k) -
                    data.oracle.gradient (data.x (k + 1)))) ^ (2 : ℕ))) +
        (∑ k ∈ Finset.range n,
          (FunctionBregman (belowHstar p) (belowMirrorMap p)
              (data.s k) (data.s (k + 1)) -
            (1 / 2) * (lpNorm p (data.v k - data.v (k + 1))) ^ (2 : ℕ))) := by
    exact add_nonneg (add_nonneg (add_nonneg h0 hsumZ) hsumG) hsumH
  linarith

private lemma primalResidual_nonneg (p : ℝ) (hp : 1 < p)
    (n : ℕ) (data : BelowPrimalData p d n)
    (hass : BelowPrimalAssumptions data) :
    0 ≤ primalResidual p n data := by
  rcases hass with
    ⟨hdyn, hconv, hgrad, hfstar, hmin, hu0, hun, hdwn, hweights,
      hs0, hv0, hx0, hstep, htrace, hlen, hqueried⟩
  unfold primalResidual
  apply Finset.sum_nonneg
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  let X : ℝ := O3.lpNorm (O3.conjugateExponent p)
    (data.oracle.gradient (data.x k) - data.oracle.gradient (data.x (k + 1)))
  let Y : ℝ := O3.lpNorm p (data.v (k + 1) - data.v k)
  have hX : 0 ≤ X := O3.lpNorm_nonneg _ _
  have hY : 0 ≤ Y := O3.lpNorm_nonneg _ _
  have hd : 0 ≤ data.dw k := by
    rw [(hweights k hkn).2.2.1]
    positivity
  have hdet : 0 ≤ data.u k - (data.dw k) ^ (2 : ℕ) := by
    rw [(hweights k hkn).2.2.2]
    positivity
  have hholder := O3.abs_pairing_le_lpNorm_mul
    (O3.holderConjugate_conjugateExponent hp).symm
    (data.oracle.gradient (data.x k) - data.oracle.gradient (data.x (k + 1)))
    (data.v (k + 1) - data.v k)
  have hpair : -X * Y ≤ O3.pairing
    (data.oracle.gradient (data.x k) - data.oracle.gradient (data.x (k + 1)))
      (data.v (k + 1) - data.v k) := by
    have hraw := neg_le_of_abs_le hholder
    dsimp [X, Y] at ⊢
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpair hd
  have hpsd : 0 ≤ data.u k * X ^ (2 : ℕ) + Y ^ (2 : ℕ) -
      2 * data.dw k * X * Y := by
    nlinarith [sq_nonneg (data.dw k * X - Y),
      mul_nonneg hdet (sq_nonneg X)]
  have hnormsym : O3.lpNorm p (data.v k - data.v (k + 1)) = Y := by
    dsimp [Y]
    rw [show data.v k - data.v (k + 1) =
      -(data.v (k + 1) - data.v k) by abel]
    exact O3.lpNorm_neg p _
  change 0 ≤ data.u k / 2 * X ^ (2 : ℕ) +
    1 / 2 * (O3.lpNorm p (data.v k - data.v (k + 1))) ^ (2 : ℕ) +
    data.dw k * O3.pairing
      (data.oracle.gradient (data.x k) - data.oracle.gradient (data.x (k + 1)))
      (data.v (k + 1) - data.v k)
  rw [hnormsym]
  nlinarith

/-- Weighted oracle values telescope when increments are successive weight differences. -/
private lemma weightedOracleValues_telescope
    {p : ℝ} (n : ℕ) (data : BelowPrimalData p d n)
    (hdw_succ : ∀ k < n, data.dw (k + 1) = data.u (k + 1) - data.u k) :
      data.u 0 * data.oracle.value (data.x 0) +
          (∑ k ∈ Finset.range n,
            data.dw (k + 1) * data.oracle.value (data.x (k + 1))) +
          (∑ k ∈ Finset.range n,
            data.u k *
              (data.oracle.value (data.x (k + 1)) - data.oracle.value (data.x k))) =
        data.u n * data.oracle.value (data.x n) := by
  rw [add_assoc, ← Finset.sum_add_distrib]
  have hpoint : ∀ k ∈ Finset.range n,
      data.dw (k + 1) * data.oracle.value (data.x (k + 1)) +
          data.u k * (data.oracle.value (data.x (k + 1)) -
            data.oracle.value (data.x k)) =
        data.u (k + 1) * data.oracle.value (data.x (k + 1)) -
          data.u k * data.oracle.value (data.x k) := by
    intro k hk
    rw [hdw_succ k (Finset.mem_range.mp hk)]
    ring
  have hsumPoint :
      (∑ k ∈ Finset.range n,
        (data.dw (k + 1) * data.oracle.value (data.x (k + 1)) +
          data.u k * (data.oracle.value (data.x (k + 1)) -
            data.oracle.value (data.x k)))) =
      ∑ k ∈ Finset.range n,
        (data.u (k + 1) * data.oracle.value (data.x (k + 1)) -
          data.u k * data.oracle.value (data.x k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hpoint k hk
  rw [hsumPoint]
  have ht := sum_succ_sub n
    (fun k ↦ data.u k * data.oracle.value (data.x k))
  rw [ht]
  ring

/-- The accumulated gradient pairing equals the negative terminal dual pairing. -/
private lemma gradientPairing_sum_eq_neg
    {p : ℝ} (n : ℕ) (data : BelowPrimalData p d n) (A : VectorSeq d)
    (hs0 : data.s 0 = 0)
    (hsdiff : ∀ k < n, data.s k - data.s (k + 1) = data.dw k • A k) :
      (∑ k ∈ Finset.range n, data.dw k * O3.pairing (A k) data.z) =
        -O3.pairing (data.s n) data.z := by
  have hsumSvec :
      (∑ k ∈ Finset.range n, data.dw k • A k) = -data.s n := by
    have htel := sum_succ_sub n data.s
    have hflip : (∑ k ∈ Finset.range n,
        (data.s k - data.s (k + 1))) =
        -(∑ k ∈ Finset.range n, (data.s (k + 1) - data.s k)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      abel
    calc
      _ = ∑ k ∈ Finset.range n, (data.s k - data.s (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hsdiff k (Finset.mem_range.mp hk)).symm
      _ = -(∑ k ∈ Finset.range n, (data.s (k + 1) - data.s k)) := hflip
      _ = -(data.s n - data.s 0) := by rw [htel]
      _ = -data.s n := by rw [hs0]; simp
  calc
    _ = ∑ k ∈ Finset.range n,
        O3.pairing (data.dw k • A k) data.z := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [pairing_smul_left]
    _ = O3.pairing (∑ k ∈ Finset.range n, data.dw k • A k) data.z :=
      (pairing_finset_sum_left (Finset.range n) (fun k ↦ data.dw k • A k) data.z).symm
    _ = _ := by rw [hsumSvec]; simp [O3.pairing]

/-- Discrete summation by parts rewrites the weighted gradient-position pairings. -/
private lemma weightedGradientPairings_telescope
    {p : ℝ} (n : ℕ) (data : BelowPrimalData p d n) (A : VectorSeq d)
    (hdw_succ : ∀ k < n, data.dw (k + 1) = data.u (k + 1) - data.u k)
    (hAn : A (n + 1) = 0) :
      -data.u 0 * O3.pairing (A 0) (data.x 0) -
          (∑ k ∈ Finset.range n,
            data.dw (k + 1) * O3.pairing (A (k + 1)) (data.x (k + 1))) +
          (∑ k ∈ Finset.range n,
            data.u k * O3.pairing (A (k + 1)) (data.x k - data.x (k + 1))) =
        -(∑ k ∈ Finset.range (n + 1),
          data.u k * O3.pairing (A k - A (k + 1)) (data.x k)) := by
  have hdiag := sum_shift_end n
    (fun k ↦ data.u k * O3.pairing (A k) (data.x k))
  rw [Finset.sum_range_succ]
  simp_rw [pairing_sub_left, pairing_sub_right]
  have hsumCoeff :
      (∑ k ∈ Finset.range n,
        data.dw (k + 1) * O3.pairing (A (k + 1)) (data.x (k + 1))) +
      (∑ k ∈ Finset.range n,
        data.u k * O3.pairing (A (k + 1)) (data.x (k + 1))) =
      ∑ k ∈ Finset.range n,
        data.u (k + 1) * O3.pairing (A (k + 1)) (data.x (k + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hdw_succ k (Finset.mem_range.mp hk)]
    ring
  simp_rw [mul_sub]
  repeat' rw [Finset.sum_sub_distrib]
  rw [hAn, show O3.pairing (0 : Point d) (data.x n) = 0 by simp [O3.pairing]]
  linarith [hdiag, hsumCoeff]

/-- The dual mirror-potential differences telescope from the zero initial dual vector. -/
private lemma mirrorPotential_telescope
    (p : ℝ) (hp : 1 < p) (n : ℕ) (data : BelowPrimalData p d n)
    (hs0 : data.s 0 = 0) :
      -(∑ k ∈ Finset.range n,
        (belowHstar p (data.s k) - belowHstar p (data.s (k + 1)))) =
        belowHstar p (data.s n) := by
  have ht := sum_succ_sub n (fun k ↦ belowHstar p (data.s k))
  have hzero : belowHstar p (data.s 0) = 0 := by
    rw [hs0, belowHstar]
    change (p - 1) / 2 * O3.lpNorm (O3.conjugateExponent p) 0 ^ 2 = 0
    rw [O3.lpNorm_zero (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp))]
    ring
  have hflip : (∑ k ∈ Finset.range n,
      (belowHstar p (data.s k) - belowHstar p (data.s (k + 1)))) =
      -(∑ k ∈ Finset.range n,
        (belowHstar p (data.s (k + 1)) - belowHstar p (data.s k))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hflip, ht, hzero]
  ring

private lemma primalPotential_identity (p : ℝ) (hp : 1 < p) (_hp2 : p < 2)
    (n : ℕ) (data : BelowPrimalData p d n)
    (hass : BelowPrimalAssumptions data) :
    primalPotential p n data =
      data.u n * (data.oracle.value (data.x n) - data.oracle.value data.z) +
        belowH p data.z + belowHstar p (data.s n) -
        O3.pairing (data.s n) data.z + primalResidual p n data := by
  rcases hass with
    ⟨hdyn, hconv, hgrad, hfstar, hmin, hu0, hun, hdwn, hweights,
      hs0, hv0, hx0, hstep, htrace, hlen, hqueried⟩
  have hn : 1 ≤ n := hdyn.1
  let A : VectorSeq d := fun k ↦
    if k ≤ n then data.oracle.gradient (data.x k) else 0
  have hA (k : ℕ) (hk : k ≤ n) : A k = data.oracle.gradient (data.x k) := by
    simp [A, hk]
  have hAn : A (n + 1) = 0 := by simp [A]
  have hdw0 : data.dw 0 = data.u 0 := by
    have h := (hweights 0 (by omega)).2.1
    simpa using h
  have hdw_succ : ∀ k < n,
      data.dw (k + 1) = data.u (k + 1) - data.u k := by
    intro k hk
    by_cases hnext : k + 1 < n
    · have h := (hweights (k + 1) hnext).2.1
      simpa using h
    · have heq : k + 1 = n := by omega
      rw [heq, hdwn, hun]
      have hpred : n - 1 = k := by omega
      rw [hpred]
      ring
  have hu_pos : ∀ j, 1 ≤ j → j ≤ n → 0 < data.u j := by
    intro j hj1 hjn
    by_cases hj : j < n
    · rw [(hweights j hj).1]
      positivity
    · have heq : j = n := by omega
      rw [heq, hun, (hweights (n - 1) (by omega)).1]
      positivity
  have hsdiff : ∀ k < n, data.s k - data.s (k + 1) = data.dw k • A k := by
    intro k hk
    rw [(hstep k hk).1, hA k (by omega)]
    abel
  have hxweighted : ∀ k < n,
      data.u (k + 1) • data.x (k + 1) - data.u k • data.x k =
        data.dw (k + 1) • data.v (k + 1) +
          data.dw k • (data.v (k + 1) - data.v k) := by
    intro k hk
    have hu : data.u (k + 1) ≠ 0 := (hu_pos (k + 1) (by omega) (by omega)).ne'
    rw [(hstep k hk).2.2.1]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hu]
    ring
  have habel := primal_abel n data.u data.dw A data.v data.x data.s
    hx0 hv0 hAn hdwn hsdiff hxweighted
  have hfun := weightedOracleValues_telescope n data hdw_succ
  have hzweights :
      data.u 0 * O3.pairing (A 0) data.z +
          (∑ k ∈ Finset.range n,
            data.dw (k + 1) * O3.pairing (A (k + 1)) data.z) =
        ∑ k ∈ Finset.range n, data.dw k * O3.pairing (A k) data.z := by
    have hshift := sum_shift_end n
      (fun k ↦ data.dw k * O3.pairing (A k) data.z)
    rw [hdwn, zero_mul, add_zero] at hshift
    rw [← hdw0]
    have hsum :
        (∑ k ∈ Finset.range n,
          data.dw (k + 1) * O3.pairing (A (k + 1)) data.z) =
        ∑ k ∈ Finset.range n,
          (fun j ↦ data.dw j * O3.pairing (A j) data.z) (k + 1) := by rfl
    rw [hsum]
    exact hshift
  have hzpair := gradientPairing_sum_eq_neg n data A hs0 hsdiff
  have hz :
      data.u 0 * O3.pairing (A 0) data.z +
          (∑ k ∈ Finset.range n,
            data.dw (k + 1) * O3.pairing (A (k + 1)) data.z) =
        -O3.pairing (data.s n) data.z := hzweights.trans hzpair
  have hxpair := weightedGradientPairings_telescope n data A hdw_succ hAn
  have hhstar := mirrorPotential_telescope p hp n data hs0
  have habelActual :
      (∑ k ∈ Finset.range n,
          O3.pairing (data.s k - data.s (k + 1)) (data.v (k + 1))) -
        (∑ k ∈ Finset.range (n + 1),
          data.u k * O3.pairing (A k - A (k + 1)) (data.x k)) =
      ∑ k ∈ Finset.range n,
        data.dw k * O3.pairing
          (data.oracle.gradient (data.x k) -
            data.oracle.gradient (data.x (k + 1)))
          (data.v (k + 1) - data.v k) := by
    rw [habel]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    rw [hA k hkn.le, hA (k + 1) (by omega)]
  have hweightSum : data.u 0 +
      (∑ k ∈ Finset.range n, data.dw (k + 1)) = data.u n := by
    have hsum : (∑ k ∈ Finset.range n, data.dw (k + 1)) =
        ∑ k ∈ Finset.range n, (data.u (k + 1) - data.u k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hdw_succ k (Finset.mem_range.mp hk)]
    rw [hsum, sum_succ_sub]
    ring
  have hzActual :
      data.u 0 * O3.pairing (data.oracle.gradient (data.x 0)) data.z +
          (∑ k ∈ Finset.range n,
            data.dw (k + 1) *
              O3.pairing (data.oracle.gradient (data.x (k + 1))) data.z) =
        -O3.pairing (data.s n) data.z := by
    rw [← hA 0 (by omega)]
    have hsumeq :
        (∑ k ∈ Finset.range n,
          data.dw (k + 1) *
            O3.pairing (data.oracle.gradient (data.x (k + 1))) data.z) =
        ∑ k ∈ Finset.range n,
          data.dw (k + 1) * O3.pairing (A (k + 1)) data.z := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hA (k + 1) (by have := Finset.mem_range.mp hk; omega)]
    rw [hsumeq]
    exact hz
  have hxActual :
      -data.u 0 * O3.pairing (data.oracle.gradient (data.x 0)) (data.x 0) -
          (∑ k ∈ Finset.range n,
            data.dw (k + 1) *
              O3.pairing (data.oracle.gradient (data.x (k + 1))) (data.x (k + 1))) +
          (∑ k ∈ Finset.range n,
            data.u k * O3.pairing (data.oracle.gradient (data.x (k + 1)))
              (data.x k - data.x (k + 1))) =
        -(∑ k ∈ Finset.range (n + 1),
          data.u k * O3.pairing (A k - A (k + 1)) (data.x k)) := by
    rw [← hA 0 (by omega)]
    have hsum1 :
        (∑ k ∈ Finset.range n,
          data.dw (k + 1) *
            O3.pairing (data.oracle.gradient (data.x (k + 1))) (data.x (k + 1))) =
        ∑ k ∈ Finset.range n,
          data.dw (k + 1) * O3.pairing (A (k + 1)) (data.x (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hA (k + 1) (by have := Finset.mem_range.mp hk; omega)]
    have hsum2 :
        (∑ k ∈ Finset.range n,
          data.u k * O3.pairing (data.oracle.gradient (data.x (k + 1)))
            (data.x k - data.x (k + 1))) =
        ∑ k ∈ Finset.range n,
          data.u k * O3.pairing (A (k + 1)) (data.x k - data.x (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hA (k + 1) (by have := Finset.mem_range.mp hk; omega)]
    rw [hsum1, hsum2]
    exact hxpair
  have hmirrorPair :
      (∑ k ∈ Finset.range n,
        O3.pairing (belowMirrorMap p (data.s (k + 1)))
          (data.s k - data.s (k + 1))) =
      ∑ k ∈ Finset.range n,
        O3.pairing (data.v (k + 1)) (data.s k - data.s (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← (hstep k (Finset.mem_range.mp hk)).2.1]
  have hconst : data.oracle.value data.z *
      (∑ k ∈ Finset.range n, data.dw (k + 1)) =
      ∑ k ∈ Finset.range n, data.oracle.value data.z * data.dw (k + 1) := by
    rw [Finset.mul_sum]
  have hcomm0 :
      (∑ k ∈ Finset.range n,
        O3.pairing (data.v (k + 1)) (data.s k)) =
      ∑ k ∈ Finset.range n,
        O3.pairing (data.s k) (data.v (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact O3.pairing_comm _ _
  have hcomm1 :
      (∑ k ∈ Finset.range n,
        O3.pairing (data.v (k + 1)) (data.s (k + 1))) =
      ∑ k ∈ Finset.range n,
        O3.pairing (data.s (k + 1)) (data.v (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact O3.pairing_comm _ _
  unfold primalPotential primalResidual FunctionBregman
  have hpairingEq : ∀ a b : Point d, pairing a b = O3.pairing a b := by
    intro a b
    rfl
  simp_rw [hpairingEq]
  simp_rw [mul_sub]
  repeat' rw [Finset.sum_sub_distrib]
  rw [hmirrorPair]
  simp_rw [pairing_sub_right, pairing_sub_left]
  simp_rw [mul_sub]
  repeat' rw [Finset.sum_add_distrib]
  repeat' rw [Finset.sum_sub_distrib]
  simp_rw [pairing_sub_right, pairing_sub_left] at hxActual habelActual
  ring_nf at ⊢ hfun hzActual hxActual hhstar habelActual hweightSum hconst hcomm0 hcomm1
  linear_combination
    (norm := (simp only [Finset.sum_add_distrib,
      Finset.sum_sub_distrib]; ring))
    hfun + hzActual + hxActual + hhstar + habelActual -
      data.oracle.value data.z * hweightSum + hconst + hcomm0 - hcomm1

theorem belowPrimal : V7.BelowPrimalStatement := by
  intro p hp hp2 d n data hass
  have hpot := primalPotential_le p hp hp2 n data hass
  have hid := primalPotential_identity p hp hp2 n data hass
  have hres := primalResidual_nonneg p hp n data hass
  have hfenchel := fenchel_upper hp (data.s n) data.z
  rcases hass with
    ⟨hdyn, hconv, hgrad, hfstar, hmin, hu0, hun, hdwn, hweights,
      hs0, hv0, hx0, hstep, htrace, hlen, hqueried⟩
  have hn : 1 ≤ n := hdyn.1
  have hunpos : 0 < data.u n := by
    rw [hun, (hweights (n - 1) (by omega)).1]
    positivity
  have hscaled : data.u n *
      (data.oracle.value (data.x n) - data.oracle.value data.z) ≤
      belowH p data.z := by
    rw [hid] at hpot
    linarith
  rw [hfstar]
  exact (le_div_iff₀ hunpos).2 (by
    nlinarith)

end V7.Stage3BelowTwo

namespace V7

theorem belowPrimal : BelowPrimalStatement :=
  Stage3BelowTwo.belowPrimal

end V7
