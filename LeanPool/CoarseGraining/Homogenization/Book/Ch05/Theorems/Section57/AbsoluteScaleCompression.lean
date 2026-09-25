/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteMinimalScale
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EntryScaleCompression

/-! # Absolute Scale Compression -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Deterministic compression for the absolute quenched scale

This file contains the deterministic estimates used to compress the explicit
absolute minimal-scale normalization to the manuscript envelope
`exp(C log^2(2 + thetaHat))`.
-/

noncomputable section

/-- An entry-scale factor times a fixed polynomial in `theta` is absorbed by
the manuscript `exp(C log^2(2 + theta))` envelope. -/
theorem const_mul_entry_rpow_mul_rpow_max_one_le_exp_logSq
    {A G θ Centry r p : ℝ}
    (hA : 0 < A) (hG : 1 ≤ G) (hθ : 0 ≤ θ)
    (hCentry : 0 < Centry) (hr : 0 ≤ r) (hp : 0 ≤ p)
    (hentry :
      G ≤ Real.exp (Centry * (Real.log (2 + θ)) ^ (2 : ℕ))) :
    ∃ C : ℝ, 0 < C ∧
      A * G ^ r * (max 1 θ) ^ p ≤
        Real.exp (C * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
  let Cθ : ℝ := 1 + (4 * max 0 (Real.log A) + 2 * p)
  let C : ℝ := r * Centry + Cθ
  have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
  have hG_pos : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hentry_r :
      G ^ r ≤ Real.exp ((r * Centry) * L2) := by
    have hpow :
        G ^ r ≤
          (Real.exp (Centry * L2)) ^ r :=
      Real.rpow_le_rpow hG_pos.le hentry hr
    have hexp_eq :
        (Real.exp (Centry * L2)) ^ r =
          Real.exp ((r * Centry) * L2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _)]
      rw [Real.log_exp]
      ring_nf
    exact hpow.trans_eq hexp_eq
  have hθ_poly :
      A * (max 1 θ) ^ p ≤ Real.exp (Cθ * L2) := by
    have hbase :=
      const_mul_rpow_max_one_le_exp_logSq
        (A := A) (θ := θ) (p := p) hA hθ hp
    have hcoef :
        (4 * max 0 (Real.log A) + 2 * p) * L2 ≤ Cθ * L2 := by
      dsimp [Cθ]
      nlinarith
    exact hbase.trans (Real.exp_le_exp.mpr hcoef)
  have hC_pos : 0 < C := by
    have hCθ_pos : 0 < Cθ := by
      dsimp [Cθ]
      have hmax_nonneg : 0 ≤ max 0 (Real.log A) := le_max_left 0 _
      nlinarith
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  calc
    A * G ^ r * (max 1 θ) ^ p
        = G ^ r * (A * (max 1 θ) ^ p) := by ring
    _ ≤ Real.exp ((r * Centry) * L2) * Real.exp (Cθ * L2) :=
        mul_le_mul hentry_r hθ_poly (by positivity) (by positivity)
    _ = Real.exp (C * L2) := by
        rw [← Real.exp_add]
        dsimp [C]
        ring_nf

/-- Natural entry scales are dominated by their base-three exponential. -/
theorem nat_cast_le_pow_three_nat (N : ℕ) :
    (N : ℝ) ≤ (3 : ℝ) ^ N := by
  have h :=
    Nat.cast_le_pow_div_sub (α := ℝ) (a := (3 : ℝ))
      (by norm_num : (1 : ℝ) < 3) N
  have htwo : (0 : ℝ) < 3 - 1 := by norm_num
  have hle : (3 : ℝ) ^ N / (3 - 1) ≤ (3 : ℝ) ^ N := by
    have hpow_nonneg : 0 ≤ (3 : ℝ) ^ N := by positivity
    nlinarith
  exact h.trans hle

/-- A logarithmic ceiling cutoff is polynomial in any positive upper bound for
the underlying quantity. -/
theorem pow_three_natCeil_max_zero_log_le_const_mul_rpow_of_le
    {M A G p : ℝ}
    (hM_one : 1 ≤ M) (hA_pos : 0 < A) (hG_one : 1 ≤ G)
    (hM_le : M ≤ A * G ^ p) :
    (3 : ℝ) ^ Nat.ceil (max 0 (Real.log M)) ≤
      3 * A ^ (Real.log (3 : ℝ)) * G ^ (p * Real.log (3 : ℝ)) := by
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hG_pos : 0 < G := lt_of_lt_of_le zero_lt_one hG_one
  have hGp_pos : 0 < G ^ p := Real.rpow_pos_of_pos hG_pos p
  have hAG_pos : 0 < A * G ^ p := mul_pos hA_pos hGp_pos
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_one
  have hlogM_nonneg : 0 ≤ Real.log M := Real.log_nonneg hM_one
  have hceil_raw :
      (3 : ℝ) ^ Nat.ceil (max 0 (Real.log M)) ≤
        3 * Real.exp (Real.log (3 : ℝ) * max 0 (Real.log M)) := by
    simpa [Real.rpow_natCast] using
      rpow_three_natCeil_le_three_mul_exp
        (y := max 0 (Real.log M)) (le_max_left 0 (Real.log M))
  have hlog_le : Real.log M ≤ Real.log (A * G ^ p) :=
    Real.log_le_log hM_pos hM_le
  have hexp_le :
      Real.exp (Real.log (3 : ℝ) * max 0 (Real.log M)) ≤
        Real.exp (Real.log (3 : ℝ) * Real.log (A * G ^ p)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [max_eq_right hlogM_nonneg]
    exact mul_le_mul_of_nonneg_left hlog_le hlog3_pos.le
  have hexp_eq :
      Real.exp (Real.log (3 : ℝ) * Real.log (A * G ^ p)) =
        A ^ (Real.log (3 : ℝ)) * G ^ (p * Real.log (3 : ℝ)) := by
    have hAG :
        Real.exp (Real.log (3 : ℝ) * Real.log (A * G ^ p)) =
          (A * G ^ p) ^ Real.log (3 : ℝ) := by
      rw [Real.rpow_def_of_pos hAG_pos]
      ring_nf
    rw [hAG]
    rw [Real.mul_rpow hA_pos.le hGp_pos.le]
    rw [← Real.rpow_mul hG_pos.le]
  calc
    (3 : ℝ) ^ Nat.ceil (max 0 (Real.log M))
        ≤ 3 * Real.exp (Real.log (3 : ℝ) * max 0 (Real.log M)) :=
          hceil_raw
    _ ≤ 3 * Real.exp (Real.log (3 : ℝ) * Real.log (A * G ^ p)) :=
          mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    _ = 3 * A ^ (Real.log (3 : ℝ)) *
          G ^ (p * Real.log (3 : ℝ)) := by rw [hexp_eq]; ring

/-- The small-bottom prefactor `Msmall` is polynomial in the entry-scale
factor `3 ^ N0`. -/
theorem smallBottom_M_le_const_mul_entry_power
    {d N0 : ℕ} {Ksmall : ℝ}
    (hKsmall : 0 ≤ Ksmall) :
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    let G : ℝ := (3 : ℝ) ^ N0
    let pref : ℝ := (N0 : ℝ) * (S.card : ℝ) * w ^ N0
    let M : ℝ := max 1 (max 0 (pref * Ksmall))
    let A : ℝ := max 1 ((S.card : ℝ) * Ksmall)
    M ≤ A * G ^ ((d : ℝ) + 1) := by
  classical
  intro S w G pref M A
  have hG_one : 1 ≤ G := by
    dsimp [G]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hG_nonneg : 0 ≤ G := le_trans zero_le_one hG_one
  have hA_one : 1 ≤ A := by
    dsimp [A]
    exact le_max_left 1 _
  have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA_one
  have hpow_one : 1 ≤ G ^ ((d : ℝ) + 1) := by
    have hexp_nonneg : 0 ≤ (d : ℝ) + 1 := by positivity
    have hbase : G ^ (0 : ℝ) ≤ G ^ ((d : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hG_one hexp_nonneg
    simpa using hbase
  have hone_le : 1 ≤ A * G ^ ((d : ℝ) + 1) := by
    nlinarith
  have hw_eq : w ^ N0 = G ^ (d : ℝ) := by
    dsimp [w, G]
    norm_num [Nat.cast_pow]
    have hleft :
        ((3 : ℝ) ^ d) ^ (N0 : ℝ) =
          (3 : ℝ) ^ ((d : ℝ) * (N0 : ℝ)) := by
      rw [← Real.rpow_natCast (3 : ℝ) d]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hright :
        ((3 : ℝ) ^ N0) ^ (d : ℝ) =
          (3 : ℝ) ^ ((N0 : ℝ) * (d : ℝ)) := by
      rw [← Real.rpow_natCast (3 : ℝ) N0]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ((3 : ℝ) ^ d) ^ N0
          = ((3 : ℝ) ^ d) ^ (N0 : ℝ) := by
              rw [Real.rpow_natCast]
      _
          = (3 : ℝ) ^ ((d : ℝ) * (N0 : ℝ)) := hleft
      _ = (3 : ℝ) ^ ((N0 : ℝ) * (d : ℝ)) := by ring_nf
      _ = ((3 : ℝ) ^ N0) ^ (d : ℝ) := hright.symm
      _ = ((3 : ℝ) ^ N0) ^ d := by
              rw [Real.rpow_natCast]
  have hN0_le_G : (N0 : ℝ) ≤ G := by
    simpa [G] using nat_cast_le_pow_three_nat N0
  have hprefK_le :
      pref * Ksmall ≤ ((S.card : ℝ) * Ksmall) * G ^ ((d : ℝ) + 1) := by
    have hS_nonneg : 0 ≤ (S.card : ℝ) := by positivity
    have hleft_nonneg : 0 ≤ (S.card : ℝ) * Ksmall := by positivity
    have hGd_nonneg : 0 ≤ G ^ (d : ℝ) :=
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hG_one) _).le
    have hG_pos : 0 < G := lt_of_lt_of_le zero_lt_one hG_one
    calc
      pref * Ksmall
          = ((N0 : ℝ) * ((S.card : ℝ) * Ksmall)) * w ^ N0 := by
              dsimp [pref]
              ring
      _ ≤ (G * ((S.card : ℝ) * Ksmall)) * w ^ N0 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hN0_le_G hleft_nonneg)
                (pow_nonneg (by dsimp [w]; positivity) N0)
      _ = ((S.card : ℝ) * Ksmall) * (G * G ^ (d : ℝ)) := by
              rw [hw_eq]
              ring
      _ = ((S.card : ℝ) * Ksmall) * G ^ ((d : ℝ) + 1) := by
              have hmul :
                  G * G ^ (d : ℝ) = G ^ ((d : ℝ) + 1) := by
                calc
                  G * G ^ (d : ℝ)
                      = G ^ (1 : ℝ) * G ^ (d : ℝ) := by
                          rw [Real.rpow_one]
                  _ = G ^ ((1 : ℝ) + (d : ℝ)) := by
                          rw [← Real.rpow_add hG_pos]
                  _ = G ^ ((d : ℝ) + 1) := by ring_nf
              rw [hmul]
  have hprefK_A :
      pref * Ksmall ≤ A * G ^ ((d : ℝ) + 1) := by
    calc
      pref * Ksmall
          ≤ ((S.card : ℝ) * Ksmall) * G ^ ((d : ℝ) + 1) := hprefK_le
      _ ≤ A * G ^ ((d : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right
            (le_max_right 1 ((S.card : ℝ) * Ksmall))
            (Real.rpow_nonneg hG_nonneg _)
  have hmax0 :
      max 0 (pref * Ksmall) ≤ A * G ^ ((d : ℝ) + 1) := by
    exact max_le (by linarith) hprefK_A
  dsimp [M]
  exact max_le hone_le hmax0

/-- If the selected leading denominator is polynomial in `theta`, then the
explicit prefactor-gap threshold attached to it is compressed by the manuscript
`exp(C log^2(2 + theta))` envelope. -/
theorem explicit_threshold_prefactor_le_exp_logSq_of_Blead_le_poly
    {η A p M : ℝ} {R Qcut : ℕ}
    (hη : 0 < η) (hA : 0 < A) (hp : 0 ≤ p) :
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ θ : ℝ, 0 ≤ θ →
      ∀ Blead : ℝ, 1 ≤ Blead →
        Blead ≤ A * (max 1 θ) ^ p →
        let Btail : ℝ := 2 * Blead
        let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
        let ρgap : ℝ := (3 : ℝ) ^ η
        let Qpref : ℕ :=
          max (Nat.ceil (max 0 (Real.log M)))
            (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
              Real.log ρgap)))
        let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
        let Q : ℕ := max Qpref (max Qlead Qcut)
        3 * ((3 : ℝ) ^ Q) * max 1 Btail ≤
          Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  classical
  let Cgap : ℝ :=
    (2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
      (η * Real.log 3)
  let Cq : ℝ :=
    18 * (3 : ℝ) ^ (Nat.ceil (max 0 (Real.log M)) + R + Qcut) *
      Real.exp (Real.log 3 * Cgap)
  let Aenv : ℝ := 3 * Cq * A ^ (4 : ℕ)
  let penv : ℝ := 4 * p
  let Cscale : ℝ := 1 + (4 * max 0 (Real.log Aenv) + 2 * penv)
  have hCq_pos : 0 < Cq := by
    dsimp [Cq]
    positivity
  have hAenv_pos : 0 < Aenv := by
    dsimp [Aenv]
    positivity
  have hpenv_nonneg : 0 ≤ penv := by
    dsimp [penv]
    positivity
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    have hmax_nonneg : 0 ≤ max 0 (Real.log Aenv) := le_max_left 0 _
    nlinarith
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro θ hθ_nonneg Blead hBlead_one hBlead_poly Btail cgap ρgap Qpref Qlead Q
  have hBlead_pos : 0 < Blead := lt_of_lt_of_le zero_lt_one hBlead_one
  have hthreshold :
      (3 : ℝ) ^ Q * max 1 Btail ≤ Cq * Blead ^ (4 : ℕ) := by
    simpa [Btail, cgap, ρgap, Qpref, Qlead, Q, Cgap, Cq] using
      pow_three_explicit_threshold_le_const_mul_Blead_four
        (M := M) (η := η) (Blead := Blead) (R := R) (Qcut := Qcut)
        hη hBlead_one
  have hblead_pow :
      Blead ^ (4 : ℕ) ≤
        (A * (max 1 θ) ^ p) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hBlead_pos.le hBlead_poly 4
  have hpoly :
      3 * ((3 : ℝ) ^ Q) * max 1 Btail ≤
        Aenv * (max 1 θ) ^ penv := by
    calc
      3 * ((3 : ℝ) ^ Q) * max 1 Btail
          = 3 * (((3 : ℝ) ^ Q) * max 1 Btail) := by ring
      _ ≤ 3 * (Cq * Blead ^ (4 : ℕ)) :=
          mul_le_mul_of_nonneg_left hthreshold (by norm_num)
      _ ≤ 3 * (Cq * ((A * (max 1 θ) ^ p) ^ (4 : ℕ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hblead_pow hCq_pos.le) (by norm_num)
      _ = Aenv * (max 1 θ) ^ penv := by
          dsimp [Aenv, penv]
          rw [mul_pow]
          have hx_pos : 0 < max 1 θ :=
            lt_of_lt_of_le zero_lt_one (le_max_left 1 θ)
          rw [show ((max 1 θ) ^ p) ^ (4 : ℕ) =
              ((max 1 θ) ^ p) ^ (4 : ℝ) by
                exact (Real.rpow_natCast ((max 1 θ) ^ p) 4).symm]
          rw [← Real.rpow_mul hx_pos.le]
          ring_nf
  have henv :=
    const_mul_rpow_max_one_le_exp_logSq
      (A := Aenv) (θ := θ) (p := penv)
      hAenv_pos hθ_nonneg hpenv_nonneg
  have henv2 :
      Real.exp ((4 * max 0 (Real.log Aenv) + 2 * penv) *
          (Real.log (2 + θ)) ^ (2 : ℕ)) ≤
        Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    refine Real.exp_le_exp.mpr ?_
    let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
    have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
    have hcoef :
        4 * max 0 (Real.log Aenv) + 2 * penv ≤ Cscale := by
      dsimp [Cscale]
      linarith
    exact mul_le_mul_of_nonneg_right hcoef hL2_nonneg
  exact hpoly.trans (henv.trans henv2)

/-- Compress the explicit small-bottom threshold once the annealed entry
factor has already been compressed. -/
theorem explicit_smallBottom_prefactor_le_exp_logSq
    {d : ℕ} [NeZero d] {σ Csmall t α CentryScale : ℝ} {Rsmall : ℕ}
    (hσ : 0 < σ) (hCsmall : 0 < Csmall) (ht : 0 < t)
    (hαt : α < t) (hCentryScale : 0 < CentryScale) :
    let K : ℝ := quenchedProbeEnvelopeConst d
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    let η : ℝ := finiteQuenchedTailExponent d σ t
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
    let Ksmall : ℝ := weightedGeometricExpKernelConst w (ρsmall ^ σ)
    let ρgap : ℝ := (3 : ℝ) ^ η
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ {θ : ℝ} {N0 : ℕ}, 0 < θ →
        (3 : ℝ) ^ N0 ≤
          Real.exp (CentryScale * (Real.log (2 + θ)) ^ (2 : ℕ)) →
        let scaleSmall : ℝ := K * (Csmall * θ ^ (2 : ℕ))
        let prefSmall : ℝ := (N0 : ℝ) * (S.card : ℝ) * w ^ N0
        let Msmall : ℝ := max 1 (max 0 (prefSmall * Ksmall))
        let BleadSmall : ℝ := smallBottomTailDenominator scaleSmall η σ
        let BtailSmall : ℝ := 2 * BleadSmall
        let cgapSmall : ℝ := BleadSmall ^ (-η) - BtailSmall ^ (-η)
        let QprefSmall : ℕ :=
          max (Nat.ceil (max 0 (Real.log Msmall)))
            (max Rsmall (Nat.ceil ((2 * max 0 (-(Real.log cgapSmall))) /
              Real.log ρgap)))
        let QleadSmall : ℕ := Nat.ceil (Real.log BleadSmall / Real.log 3)
        let Qsmall : ℕ := max QprefSmall QleadSmall
        3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall ≤
          Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  classical
  intro K S η w ρsmall Ksmall ρgap
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos (d := d)
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ ht
  have hρsmall_gt : 1 < ρsmall := by
    have hgap : 0 < t - α := sub_pos.mpr hαt
    dsimp [ρsmall]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (t - α) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hgap
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hKsmall_pos : 0 < Ksmall := by
    dsimp [Ksmall]
    exact weightedGeometricExpKernelConst_pos
      (w := w) (R := ρsmall ^ σ) hw_pos
      (Real.one_lt_rpow hρsmall_gt hσ)
  let AM : ℝ := max 1 ((S.card : ℝ) * Ksmall)
  let pM : ℝ := (d : ℝ) + 1
  let rceil : ℝ := pM * Real.log (3 : ℝ)
  let Acoef : ℝ :=
    18 * (3 : ℝ) ^ Rsmall *
      Real.exp
        (Real.log 3 *
          ((2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
            (η * Real.log 3))) *
      (3 * AM ^ Real.log (3 : ℝ))
  let Ascale : ℝ := K * Csmall
  let rB : ℝ := 4 * (σ / η)
  let AB : ℝ := (max 1 Ascale) ^ rB
  let pB : ℝ := 2 * rB
  let Afinal : ℝ := 3 * Acoef * AB
  let rfinal : ℝ := 1 + rceil
  let pfinal : ℝ := pB
  have hAM_pos : 0 < AM := by
    dsimp [AM]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have hpM_nonneg : 0 ≤ pM := by dsimp [pM]; positivity
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hrceil_nonneg : 0 ≤ rceil := by dsimp [rceil]; positivity
  have hAcoef_pos : 0 < Acoef := by dsimp [Acoef]; positivity
  have hAscale_pos : 0 < Ascale := by dsimp [Ascale]; positivity
  have hrB_nonneg : 0 ≤ rB := by dsimp [rB]; positivity
  have hAB_pos : 0 < AB := by
    dsimp [AB]
    exact Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 Ascale)) rB
  have hpB_nonneg : 0 ≤ pB := by dsimp [pB]; positivity
  have hAfinal_pos : 0 < Afinal := by dsimp [Afinal]; positivity
  have hrfinal_nonneg : 0 ≤ rfinal := by dsimp [rfinal]; positivity
  let Cθfinal : ℝ := 1 + (4 * max 0 (Real.log Afinal) + 2 * pfinal)
  let Cscale : ℝ := rfinal * CentryScale + Cθfinal
  have hCθfinal_pos : 0 < Cθfinal := by
    dsimp [Cθfinal]
    have hmax_nonneg : 0 ≤ max 0 (Real.log Afinal) := le_max_left 0 _
    nlinarith
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    positivity
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro θ N0 hθ_pos hentry scaleSmall prefSmall Msmall BleadSmall
    BtailSmall cgapSmall QprefSmall QleadSmall Qsmall
  let G : ℝ := (3 : ℝ) ^ N0
  let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
  have hθ_nonneg : 0 ≤ θ := hθ_pos.le
  have hG_one : 1 ≤ G := by
    dsimp [G]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hMsmall_one : 1 ≤ Msmall := by
    dsimp [Msmall]
    exact le_max_left 1 _
  have hM_bound :
      Msmall ≤ AM * G ^ pM := by
    simpa [S, w, G, prefSmall, Msmall, AM, pM] using
      smallBottom_M_le_const_mul_entry_power
        (d := d) (N0 := N0) (Ksmall := Ksmall) hKsmall_pos.le
  have hceil_bound :
      (3 : ℝ) ^ Nat.ceil (max 0 (Real.log Msmall)) ≤
        3 * AM ^ Real.log (3 : ℝ) * G ^ rceil := by
    simpa [rceil, pM] using
      pow_three_natCeil_max_zero_log_le_const_mul_rpow_of_le
        (M := Msmall) (A := AM) (G := G) (p := pM)
        hMsmall_one hAM_pos hG_one hM_bound
  have hBlead_one : 1 ≤ BleadSmall := by
    simpa [BleadSmall] using
      one_le_smallBottomTailDenominator
        (scale := scaleSmall) (η := η) (σ := σ) hη_pos hσ.le
  have hthreshold :
      (3 : ℝ) ^ Qsmall * max 1 BtailSmall ≤
        (18 * (3 : ℝ) ^
            (Nat.ceil (max 0 (Real.log Msmall)) + Rsmall + 0) *
          Real.exp
            (Real.log 3 *
              ((2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
                (η * Real.log 3)))) *
          BleadSmall ^ (4 : ℕ) := by
    let Qaux : ℕ := max QprefSmall (max QleadSmall 0)
    have hQsmall_le : Qsmall ≤ Qaux := by
      dsimp [Qaux, Qsmall]
      omega
    have hmono :
        (3 : ℝ) ^ Qsmall * max 1 BtailSmall ≤
          (3 : ℝ) ^ Qaux * max 1 BtailSmall := by
      exact mul_le_mul_of_nonneg_right
        (pow_three_nat_mono hQsmall_le) (by positivity)
    have haux :
        (3 : ℝ) ^ Qaux * max 1 BtailSmall ≤
          (18 * (3 : ℝ) ^
              (Nat.ceil (max 0 (Real.log Msmall)) + Rsmall + 0) *
            Real.exp
              (Real.log 3 *
                ((2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
                  (η * Real.log 3)))) *
            BleadSmall ^ (4 : ℕ) := by
      simpa [BtailSmall, cgapSmall, ρgap, QprefSmall, QleadSmall, Qaux] using
        pow_three_explicit_threshold_le_const_mul_Blead_four
          (M := Msmall) (η := η) (Blead := BleadSmall)
          (R := Rsmall) (Qcut := 0) hη_pos hBlead_one
    exact hmono.trans haux
  have hBlead_pow :
      BleadSmall ^ (4 : ℕ) ≤ AB * (max 1 θ) ^ pB := by
    have hden_eq :
        BleadSmall ^ (4 : ℕ) =
          (max 1 (Ascale * θ ^ (2 : ℕ))) ^ rB := by
      dsimp [BleadSmall, smallBottomTailDenominator, scaleSmall, Ascale, rB]
      rw [show ((max 1 (K * (Csmall * θ ^ (2 : ℕ)))) ^ (σ / η)) ^
            (4 : ℕ) =
          ((max 1 (K * (Csmall * θ ^ (2 : ℕ)))) ^ (σ / η)) ^
            (4 : ℝ) by
            exact (Real.rpow_natCast _ 4).symm]
      rw [← Real.rpow_mul
        (le_trans zero_le_one (le_max_left 1 (K * (Csmall * θ ^ (2 : ℕ)))))]
      congr 1
      field_simp [hη_pos.ne']
      ring
    rw [hden_eq]
    simpa [AB, pB, Ascale, rB] using
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := Ascale) (θ := θ) (r := rB) hθ_nonneg hrB_nonneg
  have hQsmall_bound :
      (3 : ℝ) ^ Qsmall * max 1 BtailSmall ≤
        Acoef * G ^ rceil * (AB * (max 1 θ) ^ pB) := by
    calc
      (3 : ℝ) ^ Qsmall * max 1 BtailSmall
          ≤ (18 * (3 : ℝ) ^
              (Nat.ceil (max 0 (Real.log Msmall)) + Rsmall + 0) *
            Real.exp
              (Real.log 3 *
                ((2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
                  (η * Real.log 3)))) *
            BleadSmall ^ (4 : ℕ) := hthreshold
      _ =
          (18 * (3 : ℝ) ^ Rsmall *
            Real.exp
              (Real.log 3 *
                ((2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
                  (η * Real.log 3)))) *
            ((3 : ℝ) ^ Nat.ceil (max 0 (Real.log Msmall))) *
            BleadSmall ^ (4 : ℕ) := by
              rw [show Nat.ceil (max 0 (Real.log Msmall)) + Rsmall + 0 =
                Nat.ceil (max 0 (Real.log Msmall)) + Rsmall by omega]
              rw [pow_add]
              ring
      _ ≤
          (18 * (3 : ℝ) ^ Rsmall *
            Real.exp
              (Real.log 3 *
                ((2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
                  (η * Real.log 3)))) *
            (3 * AM ^ Real.log (3 : ℝ) * G ^ rceil) *
            (AB * (max 1 θ) ^ pB) := by
              gcongr
      _ = Acoef * G ^ rceil * (AB * (max 1 θ) ^ pB) := by
              dsimp [Acoef]
              ring
  have htotal_poly :
      3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall ≤
        Afinal * G ^ rfinal * (max 1 θ) ^ pfinal := by
    have hpow_split :
        (3 : ℝ) ^ (N0 + Qsmall) = G * (3 : ℝ) ^ Qsmall := by
      dsimp [G]
      rw [pow_add]
    calc
      3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall
          = 3 * G * ((3 : ℝ) ^ Qsmall * max 1 BtailSmall) := by
              rw [hpow_split]
              ring
      _ ≤ 3 * G * (Acoef * G ^ rceil * (AB * (max 1 θ) ^ pB)) := by
              gcongr
      _ = Afinal * G ^ rfinal * (max 1 θ) ^ pfinal := by
              have hG_pos : 0 < G := lt_of_lt_of_le zero_lt_one hG_one
              have hmulG : G * G ^ rceil = G ^ rfinal := by
                dsimp [rfinal]
                calc
                  G * G ^ rceil = G ^ (1 : ℝ) * G ^ rceil := by
                    rw [Real.rpow_one]
                  _ = G ^ ((1 : ℝ) + rceil) := by
                    rw [← Real.rpow_add hG_pos]
              calc
                3 * G * (Acoef * G ^ rceil * (AB * (max 1 θ) ^ pB))
                    = 3 * Acoef * AB * (G * G ^ rceil) *
                        (max 1 θ) ^ pB := by ring
                _ = 3 * Acoef * AB * G ^ rfinal *
                        (max 1 θ) ^ pB := by rw [hmulG]
                _ = Afinal * G ^ rfinal * (max 1 θ) ^ pfinal := by
                    dsimp [Afinal, pfinal]
  have hG_pos : 0 < G := lt_of_lt_of_le zero_lt_one hG_one
  have hentry_r :
      G ^ rfinal ≤ Real.exp ((rfinal * CentryScale) * L2) := by
    have hpow :
        G ^ rfinal ≤
          (Real.exp (CentryScale * L2)) ^ rfinal :=
      Real.rpow_le_rpow hG_pos.le hentry hrfinal_nonneg
    have hexp_eq :
        (Real.exp (CentryScale * L2)) ^ rfinal =
          Real.exp ((rfinal * CentryScale) * L2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _)]
      rw [Real.log_exp]
      ring_nf
    exact hpow.trans_eq hexp_eq
  have hθ_poly :
      Afinal * (max 1 θ) ^ pfinal ≤ Real.exp (Cθfinal * L2) := by
    have hbase :=
      const_mul_rpow_max_one_le_exp_logSq
        (A := Afinal) (θ := θ) (p := pfinal)
        hAfinal_pos hθ_nonneg hpB_nonneg
    have hcoef :
        (4 * max 0 (Real.log Afinal) + 2 * pfinal) * L2 ≤
          Cθfinal * L2 := by
      dsimp [Cθfinal]
      have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
      exact mul_le_mul_of_nonneg_right (by linarith) hL2_nonneg
    exact hbase.trans (Real.exp_le_exp.mpr hcoef)
  have hfinal :
      Afinal * G ^ rfinal * (max 1 θ) ^ pfinal ≤
        Real.exp (Cscale * L2) := by
    calc
      Afinal * G ^ rfinal * (max 1 θ) ^ pfinal
          = G ^ rfinal * (Afinal * (max 1 θ) ^ pfinal) := by ring
      _ ≤ Real.exp ((rfinal * CentryScale) * L2) *
            Real.exp (Cθfinal * L2) :=
          mul_le_mul hentry_r hθ_poly (by positivity) (by positivity)
      _ = Real.exp (Cscale * L2) := by
          rw [← Real.exp_add]
          dsimp [Cscale]
          ring_nf
  simpa [L2] using htotal_poly.trans hfinal

end

end Section57
end Ch05
end Book
end Homogenization
