/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompressionThreshold

/-! # Scale Compression Final -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Final deterministic scale compression

This file compresses the explicit quantitative minimal-scale normalization
`3 * 3^Q * B` to the manuscript envelope `exp(C log^2(2 + thetaHat))`.
-/

noncomputable section

theorem one_le_rpow_of_one_le_of_nonneg {x r : ℝ}
    (hx : 1 ≤ x) (hr : 0 ≤ r) :
    1 ≤ x ^ r := by
  have hbase : x ^ (0 : ℝ) ≤ x ^ r :=
    Real.rpow_le_rpow_of_exponent_le hx hr
  simpa using hbase

theorem one_le_mixedBottomTailDenominator
    {Dhigh Dcrude η τ σ : ℝ}
    (hη : 0 < η) (hτ : 0 ≤ τ) :
    1 ≤ mixedBottomTailDenominator Dhigh Dcrude η τ σ := by
  have hbase : 1 ≤ max 1 Dhigh := le_max_left 1 Dhigh
  have hr : 0 ≤ τ / η := by positivity
  have hterm : 1 ≤ (max 1 Dhigh) ^ (τ / η) :=
    one_le_rpow_of_one_le_of_nonneg hbase hr
  exact hterm.trans (le_max_left _ _)

theorem explicit_minimalScale_prefactor_le_exp_logSq
    {d : ℕ} [NeZero d] {σ Cfluct Ccrude a t αbad : ℝ} {R : ℕ}
    (hσ : 0 < σ) (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (ha : 0 < a) (ht : 0 < t) :
    let K : ℝ := quenchedProbeEnvelopeConst d
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    let b : ℝ := (d : ℝ) / 2
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let ctop : ℝ :=
      min (t - αbad)
        (min (b - αbad)
          (min ((t - αbad) * (1 + b / a))
            (b - αbad * (1 + b / a))))
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := finiteQuenchedTailExponent d σ t
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    let ρtop : ℝ := (3 : ℝ) ^ ctop
    let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - αbad) / η)
    let ρcrude : ℝ := (3 : ℝ) ^ (t - αbad)
    let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
    let Ctop : ℝ :=
      (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
    let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
    let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
    let M : ℝ :=
      max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
        max 0 ((S.card : ℝ) * Kcrude))
    let Qcut : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ θ : ℝ, 0 < θ →
        let Dhigh : ℝ := 2 * K * Cfluct * θ ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * θ ^ (2 : ℕ)
        let Den : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
        let Ohigh : ℝ := (τ * b * (L + 1)) / η
        let Ocrude : ℝ := (σ * t * (L + 1)) / η
        let Blead : ℝ :=
          max (Den * (3 : ℝ) ^ Ohigh) (Den * (3 : ℝ) ^ Ocrude)
        let Btail : ℝ := 2 * Blead
        let B : ℝ := max 1 Btail
        let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
        let ρgap : ℝ := (3 : ℝ) ^ η
        let Qpref : ℕ :=
          max (Nat.ceil (max 0 (Real.log M)))
            (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
              Real.log ρgap)))
        let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
        let Q : ℕ := max Qpref (max Qlead Qcut)
        3 * ((3 : ℝ) ^ Q) * B ≤
          Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  classical
  intro K S b L ctop τ η w ρtop ρbottom ρcrude Cbottom Ctop Kbottom Kcrude M Qcut
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos (d := d)
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hτ_pos : 0 < τ := by
    simpa [τ] using finiteQuenchedTailTau_pos hσ
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ ht
  let Ahi : ℝ := 2 * K * Cfluct
  let Acr : ℝ := K * Ccrude
  let rτ : ℝ := τ / η
  let rσ : ℝ := σ / η
  let Cden : ℝ := max ((max 1 Ahi) ^ rτ) ((max 1 Acr) ^ rσ)
  let pDen : ℝ := 2 * max rτ rσ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let U : ℝ := (3 : ℝ) ^ Ohigh
  let V : ℝ := (3 : ℝ) ^ Ocrude
  let Cblead : ℝ := Cden * max U V
  let Cgap : ℝ :=
    (2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
      (η * Real.log 3)
  let Cq : ℝ :=
    18 * (3 : ℝ) ^ (Nat.ceil (max 0 (Real.log M)) + R + Qcut) *
      Real.exp (Real.log 3 * Cgap)
  let Aenv : ℝ := 3 * Cq * Cblead ^ (4 : ℕ)
  let penv : ℝ := 4 * pDen
  let Cscale : ℝ := 1 + (4 * max 0 (Real.log Aenv) + 2 * penv)
  have hAhi_pos : 0 < Ahi := by dsimp [Ahi]; positivity
  have hAcr_pos : 0 < Acr := by dsimp [Acr]; positivity
  have hrτ_nonneg : 0 ≤ rτ := by dsimp [rτ]; positivity
  have hrσ_nonneg : 0 ≤ rσ := by dsimp [rσ]; positivity
  have hpDen_nonneg : 0 ≤ pDen := by
    dsimp [pDen]
    nlinarith [le_max_left rτ rσ, hrτ_nonneg]
  have hU_pos : 0 < U := by dsimp [U]; positivity
  have hV_pos : 0 < V := by dsimp [V]; positivity
  have hCden_pos : 0 < Cden := by
    dsimp [Cden]
    exact (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 Ahi)) _).trans_le
        (le_max_left _ _)
  have hCblead_pos : 0 < Cblead := by
    dsimp [Cblead]
    exact mul_pos hCden_pos (by
      by_cases hUV : U ≤ V
      · simpa [max_eq_right hUV] using hV_pos
      · simpa [max_eq_left (le_of_not_ge hUV)] using hU_pos)
  have hCgap_exp_pos : 0 < Real.exp (Real.log 3 * Cgap) := Real.exp_pos _
  have hCq_pos : 0 < Cq := by
    dsimp [Cq]
    positivity
  have hAenv_pos : 0 < Aenv := by dsimp [Aenv]; positivity
  have hpenv_nonneg : 0 ≤ penv := by dsimp [penv]; positivity
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    have hmax_nonneg : 0 ≤ max 0 (Real.log Aenv) := le_max_left 0 _
    nlinarith
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro θ hθ_pos Dhigh Dcrude Den Ohigh' Ocrude' Blead Btail B cgap ρgap
    Qpref Qlead Q
  have hθ_nonneg : 0 ≤ θ := hθ_pos.le
  have hDen_ge_one : 1 ≤ Den := by
    simpa [Den, Dhigh, Dcrude, η, τ] using
      one_le_mixedBottomTailDenominator
        (Dhigh := Ahi * θ ^ (2 : ℕ)) (Dcrude := Acr * θ ^ (2 : ℕ))
        (η := η) (τ := τ) (σ := σ) hη_pos hτ_pos.le
  have hOhigh_eq : Ohigh' = Ohigh := by rfl
  have hOcrude_eq : Ocrude' = Ocrude := by rfl
  have hU_ge_one : 1 ≤ (3 : ℝ) ^ Ohigh' := by
    rw [hOhigh_eq]
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
        Real.log_nonneg (le_max_right (2 * K) 1)
      positivity
    have hO_nonneg : 0 ≤ Ohigh := by
      dsimp [Ohigh]
      positivity
    exact one_le_rpow_of_one_le_of_nonneg (by norm_num : (1 : ℝ) ≤ 3) hO_nonneg
  have hBlead_ge_one : 1 ≤ Blead := by
    dsimp [Blead]
    have hleft : 1 ≤ Den * (3 : ℝ) ^ Ohigh' := by
      have hprod_nonneg : 0 ≤ Den * (3 : ℝ) ^ Ohigh' := by positivity
      nlinarith
    exact hleft.trans (le_max_left _ _)
  have hBlead_pos : 0 < Blead := lt_of_lt_of_le zero_lt_one hBlead_ge_one
  have hblead_bound :
      Blead ≤ Cblead * (max 1 θ) ^ pDen := by
    simpa [Blead, Den, Dhigh, Dcrude, Ahi, Acr, Ohigh', Ocrude',
      Ohigh, Ocrude, U, V, Cden, Cblead, pDen, rτ, rσ] using
      selectedBlead_mul_sq_le_const_mul_rpow
        (A := Ahi) (B := Acr) (θ := θ) (η := η) (τ := τ) (σ := σ)
        (U := U) (V := V) hθ_nonneg hη_pos hτ_pos.le hσ.le
        hU_pos.le hV_pos.le
  have hthreshold :
      (3 : ℝ) ^ Q * B ≤ Cq * Blead ^ (4 : ℕ) := by
    simpa [Btail, B, cgap, ρgap, Qpref, Qlead, Q, Cgap, Cq] using
      pow_three_explicit_threshold_le_const_mul_Blead_four
        (M := M) (η := η) (Blead := Blead) (R := R) (Qcut := Qcut)
        hη_pos hBlead_ge_one
  have hblead_pow :
      Blead ^ (4 : ℕ) ≤
        (Cblead * (max 1 θ) ^ pDen) ^ (4 : ℕ) := by
    exact pow_le_pow_left₀ hBlead_pos.le hblead_bound 4
  have hpoly :
      3 * ((3 : ℝ) ^ Q) * B ≤
        Aenv * (max 1 θ) ^ penv := by
    calc
      3 * ((3 : ℝ) ^ Q) * B
          = 3 * (((3 : ℝ) ^ Q) * B) := by ring
      _ ≤ 3 * (Cq * Blead ^ (4 : ℕ)) :=
          mul_le_mul_of_nonneg_left hthreshold (by norm_num)
      _ ≤ 3 * (Cq * ((Cblead * (max 1 θ) ^ pDen) ^ (4 : ℕ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hblead_pow hCq_pos.le) (by norm_num)
      _ = Aenv * (max 1 θ) ^ penv := by
          dsimp [Aenv, penv]
          rw [mul_pow]
          have hx_nonneg : 0 ≤ max 1 θ := le_trans zero_le_one (le_max_left 1 θ)
          rw [show ((max 1 θ) ^ pDen) ^ (4 : ℕ) =
              ((max 1 θ) ^ pDen) ^ (4 : ℝ) by
                exact (Real.rpow_natCast ((max 1 θ) ^ pDen) 4).symm]
          rw [← Real.rpow_mul hx_nonneg]
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
    let A0 : ℝ := 4 * max 0 (Real.log Aenv) + 2 * penv
    let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
    have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
    have hA0_le : A0 ≤ Cscale := by
      dsimp [A0, Cscale]
      linarith
    exact mul_le_mul_of_nonneg_right hA0_le hL2_nonneg
  exact hpoly.trans (henv.trans henv2)

end

end Section57
end Ch05
end Book
end Homogenization
