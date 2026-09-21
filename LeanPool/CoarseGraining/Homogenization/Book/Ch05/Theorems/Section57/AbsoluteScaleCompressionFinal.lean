/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompression
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompressionFinal

/-! # Absolute Scale Compression Final -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Final absolute-scale compression

This file contains the last deterministic compression steps for the absolute
minimal scale in the quenched homogenization theorem.
-/

noncomputable section

/-- The union cutoff in the absolute bad-scale estimate is still polynomial in
`theta`, hence is also compressed by the manuscript `exp(C log^2)` envelope. -/
theorem explicit_union_prefactor_le_exp_logSq
    {d : ℕ} [NeZero d] {σ Cfluct CcrudeShift Csmall a t : ℝ}
    {Runion : ℕ}
    (hσ : 0 < σ) (ha : 0 < a) (ht : 0 < t) :
    let K : ℝ := quenchedProbeEnvelopeConst d
    let b : ℝ := (d : ℝ) / 2
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := finiteQuenchedTailExponent d σ t
    let ρgap : ℝ := (3 : ℝ) ^ η
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ θ : ℝ, 0 < θ →
        let Dhigh : ℝ := 2 * K * Cfluct * θ ^ (2 : ℕ)
        let Dcrude : ℝ := K * CcrudeShift * θ ^ (2 : ℕ)
        let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
        let Ohigh : ℝ := (τ * b * (L + 1)) / η
        let Ocrude : ℝ := (σ * t * (L + 1)) / η
        let BleadShift : ℝ :=
          max (DenShift * (3 : ℝ) ^ Ohigh)
            (DenShift * (3 : ℝ) ^ Ocrude)
        let BtailShift : ℝ := 2 * BleadShift
        let scaleSmall : ℝ := K * (Csmall * θ ^ (2 : ℕ))
        let BleadSmall : ℝ := smallBottomTailDenominator scaleSmall η σ
        let BtailSmall : ℝ := 2 * BleadSmall
        let BleadUnion : ℝ := max BtailShift BtailSmall
        let BtailUnion : ℝ := 2 * BleadUnion
        let cgapUnion : ℝ := BleadUnion ^ (-η) - BtailUnion ^ (-η)
        let Qunion : ℕ :=
          max (Nat.ceil (max 0 (Real.log (2 : ℝ))))
            (max Runion (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) /
              Real.log ρgap)))
        3 * ((3 : ℝ) ^ Qunion) * max 1 BtailUnion ≤
          Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  classical
  intro K b L τ η ρgap
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
  let Acr : ℝ := K * CcrudeShift
  let rτ : ℝ := τ / η
  let rσ : ℝ := σ / η
  let pShift : ℝ := 2 * max rτ rσ
  let CdenShift : ℝ := max ((max 1 Ahi) ^ rτ) ((max 1 Acr) ^ rσ)
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let U : ℝ := (3 : ℝ) ^ Ohigh
  let V : ℝ := (3 : ℝ) ^ Ocrude
  let CbleadShift : ℝ := CdenShift * max U V
  let Ashift : ℝ := 2 * CbleadShift
  let rSmall : ℝ := σ / η
  let pSmall : ℝ := 2 * rSmall
  let Asmall : ℝ := 2 * (max 1 (K * Csmall)) ^ rSmall
  let pUnion : ℝ := max pShift pSmall
  let Aunion : ℝ := max Ashift Asmall
  obtain ⟨Cscale, hCscale_pos, hthreshold⟩ :=
    explicit_threshold_prefactor_le_exp_logSq_of_Blead_le_poly
      (η := η) (A := Aunion) (p := pUnion) (M := (2 : ℝ))
      (R := Runion) (Qcut := 0) hη_pos (by
        dsimp [Aunion, Ashift, CbleadShift, CdenShift, Asmall]
        positivity) (by
        dsimp [pUnion, pShift, pSmall, rτ, rσ, rSmall]
        positivity)
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro θ hθ_pos Dhigh Dcrude DenShift Ohigh' Ocrude' BleadShift
    BtailShift scaleSmall BleadSmall BtailSmall BleadUnion BtailUnion
    cgapUnion Qunion
  have hθ_nonneg : 0 ≤ θ := hθ_pos.le
  have hpShift_nonneg : 0 ≤ pShift := by
    dsimp [pShift, rτ, rσ]
    positivity
  have hpSmall_nonneg : 0 ≤ pSmall := by
    dsimp [pSmall, rSmall]
    positivity
  have hAshift_nonneg : 0 ≤ Ashift := by
    dsimp [Ashift, CbleadShift, CdenShift, U, V]
    positivity
  have hAsmall_nonneg : 0 ≤ Asmall := by
    dsimp [Asmall, rSmall]
    positivity
  have hU_pos : 0 < U := by dsimp [U]; positivity
  have hV_pos : 0 < V := by dsimp [V]; positivity
  have hDenShift_ge_one : 1 ≤ DenShift := by
    simpa [DenShift, Dhigh, Dcrude, η, τ, Ahi, Acr] using
      one_le_mixedBottomTailDenominator
        (Dhigh := Ahi * θ ^ (2 : ℕ)) (Dcrude := Acr * θ ^ (2 : ℕ))
        (η := η) (τ := τ) (σ := σ) hη_pos hτ_pos.le
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
      Real.log_nonneg (le_max_right (2 * K) 1)
    positivity
  have hOhigh_nonneg : 0 ≤ Ohigh' := by
    dsimp [Ohigh', L]
    positivity
  have hU_ge_one : 1 ≤ (3 : ℝ) ^ Ohigh' :=
    one_le_rpow_of_one_le_of_nonneg (by norm_num : (1 : ℝ) ≤ 3)
      hOhigh_nonneg
  have hBleadShift_ge_one : 1 ≤ BleadShift := by
    dsimp [BleadShift]
    have hleft : 1 ≤ DenShift * (3 : ℝ) ^ Ohigh' := by
      have hprod_nonneg : 0 ≤ DenShift * (3 : ℝ) ^ Ohigh' := by positivity
      nlinarith
    exact hleft.trans (le_max_left _ _)
  have hBtailShift_ge_one : 1 ≤ BtailShift := by
    dsimp [BtailShift]
    nlinarith
  have hBleadSmall_ge_one : 1 ≤ BleadSmall := by
    simpa [BleadSmall] using
      one_le_smallBottomTailDenominator
        (scale := scaleSmall) (η := η) (σ := σ) hη_pos hσ.le
  have hBtailSmall_ge_one : 1 ≤ BtailSmall := by
    dsimp [BtailSmall]
    nlinarith
  have hBleadUnion_ge_one : 1 ≤ BleadUnion :=
    hBtailShift_ge_one.trans (le_max_left _ _)
  have hshift_core :
      BleadShift ≤ CbleadShift * (max 1 θ) ^ pShift := by
    simpa [BleadShift, DenShift, Dhigh, Dcrude, Ahi, Acr, Ohigh',
      Ocrude', Ohigh, Ocrude, U, V, CdenShift, CbleadShift, pShift,
      rτ, rσ] using
      selectedBlead_mul_sq_le_const_mul_rpow
        (A := Ahi) (B := Acr) (θ := θ) (η := η) (τ := τ) (σ := σ)
        (U := U) (V := V) hθ_nonneg hη_pos hτ_pos.le hσ.le
        hU_pos.le hV_pos.le
  have hshift_bound :
      BtailShift ≤ Aunion * (max 1 θ) ^ pUnion := by
    have hpow :
        (max 1 θ) ^ pShift ≤ (max 1 θ) ^ pUnion :=
      rpow_max_one_le_rpow_max_one_of_exponent_le (by
        dsimp [pUnion]
        exact le_max_left _ _)
    calc
      BtailShift = 2 * BleadShift := by rfl
      _ ≤ 2 * (CbleadShift * (max 1 θ) ^ pShift) := by
          exact mul_le_mul_of_nonneg_left hshift_core (by norm_num)
      _ = Ashift * (max 1 θ) ^ pShift := by
          dsimp [Ashift]
          ring
      _ ≤ Ashift * (max 1 θ) ^ pUnion :=
          mul_le_mul_of_nonneg_left hpow hAshift_nonneg
      _ ≤ Aunion * (max 1 θ) ^ pUnion :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hsmall_core :
      BleadSmall ≤ (max 1 (K * Csmall)) ^ rSmall *
        (max 1 θ) ^ pSmall := by
    simpa [BleadSmall, scaleSmall, smallBottomTailDenominator, rSmall,
      pSmall, mul_assoc] using
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := K * Csmall) (θ := θ) (r := rSmall)
        hθ_nonneg (by dsimp [rSmall]; positivity)
  have hsmall_bound :
      BtailSmall ≤ Aunion * (max 1 θ) ^ pUnion := by
    have hpow :
        (max 1 θ) ^ pSmall ≤ (max 1 θ) ^ pUnion :=
      rpow_max_one_le_rpow_max_one_of_exponent_le (by
        dsimp [pUnion]
        exact le_max_right _ _)
    calc
      BtailSmall = 2 * BleadSmall := by rfl
      _ ≤ 2 * ((max 1 (K * Csmall)) ^ rSmall *
            (max 1 θ) ^ pSmall) := by
          exact mul_le_mul_of_nonneg_left hsmall_core (by norm_num)
      _ = Asmall * (max 1 θ) ^ pSmall := by
          dsimp [Asmall]
          ring
      _ ≤ Asmall * (max 1 θ) ^ pUnion :=
          mul_le_mul_of_nonneg_left hpow hAsmall_nonneg
      _ ≤ Aunion * (max 1 θ) ^ pUnion :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hBleadUnion_poly :
      BleadUnion ≤ Aunion * (max 1 θ) ^ pUnion := by
    dsimp [BleadUnion]
    exact max_le hshift_bound hsmall_bound
  let QleadUnion : ℕ := Nat.ceil (Real.log BleadUnion / Real.log 3)
  let Qaux : ℕ := max Qunion (max QleadUnion 0)
  have haux :
      3 * ((3 : ℝ) ^ Qaux) * max 1 BtailUnion ≤
        Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    have hraw :=
      hthreshold θ hθ_nonneg BleadUnion hBleadUnion_ge_one
        hBleadUnion_poly
    dsimp only at hraw
    simpa only using hraw
  have hQunion_le_aux : Qunion ≤ Qaux := by
    dsimp [Qaux]
    exact le_max_left _ _
  have hleft :
      3 * ((3 : ℝ) ^ Qunion) * max 1 BtailUnion ≤
        3 * ((3 : ℝ) ^ Qaux) * max 1 BtailUnion := by
    have hpow := pow_three_nat_mono hQunion_le_aux
    gcongr
  exact hleft.trans haux

/-- The absolute prefactor is dominated by the product of the shifted,
small-bottom, and union prefactors. -/
theorem absolute_prefactor_le_branch_product
    {N0 Qshift Qsmall Qunion : ℕ} {Bshift Bsmall Bunion : ℝ}
    (hBshift : 1 ≤ Bshift) (hBsmall : 1 ≤ Bsmall)
    (hBunion : 1 ≤ Bunion) :
    let Q : ℕ := max Qshift (max Qsmall Qunion)
    3 * ((3 : ℝ) ^ (N0 + Q)) * Bunion ≤
      (3 * ((3 : ℝ) ^ Qshift) * Bshift) *
        (3 * ((3 : ℝ) ^ (N0 + Qsmall)) * Bsmall) *
          (3 * ((3 : ℝ) ^ Qunion) * Bunion) := by
  intro Q
  have hBunion_nonneg : 0 ≤ Bunion := le_trans zero_le_one hBunion
  have hBprod :
      Bunion ≤ Bshift * Bsmall * Bunion := by
    have h12 : 1 ≤ Bshift * Bsmall :=
      one_le_mul_of_one_le_of_one_le hBshift hBsmall
    have hmul : Bunion ≤ (Bshift * Bsmall) * Bunion :=
      by simpa [one_mul] using mul_le_mul_of_nonneg_right h12 hBunion_nonneg
    simpa [one_mul, mul_assoc] using hmul
  have hQsum : N0 + Q ≤ Qshift + (N0 + Qsmall) + Qunion := by
    dsimp [Q]
    omega
  have hpow :
      (3 : ℝ) ^ (N0 + Q) ≤
        (3 : ℝ) ^ (Qshift + (N0 + Qsmall) + Qunion) :=
    pow_three_nat_mono hQsum
  have hrest_nonneg :
      0 ≤ (3 : ℝ) ^ (Qshift + (N0 + Qsmall) + Qunion) *
        (Bshift * Bsmall * Bunion) := by
    have hB_nonneg : 0 ≤ Bshift * Bsmall * Bunion := by positivity
    positivity
  calc
    3 * ((3 : ℝ) ^ (N0 + Q)) * Bunion
        ≤ 3 * ((3 : ℝ) ^ (Qshift + (N0 + Qsmall) + Qunion)) * Bunion := by
          gcongr
    _ ≤ 3 * ((3 : ℝ) ^ (Qshift + (N0 + Qsmall) + Qunion)) *
          (Bshift * Bsmall * Bunion) := by
          gcongr
    _ ≤ 27 * ((3 : ℝ) ^ (Qshift + (N0 + Qsmall) + Qunion)) *
          (Bshift * Bsmall * Bunion) := by
          nlinarith
    _ =
      (3 * ((3 : ℝ) ^ Qshift) * Bshift) *
        (3 * ((3 : ℝ) ^ (N0 + Qsmall)) * Bsmall) *
          (3 * ((3 : ℝ) ^ Qunion) * Bunion) := by
          rw [pow_add, pow_add]
          ring

/-- Final deterministic compression of the explicit absolute minimal-scale
normalization. -/
theorem explicit_absoluteMinimalScale_prefactor_le_exp_logSq
    {d : ℕ} [NeZero d]
    {σ Cfluct CcrudeShift Csmall a t α CentryScale : ℝ}
    {Rshift Rsmall Runion : ℕ}
    (hσ : 0 < σ) (hCfluct : 0 < Cfluct)
    (hCcrudeShift : 0 < CcrudeShift) (hCsmall : 0 < Csmall)
    (ha : 0 < a) (ht : 0 < t) (hαt : α < t)
    (hCentryScale : 0 < CentryScale) :
    let K : ℝ := quenchedProbeEnvelopeConst d
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    let b : ℝ := (d : ℝ) / 2
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let ctop : ℝ :=
      min (t - α)
        (min ((d : ℝ) / 2 - α)
          (min ((t - α) * (1 + ((d : ℝ) / 2) / a))
            ((d : ℝ) / 2 - α * (1 + ((d : ℝ) / 2) / a))))
    let τ : ℝ := finiteQuenchedTailTau σ
    let η : ℝ := finiteQuenchedTailExponent d σ t
    let w : ℝ := ((3 ^ d : ℕ) : ℝ)
    let ρtop : ℝ := (3 : ℝ) ^ ctop
    let ρbottom : ℝ := (3 : ℝ) ^ (τ * (t - α) / η)
    let ρcrude : ℝ := (3 : ℝ) ^ (t - α)
    let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
    let Ctop : ℝ :=
      (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ τ)
    let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
    let Kcrude : ℝ := weightedGeometricExpKernelConst w (ρcrude ^ σ)
    let Mshift : ℝ :=
      max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
        max 0 ((S.card : ℝ) * Kcrude))
    let ρgap : ℝ := (3 : ℝ) ^ η
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ {θ : ℝ} {N0 : ℕ}, 0 < θ →
        (3 : ℝ) ^ N0 ≤
          Real.exp (CentryScale * (Real.log (2 + θ)) ^ (2 : ℕ)) →
        let Dhigh : ℝ := 2 * K * Cfluct * θ ^ (2 : ℕ)
        let Dcrude : ℝ := K * CcrudeShift * θ ^ (2 : ℕ)
        let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
        let Ohigh : ℝ := (τ * b * (L + 1)) / η
        let Ocrude : ℝ := (σ * t * (L + 1)) / η
        let BleadShift : ℝ :=
          max (DenShift * (3 : ℝ) ^ Ohigh)
            (DenShift * (3 : ℝ) ^ Ocrude)
        let BtailShift : ℝ := 2 * BleadShift
        let cgapShift : ℝ := BleadShift ^ (-η) - BtailShift ^ (-η)
        let QprefShift : ℕ :=
          max (Nat.ceil (max 0 (Real.log Mshift)))
            (max Rshift (Nat.ceil ((2 * max 0 (-(Real.log cgapShift))) /
              Real.log ρgap)))
        let QleadShift : ℕ := Nat.ceil (Real.log BleadShift / Real.log 3)
        let QcutShift : ℕ := Nat.ceil ((L + 1) / (1 - α / a) + 1)
        let Qshift : ℕ := max QprefShift (max QleadShift QcutShift)
        let scaleSmall : ℝ := K * (Csmall * θ ^ (2 : ℕ))
        let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
        let Ksmall : ℝ := weightedGeometricExpKernelConst w (ρsmall ^ σ)
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
        let BleadUnion : ℝ := max BtailShift BtailSmall
        let BtailUnion : ℝ := 2 * BleadUnion
        let cgapUnion : ℝ := BleadUnion ^ (-η) - BtailUnion ^ (-η)
        let Qunion : ℕ :=
          max (Nat.ceil (max 0 (Real.log (2 : ℝ))))
            (max Runion (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) /
              Real.log ρgap)))
        let Q : ℕ := max Qshift (max Qsmall Qunion)
        let B : ℝ := max 1 BtailUnion
        3 * ((3 : ℝ) ^ (N0 + Q)) * B ≤
          Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  classical
  intro K S b L ctop τ η w ρtop ρbottom ρcrude Cbottom Ctop
    Kbottom Kcrude Mshift ρgap
  obtain ⟨Cshift, hCshift_pos, hshiftBase⟩ :=
    explicit_minimalScale_prefactor_le_exp_logSq
      (d := d) (σ := σ) (Cfluct := Cfluct) (Ccrude := CcrudeShift)
      (a := a) (t := t) (αbad := α) (R := Rshift)
      hσ hCfluct hCcrudeShift ha ht
  obtain ⟨CsmallScale, hCsmallScale_pos, hsmallBase⟩ :=
    explicit_smallBottom_prefactor_le_exp_logSq
      (d := d) (σ := σ) (Csmall := Csmall) (t := t) (α := α)
      (CentryScale := CentryScale) (Rsmall := Rsmall)
      hσ hCsmall ht hαt hCentryScale
  obtain ⟨Cunion, hCunion_pos, hunionBase⟩ :=
    explicit_union_prefactor_le_exp_logSq
      (d := d) (σ := σ) (Cfluct := Cfluct)
      (CcrudeShift := CcrudeShift) (Csmall := Csmall)
      (a := a) (t := t) (Runion := Runion) hσ ha ht
  let Cscale : ℝ := Cshift + CsmallScale + Cunion
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    positivity
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro θ N0 hθ_pos hentry Dhigh Dcrude DenShift Ohigh Ocrude
    BleadShift BtailShift cgapShift QprefShift QleadShift QcutShift
    Qshift scaleSmall ρsmall Ksmall prefSmall Msmall BleadSmall
    BtailSmall cgapSmall QprefSmall QleadSmall Qsmall BleadUnion
    BtailUnion cgapUnion Qunion Q B
  let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
  have hshift :
      3 * ((3 : ℝ) ^ Qshift) * max 1 BtailShift ≤
        Real.exp (Cshift * L2) := by
    have hraw := hshiftBase θ hθ_pos
    dsimp only at hraw
    simpa only [L2] using hraw
  have hsmall :
      3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall ≤
        Real.exp (CsmallScale * L2) := by
    have hraw := hsmallBase (θ := θ) (N0 := N0) hθ_pos hentry
    dsimp only at hraw
    simpa only [L2] using hraw
  have hunion :
      3 * ((3 : ℝ) ^ Qunion) * max 1 BtailUnion ≤
        Real.exp (Cunion * L2) := by
    have hraw := hunionBase θ hθ_pos
    dsimp only at hraw
    simpa only [L2] using hraw
  have hBshift_one : 1 ≤ max 1 BtailShift := le_max_left 1 _
  have hBsmall_one : 1 ≤ max 1 BtailSmall := le_max_left 1 _
  have hBunion_one : 1 ≤ max 1 BtailUnion := le_max_left 1 _
  have hpref :
      3 * ((3 : ℝ) ^ (N0 + Q)) * B ≤
        (3 * ((3 : ℝ) ^ Qshift) * max 1 BtailShift) *
          (3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall) *
            (3 * ((3 : ℝ) ^ Qunion) * max 1 BtailUnion) := by
    simpa [Q, B] using
      absolute_prefactor_le_branch_product
        (N0 := N0) (Qshift := Qshift) (Qsmall := Qsmall)
        (Qunion := Qunion) (Bshift := max 1 BtailShift)
        (Bsmall := max 1 BtailSmall) (Bunion := max 1 BtailUnion)
        hBshift_one hBsmall_one hBunion_one
  have hprod :
      (3 * ((3 : ℝ) ^ Qshift) * max 1 BtailShift) *
          (3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall) *
            (3 * ((3 : ℝ) ^ Qunion) * max 1 BtailUnion) ≤
        Real.exp (Cshift * L2) *
          Real.exp (CsmallScale * L2) *
            Real.exp (Cunion * L2) := by
    have hleft_nonneg :
        0 ≤ 3 * ((3 : ℝ) ^ Qshift) * max 1 BtailShift := by positivity
    have hmid_nonneg :
        0 ≤ 3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall := by positivity
    have hright_nonneg :
        0 ≤ 3 * ((3 : ℝ) ^ Qunion) * max 1 BtailUnion := by positivity
    have h12 :
        (3 * ((3 : ℝ) ^ Qshift) * max 1 BtailShift) *
            (3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall) ≤
          Real.exp (Cshift * L2) * Real.exp (CsmallScale * L2) :=
      mul_le_mul hshift hsmall hmid_nonneg (Real.exp_pos _).le
    exact mul_le_mul h12 hunion hright_nonneg
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  calc
    3 * ((3 : ℝ) ^ (N0 + Q)) * B
        ≤ (3 * ((3 : ℝ) ^ Qshift) * max 1 BtailShift) *
          (3 * ((3 : ℝ) ^ (N0 + Qsmall)) * max 1 BtailSmall) *
            (3 * ((3 : ℝ) ^ Qunion) * max 1 BtailUnion) := hpref
    _ ≤ Real.exp (Cshift * L2) *
          Real.exp (CsmallScale * L2) *
            Real.exp (Cunion * L2) := hprod
    _ = Real.exp (Cscale * L2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [Cscale]
        rw [← add_mul, ← add_mul]

end

end Section57
end Ch05
end Book
end Homogenization
