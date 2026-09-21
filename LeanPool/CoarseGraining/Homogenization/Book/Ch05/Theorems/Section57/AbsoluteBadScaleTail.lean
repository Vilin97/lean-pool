/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.SmallBottomTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailFinalQuantitative
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailCollapse

/-! # Absolute Bad Scale Tail -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory

/-!
# Absolute bad-scale tail

This file assembles the shifted tail above the annealed entry scale with the
small-bottom tail below it.  The result is an absolute bad-tail estimate for
the unshifted finite-probe envelope.
-/

noncomputable section

theorem exp_neg_rpow_three_div_le_exp_neg_rpow_three_div_of_den_le
    {B₁ B₂ η : ℝ} {q : ℕ}
    (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB : B₁ ≤ B₂)
    (hη : 0 < η) :
    Real.exp (-(((3 : ℝ) ^ (q : ℝ) / B₁) ^ η)) ≤
      Real.exp (-(((3 : ℝ) ^ (q : ℝ) / B₂) ^ η)) := by
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have htail_le :
      (((3 : ℝ) ^ (q : ℝ) / B₂) ^ η) ≤
        (((3 : ℝ) ^ (q : ℝ) / B₁) ^ η) :=
    rpow_div_le_rpow_div_of_den_le hpow_nonneg hB₁ hB₂ hB hη
  exact Real.exp_le_exp.mpr (by linarith)

/-- Quantitative absolute bad-tail bound.  The entry scale is still explicit;
the following layer compresses the displayed scale to the manuscript
`exp(C log^2(2 + thetaHat))` envelope. -/
theorem exists_quantitative_threshold_absoluteBadTail_quenchedProbeEnvelope_le_interpolated_tail
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct CcrudeShift Csmall Centry a : ℝ,
      0 < Cfluct ∧ 0 < CcrudeShift ∧ 0 < Csmall ∧
      0 < Centry ∧ 0 < a ∧
      ∀ {t α : ℝ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let ctop : ℝ :=
          min (t - α)
            (min (b - α)
              (min ((t - α) * (1 + b / a))
                (b - α * (1 + b / a))))
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
        0 < t →
        t ≤ b →
        0 ≤ α →
        α < t →
        α < b →
        α * (1 + b / a) < b →
        α < a →
        ∃ Rshift Rsmall Runion : ℕ,
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let H : ℕ → ℕ → RegCoeffField d → ℝ :=
              quenchedProbeEnvelope hP hStruct
            let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
            let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
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
            let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
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
            ∀ q : ℕ, Q ≤ q →
              P.real (badTailEvent (badScaleEvent H t α) (N0 + q)) ≤
                Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η)) := by
  obtain ⟨Cfluct, CcrudeShift, Centry, a,
      hCfluct, hCcrudeShift, hCentry, ha, hshiftBase⟩ :=
    exists_quantitative_threshold_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos params
  obtain ⟨Csmall, hCsmall, hsmallBase⟩ :=
    exists_quantitative_threshold_smallBottomBadTail_quenchedProbeEnvelope_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, CcrudeShift, Csmall, Centry, a,
    hCfluct, hCcrudeShift, hCsmall, hCentry, ha, ?_⟩
  intro t α
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa
  classical
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let ctop : ℝ :=
    min (t - α)
      (min (b - α)
        (min ((t - α) * (1 + b / a))
          (b - α * (1 + b / a))))
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
  let W : ℝ := max 1 w
  let Mshift : ℝ :=
    max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
      max 0 ((S.card : ℝ) * Kcrude))
  let ρgap : ℝ := (3 : ℝ) ^ η
  obtain ⟨Rshift, _hRshift, hshiftLaw⟩ :=
    hshiftBase (t := t) (αbad := α)
      ht htb hα_nonneg hαt hαb hαharm hαa
  obtain ⟨Rsmall, _hRsmall, hsmallLaw⟩ :=
    hsmallBase (t := t) (α := α) ht hα_nonneg hαt
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hρgap_gt : 1 < ρgap := by
    dsimp [ρgap]
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hη_pos
  obtain ⟨Runion, hRunion⟩ :=
    linear_le_exp_linear_eventually
      (C := (2 : ℝ)) (γ := Real.log ρgap / 2)
      (by norm_num) (by
        have hlogρ_pos : 0 < Real.log ρgap := Real.log_pos hρgap_gt
        positivity)
  refine ⟨Rshift, Rsmall, Runion, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let H : ℕ → ℕ → RegCoeffField d → ℝ :=
    quenchedProbeEnvelope hP hStruct
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω => H (N0 + M) (N0 + N) aω
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
  let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let BleadShift : ℝ :=
    max (DenShift * (3 : ℝ) ^ Ohigh) (DenShift * (3 : ℝ) ^ Ocrude)
  let BtailShift : ℝ := 2 * BleadShift
  let cgapShift : ℝ := BleadShift ^ (-η) - BtailShift ^ (-η)
  let QprefShift : ℕ :=
    max (Nat.ceil (max 0 (Real.log Mshift)))
      (max Rshift (Nat.ceil ((2 * max 0 (-(Real.log cgapShift))) /
        Real.log ρgap)))
  let QleadShift : ℕ := Nat.ceil (Real.log BleadShift / Real.log 3)
  let QcutShift : ℕ := Nat.ceil ((L + 1) / (1 - α / a) + 1)
  let Qshift : ℕ := max QprefShift (max QleadShift QcutShift)
  let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
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
  intro q hQq
  have hq_shift : Qshift ≤ q := (le_max_left Qshift (max Qsmall Qunion)).trans hQq
  have hq_small : Qsmall ≤ q :=
    (le_max_left Qsmall Qunion).trans
      ((le_max_right Qshift (max Qsmall Qunion)).trans hQq)
  have hq_union : Qunion ≤ q :=
    (le_max_right Qsmall Qunion).trans
      ((le_max_right Qshift (max Qsmall Qunion)).trans hQq)
  have hshift_q :
      P.real (badScaleEvent Hshift t α q) ≤
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailShift) ^ η)) := by
    simpa [K, S, b, L, ctop, τ, η, w, ρtop, ρbottom, ρcrude,
      Cbottom, Ctop, Kbottom, Kcrude, W, Mshift, ρgap, N0, H, Hshift,
      Dhigh, Dcrude, DenShift, Ohigh, Ocrude, BleadShift, BtailShift,
      cgapShift, QprefShift, QleadShift, QcutShift, Qshift] using
      hshiftLaw hP hStruct hΓ hσ_eq hparams (q := q) hq_shift
  have hshift_tail :
      P.real (badTailEvent (badScaleEvent Hshift t α) q) ≤
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailShift) ^ η)) := by
    have hmono :
        P.real (badTailEvent (badScaleEvent Hshift t α) q) ≤
          P.real (badScaleEvent Hshift t α q) :=
      measureReal_mono (μ := P)
        (badTailEvent_badScaleEvent_subset
          (H := Hshift) (t := t) (α := α) hα_nonneg)
    exact hmono.trans hshift_q
  have hsmall_tail :
      P.real
          (badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q)) ≤
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailSmall) ^ η)) := by
    simpa [K, S, η, w, W, ρgap, H, scaleSmall, ρsmall, Ksmall,
      prefSmall, Msmall, BleadSmall, BtailSmall, cgapSmall, QprefSmall,
      QleadSmall, Qsmall] using
      hsmallLaw hP hStruct hΓ hσ_eq hparams (Nentry := N0) q hq_small
  have hsplit :
      badTailEvent (badScaleEvent H t α) (N0 + q) ⊆
        badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q) ∪
          badTailEvent (badScaleEvent Hshift t α) q := by
    have hraw :=
      badTailEvent_subset_smallBottom_union_shifted
        (H := H) (Nentry := N0) (N := N0 + q) (t := t) (α := α)
        (Nat.le_add_right N0 q)
    simpa [Hshift, Nat.add_sub_cancel_left] using hraw
  have hBtailShift_pos : 0 < BtailShift := by
    have hDenShift_pos : 0 < DenShift := by
      simpa [DenShift] using
        mixedBottomTailDenominator_pos
          (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
    have hBleadShift_pos : 0 < BleadShift := by
      have hleft : 0 < DenShift * (3 : ℝ) ^ Ohigh :=
        mul_pos hDenShift_pos
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ohigh)
      exact hleft.trans_le (le_max_left _ _)
    dsimp [BtailShift]
    positivity
  have hBtailSmall_pos : 0 < BtailSmall := by
    have hscaleSmall_pos : 0 < scaleSmall := by
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      dsimp [scaleSmall]
      exact mul_pos hK_pos (mul_pos hCsmall (pow_pos hΓ.thetaHat_pos 2))
    have hBleadSmall_pos : 0 < BleadSmall := by
      simpa [BleadSmall] using
        smallBottomTailDenominator_pos
          (scale := scaleSmall) (η := η) (σ := σ)
    dsimp [BtailSmall]
    positivity
  have hBleadUnion_pos : 0 < BleadUnion := by
    exact hBtailShift_pos.trans_le (le_max_left _ _)
  have hBtailUnion_pos : 0 < BtailUnion := by
    dsimp [BtailUnion]
    positivity
  have hBleadUnion_lt : BleadUnion < BtailUnion := by
    dsimp [BtailUnion]
    nlinarith
  let Alead : ℝ := ((3 : ℝ) ^ (q : ℝ) / BleadUnion) ^ η
  let Atail : ℝ := ((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η
  have hshift_to_union :
      Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailShift) ^ η)) ≤
        Real.exp (-Alead) := by
    simpa [Alead, BleadUnion] using
      exp_neg_rpow_three_div_le_exp_neg_rpow_three_div_of_den_le
        (B₁ := BtailShift) (B₂ := BleadUnion) (η := η) (q := q)
        hBtailShift_pos hBleadUnion_pos (le_max_left _ _) hη_pos
  have hsmall_to_union :
      Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailSmall) ^ η)) ≤
        Real.exp (-Alead) := by
    simpa [Alead, BleadUnion] using
      exp_neg_rpow_three_div_le_exp_neg_rpow_three_div_of_den_le
        (B₁ := BtailSmall) (B₂ := BleadUnion) (η := η) (q := q)
        hBtailSmall_pos hBleadUnion_pos (le_max_right _ _) hη_pos
  have hcUnion_pos : 0 < cgapUnion := by
    simpa [cgapUnion, BtailUnion] using
      inv_rpow_sub_pos_of_lt
        hBleadUnion_pos hBtailUnion_pos hη_pos hBleadUnion_lt
  have hqU_M :
      Nat.ceil (max 0 (Real.log (2 : ℝ))) ≤ q :=
    (le_max_left _ _).trans hq_union
  have hqU_R : Runion ≤ q :=
    (le_max_left Runion
        (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_union)
  have hqU_c :
      Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) / Real.log ρgap) ≤ q :=
    (le_max_right Runion
        (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_union)
  have hpref_union_gap :
      (2 : ℝ) ≤ Real.exp (Alead - Atail) := by
    have hpref_linear :
        (2 : ℝ) * (((q : ℝ) + 1) * (1 : ℝ) ^ q) ≤
          Real.exp (cgapUnion * ρgap ^ q) :=
      linear_prefactor_le_exp_const_mul_pow_of_large
        (M := (2 : ℝ)) (W := (1 : ℝ)) (C₀ := (2 : ℝ))
        (c := cgapUnion) (ρ := ρgap) (R := Runion) (q := q)
        (by norm_num) (by norm_num) hcUnion_pos hρgap_gt
        (by simp) hRunion hqU_M hqU_R hqU_c
    have hgap :
        cgapUnion * ρgap ^ q ≤ Alead - Atail := by
      simpa [Alead, Atail, cgapUnion, ρgap] using
        geometric_gap_le_rpow_three_nat_div_gap
          (Blead := BleadUnion) (Btail := BtailUnion) (η := η)
          (c := cgapUnion) (ρ := ρgap) (q := q)
          hBleadUnion_pos hBtailUnion_pos
          (le_rfl : cgapUnion ≤ BleadUnion ^ (-η) - BtailUnion ^ (-η))
          (le_rfl : ρgap ≤ (3 : ℝ) ^ η) hcUnion_pos.le
          (le_of_lt (lt_trans zero_lt_one hρgap_gt))
    have hpref_gap := hpref_linear.trans (Real.exp_le_exp.mpr hgap)
    have htwo_pref :
        (2 : ℝ) ≤ (2 : ℝ) * (((q : ℝ) + 1) * (1 : ℝ) ^ q) := by
      have hfactor : 1 ≤ ((q : ℝ) + 1) * (1 : ℝ) ^ q := by
        simp
      nlinarith
    exact htwo_pref.trans hpref_gap
  have hunion_measure :
      P.real (badTailEvent (badScaleEvent H t α) (N0 + q)) ≤
        Real.exp (-Alead) + Real.exp (-Alead) := by
    calc
      P.real (badTailEvent (badScaleEvent H t α) (N0 + q))
          ≤ P.real
              (badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q) ∪
                badTailEvent (badScaleEvent Hshift t α) q) :=
            measureReal_mono (μ := P) hsplit
      _ ≤ P.real
              (badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q)) +
            P.real (badTailEvent (badScaleEvent Hshift t α) q) :=
            measureReal_union_le _ _
      _ ≤ Real.exp (-Alead) + Real.exp (-Alead) := by
            exact add_le_add
              (hsmall_tail.trans hsmall_to_union)
              (hshift_tail.trans hshift_to_union)
  calc
    P.real (badTailEvent (badScaleEvent H t α) (N0 + q))
        ≤ Real.exp (-Alead) + Real.exp (-Alead) := hunion_measure
    _ = (2 : ℝ) * Real.exp (-Alead) := by ring
    _ ≤ Real.exp (Alead - Atail) * Real.exp (-Alead) :=
        mul_le_mul_of_nonneg_right hpref_union_gap (Real.exp_pos _).le
    _ = Real.exp (-Atail) := by
        rw [← Real.exp_add]
        ring_nf

/-- Uniform-in-`σ` version of
`exists_quantitative_threshold_absoluteBadTail_quenchedProbeEnvelope_le_interpolated_tail`. -/
theorem exists_quantitative_threshold_absoluteBadTail_quenchedProbeEnvelope_le_interpolated_tail_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct CcrudeShift Csmall : ℝ,
          0 < Cfluct ∧ 0 < CcrudeShift ∧ 0 < Csmall ∧
          ∀ {t α : ℝ},
            let K : ℝ := quenchedProbeEnvelopeConst d
            let S : Finset (NormalizedProbeIndex d) := Finset.univ
            let b : ℝ := (d : ℝ) / 2
            let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
            let ctop : ℝ :=
              min (t - α)
                (min (b - α)
                  (min ((t - α) * (1 + b / a))
                    (b - α * (1 + b / a))))
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
            0 < t →
            t ≤ b →
            0 ≤ α →
            α < t →
            α < b →
            α * (1 + b / a) < b →
            α < a →
            ∃ Rshift Rsmall Runion : ℕ,
              ∀ {P : Ch04.RestrictionCoeffLaw d}
                (hP : Ch04.RestrictionLawCarrier P)
                (hStruct : Ch04.RestrictionStructuralLaw P)
                (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
                hΓ.sigma = σ → hΓ.params = params →
                let N0 : ℕ :=
                  annealedAlgebraicEntryScale P
                    hΓ.toQuantitativeCoarseGrainedEllipticity Centry
                let H : ℕ → ℕ → RegCoeffField d → ℝ :=
                  quenchedProbeEnvelope hP hStruct
                let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
                let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
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
                let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
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
                ∀ q : ℕ, Q ≤ q →
                  P.real (badTailEvent (badScaleEvent H t α) (N0 + q)) ≤
                    Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η)) := by
  obtain ⟨Centry, a, hCentry, ha, hshiftUniform⟩ :=
    exists_quantitative_threshold_shiftedBadScaleEvent_quenchedProbeEnvelope_le_interpolated_tail_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, CcrudeShift, hCfluct, hCcrudeShift, hshiftBase⟩ :=
    hshiftUniform hσ_pos
  obtain ⟨Csmall, hCsmall, hsmallBase⟩ :=
    exists_quantitative_threshold_smallBottomBadTail_quenchedProbeEnvelope_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, CcrudeShift, Csmall,
    hCfluct, hCcrudeShift, hCsmall, ?_⟩
  intro t α
  dsimp only
  intro ht htb hα_nonneg hαt hαb hαharm hαa
  classical
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let ctop : ℝ :=
    min (t - α)
      (min (b - α)
        (min ((t - α) * (1 + b / a))
          (b - α * (1 + b / a))))
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
  let W : ℝ := max 1 w
  let Mshift : ℝ :=
    max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) +
      max 0 ((S.card : ℝ) * Kcrude))
  let ρgap : ℝ := (3 : ℝ) ^ η
  obtain ⟨Rshift, _hRshift, hshiftLaw⟩ :=
    hshiftBase (t := t) (αbad := α)
      ht htb hα_nonneg hαt hαb hαharm hαa
  obtain ⟨Rsmall, _hRsmall, hsmallLaw⟩ :=
    hsmallBase (t := t) (α := α) ht hα_nonneg hαt
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hρgap_gt : 1 < ρgap := by
    dsimp [ρgap]
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hη_pos
  obtain ⟨Runion, hRunion⟩ :=
    linear_le_exp_linear_eventually
      (C := (2 : ℝ)) (γ := Real.log ρgap / 2)
      (by norm_num) (by
        have hlogρ_pos : 0 < Real.log ρgap := Real.log_pos hρgap_gt
        positivity)
  refine ⟨Rshift, Rsmall, Runion, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let H : ℕ → ℕ → RegCoeffField d → ℝ :=
    quenchedProbeEnvelope hP hStruct
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω => H (N0 + M) (N0 + N) aω
  let Dhigh : ℝ := 2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * CcrudeShift * hΓ.thetaHat ^ (2 : ℕ)
  let DenShift : ℝ := mixedBottomTailDenominator Dhigh Dcrude η τ σ
  let Ohigh : ℝ := (τ * b * (L + 1)) / η
  let Ocrude : ℝ := (σ * t * (L + 1)) / η
  let BleadShift : ℝ :=
    max (DenShift * (3 : ℝ) ^ Ohigh) (DenShift * (3 : ℝ) ^ Ocrude)
  let BtailShift : ℝ := 2 * BleadShift
  let cgapShift : ℝ := BleadShift ^ (-η) - BtailShift ^ (-η)
  let QprefShift : ℕ :=
    max (Nat.ceil (max 0 (Real.log Mshift)))
      (max Rshift (Nat.ceil ((2 * max 0 (-(Real.log cgapShift))) /
        Real.log ρgap)))
  let QleadShift : ℕ := Nat.ceil (Real.log BleadShift / Real.log 3)
  let QcutShift : ℕ := Nat.ceil ((L + 1) / (1 - α / a) + 1)
  let Qshift : ℕ := max QprefShift (max QleadShift QcutShift)
  let scaleSmall : ℝ := K * (Csmall * hΓ.thetaHat ^ (2 : ℕ))
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
  intro q hQq
  have hq_shift : Qshift ≤ q := (le_max_left Qshift (max Qsmall Qunion)).trans hQq
  have hq_small : Qsmall ≤ q :=
    (le_max_left Qsmall Qunion).trans
      ((le_max_right Qshift (max Qsmall Qunion)).trans hQq)
  have hq_union : Qunion ≤ q :=
    (le_max_right Qsmall Qunion).trans
      ((le_max_right Qshift (max Qsmall Qunion)).trans hQq)
  have hshift_q :
      P.real (badScaleEvent Hshift t α q) ≤
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailShift) ^ η)) := by
    simpa [K, S, b, L, ctop, τ, η, w, ρtop, ρbottom, ρcrude,
      Cbottom, Ctop, Kbottom, Kcrude, W, Mshift, ρgap, N0, H, Hshift,
      Dhigh, Dcrude, DenShift, Ohigh, Ocrude, BleadShift, BtailShift,
      cgapShift, QprefShift, QleadShift, QcutShift, Qshift] using
      hshiftLaw hP hStruct hΓ hσ_eq hparams (q := q) hq_shift
  have hshift_tail :
      P.real (badTailEvent (badScaleEvent Hshift t α) q) ≤
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailShift) ^ η)) := by
    have hmono :
        P.real (badTailEvent (badScaleEvent Hshift t α) q) ≤
          P.real (badScaleEvent Hshift t α q) :=
      measureReal_mono (μ := P)
        (badTailEvent_badScaleEvent_subset
          (H := Hshift) (t := t) (α := α) hα_nonneg)
    exact hmono.trans hshift_q
  have hsmall_tail :
      P.real
          (badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q)) ≤
        Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailSmall) ^ η)) := by
    simpa [K, S, η, w, W, ρgap, H, scaleSmall, ρsmall, Ksmall,
      prefSmall, Msmall, BleadSmall, BtailSmall, cgapSmall, QprefSmall,
      QleadSmall, Qsmall] using
      hsmallLaw hP hStruct hΓ hσ_eq hparams (Nentry := N0) q hq_small
  have hsplit :
      badTailEvent (badScaleEvent H t α) (N0 + q) ⊆
        badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q) ∪
          badTailEvent (badScaleEvent Hshift t α) q := by
    have hraw :=
      badTailEvent_subset_smallBottom_union_shifted
        (H := H) (Nentry := N0) (N := N0 + q) (t := t) (α := α)
        (Nat.le_add_right N0 q)
    simpa [Hshift, Nat.add_sub_cancel_left] using hraw
  have hBtailShift_pos : 0 < BtailShift := by
    have hDenShift_pos : 0 < DenShift := by
      simpa [DenShift] using
        mixedBottomTailDenominator_pos
          (Dhigh := Dhigh) (Dcrude := Dcrude) (η := η) (τ := τ) (σ := σ)
    have hBleadShift_pos : 0 < BleadShift := by
      have hleft : 0 < DenShift * (3 : ℝ) ^ Ohigh :=
        mul_pos hDenShift_pos
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) Ohigh)
      exact hleft.trans_le (le_max_left _ _)
    dsimp [BtailShift]
    positivity
  have hBtailSmall_pos : 0 < BtailSmall := by
    have hscaleSmall_pos : 0 < scaleSmall := by
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      dsimp [scaleSmall]
      exact mul_pos hK_pos (mul_pos hCsmall (pow_pos hΓ.thetaHat_pos 2))
    have hBleadSmall_pos : 0 < BleadSmall := by
      simpa [BleadSmall] using
        smallBottomTailDenominator_pos
          (scale := scaleSmall) (η := η) (σ := σ)
    dsimp [BtailSmall]
    positivity
  have hBleadUnion_pos : 0 < BleadUnion := by
    exact hBtailShift_pos.trans_le (le_max_left _ _)
  have hBtailUnion_pos : 0 < BtailUnion := by
    dsimp [BtailUnion]
    positivity
  have hBleadUnion_lt : BleadUnion < BtailUnion := by
    dsimp [BtailUnion]
    nlinarith
  let Alead : ℝ := ((3 : ℝ) ^ (q : ℝ) / BleadUnion) ^ η
  let Atail : ℝ := ((3 : ℝ) ^ (q : ℝ) / BtailUnion) ^ η
  have hshift_to_union :
      Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailShift) ^ η)) ≤
        Real.exp (-Alead) := by
    simpa [Alead, BleadUnion] using
      exp_neg_rpow_three_div_le_exp_neg_rpow_three_div_of_den_le
        (B₁ := BtailShift) (B₂ := BleadUnion) (η := η) (q := q)
        hBtailShift_pos hBleadUnion_pos (le_max_left _ _) hη_pos
  have hsmall_to_union :
      Real.exp (-(((3 : ℝ) ^ (q : ℝ) / BtailSmall) ^ η)) ≤
        Real.exp (-Alead) := by
    simpa [Alead, BleadUnion] using
      exp_neg_rpow_three_div_le_exp_neg_rpow_three_div_of_den_le
        (B₁ := BtailSmall) (B₂ := BleadUnion) (η := η) (q := q)
        hBtailSmall_pos hBleadUnion_pos (le_max_right _ _) hη_pos
  have hcUnion_pos : 0 < cgapUnion := by
    simpa [cgapUnion, BtailUnion] using
      inv_rpow_sub_pos_of_lt
        hBleadUnion_pos hBtailUnion_pos hη_pos hBleadUnion_lt
  have hqU_M :
      Nat.ceil (max 0 (Real.log (2 : ℝ))) ≤ q :=
    (le_max_left _ _).trans hq_union
  have hqU_R : Runion ≤ q :=
    (le_max_left Runion
        (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_union)
  have hqU_c :
      Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) / Real.log ρgap) ≤ q :=
    (le_max_right Runion
        (Nat.ceil ((2 * max 0 (-(Real.log cgapUnion))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_union)
  have hpref_union_gap :
      (2 : ℝ) ≤ Real.exp (Alead - Atail) := by
    have hpref_linear :
        (2 : ℝ) * (((q : ℝ) + 1) * (1 : ℝ) ^ q) ≤
          Real.exp (cgapUnion * ρgap ^ q) :=
      linear_prefactor_le_exp_const_mul_pow_of_large
        (M := (2 : ℝ)) (W := (1 : ℝ)) (C₀ := (2 : ℝ))
        (c := cgapUnion) (ρ := ρgap) (R := Runion) (q := q)
        (by norm_num) (by norm_num) hcUnion_pos hρgap_gt
        (by simp) hRunion hqU_M hqU_R hqU_c
    have hgap :
        cgapUnion * ρgap ^ q ≤ Alead - Atail := by
      simpa [Alead, Atail, cgapUnion, ρgap] using
        geometric_gap_le_rpow_three_nat_div_gap
          (Blead := BleadUnion) (Btail := BtailUnion) (η := η)
          (c := cgapUnion) (ρ := ρgap) (q := q)
          hBleadUnion_pos hBtailUnion_pos
          (le_rfl : cgapUnion ≤ BleadUnion ^ (-η) - BtailUnion ^ (-η))
          (le_rfl : ρgap ≤ (3 : ℝ) ^ η) hcUnion_pos.le
          (le_of_lt (lt_trans zero_lt_one hρgap_gt))
    have hpref_gap := hpref_linear.trans (Real.exp_le_exp.mpr hgap)
    have htwo_pref :
        (2 : ℝ) ≤ (2 : ℝ) * (((q : ℝ) + 1) * (1 : ℝ) ^ q) := by
      have hfactor : 1 ≤ ((q : ℝ) + 1) * (1 : ℝ) ^ q := by
        simp
      nlinarith
    exact htwo_pref.trans hpref_gap
  have hunion_measure :
      P.real (badTailEvent (badScaleEvent H t α) (N0 + q)) ≤
        Real.exp (-Alead) + Real.exp (-Alead) := by
    calc
      P.real (badTailEvent (badScaleEvent H t α) (N0 + q))
          ≤ P.real
              (badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q) ∪
                badTailEvent (badScaleEvent Hshift t α) q) :=
            measureReal_mono (μ := P) hsplit
      _ ≤ P.real
              (badTailEvent (smallBottomBadScaleEvent H N0 t α) (N0 + q)) +
            P.real (badTailEvent (badScaleEvent Hshift t α) q) :=
            measureReal_union_le _ _
      _ ≤ Real.exp (-Alead) + Real.exp (-Alead) := by
            exact add_le_add
              (hsmall_tail.trans hsmall_to_union)
              (hshift_tail.trans hshift_to_union)
  calc
    P.real (badTailEvent (badScaleEvent H t α) (N0 + q))
        ≤ Real.exp (-Alead) + Real.exp (-Alead) := hunion_measure
    _ = (2 : ℝ) * Real.exp (-Alead) := by ring
    _ ≤ Real.exp (Alead - Atail) * Real.exp (-Alead) :=
        mul_le_mul_of_nonneg_right hpref_union_gap (Real.exp_pos _).le
    _ = Real.exp (-Atail) := by
        rw [← Real.exp_add]
        ring_nf

end

end Section57
end Ch05
end Book
end Homogenization
