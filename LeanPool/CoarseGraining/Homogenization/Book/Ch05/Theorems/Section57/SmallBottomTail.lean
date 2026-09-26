/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.SmallBottomBand
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailDenominator
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGapQuantitative
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleThresholds

/-! # Small Bottom Tail -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory

/-!
# Tail collapse for the small-bottom band

This file converts the weighted kernel bound for the finite band
`n < Nentry` into the same stretched-exponential bad-scale tail used by the
shifted large-scale branch.
-/

noncomputable section

variable {Ω : Type*}

/-- The small-bottom bad-scale events are antitone in the bad scale. -/
theorem smallBottomBadScaleEvent_antitone
    {H : ℕ → ℕ → Ω → ℝ} {Nentry : ℕ} {t α : ℝ}
    (hα : 0 ≤ α) {N K : ℕ} (hNK : N ≤ K) :
    smallBottomBadScaleEvent H Nentry t α K ⊆
      smallBottomBadScaleEvent H Nentry t α N := by
  intro ω hω
  rcases hω with ⟨m, n, hn_entry, hnm, hKm, hbad⟩
  refine ⟨m, n, hn_entry, hnm, hNK.trans hKm, ?_⟩
  have hsub_le : m - K ≤ m - N := Nat.sub_le_sub_left hNK m
  have hcast_le : ((m - K : ℕ) : ℝ) ≤ ((m - N : ℕ) : ℝ) := by
    exact_mod_cast hsub_le
  have hexp_le :
      -α * ((m - N : ℕ) : ℝ) ≤ -α * ((m - K : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonpos_left hcast_le (by linarith)
  have hrhs_le :
      (3 : ℝ) ^ (-α * ((m - N : ℕ) : ℝ)) ≤
        (3 : ℝ) ^ (-α * ((m - K : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp_le
  exact lt_of_le_of_lt hrhs_le hbad

/-- Tail form of small-bottom monotonicity. -/
theorem badTailEvent_smallBottomBadScaleEvent_subset
    [MeasurableSpace Ω]
    {H : ℕ → ℕ → Ω → ℝ} {Nentry : ℕ} {t α : ℝ}
    (hα : 0 ≤ α) {N : ℕ} :
    badTailEvent (smallBottomBadScaleEvent H Nentry t α) N ⊆
      smallBottomBadScaleEvent H Nentry t α N := by
  intro ω hω
  rcases hω with ⟨K, hNK, hK⟩
  exact smallBottomBadScaleEvent_antitone
    (H := H) (Nentry := Nentry) (t := t) (α := α) hα hNK hK

/-- Denominator which rewrites the crude small-bottom `sigma * t` tail in the
common interpolated exponent. -/
noncomputable def smallBottomTailDenominator (scale η σ : ℝ) : ℝ :=
  (max 1 scale) ^ (σ / η)

theorem smallBottomTailDenominator_pos {scale η σ : ℝ} :
    0 < smallBottomTailDenominator scale η σ := by
  have hbase : 0 < max 1 scale :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 scale)
  exact Real.rpow_pos_of_pos hbase _

theorem one_le_smallBottomTailDenominator
    {scale η σ : ℝ} (hη : 0 < η) (hσ : 0 ≤ σ) :
    1 ≤ smallBottomTailDenominator scale η σ := by
  have hbase : 1 ≤ max 1 scale := le_max_left 1 scale
  have hexp : 0 ≤ σ / η := div_nonneg hσ hη.le
  have hpow :
      (max 1 scale) ^ (0 : ℝ) ≤ (max 1 scale) ^ (σ / η) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  simpa [smallBottomTailDenominator] using hpow

theorem scale_rpow_le_smallBottomTailDenominator_pow_eta
    {scale η σ : ℝ} (hscale : 0 < scale) (hη : 0 < η)
    (hσ : 0 < σ) :
    scale ^ σ ≤ (smallBottomTailDenominator scale η σ) ^ η := by
  have hbase : 0 < max 1 scale :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 scale)
  have hterm_nonneg : 0 ≤ (max 1 scale) ^ (σ / η) :=
    (Real.rpow_pos_of_pos hbase _).le
  have hpow_eq :
      ((max 1 scale) ^ (σ / η)) ^ η = (max 1 scale) ^ σ := by
    rw [← Real.rpow_mul hbase.le]
    congr 1
    field_simp [hη.ne']
  have hscale_le : scale ≤ max 1 scale := le_max_right 1 scale
  have hscale_pow : scale ^ σ ≤ (max 1 scale) ^ σ :=
    Real.rpow_le_rpow hscale.le hscale_le hσ.le
  simpa [smallBottomTailDenominator, hpow_eq] using hscale_pow

/-- The small-bottom denominator converts the crude `sigma * t` scale into
the common interpolated exponent. -/
theorem smallBottomTailDenominator_rpow_le_crude_scale
    {scale η σ t : ℝ} {q : ℕ}
    (hscale : 0 < scale) (hη : 0 < η) (hσ : 0 < σ)
    (hη_le : η ≤ σ * t) :
    (((3 : ℝ) ^ (q : ℝ) / smallBottomTailDenominator scale η σ) ^ η) ≤
      (((3 : ℝ) ^ (t * (q : ℝ)) / scale) ^ σ) := by
  let Den : ℝ := smallBottomTailDenominator scale η σ
  let X : ℝ := η * (q : ℝ)
  let Y : ℝ := σ * t * (q : ℝ)
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      smallBottomTailDenominator_pos (scale := scale) (η := η) (σ := σ)
  have hDen_pow :
      scale ^ σ ≤ Den ^ η := by
    simpa [Den] using
      scale_rpow_le_smallBottomTailDenominator_pow_eta
        (scale := scale) (η := η) (σ := σ) hscale hη hσ
  have hXY : X ≤ Y := by
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hη_le hq
    dsimp [X, Y]
    nlinarith
  have hgeneric :=
    rpow_three_div_den_rpow_le_of_exponent_le
      (X := X) (Y := Y) (D := scale) (Den := Den)
      (η := η) (γ := σ)
      hη hσ hscale hDen_pos hDen_pow hXY
  convert hgeneric using 1
  · dsimp [Den, X]
    congr 2
    field_simp [hη.ne']
  · dsimp [Y]
    congr 2
    field_simp [hσ.ne']

/-- Quantitative small-bottom bad-tail bound with the fixed prefactor-growth
threshold chosen before the law. -/
theorem exists_quantitative_threshold_smallBottomBadTail_quenchedProbeEnvelope_le_interpolated_tail
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {t α : ℝ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let η : ℝ := finiteQuenchedTailExponent d σ t
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let W : ℝ := max 1 w
        let ρgap : ℝ := (3 : ℝ) ^ η
        let C₀ : ℝ := 2 + Real.log W
        0 < t →
        0 ≤ α →
        α < t →
        ∃ R : ℕ,
          (∀ q : ℕ, R ≤ q →
            C₀ * (q : ℝ) ≤
              Real.exp ((Real.log ρgap / 2) * (q : ℝ))) ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ {Nentry : ℕ},
            let H : ℕ → ℕ → RegCoeffField d → ℝ :=
              quenchedProbeEnvelope hP hStruct
            let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
            let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
            let Ksmall : ℝ :=
              weightedGeometricExpKernelConst w (ρsmall ^ σ)
            let pref : ℝ := (Nentry : ℝ) * (S.card : ℝ) * w ^ Nentry
            let M : ℝ := max 1 (max 0 (pref * Ksmall))
            let Blead : ℝ := smallBottomTailDenominator scale η σ
            let Btail : ℝ := 2 * Blead
            let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
            let Qpref : ℕ :=
              max (Nat.ceil (max 0 (Real.log M)))
                (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
                  Real.log ρgap)))
            let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
            let Q : ℕ := max Qpref Qlead
            ∀ q : ℕ, Q ≤ q →
              P.real
                (badTailEvent
                  (smallBottomBadScaleEvent H Nentry t α)
                  (Nentry + q)) ≤
                Real.exp (-(((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
  obtain ⟨Ccrude, hCcrude, hkernel⟩ :=
    measureReal_smallBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro t α
  dsimp only
  intro ht hα_nonneg hαt
  classical
  let K : ℝ := quenchedProbeEnvelopeConst d
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let η : ℝ := finiteQuenchedTailExponent d σ t
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let W : ℝ := max 1 w
  let ρgap : ℝ := (3 : ℝ) ^ η
  let C₀ : ℝ := 2 + Real.log W
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  have hρgap_gt : 1 < ρgap := by
    dsimp [ρgap]
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hη_pos
  have hW_one : 1 ≤ W := by
    dsimp [W]
    exact le_max_left 1 w
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hlogW_nonneg : 0 ≤ Real.log W := Real.log_nonneg hW_one
    dsimp [C₀]
    linarith
  obtain ⟨R, hR⟩ :=
    linear_le_exp_linear_eventually
      (C := C₀) (γ := Real.log ρgap / 2)
      hC₀_nonneg (by
        have hlogρ_pos : 0 < Real.log ρgap := Real.log_pos hρgap_gt
        positivity)
  refine ⟨R, ?_, ?_⟩
  · simpa [K, S, η, w, W, ρgap, C₀] using hR
  intro P hP hStruct hΓ hσ_eq hparams Nentry
  let : IsProbabilityMeasure P := hP.isProbability
  let H : ℕ → ℕ → RegCoeffField d → ℝ :=
    quenchedProbeEnvelope hP hStruct
  let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  let ρsmall : ℝ := (3 : ℝ) ^ (t - α)
  let Ksmall : ℝ := weightedGeometricExpKernelConst w (ρsmall ^ σ)
  let pref : ℝ := (Nentry : ℝ) * (S.card : ℝ) * w ^ Nentry
  let M : ℝ := max 1 (max 0 (pref * Ksmall))
  let Blead : ℝ := smallBottomTailDenominator scale η σ
  let Btail : ℝ := 2 * Blead
  let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
  let Qpref : ℕ :=
    max (Nat.ceil (max 0 (Real.log M)))
      (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
        Real.log ρgap)))
  let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
  let Q : ℕ := max Qpref Qlead
  intro q hQq
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos hK_pos (mul_pos hCcrude (pow_pos hΓ.thetaHat_pos 2))
  have hBlead_pos : 0 < Blead := by
    simpa [Blead] using
      smallBottomTailDenominator_pos
        (scale := scale) (η := η) (σ := σ)
  have hBtail_pos : 0 < Btail := by
    dsimp [Btail]
    positivity
  have hBlead_lt_Btail : Blead < Btail := by
    dsimp [Btail]
    nlinarith
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
      (Real.one_lt_rpow hρsmall_gt hσ_pos)
  have hpref_nonneg : 0 ≤ pref := by
    dsimp [pref]
    positivity
  have hM_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left 1 _
  have hq_pref : Qpref ≤ q := (le_max_left Qpref Qlead).trans hQq
  have hq_lead : Qlead ≤ q := (le_max_right Qpref Qlead).trans hQq
  have hqM :
      Nat.ceil (max 0 (Real.log M)) ≤ q :=
    (le_max_left _ _).trans hq_pref
  have hqR : R ≤ q :=
    (le_max_left R
        (Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_pref)
  have hqc :
      Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap) ≤ q :=
    (le_max_right R
        (Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap))).trans
      ((le_max_right _ _).trans hq_pref)
  have hlead_one : 1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead := by
    simpa [Blead] using
      one_le_rpow_three_linear_sub_nat_div_of_natCeil_le
        (β := (1 : ℝ)) (O := (0 : ℝ)) (D := Blead) (q := q)
        (by norm_num) hBlead_pos
        (by simpa [Qlead] using hq_lead)
  have hη_le : η ≤ σ * t := by
    have hb_pos : 0 < (d : ℝ) / 2 := by
      have hd : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      positivity
    simpa [η, finiteQuenchedTailExponent] using
      interpolatedQuenchedTailExponent_le_sigma_mul_t
        (b := (d : ℝ) / 2) (σ := σ) (t := t)
        hb_pos hσ_pos ht
  let Aold : ℝ := (3 : ℝ) ^ (t * (q : ℝ)) / scale
  let Alead : ℝ := ((3 : ℝ) ^ (q : ℝ) / Blead) ^ η
  let Atail : ℝ := ((3 : ℝ) ^ (q : ℝ) / Btail) ^ η
  have hAlead_to_old : Alead ≤ Aold ^ σ := by
    simpa [Aold, Alead, Blead] using
      smallBottomTailDenominator_rpow_le_crude_scale
        (scale := scale) (η := η) (σ := σ) (t := t) (q := q)
        hscale_pos hη_pos hσ_pos hη_le
  have hAold_nonneg : 0 ≤ Aold := by
    dsimp [Aold]
    exact div_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      hscale_pos.le
  have hAold_one : 1 ≤ Aold := by
    have hAlead_one : 1 ≤ Alead := by
      dsimp [Alead]
      exact Real.one_le_rpow hlead_one hη_pos.le
    exact one_le_of_one_le_rpow hAold_nonneg hσ_pos
      (hAlead_one.trans hAlead_to_old)
  have hkernel_q :
      P.real (smallBottomBadScaleEvent H Nentry t α (Nentry + q)) ≤
        ((Nentry : ℝ) * ((S.card : ℝ) * w ^ Nentry * w ^ q)) *
          (Real.exp (-(Aold ^ σ)) * Ksmall) := by
    simpa [K, H, S, w, scale, Aold, ρsmall, Ksmall] using
      hkernel (t := t) (α := α) hP hStruct hΓ hσ_eq hparams
        (Nentry := Nentry) (q := q) ht hαt hAold_one
  have htail_subset :
      badTailEvent (smallBottomBadScaleEvent H Nentry t α) (Nentry + q) ⊆
        smallBottomBadScaleEvent H Nentry t α (Nentry + q) :=
    badTailEvent_smallBottomBadScaleEvent_subset
      (H := H) (Nentry := Nentry) (t := t) (α := α) hα_nonneg
  have htail_mono :
      P.real
          (badTailEvent
            (smallBottomBadScaleEvent H Nentry t α) (Nentry + q)) ≤
        P.real (smallBottomBadScaleEvent H Nentry t α (Nentry + q)) :=
    measureReal_mono (μ := P) htail_subset
  have hprefix_le :
      pref * Ksmall * w ^ q ≤ M * (((q : ℝ) + 1) * W ^ q) := by
    have hprefK_nonneg : 0 ≤ pref * Ksmall :=
      mul_nonneg hpref_nonneg hKsmall_pos.le
    have hprefK_le_M : pref * Ksmall ≤ M := by
      calc
        pref * Ksmall ≤ max 0 (pref * Ksmall) :=
          le_max_right 0 (pref * Ksmall)
        _ ≤ M := by
          dsimp [M]
          exact le_max_right 1 _
    have hwW : w ≤ W := by
      dsimp [W]
      exact le_max_right 1 w
    have hwq_le : w ^ q ≤ W ^ q :=
      pow_le_pow_left₀ hw_pos.le hwW q
    have hWq_nonneg : 0 ≤ W ^ q := by positivity
    have hleft :
        pref * Ksmall * w ^ q ≤ M * W ^ q :=
      mul_le_mul hprefK_le_M hwq_le
        (pow_nonneg hw_pos.le q) (zero_le_one.trans hM_one)
    have hqplus_one : 1 ≤ (q : ℝ) + 1 := by
      have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
      linarith
    have hright :
        M * W ^ q ≤ M * (((q : ℝ) + 1) * W ^ q) := by
      have hfactor : W ^ q ≤ ((q : ℝ) + 1) * W ^ q := by
        calc
          W ^ q = 1 * W ^ q := by ring
          _ ≤ ((q : ℝ) + 1) * W ^ q :=
            mul_le_mul_of_nonneg_right hqplus_one hWq_nonneg
      exact mul_le_mul_of_nonneg_left hfactor (zero_le_one.trans hM_one)
    exact hleft.trans hright
  have hc_pos : 0 < cgap := by
    simpa [cgap, Btail] using
      inv_rpow_sub_pos_of_lt hBlead_pos hBtail_pos hη_pos hBlead_lt_Btail
  have hpref_gap :
      M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (Alead - Atail) := by
    have hpref_exp :
        M * (((q : ℝ) + 1) * W ^ q) ≤
          Real.exp (cgap * ρgap ^ q) :=
      linear_prefactor_le_exp_const_mul_pow_of_large
        (M := M) (W := W) (C₀ := C₀) (c := cgap)
        (ρ := ρgap) (R := R) (q := q)
        hM_one hW_one hc_pos hρgap_gt
        (le_rfl : 2 + Real.log W ≤ C₀) hR hqM hqR hqc
    have hgap :
        cgap * ρgap ^ q ≤ Alead - Atail := by
      simpa [Alead, Atail, cgap, ρgap] using
        geometric_gap_le_rpow_three_nat_div_gap
          (Blead := Blead) (Btail := Btail) (η := η)
          (c := cgap) (ρ := ρgap) (q := q)
          hBlead_pos hBtail_pos
          (le_rfl : cgap ≤ Blead ^ (-η) - Btail ^ (-η))
          (le_rfl : ρgap ≤ (3 : ℝ) ^ η) hc_pos.le
          (le_of_lt (lt_trans zero_lt_one hρgap_gt))
    exact hpref_exp.trans (Real.exp_le_exp.mpr hgap)
  have hexp_old :
      Real.exp (-(Aold ^ σ)) ≤ Real.exp (-Alead) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmeasure_tail :
      P.real
          (badTailEvent
            (smallBottomBadScaleEvent H Nentry t α) (Nentry + q)) ≤
        M * (((q : ℝ) + 1) * W ^ q) * Real.exp (-Alead) := by
    calc
      P.real
          (badTailEvent
            (smallBottomBadScaleEvent H Nentry t α) (Nentry + q))
          ≤ P.real (smallBottomBadScaleEvent H Nentry t α (Nentry + q)) :=
            htail_mono
      _ ≤ ((Nentry : ℝ) * ((S.card : ℝ) * w ^ Nentry * w ^ q)) *
            (Real.exp (-(Aold ^ σ)) * Ksmall) :=
            hkernel_q
      _ = pref * Ksmall * w ^ q * Real.exp (-(Aold ^ σ)) := by
            dsimp [pref]
            ring
      _ ≤ pref * Ksmall * w ^ q * Real.exp (-Alead) :=
            mul_le_mul_of_nonneg_left hexp_old
              (by positivity : 0 ≤ pref * Ksmall * w ^ q)
      _ ≤ M * (((q : ℝ) + 1) * W ^ q) * Real.exp (-Alead) :=
            mul_le_mul_of_nonneg_right hprefix_le (Real.exp_pos _).le
  calc
    P.real
        (badTailEvent
          (smallBottomBadScaleEvent H Nentry t α) (Nentry + q))
        ≤ M * (((q : ℝ) + 1) * W ^ q) * Real.exp (-Alead) :=
          hmeasure_tail
    _ ≤ Real.exp (Alead - Atail) * Real.exp (-Alead) :=
          mul_le_mul_of_nonneg_right hpref_gap (Real.exp_pos _).le
    _ = Real.exp (-Atail) := by
          rw [← Real.exp_add]
          ring_nf

end

end Section57
end Ch05
end Book
end Homogenization
