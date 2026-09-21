/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformCrudeBottom
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePairCollapse

/-! # Uniform High Bottom -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# The mixed high-bottom branch at the uniform endpoint

The endpoint high-bottom branch keeps the localized `Γ_2` concentration
mechanism and adds the deterministic `Γ_∞` crude cutoff.  The final row
collapse is built on these two separate inputs.
-/

noncomputable section

/-- The localized high estimate in the high-bottom branch, specialized to
the uniform endpoint by forgetting `Γ_∞` to finite `Γ_2`. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_high_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry a : ℝ,
      0 < Cfluct ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          softPairTail pref highA 2 := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hhigh⟩ :=
    measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_high
      (d := d) (σ := (2 : ℝ)) (by norm_num) params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hInf hparams q m n
  dsimp only
  intro hnm hqm ht hαt
  let hΓ2 := hInf.toGammaSigma 2 (by norm_num : (0 : ℝ) < 2)
  have hΓ2_params : hΓ2.params = params := by
    simpa [hΓ2, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using hparams
  simpa [hΓ2, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using!
    hhigh (t := t) (αbad := αbad) hP hStruct hΓ2 rfl hΓ2_params
      (q := q) (m := m) (n := n) hnm hqm ht hαt

/-- The deterministic crude cutoff in the high-bottom branch.  If the crude
tail parameter is at least one, the bad-pair event, hence the high-bottom
subevent, has zero probability. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_eq_zero_of_crudeA_one_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {Centry a t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → n ≤ q → αbad < t → 1 ≤ crudeA →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) = 0 := by
  obtain ⟨Ccrude, hCcrude, hraw⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_eq_zero_of_gammaInfinity
      (d := d) params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro Centry a t αbad P hP hStruct hInf hparams q m n
  dsimp only
  intro hnm hqm hnq hαt hcrudeA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let scale : ℝ := K * (Ccrude * hInf.thetaHat ^ (2 : ℕ))
  let T : ℝ := (3 : ℝ) ^ (-x)
  let lam : ℝ := T / scale
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      (K * Ccrude * hInf.thetaHat ^ (2 : ℕ))
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hlam_lower : crudeA ≤ lam := by
    simpa [K, x, scale, T, lam, crudeA] using
      crudeBottom_tailParameter_discount_lower_bound
        (K := K) (C := Ccrude) (θ := hInf.thetaHat)
        (t := t) (α := αbad) (q := q) (m := m) (n := n)
        hK_pos hCcrude hInf.thetaHat_pos hnq hqm
  have hlam_one : 1 ≤ lam := hcrudeA_one.trans hlam_lower
  have hbad_zero :
      P.real (badPairEvent Hshift t αbad q m n) = 0 := by
    have h := hraw (t := t) (αbad := αbad) hP hStruct hInf hparams
      (N0 := N0) (q := q) (m := m) (n := n)
    simpa [K, Hshift, x, scale, T, lam] using h hnm hqm hlam_one
  have hle_zero :
      P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤ 0 := by
    have hmono :
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          P.real (badPairEvent Hshift t αbad q m n) :=
      measureReal_mono (μ := P) (by
        intro ω hω
        exact hω.2.2)
    exact hmono.trans_eq hbad_zero
  exact le_antisymm hle_zero MeasureTheory.measureReal_nonneg

/-- Convert a one-branch softened fixed-pair estimate into the weighted row
shape used by the endpoint bottom summation. -/
theorem le_weighted_row_of_le_soft_single
    {x pref highA A ρ η C w : ℝ} {q r : ℕ}
    (hx : x ≤ softPairTail pref highA 2)
    (hpref : max 1 pref ≤ C * w ^ q * w ^ r)
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hpow : (A * ρ ^ r) ^ η ≤ (max 1 highA) ^ (2 : ℝ)) :
    x ≤
      (Real.exp 1 * C * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
  have hexp :
      Real.exp (1 - (max 1 highA) ^ (2 : ℝ)) ≤
        Real.exp (1 - (A * ρ ^ r) ^ η) :=
    Real.exp_le_exp.mpr (by linarith)
  have hrow_nonneg : 0 ≤ C * w ^ q * w ^ r := by
    positivity
  have hexp_split :
      Real.exp (1 - (A * ρ ^ r) ^ η) =
        Real.exp 1 * Real.exp (-((A * ρ ^ r) ^ η)) := by
    rw [← Real.exp_add]
    congr 1
  calc
    x ≤ softPairTail pref highA 2 := hx
    _ = max 1 pref * Real.exp (1 - (max 1 highA) ^ (2 : ℝ)) := by
          rfl
    _ ≤ (C * w ^ q * w ^ r) *
        Real.exp (1 - (A * ρ ^ r) ^ η) :=
          mul_le_mul hpref hexp (Real.exp_pos _).le hrow_nonneg
    _ =
        (Real.exp 1 * C * w ^ q) *
          (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
          rw [hexp_split]
          ring

/-- Endpoint high-bottom deterministic tail-parameter comparison.

When the crude cutoff has not fired, the crude denominator pays for the
missing high-branch factor `3 ^ ((d - 2t) * (q - n))`. -/
theorem uniformEndpoint_highBottom_tailParameter_rpow_le_high
    {d q r : ℕ} [NeZero d] {j : Fin (q + 1)}
    {t α L Dhigh Dcrude Den : ℝ}
    (ht : 0 < t) (hαt : α < t) (htb : t ≤ (d : ℝ) / 2)
    (hDhigh : 0 < Dhigh) (hDcrude : 0 < Dcrude) (hDen : 0 < Den)
    (hDen_dom :
      Dhigh ^ (2 : ℝ) *
          (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤
        Den ^ ((d : ℕ) : ℝ))
    (hcrude :
      (3 : ℝ) ^
          (t * ((q - (q - j.val) : ℕ) : ℝ) +
            (t - α) * ((q + r - q : ℕ) : ℝ)) /
        Dcrude < 1) :
    let b : ℝ := (d : ℝ) / 2
    let m : ℕ := q + r
    let n : ℕ := q - j.val
    let highA : ℝ :=
      (3 : ℝ) ^
          (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
            (t - α) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
        Dhigh
    let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
    let ρ : ℝ := (3 : ℝ) ^ (2 * (t - α) / ((d : ℕ) : ℝ))
    (A * ρ ^ r) ^ ((d : ℕ) : ℝ) ≤ (max 1 highA) ^ (2 : ℝ) := by
  intro b m n highA A ρ
  have hd_pos : 0 < ((d : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hthree_pos : 0 < (3 : ℝ) := by norm_num
  have hthree_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  have hκ_nonneg : 0 ≤ ((d : ℝ) - 2 * t) / t := by
    have hnum : 0 ≤ (d : ℝ) - 2 * t := by linarith
    positivity
  let κ : ℝ := ((d : ℝ) - 2 * t) / t
  let Z : ℝ :=
    t * ((q - (q - j.val) : ℕ) : ℝ) +
      (t - α) * ((q + r - q : ℕ) : ℝ)
  let M : ℝ := ((d : ℝ) - 2 * t) * (j.val : ℝ)
  let X : ℝ :=
    (d : ℝ) * (q : ℝ) - (d : ℝ) * (L + 1) +
      2 * (t - α) * (r : ℝ)
  let Y : ℝ :=
    2 *
      (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
        (t - α) * ((m - q : ℕ) : ℝ) - b * (L + 1))
  have hm_sub_q : ((m - q : ℕ) : ℝ) = (r : ℝ) := by
    dsimp [m]
    rw [Nat.add_sub_cancel_left]
  have hq_sub_n : ((q - n : ℕ) : ℝ) = (j.val : ℝ) := by
    dsimp [n]
    have hj : j.val ≤ q := Nat.lt_succ_iff.mp j.isLt
    norm_num [Nat.sub_sub_self hj]
  have hY_eq : Y = X - M := by
    dsimp [X, Y, M, b]
    rw [hm_sub_q, hq_sub_n]
    ring
  have hZ_eq :
      Z = t * (j.val : ℝ) + (t - α) * (r : ℝ) := by
    dsimp [Z]
    have hj : j.val ≤ q := Nat.lt_succ_iff.mp j.isLt
    rw [Nat.sub_sub_self hj, Nat.add_sub_cancel_left]
  have hM_le : M ≤ κ * Z := by
    have hgap_nonneg : 0 ≤ t - α := (sub_pos.mpr hαt).le
    have hj_nonneg : 0 ≤ (j.val : ℝ) := by positivity
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    have htj_nonneg : 0 ≤ t * (j.val : ℝ) := mul_nonneg ht.le hj_nonneg
    have hrow_nonneg : 0 ≤ (t - α) * (r : ℝ) :=
      mul_nonneg hgap_nonneg hr_nonneg
    have hterm_le :
        t * (j.val : ℝ) ≤
          t * (j.val : ℝ) + (t - α) * (r : ℝ) := by
      linarith
    calc
      M = κ * (t * (j.val : ℝ)) := by
        dsimp [M, κ]
        field_simp [ht.ne']
      _ ≤ κ * (t * (j.val : ℝ) + (t - α) * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hterm_le hκ_nonneg
      _ = κ * Z := by
        rw [hZ_eq]
  have hcrude_num : (3 : ℝ) ^ Z < Dcrude := by
    have hcrude' : (3 : ℝ) ^ Z / Dcrude < 1 := by
      simpa [Z] using hcrude
    exact (div_lt_one hDcrude).mp hcrude'
  have hthreeM_le :
      (3 : ℝ) ^ M ≤ (max 1 Dcrude) ^ κ := by
    have hpowMκ :
        (3 : ℝ) ^ M ≤ (3 : ℝ) ^ (κ * Z) :=
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) hM_le
    have hpow_mul :
        (3 : ℝ) ^ (κ * Z) = ((3 : ℝ) ^ Z) ^ κ := by
      rw [← Real.rpow_mul hthree_nonneg]
      ring_nf
    have hmaxD : (3 : ℝ) ^ Z ≤ max 1 Dcrude :=
      (le_of_lt hcrude_num).trans (le_max_right 1 Dcrude)
    have hmono :
        ((3 : ℝ) ^ Z) ^ κ ≤ (max 1 Dcrude) ^ κ :=
      Real.rpow_le_rpow
        (Real.rpow_pos_of_pos hthree_pos Z).le hmaxD hκ_nonneg
    exact hpowMκ.trans (by simpa [hpow_mul] using hmono)
  have hAρ_eq :
      (A * ρ ^ r) ^ ((d : ℕ) : ℝ) =
        (3 : ℝ) ^ X / Den ^ ((d : ℕ) : ℝ) := by
    have hρ_pow :
        ρ ^ r = (3 : ℝ) ^ ((2 * (t - α) / ((d : ℕ) : ℝ)) * (r : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hthree_nonneg]
    have hbase :
        A * ρ ^ r =
          (3 : ℝ) ^ (X / ((d : ℕ) : ℝ)) / Den := by
      dsimp [A, ρ, X]
      rw [hρ_pow]
      calc
        ((3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den) *
            (3 : ℝ) ^ ((2 * (t - α) / ((d : ℕ) : ℝ)) * (r : ℝ))
            =
          ((3 : ℝ) ^ ((q : ℝ) - (L + 1)) *
            (3 : ℝ) ^ ((2 * (t - α) / ((d : ℕ) : ℝ)) * (r : ℝ))) /
              Den := by ring
        _ =
          (3 : ℝ) ^
              (((q : ℝ) - (L + 1)) +
                (2 * (t - α) / ((d : ℕ) : ℝ)) * (r : ℝ)) /
              Den := by
            rw [← Real.rpow_add hthree_pos]
        _ = (3 : ℝ) ^ (X / ((d : ℕ) : ℝ)) / Den := by
            congr 2
            field_simp [hd_pos.ne']
            ring
    rw [hbase]
    rw [Real.div_rpow (Real.rpow_nonneg hthree_nonneg _) hDen.le]
    congr 1
    rw [← Real.rpow_mul hthree_nonneg]
    congr 1
    field_simp [hd_pos.ne']
  have hhigh_sq_le :
      (3 : ℝ) ^ Y / Dhigh ^ (2 : ℝ) ≤ (max 1 highA) ^ (2 : ℝ) := by
    have hhigh_nonneg : 0 ≤ highA := by
      dsimp [highA]
      exact div_nonneg (Real.rpow_pos_of_pos hthree_pos _).le hDhigh.le
    have hhigh_sq :
        highA ^ (2 : ℝ) =
          (3 : ℝ) ^ Y / Dhigh ^ (2 : ℝ) := by
      dsimp [highA, Y]
      rw [Real.div_rpow (Real.rpow_nonneg hthree_nonneg _) hDhigh.le]
      congr 1
      rw [← Real.rpow_mul hthree_nonneg]
      congr 1
      ring
    have hmono :
        highA ^ (2 : ℝ) ≤ (max 1 highA) ^ (2 : ℝ) :=
      Real.rpow_le_rpow hhigh_nonneg
        (le_max_right 1 highA) (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    simpa [hhigh_sq] using hmono
  have hnum :
      (3 : ℝ) ^ X ≤ (3 : ℝ) ^ Y * (max 1 Dcrude) ^ κ := by
    calc
      (3 : ℝ) ^ X
          = (3 : ℝ) ^ (Y + M) := by
          rw [hY_eq]
          ring_nf
      _ = (3 : ℝ) ^ Y * (3 : ℝ) ^ M := by
          rw [Real.rpow_add hthree_pos]
      _ ≤ (3 : ℝ) ^ Y * (max 1 Dcrude) ^ κ :=
          mul_le_mul_of_nonneg_left hthreeM_le
            (Real.rpow_pos_of_pos hthree_pos Y).le
  have hMpos : 0 < (max 1 Dcrude) ^ κ := by
    exact Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 Dcrude)) κ
  have hDhigh_sq_pos : 0 < Dhigh ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos hDhigh 2
  rw [hAρ_eq]
  calc
    (3 : ℝ) ^ X / Den ^ ((d : ℕ) : ℝ)
        ≤ ((3 : ℝ) ^ Y * (max 1 Dcrude) ^ κ) /
            Den ^ ((d : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hnum
            (Real.rpow_pos_of_pos hDen ((d : ℕ) : ℝ)).le
    _ ≤ ((3 : ℝ) ^ Y * (max 1 Dcrude) ^ κ) /
            (Dhigh ^ (2 : ℝ) * (max 1 Dcrude) ^ κ) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (Real.rpow_pos_of_pos hthree_pos Y).le hMpos.le)
            (mul_pos hDhigh_sq_pos hMpos) hDen_dom
    _ = (3 : ℝ) ^ Y / Dhigh ^ (2 : ℝ) := by
          field_simp [hDhigh_sq_pos.ne', hMpos.ne']
    _ ≤ (max 1 highA) ^ (2 : ℝ) := hhigh_sq_le

/-- Endpoint high-bottom fixed row estimate.  The only side condition is the
explicit domination of the high denominator and the crude cutoff denominator by
the selected endpoint denominator. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        αbad < t →
        t ≤ b →
        0 < Den →
        Dhigh ^ (2 : ℝ) *
            (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤ Den ^ η →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
  obtain ⟨Cfluct, CentryHigh, aHigh, hCfluct, hCentryHigh, haHigh, hhigh⟩ :=
    measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_high_gammaInfinity
      (d := d) params
  obtain ⟨Ccrude, hCcrude, hzero⟩ :=
    measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_eq_zero_of_crudeA_one_gammaInfinity
      (d := d) params
  refine ⟨Cfluct, Ccrude, CentryHigh, aHigh,
    hCfluct, hCcrude, hCentryHigh, haHigh, ?_⟩
  intro t αbad Den P hP hStruct hInf hparams q r j
  dsimp only
  intro ht hαt htb hDen hDen_dom
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity CentryHigh
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (aHigh * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
  let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  let m : ℕ := q + r
  let n : ℕ := q - j.val
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let highA : ℝ :=
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
      Dhigh
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      Dcrude
  have hd_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hDhigh_pos : 0 < Dhigh := by
    dsimp [Dhigh]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num : (0 : ℝ) < 2) hK_pos) hCfluct)
      (pow_pos hInf.thetaHat_pos 2)
  have hDcrude_pos : 0 < Dcrude := by
    dsimp [Dcrude]
    exact mul_pos (mul_pos hK_pos hCcrude) (pow_pos hInf.thetaHat_pos 2)
  have hqm : q ≤ m := by
    dsimp [m]
    exact Nat.le_add_right q r
  have hnq : n ≤ q := by
    dsimp [n]
    exact Nat.sub_le q j.val
  have htail_nonneg :
      0 ≤ (Cpref * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
    positivity
  by_cases hnm : n < m
  · by_cases hcrude_one : 1 ≤ crudeA
    · have hzero_pair :
          P.real (highBottomPairEvent Hshift K aHigh t αbad q m n) = 0 := by
        have hz :=
          hzero (Centry := CentryHigh) (a := aHigh) (t := t) (αbad := αbad)
            hP hStruct hInf hparams (q := q) (m := m) (n := n)
        simpa [K, N0, Hshift, crudeA, Dcrude] using
          hz hnm hqm hnq hαt hcrude_one
      rw [hzero_pair]
      exact htail_nonneg
    · have hcrude_lt : crudeA < 1 := lt_of_not_ge hcrude_one
      have hfixed :
          P.real (highBottomPairEvent Hshift K aHigh t αbad q m n) ≤
            softPairTail pref highA 2 := by
        have hx :=
          hhigh (t := t) (αbad := αbad)
            hP hStruct hInf hparams (q := q) (m := m) (n := n)
        dsimp only at hx
        simpa [K, N0, Hshift, D, S, b, L, pref, highA, Dhigh] using
          hx hnm hqm ht hαt
      have hw_pos : 0 < w := by
        dsimp [w]
        exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
      have hw_one : 1 ≤ w := by
        have hn : 1 ≤ 3 ^ d :=
          Nat.succ_le_of_lt (pow_pos (by norm_num : (0 : ℕ) < 3) d)
        simpa [w] using (by exact_mod_cast hn : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ))
      have hwq_one : 1 ≤ w ^ q := one_le_pow₀ hw_one
      have hwr_one : 1 ≤ w ^ r := one_le_pow₀ hw_one
      have hDcard :
          (D.card : ℝ) ≤ w ^ q * w ^ r := by
        have hnm_le : n ≤ m := le_of_lt hnm
        simpa [D, w, m, n] using
          descendantsAtScale_bottom_row_card_le_weight
            (d := d) (N := N0) (q := q) (r := r) (j := j) hnm_le
      have hpref_bound :
          max 1 pref ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
        have hD_nonneg : 0 ≤ (D.card : ℝ) := by positivity
        have hpref_le :
            pref ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
          calc
            pref = (S.card : ℝ) * (D.card : ℝ) := rfl
            _ ≤ max 1 (S.card : ℝ) * (w ^ q * w ^ r) :=
              mul_le_mul
                (le_max_right 1 (S.card : ℝ)) hDcard
                hD_nonneg
                ((by norm_num : (0 : ℝ) ≤ 1).trans
                  (le_max_left 1 (S.card : ℝ)))
            _ = max 1 (S.card : ℝ) * w ^ q * w ^ r := by ring
        have hone :
            1 ≤ max 1 (S.card : ℝ) * w ^ q * w ^ r := by
          have hmaxS : 1 ≤ max 1 (S.card : ℝ) :=
            le_max_left 1 (S.card : ℝ)
          nlinarith [hmaxS, hwq_one, hwr_one]
        exact max_le hone hpref_le
      have hpow :
          (A * ρ ^ r) ^ η ≤ (max 1 highA) ^ (2 : ℝ) := by
        simpa [b, m, n, highA, A, ρ, η, Dhigh, Dcrude, crudeA] using
          uniformEndpoint_highBottom_tailParameter_rpow_le_high
            (d := d) (q := q) (r := r) (j := j)
            (t := t) (α := αbad) (L := L)
            (Dhigh := Dhigh) (Dcrude := Dcrude) (Den := Den)
            ht hαt (by simpa [b] using htb)
            hDhigh_pos hDcrude_pos hDen
            (by simpa [Dhigh, Dcrude, η] using hDen_dom)
            (by simpa [m, n, Dcrude, crudeA] using hcrude_lt)
      have hCpref_nonneg : 0 ≤ max 1 (S.card : ℝ) := by
        exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (S.card : ℝ))
      have hrow :=
        le_weighted_row_of_le_soft_single
          (x := P.real (highBottomPairEvent Hshift K aHigh t αbad q m n))
          (pref := pref) (highA := highA) (A := A) (ρ := ρ) (η := η)
          (C := max 1 (S.card : ℝ)) (w := w) (q := q) (r := r)
          hfixed hpref_bound hCpref_nonneg hw_pos.le hpow
      change
        P.real (highBottomPairEvent Hshift K aHigh t αbad q m n) ≤
          (Cpref * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))
      calc
        P.real (highBottomPairEvent Hshift K aHigh t αbad q m n)
            ≤ (Real.exp 1 * max 1 (S.card : ℝ) * w ^ q) *
                (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := hrow
        _ = (Cpref * w ^ q) *
                (w ^ r * Real.exp (-((A * ρ ^ r) ^ η))) := by
              dsimp [Cpref]
  · have hempty :
        highBottomPairEvent Hshift K aHigh t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, badPairEvent, hnm]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact htail_nonneg

/-- Endpoint high-bottom component estimate after summing the fixed rows. -/
theorem measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_gammaInfinity
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Den : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
        let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        0 < t →
        αbad < t →
        t ≤ b →
        0 < Den →
        Dhigh ^ (2 : ℝ) *
            (max 1 Dcrude) ^ (((d : ℝ) - 2 * t) / t) ≤ Den ^ η →
        1 ≤ A →
        P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * (Cpref * w ^ q) *
            (Real.exp (-(A ^ η)) *
              weightedGeometricExpKernelConst w (ρ ^ η)) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hrow⟩ :=
    measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_gammaInfinity
      (d := d) params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad Den P hP hStruct hInf hparams q
  dsimp only
  intro ht hαt htb hDen hDen_dom hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
  let ρ : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
  let Cpref : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hρ_gt : 1 < ρ := by
    have hexp_pos : 0 < 2 * (t - αbad) / η := by
      exact div_pos
        (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hαt)) hη_pos
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (2 * (t - αbad) / η) :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hexp_pos
  have hC_nonneg : 0 ≤ Cpref * w ^ q := by
    dsimp [Cpref]
    positivity
  exact
    measureReal_highBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (A := A) (ρ := ρ) (η := η)
      (C := Cpref * w ^ q) (w := w)
      hC_nonneg hw_pos hA_one hρ_gt hη_pos
      (by
        intro r j
        simpa [K, N0, Hshift, S, b, L, η, w, Dhigh, Dcrude,
          A, ρ, Cpref] using
          hrow (t := t) (αbad := αbad) (Den := Den)
            hP hStruct hInf hparams
            (q := q) (r := r) (j := j)
            ht hαt htb hDen hDen_dom)

end

end Section57
end Ch05
end Book
end Homogenization
