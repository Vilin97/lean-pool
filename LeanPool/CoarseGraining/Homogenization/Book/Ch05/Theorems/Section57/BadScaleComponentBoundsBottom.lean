/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairNoLog
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentRows
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsTop

/-! # Bad Scale Component Bounds Bottom -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Bottom component bad-scale bounds

This file builds the concrete bottom row estimates used by the weighted
component summation lemmas.
-/

noncomputable section

private theorem rpow_three_mul_rpow_pow_nat_eq
    {x y : ℝ} {r : ℕ} :
    (3 : ℝ) ^ x * ((3 : ℝ) ^ y) ^ r =
      (3 : ℝ) ^ (x + y * (r : ℝ)) := by
  have hpow :
      ((3 : ℝ) ^ y) ^ r = (3 : ℝ) ^ (y * (r : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hpow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

/-- Deterministic lower bound on the high-bottom tail parameter. -/
theorem highBottom_lam_lower
    {d : ℕ} [NeZero d]
    {K Cfluct θ a t α : ℝ} {q r : ℕ} {j : Fin (q + 1)}
    (hK : 0 < K) (hCfluct : 0 < Cfluct) (hθ : 0 < θ)
    (ha : 0 < a) (ht : 0 < t)
    (hαt : α < t) (hαb : α < (d : ℝ) / 2)
    (hαharm : α * (1 + ((d : ℝ) / 2) / a) < (d : ℝ) / 2) :
    let m : ℕ := q + r
    let n : ℕ := q - j.val
    let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let ℓ : ℕ :=
      Nat.ceil
        ((a * Real.log 3)⁻¹ *
          (Real.log (max (2 * K) 1) + x * Real.log 3))
    let b : ℝ := (d : ℝ) / 2
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let c : ℝ :=
      min t
        (min b
          (min (t - α)
            (min (b - α)
              (min ((t - α) * (1 + b / a))
                (b - α * (1 + b / a))))))
    let scale : ℝ :=
      Cfluct * (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ℓ : ℕ) : ℝ)) *
        θ ^ (2 : ℕ)
    let T : ℝ := (3 : ℝ) ^ (-x)
    let lam : ℝ := T / (2 * K * scale)
    let A : ℝ :=
      (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
        (2 * K * Cfluct * θ ^ (2 : ℕ))
    let ρ : ℝ := (3 : ℝ) ^ c
    ℓ < n → n < m → A * ρ ^ r ≤ lam := by
  intro m n x ℓ b L c scale T lam A ρ hℓn hnm
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hL_nonneg : 0 ≤ L := by
    have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
    have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
      Real.log_nonneg (le_max_right (2 * K) 1)
    dsimp [L]
    positivity
  have hqm : q ≤ m := by
    dsimp [m]
    exact Nat.le_add_right q r
  have hnm_le : n ≤ m := le_of_lt hnm
  have hceil :
      (ℓ : ℝ) ≤ L + max (x / a) 0 + 1 := by
    have hℓ_eq : ℓ = selectedBadPairScale K a t α q m n := by
      dsimp [ℓ, selectedBadPairScale, x]
    rw [hℓ_eq]
    simpa [L, x] using
      selectedBadPairScale_cast_le_logOffset
        (K := K) (a := a) (t := t) (α := α)
        (q := q) (m := m) (n := n) ha
  have hexp_comp :
      b * ((n - ℓ : ℕ) : ℝ) - x ≥
        c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) - b * (L + 1) := by
    have hraw :=
      highNatScaleExponent_lower_bound_of_ceil_any_q
        (a := a) (b := b) (t := t) (α := α) (L := L)
        (q := q) (m := m) (n := n) (ℓ := ℓ)
        ha hb_pos ht hαt hαb hαharm hL_nonneg
        (le_of_lt hℓn) hqm hnm_le
        (by simpa [x] using hceil)
    simpa [x, c] using hraw
  have hden_pos : 0 < 2 * K * Cfluct * θ ^ (2 : ℕ) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hK) hCfluct)
      (pow_pos hθ 2)
  have hlam_eq :
      lam =
        (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
    let decay : ℝ :=
      (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ℓ : ℕ) : ℝ))
    have hdecay_pos : 0 < decay := by
      dsimp [decay]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hquot :
        (3 : ℝ) ^ (-x) / decay =
          (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) := by
      dsimp [decay, b]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring_nf
    dsimp [lam, T, scale]
    change
      (3 : ℝ) ^ (-x) /
          (2 * K * (Cfluct * decay * θ ^ (2 : ℕ))) =
        (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))
    calc
      (3 : ℝ) ^ (-x) /
          (2 * K * (Cfluct * decay * θ ^ (2 : ℕ)))
          =
        ((3 : ℝ) ^ (-x) / decay) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            field_simp [hK.ne', hCfluct.ne', hθ.ne', hdecay_pos.ne']
      _ =
        (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            rw [hquot]
  have hpow_base :
      (3 : ℝ) ^ (c * ((q : ℝ) + (r : ℝ)) - b * (L + 1)) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))
        =
      A * ρ ^ r := by
    dsimp [A, ρ]
    have hrpow :=
      rpow_three_mul_rpow_pow_nat_eq
        (x := c * (q : ℝ) - b * (L + 1))
        (y := c) (r := r)
    calc
      (3 : ℝ) ^ (c * ((q : ℝ) + (r : ℝ)) - b * (L + 1)) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))
          =
        ((3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) *
            ((3 : ℝ) ^ c) ^ r) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            rw [hrpow]
            congr 1
            ring_nf
      _ =
        ((3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))) *
            ((3 : ℝ) ^ c) ^ r := by
            field_simp [hden_pos.ne']
  rw [hlam_eq]
  rw [← hpow_base]
  have hmr : ((m - q : ℕ) : ℝ) = (r : ℝ) := by
    dsimp [m]
    rw [Nat.add_sub_cancel_left]
  have hpow_le :
      (3 : ℝ) ^ (c * ((q : ℝ) + (r : ℝ)) - b * (L + 1)) ≤
        (3 : ℝ) ^ (b * ((n - ℓ : ℕ) : ℝ) - x) := by
    exact
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3)
        (by
          have hcomp := hexp_comp
          rw [hmr] at hcomp
          linarith)
  exact div_le_div_of_nonneg_right hpow_le hden_pos.le

/-- Deterministic lower bound on the crude-bottom tail parameter.  The
condition `n ≤ ℓ` is the complementary high-scale condition; together with
`n ≤ q` it bounds `n` by the logarithmic offset, so the discount supplies the
full `t q` gain. -/
theorem crudeBottom_lam_lower
    {d : ℕ} [NeZero d]
    {K C θ a t α : ℝ} {q r : ℕ} {j : Fin (q + 1)}
    (hK : 0 < K) (hC : 0 < C) (hθ : 0 < θ)
    (ha : 0 < a) (ht : 0 < t) (hαt : α < t) :
    let m : ℕ := q + r
    let n : ℕ := q - j.val
    let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let ℓ : ℕ :=
      Nat.ceil
        ((a * Real.log 3)⁻¹ *
          (Real.log (max (2 * K) 1) + x * Real.log 3))
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let scale : ℝ := K * (C * θ ^ (2 : ℕ))
    let T : ℝ := (3 : ℝ) ^ (-x)
    let lam : ℝ := T / scale
    let A : ℝ :=
      (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
        (K * C * θ ^ (2 : ℕ))
    let ρ : ℝ := (3 : ℝ) ^ (t - α)
    n ≤ ℓ → n < m → A * ρ ^ r ≤ lam := by
  intro m n x ℓ L scale T lam A ρ hnℓ hnm
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hL_nonneg : 0 ≤ L := by
    have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
    have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
      Real.log_nonneg (le_max_right (2 * K) 1)
    dsimp [L]
    positivity
  have hqm : q ≤ m := by
    dsimp [m]
    exact Nat.le_add_right q r
  have hnq : n ≤ q := by
    dsimp [n]
    exact Nat.sub_le q j.val
  have hceil :
      (ℓ : ℝ) ≤ L + max (x / a) 0 + 1 := by
    have hℓ_eq : ℓ = selectedBadPairScale K a t α q m n := by
      dsimp [ℓ, selectedBadPairScale, x]
    rw [hℓ_eq]
    simpa [L, x] using
      selectedBadPairScale_cast_le_logOffset
        (K := K) (a := a) (t := t) (α := α)
        (q := q) (m := m) (n := n) ha
  have hn_bound : (n : ℝ) ≤ L + 1 := by
    exact
      n_le_logOffset_add_one_of_not_high_n_le_q
        (a := a) (t := t) (α := α) (L := L)
        (q := q) (m := m) (n := n) (ℓ := ℓ)
        ha ht hαt (by simpa [x] using hceil) hnℓ hnq hqm
  have hj_le_q : j.val ≤ q := Nat.le_of_lt_succ j.isLt
  have hmq : m - q = r := by
    dsimp [m]
    exact Nat.add_sub_cancel_left q r
  have hmn : m - n = r + j.val := by
    dsimp [m, n]
    omega
  have hq_decomp :
      (q : ℝ) = (n : ℝ) + (j.val : ℝ) := by
    have hnat : n + j.val = q := by
      dsimp [n]
      exact Nat.sub_add_cancel hj_le_q
    exact_mod_cast hnat.symm
  have hx_neg_eq :
      -x = (t - α) * (r : ℝ) + t * (j.val : ℝ) := by
    dsimp [x]
    rw [hmq, hmn]
    norm_num [Nat.cast_add]
    ring
  have hj_gain :
      t * (q : ℝ) - t * (L + 1) ≤ t * (j.val : ℝ) := by
    rw [hq_decomp]
    have hn_mul : t * (n : ℝ) ≤ t * (L + 1) :=
      mul_le_mul_of_nonneg_left hn_bound ht.le
    calc
      t * ((n : ℝ) + (j.val : ℝ)) - t * (L + 1) =
          t * (j.val : ℝ) + (t * (n : ℝ) - t * (L + 1)) := by ring
      _ ≤ t * (j.val : ℝ) + 0 :=
          add_le_add le_rfl (sub_nonpos.mpr hn_mul)
      _ = t * (j.val : ℝ) := by ring
  have hexp_lower :
      t * (q : ℝ) - t * (L + 1) + (t - α) * (r : ℝ) ≤ -x := by
    rw [hx_neg_eq]
    calc
      t * (q : ℝ) - t * (L + 1) + (t - α) * (r : ℝ)
          ≤ t * (j.val : ℝ) + (t - α) * (r : ℝ) :=
        add_le_add hj_gain le_rfl
      _ = (t - α) * (r : ℝ) + t * (j.val : ℝ) := by ring
  have hden_pos : 0 < K * C * θ ^ (2 : ℕ) := by
    exact mul_pos (mul_pos hK hC) (pow_pos hθ 2)
  have hlam_eq :
      lam = (3 : ℝ) ^ (-x) / (K * C * θ ^ (2 : ℕ)) := by
    dsimp [lam, T, scale]
    ring
  have hpow_base :
      (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1) + (t - α) * (r : ℝ)) /
          (K * C * θ ^ (2 : ℕ))
        =
      A * ρ ^ r := by
    dsimp [A, ρ]
    have hrpow :=
      rpow_three_mul_rpow_pow_nat_eq
        (x := t * (q : ℝ) - t * (L + 1))
        (y := t - α) (r := r)
    calc
      (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1) + (t - α) * (r : ℝ)) /
          (K * C * θ ^ (2 : ℕ))
          =
        ((3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) *
            ((3 : ℝ) ^ (t - α)) ^ r) /
          (K * C * θ ^ (2 : ℕ)) := by
            rw [hrpow]
      _ =
        ((3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
          (K * C * θ ^ (2 : ℕ))) *
            ((3 : ℝ) ^ (t - α)) ^ r := by
            field_simp [hden_pos.ne']
  rw [hlam_eq, ← hpow_base]
  have hpow_le :
      (3 : ℝ) ^
          (t * (q : ℝ) - t * (L + 1) + (t - α) * (r : ℝ)) ≤
        (3 : ℝ) ^ (-x) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp_lower
  exact div_le_div_of_nonneg_right hpow_le hden_pos.le

/-- Concrete high-bottom row estimate from a fixed high-pair tail bound. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_of_badPair_bound
    {d : ℕ} [NeZero d] {σ Cfluct Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (hCfluct : 0 < Cfluct) (_hCentry : 0 < Centry) (ha : 0 < a)
    (hpair :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let ell : ℕ :=
          Nat.ceil
            ((a * Real.log 3)⁻¹ *
              (Real.log (max (2 * K) 1) + x * Real.log 3))
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let tau : ℝ := min σ 2
        let scale : ℝ :=
          Cfluct *
            (3 : ℝ) ^
              ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ)
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let lam : ℝ := T / (2 * K * scale)
        ell < n → n < m → q ≤ m → 1 ≤ lam →
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau)))) :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let c : ℝ :=
          min t
            (min b
              (min (t - αbad)
                (min (b - αbad)
                  (min ((t - αbad) * (1 + b / a))
                    (b - αbad * (1 + b / a))))))
        let τ : ℝ := min σ 2
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ c
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        1 ≤ A →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          ((S.card : ℝ) * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
  intro t αbad P hP hStruct hΓ hσ_eq hparams q r j
  dsimp only
  intro ht_pos hαt hαb hαharm hA_one
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ :=
    (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let c : ℝ :=
    min t
      (min b
        (min (t - αbad)
          (min (b - αbad)
            (min ((t - αbad) * (1 + b / a))
              (b - αbad * (1 + b / a))))))
  let τ : ℝ := min σ 2
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ :=
    (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
  let ρ : ℝ := (3 : ℝ) ^ c
  let m : ℕ := q + r
  let n : ℕ := q - j.val
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ℓ : ℕ :=
    Nat.ceil
      ((a * Real.log 3)⁻¹ *
        (Real.log (max (2 * K) 1) + x * Real.log 3))
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let scale : ℝ :=
    Cfluct *
      (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ℓ : ℕ) : ℝ)) *
      hΓ.thetaHat ^ (2 : ℕ)
  let T : ℝ := (3 : ℝ) ^ (-x)
  let lam : ℝ := T / (2 * K * scale)
  have hA_one_local : 1 ≤ A := by
    exact hA_one
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    have hta : 0 < t - αbad := sub_pos.mpr hαt
    have hba : 0 < b - αbad := sub_pos.mpr hαb
    have hone_ba : 0 < 1 + b / a := by positivity
    have hprod : 0 < (t - αbad) * (1 + b / a) :=
      mul_pos hta hone_ba
    have hharm : 0 < b - αbad * (1 + b / a) :=
      sub_pos.mpr hαharm
    positivity
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have hρ_gt : 1 < ρ := by
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ c :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hc_pos
  have hS_nonneg : 0 ≤ (S.card : ℝ) := by positivity
  have hA_nonneg : 0 ≤ A := by linarith [hA_one_local]
  have hAρ_nonneg : 0 ≤ A * ρ ^ r :=
    mul_nonneg hA_nonneg (pow_nonneg hρ_pos.le r)
  have htail_nonneg :
      0 ≤ ((S.card : ℝ) * w ^ q) *
        (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
    exact mul_nonneg
      (mul_nonneg hS_nonneg (pow_nonneg hw_pos.le q))
      (mul_nonneg (pow_nonneg hw_pos.le r) (Real.exp_pos _).le)
  by_cases hhigh : selectedBadPairScale K a t αbad q m n < n
  · by_cases hnm : n < m
    · have hℓ_eq : ℓ = selectedBadPairScale K a t αbad q m n := by
        dsimp [ℓ, selectedBadPairScale, x]
      have hℓn : ℓ < n := by
        simpa [hℓ_eq] using hhigh
      have hqm : q ≤ m := by
        dsimp [m]
        exact Nat.le_add_right q r
      have hraw :=
        hpair (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
          (q := q) (m := m) (n := n)
      dsimp only at hraw
      have hlam_lower : A * ρ ^ r ≤ lam := by
        exact
          highBottom_lam_lower
            (d := d) (K := K) (Cfluct := Cfluct)
            (θ := hΓ.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (r := r) (j := j)
            hK_pos hCfluct hΓ.thetaHat_pos ha ht_pos hαt hαb hαharm
            hℓn hnm
      have hρ_pow_one : 1 ≤ ρ ^ r :=
        one_le_pow₀ (le_of_lt hρ_gt)
      have hlam_one : 1 ≤ lam := by
        have hAρ_one : 1 ≤ A * ρ ^ r := by
          simpa using
            mul_le_mul hA_one_local hρ_pow_one
              (by norm_num : (0 : ℝ) ≤ 1) hA_nonneg
        exact hAρ_one.trans hlam_lower
      have hbad :
          P.real (badPairEvent Hshift t αbad q m n) ≤
            (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ τ))) := by
        exact hraw hℓn hnm hqm hlam_one
      have hD :
          (D.card : ℝ) ≤ w ^ q * w ^ r := by
        have hnm_le : n ≤ m := le_of_lt hnm
        simpa [D, w, m, n] using
          descendantsAtScale_bottom_row_card_le_weight
            (d := d) (N := N0) (q := q) (r := r) (j := j) hnm_le
      exact
        measureReal_highBottomPairEvent_le_weighted_row_of_badPair_bound
          (μ := P) (H := Hshift) (K := K) (a := a)
          (t := t) (α := αbad) (q := q) (m := m) (n := n)
          (r := r) (S := (S.card : ℝ)) (D := (D.card : ℝ))
          (A := A) (ρ := ρ) (τ := τ) (lam := lam) (w := w)
          hS_nonneg hw_pos.le hD hAρ_nonneg hlam_lower hτ_pos hbad
    · have hempty :
          highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [highBottomPairEvent, badPairEvent, hnm]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact htail_nonneg
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, hhigh]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact htail_nonneg

/-- Concrete high-bottom row estimate. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry a : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let c : ℝ :=
          min t
            (min b
              (min (t - αbad)
                (min (b - αbad)
                  (min ((t - αbad) * (1 + b / a))
                    (b - αbad * (1 + b / a))))))
        let τ : ℝ := min σ 2
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ c
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        1 ≤ A →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          ((S.card : ℝ) * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ))) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hpair⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  exact
    ⟨Cfluct, Centry, a, hCfluct, hCentry, ha,
      measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row_of_badPair_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Centry := Centry) (a := a)
        hσ_pos params hCfluct hCentry ha hpair⟩

/-- Concrete high-bottom component estimate obtained by summing a fixed
weighted row estimate. -/
theorem measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_row_bound
    {d : ℕ} [NeZero d] {σ Cfluct Centry a : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    (_hCfluct : 0 < Cfluct) (_hCentry : 0 < Centry) (_ha : 0 < a)
    (hrow :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q r : ℕ} {j : Fin (q + 1)},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let c : ℝ :=
          min t
            (min b
              (min (t - αbad)
                (min (b - αbad)
                  (min ((t - αbad) * (1 + b / a))
                    (b - αbad * (1 + b / a))))))
        let τ : ℝ := min σ 2
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ c
        let m : ℕ := q + r
        let n : ℕ := q - j.val
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        1 ≤ A →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          ((S.card : ℝ) * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ τ)))) :
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let c : ℝ :=
          min t
            (min b
              (min (t - αbad)
                (min (b - αbad)
                  (min ((t - αbad) * (1 + b / a))
                    (b - αbad * (1 + b / a))))))
        let τ : ℝ := min σ 2
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ c
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        1 ≤ A →
        P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            (Real.exp (-(A ^ τ)) *
              weightedGeometricExpKernelConst w (ρ ^ τ)) := by
  intro t αbad P hP hStruct hΓ hσ_eq hparams q
  dsimp only
  intro ht_pos hαt hαb hαharm hA_one
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ :=
    (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let c : ℝ :=
    min t
      (min b
        (min (t - αbad)
          (min (b - αbad)
            (min ((t - αbad) * (1 + b / a))
              (b - αbad * (1 + b / a))))))
  let τ : ℝ := min σ 2
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ :=
    (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
  let ρ : ℝ := (3 : ℝ) ^ c
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    have hta : 0 < t - αbad := sub_pos.mpr hαt
    have hba : 0 < b - αbad := sub_pos.mpr hαb
    have hone_ba : 0 < 1 + b / a := by positivity
    have hprod : 0 < (t - αbad) * (1 + b / a) :=
      mul_pos hta hone_ba
    have hharm : 0 < b - αbad * (1 + b / a) :=
      sub_pos.mpr hαharm
    positivity
  have hρ_gt : 1 < ρ := by
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ c :=
          Real.rpow_lt_rpow_of_exponent_lt
            (by norm_num : (1 : ℝ) < 3) hc_pos
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hC_nonneg : 0 ≤ (S.card : ℝ) * w ^ q := by
    positivity
  have hA_one_local : 1 ≤ A := by
    exact hA_one
  exact
    measureReal_highBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
      (μ := P) (H := Hshift) (K := K) (a := a)
      (t := t) (α := αbad) (q := q)
      (A := A) (ρ := ρ) (η := τ)
      (C := (S.card : ℝ) * w ^ q) (w := w)
      hC_nonneg hw_pos hA_one_local hρ_gt hτ_pos
      (by
        intro r j
        have hrow_inst :=
          hrow (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
            (q := q) (r := r) (j := j)
            ht_pos hαt hαb hαharm hA_one_local
        exact hrow_inst)

/-- Concrete high-bottom component estimate obtained by summing the weighted
row estimate. -/
theorem measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry a : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ :=
          (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let c : ℝ :=
          min t
            (min b
              (min (t - αbad)
                (min (b - αbad)
                  (min ((t - αbad) * (1 + b / a))
                    (b - αbad * (1 + b / a))))))
        let τ : ℝ := min σ 2
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let A : ℝ :=
          (3 : ℝ) ^ (c * (q : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let ρ : ℝ := (3 : ℝ) ^ c
        0 < t →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        1 ≤ A →
        P.real (highBottomBadScaleEvent Hshift K a t αbad q) ≤
          ((q + 1 : ℕ) : ℝ) * ((S.card : ℝ) * w ^ q) *
            (Real.exp (-(A ^ τ)) *
              weightedGeometricExpKernelConst w (ρ ^ τ)) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hrow⟩ :=
    measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_weighted_row
      (d := d) (σ := σ) hσ_pos params
  exact
    ⟨Cfluct, Centry, a, hCfluct, hCentry, ha,
      measureReal_shiftedHighBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel_of_row_bound
        (d := d) (σ := σ) (Cfluct := Cfluct) (Centry := Centry) (a := a)
        hσ_pos params hCfluct hCentry ha hrow⟩

end

end Section57
end Ch05
end Book
end Homogenization
