/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorControl

/-! # Homogenization Error Finite Q -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open Section54.VarianceBoundGoodScale
open scoped ENNReal MatrixOrder BigOperators

/-!
# Finite-q homogenization-error control

This file continues the Section 5.7 conversion from the localized quenched
`J` estimate to finite-`q` homogenization-error bounds.  The lemmas below are
the deterministic square-root step: a weighted `J` estimate at one scale gives
the corresponding `p = infinity` scale-response estimate with half the
discount exponent.
-/

noncomputable section

/-- If `3^{-τL} Y` is bounded by `R²`, then the square-root response gains the
factor `3^{τL/2}`. -/
theorem sqrt_mul_le_sqrt_mul_rpow_half_of_weighted_le
    {C Y R τ L : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hweighted :
      Real.rpow (3 : ℝ) (-τ * L) * Y ≤ R ^ (2 : ℕ)) :
    Real.sqrt (C * Y) ≤
      Real.sqrt C * Real.rpow (3 : ℝ) ((τ / 2) * L) * R := by
  let W : ℝ := Real.rpow (3 : ℝ) (-τ * L)
  let P : ℝ := Real.rpow (3 : ℝ) ((τ / 2) * L)
  have hW_pos : 0 < W := by
    dsimp [W]
    positivity
  have hW_inv : W⁻¹ = Real.rpow (3 : ℝ) (τ * L) := by
    dsimp [W]
    rw [show -τ * L = -(τ * L) by ring]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (τ * L)]
    rw [inv_inv]
  have hY_le : Y ≤ W⁻¹ * R ^ (2 : ℕ) :=
    (le_inv_mul_iff₀ hW_pos).mpr (by simpa [W] using hweighted)
  have hP_sq : P ^ (2 : ℕ) = Real.rpow (3 : ℝ) (τ * L) := by
    dsimp [P]
    have hpow₀ :
        Real.rpow (3 : ℝ) (((τ / 2) * L) * (2 : ℝ)) =
          Real.rpow (Real.rpow (3 : ℝ) ((τ / 2) * L)) (2 : ℝ) := by
      exact Real.rpow_mul (x := (3 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 3) ((τ / 2) * L) (2 : ℝ)
    have hpow :
        Real.rpow (3 : ℝ) (((τ / 2) * L) * (2 : ℝ)) =
          Real.rpow (3 : ℝ) ((τ / 2) * L) ^ (2 : ℕ) := by
      simpa [Real.rpow_two] using hpow₀
    calc
      Real.rpow (3 : ℝ) ((τ / 2) * L) ^ (2 : ℕ)
          = Real.rpow (3 : ℝ) (((τ / 2) * L) * (2 : ℝ)) := hpow.symm
      _ = Real.rpow (3 : ℝ) (τ * L) := by
          congr 1
          ring
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hrhs_nonneg :
      0 ≤ Real.sqrt C * P * R :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg C) hP_nonneg) hR
  refine (Real.sqrt_le_iff).2 ⟨hrhs_nonneg, ?_⟩
  calc
    C * Y ≤ C * (W⁻¹ * R ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hY_le hC
    _ = C * (Real.rpow (3 : ℝ) (τ * L) * R ^ (2 : ℕ)) := by
      rw [hW_inv]
    _ = (Real.sqrt C * P * R) ^ (2 : ℕ) := by
      rw [← hP_sq]
      have hCeq : (Real.sqrt C) ^ (2 : ℕ) = C := Real.sq_sqrt hC
      calc
        C * (P ^ (2 : ℕ) * R ^ (2 : ℕ))
            = (Real.sqrt C) ^ (2 : ℕ) * (P ^ (2 : ℕ) * R ^ (2 : ℕ)) := by
              rw [hCeq]
        _ = (Real.sqrt C * P * R) ^ (2 : ℕ) := by
              ring

/-- One-scale response control from the localized finite-probe maximum, after
using the weighted Section 5.7 estimate. -/
theorem scaleResponseAtScale_originCube_nat_le_rpow_of_weighted_localizedNormalizedProbeJMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℕ} (hnm : n ≤ m) {τ R : ℝ} (hR : 0 ≤ R)
    (hweighted :
      Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m n a ≤
        R ^ (2 : ℕ)) :
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        Ch02.MultiscaleExponent.infinity
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.sqrt
          (4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
        Real.rpow (3 : ℝ) ((τ / 2) * ((m - n : ℕ) : ℝ)) * R := by
  let Cprobe : ℝ :=
    4 * (Fintype.card (BlockCoord d) : ℝ) *
      (Fintype.card (NormalizedProbeIndex d) : ℝ)
  let Y : ℝ := localizedNormalizedProbeJMax hP hStruct m n a
  have hCprobe : 0 ≤ Cprobe := by
    dsimp [Cprobe]
    positivity
  have hscale :=
    scaleResponseAtScale_originCube_nat_le_sqrt_const_mul_localizedNormalizedProbeJMax
      hP hStruct hΓ ha hnm
  have hsqrt :
      Real.sqrt (Cprobe * Y) ≤
        Real.sqrt Cprobe *
          Real.rpow (3 : ℝ) ((τ / 2) * ((m - n : ℕ) : ℝ)) * R := by
    exact
      sqrt_mul_le_sqrt_mul_rpow_half_of_weighted_le
        (C := Cprobe) (Y := Y) (R := R) (τ := τ)
        (L := ((m - n : ℕ) : ℝ)) hCprobe hR
        (by simpa [Y] using hweighted)
  exact hscale.trans (by simpa [Cprobe, Y] using hsqrt)

/-- The same one-scale response control, using the unit-vector form supplied by
the minimal-scale theorem. -/
theorem scaleResponseAtScale_originCube_nat_le_rpow_of_weighted_localizedUnitJMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℕ} (hnm : n ≤ m) {τ R : ℝ} (hR : 0 ≤ R)
    (hunit : ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
      Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
          localizedLimitNormalizedJMax hP hStruct m n e a ≤
        R ^ (2 : ℕ)) :
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        Ch02.MultiscaleExponent.infinity
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.sqrt
          (4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
        Real.rpow (3 : ℝ) ((τ / 2) * ((m - n : ℕ) : ℝ)) * R := by
  let W : ℝ := Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ))
  have hW : 0 < W := by
    dsimp [W]
    positivity
  have hprobe :
      W * localizedNormalizedProbeJMax hP hStruct m n a ≤ R ^ (2 : ℕ) := by
    exact
      weighted_localizedNormalizedProbeJMax_le_of_forall_probe
        hP hStruct a hW
        (by
          intro i
          exact hunit (normalizedProbeVec i)
            (normalizedProbeVec_dotProduct_self_le_one i))
  exact
    scaleResponseAtScale_originCube_nat_le_rpow_of_weighted_localizedNormalizedProbeJMax
      hP hStruct hΓ ha hnm hR (by simpa [W] using hprobe)

/-- Natural lower-scale version of
`scaleResponseAtScale_originCube_nat_le_rpow_of_weighted_localizedUnitJMax`.
This is the form used in the finite-`q` row summation: the `l`-th term in
`\mathcal E(Q,n)` samples the scale `n-l`. -/
theorem scaleResponseAtScale_originCube_nat_sub_le_rpow_of_weighted_localizedUnitJMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n l : ℕ} (hln : l ≤ n) (hnm : n ≤ m) {τ R : ℝ} (hR : 0 ≤ R)
    (hunit : ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
      Real.rpow (3 : ℝ) (-τ * ((m - (n - l) : ℕ) : ℝ)) *
          localizedLimitNormalizedJMax hP hStruct m (n - l) e a ≤
        R ^ (2 : ℕ)) :
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
        ((n : ℤ) - (l : ℤ))
        Ch02.MultiscaleExponent.infinity
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.sqrt
          (4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
        Real.rpow (3 : ℝ) ((τ / 2) * ((m - (n - l) : ℕ) : ℝ)) * R := by
  have hcast : (((n - l : ℕ) : ℤ)) = (n : ℤ) - (l : ℤ) := by
    omega
  have hle : n - l ≤ m := by
    omega
  have hresp :=
    scaleResponseAtScale_originCube_nat_le_rpow_of_weighted_localizedUnitJMax
      hP hStruct hΓ ha hle hR hunit
  simpa [hcast] using hresp

/-- One natural lower-scale response estimate obtained by inserting the
minimal-scale envelope and taking a square root. -/
theorem scaleResponseAtScale_originCube_nat_sub_le_of_minimalScaleUnitJ
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n l : ℕ} (hln : l ≤ n) (hnm : n ≤ m)
    {τ X α : ℝ} (hX : 0 < X)
    (hunit : ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
      Real.rpow (3 : ℝ) (-τ * ((m - (n - l) : ℕ) : ℝ)) *
          localizedLimitNormalizedJMax hP hStruct m (n - l) e a ≤
        ((3 : ℝ) ^ m / X) ^ (-α)) :
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
        ((n : ℤ) - (l : ℤ))
        Ch02.MultiscaleExponent.infinity
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.sqrt
          (4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
        Real.rpow (3 : ℝ) ((τ / 2) * ((m - (n - l) : ℕ) : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))
  have hbase_pos : 0 < (3 : ℝ) ^ m / X := by
    exact div_pos (by positivity) hX
  have hD_nonneg : 0 ≤ ((3 : ℝ) ^ m / X) ^ (-α) :=
    (Real.rpow_pos_of_pos hbase_pos (-α)).le
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hunit_sq :
      ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
        Real.rpow (3 : ℝ) (-τ * ((m - (n - l) : ℕ) : ℝ)) *
            localizedLimitNormalizedJMax hP hStruct m (n - l) e a ≤
          R ^ (2 : ℕ) := by
    intro e he
    have h := hunit e he
    simpa [R, Real.sq_sqrt hD_nonneg] using h
  exact
    scaleResponseAtScale_originCube_nat_sub_le_rpow_of_weighted_localizedUnitJMax
      hP hStruct hΓ ha hln hnm hR_nonneg hunit_sq

/-- Natural-scale finite-row summation from the minimal-scale `J` estimate.

This controls the part of the finite-`q` homogenization-error series with
`l ≤ n`, i.e. the scales which are still nonnegative.  The closed
`\mathcal E` corollary absorbs the lower scales into the same minimal-scale
envelope before exposing a theorem statement. -/
theorem finset_sum_nat_scaleResponse_terms_le_of_minimalScaleUnitJ
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℕ} (hnm : n ≤ m)
    {r τ δ q X α : ℝ}
    (hδ : δ = r - τ / 2)
    (hrq : 0 ≤ r * q) (hδq : 0 < δ * q) (hq : 0 < q)
    (hX : 0 < X)
    (hunit : ∀ l : ℕ, l ≤ n →
      ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
        Real.rpow (3 : ℝ) (-τ * ((m - (n - l) : ℕ) : ℝ)) *
            localizedLimitNormalizedJMax hP hStruct m (n - l) e a ≤
          ((3 : ℝ) ^ m / X) ^ (-α)) :
    let Cresp : ℝ :=
      Real.sqrt
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
          (Fintype.card (NormalizedProbeIndex d) : ℝ));
    let A : ℝ :=
      Cresp * Real.rpow (3 : ℝ) ((τ / 2) * ((m - n : ℕ) : ℝ));
    let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α));
    Finset.sum (Finset.range (n + 1)) (fun l =>
        Ch02.geometricWeight r q l *
          Real.rpow
            (Ch02.scaleResponseAtScale
              (originCube d ((m : ℕ) : ℤ)) ((n : ℤ) - (l : ℤ))
              Ch02.MultiscaleExponent.infinity
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
              (scalarMatrix (d := d) (barSigmaLimit hP hStruct))) q) ≤
      Ch02.geometricDiscount r q *
        (Ch02.geometricDiscount δ q)⁻¹ *
        Real.rpow A q * Real.rpow R q := by
  classical
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let a0 : Mat d := scalarMatrix (d := d) (barSigmaLimit hP hStruct)
  let Cresp : ℝ :=
    Real.sqrt
      (4 * (Fintype.card (BlockCoord d) : ℝ) *
        (Fintype.card (NormalizedProbeIndex d) : ℝ))
  let A : ℝ :=
    Cresp * Real.rpow (3 : ℝ) ((τ / 2) * ((m - n : ℕ) : ℝ))
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))
  let B : ℝ :=
    Ch02.geometricDiscount r q *
      (Ch02.geometricDiscount δ q)⁻¹ *
      Real.rpow A q * Real.rpow R q
  let f : ℕ → ℝ := fun l =>
    Ch02.geometricWeight r q l *
      Real.rpow
        (Ch02.scaleResponseAtScale Q ((n : ℤ) - (l : ℤ))
          Ch02.MultiscaleExponent.infinity F a0) q
  let g : ℕ → ℝ := fun l => Ch02.geometricWeight δ q l * B
  have hnQ : ((n : ℕ) : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    exact_mod_cast hnm
  have hbase_pos : 0 < (3 : ℝ) ^ m / X := by
    exact div_pos (by positivity) hX
  have hD_nonneg : 0 ≤ ((3 : ℝ) ^ m / X) ^ (-α) :=
    (Real.rpow_pos_of_pos hbase_pos (-α)).le
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hCresp_nonneg : 0 ≤ Cresp := by
    dsimp [Cresp]
    positivity
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdisc_r_nonneg : 0 ≤ Ch02.geometricDiscount r q := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg hrq
  have hdisc_δ_pos : 0 < Ch02.geometricDiscount δ q := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos hδq
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hterm : ∀ l ∈ Finset.range (n + 1), f l ≤ g l := by
    intro l hl
    have hln : l ≤ n := by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hdiff :
        ((m - (n - l) : ℕ) : ℝ) =
          ((m - n : ℕ) : ℝ) + (l : ℝ) := by
      have hnat : m - (n - l) = (m - n) + l := by
        omega
      exact_mod_cast hnat
    have hpow_split :
        Real.rpow (3 : ℝ) ((τ / 2) * ((m - (n - l) : ℕ) : ℝ)) =
          Real.rpow (3 : ℝ) ((τ / 2) * ((m - n : ℕ) : ℝ)) *
            Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) := by
      rw [hdiff]
      rw [show (τ / 2) * (((m - n : ℕ) : ℝ) + (l : ℝ)) =
          (τ / 2) * ((m - n : ℕ) : ℝ) + (τ / 2) * (l : ℝ) by ring]
      exact Real.rpow_add (by norm_num : (0 : ℝ) < 3)
        ((τ / 2) * ((m - n : ℕ) : ℝ)) ((τ / 2) * (l : ℝ))
    have hscale_raw :=
      scaleResponseAtScale_originCube_nat_sub_le_of_minimalScaleUnitJ
        hP hStruct hΓ ha hln hnm hX (hunit l hln)
    have hscale :
        Ch02.scaleResponseAtScale Q ((n : ℤ) - (l : ℤ))
            Ch02.MultiscaleExponent.infinity F a0 ≤
          A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
      calc
        Ch02.scaleResponseAtScale Q ((n : ℤ) - (l : ℤ))
            Ch02.MultiscaleExponent.infinity F a0
            ≤ Cresp *
                Real.rpow (3 : ℝ)
                  ((τ / 2) * ((m - (n - l) : ℕ) : ℝ)) * R := by
                simpa [Q, F, a0, Cresp, R] using hscale_raw
        _ = A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                rw [hpow_split]
                dsimp [A]
                ring
    simpa [f, g, Q, F, a0, B] using
      weighted_scaleResponse_term_le_of_scaleResponse_le
        (Q := Q) (n := ((n : ℕ) : ℤ)) hnQ F a0
        (r := r) (tau := τ) (delta := δ) (q := q)
        (A := A) (R := R) (l := l)
        hδ hrq hδq hq hA_nonneg hR_nonneg hscale
  have hg_nonneg : ∀ l : ℕ, 0 ≤ g l := by
    intro l
    exact mul_nonneg
      (by
        simpa [Ch02.geometricWeight_eq_old] using
          Homogenization.geometricWeight_nonneg
            (s := δ) (q := q) l hδq.le)
      hB_nonneg
  have hg_summable : Summable g := by
    have hbase :
        Summable (fun l : ℕ => Homogenization.geometricWeight δ q l) :=
      Homogenization.summable_geometricWeight hδq
    have hscaled :
        Summable (fun l : ℕ =>
          B * Homogenization.geometricWeight δ q l) :=
      hbase.mul_left B
    simpa [g, Ch02.geometricWeight_eq_old, mul_comm, mul_left_comm, mul_assoc]
      using hscaled
  have hsum_g_le_tsum :
      Finset.sum (Finset.range (n + 1)) (fun l => g l) ≤ ∑' l : ℕ, g l :=
    hg_summable.sum_le_tsum (Finset.range (n + 1))
      (fun l _hl => hg_nonneg l)
  have htsum_g : (∑' l : ℕ, g l) = B := by
    have hbase :
        Summable (fun l : ℕ => Homogenization.geometricWeight δ q l) :=
      Homogenization.summable_geometricWeight hδq
    calc
      (∑' l : ℕ, g l)
          = ∑' l : ℕ, B * Homogenization.geometricWeight δ q l := by
              simp [g, Ch02.geometricWeight_eq_old, mul_comm]
      _ = B * ∑' l : ℕ, Homogenization.geometricWeight δ q l := by
              simpa using hbase.tsum_mul_left B
      _ = B := by
              rw [Homogenization.tsum_geometricWeight_eq_one hδq]
              ring
  calc
    Finset.sum (Finset.range (n + 1)) (fun l => f l)
        ≤ Finset.sum (Finset.range (n + 1)) (fun l => g l) :=
          Finset.sum_le_sum hterm
    _ ≤ ∑' l : ℕ, g l := hsum_g_le_tsum
    _ = B := htsum_g

end

end Section57
end Ch05
end Book
end Homogenization
