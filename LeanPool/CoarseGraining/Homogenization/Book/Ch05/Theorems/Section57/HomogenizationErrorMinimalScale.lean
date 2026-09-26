/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorClosed
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorLowerEnvelope
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticity

/-! # Homogenization Error Minimal Scale -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal MatrixOrder BigOperators

/-!
# Minimal-scale finite-q homogenization-error assembly

This file contains the deterministic bridge used in the Section 5.7 corollary:
pointwise localized `J` control and pointwise unit-ellipticity control imply a
single collapsed bound on `\mathcal E_{r,\infty,q}`.
-/

noncomputable section

/-- Increasing the random scale weakens the collapsed algebraic factor. -/
private theorem collapsed_algebraic_factor_le_of_le
    {m : ℕ} {X Y α : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hα : 0 ≤ α) :
    ((3 : ℝ) ^ m / X) ^ (-α) ≤ ((3 : ℝ) ^ m / Y) ^ (-α) := by
  have hY : 0 < Y := hX.trans_le hXY
  have hbaseX_pos : 0 < (3 : ℝ) ^ m / X := div_pos (by positivity) hX
  have hbaseY_pos : 0 < (3 : ℝ) ^ m / Y := div_pos (by positivity) hY
  have hbase_le : (3 : ℝ) ^ m / Y ≤ (3 : ℝ) ^ m / X := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv : Y⁻¹ ≤ X⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hX hXY
    exact mul_le_mul_of_nonneg_left
      hinv (by positivity)
  by_cases hα0 : α = 0
  · simp [hα0]
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    exact
      (Real.rpow_le_rpow_iff_of_neg hbaseX_pos hbaseY_pos
        (by linarith : (-α : ℝ) < 0)).2 hbase_le

/-- Increasing the random scale weakens the square-root envelope used in the
unit-ellipticity rows. -/
private theorem collapsed_square_envelope_le_of_le
    {m : ℕ} {X Y α s : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hα : 0 ≤ α) :
    (Real.rpow (3 : ℝ) (s * (m : ℝ)) *
        Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))) ^ (2 : ℕ) ≤
      (Real.rpow (3 : ℝ) (s * (m : ℝ)) *
        Real.sqrt (((3 : ℝ) ^ m / Y) ^ (-α))) ^ (2 : ℕ) := by
  have hfactor :=
    collapsed_algebraic_factor_le_of_le
      (m := m) (X := X) (Y := Y) (α := α) hX hXY hα
  have hleft_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (s * (m : ℝ)) *
        Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
    exact mul_nonneg
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      (Real.sqrt_nonneg _)
  have hmul :
      Real.rpow (3 : ℝ) (s * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) ≤
        Real.rpow (3 : ℝ) (s * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / Y) ^ (-α)) := by
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hfactor)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  exact pow_le_pow_left₀ hleft_nonneg hmul 2

/-- Whole-cube finite-`q` homogenization-error control from one random scale
which controls both the positive-scale `J` rows and the negative-scale
unit-ellipticity rows. -/
theorem homogenizationErrorOnOriginCube_le_of_minimalScaleUnitJ_and_unitEllipticity
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m : ℕ} {r τ δ q X α : ℝ}
    (hδ : δ = r - τ / 2)
    (hτ : 0 < τ) (hrq : 0 ≤ r * q) (hδq : 0 < δ * q) (hq : 0 < q)
    (hUpper : hΓ.params.sUpper < τ / 2)
    (hLower : hΓ.params.sLower < τ / 2)
    (hX : 0 < X)
    (hJ : ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
      ∀ {n : ℕ},
        X ≤ (3 : ℝ) ^ m →
        n < m →
        Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
            localizedLimitNormalizedJMax hP hStruct m n e a ≤
          ((3 : ℝ) ^ m / X) ^ (-α))
    (hUnit :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))) ^ (2 : ℕ))
    (hScale : X ≤ (3 : ℝ) ^ m) :
    let Cresp : ℝ :=
      Real.sqrt
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
          (Fintype.card (NormalizedProbeIndex d) : ℝ));
    let Cneg : ℝ :=
      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
        (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
    Ch02.HomogenizationErrorOnCube (originCube d ((m : ℕ) : ℤ)) r
        Ch02.MultiscaleExponent.infinity (.finite q)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.rpow
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount δ q)⁻¹)
          (1 / q) *
        A * Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
  classical
  intro Cresp Cneg A
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let σbar : ℝ := barSigmaLimit hP hStruct
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))
  have hτ2_pos : 0 < τ / 2 := by positivity
  have hσbar_pos : 0 < σbar := by
    simpa [σbar] using hΓ.barSigmaLimit_pos
  have hbase_pos : 0 < (3 : ℝ) ^ m / X :=
    div_pos (by positivity) hX
  have hD_nonneg : 0 ≤ ((3 : ℝ) ^ m / X) ^ (-α) :=
    (Real.rpow_pos_of_pos hbase_pos (-α)).le
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hCresp_nonneg : 0 ≤ Cresp := by
    dsimp [Cresp]
    positivity
  have hdiscτ_pos : 0 < Ch02.geometricDiscount (τ / 2) 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos (s := τ / 2) (q := 1)
        (by simpa using hτ2_pos)
  have hCneg_nonneg : 0 ≤ Cneg := by
    dsimp [Cneg]
    positivity
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA_ge_resp : Cresp ≤ A := by
    dsimp [A]
    have hpow_one : 1 ≤ Real.rpow (3 : ℝ) (τ / 2) :=
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hτ2_pos.le
    calc
      Cresp ≤ max Cresp Cneg := le_max_left _ _
      _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) := by
        have hmax_nonneg : 0 ≤ max Cresp Cneg :=
          le_max_of_le_left hCresp_nonneg
        calc
          max Cresp Cneg = max Cresp Cneg * 1 := by ring
          _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) :=
            mul_le_mul_of_nonneg_left hpow_one hmax_nonneg
  have hA_ge_neg : Cneg ≤ A := by
    dsimp [A]
    have hpow_one : 1 ≤ Real.rpow (3 : ℝ) (τ / 2) :=
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hτ2_pos.le
    calc
      Cneg ≤ max Cresp Cneg := le_max_right _ _
      _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) := by
        have hmax_nonneg : 0 ≤ max Cresp Cneg :=
          le_max_of_le_right hCneg_nonneg
        calc
          max Cresp Cneg = max Cresp Cneg * 1 := by ring
          _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) :=
            mul_le_mul_of_nonneg_left hpow_one hmax_nonneg
  have hA_ge_resp_step :
      Cresp * Real.rpow (3 : ℝ) (τ / 2) ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_max_left Cresp Cneg)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hA_ge_neg_step :
      Cneg * Real.rpow (3 : ℝ) (τ / 2) ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_max_right Cresp Cneg)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hell :=
    scaleZero_ellipticity_sup_bounds_of_localizedLimitWeightedUnitEllipticitySup_le
      hP hStruct hΓ ha (m := m) (t := τ / 2)
      (M := Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) * R)
      hUpper hLower (by simpa [R] using hUnit)
  have hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
          (((m : ℕ) : ℤ) - (l : ℤ))
          Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) ≤
        A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
    intro l
    by_cases hl0 : l = 0
    · subst l
      by_cases hm0 : m = 0
      · subst m
        have hself :
            Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (0 : ℤ)
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) ≤
            Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (-(1 : ℤ))
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) := by
          exact
            Ch02.scaleResponseAtScale_infinity_self_le
              (Q := originCube d (0 : ℤ)) (k := -(1 : ℤ))
              (by simp [originCube]) F (scalarMatrix (d := d) σbar)
        have hneg_weighted :=
          weighted_negative_scaleResponse_le_of_scaleZero_collapsed
            (d := d) 0 1 (s := τ / 2) (σ := σbar) (R := R)
            hτ2_pos hσbar_pos hR_nonneg F
            (by simpa [F, σbar] using hell.1)
            (by simpa [F, σbar] using hell.2)
        have hneg :=
          negative_scaleResponse_le_of_weighted_envelope
            (d := d) 0 1 (s := τ / 2) (σ := σbar)
            (A := 2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
            (R := R) hτ2_pos (by positivity) hR_nonneg F hneg_weighted
        calc
          Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (0 : ℤ)
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              ≤ Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (-(1 : ℤ))
                  Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) :=
                hself
          _ ≤ Cneg * Real.rpow (3 : ℝ) (τ / 2) * R := by
                simpa [Cneg, Nat.cast_one] using hneg
          _ ≤ A * R := by
                exact mul_le_mul_of_nonneg_right hA_ge_neg_step hR_nonneg
          _ = A * Real.rpow (3 : ℝ) ((τ / 2) * (((0 : ℕ) : ℝ))) * R := by
                norm_num
      · have hm_pos : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
        have hself :
            Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) ≤
              Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
                (((m : ℕ) : ℤ) - (1 : ℤ))
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) := by
          exact
            Ch02.scaleResponseAtScale_infinity_self_le
              (Q := originCube d ((m : ℕ) : ℤ))
              (k := ((m : ℕ) : ℤ) - (1 : ℤ))
              (by simp [originCube]) F (scalarMatrix (d := d) σbar)
        have hresp :=
          scaleResponseAtScale_originCube_nat_sub_le_of_minimalScaleUnitJ
            hP hStruct hΓ ha (m := m) (n := m) (l := 1)
            hm_pos le_rfl hX
            (by
              intro e he
              exact hJ e he hScale (by omega))
        have hdiff : ((m - (m - 1) : ℕ) : ℝ) = (1 : ℝ) := by
          exact_mod_cast (by omega : m - (m - 1) = 1)
        calc
          Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              ≤ Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
                  (((m : ℕ) : ℤ) - (1 : ℤ))
                  Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) :=
                hself
          _ ≤ Cresp * Real.rpow (3 : ℝ) (τ / 2) * R := by
                simpa [F, σbar, Cresp, R, hdiff, Nat.cast_one] using hresp
          _ ≤ A * R := by
                exact mul_le_mul_of_nonneg_right hA_ge_resp_step hR_nonneg
          _ = A * Real.rpow (3 : ℝ) ((τ / 2) * (((0 : ℕ) : ℝ))) * R := by
                norm_num
    · by_cases hlm : l ≤ m
      · have hl_pos : 1 ≤ l := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hl0)
        have hresp :=
          scaleResponseAtScale_originCube_nat_sub_le_of_minimalScaleUnitJ
            hP hStruct hΓ ha (m := m) (n := m) (l := l)
            hlm le_rfl hX
            (by
              intro e he
              exact hJ e he hScale (by omega))
        have hdiff : ((m - (m - l) : ℕ) : ℝ) = (l : ℝ) := by
          exact_mod_cast (by omega : m - (m - l) = l)
        calc
          Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
              (((m : ℕ) : ℤ) - (l : ℤ))
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              ≤ Cresp * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                simpa [F, σbar, Cresp, R, hdiff] using hresp
          _ ≤ A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hA_ge_resp
                    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le)
                  hR_nonneg
      · let j : ℕ := l - m
        have hj_pos : 0 < j := by
          dsimp [j]
          omega
        have hl_eq : l = j + m := by
          dsimp [j]
          omega
        have hk_eq : ((m : ℕ) : ℤ) - (l : ℤ) = -((j : ℕ) : ℤ) := by
          dsimp [j]
          omega
        have hneg_weighted :=
          weighted_negative_scaleResponse_le_of_scaleZero_collapsed
            (d := d) m j (s := τ / 2) (σ := σbar) (R := R)
            hτ2_pos hσbar_pos hR_nonneg F
            (by simpa [F, σbar] using hell.1)
            (by simpa [F, σbar] using hell.2)
        have hneg :=
          negative_scaleResponse_le_of_weighted_envelope
            (d := d) m j (s := τ / 2) (σ := σbar)
            (A := 2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
            (R := R) hτ2_pos (by positivity) hR_nonneg F hneg_weighted
        calc
          Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
              (((m : ℕ) : ℤ) - (l : ℤ))
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              =
            Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ))
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) := by
                rw [hk_eq]
          _ ≤ Cneg * Real.rpow (3 : ℝ) ((τ / 2) * ((j + m : ℕ) : ℝ)) * R := by
                simpa [Cneg] using hneg
          _ = Cneg * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                rw [hl_eq]
          _ ≤ A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hA_ge_neg
                    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le)
                  hR_nonneg
  exact
    homogenizationErrorOnOriginCube_le_of_scaleResponseMinimalEnvelope
      (d := d) (m := m) F (scalarMatrix (d := d) σbar)
      (r := r) (tau := τ) (delta := δ) (q := q)
      (A := A) (X := X) (alpha := α)
      hδ hrq hδq hq hA_nonneg hX hscale

/-- Natural lower-scale response estimate obtained from the finite normalized
probe maximum and the minimal-scale envelope. -/
theorem scaleResponseAtScale_originCube_nat_sub_le_of_minimalScaleProbeJ
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n l : ℕ} (hln : l ≤ n) (hnm : n ≤ m)
    {τ X α : ℝ} (hX : 0 < X)
    (hprobe :
      Real.rpow (3 : ℝ) (-τ * ((m - (n - l) : ℕ) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m (n - l) a ≤
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
  have hprobe_sq :
      Real.rpow (3 : ℝ) (-τ * ((m - (n - l) : ℕ) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m (n - l) a ≤
        R ^ (2 : ℕ) := by
    simpa [R, Real.sq_sqrt hD_nonneg] using hprobe
  have hcast : (((n - l : ℕ) : ℤ)) = (n : ℤ) - (l : ℤ) := by
    omega
  have hle : n - l ≤ m := by
    omega
  have hresp :=
    scaleResponseAtScale_originCube_nat_le_rpow_of_weighted_localizedNormalizedProbeJMax
      hP hStruct hΓ ha hle hR_nonneg hprobe_sq
  simpa [hcast] using hresp

/-- Whole-cube finite-`q` homogenization-error control from positive-scale
response rows and the negative-scale unit-ellipticity envelope. -/
theorem homogenizationErrorOnOriginCube_le_of_positiveScaleResponses_and_unitEllipticity
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m : ℕ} {r τ δ q X α : ℝ}
    (hδ : δ = r - τ / 2)
    (hτ : 0 < τ) (hrq : 0 ≤ r * q) (hδq : 0 < δ * q) (hq : 0 < q)
    (hUpper : hΓ.params.sUpper < τ / 2)
    (hLower : hΓ.params.sLower < τ / 2)
    (hX : 0 < X)
    (hPos :
      ∀ {l : ℕ}, 1 ≤ l → l ≤ m →
        Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
            (((m : ℕ) : ℤ) - (l : ℤ))
            Ch02.MultiscaleExponent.infinity
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
            (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
          Real.sqrt
              (4 * (Fintype.card (BlockCoord d) : ℝ) *
                (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
            Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) *
              Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)))
    (hUnit :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))) ^ (2 : ℕ)) :
    let Cresp : ℝ :=
      Real.sqrt
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
          (Fintype.card (NormalizedProbeIndex d) : ℝ));
    let Cneg : ℝ :=
      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
        (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
    Ch02.HomogenizationErrorOnCube (originCube d ((m : ℕ) : ℤ)) r
        Ch02.MultiscaleExponent.infinity (.finite q)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.rpow
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount δ q)⁻¹)
          (1 / q) *
        A * Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
  classical
  intro Cresp Cneg A
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let σbar : ℝ := barSigmaLimit hP hStruct
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))
  have hτ2_pos : 0 < τ / 2 := by positivity
  have hσbar_pos : 0 < σbar := by
    simpa [σbar] using hΓ.barSigmaLimit_pos
  have hbase_pos : 0 < (3 : ℝ) ^ m / X :=
    div_pos (by positivity) hX
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hCresp_nonneg : 0 ≤ Cresp := by
    dsimp [Cresp]
    positivity
  have hdiscτ_pos : 0 < Ch02.geometricDiscount (τ / 2) 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos (s := τ / 2) (q := 1)
        (by simpa using hτ2_pos)
  have hCneg_nonneg : 0 ≤ Cneg := by
    dsimp [Cneg]
    positivity
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA_ge_resp : Cresp ≤ A := by
    dsimp [A]
    have hpow_one : 1 ≤ Real.rpow (3 : ℝ) (τ / 2) :=
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hτ2_pos.le
    calc
      Cresp ≤ max Cresp Cneg := le_max_left _ _
      _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) := by
        have hmax_nonneg : 0 ≤ max Cresp Cneg :=
          le_max_of_le_left hCresp_nonneg
        calc
          max Cresp Cneg = max Cresp Cneg * 1 := by ring
          _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) :=
            mul_le_mul_of_nonneg_left hpow_one hmax_nonneg
  have hA_ge_neg : Cneg ≤ A := by
    dsimp [A]
    have hpow_one : 1 ≤ Real.rpow (3 : ℝ) (τ / 2) :=
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hτ2_pos.le
    calc
      Cneg ≤ max Cresp Cneg := le_max_right _ _
      _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) := by
        have hmax_nonneg : 0 ≤ max Cresp Cneg :=
          le_max_of_le_right hCneg_nonneg
        calc
          max Cresp Cneg = max Cresp Cneg * 1 := by ring
          _ ≤ max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2) :=
            mul_le_mul_of_nonneg_left hpow_one hmax_nonneg
  have hA_ge_resp_step :
      Cresp * Real.rpow (3 : ℝ) (τ / 2) ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_max_left Cresp Cneg)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hA_ge_neg_step :
      Cneg * Real.rpow (3 : ℝ) (τ / 2) ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_max_right Cresp Cneg)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hell :=
    scaleZero_ellipticity_sup_bounds_of_localizedLimitWeightedUnitEllipticitySup_le
      hP hStruct hΓ ha (m := m) (t := τ / 2)
      (M := Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) * R)
      hUpper hLower (by simpa [R] using hUnit)
  have hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
          (((m : ℕ) : ℤ) - (l : ℤ))
          Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) ≤
        A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
    intro l
    by_cases hl0 : l = 0
    · subst l
      by_cases hm0 : m = 0
      · subst m
        have hself :
            Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (0 : ℤ)
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) ≤
            Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (-(1 : ℤ))
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) := by
          exact
            Ch02.scaleResponseAtScale_infinity_self_le
              (Q := originCube d (0 : ℤ)) (k := -(1 : ℤ))
              (by simp [originCube]) F (scalarMatrix (d := d) σbar)
        have hneg_weighted :=
          weighted_negative_scaleResponse_le_of_scaleZero_collapsed
            (d := d) 0 1 (s := τ / 2) (σ := σbar) (R := R)
            hτ2_pos hσbar_pos hR_nonneg F
            (by simpa [F, σbar] using hell.1)
            (by simpa [F, σbar] using hell.2)
        have hneg :=
          negative_scaleResponse_le_of_weighted_envelope
            (d := d) 0 1 (s := τ / 2) (σ := σbar)
            (A := 2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
            (R := R) hτ2_pos (by positivity) hR_nonneg F hneg_weighted
        calc
          Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (0 : ℤ)
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              ≤ Ch02.scaleResponseAtScale (originCube d (0 : ℤ)) (-(1 : ℤ))
                  Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) :=
                hself
          _ ≤ Cneg * Real.rpow (3 : ℝ) (τ / 2) * R := by
                simpa [Cneg, Nat.cast_one] using hneg
          _ ≤ A * R := by
                exact mul_le_mul_of_nonneg_right hA_ge_neg_step hR_nonneg
          _ = A * Real.rpow (3 : ℝ) ((τ / 2) * (((0 : ℕ) : ℝ))) * R := by
                norm_num
      · have hm_pos : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
        have hself :
            Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) ≤
              Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
                (((m : ℕ) : ℤ) - (1 : ℤ))
                Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) := by
          exact
            Ch02.scaleResponseAtScale_infinity_self_le
              (Q := originCube d ((m : ℕ) : ℤ))
              (k := ((m : ℕ) : ℤ) - (1 : ℤ))
              (by simp [originCube]) F (scalarMatrix (d := d) σbar)
        have hresp := hPos (l := 1) (by omega) hm_pos
        calc
          Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((m : ℕ) : ℤ)
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              ≤ Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
                  (((m : ℕ) : ℤ) - (1 : ℤ))
                  Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) :=
                hself
          _ ≤ Cresp * Real.rpow (3 : ℝ) (τ / 2) * R := by
                simpa [F, σbar, Cresp, R, Nat.cast_one] using hresp
          _ ≤ A * R := by
                exact mul_le_mul_of_nonneg_right hA_ge_resp_step hR_nonneg
          _ = A * Real.rpow (3 : ℝ) ((τ / 2) * (((0 : ℕ) : ℝ))) * R := by
                norm_num
    · by_cases hlm : l ≤ m
      · have hl_pos : 1 ≤ l := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hl0)
        have hresp := hPos (l := l) hl_pos hlm
        calc
          Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
              (((m : ℕ) : ℤ) - (l : ℤ))
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              ≤ Cresp * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                simpa [F, σbar, Cresp, R] using hresp
          _ ≤ A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hA_ge_resp
                    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le)
                  hR_nonneg
      · let j : ℕ := l - m
        have hj_pos : 0 < j := by
          dsimp [j]
          omega
        have hl_eq : l = j + m := by
          dsimp [j]
          omega
        have hk_eq : ((m : ℕ) : ℤ) - (l : ℤ) = -((j : ℕ) : ℤ) := by
          dsimp [j]
          omega
        have hneg_weighted :=
          weighted_negative_scaleResponse_le_of_scaleZero_collapsed
            (d := d) m j (s := τ / 2) (σ := σbar) (R := R)
            hτ2_pos hσbar_pos hR_nonneg F
            (by simpa [F, σbar] using hell.1)
            (by simpa [F, σbar] using hell.2)
        have hneg :=
          negative_scaleResponse_le_of_weighted_envelope
            (d := d) m j (s := τ / 2) (σ := σbar)
            (A := 2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
            (R := R) hτ2_pos (by positivity) hR_nonneg F hneg_weighted
        calc
          Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
              (((m : ℕ) : ℤ) - (l : ℤ))
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar)
              =
            Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ))
              Ch02.MultiscaleExponent.infinity F (scalarMatrix (d := d) σbar) := by
                rw [hk_eq]
          _ ≤ Cneg * Real.rpow (3 : ℝ) ((τ / 2) * ((j + m : ℕ) : ℝ)) * R := by
                simpa [Cneg] using hneg
          _ = Cneg * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                rw [hl_eq]
          _ ≤ A * Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) * R := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hA_ge_neg
                    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le)
                  hR_nonneg
  exact
    homogenizationErrorOnOriginCube_le_of_scaleResponseMinimalEnvelope
      (d := d) (m := m) F (scalarMatrix (d := d) σbar)
      (r := r) (tau := τ) (delta := δ) (q := q)
      (A := A) (X := X) (alpha := α)
      hδ hrq hδq hq hA_nonneg hX hscale

/-- Whole-cube finite-`q` homogenization-error control from one random scale
which controls the positive finite-probe `J` rows and the negative-scale
unit-ellipticity rows. -/
theorem homogenizationErrorOnOriginCube_le_of_minimalScaleProbeJ_and_unitEllipticity
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m : ℕ} {r τ δ q X α : ℝ}
    (hδ : δ = r - τ / 2)
    (hτ : 0 < τ) (hrq : 0 ≤ r * q) (hδq : 0 < δ * q) (hq : 0 < q)
    (hUpper : hΓ.params.sUpper < τ / 2)
    (hLower : hΓ.params.sLower < τ / 2)
    (hX : 0 < X)
    (hProbe :
      ∀ {n : ℕ},
        X ≤ (3 : ℝ) ^ m →
        n < m →
        Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
            localizedNormalizedProbeJMax hP hStruct m n a ≤
          ((3 : ℝ) ^ m / X) ^ (-α))
    (hUnit :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))) ^ (2 : ℕ))
    (hScale : X ≤ (3 : ℝ) ^ m) :
    let Cresp : ℝ :=
      Real.sqrt
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
          (Fintype.card (NormalizedProbeIndex d) : ℝ));
    let Cneg : ℝ :=
      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
        (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
    Ch02.HomogenizationErrorOnCube (originCube d ((m : ℕ) : ℤ)) r
        Ch02.MultiscaleExponent.infinity (.finite q)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.rpow
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount δ q)⁻¹)
          (1 / q) *
        A * Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
  intro Cresp Cneg A
  have hPos :
      ∀ {l : ℕ}, 1 ≤ l → l ≤ m →
        Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
            (((m : ℕ) : ℤ) - (l : ℤ))
            Ch02.MultiscaleExponent.infinity
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
            (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
          Real.sqrt
              (4 * (Fintype.card (BlockCoord d) : ℝ) *
                (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
            Real.rpow (3 : ℝ) ((τ / 2) * (l : ℝ)) *
              Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
    intro l hl_pos hlm
    have hprobe :
        Real.rpow (3 : ℝ) (-τ * ((m - (m - l) : ℕ) : ℝ)) *
            localizedNormalizedProbeJMax hP hStruct m (m - l) a ≤
          ((3 : ℝ) ^ m / X) ^ (-α) := by
      exact hProbe hScale (by omega)
    have hresp :=
      scaleResponseAtScale_originCube_nat_sub_le_of_minimalScaleProbeJ
        hP hStruct hΓ ha (m := m) (n := m) (l := l)
        hlm le_rfl hX hprobe
    have hdiff : ((m - (m - l) : ℕ) : ℝ) = (l : ℝ) := by
      exact_mod_cast (by omega : m - (m - l) = l)
    simpa [Cresp, hdiff] using hresp
  simpa [Cresp, Cneg, A] using
    homogenizationErrorOnOriginCube_le_of_positiveScaleResponses_and_unitEllipticity
      hP hStruct hΓ ha (m := m) (r := r) (τ := τ) (δ := δ)
      (q := q) (X := X) (α := α)
      hδ hτ hrq hδq hq hUpper hLower hX hPos hUnit

/-- Same deterministic assembly with separate pointwise scales for the finite
probe `J` rows and the unit-ellipticity rows.  The exposed bound uses the
single collapsed scale `max XJ XU`. -/
theorem homogenizationErrorOnOriginCube_le_of_two_minimalScales_probeJ
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m : ℕ} {r τ δ q XJ XU α : ℝ}
    (hδ : δ = r - τ / 2)
    (hτ : 0 < τ) (hrq : 0 ≤ r * q) (hδq : 0 < δ * q) (hq : 0 < q)
    (hUpper : hΓ.params.sUpper < τ / 2)
    (hLower : hΓ.params.sLower < τ / 2)
    (hα : 0 ≤ α)
    (hXJ : 0 < XJ) (hXU : 0 < XU)
    (hProbe :
      ∀ {n : ℕ},
        XJ ≤ (3 : ℝ) ^ m →
        n < m →
        Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
            localizedNormalizedProbeJMax hP hStruct m n a ≤
          ((3 : ℝ) ^ m / XJ) ^ (-α))
    (hUnit :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / XU) ^ (-α))) ^ (2 : ℕ))
    (hScale : max XJ XU ≤ (3 : ℝ) ^ m) :
    let X : ℝ := max XJ XU;
    let Cresp : ℝ :=
      Real.sqrt
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
          (Fintype.card (NormalizedProbeIndex d) : ℝ));
    let Cneg : ℝ :=
      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
        (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
    Ch02.HomogenizationErrorOnCube (originCube d ((m : ℕ) : ℤ)) r
        Ch02.MultiscaleExponent.infinity (.finite q)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.rpow
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount δ q)⁻¹)
          (1 / q) *
        A * Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
  intro X Cresp Cneg A
  have hX : 0 < X := by
    dsimp [X]
    exact hXJ.trans_le (le_max_left XJ XU)
  have hProbe_lift :
      ∀ {n : ℕ},
        X ≤ (3 : ℝ) ^ m →
        n < m →
        Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
            localizedNormalizedProbeJMax hP hStruct m n a ≤
          ((3 : ℝ) ^ m / X) ^ (-α) := by
    intro n hXm hnm
    have hraw := hProbe (le_trans (le_max_left XJ XU) hXm) hnm
    exact hraw.trans
      (by
        simpa [X] using
          collapsed_algebraic_factor_le_of_le
            (m := m) (X := XJ) (Y := X) (α := α)
            hXJ (by dsimp [X]; exact le_max_left XJ XU) hα)
  have hUnit_lift :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))) ^ (2 : ℕ) := by
    exact hUnit.trans
      (by
        simpa [X] using
          collapsed_square_envelope_le_of_le
            (m := m) (X := XU) (Y := X) (α := α) (s := τ / 2)
            hXU (by dsimp [X]; exact le_max_right XJ XU) hα)
  simpa [X, Cresp, Cneg, A] using
    homogenizationErrorOnOriginCube_le_of_minimalScaleProbeJ_and_unitEllipticity
      hP hStruct hΓ ha (m := m) (r := r) (τ := τ) (δ := δ)
      (q := q) (X := X) (α := α)
      hδ hτ hrq hδq hq hUpper hLower hX hProbe_lift hUnit_lift
      (by simpa [X] using hScale)

/-- Same deterministic assembly with separate pointwise scales for the `J`
rows and the unit-ellipticity rows.  The exposed bound uses the single
collapsed scale `max XJ XU`. -/
theorem homogenizationErrorOnOriginCube_le_of_two_minimalScales
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m : ℕ} {r τ δ q XJ XU α : ℝ}
    (hδ : δ = r - τ / 2)
    (hτ : 0 < τ) (hrq : 0 ≤ r * q) (hδq : 0 < δ * q) (hq : 0 < q)
    (hUpper : hΓ.params.sUpper < τ / 2)
    (hLower : hΓ.params.sLower < τ / 2)
    (hα : 0 ≤ α)
    (hXJ : 0 < XJ) (hXU : 0 < XU)
    (hJ : ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
      ∀ {n : ℕ},
        XJ ≤ (3 : ℝ) ^ m →
        n < m →
        Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
            localizedLimitNormalizedJMax hP hStruct m n e a ≤
          ((3 : ℝ) ^ m / XJ) ^ (-α))
    (hUnit :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / XU) ^ (-α))) ^ (2 : ℕ))
    (hScale : max XJ XU ≤ (3 : ℝ) ^ m) :
    let X : ℝ := max XJ XU;
    let Cresp : ℝ :=
      Real.sqrt
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
          (Fintype.card (NormalizedProbeIndex d) : ℝ));
    let Cneg : ℝ :=
      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
        (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
    Ch02.HomogenizationErrorOnCube (originCube d ((m : ℕ) : ℤ)) r
        Ch02.MultiscaleExponent.infinity (.finite q)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.rpow
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount δ q)⁻¹)
          (1 / q) *
        A * Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α)) := by
  intro X Cresp Cneg A
  have hX : 0 < X := by
    dsimp [X]
    exact hXJ.trans_le (le_max_left XJ XU)
  have hJ_lift :
      ∀ e : FullBlockVec d, dotProduct e e ≤ 1 →
        ∀ {n : ℕ},
          X ≤ (3 : ℝ) ^ m →
          n < m →
          Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
              localizedLimitNormalizedJMax hP hStruct m n e a ≤
            ((3 : ℝ) ^ m / X) ^ (-α) := by
    intro e he n hXm hnm
    have hraw :=
      hJ e he (le_trans (le_max_left XJ XU) hXm) hnm
    exact hraw.trans
      (by
        simpa [X] using
          collapsed_algebraic_factor_le_of_le
            (m := m) (X := XJ) (Y := X) (α := α)
            hXJ (by dsimp [X]; exact le_max_left XJ XU) hα)
  have hUnit_lift :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m a ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-α))) ^ (2 : ℕ) := by
    exact hUnit.trans
      (by
        simpa [X] using
          collapsed_square_envelope_le_of_le
            (m := m) (X := XU) (Y := X) (α := α) (s := τ / 2)
            hXU (by dsimp [X]; exact le_max_right XJ XU) hα)
  simpa [X, Cresp, Cneg, A] using
    homogenizationErrorOnOriginCube_le_of_minimalScaleUnitJ_and_unitEllipticity
      hP hStruct hΓ ha (m := m) (r := r) (τ := τ) (δ := δ)
      (q := q) (X := X) (α := α)
      hδ hτ hrq hδq hq hUpper hLower hX hJ_lift hUnit_lift
      (by simpa [X] using hScale)

end

end Section57
end Ch05
end Book
end Homogenization
