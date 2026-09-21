/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Full
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2
import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.DualToCircLoss.FiniteLoss
import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.NegativeBesovLocalize

/-! # Duality Exponent Loss -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Exponent-loss Besov bridge

This file contains the pure function-space exponent-loss bridge used by the
sharp-boundary scalar duality path.  It consumes the Chapter 1 legacy
finite-truncation, totalized-real, disjoint/componentwise compatibility lane;
it is not an exact `ENNReal` source-norm bridge.
-/

/-- Geometric singular factor for the embedding
`B^{-t}_{2,2,dual} -> B^{-s}_{2,2,circ}`.

The projection-test proof has singularities both at `t = 0` and at `s = t`.
This is definitionally the coefficient proved in Chapter 1's pure Besov
dual-to-circ bridge, repeated in the root namespace so deterministic theorem
surfaces do not mention book-facing names. -/
noncomputable def besovExponentLossGap (s t : ℝ) : ℝ :=
  (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
    (2 * (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
      (1 - Real.rpow (3 : ℝ) (-(s - t)))⁻¹

theorem besovExponentLossGap_nonneg {s t : ℝ} (ht : 0 < t) (hts : t < s) :
    0 ≤ besovExponentLossGap s t := by
  have hs : 0 < s := lt_trans ht hts
  have hst : 0 < s - t := sub_pos.mpr hts
  have hs_lt_one :
      Real.rpow (3 : ℝ) (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have ht_lt_one :
      Real.rpow (3 : ℝ) (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hst_lt_one :
      Real.rpow (3 : ℝ) (-(s - t)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  unfold besovExponentLossGap
  exact add_nonneg
    (inv_nonneg.mpr (sub_nonneg.mpr hs_lt_one.le))
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (sub_nonneg.mpr ht_lt_one.le)))
      (inv_nonneg.mpr (sub_nonneg.mpr hst_lt_one.le)))

/-- Half-exponent specialization of the geometric gap.  This is the
one-parameter loss used when the downstream theorem exposes only the larger
output exponent `s` and measures the localized flux defect at `s / 2`. -/
theorem besovExponentLossGap_half_le_fiftyFive_inv_sq {s : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) :
    besovExponentLossGap s (s / 2) ≤ 55 * (s⁻¹) ^ (2 : ℕ) := by
  simpa [besovExponentLossGap, Book.Ch01.Legacy.dualToCircGeometricLossCoefficient]
    using
      Book.Ch01.Legacy.dualToCircGeometricLossCoefficient_half_le_fiftyFive_inv_sq
        hs hs_lt.le

/-- A zero-trace potential field has the `L²` membership supplied by its
`H¹₀` primitive.  This local copy avoids importing the Ch1 public theorem layer
into the deterministic black-box namespace. -/
theorem memVectorL2_of_isPotentialZeroTraceOn
    {d : ℕ} {U : Set (Vec d)} {w : Vec d → Vec d}
    (hw : IsPotentialZeroTraceOn U w) :
    MemVectorL2 U w := by
  rcases hw with ⟨u, hgrad⟩
  simpa [hgrad] using u.toH1Function.grad_memVectorL2

private theorem cubeBesovConjExponent_two_eq_dualityExponentLoss :
    cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

private theorem cubeBesovConjExponent_two_ne_zero_dualityExponentLoss :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
  rw [cubeBesovConjExponent_two_eq_dualityExponentLoss]
  norm_num

private theorem cubeBesovConjExponent_two_ne_top_dualityExponentLoss :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [cubeBesovConjExponent_two_eq_dualityExponentLoss]
  norm_num

/-- Root-namespace version of the note-normalized vector genuine dual negative
Besov norm.  This matches the Chapter 3 public definition but lives in the
deterministic black-box layer to avoid a reverse dependency on the book-facing
namespace. -/
noncomputable def cubeScaleNormalizedDualNegativeBesovVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  cubeBesovScaleWeight s Q *
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x => F x i)

theorem cubeScaleNormalizedDualNegativeBesovVectorNormTwo_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    0 ≤ cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F := by
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  refine mul_nonneg (cubeBesovScaleWeight_nonneg s Q) ?_
  exact Finset.sum_nonneg fun i _hi =>
    cubeBesovDualFullNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (fun x => F x i)
      cubeBesovConjExponent_two_ne_zero_dualityExponentLoss
      cubeBesovConjExponent_two_ne_top_dualityExponentLoss

/-- Localized descendant `ℓ²` average of note-normalized vector genuine-dual
negative Besov norms. -/
noncomputable def localizedScaleNormalizedDualNegativeBesovVectorAverageTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.sqrt <|
    descendantsAverage Q j fun R =>
      (cubeScaleNormalizedDualNegativeBesovVectorNormTwo R s F) ^ 2

theorem localizedScaleNormalizedDualNegativeBesovVectorAverageTwo_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q s F j := by
  unfold localizedScaleNormalizedDualNegativeBesovVectorAverageTwo
  exact Real.sqrt_nonneg _

private theorem cubeBesovScaleWeight_mul_component_localizedDualAverage_le
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) (i : Fin d) :
    cubeBesovScaleWeight s Q *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x => F x i)) ^ 2) ≤
      localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q s F j := by
  classical
  let wQ : ℝ := cubeBesovScaleWeight s Q
  let a : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  have hwQ_nonneg : 0 ≤ wQ := by
    dsimp [wQ]
    exact cubeBesovScaleWeight_nonneg s Q
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have havg_nonneg :
      0 ≤ descendantsAverage Q j fun R =>
        (a * cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x => F x i)) ^ 2 := by
    exact descendantsAverage_nonneg Q j _ fun R _hR => sq_nonneg _
  unfold localizedScaleNormalizedDualNegativeBesovVectorAverageTwo
  refine Real.le_sqrt_of_sq_le ?_
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        wQ ^ 2 *
            (a * cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F x i)) ^ 2 ≤
          (cubeScaleNormalizedDualNegativeBesovVectorNormTwo R s F) ^ 2 := by
    intro R hR
    have hscale :
        cubeBesovScaleWeight s R = wQ * a := by
      dsimp [wQ, a]
      exact cubeBesovScaleWeight_eq_mul_rpow_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) s hR
    have hdual_nonneg :
        ∀ k : Fin d,
          0 ≤ cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x k) := by
      intro k
      exact cubeBesovDualFullNorm_nonneg R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x => F x k)
        cubeBesovConjExponent_two_ne_zero_dualityExponentLoss
        cubeBesovConjExponent_two_ne_top_dualityExponentLoss
    have hsingle :
        cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i) ≤
          ∑ k : Fin d,
            cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F x k) :=
      Finset.single_le_sum (fun k _hk => hdual_nonneg k) (Finset.mem_univ i)
    have hleft_nonneg :
        0 ≤ wQ * a *
          cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i) := by
      exact mul_nonneg (mul_nonneg hwQ_nonneg ha_nonneg) (hdual_nonneg i)
    have hleft_le :
        wQ * a *
            cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F x i) ≤
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo R s F := by
      unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
      rw [hscale]
      exact mul_le_mul_of_nonneg_left hsingle (mul_nonneg hwQ_nonneg ha_nonneg)
    calc
      wQ ^ 2 *
          (a * cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i)) ^ 2 =
        (wQ * a *
          cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i)) ^ 2 := by
          ring
      _ ≤ (cubeScaleNormalizedDualNegativeBesovVectorNormTwo R s F) ^ 2 :=
        pow_le_pow_left₀ hleft_nonneg hleft_le 2
  calc
    (wQ *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (a * cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F x i)) ^ 2)) ^ 2
        =
      wQ ^ 2 *
        (Real.sqrt
          (descendantsAverage Q j fun R =>
            (a * cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F x i)) ^ 2)) ^ 2 := by
        ring
    _ =
      wQ ^ 2 *
        descendantsAverage Q j (fun R =>
          (a * cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i)) ^ 2) := by
        rw [Real.sq_sqrt havg_nonneg]
    _ =
      descendantsAverage Q j (fun R =>
        wQ ^ 2 *
          (a * cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i)) ^ 2) := by
        rw [descendantsAverage_mul_left]
    _ ≤
      descendantsAverage Q j fun R =>
        (cubeScaleNormalizedDualNegativeBesovVectorNormTwo R s F) ^ 2 :=
        descendantsAverage_le_descendantsAverage Q j hpoint

/-- Componentwise Ch1 negative localization, repackaged for the deterministic
note-normalized vector full-dual norm. -/
theorem cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul_negativeBesovLocalizeConstant_mul_localizedAverage
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ)
    (hs : 0 < s)
    (hF : MemVectorL2 (cubeSet Q) F) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F ≤
      (Fintype.card (Fin d) : ℝ) * Book.Ch01.Legacy.negativeBesovLocalizeConstant d *
        localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q s F j := by
  classical
  let C : ℝ := Book.Ch01.Legacy.negativeBesovLocalizeConstant d
  let L : ℝ := localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q s F j
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, Book.Ch01.Legacy.negativeBesovLocalizeConstant]
    norm_num
  have hwQ_nonneg : 0 ≤ cubeBesovScaleWeight s Q :=
    cubeBesovScaleWeight_nonneg s Q
  have hcomp :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
    Book.Ch01.Legacy.component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1
      Q hF
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  calc
    cubeBesovScaleWeight s Q *
        ∑ i : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i)
        =
      ∑ i : Fin d,
        cubeBesovScaleWeight s Q *
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i) := by
        rw [Finset.mul_sum]
    _ ≤
      ∑ _i : Fin d, C * L := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        let S : ℝ :=
          Real.sqrt
            (descendantsAverage Q j fun R =>
              (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
                cubeBesovDualFullNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                  (fun x => F x i)) ^ 2)
        have hscalar :
            cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x => F x i) ≤
              C * S := by
          dsimp [C, S]
          simpa [Book.Ch01.Legacy.dualNegativeBesovNorm] using
            Book.Ch01.Legacy.negativeBesovFullLocalize_of_memLp
              Q s (fun x => F x i) j hs (hcomp i)
        have hlocal :
            cubeBesovScaleWeight s Q * S ≤ L := by
          dsimp [S, L]
          exact cubeBesovScaleWeight_mul_component_localizedDualAverage_le
            Q s F j i
        calc
          cubeBesovScaleWeight s Q *
              cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                (fun x => F x i)
              ≤ cubeBesovScaleWeight s Q * (C * S) :=
                mul_le_mul_of_nonneg_left hscalar hwQ_nonneg
          _ = C * (cubeBesovScaleWeight s Q * S) := by
                ring
          _ ≤ C * L :=
                mul_le_mul_of_nonneg_left hlocal hC_nonneg
    _ =
      (Fintype.card (Fin d) : ℝ) * Book.Ch01.Legacy.negativeBesovLocalizeConstant d *
        localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q s F j := by
        dsimp [C, L]
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Pure function-space bridge: concrete/circ negative Besov at the larger
exponent `s` is controlled by genuine dual negative Besov at the smaller
exponent `t`. -/
def ConcreteNegativeFromDualExponentLoss
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) (F : Vec d → Vec d) {s t : ℝ},
      0 < t →
      t < s →
      s < 1 →
      MemVectorL2 (cubeSet Q) F →
      cubeBesovNegativeVectorSeminormTwo Q s F ≤
        C * besovExponentLossGap s t *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t F

/-- The pure Chapter 1 dual-to-circ theorem realizes the deterministic
exponent-loss bridge with unit prefactor. -/
theorem concreteNegativeFromDualExponentLoss_geometric
    (d : ℕ) [NeZero d] :
    ConcreteNegativeFromDualExponentLoss d 1 := by
  refine ⟨by norm_num, ?_⟩
  intro Q F s t ht hts _hs_lt_one hF
  have hs : 0 < s := lt_trans ht hts
  have hcomp :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
    Book.Ch01.Legacy.component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1
      Q hF
  have h :=
    Book.Ch01.Legacy.cubeBesovNegativeVectorSeminormTwo_le_dualToCircGeometricLossCoefficient_mul_normalizedDual
      Q F hs ht hts hcomp
  simpa [besovExponentLossGap, cubeScaleNormalizedDualNegativeBesovVectorNormTwo,
    Book.Ch01.Legacy.dualToCircGeometricLossCoefficient,
    Book.Ch01.Legacy.normalizedDualNegativeBesovVectorNormTwo,
    Book.Ch01.Legacy.dualNegativeBesovNorm] using h

/-- Localized concrete/circ consequence of the exponent-loss bridge and Ch1
negative Besov localization.

This is the downstream-facing form: the parent concrete negative Besov seminorm
is controlled by the descendant RMS of note-normalized vector full-dual norms at
the lower exponent. -/
theorem cubeBesovNegativeVectorSeminormTwo_le_localizedDualAverage_exponentLoss
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (F : Vec d → Vec d)
    {s t : ℝ} (j : ℕ)
    (ht : 0 < t) (hts : t < s) (hs_lt_one : s < 1)
    (hF : MemVectorL2 (cubeSet Q) F) :
    cubeBesovNegativeVectorSeminormTwo Q s F ≤
      ((Fintype.card (Fin d) : ℝ) * Book.Ch01.Legacy.negativeBesovLocalizeConstant d) *
        besovExponentLossGap s t *
          localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q t F j := by
  have hdual :=
    (concreteNegativeFromDualExponentLoss_geometric d).2 Q F ht hts hs_lt_one hF
  have hlocalized :=
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul_negativeBesovLocalizeConstant_mul_localizedAverage
      Q t F j ht hF
  have hgap_nonneg : 0 ≤ besovExponentLossGap s t :=
    besovExponentLossGap_nonneg ht hts
  calc
    cubeBesovNegativeVectorSeminormTwo Q s F
        ≤
          1 * besovExponentLossGap s t *
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t F := hdual
    _ =
          besovExponentLossGap s t *
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t F := by
            ring
    _ ≤
          besovExponentLossGap s t *
            ((Fintype.card (Fin d) : ℝ) * Book.Ch01.Legacy.negativeBesovLocalizeConstant d *
              localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q t F j) :=
            mul_le_mul_of_nonneg_left hlocalized hgap_nonneg
    _ =
          ((Fintype.card (Fin d) : ℝ) * Book.Ch01.Legacy.negativeBesovLocalizeConstant d) *
            besovExponentLossGap s t *
              localizedScaleNormalizedDualNegativeBesovVectorAverageTwo Q t F j := by
            ring


end

end Homogenization
