/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectNormalization
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPStoppingPositiveClosure

/-!
# Direct quadratic estimate in the p-stopping one-node interface

This module normalizes the independent root averages, applies the checked
direct quadratic maximal-tail estimate to the active good collection, and
restores the original scales by exact homogeneity.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectPStopping

open HardyLittlewoodSparseReduction
open FiniteLaminarMaximalSparse
open KrauseLaceyPStoppingPositiveClosure KrauseLaceyPStoppingRecursion
open KrauseLaceyQuadraticDirectAction KrauseLaceyQuadraticDirectLowPairing
open KrauseLaceyQuadraticDirectNormalization
open KrauseLaceyQuadraticDirectRootLocalization
open KrauseLaceyStoppingExtraction KrauseLaceyStoppingRecursion
open KrauseLaceyThreeShiftGrid


noncomputable section

/-- The universal extended-nonnegative coefficient remaining after the
normalized offset summation. -/
def directQuadraticNormalizedCoefficient : ℝ≥0∞ :=
  (directQuadraticTailEnergyConstant 10) ^ (1 / 2 : ℝ) +
    ENNReal.ofReal (8 * positiveDyadicAmplitudeBound) +
    ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * 10 * 10)

/-- A real one-node constant suitable for the existing sparse-recursion
interface. -/
def directQuadraticOneNodeConstant : ℝ :=
  20 * directQuadraticNormalizedCoefficient.toReal

theorem directQuadraticNormalizedCoefficient_ne_top :
    directQuadraticNormalizedCoefficient ≠ ∞ := by
  unfold directQuadraticNormalizedCoefficient directQuadraticTailEnergyConstant
  finiteness

theorem directQuadraticOneNodeConstant_nonneg :
    0 ≤ directQuadraticOneNodeConstant := by
  exact mul_nonneg (by norm_num) ENNReal.toReal_nonneg

theorem ofReal_directQuadraticOneNodeConstant :
    ENNReal.ofReal directQuadraticOneNodeConstant =
      20 * directQuadraticNormalizedCoefficient := by
  unfold directQuadraticOneNodeConstant
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20),
    ENNReal.ofReal_toReal directQuadraticNormalizedCoefficient_ne_top]
  norm_num

/-- Every integer-valued label on a finite collection has a natural strict
upper bound. -/
theorem exists_nat_strictUpperBound_finset_int
    (S : Finset RealInterval) (scale : RealInterval → ℤ) :
    ∃ N : ℕ, ∀ I ∈ S, scale I < N := by
  classical
  refine ⟨(∑ I ∈ S, (scale I).natAbs) + 1, ?_⟩
  intro I hI
  have habs : (scale I).natAbs ≤ ∑ J ∈ S, (scale J).natAbs := by
    exact Finset.single_le_sum (s := S) (f := fun J ↦ (scale J).natAbs)
      (fun J hJ ↦ Nat.zero_le _) hI
  have hle : scale I ≤ ((scale I).natAbs : ℤ) := Int.le_natAbs
  have hlt : ((scale I).natAbs : ℤ) <
      (((∑ J ∈ S, (scale J).natAbs) + 1 : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_succ_of_le habs
  exact hle.trans_lt hlt

/-- A localized quadratic piece depends only on the almost-everywhere class
of its input.  Translation of the exceptional null set is justified by
Lebesgue invariance. -/
theorem krauseLaceyLocalizedPiece_congr_ae
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g)
    (j : ℤ) (I : RealInterval) (x : ℝ) :
    krauseLaceyLocalizedPiece 1 j I f x =
      krauseLaceyLocalizedPiece 1 j I g x := by
  unfold krauseLaceyLocalizedPiece
  apply integral_congr_ae
  have hshift :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae hfg
  filter_upwards [hshift] with y hy
  by_cases hmem : x - y ∈ I.centralThird
  · simp only [Set.indicator_of_mem hmem, hy]
  · simp only [Set.indicator_of_notMem hmem]

/-- The localized maximal tail also depends only on the almost-everywhere
class of its input. -/
theorem localizedTailMaximal_congr_ae
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g)
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (x : ℝ) :
    localizedTailMaximal ell₀ scale S f x =
      localizedTailMaximal ell₀ scale S g x := by
  classical
  apply iSup_congr
  intro ell
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hlen : (2 : ℝ) ^ ell.1 ≤ I.length
  · simp only [localizedTailAction, hlen, if_pos]
    exact krauseLaceyLocalizedPiece_congr_ae hfg (scale I) I x
  · simp [hlen]

theorem localizedTailMaximal_zero
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (x : ℝ) :
    localizedTailMaximal ell₀ scale S (0 : ℝ → ℂ) x = 0 := by
  classical
  simp [localizedTailMaximal, localizedTailAction,
    krauseLaceyLocalizedPiece]

/-- A zero positive local `L^p` average means that the function vanishes
almost everywhere on that interval.  The conclusion is phrased using the
root restriction needed by the direct quadratic estimate. -/
theorem intervalRestrictionL0Infinity_ae_eq_zero_of_localAverage_eq_zero
    (g : L0Infinity) (I : RealInterval) {p : ℝ} (hp : 0 < p)
    (havg : localAverage p g I = 0) :
    (intervalRestrictionL0Infinity g I : ℝ → ℂ) =ᵐ[volume] 0 := by
  have hmassNonneg :
      0 ≤ ∫ x in I.carrier, ‖g x‖ ^ p :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hbaseNonneg :
      0 ≤ I.length⁻¹ * ∫ x in I.carrier, ‖g x‖ ^ p :=
    mul_nonneg (inv_nonneg.mpr I.length_pos.le) hmassNonneg
  have hbase : I.length⁻¹ * ∫ x in I.carrier, ‖g x‖ ^ p = 0 := by
    exact (Real.rpow_eq_zero hbaseNonneg (one_div_ne_zero hp.ne')).mp havg
  have hmass : ∫ x in I.carrier, ‖g x‖ ^ p = 0 := by
    exact (mul_eq_zero.mp hbase).resolve_left (inv_ne_zero I.length_pos.ne')
  have hpowzero :
      (fun x ↦ ‖g x‖ ^ p) =ᵐ[volume.restrict I.carrier] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
      ((KrauseLaceyQuadraticDirectExceptionalPairing.L0Infinity.integrable_norm_rpow_direct
        g hp).integrableOn)).mp hmass
  have hgzero : (g : ℝ → ℂ) =ᵐ[volume.restrict I.carrier] 0 := by
    filter_upwards [hpowzero] with x hx
    have hnorm : ‖g x‖ = 0 :=
      (Real.rpow_eq_zero (norm_nonneg _) hp.ne').mp hx
    exact norm_eq_zero.mp hnorm
  change I.carrier.indicator g =ᵐ[volume] 0
  exact indicator_ae_eq_zero_of_restrict_ae_eq_zero
    I.measurableSet_carrier hgzero

/-- If the root `L¹` average vanishes, every localized descendant tail is
identically zero. -/
theorem localizedTailMaximal_eq_zero_of_rootAverage_eq_zero
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (f : L0Infinity) (I : RealInterval)
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier)
    (havg : localAverage 1 f I = 0) (x : ℝ) :
    localizedTailMaximal ell₀ scale S f x = 0 := by
  have hrestrict :=
    intervalRestrictionL0Infinity_ae_eq_zero_of_localAverage_eq_zero
      f I zero_lt_one havg
  calc
    localizedTailMaximal ell₀ scale S f x =
        localizedTailMaximal ell₀ scale S
          (intervalRestrictionL0Infinity f I) x := by
      symm
      exact localizedTailMaximal_indicator_parent ell₀ scale S f I hsub x
    _ = localizedTailMaximal ell₀ scale S (0 : ℝ → ℂ) x :=
      localizedTailMaximal_congr_ae hrestrict ell₀ scale S x
    _ = 0 := localizedTailMaximal_zero ell₀ scale S x

/-- The checked direct quadratic estimate supplies the required one-node
pairing whenever the two root averages are positive. -/
theorem pStopping_good_part_pairing_directQuadratic_of_pos_averages
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (I : RealInterval) (f g : L0Infinity)
    (hell : 3 ≤ ell₀)
    (hS : S ⊆ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hI : I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier)
    (ha : 0 < localAverage 1 f I) (hb : 0 < localAverage p g I) :
    (∫⁻ x, localizedTailMaximal ell₀ (finiteShiftGridScale topScale shift)
      (goodCollection S f
        (pStoppingMonitor g p (lt_trans zero_lt_one hp)) I) f x * ‖g x‖ₑ) ≤
      ENNReal.ofReal
          (directQuadraticOneNodeConstant * holderConjugate p) *
        pStoppingSparseAtom p f g I := by
  classical
  let scale := finiteShiftGridScale topScale shift
  let monitor := pStoppingMonitor g p (lt_trans zero_lt_one hp)
  let T := goodCollection S f monitor I
  let A := activeHighCollection ell₀ T
  let a := localAverage 1 f I
  let b := localAverage p g I
  let f₀ := L0Infinity.smul ((a⁻¹ : ℝ) : ℂ) f
  let g₀ := L0Infinity.smul ((b⁻¹ : ℝ) : ℂ) g
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hTS : T ⊆ S := by
    intro J hJ
    exact (Finset.mem_filter.mp hJ).1
  have hAT : A ⊆ T := Finset.filter_subset _ T
  have hAS : A ⊆ S := hAT.trans hTS
  have hscaleS : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2) := by
    intro J hJ
    exact completeFiniteShiftGridTree_length_eq_scale
      topScale shift maxDepth q₀ J (hS hJ)
  have hscaleA : ∀ J ∈ A, J.length = (2 : ℝ) ^ (scale J + 2) := by
    intro J hJ
    exact hscaleS J (hAS hJ)
  have hscaleT : ∀ J ∈ T, J.length = (2 : ℝ) ^ (scale J + 2) := by
    intro J hJ
    exact hscaleS J (hTS hJ)
  have hsubA : ∀ J ∈ A, J.carrier ⊆ I.carrier := by
    intro J hJ
    exact hsub J (hAS hJ)
  have hlamA : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨
        Disjoint J.carrier K.carrier :=
    (completeFiniteShiftGridTree_laminar
      topScale shift maxDepth q₀).mono (hAS.trans hS)
  have hscaleNonneg : ∀ J ∈ A, 0 ≤ scale J := by
    intro J hJ
    have hcut : ell₀ ≤ scale J + 2 :=
      scale_add_two_ge_cutoff_of_mem_activeHighCollection hscaleT hJ
    omega
  obtain ⟨N, hbound⟩ := exists_nat_strictUpperBound_finset_int A scale
  have hfavgA : ∀ J ∈ A, intervalL1Average f₀ J ≤ 10 := by
    intro J hJ
    have hgood := (goodCollection_averages_le hsub (hAT hJ)).1
    rw [← localAverage_one_eq_intervalL1Average,
      localAverage_smul a⁻¹ (inv_pos.mpr ha') f J 1 zero_lt_one]
    rw [inv_mul_le_iff₀ ha']
    simpa only [a, localAverage_one_eq_intervalL1Average, mul_comm] using hgood
  have hmassA : ∀ J ∈ A,
      (∫ x in J.carrier, ‖f₀ x‖) ≤ 10 * J.length := by
    intro J hJ
    rw [← intervalL1Average_mul_length]
    exact mul_le_mul_of_nonneg_right (hfavgA J hJ) J.length_pos.le
  have hfroot : (∫ x in I.carrier, ‖f₀ x‖) ≤ I.length := by
    rw [← intervalL1Average_mul_length]
    have havg : intervalL1Average f₀ I = 1 := by
      rw [← localAverage_one_eq_intervalL1Average,
        localAverage_smul a⁻¹ (inv_pos.mpr ha') f I 1 zero_lt_one]
      exact inv_mul_cancel₀ ha'.ne'
    rw [havg, one_mul]
  have hpowCancel : b⁻¹ ^ p * b ^ p = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.mpr hb'.le) hb'.le,
      inv_mul_cancel₀ hb'.ne', Real.one_rpow]
  have hgmassA : ∀ J ∈ A,
      (∫ x in J.carrier, ‖g₀ x‖ ^ p) ≤ 10 * J.length := by
    intro J hJ
    have hgood := goodCollection_pMass_le g hp0 hsub (hAT hJ)
    rw [intervalL1Average_pStoppingMonitor_eq_localAverage_rpow] at hgood
    calc
      (∫ x in J.carrier, ‖g₀ x‖ ^ p) =
          b⁻¹ ^ p * ∫ x in J.carrier, ‖g x‖ ^ p :=
        by simpa only [g₀] using
          integral_norm_rpow_smul b⁻¹ (inv_pos.mpr hb').le g J p
      _ ≤ b⁻¹ ^ p * ((10 * b ^ p) * J.length) :=
        mul_le_mul_of_nonneg_left (by simpa only [b] using hgood)
          (Real.rpow_nonneg (inv_nonneg.mpr hb'.le) p)
      _ = 10 * J.length := by rw [show b⁻¹ ^ p * ((10 * b ^ p) * J.length) =
          10 * (b⁻¹ ^ p * b ^ p) * J.length by ring, hpowCancel, mul_one]
  have hgavgA : ∀ J ∈ A, intervalL1Average g₀ J ≤ 10 := by
    intro J hJ
    have hbase : J.length⁻¹ * ∫ x in J.carrier, ‖g₀ x‖ ^ p ≤ 10 := by
      calc
        J.length⁻¹ * ∫ x in J.carrier, ‖g₀ x‖ ^ p ≤
            J.length⁻¹ * (10 * J.length) :=
          mul_le_mul_of_nonneg_left (hgmassA J hJ)
            (inv_nonneg.mpr J.length_pos.le)
        _ = 10 := by field_simp [J.length_pos.ne']
    have hpinv0 : 0 ≤ 1 / p := one_div_nonneg.mpr hp0.le
    have hpinv1 : 1 / p ≤ 1 := (div_le_one hp0).2 hp.le
    calc
      intervalL1Average g₀ J = localAverage 1 g₀ J :=
        (localAverage_one_eq_intervalL1Average g₀ J).symm
      _ ≤ localAverage p g₀ J := localAverage_one_le g₀ J hp.le
      _ ≤ 10 ^ (1 / p) := Real.rpow_le_rpow
        (mul_nonneg (inv_nonneg.mpr J.length_pos.le)
          (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (g₀ x)) p))
        hbase hpinv0
      _ ≤ 10 := Real.rpow_le_self_of_one_le (by norm_num) hpinv1
  have hgroot : (∫ x in I.carrier, ‖g₀ x‖ ^ p) ≤ I.length := by
    have hrootMass : (∫ x in I.carrier, ‖g x‖ ^ p) = b ^ p * I.length := by
      calc
        (∫ x in I.carrier, ‖g x‖ ^ p) =
            intervalL1Average (pStoppingMonitor g p hp0) I * I.length := by
          rw [intervalL1Average_mul_length]
          simp only [norm_pStoppingMonitor]
        _ = b ^ p * I.length := by
          rw [intervalL1Average_pStoppingMonitor_eq_localAverage_rpow]
    calc
      (∫ x in I.carrier, ‖g₀ x‖ ^ p) =
          b⁻¹ ^ p * ∫ x in I.carrier, ‖g x‖ ^ p :=
        by simpa only [g₀] using
          integral_norm_rpow_smul b⁻¹ (inv_pos.mpr hb').le g I p
      _ = b⁻¹ ^ p * (b ^ p * I.length) := by rw [hrootMass]
      _ = I.length := by rw [← mul_assoc, hpowCancel, one_mul]
      _ ≤ I.length := le_rfl
  have hnormalized :=
    lintegral_localizedTailMaximal_le_directQuadratic_geometric_local
      hlamA scale hscaleA hscaleNonneg f₀ (M := 10) (by norm_num) hmassA
      I hsubA ell₀ N hbound g₀ hp hp2 I.length_pos.le hfroot hgroot
      (F := 10) (G := 10) (by norm_num) (by norm_num) hfavgA hgavgA
  have hnormalized' :
      (∫⁻ x, localizedTailMaximal ell₀ scale A f₀ x * ‖g₀ x‖ₑ) ≤
        directQuadraticNormalizedCoefficient *
          ENNReal.ofReal (20 * holderConjugate p * I.length) := by
    simpa only [directQuadraticNormalizedCoefficient] using hnormalized
  have hfback : (L0Infinity.smul (a : ℂ) f₀ : ℝ → ℂ) = f := by
    funext x
    simp only [f₀, L0Infinity.smul_apply]
    rw [← mul_assoc]
    have hc : (a : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ ha'.ne'
    rw [hc, one_mul]
  have hgback : (L0Infinity.smul (b : ℂ) g₀ : ℝ → ℂ) = g := by
    funext x
    simp only [g₀, L0Infinity.smul_apply]
    rw [← mul_assoc]
    have hc : (b : ℂ) * ((b⁻¹ : ℝ) : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ hb'.ne'
    rw [hc, one_mul]
  have htail (x : ℝ) :
      localizedTailMaximal ell₀ scale A f x =
        ENNReal.ofReal a * localizedTailMaximal ell₀ scale A f₀ x := by
    have hs := localizedTailMaximal_smul (a : ℂ) ell₀ scale A f₀ x
    rw [hfback] at hs
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha'] at hs
    exact hs
  have hgnorm (x : ℝ) : ‖g x‖ₑ = ENNReal.ofReal b * ‖g₀ x‖ₑ := by
    have hx := congrFun hgback x
    rw [L0Infinity.smul_apply] at hx
    rw [← hx, enorm_mul, ← ofReal_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hb']
  have hpair :
      (∫⁻ x, localizedTailMaximal ell₀ scale T f x * ‖g x‖ₑ) =
        ENNReal.ofReal (a * b) *
          ∫⁻ x, localizedTailMaximal ell₀ scale A f₀ x * ‖g₀ x‖ₑ := by
    rw [← localizedTailMaximal_activeHighCollection ell₀ scale T f]
    calc
      (∫⁻ x, localizedTailMaximal ell₀ scale A f x * ‖g x‖ₑ) =
          ∫⁻ x, ENNReal.ofReal (a * b) *
            (localizedTailMaximal ell₀ scale A f₀ x * ‖g₀ x‖ₑ) := by
        apply lintegral_congr
        intro x
        rw [htail x, hgnorm x, ENNReal.ofReal_mul ha'.le]
        ring
      _ = ENNReal.ofReal (a * b) *
          ∫⁻ x, localizedTailMaximal ell₀ scale A f₀ x * ‖g₀ x‖ₑ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [show goodCollection S f
      (pStoppingMonitor g p (lt_trans zero_lt_one hp)) I = T by rfl]
  rw [hpair]
  apply (mul_le_mul' le_rfl hnormalized').trans_eq
  unfold pStoppingSparseAtom
  have hq0 : 0 ≤ holderConjugate p := (holderConjugate_spec hp).symm.pos.le
  rw [ENNReal.ofReal_mul directQuadraticOneNodeConstant_nonneg,
    ofReal_directQuadraticOneNodeConstant,
    ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hq0),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20),
    ENNReal.ofReal_mul (mul_nonneg I.length_pos.le
      (localAverage_nonneg 1 f I)),
    ENNReal.ofReal_mul I.length_pos.le,
    ENNReal.ofReal_mul ha'.le]
  simp only [a, b]
  norm_num
  ring

/-- The direct quadratic argument supplies the complete one-node estimate,
including the two normalization-degenerate zero-average cases. -/
theorem hasOneNodePStoppingGoodPartPairingBound_directQuadratic :
    HasOneNodePStoppingGoodPartPairingBound
      directQuadraticOneNodeConstant := by
  classical
  refine ⟨directQuadraticOneNodeConstant_nonneg, ?_⟩
  intro p hp hp2 ell₀ topScale shift maxDepth q₀ S I f g
    hell hS hI hsub
  let scale := finiteShiftGridScale topScale shift
  let monitor := pStoppingMonitor g p (lt_trans zero_lt_one hp)
  let T := goodCollection S f monitor I
  by_cases ha : 0 < localAverage 1 f I
  · by_cases hb : 0 < localAverage p g I
    · exact pStopping_good_part_pairing_directQuadratic_of_pos_averages
        hp hp2 ell₀ topScale shift maxDepth q₀ S I f g
        hell hS hI hsub ha hb
    · have hb0 : localAverage p g I = 0 :=
        le_antisymm (le_of_not_gt hb) (localAverage_nonneg p g I)
      have hgzero :=
        intervalRestrictionL0Infinity_ae_eq_zero_of_localAverage_eq_zero
          g I (lt_trans zero_lt_one hp) hb0
      have hTS : T ⊆ S := by
        intro J hJ
        exact (Finset.mem_filter.mp hJ).1
      have hscaleT : ∀ J ∈ T,
          J.length = (2 : ℝ) ^ (scale J + 2) := by
        intro J hJ
        exact completeFiniteShiftGridTree_length_eq_scale
          topScale shift maxDepth q₀ J (hS (hTS hJ))
      have hsubT : ∀ J ∈ T, J.carrier ⊆ I.carrier := by
        intro J hJ
        exact hsub J (hTS hJ)
      have hpairRestrict :=
        lintegral_localizedTailMaximal_mul_intervalRestrictionL0Infinity_eq
          scale f g ell₀ I hscaleT hsubT
      calc
        (∫⁻ x, localizedTailMaximal ell₀ scale T f x * ‖g x‖ₑ) =
            ∫⁻ x, localizedTailMaximal ell₀ scale T f x *
              ‖intervalRestrictionL0Infinity g I x‖ₑ := hpairRestrict.symm
        _ = 0 := by
          apply lintegral_eq_zero_of_ae_eq_zero
          filter_upwards [hgzero] with x hx
          simp only [hx, Pi.zero_apply, enorm_zero, mul_zero]
        _ ≤ ENNReal.ofReal
              (directQuadraticOneNodeConstant * holderConjugate p) *
            pStoppingSparseAtom p f g I := bot_le
  · have ha0 : localAverage 1 f I = 0 :=
      le_antisymm (le_of_not_gt ha) (localAverage_nonneg 1 f I)
    have hTS : T ⊆ S := by
      intro J hJ
      exact (Finset.mem_filter.mp hJ).1
    have hsubT : ∀ J ∈ T, J.carrier ⊆ I.carrier := by
      intro J hJ
      exact hsub J (hTS hJ)
    have htail (x : ℝ) : localizedTailMaximal ell₀ scale T f x = 0 :=
      localizedTailMaximal_eq_zero_of_rootAverage_eq_zero
        ell₀ scale T f I hsubT ha0 x
    calc
      (∫⁻ x, localizedTailMaximal ell₀ scale T f x * ‖g x‖ₑ) = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards with x
        simp only [htail x, zero_mul, Pi.zero_apply]
      _ ≤ ENNReal.ofReal
            (directQuadraticOneNodeConstant * holderConjugate p) *
          pStoppingSparseAtom p f g I := bot_le


end
end KrauseLaceyQuadraticDirectPStopping
end QuadraticCarleson
