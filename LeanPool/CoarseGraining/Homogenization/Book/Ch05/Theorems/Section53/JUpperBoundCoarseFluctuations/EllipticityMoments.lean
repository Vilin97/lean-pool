/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Assembly
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.FluctuationIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.MomentBounds
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.EnergyDefect

/-! # Ellipticity Moments -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory

noncomputable section

/-!
# Ellipticity positive-excess moments for the coarse-fluctuation lemma

This file contains the internal Holder conversion for the lower and upper
positive-excess ellipticity factors appearing in the third Section 5.3 lemma.
-/

theorem holderConjugate_xi_section53CoarseFluctuationZeta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (hP4.xi : ℝ).HolderConjugate (section53CoarseFluctuationZeta hP4) where
  inv_add_inv_eq_inv := by
    simpa using inv_xi_add_inv_section53CoarseFluctuationZeta hP4
  left_pos := by
    exact_mod_cast hP4.xi_pos
  right_pos := section53CoarseFluctuationZeta_pos hP4

theorem memLp_of_integrable_nonneg_nat_pow
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ξ : ℕ} {X : RegCoeffField d → ℝ}
    (hξ : 0 < ξ) (hX_aemeas : AEMeasurable X P)
    (hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a)
    (hX_int : Integrable (fun a => X a ^ ξ) P) :
    MemLp X (ENNReal.ofReal (ξ : ℝ)) P := by
  have hξ_ne : ξ ≠ 0 := Nat.ne_of_gt hξ
  have hnorm_int : Integrable (fun a => ‖X a‖ ^ ξ) P := by
    refine hX_int.congr ?_
    filter_upwards [hX_nonneg] with a ha
    rw [Real.norm_of_nonneg ha]
  have hmem : MemLp X (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff
      hX_aemeas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.rpow_natCast] using hnorm_int
  simpa using hmem

private theorem memLp_of_integrable_nonneg_rpow
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {p : ℝ} {X : RegCoeffField d → ℝ}
    (hp : 0 < p) (hX_aemeas : AEMeasurable X P)
    (hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a)
    (hX_int : Integrable (fun a => Real.rpow (X a) p) P) :
    MemLp X (ENNReal.ofReal p) P := by
  have hnorm_int :
      Integrable (fun a => ‖X a‖ ^ (ENNReal.ofReal p).toReal) P := by
    refine hX_int.congr ?_
    filter_upwards [hX_nonneg] with a ha
    rw [Real.norm_of_nonneg ha, ENNReal.toReal_ofReal hp.le, Real.rpow_eq_pow]
  rw [← MeasureTheory.integrable_norm_rpow_iff
    hX_aemeas.aestronglyMeasurable
    (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hp])
    (by simp)]
  exact hnorm_int

theorem shiftedUpperDecay_le_betaDecay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    Real.rpow (3 : ℝ)
        (-((hP4.sUpper + β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) := by
  intro β
  have hβ_le : β ≤ hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
    simpa [β] using section53CoarseFluctuationBeta_le_sUpper_sub_dim_div_xi hP4
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  nlinarith

theorem shiftedLowerDecay_le_betaDecay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    Real.rpow (3 : ℝ)
        (-((hP4.sLower + β) - (d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) := by
  intro β
  have hβ_le : β ≤ hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
    simpa [β] using section53CoarseFluctuationBeta_le_sLower_sub_dim_div_xi hP4
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  nlinarith

private theorem shiftedMomentDenom_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) {r : ℝ} (hr : r < 1) :
    0 < ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - r := by
  have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
  have hd_half : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast Nat.zero_le hP4.xi
  have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
    div_nonneg hd_nonneg hxi_nonneg
  linarith

theorem section52MomentLossCoeff_nonneg_at_shift
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) {s r : ℝ}
    (_hs : 0 < s) (_hsr : s < r) (hr : r < 1) :
    0 ≤ section52MomentLossCoeff d hP4.xi s r := by
  unfold section52MomentLossCoeff
  have hden : 0 ≤ ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - r :=
    (shiftedMomentDenom_pos hP4 hr).le
  have hxi_nonneg : 0 ≤ (hP4.xi : ℝ) := by
    exact_mod_cast Nat.zero_le hP4.xi
  exact mul_nonneg (sq_nonneg _)
    (add_nonneg (div_nonneg hxi_nonneg hden) (sq_nonneg _))

private theorem int_toNat_sub_add_toNat_sub
    {k n m : ℤ} (hkn : k ≤ n) (hnm : n ≤ m) :
    Int.toNat (m - n) + Int.toNat (n - k) = Int.toNat (m - k) := by
  have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hnm
  have hnk_nonneg : 0 ≤ n - k := sub_nonneg.mpr hkn
  have hmk_nonneg : 0 ≤ m - k := sub_nonneg.mpr (hkn.trans hnm)
  have hcast :
      ((Int.toNat (m - n) + Int.toNat (n - k) : ℕ) : ℤ) =
        ((Int.toNat (m - k) : ℕ) : ℤ) := by
    rw [Nat.cast_add, Int.toNat_of_nonneg hmn_nonneg,
    Int.toNat_of_nonneg hnk_nonneg, Int.toNat_of_nonneg hmk_nonneg]
    ring
  exact_mod_cast hcast

private theorem sum_range_to_Icc_descending {k m : ℤ} (hkm : k ≤ m)
    (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (Int.toNat (m - k)), F j) =
      ∑ n ∈ Finset.Icc (k + 1) m, F (Int.toNat (m - n)) := by
  classical
  refine Finset.sum_bij (fun j _hj => m - (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
    have hj_lt_nat : j < Int.toNat (m - k) := Finset.mem_range.mp hj
    have hj_lt : (j : ℤ) < m - k := by
      have hj_lt' : (j : ℤ) < ((Int.toNat (m - k) : ℕ) : ℤ) := by
        exact_mod_cast hj_lt_nat
      simpa [hL] using hj_lt'
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro j₁ _hj₁ j₂ _hj₂ h
    have h' : m - (j₁ : ℤ) = m - (j₂ : ℤ) := by simpa using h
    have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by omega
    exact_mod_cast hcast
  · intro n hn
    have hn_low : k + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_high : n ≤ m := (Finset.mem_Icc.mp hn).2
    refine ⟨Int.toNat (m - n), ?_, ?_⟩
    · have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
        Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
      have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hmn_lt : m - n < m - k := by omega
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      apply Finset.mem_range.mpr
      have hcast : ((Int.toNat (m - n) : ℕ) : ℤ) <
          ((Int.toNat (m - k) : ℕ) : ℤ) := by
        simpa [hto, hL] using hmn_lt
      exact_mod_cast hcast
    · have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      change m - ((Int.toNat (m - n) : ℕ) : ℤ) = n
      rw [hto]
      omega
  · intro j _hj
    have harg : Int.toNat (m - (m - (j : ℤ))) = j := by
      have hsub : m - (m - (j : ℤ)) = (j : ℤ) := by ring
      simp [hsub]
    exact congrArg F harg.symm

private theorem sum_Icc_betaWeight_le_five_beta_inv
    {k m : ℤ} (hkm : k ≤ m) {β : ℝ} (hβ : 0 < β) (hβ_le : β ≤ 1) :
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) ≤
      5 * β⁻¹ := by
  let L : ℕ := Int.toNat (m - k)
  have hsum_eq :
      (∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) =
        ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    simpa [L] using
      (sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j => Real.rpow (3 : ℝ) (-β * (j : ℝ)))).symm
  have hrange_le :
      (∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ))) ≤
        ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
          Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      simpa only [Finset.mem_filter, and_true] using
        Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
    · intro j _hj _hj_not
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hgeom :=
    Homogenization.sum_filter_triadicDepthWeight_le_geometric_inv
      β L (fun _j => True) hβ
  have hgeom_five :
      (1 - Real.rpow (3 : ℝ) (-β))⁻¹ ≤ 5 * β⁻¹ :=
    Homogenization.Book.Ch02.inv_one_sub_rpow_three_neg_le_five_inv hβ hβ_le
  calc
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)))
        =
      ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hsum_eq
    _ ≤
      ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
        Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hrange_le
    _ ≤ (1 - Real.rpow (3 : ℝ) (-β))⁻¹ := hgeom
    _ ≤ 5 * β⁻¹ := hgeom_five

private theorem descendantsAverage_restrictionResponseJObservableCubeSet_mono_to_finerScale
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k n m : ℤ} (hkn : k ≤ n) (hnm : n ≤ m) (p q : Vec d) :
    descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) ≤
      descendantsAverage (originCube d m) (Int.toNat (m - k))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  let l : ℕ := Int.toNat (n - k)
  let F : TriadicCube d → ℝ := fun R => Ch04.restrictionResponseJObservableCubeSet R p q a
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j, F R ≤ descendantsAverage R l F := by
    intro R hR
    have hRscaleMem : R ∈ descendantsAtScale Q n := by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth Q hnm] using! hR
    have hRscale : R.scale = n := scale_eq_of_mem_descendantsAtScale hRscaleMem
    have hkR : k ≤ R.scale := by simpa [hRscale] using hkn
    simpa [F, l, hRscale] using
      Ch04.restrictionResponseJObservableCubeSet_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
        ha R hkR p q
  have hmono :
      descendantsAverage Q j F ≤
        descendantsAverage Q j (fun R => descendantsAverage R l F) :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have hcompose :
      descendantsAverage Q j (fun R => descendantsAverage R l F) =
        descendantsAverage Q (j + l) F := by
    exact (descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q j l F).symm
  have hjl : j + l = Int.toNat (m - k) := by
    simpa [j, l] using int_toNat_sub_add_toNat_sub hkn hnm
  calc
    descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
        = descendantsAverage Q j F := rfl
    _ ≤ descendantsAverage Q j (fun R => descendantsAverage R l F) := hmono
    _ = descendantsAverage Q (j + l) F := hcompose
    _ = descendantsAverage Q (Int.toNat (m - k)) F := by rw [hjl]
    _ =
      descendantsAverage (originCube d m) (Int.toNat (m - k))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := rfl

private theorem responseDefectAverageAtScale_le_childResponseAverageAtScale
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k n m : ℤ} (hkn : k ≤ n) (hnm : n ≤ m) (p q : Vec d) :
    WeakNormsMaximizer.responseDefectAverageAtScale m n p q a ≤
      descendantsAverage (originCube d m) (Int.toNat (m - k))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
  have hparent_nonneg :
      0 ≤ Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a :=
    Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d m) p q a
  have hdef_le :
      WeakNormsMaximizer.responseDefectAverageAtScale m n p q a ≤
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
    have hparent_nonneg' :
        0 ≤ ResponseJ (cubeSet (originCube d m)) p q a := by
      simpa [Ch04.restrictionResponseJObservableCubeSet] using hparent_nonneg
    dsimp [WeakNormsMaximizer.responseDefectAverageAtScale]
    linarith
  exact hdef_le.trans
    (descendantsAverage_restrictionResponseJObservableCubeSet_mono_to_finerScale
      ha hkn hnm p q)

theorem sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_childResponseAverageAtScale
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℤ} (_hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {β : ℝ} (hβ : 0 < β) (hβ_le : β ≤ 1) (p q : Vec d) :
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)) *
          Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) ^ 2
      ≤
        (5 * β⁻¹) ^ 2 *
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
  let S : Finset ℤ := Finset.Icc (k + 1) m
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))
  let D : ℤ → ℝ :=
    fun n => WeakNormsMaximizer.responseDefectAverageAtScale m n p q a
  let childK : ℝ :=
    descendantsAverage (originCube d m) (Int.toNat (m - k))
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
  have hw : ∀ n ∈ S, 0 ≤ w n := by
    intro n _hn
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hIndex : ∀ n ∈ S, k ≤ n ∧ n ≤ m := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    constructor
    · linarith
    · exact hn'.2
  have hD_nonneg : ∀ n ∈ S, 0 ≤ D n := by
    intro n hn
    exact WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
      a ha m n p q
  have hD_le_child : ∀ n ∈ S, D n ≤ childK := by
    intro n hn
    exact responseDefectAverageAtScale_le_childResponseAverageAtScale
      ha (hIndex n hn).1 (hIndex n hn).2 p q
  have hchild_nonneg : 0 ≤ childK := by
    dsimp [childK]
    exact JUpperBoundWeakNorms.descendantsAverage_restrictionResponseJObservableCubeSet_nonneg
      (originCube d m) (Int.toNat (m - k)) p q a
  have hCauchy :=
    sq_sum_mul_sqrt_le_sum_mul_sum_mul S w D hw hD_nonneg
  have hsumD :
      ∑ n ∈ S, w n * D n ≤ (∑ n ∈ S, w n) * childK := by
    calc
      ∑ n ∈ S, w n * D n
          ≤ ∑ n ∈ S, w n * childK :=
            Finset.sum_le_sum fun n hn =>
              mul_le_mul_of_nonneg_left (hD_le_child n hn) (hw n hn)
      _ = (∑ n ∈ S, w n) * childK := by
            rw [Finset.sum_mul]
  have hsum_nonneg : 0 ≤ ∑ n ∈ S, w n :=
    Finset.sum_nonneg hw
  have hsum_le : (∑ n ∈ S, w n) ≤ 5 * β⁻¹ := by
    simpa [S, w] using
      sum_Icc_betaWeight_le_five_beta_inv
        (k := k) (m := m) hkm hβ hβ_le
  have hfive_nonneg : 0 ≤ 5 * β⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr hβ.le)
  calc
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)) *
          Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) ^ 2
        =
      (∑ n ∈ S, w n * Real.sqrt (D n)) ^ 2 := rfl
    _ ≤ (∑ n ∈ S, w n) * ∑ n ∈ S, w n * D n := hCauchy
    _ ≤ (∑ n ∈ S, w n) * ((∑ n ∈ S, w n) * childK) :=
          mul_le_mul_of_nonneg_left hsumD hsum_nonneg
    _ = (∑ n ∈ S, w n) ^ 2 * childK := by ring
    _ ≤ (5 * β⁻¹) ^ 2 * childK := by
          have habs : |∑ n ∈ S, w n| ≤ |5 * β⁻¹| := by
            rwa [abs_of_nonneg hsum_nonneg, abs_of_nonneg hfive_nonneg]
          exact mul_le_mul_of_nonneg_right
            (sq_le_sq.mpr habs) hchild_nonneg

/-- Holder conversion for the lower inverse ellipticity positive-excess term. -/
theorem lowerPositiveExcess_responseJ_expectation_le_of_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d)
    (hLowerPowInt :
      let β := section53CoarseFluctuationBeta hP4
      let rLower := hP4.sLower + β
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField
                (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ hP4.xi) P)
    (hResponsePowInt :
      let ζ := section53CoarseFluctuationZeta hP4
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      Integrable
        (fun a : RegCoeffField d =>
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ) P) :
    let β := section53CoarseFluctuationBeta hP4
    let rLower := hP4.sLower + β
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    ∫ a,
        (max
            ((Ch04.lambdaSqCoeffField
                (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) *
          Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a ∂P
      ≤
        lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi hP hStruct *
          coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let ζ := section53CoarseFluctuationZeta hP4
  let rLower := hP4.sLower + β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField
            (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let J : RegCoeffField d → ℝ :=
    fun a => Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hrLower_pos : 0 < rLower := by
    dsimp [rLower, β]
    linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
  have hLower_aemeas : AEMeasurable lowerExcess P := by
    exact
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
          (originCube d (m : ℤ)) hrLower_pos).sub aemeasurable_const).max
        aemeasurable_const
  have hLower_nonneg : ∀ᵐ a ∂P, 0 ≤ lowerExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hLower_mem :
      MemLp lowerExcess (ENNReal.ofReal (hP4.xi : ℝ)) P := by
    exact
      memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hLower_aemeas
        hLower_nonneg (by simpa [lowerExcess, rLower, β] using hLowerPowInt)
  have hJ_aemeas : AEMeasurable J P := by
    simpa [J] using!
      hP.aemeasurable_restrictionResponseJObservableCubeSet
        (originCube d (k : ℤ)) p_e q_e
  have hJ_nonneg : ∀ᵐ a ∂P, 0 ≤ J a := by
    filter_upwards with a
    exact Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p_e q_e a
  have hJ_mem : MemLp J (ENNReal.ofReal ζ) P := by
    exact
      memLp_of_integrable_nonneg_rpow hζ_pos hJ_aemeas hJ_nonneg
        (by simpa [J, ζ, p_e, q_e] using hResponsePowInt)
  have hHolder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := P) (holderConjugate_xi_section53CoarseFluctuationZeta hP4)
      hLower_nonneg hJ_nonneg hLower_mem hJ_mem
  simpa [lowerExcess, J, lambdaInvPositiveExcessMomentAtScale,
    Ch04.annealedMomentRoot, coarseFluctuationResponseMomentAtScale,
    rLower, β, ζ, p_e, q_e, one_div, Real.rpow_natCast] using hHolder

/-- Holder conversion for the upper ellipticity positive-excess term. -/
theorem upperPositiveExcess_responseJ_expectation_le_of_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d)
    (hUpperPowInt :
      let β := section53CoarseFluctuationBeta hP4
      let rUpper := hP4.sUpper + β
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField
                (originCube d (m : ℤ)) rUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ hP4.xi) P)
    (hResponsePowInt :
      let ζ := section53CoarseFluctuationZeta hP4
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      Integrable
        (fun a : RegCoeffField d =>
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ) P) :
    let β := section53CoarseFluctuationBeta hP4
    let rUpper := hP4.sUpper + β
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    ∫ a,
        (max
            (Ch04.LambdaSqCoeffField
                (originCube d (m : ℤ)) rUpper (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) *
          Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a ∂P
      ≤
        LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi hP hStruct *
          coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let ζ := section53CoarseFluctuationZeta hP4
  let rUpper := hP4.sUpper + β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField
            (originCube d (m : ℤ)) rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let J : RegCoeffField d → ℝ :=
    fun a => Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hrUpper_pos : 0 < rUpper := by
    dsimp [rUpper, β]
    linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
  have hUpper_aemeas : AEMeasurable upperExcess P := by
    exact
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one
          (originCube d (m : ℤ)) hrUpper_pos).sub aemeasurable_const).max
        aemeasurable_const
  have hUpper_nonneg : ∀ᵐ a ∂P, 0 ≤ upperExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hUpper_mem :
      MemLp upperExcess (ENNReal.ofReal (hP4.xi : ℝ)) P := by
    exact
      memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hUpper_aemeas
        hUpper_nonneg (by simpa [upperExcess, rUpper, β] using hUpperPowInt)
  have hJ_aemeas : AEMeasurable J P := by
    simpa [J] using!
      hP.aemeasurable_restrictionResponseJObservableCubeSet
        (originCube d (k : ℤ)) p_e q_e
  have hJ_nonneg : ∀ᵐ a ∂P, 0 ≤ J a := by
    filter_upwards with a
    exact Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p_e q_e a
  have hJ_mem : MemLp J (ENNReal.ofReal ζ) P := by
    exact
      memLp_of_integrable_nonneg_rpow hζ_pos hJ_aemeas hJ_nonneg
        (by simpa [J, ζ, p_e, q_e] using hResponsePowInt)
  have hHolder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := P) (holderConjugate_xi_section53CoarseFluctuationZeta hP4)
      hUpper_nonneg hJ_nonneg hUpper_mem hJ_mem
  simpa [upperExcess, J, LambdaPositiveExcessMomentAtScale,
    Ch04.annealedMomentRoot, coarseFluctuationResponseMomentAtScale,
    rUpper, β, ζ, p_e, q_e, one_div, Real.rpow_natCast] using hHolder

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
