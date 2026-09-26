/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.WidetildeTheta
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.Theory

public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds.Helpers

/-! # Factor Bounds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Matrix.Norms.Elementwise Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace RestrictionLawCarrier

/-- Lower-right finite-parent coarse-block fluctuation bound, stated directly
against the law-facing Ch4 surface.  The proof owns all locality,
measurability, covariance, and deterministic positive-excess domination. -/
theorem lowerRight_matrixNorm_positiveExcess_finsetSup_momentRoot_le_of_restrictionUnitRangeDependentLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {n : ℤ} {ξ : ℕ} {K B : ℝ}
    (hn : 0 ≤ n)
    (hparent_scale : ∀ Q ∈ parents, n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d n)) b).lowerRight i j ∂P)
    (hξ : 2 ≤ ξ) (hK_nonneg : 0 ≤ K) (hB_nonneg : 0 ≤ B)
    (hOriginLp_int :
      ∀ i j : Fin d,
        Integrable
          (fun a =>
            |restrictionCenteredOriginObservable P n
              (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^ ξ) P)
    (hOriginLp :
      ∀ i j : Fin d,
        (∫ a,
            |restrictionCenteredOriginObservable P n
              (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^ ξ ∂P) ^
            (1 / (ξ : ℝ)) ≤ K)
    (hBudget :
      ∀ Q ∈ parents,
        ((descendantsAtScale Q n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n ξ *
              ((descendantsAtScale Q n).card : ℝ) ^ (1 / (ξ : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n ξ *
              Real.sqrt ((descendantsAtScale Q n).card : ℝ) * K) ≤ B) :
    annealedMomentRoot P ξ
      (fun a =>
        parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm center)
              0)) ≤
      ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
        ((parents.card : ℝ) ^ (1 / (ξ : ℝ)) * B) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let C : ℝ := (parents.card : ℝ) ^ (1 / (ξ : ℝ)) * B
  let excess : RegCoeffField d → ℝ :=
    fun a =>
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm center)
            0)
  let entry : Fin d → Fin d → RegCoeffField d → ℝ :=
    fun i j a =>
      parents.sup' hparents
        (fun Q =>
          |restrictionCenteredDescendantAverageOnCube P Q n
            (fun U a => (coarseBlockMatrix U a).lowerRight i j) a|)
  have hξ_one : 1 ≤ ξ := by omega
  have hexcess_nonneg : ∀ a, 0 ≤ excess a := by
    intro a
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right _ _).trans
      (Finset.le_sup'
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm center)
            0) hQ0)
  have hentry_nonneg : ∀ i j a, 0 ≤ entry i j a := by
    intro i j a
    exact finsetSup_abs_restrictionCenteredDescendantAverageOnCube_nonneg hparents
      (fun U a => (coarseBlockMatrix U a).lowerRight i j) a
  have hexcess_aemeas : AEMeasurable excess P := by
    simpa [excess] using
      aemeasurable_lowerRight_matrixNorm_positiveExcess_finsetSup hP hparents center
  have hentry_aemeas : ∀ i j, AEMeasurable (entry i j) P := by
    intro i j
    simpa [entry] using
      aemeasurable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube
        (P := P) (n := n) hparents
        (fun U a => (coarseBlockMatrix U a).lowerRight i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet R i j)
  have hentry_int :
      ∀ i j, Integrable (fun a => |entry i j a| ^ ξ) P := by
    intro i j
    have hint :
        Integrable
          (fun a : RegCoeffField d =>
            (parents.sup' hparents
              (fun Q =>
                |restrictionCenteredDescendantAverageOnCube P Q n
                  (fun U a => (coarseBlockMatrix U a).lowerRight i j) a|)) ^ ξ) P :=
      integrable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_of_stationary
        (d := d) (n := n) (P := P) (parents := parents) hparents
        hn hparent_scale hPstat
        (fun U a => (coarseBlockMatrix U a).lowerRight i j)
        (by
          simpa [blockMatEntry] using
            isRestrictionTranslationCovariant_comp_toFun
              (coarseBlockMatrix_entry_translation_covariant (Sum.inr i) (Sum.inr j)))
        (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet (originCube d n) i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet R i j)
        hξ_one (hOriginLp_int i j)
    refine hint.congr ?_
    filter_upwards with a
    simp [entry, abs_of_nonneg (hentry_nonneg i j a)]
  have hentry_root :
      ∀ i j,
        (∫ a, |entry i j a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤ C := by
    intro i j
    have hroot :=
      integral_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
        (d := d) (n := n) (P := P) (parents := parents) hparents
        (p := ξ) (K := K) (B := B)
        hP hn hparent_scale hPstat hPdep
        (fun U a => (coarseBlockMatrix U a).lowerRight i j)
        (fun Q hQ R hR =>
          hP.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerRight_apply_cubeSet R i j)
        (by
          simpa [blockMatEntry] using
            isRestrictionTranslationCovariant_comp_toFun
              (coarseBlockMatrix_entry_translation_covariant (Sum.inr i) (Sum.inr j)))
        (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet (originCube d n) i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet R i j)
        hξ hK_nonneg hB_nonneg (hOriginLp_int i j) (hOriginLp i j) hBudget
    calc
      (∫ a, |entry i j a| ^ ξ ∂P) ^ (1 / (ξ : ℝ))
          = (∫ a, entry i j a ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
              congr 1
              exact integral_congr_ae (Filter.Eventually.of_forall fun a => by
                simp [abs_of_nonneg (hentry_nonneg i j a)])
      _ ≤ C := by
              simpa [entry, C] using hroot
  have hpoint :
      excess ≤ᵐ[P] fun a => ∑ i : Fin d, ∑ j : Fin d, entry i j a := by
    simpa [excess, entry] using
      hP.coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_finsetSup_le_sum_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_ae
        hparents hparent_scale center hcenter
  simpa [excess, entry, C] using
    momentRoot_excess_le_card_mul_entryRootBound
      (P := P) (ξ := ξ) (C := C) hξ_one
      excess entry hexcess_nonneg hexcess_aemeas hentry_nonneg
      hentry_aemeas hentry_int hentry_root hpoint

private theorem upperLeft_abs_entry_le_LambdaSqCoeffField_ae_aux
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (i j : Fin d) :
    (fun a : RegCoeffField d => |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|) ≤ᵐ[P]
      fun a => LambdaSqCoeffField Q s (.finite 1) a := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hEntry :
      |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft i j| ≤
        Ch02.coarseBMatrixNorm Q F := by
    simpa [Ch02.coarseBMatrixNorm, Ch02.matrixNorm_eq_matrixOperatorNorm] using
      Ch02.abs_entry_le_matrixOperatorNorm
        ((Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft) i j
  calc
    |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|
        = |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft i j| := by
      rw [hEq]
    _ ≤ Ch02.coarseBMatrixNorm Q F := hEntry
    _ ≤ Ch02.LambdaSq Q s (.finite 1) F :=
      Ch02.oneCube_b_le_LambdaSq_finite Q F hs (by norm_num : (1 : ℝ) ≤ 1)
    _ = LambdaSqCoeffField Q s (.finite 1) a := by
      simp [LambdaSqCoeffField, ha, F]

private theorem lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae_aux
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (i j : Fin d) :
    (fun a : RegCoeffField d => |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|) ≤ᵐ[P]
      fun a => (lambdaSqCoeffField Q s (.finite 1) a)⁻¹ := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hEntry :
      |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight i j| ≤
        Ch02.coarseSigmaStarInvMatrixNorm Q F := by
    simpa [Ch02.coarseSigmaStarInvMatrixNorm, Ch02.matrixNorm_eq_matrixOperatorNorm] using
      Ch02.abs_entry_le_matrixOperatorNorm
        ((Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight) i j
  calc
    |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|
        = |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight i j| := by
      rw [hEq]
    _ ≤ Ch02.coarseSigmaStarInvMatrixNorm Q F := hEntry
    _ ≤ (Ch02.lambdaSq Q s (.finite 1) F)⁻¹ :=
      Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q F hs
        (by norm_num : (1 : ℝ) ≤ 1)
    _ = (lambdaSqCoeffField Q s (.finite 1) a)⁻¹ := by
      simp [lambdaSqCoeffField, ha, F]


theorem upperLeft_entry_le_LambdaSqCoeffField_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft 0 0) ≤ᵐ[P]
      fun a => LambdaSqCoeffField Q s (.finite 1) a := by
  filter_upwards [upperLeft_abs_entry_le_LambdaSqCoeffField_ae_aux hP Q hs 0 0] with a hle
  exact (le_abs_self ((coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft 0 0)).trans hle

theorem lowerRight_entry_le_lambdaSqCoeffField_inv_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 0 0) ≤ᵐ[P]
      fun a => (lambdaSqCoeffField Q s (.finite 1) a)⁻¹ := by
  filter_upwards [lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae_aux hP Q hs 0 0] with a hle
  exact (le_abs_self ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 0 0)).trans hle

theorem upperLeft_abs_entry_le_LambdaSqCoeffField_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (i j : Fin d) :
    (fun a : RegCoeffField d => |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|) ≤ᵐ[P]
      fun a => LambdaSqCoeffField Q s (.finite 1) a := by
  exact upperLeft_abs_entry_le_LambdaSqCoeffField_ae_aux hP Q hs i j

theorem lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (i j : Fin d) :
    (fun a : RegCoeffField d => |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|) ≤ᵐ[P]
      fun a => (lambdaSqCoeffField Q s (.finite 1) a)⁻¹ := by
  exact lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae_aux hP Q hs i j

theorem integrable_abs_pow_of_ae_abs_le_nonneg
    {d : ℕ} {P : RestrictionCoeffLaw d} {ξ : ℕ}
    {X Y : RegCoeffField d → ℝ}
    (hX_meas : AEMeasurable X P)
    (hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a)
    (hXY : (fun a => |X a|) ≤ᵐ[P] Y)
    (hY_pow_int : Integrable (fun a => Y a ^ ξ) P) :
    Integrable (fun a => |X a| ^ ξ) P := by
  have hY_abs_pow_int : Integrable (fun a => |Y a| ^ ξ) P := by
    refine hY_pow_int.congr ?_
    filter_upwards [hY_nonneg] with a ha
    simp [abs_of_nonneg ha]
  refine Integrable.mono' hY_abs_pow_int ?_ ?_
  · exact ((hX_meas.norm.pow_const ξ)).aestronglyMeasurable
  · filter_upwards [hY_nonneg, hXY] with a hY_nonneg_a hXY_a
    have hpow : |X a| ^ ξ ≤ |Y a| ^ ξ := by
      simpa [abs_of_nonneg hY_nonneg_a] using
        pow_le_pow_left₀ (abs_nonneg (X a)) hXY_a ξ
    have hleft_nonneg : 0 ≤ |X a| ^ ξ :=
      pow_nonneg (abs_nonneg (X a)) ξ
    have hright_nonneg : 0 ≤ |Y a| ^ ξ :=
      pow_nonneg (abs_nonneg (Y a)) ξ
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg,
      abs_of_nonneg hright_nonneg] using hpow

private theorem annealedMomentRoot_abs_le_of_ae_abs_le_nonneg
    {d : ℕ} {P : RestrictionCoeffLaw d} {ξ : ℕ}
    {X Y : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (_hY_nonneg : ∀ a, 0 ≤ Y a)
    (hXY : (fun a => |X a|) ≤ᵐ[P] Y)
    (hX_abs_pow_int : Integrable (fun a => |X a| ^ ξ) P)
    (hY_pow_int : Integrable (fun a => Y a ^ ξ) P) :
    annealedMomentRoot P ξ (fun a => |X a|) ≤ annealedMomentRoot P ξ Y := by
  have hpow :
      (fun a => |X a| ^ ξ) ≤ᵐ[P] fun a => Y a ^ ξ := by
    filter_upwards [hXY] with a hle
    exact pow_le_pow_left₀ (abs_nonneg (X a)) hle ξ
  have hint_le :
      ∫ a, |X a| ^ ξ ∂P ≤ ∫ a, Y a ^ ξ ∂P :=
    integral_mono_ae hX_abs_pow_int hY_pow_int hpow
  have hleft_nonneg : 0 ≤ ∫ a, |X a| ^ ξ ∂P :=
    integral_nonneg fun a => pow_nonneg (abs_nonneg (X a)) ξ
  have hexp_nonneg : 0 ≤ 1 / (ξ : ℝ) := by positivity
  simpa [annealedMomentRoot] using
    Real.rpow_le_rpow hleft_nonneg hint_le hexp_nonneg

private theorem annealedMomentRoot_abs_sub_integral_le_two_mul
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ) (hX_meas : AEMeasurable X P)
    (hX_abs_pow_int : Integrable (fun a => |X a| ^ ξ) P) :
    annealedMomentRoot P ξ
        (fun a => |X a - ∫ b, X b ∂P|) ≤
      2 * annealedMomentRoot P ξ (fun a => |X a|) := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hmem_p : MemLp X (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hX_abs_pow_int
  have hmem_one : MemLp X (1 : ENNReal) P :=
    hmem_p.mono_exponent (by exact_mod_cast hξ)
  have hX_int : Integrable X P := by
    rwa [MeasureTheory.memLp_one_iff_integrable] at hmem_one
  let c : ℝ := ∫ b, X b ∂P
  have hconst_mem : MemLp (fun _ : RegCoeffField d => c) (ξ : ENNReal) P :=
    memLp_const c
  have hcenter_mem : MemLp (fun a => X a - c) (ξ : ENNReal) P :=
    hmem_p.sub hconst_mem
  have hcenter_toReal :
      ENNReal.toReal (eLpNorm (fun a => X a - c) (ξ : ENNReal) P) =
        annealedMomentRoot P ξ (fun a => |X a - c|) := by
    calc
      ENNReal.toReal (eLpNorm (fun a => X a - c) (ξ : ENNReal) P)
          = (∫ a, ‖X a - c‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := fun a => X a - c) (p := ξ) hξ hcenter_mem
      _ = annealedMomentRoot P ξ (fun a => |X a - c|) := by
            simp [annealedMomentRoot, Real.norm_eq_abs]
  have hX_toReal :
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) =
        annealedMomentRoot P ξ (fun a => |X a|) := by
    calc
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P)
          = (∫ a, ‖X a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := X) (p := ξ) hξ hmem_p
      _ = annealedMomentRoot P ξ (fun a => |X a|) := by
            simp [annealedMomentRoot, Real.norm_eq_abs]
  have hroot_abs_nonneg :
      0 ≤ annealedMomentRoot P ξ (fun a => |X a|) :=
    annealedMomentRoot_nonneg_of_nonneg P ξ fun a => abs_nonneg (X a)
  have hmean_le :
      |c| ≤ annealedMomentRoot P ξ (fun a => |X a|) := by
    have hAbs_meas : AEMeasurable (fun a => |X a|) P := by
      simpa [Real.norm_eq_abs] using hX_meas.norm
    have hAbs_int : Integrable (fun a => |X a|) P := by
      have hAbs_mem_one : MemLp (fun a => |X a|) (1 : ENNReal) P := by
        have hAbs_mem_p : MemLp (fun a => |X a|) (ξ : ENNReal) P := by
          rw [← MeasureTheory.integrable_norm_rpow_iff hAbs_meas.aestronglyMeasurable
            (by exact_mod_cast hξ_ne) (by simp)]
          simpa [Real.norm_eq_abs, abs_abs] using hX_abs_pow_int
        exact hAbs_mem_p.mono_exponent (by exact_mod_cast hξ)
      rwa [MeasureTheory.memLp_one_iff_integrable] at hAbs_mem_one
    have hInt_le_root :
        ∫ a, |X a| ∂P ≤ annealedMomentRoot P ξ (fun a => |X a|) := by
      exact integral_le_annealedMomentRoot_of_ae_nonneg hξ hAbs_meas
        (Filter.Eventually.of_forall fun a => abs_nonneg (X a))
        (by simpa using hX_abs_pow_int)
    exact (abs_integral_le_integral_abs (f := X) (μ := P)).trans hInt_le_root
  have hconst_toReal :
      ENNReal.toReal (eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P) = |c| := by
    have hμ_ne_zero : (P : Measure (RegCoeffField d)) ≠ 0 :=
      IsProbabilityMeasure.ne_zero P
    have hξ_enn_ne_zero : (ξ : ENNReal) ≠ 0 := by exact_mod_cast hξ_ne
    rw [MeasureTheory.eLpNorm_const (μ := P) (c := c) (p := (ξ : ENNReal))
      hξ_enn_ne_zero hμ_ne_zero]
    simp [IsProbabilityMeasure.measure_univ, Real.norm_eq_abs]
  have hconst_ne_top :
      eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P ≠ ⊤ :=
    hconst_mem.2.ne
  have hsum_ne_top :
      eLpNorm X (ξ : ENNReal) P +
          eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hmem_p.2.ne, hconst_ne_top⟩
  have hsub_le :
      eLpNorm (fun a => X a - c) (ξ : ENNReal) P ≤
        eLpNorm X (ξ : ENNReal) P +
          eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P := by
    simpa [c, Pi.sub_apply] using!
      eLpNorm_sub_le hX_meas.aestronglyMeasurable
        (aestronglyMeasurable_const (μ := P) (b := c))
        (by exact_mod_cast hξ)
  calc
    annealedMomentRoot P ξ (fun a => |X a - ∫ b, X b ∂P|)
        = ENNReal.toReal (eLpNorm (fun a => X a - c) (ξ : ENNReal) P) := by
          simp [hcenter_toReal, c]
    _ ≤ ENNReal.toReal
          (eLpNorm X (ξ : ENNReal) P +
            eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P) :=
          ENNReal.toReal_mono hsum_ne_top hsub_le
    _ = annealedMomentRoot P ξ (fun a => |X a|) + |c| := by
          rw [ENNReal.toReal_add hmem_p.2.ne hconst_ne_top,
            hX_toReal, hconst_toReal]
    _ ≤ annealedMomentRoot P ξ (fun a => |X a|) +
          annealedMomentRoot P ξ (fun a => |X a|) := by
          gcongr
    _ = 2 * annealedMomentRoot P ξ (fun a => |X a|) := by ring

private theorem centered_abs_sub_integrable_and_momentRoot_le_two_of_abs_le_nonneg
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P] {ξ : ℕ}
    {X Y : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ) (hX_meas : AEMeasurable X P)
    (hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a) (hY_nonneg_forall : ∀ a, 0 ≤ Y a)
    (hXY : (fun a => |X a|) ≤ᵐ[P] Y)
    (hY_pow_int : Integrable (fun a => Y a ^ ξ) P) :
    Integrable (fun a => |X a - ∫ b, X b ∂P| ^ ξ) P ∧
      (∫ a, |X a - ∫ b, X b ∂P| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤
        2 * annealedMomentRoot P ξ Y := by
  have hX_abs_pow_int : Integrable (fun a => |X a| ^ ξ) P :=
    integrable_abs_pow_of_ae_abs_le_nonneg hX_meas hY_nonneg hXY hY_pow_int
  have hcenter_int : Integrable (fun a => |X a - ∫ b, X b ∂P| ^ ξ) P := by
    have hcenter_mem : MemLp (fun a => X a - ∫ b, X b ∂P) (ξ : ENNReal) P := by
      have hξ_ne : ξ ≠ 0 := by omega
      have hmem_p : MemLp X (ξ : ENNReal) P := by
        rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
          (by exact_mod_cast hξ_ne) (by simp)]
        simpa [Real.norm_eq_abs] using hX_abs_pow_int
      exact hmem_p.sub (memLp_const (∫ b, X b ∂P))
    have hξ_ne : (ξ : ENNReal) ≠ 0 := by
      have hnat : ξ ≠ 0 := by omega
      exact_mod_cast hnat
    have hξ_top : (ξ : ENNReal) ≠ ⊤ := by simp
    have hint := hcenter_mem.integrable_norm_rpow hξ_ne hξ_top
    simpa [Real.norm_eq_abs] using hint
  constructor
  · exact hcenter_int
  · have hroot :=
      annealedMomentRoot_abs_sub_integral_le_two_mul
        (P := P) (ξ := ξ) (X := X) hξ hX_meas hX_abs_pow_int
    have hUncentered :
        annealedMomentRoot P ξ (fun a => |X a|) ≤ annealedMomentRoot P ξ Y :=
      annealedMomentRoot_abs_le_of_ae_abs_le_nonneg
        (P := P) (ξ := ξ) (X := X) (Y := Y)
        hξ hY_nonneg_forall hXY hX_abs_pow_int hY_pow_int
    calc
      (∫ a, |X a - ∫ b, X b ∂P| ^ ξ ∂P) ^ (1 / (ξ : ℝ))
          ≤ 2 * annealedMomentRoot P ξ (fun a => |X a|) := by
            simpa [annealedMomentRoot] using hroot
      _ ≤ 2 * annealedMomentRoot P ξ Y := by
            exact mul_le_mul_of_nonneg_left hUncentered (by norm_num)

/-- Unit-scale centered upper-left entries have their `L^ξ` roots controlled
by the unit upper multiscale ellipticity moment. -/
theorem restrictionCenteredOriginObservable_upperLeft_entry_momentRoot_le_two_LambdaMomentAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {s : ℝ} {ξ : ℕ} (hs : 0 < s) (hξ : 1 ≤ ξ)
    (hUpperPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (LambdaSqCoeffField (originCube d 0) s (.finite 1) a) ^ ξ) P)
    (i j : Fin d) :
    Integrable
        (fun a =>
          |restrictionCenteredOriginObservable P 0
            (fun U a => (coarseBlockMatrix U a).upperLeft i j) a| ^ ξ) P ∧
      (∫ a,
          |restrictionCenteredOriginObservable P 0
            (fun U a => (coarseBlockMatrix U a).upperLeft i j) a| ^ ξ ∂P) ^
          (1 / (ξ : ℝ)) ≤
        2 * LambdaMomentAtScale P 0 s ξ := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : RegCoeffField d → ℝ :=
    fun a => (coarseBlockMatrix (cubeSet (originCube d 0)) a).upperLeft i j
  let Y : RegCoeffField d → ℝ :=
    fun a => LambdaSqCoeffField (originCube d 0) s (.finite 1) a
  have hX_meas : AEMeasurable X P := by
    simpa [X] using hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
      (originCube d 0) i j
  have hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a :=
    Filter.Eventually.of_forall fun a =>
      LambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
        (by norm_num : (1 : ℝ) ≤ 1)
  have hY_nonneg_forall : ∀ a, 0 ≤ Y a := fun a =>
    LambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
      (by norm_num : (1 : ℝ) ≤ 1)
  have hXY : (fun a => |X a|) ≤ᵐ[P] Y := by
    simpa [X, Y] using
      upperLeft_abs_entry_le_LambdaSqCoeffField_ae hP (originCube d 0) hs i j
  simpa [restrictionCenteredOriginObservable, X, Y, LambdaMomentAtScale] using
    centered_abs_sub_integrable_and_momentRoot_le_two_of_abs_le_nonneg
      (P := P) (ξ := ξ) (X := X) (Y := Y)
      hξ hX_meas hY_nonneg hY_nonneg_forall hXY
      (by simpa [Y] using hUpperPowInt)

/-- Unit-scale centered lower-right entries have their `L^ξ` roots controlled
by the unit lower inverse multiscale ellipticity moment. -/
theorem restrictionCenteredOriginObservable_lowerRight_entry_momentRoot_le_two_lambdaInvMomentAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {s : ℝ} {ξ : ℕ} (hs : 0 < s) (hξ : 1 ≤ ξ)
    (hLowerPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹) ^ ξ) P)
    (i j : Fin d) :
    Integrable
        (fun a =>
          |restrictionCenteredOriginObservable P 0
            (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^ ξ) P ∧
      (∫ a,
          |restrictionCenteredOriginObservable P 0
            (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^ ξ ∂P) ^
          (1 / (ξ : ℝ)) ≤
        2 * lambdaInvMomentAtScale P 0 s ξ := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : RegCoeffField d → ℝ :=
    fun a => (coarseBlockMatrix (cubeSet (originCube d 0)) a).lowerRight i j
  let Y : RegCoeffField d → ℝ :=
    fun a => (lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹
  have hX_meas : AEMeasurable X P := by
    simpa [X] using hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
      (originCube d 0) i j
  have hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a :=
    Filter.Eventually.of_forall fun a =>
      inv_nonneg.mpr
        (lambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
          (by norm_num : (1 : ℝ) ≤ 1))
  have hY_nonneg_forall : ∀ a, 0 ≤ Y a := fun a =>
    inv_nonneg.mpr
      (lambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
        (by norm_num : (1 : ℝ) ≤ 1))
  have hXY : (fun a => |X a|) ≤ᵐ[P] Y := by
    simpa [X, Y] using
      lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae hP (originCube d 0) hs i j
  simpa [restrictionCenteredOriginObservable, X, Y, lambdaInvMomentAtScale] using
    centered_abs_sub_integrable_and_momentRoot_le_two_of_abs_le_nonneg
      (P := P) (ξ := ξ) (X := X) (Y := Y)
      hξ hX_meas hY_nonneg hY_nonneg_forall hXY
      (by simpa [Y] using hLowerPowInt)


end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
