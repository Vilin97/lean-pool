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

/-! # Helpers -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Matrix.Norms.Elementwise Matrix.Norms.L2Operator BigOperators

/-!
# Moment factor bounds

This file exposes Chapter 4 scalar factor bounds used to compare the structural
contrast `Theta_n` with the moment-enhanced quantity `widetildeTheta_n`.
-/

noncomputable section

/-- Proof-local primitive scalarization data at every nonnegative scale. -/
abbrev AnnealedPrimitiveScalarizationFamily {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) : Prop :=
  ∀ n : ℕ, Internal.AnnealedPrimitiveScalarizationData (d := d) P (n : ℤ)

/-- Proof-local scalar factor bounds used to compare `Theta_n` with
`widetildeTheta_n` internally. -/
structure AnnealedPrimitiveMomentFactorBounds {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (sUpper sLower : ℝ) (ξ : ℕ) : Prop where
  upper :
    ∀ (primitive : AnnealedPrimitiveScalarizationFamily (d := d) P) (n : ℕ),
      Internal.barBAtScaleOfPrimitive (primitive n) ≤
        LambdaMomentAtScale P (n : ℤ) sUpper ξ
  lower :
    ∀ (primitive : AnnealedPrimitiveScalarizationFamily (d := d) P) (n : ℕ),
      Internal.barSigmaStarInvAtScaleOfPrimitive (primitive n) ≤
        lambdaInvMomentAtScale P (n : ℤ) sLower ξ

theorem toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hmem : MemLp f (p : ENNReal) μ) :
    ENNReal.toReal (eLpNorm f (p : ENNReal) μ) =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_ne : p ≠ 0 := by omega
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hp_ne) (by simp)]
  have hnonneg :
      0 ≤ (∫ x, ‖f x‖ ^ (p : ENNReal).toReal ∂μ) ^
        (p : ENNReal).toReal⁻¹ := by
    positivity
  rw [ENNReal.toReal_ofReal hnonneg]
  simp [one_div]

theorem integrable_of_ae_nonneg_pow_integrable
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ) (hX_meas : AEMeasurable X P)
    (hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a)
    (hXpow_int : Integrable (fun a => X a ^ ξ) P) :
    Integrable X P := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hnormpow_int : Integrable (fun a => ‖X a‖ ^ ξ) P := by
    refine hXpow_int.congr ?_
    filter_upwards [hX_nonneg] with a ha
    simp [Real.norm_eq_abs, abs_of_nonneg ha]
  have hmem_p : MemLp X (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa using hnormpow_int
  have hmem_one : MemLp X (1 : ENNReal) P := by
    exact hmem_p.mono_exponent (by exact_mod_cast hξ)
  rwa [MeasureTheory.memLp_one_iff_integrable] at hmem_one

theorem integral_le_annealedMomentRoot_of_ae_nonneg
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ) (hX_meas : AEMeasurable X P)
    (hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a)
    (hXpow_int : Integrable (fun a => X a ^ ξ) P) :
    ∫ a, X a ∂P ≤ annealedMomentRoot P ξ X := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hnormpow_int : Integrable (fun a => ‖X a‖ ^ ξ) P := by
    refine hXpow_int.congr ?_
    filter_upwards [hX_nonneg] with a ha
    simp [Real.norm_eq_abs, abs_of_nonneg ha]
  have hmem_p : MemLp X (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa using hnormpow_int
  have hmem_one : MemLp X (1 : ENNReal) P := by
    exact hmem_p.mono_exponent (by exact_mod_cast hξ)
  have hX_int : Integrable X P := by
    rwa [MeasureTheory.memLp_one_iff_integrable] at hmem_one
  have hX_norm_int : Integrable (fun a => ‖X a‖) P := hX_int.norm
  have hint_le_norm : ∫ a, X a ∂P ≤ ∫ a, ‖X a‖ ∂P := by
    exact integral_mono_ae hX_int hX_norm_int
      (Filter.Eventually.of_forall fun a => by
        simpa [Real.norm_eq_abs] using le_abs_self (X a))
  have hcmp :
      eLpNorm X (1 : ENNReal) P ≤ eLpNorm X (ξ : ENNReal) P := by
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (μ := P) (f := X) (by exact_mod_cast hξ) hX_meas.aestronglyMeasurable
  have hcmp_toReal :
      ENNReal.toReal (eLpNorm X (1 : ENNReal) P) ≤
        ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) := by
    exact ENNReal.toReal_mono hmem_p.2.ne hcmp
  have hL1 :
      ENNReal.toReal (eLpNorm X (1 : ENNReal) P) = ∫ a, ‖X a‖ ∂P := by
    calc
      ENNReal.toReal (eLpNorm X (1 : ENNReal) P)
          = (∫ a, ‖X a‖ ^ (1 : ℕ) ∂P) ^ (1 / (1 : ℝ)) := by
            simpa using
              (toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
                (μ := P) (f := X) (p := 1) (by norm_num) (by simpa using hmem_one))
      _ = ∫ a, ‖X a‖ ∂P := by simp
  have hLp :
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) =
        annealedMomentRoot P ξ X := by
    calc
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P)
          = (∫ a, ‖X a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := X) (p := ξ) hξ hmem_p
      _ = (∫ a, X a ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            congr 1
            exact integral_congr_ae (by
              filter_upwards [hX_nonneg] with a ha
              simp [Real.norm_eq_abs, abs_of_nonneg ha])
      _ = annealedMomentRoot P ξ X := rfl
  calc
    ∫ a, X a ∂P ≤ ∫ a, ‖X a‖ ∂P := hint_le_norm
    _ = ENNReal.toReal (eLpNorm X (1 : ENNReal) P) := hL1.symm
    _ ≤ ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) := hcmp_toReal
    _ = annealedMomentRoot P ξ X := hLp

namespace RestrictionLawCarrier

theorem finsetSup_abs_restrictionCenteredDescendantAverageOnCube_nonneg
    {d : ℕ} {n : ℤ} {P : RestrictionCoeffLaw d}
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    (X : Set (Vec d) → RegCoeffField d → ℝ) (a : RegCoeffField d) :
    0 ≤ parents.sup' hparents
      (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) := by
  rcases hparents with ⟨Q0, hQ0⟩
  exact (abs_nonneg (restrictionCenteredDescendantAverageOnCube P Q0 n X a)).trans
    (Finset.le_sup'
      (f := fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|) hQ0)

theorem aemeasurable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube
    {d : ℕ} {n : ℤ} {P : RestrictionCoeffLaw d}
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_desc_aemeas :
      ∀ Q ∈ parents, ∀ R ∈ descendantsAtScale Q n,
        AEMeasurable (X (cubeSet R)) P) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        parents.sup' hparents
          (fun Q => |restrictionCenteredDescendantAverageOnCube P Q n X a|)) P := by
  have h :
      AEMeasurable
        (parents.sup' hparents
          (fun Q (a : RegCoeffField d) =>
            |restrictionCenteredDescendantAverageOnCube P Q n X a|)) P := by
    refine aemeasurable_finset_sup' (μ := P) (s := parents) hparents ?_
    intro Q hQ
    have havg :
        AEMeasurable
          (fun a : RegCoeffField d => restrictionCenteredDescendantAverageOnCube P Q n X a) P := by
      unfold restrictionCenteredDescendantAverageOnCube
      have hsum :
          AEMeasurable
            (fun a =>
              ∑ R ∈ descendantsAtScale Q n,
                (X (cubeSet R) a - ∫ b, X (cubeSet (originCube d n)) b ∂P)) P := by
        have hsum' : AEMeasurable
            (∑ R ∈ descendantsAtScale Q n,
              fun a => X (cubeSet R) a -
                ∫ b, X (cubeSet (originCube d n)) b ∂P) P :=
          Finset.aemeasurable_sum _ fun R hR =>
            (hX_desc_aemeas Q hQ R hR).sub aemeasurable_const
        convert hsum' using 1
        ext a
        simp
      exact aemeasurable_const.mul hsum
    simpa [Real.norm_eq_abs] using havg.norm
  convert h using 1
  ext a
  exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hparents
    (fun Q (a : RegCoeffField d) =>
      |restrictionCenteredDescendantAverageOnCube P Q n X a|) a).symm

/-- AEMeasurability of the upper-left finite-parent positive excess for the
operator norm of coarse blocks. -/
theorem aemeasurable_upperLeft_matrixNorm_positiveExcess_finsetSup
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    (center : Mat d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                Ch02.matrixNorm center)
              0)) P := by
  have h :
      AEMeasurable
        (parents.sup' hparents
          (fun Q (a : RegCoeffField d) =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                Ch02.matrixNorm center)
              0)) P := by
    refine aemeasurable_finset_sup' (μ := P) (s := parents) hparents ?_
    intro Q _hQ
    have hNorm :
        AEMeasurable
          (fun a : RegCoeffField d =>
            Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft) P := by
      simpa [Ch02.matrixNorm, Real.norm_eq_abs] using!
        (hP.aemeasurable_coarseB_cubeSet Q).norm
    exact (hNorm.sub aemeasurable_const).max aemeasurable_const
  convert h using 1
  ext a
  exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hparents
    (fun Q (a : RegCoeffField d) =>
      max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
          Ch02.matrixNorm center)
        0) a).symm

/-- AEMeasurability of the lower-right finite-parent positive excess for the
operator norm of coarse blocks. -/
theorem aemeasurable_lowerRight_matrixNorm_positiveExcess_finsetSup
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    (center : Mat d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm center)
              0)) P := by
  have h :
      AEMeasurable
        (parents.sup' hparents
          (fun Q (a : RegCoeffField d) =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm center)
              0)) P := by
    refine aemeasurable_finset_sup' (μ := P) (s := parents) hparents ?_
    intro Q _hQ
    have hNorm :
        AEMeasurable
          (fun a : RegCoeffField d =>
            Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight) P := by
      simpa [Ch02.matrixNorm, Real.norm_eq_abs] using!
        (hP.aemeasurable_coarseSigmaStarInv_cubeSet Q).norm
    exact (hNorm.sub aemeasurable_const).max aemeasurable_const
  convert h using 1
  ext a
  exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hparents
    (fun Q (a : RegCoeffField d) =>
      max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
          Ch02.matrixNorm center)
        0) a).symm

private theorem finset_univ_pair_sum_eq_sum_sum
    {d : ℕ} (f : Fin d → Fin d → ℝ) :
    (∑ ij : Fin d × Fin d, f ij.1 ij.2) =
      ∑ i : Fin d, ∑ j : Fin d, f i j := by
  classical
  simpa [Finset.univ_product_univ] using
    (Finset.sum_product'
      (s := (Finset.univ : Finset (Fin d)))
      (t := (Finset.univ : Finset (Fin d)))
      (f := fun i j => f i j))

private theorem integrable_abs_pow_excess_of_ae_nonneg_le_entry_sum
    {d : ℕ} {P : RestrictionCoeffLaw d} {ξ : ℕ}
    (hξ : 1 ≤ ξ)
    (excess : RegCoeffField d → ℝ)
    (entry : Fin d → Fin d → RegCoeffField d → ℝ)
    (hexcess_nonneg : ∀ a, 0 ≤ excess a)
    (hexcess_aemeas : AEMeasurable excess P)
    (hentry_nonneg : ∀ i j a, 0 ≤ entry i j a)
    (hentry_aemeas : ∀ i j, AEMeasurable (entry i j) P)
    (hentry_int :
      ∀ i j, Integrable (fun a => |entry i j a| ^ ξ) P)
    (hpoint :
      excess ≤ᵐ[P] fun a => ∑ i : Fin d, ∑ j : Fin d, entry i j a) :
    Integrable (fun a => |excess a| ^ ξ) P := by
  classical
  let s : Finset (Fin d × Fin d) := Finset.univ
  let entryPair : Fin d × Fin d → RegCoeffField d → ℝ :=
    fun ij a => entry ij.1 ij.2 a
  let entrySum : RegCoeffField d → ℝ :=
    fun a => ∑ ij ∈ s, entryPair ij a
  have hξ_ne_zero : ξ ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hξ)
  have hentryPair_nonneg : ∀ ij a, 0 ≤ entryPair ij a := by
    intro ij a
    exact hentry_nonneg ij.1 ij.2 a
  have hentryPair_aemeas : ∀ ij ∈ s, AEMeasurable (entryPair ij) P := by
    intro ij _hij
    exact hentry_aemeas ij.1 ij.2
  have hentryPair_int :
      ∀ ij ∈ s, Integrable (fun a => |entryPair ij a| ^ ξ) P := by
    intro ij _hij
    exact hentry_int ij.1 ij.2
  have hentryPair_memLp :
      ∀ ij ∈ s, MemLp (entryPair ij) (ξ : ENNReal) P := by
    intro ij hij
    rw [← integrable_norm_rpow_iff
      (hentryPair_aemeas ij hij).aestronglyMeasurable
      (by exact_mod_cast hξ_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hentryPair_int ij hij
  have hentrySum_memLp : MemLp entrySum (ξ : ENNReal) P := by
    have hsum : MemLp (fun a => ∑ ij ∈ s, entryPair ij a) (ξ : ENNReal) P :=
      memLp_finsetSum s hentryPair_memLp
    simpa [entrySum] using hsum
  have hentrySum_abs_int :
      Integrable (fun a => |entrySum a| ^ ξ) P := by
    simpa [entrySum, Real.norm_eq_abs] using
      hentrySum_memLp.integrable_norm_pow hξ_ne_zero
  have hentrySum_nonneg : ∀ a, 0 ≤ entrySum a := by
    intro a
    exact Finset.sum_nonneg fun ij _hij => hentryPair_nonneg ij a
  have hpoint_pair : excess ≤ᵐ[P] entrySum := by
    filter_upwards [hpoint] with a ha
    show excess a ≤ ∑ ij : Fin d × Fin d, entry ij.1 ij.2 a
    have hpair_eq :
        (∑ ij : Fin d × Fin d, entry ij.1 ij.2 a) =
          ∑ i : Fin d, ∑ j : Fin d, entry i j a :=
      finset_univ_pair_sum_eq_sum_sum (fun i j => entry i j a)
    rw [hpair_eq]
    exact ha
  refine Integrable.mono' hentrySum_abs_int
    (hexcess_aemeas.norm.pow_const ξ).aestronglyMeasurable ?_
  filter_upwards [hpoint_pair] with a ha
  have hx : 0 ≤ excess a := hexcess_nonneg a
  have hy : 0 ≤ entrySum a := hentrySum_nonneg a
  have hpow : |excess a| ^ ξ ≤ |entrySum a| ^ ξ := by
    simpa [abs_of_nonneg hx, abs_of_nonneg hy] using
      pow_le_pow_left₀ hx ha ξ
  have hleft_nonneg : 0 ≤ |excess a| ^ ξ :=
    pow_nonneg (abs_nonneg (excess a)) ξ
  have hright_nonneg : 0 ≤ |entrySum a| ^ ξ :=
    pow_nonneg (abs_nonneg (entrySum a)) ξ
  simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg,
    abs_of_nonneg hright_nonneg] using hpow

theorem momentRoot_excess_le_card_mul_entryRootBound
    {d : ℕ} {P : RestrictionCoeffLaw d} {ξ : ℕ} {C : ℝ}
    (hξ : 1 ≤ ξ)
    (excess : RegCoeffField d → ℝ)
    (entry : Fin d → Fin d → RegCoeffField d → ℝ)
    (hexcess_nonneg : ∀ a, 0 ≤ excess a)
    (hexcess_aemeas : AEMeasurable excess P)
    (hentry_nonneg : ∀ i j a, 0 ≤ entry i j a)
    (hentry_aemeas : ∀ i j, AEMeasurable (entry i j) P)
    (hentry_int :
      ∀ i j, Integrable (fun a => |entry i j a| ^ ξ) P)
    (hentry_root :
      ∀ i j,
        (∫ a, |entry i j a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤ C)
    (hpoint :
      excess ≤ᵐ[P] fun a => ∑ i : Fin d, ∑ j : Fin d, entry i j a) :
    annealedMomentRoot P ξ excess ≤
      ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) * C := by
  classical
  let s : Finset (Fin d × Fin d) := Finset.univ
  let entryPair : Fin d × Fin d → RegCoeffField d → ℝ :=
    fun ij a => entry ij.1 ij.2 a
  let entrySum : RegCoeffField d → ℝ :=
    fun a => ∑ ij ∈ s, entryPair ij a
  have hξ_ne_zero : ξ ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hξ)
  have hentryPair_nonneg : ∀ ij a, 0 ≤ entryPair ij a := by
    intro ij a
    exact hentry_nonneg ij.1 ij.2 a
  have hentryPair_aemeas : ∀ ij ∈ s, AEMeasurable (entryPair ij) P := by
    intro ij _hij
    exact hentry_aemeas ij.1 ij.2
  have hentryPair_int :
      ∀ ij ∈ s, Integrable (fun a => |entryPair ij a| ^ ξ) P := by
    intro ij _hij
    exact hentry_int ij.1 ij.2
  have hentryPair_root :
      ∀ ij ∈ s,
        (∫ a, |entryPair ij a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤ C := by
    intro ij _hij
    exact hentry_root ij.1 ij.2
  have hentryPair_memLp :
      ∀ ij ∈ s, MemLp (entryPair ij) (ξ : ENNReal) P := by
    intro ij hij
    rw [← integrable_norm_rpow_iff
      (hentryPair_aemeas ij hij).aestronglyMeasurable
      (by exact_mod_cast hξ_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hentryPair_int ij hij
  have hentrySum_memLp : MemLp entrySum (ξ : ENNReal) P := by
    have hsum : MemLp (fun a => ∑ ij ∈ s, entryPair ij a) (ξ : ENNReal) P :=
      memLp_finsetSum s hentryPair_memLp
    simpa [entrySum] using hsum
  have hentrySum_abs_int :
      Integrable (fun a => |entrySum a| ^ ξ) P := by
    simpa [entrySum, Real.norm_eq_abs] using
      hentrySum_memLp.integrable_norm_pow hξ_ne_zero
  have hentrySum_nonneg : ∀ a, 0 ≤ entrySum a := by
    intro a
    exact Finset.sum_nonneg fun ij _hij => hentryPair_nonneg ij a
  have hentrySum_int :
      Integrable (fun a => entrySum a ^ ξ) P := by
    refine hentrySum_abs_int.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hentrySum_nonneg a)]
  have hpoint_pair : excess ≤ᵐ[P] entrySum := by
    filter_upwards [hpoint] with a ha
    show excess a ≤ ∑ ij : Fin d × Fin d, entry ij.1 ij.2 a
    have hpair_eq :
        (∑ ij : Fin d × Fin d, entry ij.1 ij.2 a) =
          ∑ i : Fin d, ∑ j : Fin d, entry i j a :=
      finset_univ_pair_sum_eq_sum_sum (fun i j => entry i j a)
    rw [hpair_eq]
    exact ha
  have hexcess_int :
      Integrable (fun a => excess a ^ ξ) P := by
    refine Integrable.mono' hentrySum_int
      (hexcess_aemeas.pow_const ξ).aestronglyMeasurable ?_
    filter_upwards [hpoint_pair] with a ha
    have hx : 0 ≤ excess a := hexcess_nonneg a
    have hy : 0 ≤ entrySum a := hentrySum_nonneg a
    have hpow : excess a ^ ξ ≤ entrySum a ^ ξ :=
      pow_le_pow_left₀ hx ha ξ
    have hleft_abs : |excess a| = excess a := abs_of_nonneg hx
    have hright_abs : |entrySum a ^ ξ| = entrySum a ^ ξ :=
      abs_of_nonneg (pow_nonneg hy ξ)
    simpa [Real.norm_eq_abs, hleft_abs, hright_abs] using hpow
  have hroot_excess_sum :
      annealedMomentRoot P ξ excess ≤ annealedMomentRoot P ξ entrySum :=
    annealedMomentRoot_le_of_ae_nonneg_le hξ hexcess_nonneg hexcess_int hentrySum_int hpoint_pair
  have htriangle :
      (∫ a, |entrySum a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤
        ∑ ij ∈ s, (∫ a, |entryPair ij a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
    simpa [entrySum] using
      integral_abs_finsetSum_pow_rpow_inv_le_sum_aemeasurable
        (μ := P) (s := s) (p := ξ) hξ hentryPair_aemeas hentryPair_int
  have hsum_roots :
      ∑ ij ∈ s, (∫ a, |entryPair ij a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) * C := by
    calc
      ∑ ij ∈ s, (∫ a, |entryPair ij a| ^ ξ ∂P) ^ (1 / (ξ : ℝ))
          ≤ ∑ ij ∈ s, C := by
            exact Finset.sum_le_sum hentryPair_root
      _ = ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) * C := by
            simp [s, Finset.sum_const, nsmul_eq_mul, Fintype.card_prod]
  have hentryRoot :
      annealedMomentRoot P ξ entrySum ≤
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) * C := by
    calc
      annealedMomentRoot P ξ entrySum
          = (∫ a, |entrySum a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
              unfold annealedMomentRoot
              congr 1
              exact integral_congr_ae (Filter.Eventually.of_forall fun a => by
                simp [abs_of_nonneg (hentrySum_nonneg a)])
      _ ≤ ∑ ij ∈ s,
            (∫ a, |entryPair ij a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := htriangle
      _ ≤ ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) * C :=
            hsum_roots
  exact hroot_excess_sum.trans hentryRoot

/-- Integrability of the upper-left finite-parent operator-norm positive
excess.  This is the integrability half of
`upperLeft_matrixNorm_positiveExcess_finsetSup_momentRoot_le_of_restrictionUnitRangeDependentLaw`. -/
theorem upperLeft_matrixNorm_positiveExcess_finsetSup_integrable_abs_pow_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {n : ℤ} {ξ : ℕ}
    (hn : 0 ≤ n)
    (hparent_scale : ∀ Q ∈ parents, n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P)
    (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d n)) b).upperLeft i j ∂P)
    (hξ : 2 ≤ ξ)
    (hOriginLp_int :
      ∀ i j : Fin d,
        Integrable
          (fun a =>
            |restrictionCenteredOriginObservable P n
              (fun U a => (coarseBlockMatrix U a).upperLeft i j) a| ^ ξ) P) :
    Integrable
      (fun a =>
        ‖(parents.sup' hparents
            (fun Q =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                  Ch02.matrixNorm center)
                0))‖ ^ ξ) P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let excess : RegCoeffField d → ℝ :=
    fun a =>
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
              Ch02.matrixNorm center)
            0)
  let entry : Fin d → Fin d → RegCoeffField d → ℝ :=
    fun i j a =>
      parents.sup' hparents
        (fun Q =>
          |restrictionCenteredDescendantAverageOnCube P Q n
            (fun U a => (coarseBlockMatrix U a).upperLeft i j) a|)
  have hξ_one : 1 ≤ ξ := by omega
  have hexcess_nonneg : ∀ a, 0 ≤ excess a := by
    intro a
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right _ _).trans
      (Finset.le_sup'
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
              Ch02.matrixNorm center)
            0) hQ0)
  have hentry_nonneg : ∀ i j a, 0 ≤ entry i j a := by
    intro i j a
    exact finsetSup_abs_restrictionCenteredDescendantAverageOnCube_nonneg hparents
      (fun U a => (coarseBlockMatrix U a).upperLeft i j) a
  have hexcess_aemeas : AEMeasurable excess P := by
    simpa [excess] using
      aemeasurable_upperLeft_matrixNorm_positiveExcess_finsetSup hP hparents center
  have hentry_aemeas : ∀ i j, AEMeasurable (entry i j) P := by
    intro i j
    simpa [entry] using
      aemeasurable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube
        (P := P) (n := n) hparents
        (fun U a => (coarseBlockMatrix U a).upperLeft i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet R i j)
  have hentry_int :
      ∀ i j, Integrable (fun a => |entry i j a| ^ ξ) P := by
    intro i j
    have hint :
        Integrable
          (fun a : RegCoeffField d =>
            (parents.sup' hparents
              (fun Q =>
                |restrictionCenteredDescendantAverageOnCube P Q n
                  (fun U a => (coarseBlockMatrix U a).upperLeft i j) a|)) ^ ξ) P :=
      integrable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_of_stationary
        (d := d) (n := n) (P := P) (parents := parents) hparents
        hn hparent_scale hPstat
        (fun U a => (coarseBlockMatrix U a).upperLeft i j)
        (by
          simpa [blockMatEntry] using
            isRestrictionTranslationCovariant_comp_toFun
              (coarseBlockMatrix_entry_translation_covariant (Sum.inl i) (Sum.inl j)))
        (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet (originCube d n) i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet R i j)
        hξ_one (hOriginLp_int i j)
    refine hint.congr ?_
    filter_upwards with a
    simp [entry, abs_of_nonneg (hentry_nonneg i j a)]
  have hpoint :
      excess ≤ᵐ[P] fun a => ∑ i : Fin d, ∑ j : Fin d, entry i j a := by
    simpa [excess, entry] using
      hP.coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_finsetSup_le_sum_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_ae
        hparents hparent_scale center hcenter
  simpa [excess, Real.norm_eq_abs] using
    integrable_abs_pow_excess_of_ae_nonneg_le_entry_sum
      (P := P) (ξ := ξ) hξ_one excess entry hexcess_nonneg
      hexcess_aemeas hentry_nonneg hentry_aemeas hentry_int hpoint

/-- Upper-left finite-parent coarse-block fluctuation bound, stated directly
against the law-facing Ch4 surface.  The proof owns all locality,
measurability, covariance, and deterministic positive-excess domination. -/
theorem upperLeft_matrixNorm_positiveExcess_finsetSup_momentRoot_le_of_restrictionUnitRangeDependentLaw
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
            (coarseBlockMatrix (cubeSet (originCube d n)) b).upperLeft i j ∂P)
    (hξ : 2 ≤ ξ) (hK_nonneg : 0 ≤ K) (hB_nonneg : 0 ≤ B)
    (hOriginLp_int :
      ∀ i j : Fin d,
        Integrable
          (fun a =>
            |restrictionCenteredOriginObservable P n
              (fun U a => (coarseBlockMatrix U a).upperLeft i j) a| ^ ξ) P)
    (hOriginLp :
      ∀ i j : Fin d,
        (∫ a,
            |restrictionCenteredOriginObservable P n
              (fun U a => (coarseBlockMatrix U a).upperLeft i j) a| ^ ξ ∂P) ^
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
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
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
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
              Ch02.matrixNorm center)
            0)
  let entry : Fin d → Fin d → RegCoeffField d → ℝ :=
    fun i j a =>
      parents.sup' hparents
        (fun Q =>
          |restrictionCenteredDescendantAverageOnCube P Q n
            (fun U a => (coarseBlockMatrix U a).upperLeft i j) a|)
  have hξ_one : 1 ≤ ξ := by omega
  have hexcess_nonneg : ∀ a, 0 ≤ excess a := by
    intro a
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right _ _).trans
      (Finset.le_sup'
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
              Ch02.matrixNorm center)
            0) hQ0)
  have hentry_nonneg : ∀ i j a, 0 ≤ entry i j a := by
    intro i j a
    exact finsetSup_abs_restrictionCenteredDescendantAverageOnCube_nonneg hparents
      (fun U a => (coarseBlockMatrix U a).upperLeft i j) a
  have hexcess_aemeas : AEMeasurable excess P := by
    simpa [excess] using
      aemeasurable_upperLeft_matrixNorm_positiveExcess_finsetSup hP hparents center
  have hentry_aemeas : ∀ i j, AEMeasurable (entry i j) P := by
    intro i j
    simpa [entry] using
      aemeasurable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube
        (P := P) (n := n) hparents
        (fun U a => (coarseBlockMatrix U a).upperLeft i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet R i j)
  have hentry_int :
      ∀ i j, Integrable (fun a => |entry i j a| ^ ξ) P := by
    intro i j
    have hint :
        Integrable
          (fun a : RegCoeffField d =>
            (parents.sup' hparents
              (fun Q =>
                |restrictionCenteredDescendantAverageOnCube P Q n
                  (fun U a => (coarseBlockMatrix U a).upperLeft i j) a|)) ^ ξ) P :=
      integrable_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_pow_of_stationary
        (d := d) (n := n) (P := P) (parents := parents) hparents
        hn hparent_scale hPstat
        (fun U a => (coarseBlockMatrix U a).upperLeft i j)
        (by
          simpa [blockMatEntry] using
            isRestrictionTranslationCovariant_comp_toFun
              (coarseBlockMatrix_entry_translation_covariant (Sum.inl i) (Sum.inl j)))
        (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet (originCube d n) i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet R i j)
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
        (fun U a => (coarseBlockMatrix U a).upperLeft i j)
        (fun Q hQ R hR =>
          hP.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperLeft_apply_cubeSet R i j)
        (by
          simpa [blockMatEntry] using
            isRestrictionTranslationCovariant_comp_toFun
              (coarseBlockMatrix_entry_translation_covariant (Sum.inl i) (Sum.inl j)))
        (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet (originCube d n) i j)
        (fun Q hQ R hR =>
          hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet R i j)
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
      hP.coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_finsetSup_le_sum_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_ae
        hparents hparent_scale center hcenter
  simpa [excess, entry, C] using
    momentRoot_excess_le_card_mul_entryRootBound
      (P := P) (ξ := ξ) (C := C) hξ_one
      excess entry hexcess_nonneg hexcess_aemeas hentry_nonneg
      hentry_aemeas hentry_int hentry_root hpoint

/-- Integrability of the lower-right finite-parent operator-norm positive
excess.  This is the integrability half of
`lowerRight_matrixNorm_positiveExcess_finsetSup_momentRoot_le_of_restrictionUnitRangeDependentLaw`. -/
theorem lowerRight_matrixNorm_positiveExcess_finsetSup_integrable_abs_pow_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {n : ℤ} {ξ : ℕ}
    (hn : 0 ≤ n)
    (hparent_scale : ∀ Q ∈ parents, n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P)
    (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d n)) b).lowerRight i j ∂P)
    (hξ : 2 ≤ ξ)
    (hOriginLp_int :
      ∀ i j : Fin d,
        Integrable
          (fun a =>
            |restrictionCenteredOriginObservable P n
              (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^ ξ) P) :
    Integrable
      (fun a =>
        ‖(parents.sup' hparents
            (fun Q =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                  Ch02.matrixNorm center)
                0))‖ ^ ξ) P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
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
  have hpoint :
      excess ≤ᵐ[P] fun a => ∑ i : Fin d, ∑ j : Fin d, entry i j a := by
    simpa [excess, entry] using
      hP.coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_finsetSup_le_sum_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_ae
        hparents hparent_scale center hcenter
  simpa [excess, Real.norm_eq_abs] using
    integrable_abs_pow_excess_of_ae_nonneg_le_entry_sum
      (P := P) (ξ := ξ) hξ_one excess entry hexcess_nonneg
      hexcess_aemeas hentry_nonneg hentry_aemeas hentry_int hpoint

end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
