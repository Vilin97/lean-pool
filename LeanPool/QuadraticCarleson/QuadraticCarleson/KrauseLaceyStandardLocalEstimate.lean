/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyEnergyClassification
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPhysicalTailPrefix
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyRademacherMenshov
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPrunedPhysicalMaximal

/-!
# Scalar-standard local estimates

This is the complementary scalar branch of the energy classification. It
uses the proved standard diagonal-energy estimate directly. Cross-scale
orthogonality is not assumed: finite Rademacher--Menshov is applied to the
concrete minimal-generation `Lp` vectors, with the finite cardinality loss
made explicit. Thus the result is a genuine finite physical-tail estimate,
not a sparse or oscillatory conclusion.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers
  KrauseLaceyRademacherMenshov

attribute [local instance] Classical.propDecidable

/-- The sum in L² of the standard bad pieces belonging to one generation. -/
noncomputable def energyStandardGenerationLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ I ∈ generation N n, badPieceLp S f hf I₀ k₀ s scale I

theorem energyStandardGenerationLp_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (n : ℕ) :
    energyStandardGenerationLp S f hf I₀ k₀ s scale N n =ᵐ[volume]
      krauseLaceyCollectionAction (generation N n) scale
        (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by
  apply (Lp.coeFn_finsetSum (generation N n) (badPieceLp S f hf I₀ k₀ s scale)).trans
  have hall : ∀ᵐ x ∂volume, ∀ I ∈ generation N n,
      badPieceLp S f hf I₀ k₀ s scale I x =
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x :=
    (ae_ball_iff (Finset.countable_toSet _)).mpr fun I _ ↦ localizedPieceLp_ae_eq _ _ _ _
  filter_upwards [hall] with x hx
  simp only [Finset.sum_apply, krauseLaceyCollectionAction]
  exact Finset.sum_congr rfl hx

/-- The pointwise maximum of norms of the finite generation-prefix sums. -/
noncomputable def energyStandardGenerationPrefixMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) : ℝ :=
  ⨆ n : Fin (N.card + 1), ‖∑ i ∈ Finset.range n.val,
    krauseLaceyCollectionAction (generation N i) scale
      (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖

theorem energyStandardGenerationPrefixMaximal_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) :
    energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N =ᵐ[volume]
      finitePrefixMaximal N.card (energyStandardGenerationLp S f hf I₀ k₀ s scale N) := by
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      energyStandardGenerationLp S f hf I₀ k₀ s scale N n x =
        krauseLaceyCollectionAction (generation N n) scale
          (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x :=
    ae_all_iff.mpr fun n ↦ energyStandardGenerationLp_ae_eq S f hf I₀ k₀ s scale N n
  filter_upwards [hall] with x hx
  unfold energyStandardGenerationPrefixMaximal finitePrefixMaximal
  apply iSup_congr
  intro n
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ (hx i).symm

/-- The finite signed-sum input required by Rademacher--Menshov follows from
the already proved standard diagonal estimate. The visible `N.card` is the
only loss introduced here; no cross-scale cancellation is asserted. -/
theorem hasSignedSumSquareBound_energyStandardGenerations
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s kmin : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hmin : ∀ I ∈ N, kmin ≤ scale I) :
    HasSignedSumSquareBound N.card
      (energyStandardGenerationLp S f hf I₀ k₀ s scale N)
      ((N.card : ℝ) *
        ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
          (2 : ℝ) ^ (kmin + 2)) * ∫ x, ‖f x‖)) := by
  intro c hc
  change ‖∑ n ∈ Finset.range N.card, c n • ∑ I ∈ generation N n,
    badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤ _
  rw [sum_smul_generations_eq]
  let v := badPieceLp S f hf I₀ k₀ s scale
  have hcoeff (I : RealInterval) (hI : I ∈ N) : |c (generationIndex N I)| ≤ 1 := by
    exact (hc _ (generationIndex_spec hI).1).elim (fun h ↦ by rw [h]; norm_num)
      (fun h ↦ h.elim (fun h ↦ by rw [h]; norm_num) (fun h ↦ by rw [h]; norm_num))
  have hdiag : (∑ I ∈ N, ‖v I‖ ^ 2) ≤
      (2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ (kmin + 2)) * ∫ x, ‖f x‖ := by
    simp_rw [v, badPieceLp, norm_localizedPieceLp_sq]
    exact sum_energyStandard_badPiece_diagonalEnergy_le hf I₀ k₀ s kmin scale hlam hsub
      N hN hmin
  calc
    _ ≤ (∑ I ∈ N, ‖c (generationIndex N I) • v I‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ I ∈ N, ‖v I‖) ^ 2 := by
      gcongr with I hI
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcoeff I hI)
    _ ≤ (N.card : ℝ) * ∑ I ∈ N, ‖v I‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := N) (f := fun I ↦ ‖v I‖)
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (by positivity)

theorem eLpNorm_energyStandardGenerationPrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s kmin : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hmin : ∀ I ∈ N, kmin ≤ scale I) :
    eLpNorm (energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 N.card + 1 : ℝ) * Real.sqrt
        ((N.card : ℝ) * ((2560 * positiveDyadicAmplitudeBound ^ 2 *
          intervalL1Average f I₀ / (2 : ℝ) ^ (kmin + 2)) * ∫ x, ‖f x‖))) := by
  rw [eLpNorm_congr_ae (energyStandardGenerationPrefixMaximal_ae_eq S f hf I₀ k₀ s scale N)]
  apply eLpNorm_finitePrefixMaximal_le_log2 _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt]
  · exact hasSignedSumSquareBound_energyStandardGenerations hf I₀ k₀ s kmin scale
      hlam hsub N hN hmin
  · positivity [intervalL1Average_nonneg f I₀]

/-- The source-oriented physical suffix maximum for the scalar-standard
collection. The subtype keeps the required orientation `ell ≥ k₀ + s`. -/
noncomputable def energyStandardSourceTailMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) : ℝ :=
  ⨆ ell : {ell : ℤ // k₀ + s ≤ ell},
    ‖badLengthTailAction S f I₀ k₀ s scale N ell.1 x‖

theorem energyStandardGenerationPrefixMaximal_nonneg
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) :
    0 ≤ energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N x := by
  have h := le_ciSup (Set.finite_range
    (fun n : Fin (N.card + 1) ↦ ‖∑ i ∈ Finset.range n.val,
      krauseLaceyCollectionAction (generation N i) scale
        (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖)).bddAbove
    (0 : Fin (N.card + 1))
  simpa [energyStandardGenerationPrefixMaximal] using h

theorem norm_energyStandard_tailAction_le_prefix
    {S : Finset RealInterval} {f : ℝ → ℂ} (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (ell : ℤ) (x : ℝ) :
    ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖ ≤
      2 * energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N x := by
  have hSN : N ⊆ S := hN.trans ((Finset.filter_subset _ _).trans
    (energyEligibleIntervals_subset S f I₀ k₀ s scale))
  apply norm_lengthTail_le_two_generationPrefixNormMax N
    (fun I hI J hJ hne ↦ hlam (hSN hI) (hSN hJ) hne) _ ((2 : ℝ) ^ ell) x
  intro I hI hxI
  exact krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hI)).1).2.1 hxI

theorem energyStandardSourceTailMaximal_le_prefix
    {S : Finset RealInterval} {f : ℝ → ℂ} (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    energyStandardSourceTailMaximal S f I₀ k₀ s scale N x ≤
      2 * energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N x :=
  ciSup_le fun ell ↦ norm_energyStandard_tailAction_le_prefix I₀ k₀ s scale hlam N hN ell.1 x

theorem energyStandardSourceTailMaximal_nonneg
    {S : Finset RealInterval} {f : ℝ → ℂ} (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    0 ≤ energyStandardSourceTailMaximal S f I₀ k₀ s scale N x := by
  have hb : BddAbove (Set.range fun ell : {ell : ℤ // k₀ + s ≤ ell} ↦
      ‖badLengthTailAction S f I₀ k₀ s scale N ell.1 x‖) :=
    ⟨2 * energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N x, by
      rintro _ ⟨ell, rfl⟩
      exact norm_energyStandard_tailAction_le_prefix I₀ k₀ s scale hlam N hN ell x⟩
  exact (norm_nonneg _).trans (le_ciSup hb ⟨k₀ + s, le_rfl⟩)

theorem aemeasurable_energyStandardSourceTailMaximal
    (S : Finset RealInterval) {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (N : Finset RealInterval) :
    AEMeasurable (energyStandardSourceTailMaximal S f I₀ k₀ s scale N) volume := by
  apply AEMeasurable.iSup
  intro ell
  apply AEStronglyMeasurable.aemeasurable
  apply AEStronglyMeasurable.norm
  apply Finset.aestronglyMeasurable_fun_sum
  intro I hI
  by_cases he : (2 : ℝ) ^ ell.1 ≤ I.length
  · simpa only [ite_eq_left he] using
      (memLp_localizedPiece_of_integrable (scale I) I
        (integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s))).aestronglyMeasurable
  · simp only [ite_eq_right he]
    exact aestronglyMeasurable_const

/-- The standard physical tail has the genuine `L²` pairing estimate. This
is Hölder applied to the actual source-oriented maximum; the preceding
theorem supplies its fully concrete first factor. -/
theorem lintegral_energyStandardSourceTail_pairing_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} (hf : Integrable f) (hgi : Integrable g)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (N : Finset RealInterval) :
    (∫⁻ x, ‖energyStandardSourceTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤
      eLpNorm (energyStandardSourceTailMaximal S f I₀ k₀ s scale N) 2 volume *
        eLpNorm g 2 volume := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    (aemeasurable_energyStandardSourceTailMaximal S hf I₀ k₀ s scale N).enorm
    hgi.aestronglyMeasurable.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (aemeasurable_energyStandardSourceTailMaximal S hf I₀ k₀ s scale N).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hgi.aestronglyMeasurable]
  simpa only [Pi.mul_apply, ENNReal.toReal_ofNat] using h

theorem eLpNorm_energyStandardSourceTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s kmin : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hmin : ∀ I ∈ N, kmin ≤ scale I) :
    eLpNorm (energyStandardSourceTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal (2 * ((Nat.log2 N.card + 1 : ℝ) * Real.sqrt
        ((N.card : ℝ) * ((2560 * positiveDyadicAmplitudeBound ^ 2 *
          intervalL1Average f I₀ / (2 : ℝ) ^ (kmin + 2)) * ∫ x, ‖f x‖))) ) := by
  calc
    _ ≤ eLpNorm ((2 : ℝ) • energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N)
        2 volume := eLpNorm_mono
          (aemeasurable_energyStandardSourceTailMaximal S hf I₀ k₀ s scale N).aestronglyMeasurable
          fun x ↦ ?_
    _ = ENNReal.ofReal 2 *
        eLpNorm (energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N) 2 volume := by
      rw [eLpNorm_const_smul, show ‖(2 : ℝ)‖ₑ = ENNReal.ofReal 2 by
        exact Real.enorm_of_nonneg (by norm_num)]
    _ ≤ _ := by
      calc
        _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal ((Nat.log2 N.card + 1 : ℝ) * Real.sqrt
            ((N.card : ℝ) * ((2560 * positiveDyadicAmplitudeBound ^ 2 *
              intervalL1Average f I₀ / (2 : ℝ) ^ (kmin + 2)) * ∫ x, ‖f x‖))) :=
          mul_le_mul' le_rfl (eLpNorm_energyStandardGenerationPrefixMaximal_le hf I₀ k₀ s kmin
            scale hlam hsub N hN hmin)
        _ = _ := (ENNReal.ofReal_mul (by norm_num)).symm
  rw [Real.norm_of_nonneg
    (energyStandardSourceTailMaximal_nonneg I₀ k₀ s scale hlam N hN x)]
  change energyStandardSourceTailMaximal S f I₀ k₀ s scale N x ≤
    ‖2 * energyStandardGenerationPrefixMaximal S f I₀ k₀ s scale N x‖
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num)
    (energyStandardGenerationPrefixMaximal_nonneg S f I₀ k₀ s scale N x))]
  exact energyStandardSourceTailMaximal_le_prefix I₀ k₀ s scale hlam N hN x


end KrauseLaceyBadScale
end QuadraticCarleson
