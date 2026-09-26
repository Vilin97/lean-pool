/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyEnergyClassification
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardCrossRows
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleMaximal

/-!
# Fixed-physical-scale source summation for the scalar-standard branch

This follows the organization of the standard part of the Krause--Lacey
local lemma: fix a physical scale `j`, retain the source gaps in a finite
set, and only afterwards apply finite Cauchy--Schwarz in that gap variable.
The crucial preliminary statement is that the diagonal energy over *all*
source gaps still has no multiplicity: distinct bad-scale inputs have
disjoint spatial supports.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

/-- Pointwise no-loss packing simultaneously over finitely many source gaps
at one physical output scale. -/
theorem sum_norm_intervalBadInput_over_gaps_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hNS : ∀ s ∈ R, N s ⊆ S)
    (hscale : ∀ s ∈ R, ∀ I ∈ N s, I.length = (2 : ℝ) ^ (scale I + 2))
    (j : ℤ) (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) (x : ℝ) :
    (∑ s ∈ R, ∑ I ∈ N s, ‖intervalBadInput S f I₀ k₀ s scale I x‖) ≤ ‖f x‖ := by
  by_cases hex : ∃ s ∈ R, ∃ I ∈ N s,
      intervalBadInput S f I₀ k₀ s scale I x ≠ 0
  · obtain ⟨s, hsR, I, hIN, hxI⟩ := hex
    rw [Finset.sum_eq_single s]
    · rw [Finset.sum_eq_single I]
      · exact (norm_indicator_le_norm_self _ _).trans
          (norm_badScaleInput_le f I₀ k₀ (scale I + 2 - s) hlam x)
      · intro J hJN hJI
        have hz : intervalBadInput S f I₀ k₀ s scale J x = 0 := by
          by_contra hxJ
          exact hJI (intervalBadInput_unique_of_ne_zero f I₀ k₀ s scale hlam
            (hNS s hsR hJN) (hNS s hsR hIN)
            (hscale s hsR J hJN) (hscale s hsR I hIN) hxJ hxI)
        rw [hz, norm_zero]
      · intro hnot
        exact (hnot hIN).elim
    · intro t htR hts
      rw [Finset.sum_eq_zero]
      intro J hJN
      have hz : intervalBadInput S f I₀ k₀ t scale J x = 0 := by
        by_contra hxJ
        have hI := Set.indicator_apply_ne_zero.mp hxI
        have hJ := Set.indicator_apply_ne_zero.mp hxJ
        have hidx := badScale_indices_eq_of_ne_zero f I₀ k₀ hlam hI.2 hJ.2
        have hst : s = t := by
          rw [hfixed s hsR I hIN, hfixed t htR J hJN] at hidx
          omega
        exact hts hst.symm
      rw [hz, norm_zero]
    · intro hnot
      exact (hnot hsR).elim
  · have hz (s : ℤ) (hs : s ∈ R) (I : RealInterval) (hI : I ∈ N s) :
      intervalBadInput S f I₀ k₀ s scale I x = 0 := by
      apply not_ne_iff.mp
      intro h
      exact hex ⟨s, hs, I, hI, h⟩
    have hzero : (∑ s ∈ R, ∑ I ∈ N s,
        ‖intervalBadInput S f I₀ k₀ s scale I x‖) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      apply Finset.sum_eq_zero
      intro I hI
      rw [hz s hs I hI, norm_zero]
    rw [hzero]
    exact norm_nonneg _

/-- The corresponding integral packing. This is the source-gap version of
the bad-input mass estimate and is independent of `R.card`. -/
theorem sum_intervalBadInput_mass_over_gaps_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hNS : ∀ s ∈ R, N s ⊆ S)
    (hscale : ∀ s ∈ R, ∀ I ∈ N s, I.length = (2 : ℝ) ^ (scale I + 2))
    (j : ℤ) (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) :
    (∑ s ∈ R, ∑ I ∈ N s, ∫ x in I.centralThird,
      ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖) ≤ ∫ x, ‖f x‖ := by
  have hint (s : ℤ) (I : RealInterval) :
      Integrable (intervalBadInput S f I₀ k₀ s scale I) :=
    (integrable_badScaleInput S hf I₀ k₀ _).indicator I.measurableSet_centralThird
  have hmass (s : ℤ) (I : RealInterval) :
      (∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖) =
        ∫ x, ‖intervalBadInput S f I₀ k₀ s scale I x‖ := by
    simp only [intervalBadInput, norm_indicator_eq_indicator_norm,
      integral_indicator I.measurableSet_centralThird]
  calc
    _ = ∑ s ∈ R, ∑ I ∈ N s, ∫ x, ‖intervalBadInput S f I₀ k₀ s scale I x‖ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro I hI
      exact congrArg (fun z : ℝ ↦ z) (hmass s I)
    _ = ∑ s ∈ R, ∫ x, ∑ I ∈ N s, ‖intervalBadInput S f I₀ k₀ s scale I x‖ := by
      apply Finset.sum_congr rfl
      intro s hs
      exact (integral_finsetSum _ (fun I _ ↦ (hint s I).norm)).symm
    _ = ∫ x, ∑ s ∈ R, ∑ I ∈ N s, ‖intervalBadInput S f I₀ k₀ s scale I x‖ := by
      exact (integral_finsetSum _ (fun s _ ↦
        integrable_finsetSum _ (fun I _ ↦ (hint s I).norm))).symm
    _ ≤ _ := integral_mono
      (integrable_finsetSum _ (fun s _ ↦
        integrable_finsetSum _ (fun I _ ↦ (hint s I).norm))) hf.norm
      (sum_norm_intervalBadInput_over_gaps_le f I₀ k₀ scale hlam R N hNS hscale j hfixed)

/-- Scalar-standard diagonal energy summed over every selected source gap at
a fixed physical scale. There is no gap-count loss at this stage. -/
theorem sum_energyStandard_fixedPhysical_diagonalEnergy_over_gaps_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) :
    (∑ s ∈ R, ∑ I ∈ N s, localizedEnergy (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s))) ≤
      (2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ j) * ∫ x, ‖f x‖ := by
  let C := 2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
    (2 : ℝ) ^ j
  have hNS : ∀ s ∈ R, N s ⊆ S := fun s hs ↦
    (hN s hs).trans (fun I hI ↦ energyEligibleIntervals_subset S f I₀ k₀ s scale
      (Finset.mem_filter.mp hI).1)
  have hscale : ∀ s ∈ R, ∀ I ∈ N s,
      I.length = (2 : ℝ) ^ (scale I + 2) := by
    intro s hs I hI
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hN s hs hI)).1).2.1
  calc
    _ ≤ ∑ s ∈ R, ∑ I ∈ N s, C * ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖ := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro I hI
      have he := Finset.mem_filter.mp (Finset.mem_filter.mp (hN s hs hI)).1
      have hstd := (Finset.mem_filter.mp (hN s hs hI)).2
      have hE := energyStandard_badPiece_diagonalEnergy_le hf I₀ k₀ (scale I) s
        hlam hsub he.1 he.2.1 hstd
      have hlenj : I.length = (2 : ℝ) ^ j := by
        rw [he.2.1, hfixed s hs I hI]
      rw [hlenj] at hE
      simpa only [C] using hE
    _ = C * (∑ s ∈ R, ∑ I ∈ N s, ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖) := by
      simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalBadInput_mass_over_gaps_le hf I₀ k₀ scale hlam R N hNS hscale j hfixed)
      (by dsimp [C]; positivity [intervalL1Average_nonneg f I₀])

/-- The genuine finite sum of localized `L²` representatives at one output
physical scale, with the source gap retained as an outer finite index. -/
noncomputable def energyStandardFixedPhysicalSourceLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ s ∈ R, ∑ I ∈ N s, localizedPieceLp (scale I) I
    (badScaleInput S f I₀ k₀ (scale I + 2 - s))
    (integrable_badScaleInput S hf I₀ k₀ _)

/-- The pointwise finite operator represented by
`energyStandardFixedPhysicalSourceLp`. -/
noncomputable def energyStandardFixedPhysicalSourceAction
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (x : ℝ) : ℂ :=
  ∑ s ∈ R, ∑ I ∈ N s, krauseLaceyLocalizedPiece 1 (scale I) I
    (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x

theorem energyStandardFixedPhysicalSourceLp_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval) :
    energyStandardFixedPhysicalSourceLp S f hf I₀ k₀ scale R N =ᵐ[volume]
      energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale R N := by
  apply (Lp.coeFn_finsetSum R (fun s ↦ ∑ I ∈ N s, localizedPieceLp (scale I) I
    (badScaleInput S f I₀ k₀ (scale I + 2 - s))
    (integrable_badScaleInput S hf I₀ k₀ _))).trans
  have hpieces : ∀ᵐ x ∂volume, ∀ s ∈ R, ∀ I ∈ N s,
      localizedPieceLp (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s))
        (integrable_badScaleInput S hf I₀ k₀ _) x =
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x :=
    (ae_ball_iff (Finset.countable_toSet R)).mpr fun s _ ↦
      (ae_ball_iff (Finset.countable_toSet (N s))).mpr fun I _ ↦
        localizedPieceLp_ae_eq _ _ _ _
  have hall : ∀ᵐ x ∂volume, ∀ s ∈ R,
      (∑ I ∈ N s, localizedPieceLp (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s))
        (integrable_badScaleInput S hf I₀ k₀ _)) x =
        ∑ I ∈ N s, krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x :=
    (ae_ball_iff (Finset.countable_toSet R)).mpr fun s hs ↦
      (Lp.coeFn_finsetSum (N s) (fun I ↦ localizedPieceLp (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s))
        (integrable_badScaleInput S hf I₀ k₀ _))).trans <| by
          filter_upwards [hpieces] with x hx
          simp only [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro I hI
          exact hx s hs I hI
  filter_upwards [hall] with x hx
  simp only [Finset.sum_apply, energyStandardFixedPhysicalSourceAction]
  apply Finset.sum_congr rfl
  intro s hs
  exact hx s hs

theorem norm_energyStandard_fixedPhysical_layer_sq_eq
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ I ∈ N, scale I + 2 = j) :
    ‖∑ I ∈ N, localizedPieceLp (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s))
      (integrable_badScaleInput S hf I₀ k₀ _)‖ ^ 2 =
      ∑ I ∈ N, localizedEnergy (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by
  have hNS : N ⊆ S := fun I hI ↦ energyEligibleIntervals_subset S f I₀ k₀ s scale
    (Finset.mem_filter.mp (hN hI)).1
  rw [norm_sum_sq_eq_sum_of_inner_zero]
  · simp_rw [norm_localizedPieceLp_sq, localizedEnergy]
  · intro I hI J hJ hne
    have hlenI := (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hI)).1).2.1
    have hlenJ := (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hJ)).1).2.1
    have hlen : I.length = J.length := by
      rw [hlenI, hlenJ, hfixed I hI, hfixed J hJ]
    have hd : Disjoint I.carrier J.carrier := by
      rcases hlam (hNS hI) (hNS hJ) hne with hsub | hsub | hd
      · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)).elim
      · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm).elim
      · exact hd
    exact inner_localizedPieceLp_eq_zero_of_disjoint _ _ _ _ _ _ _ _ hlenI hlenJ hd

/-- The paper's finite-Cauchy step. The source-gap cardinality appears
exactly once, while the diagonal energy is aggregated before that step. -/
theorem norm_energyStandardFixedPhysicalSourceLp_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) :
    ‖energyStandardFixedPhysicalSourceLp S f hf I₀ k₀ scale R N‖ ^ 2 ≤
      (R.card : ℝ) *
        ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
          (2 : ℝ) ^ j) * ∫ x, ‖f x‖) := by
  let v (s : ℤ) := ∑ I ∈ N s, localizedPieceLp (scale I) I
    (badScaleInput S f I₀ k₀ (scale I + 2 - s))
    (integrable_badScaleInput S hf I₀ k₀ _)
  have hv (s : ℤ) (hs : s ∈ R) : ‖v s‖ ^ 2 =
      ∑ I ∈ N s, localizedEnergy (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by
    exact norm_energyStandard_fixedPhysical_layer_sq_eq hf I₀ k₀ s j scale hlam
      (N s) (hN s hs) (hfixed s hs)
  have hsum : (∑ s ∈ R, ‖v s‖ ^ 2) =
      ∑ s ∈ R, ∑ I ∈ N s, localizedEnergy (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by
    apply Finset.sum_congr rfl
    intro s hs
    exact hv s hs
  change ‖∑ s ∈ R, v s‖ ^ 2 ≤ _
  calc
    _ ≤ (∑ s ∈ R, ‖v s‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (R.card : ℝ) * ∑ s ∈ R, ‖v s‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := R) (f := fun s ↦ ‖v s‖)
    _ = (R.card : ℝ) * ∑ s ∈ R, ∑ I ∈ N s,
        localizedEnergy (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by rw [hsum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_energyStandard_fixedPhysical_diagonalEnergy_over_gaps_le hf I₀ k₀ j scale
        hlam hsub R N hN hfixed)
      (by exact_mod_cast R.card.zero_le)

/-- The paper's precise source-gap range at physical scale `j`. -/
noncomputable abbrev standardSourceGaps (k₀ j : ℤ) : Finset ℤ := Finset.Icc 0 (j - k₀)

/-- With `1 ≤ k₀ ≤ j`, the finite Cauchy factor for the source gaps is at
most `j`. This is the single visible `j` in the scalar-standard squared
`L²` estimate. -/
theorem norm_energyStandardFixedPhysicalSourceLp_sq_le_j_mul
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (hk₀ : 1 ≤ k₀) (hk₀j : k₀ ≤ j)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ standardSourceGaps k₀ j,
      N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ standardSourceGaps k₀ j, ∀ I ∈ N s, scale I + 2 = j) :
    ‖energyStandardFixedPhysicalSourceLp S f hf I₀ k₀ scale
      (standardSourceGaps k₀ j) N‖ ^ 2 ≤
      (j : ℝ) * ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ j) * ∫ x, ‖f x‖) := by
  have hcardZ : ((standardSourceGaps k₀ j).card : ℤ) = j - k₀ + 1 := by
    rw [standardSourceGaps, Int.card_Icc_of_le]
    · omega
    · omega
  have hcardZle : ((standardSourceGaps k₀ j).card : ℤ) ≤ j := by
    rw [hcardZ]
    omega
  have hcard : ((standardSourceGaps k₀ j).card : ℝ) ≤ j := by
    exact_mod_cast hcardZle
  apply (norm_energyStandardFixedPhysicalSourceLp_sq_le hf I₀ k₀ j scale hlam hsub
    (standardSourceGaps k₀ j) N hN hfixed).trans
  exact mul_le_mul_of_nonneg_right hcard
    (mul_nonneg
      (div_nonneg (by positivity [intervalL1Average_nonneg f I₀]) (by positivity))
      (integral_nonneg fun _ ↦ norm_nonneg _))


end KrauseLaceyBadScale
end QuadraticCarleson
