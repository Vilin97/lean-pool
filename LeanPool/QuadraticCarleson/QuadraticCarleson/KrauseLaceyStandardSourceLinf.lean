/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStandardSourceSummation

/-!
# Regrouping the scalar-standard source gaps at a fixed physical scale

The finite identity below is the exact bookkeeping step used before the
fixed-scale endpoint: the source-gap sum is regrouped by its parent interval.
It does not use any cancellation or analytic estimate.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

/-- Finite linearity of an actual finite-range kernel on integrable inputs. -/
theorem FiniteRangeKernel.applyIntegral_finsetSum
    {α : Type*} (K : FiniteRangeKernel) (T : Finset α) (b : α → ℝ → ℂ)
    (hb : ∀ a ∈ T, Integrable (b a)) (x : ℝ) :
    K.applyIntegral (fun t ↦ ∑ a ∈ T, b a t) x =
      ∑ a ∈ T, K.applyIntegral (b a) x := by
  unfold FiniteRangeKernel.applyIntegral
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun a ha ↦ K.integrable_row_mul (hb a ha) x)

theorem krauseLaceyLocalizedPiece_eq_applyIntegral_intervalBadInput
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (I : RealInterval) (x : ℝ) :
    krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x =
      (krauseLaceyPositiveKernel (scale I)).applyIntegral
        (intervalBadInput S f I₀ k₀ s scale I) x := by
  let K := krauseLaceyPositiveKernel (scale I)
  let c := intervalBadInput S f I₀ k₀ s scale I
  have ha : K.applyIntegral c = krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by
    funext y
    exact (krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution
      (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s)) y).symm
  exact (congrFun ha x).symm

/-- A fixed-scale endpoint with one bounded input per parent. This is the
same support-disjoint argument as the common-input endpoint, with no loss
from the number of parents. -/
theorem norm_krauseLaceyFixedScaleLocalizedSum_variable_le
    (j : ℤ) (S : Finset RealInterval) (b : RealInterval → ℝ → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ I ∈ S, ∀ t, ‖b I t‖ ≤ M)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (j + 2))
    (hdisj : Set.Pairwise (↑S : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier)) (x : ℝ) :
    ‖∑ I ∈ S, krauseLaceyLocalizedPiece 1 j I (b I) x‖ ≤
      positiveDyadicAmplitudeBound * M := by
  by_cases hex : ∃ I ∈ S, krauseLaceyLocalizedPiece 1 j I (b I) x ≠ 0
  · obtain ⟨I, hIS, hIx⟩ := hex
    have hxI : x ∈ I.carrier :=
      krauseLaceyLocalizedPiece_support_subset 1 j I (b I) (hscale I hIS) hIx
    have hsum : (∑ I ∈ S, krauseLaceyLocalizedPiece 1 j I (b I) x) =
        krauseLaceyLocalizedPiece 1 j I (b I) x := by
      rw [Finset.sum_eq_single I]
      · intro J hJS hJI
        apply krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 j J (b J) (hscale J hJS)
        intro hxJ
        exact Set.disjoint_left.1 (hdisj hIS hJS hJI.symm) hxI hxJ
      · intro hnot
        exact (hnot hIS).elim
    rw [hsum]
    exact norm_krauseLaceyLocalizedPiece_le j I (b I) hM (hb I hIS) x
  · have hzero : (∑ I ∈ S, krauseLaceyLocalizedPiece 1 j I (b I) x) = 0 := by
      apply Finset.sum_eq_zero
      intro I hIS
      by_contra h
      exact hex ⟨I, hIS, h⟩
    rw [hzero, norm_zero]
    exact mul_nonneg positiveDyadicAmplitudeBound_nonneg hM

/-- The selected source inputs attached to one parent, already restricted to
its central third. -/
noncomputable def energyStandardSourceParentInput
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (I : RealInterval) (x : ℝ) : ℂ :=
  ∑ s ∈ R, if I ∈ N s then intervalBadInput S f I₀ k₀ s scale I x else 0

/-- Singleton-fibre form of the source-gap packing: every regrouped parent
input is pointwise dominated by the original input, with no gap factor. -/
theorem norm_energyStandardSourceParentInput_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hNS : ∀ s ∈ R, N s ⊆ S)
    (hscale : ∀ s ∈ R, ∀ I ∈ N s, I.length = (2 : ℝ) ^ (scale I + 2))
    (j : ℤ) (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j)
    {I : RealInterval} (x : ℝ) :
    ‖energyStandardSourceParentInput S f I₀ k₀ scale R N I x‖ ≤ ‖f x‖ := by
  let NI : ℤ → Finset RealInterval := fun s ↦ if I ∈ N s then {I} else ∅
  have hNIS : ∀ s ∈ R, NI s ⊆ S := by
    intro s hs J hJ
    by_cases hmem : I ∈ N s
    · have hJI : J = I := by simpa [NI, hmem] using hJ
      subst J
      exact hNS s hs hmem
    · simp [NI, hmem] at hJ
  have hNIscale : ∀ s ∈ R, ∀ J ∈ NI s,
      J.length = (2 : ℝ) ^ (scale J + 2) := by
    intro s hs J hJ
    by_cases hmem : I ∈ N s
    · have hJI : J = I := by simpa [NI, hmem] using hJ
      subst J
      exact hscale s hs I hmem
    · simp [NI, hmem] at hJ
  have hNIfixed : ∀ s ∈ R, ∀ J ∈ NI s, scale J + 2 = j := by
    intro s hs J hJ
    by_cases hmem : I ∈ N s
    · have hJI : J = I := by simpa [NI, hmem] using hJ
      subst J
      exact hfixed s hs I hmem
    · simp [NI, hmem] at hJ
  have hpack := sum_norm_intervalBadInput_over_gaps_le f I₀ k₀ scale hlam R NI
    hNIS hNIscale j hNIfixed x
  calc
    _ ≤ ∑ s ∈ R, ‖if I ∈ N s then intervalBadInput S f I₀ k₀ s scale I x else 0‖ := by
      unfold energyStandardSourceParentInput
      exact norm_sum_le _ _
    _ = ∑ s ∈ R, ∑ J ∈ NI s, ‖intervalBadInput S f I₀ k₀ s scale J x‖ := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hmem : I ∈ N s
      · simp [NI, hmem]
      · simp [NI, hmem]
    _ ≤ _ := hpack

theorem integrable_energyStandardSourceParentInput
    (S : Finset RealInterval) {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval) (I : RealInterval) :
    Integrable (energyStandardSourceParentInput S f I₀ k₀ scale R N I) := by
  unfold energyStandardSourceParentInput
  apply integrable_finsetSum
  intro s hs
  by_cases hIs : I ∈ N s
  · simp only [hIs, ite_eq_left, intervalBadInput]
    exact (integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s)).indicator
      I.measurableSet_centralThird
  · simp only [hIs]
    exact integrable_zero ℝ ℂ volume

theorem centralThird_indicator_energyStandardSourceParentInput
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (I : RealInterval) :
    I.centralThird.indicator
        (energyStandardSourceParentInput S f I₀ k₀ scale R N I) =
      energyStandardSourceParentInput S f I₀ k₀ scale R N I := by
  funext x
  by_cases hx : x ∈ I.centralThird <;>
    simp [energyStandardSourceParentInput, intervalBadInput, hx]

/-- The regrouped input has the same local mass bound as a single source
bad piece. Disjointness across source gaps removes any gap-count loss. -/
theorem integral_norm_energyStandardSourceParentInput_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j)
    {I : RealInterval} (hIU : I ∈ R.biUnion N) :
    (∫ x, ‖energyStandardSourceParentInput S f I₀ k₀ scale R N I x‖) ≤
      10 * intervalL1Average f I₀ * I.length := by
  obtain ⟨s₀, hs₀, hIs₀⟩ := Finset.mem_biUnion.mp hIU
  have hstandard := hN s₀ hs₀ hIs₀
  have hgood : I ∈ goodCollection S f 0 I₀ :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hstandard).1).1
  have hNS : ∀ s ∈ R, N s ⊆ S := by
    intro s hs J hJ
    exact energyEligibleIntervals_subset S f I₀ k₀ s scale
      (Finset.mem_filter.mp (hN s hs hJ)).1
  have hscale : ∀ s ∈ R, ∀ J ∈ N s,
      J.length = (2 : ℝ) ^ (scale J + 2) := by
    intro s hs J hJ
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hN s hs hJ)).1).2.1
  have hp (x : ℝ) :
      ‖energyStandardSourceParentInput S f I₀ k₀ scale R N I x‖ ≤
        I.centralThird.indicator (fun y ↦ ‖f y‖) x := by
    by_cases hx : x ∈ I.centralThird
    · rw [Set.indicator_of_mem hx]
      exact norm_energyStandardSourceParentInput_le f I₀ k₀ scale hlam R N hNS
        hscale j hfixed x
    · rw [Set.indicator_of_notMem hx]
      have hz : energyStandardSourceParentInput S f I₀ k₀ scale R N I x = 0 := by
        have hfun := centralThird_indicator_energyStandardSourceParentInput
          S f I₀ k₀ scale R N I
        exact (congrFun hfun x).symm.trans (Set.indicator_of_notMem hx _)
      rw [hz, norm_zero]
  calc
    _ ≤ ∫ x, I.centralThird.indicator (fun y ↦ ‖f y‖) x :=
      integral_mono
        (integrable_energyStandardSourceParentInput S hf I₀ k₀ scale R N I).norm
        (hf.norm.indicator I.measurableSet_centralThird) hp
    _ = ∫ x in I.centralThird, ‖f x‖ :=
      integral_indicator I.measurableSet_centralThird
    _ ≤ ∫ x in I.carrier, ‖f x‖ :=
      setIntegral_mono_set hf.norm.integrableOn
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
        I.centralThird_subset_carrier.eventuallyLE
    _ = intervalL1Average f I * I.length :=
      (intervalL1Average_mul_length f I).symm
    _ ≤ 10 * intervalL1Average f I₀ * I.length :=
      mul_le_mul_of_nonneg_right (goodCollection_averages_le hsub hgood).1 I.length_pos.le

/-- The source sum after its finite regrouping by parent intervals. -/
noncomputable def energyStandardRegroupedSourceAction
  (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (j : ℤ) (scale : RealInterval → ℤ) (R : Finset ℤ)
    (N : ℤ → Finset RealInterval) (x : ℝ) : ℂ :=
  ∑ I ∈ R.biUnion N, krauseLaceyLocalizedPiece 1 (j - 2) I
    (energyStandardSourceParentInput S f I₀ k₀ scale R N I) x

/-- Uniform fixed-physical-scale `L∞` endpoint for the regrouped source
action. The source-gap count is absent: it was eliminated pointwise before
the fixed-scale support argument. -/
theorem norm_energyStandardRegroupedSourceAction_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ j : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hNS : ∀ s ∈ R, N s ⊆ S)
    (hscale : ∀ s ∈ R, ∀ I ∈ N s, I.length = (2 : ℝ) ^ (scale I + 2))
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j)
    {M : ℝ} (hM : 0 ≤ M) (hfTop : ∀ x, ‖f x‖ ≤ M) (x : ℝ) :
    ‖energyStandardRegroupedSourceAction S f I₀ k₀ j scale R N x‖ ≤
      positiveDyadicAmplitudeBound * M := by
  let U := R.biUnion N
  have hUS : U ⊆ S := by
    intro I hI
    obtain ⟨s, hs, hIs⟩ := Finset.mem_biUnion.mp hI
    exact hNS s hs hIs
  have hscaleU (I : RealInterval) (hI : I ∈ U) : I.length = (2 : ℝ) ^ ((j - 2) + 2) := by
    obtain ⟨s, hs, hIs⟩ := Finset.mem_biUnion.mp hI
    rw [hscale s hs I hIs, hfixed s hs I hIs]
    ring
  have hdisj : Set.Pairwise (↑U : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier) := by
    intro I hI J hJ hne
    have hlen : I.length = J.length := by rw [hscaleU I hI, hscaleU J hJ]
    rcases hlam (hUS hI) (hUS hJ) hne with hsub | hsub | hd
    · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)).elim
    · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm).elim
    · exact hd
  unfold energyStandardRegroupedSourceAction
  apply norm_krauseLaceyFixedScaleLocalizedSum_variable_le (j - 2) U
    (energyStandardSourceParentInput S f I₀ k₀ scale R N) hM
  · intro I hI t
    exact (norm_energyStandardSourceParentInput_le f I₀ k₀ scale hlam R N hNS hscale j
      hfixed t).trans (hfTop t)
  · exact hscaleU
  · exact hdisj

theorem energyStandardFixedPhysicalSourceAction_reindex
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (x : ℝ) :
    energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale R N x =
      ∑ I ∈ R.biUnion N, ∑ s ∈ R,
        if I ∈ N s then
          krauseLaceyLocalizedPiece 1 (scale I) I
            (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x
        else 0 := by
  let U := R.biUnion N
  have hsub (s : ℤ) (hs : s ∈ R) : N s ⊆ U := by
    intro I hI
    exact Finset.mem_biUnion.mpr ⟨s, hs, hI⟩
  unfold energyStandardFixedPhysicalSourceAction
  calc
    _ = ∑ s ∈ R, ∑ I ∈ U,
        if I ∈ N s then
          krauseLaceyLocalizedPiece 1 (scale I) I
            (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x
        else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      symm
      have hext : (∑ I ∈ N s,
          if I ∈ N s then
            krauseLaceyLocalizedPiece 1 (scale I) I
              (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x
          else 0) =
          ∑ I ∈ U, if I ∈ N s then
            krauseLaceyLocalizedPiece 1 (scale I) I
              (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x
          else 0 := by
        apply Finset.sum_subset (hsub s hs)
        intro I hIU hIN
        simp only [ite_eq_right hIN]
      rw [← hext]
      simp
    _ = _ := by
      rw [Finset.sum_comm]

/-- At one fixed physical scale, the source's outer gap sum is exactly the
single regrouped action. This is finite kernel linearity; no estimate and no
triangle inequality is used. -/
theorem energyStandardFixedPhysicalSourceAction_eq_regrouped
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) (x : ℝ) :
    energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale R N x =
      energyStandardRegroupedSourceAction S f I₀ k₀ j scale R N x := by
  classical
  rw [energyStandardFixedPhysicalSourceAction_reindex]
  unfold energyStandardRegroupedSourceAction
  apply Finset.sum_congr rfl
  intro I hIU
  obtain ⟨s₀, hs₀, hIs₀⟩ := Finset.mem_biUnion.mp hIU
  have hk : scale I = j - 2 := by
    have := hfixed s₀ hs₀ I hIs₀
    omega
  let K := krauseLaceyPositiveKernel (j - 2)
  let b : ℤ → ℝ → ℂ := fun s ↦
    if I ∈ N s then intervalBadInput S f I₀ k₀ s scale I else 0
  let parent := energyStandardSourceParentInput S f I₀ k₀ scale R N I
  have hb : ∀ s ∈ R, Integrable (b s) := by
    intro s hs
    by_cases hIs : I ∈ N s
    · simpa only [b, hIs, ite_eq_left, intervalBadInput] using
        (integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s)).indicator
          I.measurableSet_centralThird
    · simp only [b, hIs]
      exact integrable_zero ℝ ℂ volume
  have hparent : (fun t ↦ ∑ s ∈ R, b s t) = parent := by
    funext t
    simp only [b, parent, energyStandardSourceParentInput]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hIs : I ∈ N s <;> simp [hIs]
  have hsupport : I.centralThird.indicator parent = parent := by
    funext t
    by_cases ht : t ∈ I.centralThird <;>
      simp [parent, energyStandardSourceParentInput, intervalBadInput, ht]
  have hKparent : K.applyIntegral parent =
      krauseLaceyLocalizedPiece 1 (j - 2) I parent := by
    have ha : K.applyIntegral (I.centralThird.indicator parent) =
        krauseLaceyLocalizedPiece 1 (j - 2) I parent := by
      funext y
      exact (krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution
        (j - 2) I parent y).symm
    calc
      K.applyIntegral parent =
          K.applyIntegral (I.centralThird.indicator parent) :=
        congrArg K.applyIntegral hsupport.symm
      _ = _ := ha
  calc
    (∑ s ∈ R, if I ∈ N s then
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0) =
        ∑ s ∈ R, K.applyIntegral (b s) x := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hIs : I ∈ N s
      · simp only [hIs, ite_eq_left]
        simpa only [K, b, hIs, ite_eq_left, hk] using
          (krauseLaceyLocalizedPiece_eq_applyIntegral_intervalBadInput
            S f I₀ k₀ s scale I x)
      · simp only [hIs, b, FiniteRangeKernel.applyIntegral]
        simp
    _ = K.applyIntegral (fun t ↦ ∑ s ∈ R, b s t) x :=
      (FiniteRangeKernel.applyIntegral_finsetSum K R b hb x).symm
    _ = K.applyIntegral parent x := by rw [hparent]
    _ = krauseLaceyLocalizedPiece 1 (j - 2) I parent x := congrFun hKparent x

/-- The source-faithful fixed-scale endpoint for a single regrouped parent.
Unlike the preliminary global-`L∞` estimate above, this uses only the
stopping-time average on the ambient interval. The factor eight is exactly
the ratio between the parent length `2^j` and the kernel radius `2^(j-3)`. -/
theorem norm_energyStandardRegroupedSourcePiece_le_localAverage
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j)
    {I : RealInterval} (hIU : I ∈ R.biUnion N) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 (j - 2) I
        (energyStandardSourceParentInput S f I₀ k₀ scale R N I) x‖ ≤
      80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀ := by
  let K := krauseLaceyPositiveKernel (j - 2)
  let b := energyStandardSourceParentInput S f I₀ k₀ scale R N I
  have hb : Integrable b :=
    integrable_energyStandardSourceParentInput S hf I₀ k₀ scale R N I
  have hsupport : I.centralThird.indicator b = b := by
    exact centralThird_indicator_energyStandardSourceParentInput
      S f I₀ k₀ scale R N I
  have hK : K.applyIntegral b = krauseLaceyLocalizedPiece 1 (j - 2) I b := by
    have ha : K.applyIntegral (I.centralThird.indicator b) =
        krauseLaceyLocalizedPiece 1 (j - 2) I b := by
      funext y
      exact (krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution
        (j - 2) I b y).symm
    calc
      K.applyIntegral b = K.applyIntegral (I.centralThird.indicator b) :=
        congrArg K.applyIntegral hsupport.symm
      _ = _ := ha
  have hkernel := K.norm_applyIntegral_le hb x
  rw [hK] at hkernel
  have hmass := integral_norm_energyStandardSourceParentInput_le
    hf I₀ k₀ j scale hlam hsub R N hN hfixed hIU
  obtain ⟨s₀, hs₀, hIs₀⟩ := Finset.mem_biUnion.mp hIU
  have hlen : I.length = (2 : ℝ) ^ j := by
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hN s₀ hs₀ hIs₀)).1).2.1.trans
      (congrArg (fun z : ℤ ↦ (2 : ℝ) ^ z) (hfixed s₀ hs₀ I hIs₀))
  calc
    _ ≤ (positiveDyadicAmplitudeBound / (2 : ℝ) ^ ((j - 2) - 1)) *
        ∫ t, ‖b t‖ := hkernel
    _ ≤ (positiveDyadicAmplitudeBound / (2 : ℝ) ^ ((j - 2) - 1)) *
        (10 * intervalL1Average f I₀ * I.length) :=
      mul_le_mul_of_nonneg_left hmass
        (div_nonneg positiveDyadicAmplitudeBound_nonneg (by positivity))
    _ = 80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀ := by
      rw [hlen, show j = (j - 2) + 2 by ring,
        krauseLacey_scale_eq_eight_mul_radius (j - 2)]
      field_simp; ring

/-- At one fixed physical scale, the complete scalar-standard source sum is
bounded by the local stopping average, with no loss in the number of source
gaps or parents. Equal-length laminar parents have disjoint carriers, so at
most one regrouped output is nonzero at each point. -/
theorem norm_energyStandardRegroupedSourceAction_le_localAverage
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) (x : ℝ) :
    ‖energyStandardRegroupedSourceAction S f I₀ k₀ j scale R N x‖ ≤
      80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀ := by
  let U := R.biUnion N
  have hUS : U ⊆ S := by
    intro I hI
    obtain ⟨s, hs, hIs⟩ := Finset.mem_biUnion.mp hI
    exact energyEligibleIntervals_subset S f I₀ k₀ s scale
      (Finset.mem_filter.mp (hN s hs hIs)).1
  have hscaleU (I : RealInterval) (hI : I ∈ U) :
      I.length = (2 : ℝ) ^ ((j - 2) + 2) := by
    obtain ⟨s, hs, hIs⟩ := Finset.mem_biUnion.mp hI
    rw [(Finset.mem_filter.mp (Finset.mem_filter.mp (hN s hs hIs)).1).2.1,
      hfixed s hs I hIs]
    ring
  have hdisj : Set.Pairwise (↑U : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier) := by
    intro I hI J hJ hne
    have hlen : I.length = J.length := by rw [hscaleU I hI, hscaleU J hJ]
    rcases hlam (hUS hI) (hUS hJ) hne with hsubset | hsubset | hd
    · exact (hne (interval_eq_of_carrier_subset_of_length_le hsubset hlen.ge)).elim
    · exact (hne (interval_eq_of_carrier_subset_of_length_le hsubset hlen.le).symm).elim
    · exact hd
  by_cases hex : ∃ I ∈ U, krauseLaceyLocalizedPiece 1 (j - 2) I
      (energyStandardSourceParentInput S f I₀ k₀ scale R N I) x ≠ 0
  · obtain ⟨I, hIU, hIx⟩ := hex
    have hxI : x ∈ I.carrier :=
      krauseLaceyLocalizedPiece_support_subset 1 (j - 2) I
        (energyStandardSourceParentInput S f I₀ k₀ scale R N I)
        (hscaleU I hIU) hIx
    have hsum : energyStandardRegroupedSourceAction S f I₀ k₀ j scale R N x =
        krauseLaceyLocalizedPiece 1 (j - 2) I
          (energyStandardSourceParentInput S f I₀ k₀ scale R N I) x := by
      unfold energyStandardRegroupedSourceAction
      rw [Finset.sum_eq_single I]
      · intro J hJU hJI
        apply krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (j - 2) J _
          (hscaleU J hJU)
        intro hxJ
        exact Set.disjoint_left.1 (hdisj hIU hJU hJI.symm) hxI hxJ
      · intro hnot
        exact (hnot hIU).elim
    rw [hsum]
    exact norm_energyStandardRegroupedSourcePiece_le_localAverage
      hf I₀ k₀ j scale hlam hsub R N hN hfixed hIU x
  · have hzero : energyStandardRegroupedSourceAction S f I₀ k₀ j scale R N x = 0 := by
      unfold energyStandardRegroupedSourceAction
      apply Finset.sum_eq_zero
      intro I hIU
      by_contra h
      exact hex ⟨I, hIU, h⟩
    rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
      (intervalL1Average_nonneg f I₀)

/-- Source-faithful fixed-physical-scale `L∞` estimate in the original
outer-gap presentation. Exact regrouping transfers the preceding local
average bound without any triangle-inequality loss. -/
theorem norm_energyStandardFixedPhysicalSourceAction_le_localAverage
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (R : Finset ℤ) (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ R, N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ R, ∀ I ∈ N s, scale I + 2 = j) (x : ℝ) :
    ‖energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale R N x‖ ≤
      80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀ := by
  rw [energyStandardFixedPhysicalSourceAction_eq_regrouped
    S f hf I₀ k₀ j scale R N hfixed x]
  exact norm_energyStandardRegroupedSourceAction_le_localAverage
    hf I₀ k₀ j scale hlam hsub R N hN hfixed x


end KrauseLaceyBadScale
end QuadraticCarleson
