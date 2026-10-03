/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectOffsetEnergy
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectPositivePairing

/-!
# Fixed-output-scale energy for the direct offset action

The output family may be any subcollection `A`; the smallest-region input
partition is always the one attached to the ambient family `S`.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectScaleEnergy

open KrauseLaceyBadScale KrauseLaceyQuadraticDirectPartition
open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectOffsetEnergy
open KrauseLaceyQuadraticDirectPositivePairing


noncomputable
section

/-- Classical equality for interval indices in the scale-energy decomposition. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- One genuine localized output, represented in `L²`. -/
noncomputable def offsetLocalizedPieceLp
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (I : RealInterval) (s : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  localizedPieceLp (scale I) I (offsetGroupedInput S scale f I s)
    (integrable_offsetGroupedInput S scale f I s)

/-- The actual sum of all retained outputs at one output scale. -/
noncomputable def offsetOutputScaleLp
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ I ∈ A.filter (fun I ↦ scale I = k),
    offsetLocalizedPieceLp S scale f I s

/-- The `L²` representative is a.e. the literal finite sum of localized
integrals. -/
theorem offsetOutputScaleLp_ae_eq
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    offsetOutputScaleLp S A scale f k s =ᵐ[volume]
      fun x ↦ ∑ I ∈ A.filter (fun I ↦ scale I = k),
        krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x := by
  let T := A.filter (fun I ↦ scale I = k)
  have hsum := Lp.coeFn_finsetSum T (fun I ↦ offsetLocalizedPieceLp S scale f I s)
  apply hsum.trans
  have hall : ∀ᵐ x ∂volume, ∀ I ∈ T,
      offsetLocalizedPieceLp S scale f I s x =
        krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x :=
    (ae_ball_iff (Finset.countable_toSet T)).mpr fun I hI ↦
      localizedPieceLp_ae_eq (scale I) I
        (offsetGroupedInput S scale f I s) (integrable_offsetGroupedInput S scale f I s)
  filter_upwards [hall] with x hx
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (hx ·)

/-- Equal output scales have disjoint carriers inside every retained ambient
subcollection. -/
theorem outputScale_pairwiseDisjoint
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2)) (k : ℤ) :
    Set.Pairwise (↑(A.filter (fun I ↦ scale I = k)) : Set RealInterval)
      (Disjoint on RealInterval.carrier) := by
  intro I hI J hJ hne
  exact sameScale_carriers_pairwiseDisjoint hlam scale hscale k
    (Finset.mem_filter.mpr ⟨hA (Finset.mem_filter.mp hI).1,
      (Finset.mem_filter.mp hI).2⟩)
    (Finset.mem_filter.mpr ⟨hA (Finset.mem_filter.mp hJ).1,
      (Finset.mem_filter.mp hJ).2⟩) hne

/-- Exact spatial orthogonality of two distinct same-scale direct outputs. -/
theorem inner_offsetLocalizedPieceLp_eq_zero_of_sameScale
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ H ∈ S, H.length = (2 : ℝ) ^ (scale H + 2))
    (f : L0Infinity) (k s : ℤ) {I J : RealInterval}
    (hI : I ∈ A.filter (fun H ↦ scale H = k))
    (hJ : J ∈ A.filter (fun H ↦ scale H = k)) (hne : I ≠ J) :
    inner ℝ (offsetLocalizedPieceLp S scale f I s)
      (offsetLocalizedPieceLp S scale f J s) = 0 := by
  apply inner_localizedPieceLp_eq_zero_of_disjoint (scale J) (scale I) I J
    (offsetGroupedInput S scale f I s) (offsetGroupedInput S scale f J s)
    (integrable_offsetGroupedInput S scale f I s)
    (integrable_offsetGroupedInput S scale f J s)
  · exact hscale I (hA (Finset.mem_filter.mp hI).1)
  · exact hscale J (hA (Finset.mem_filter.mp hJ).1)
  · exact outputScale_pairwiseDisjoint hA hlam scale hscale k hI hJ hne

/-- Same-scale spatial orthogonality identifies the squared `L²` norm with
the finite sum of the genuine one-piece energies. -/
theorem norm_offsetOutputScaleLp_sq_eq_sum_localizedEnergy
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ H ∈ S, H.length = (2 : ℝ) ^ (scale H + 2))
    (f : L0Infinity) (k s : ℤ) :
    ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 =
      ∑ I ∈ A.filter (fun I ↦ scale I = k),
        localizedEnergy (scale I) I (offsetGroupedInput S scale f I s) := by
  classical
  unfold offsetOutputScaleLp
  rw [norm_sum_sq_eq_sum_of_inner_zero]
  · apply Finset.sum_congr rfl
    intro I hI
    exact norm_localizedPieceLp_sq (scale I) I
      (offsetGroupedInput S scale f I s) (integrable_offsetGroupedInput S scale f I s)
  · intro I hI J hJ hne
    exact inner_offsetLocalizedPieceLp_eq_zero_of_sameScale hA hlam scale hscale f k s hI hJ hne

/-- Summing the direct one-piece bounds on a fixed output scale. -/
theorem norm_offsetOutputScaleLp_sq_le_sum_energy_bounds
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ H ∈ S, H.length = (2 : ℝ) ^ (scale H + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (k : ℤ) (hgap : ∀ I ∈ A.filter (fun I ↦ scale I = k),
      0 ≤ scale I + 2 - s) :
    ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 ≤
      ∑ I ∈ A.filter (fun I ↦ scale I = k),
        (432 * positiveDyadicAmplitudeBound ^ 2 * M * (2 : ℝ) ^ (-s)) *
          ∫ x in I.centralThird, ‖offsetGroupedInput S scale f I s x‖ := by
  rw [norm_offsetOutputScaleLp_sq_eq_sum_localizedEnergy hA hlam scale hscale f k s]
  apply Finset.sum_le_sum
  intro I hI
  exact localizedEnergy_offsetGroupedInput_le hlam scale hscale f hs hM hmass I
    (hA (Finset.mem_filter.mp hI).1) (hgap I hI)

/-- The summed energy bounds retain an exact ambient-region mass expansion,
valid for every output subcollection `A`. -/
theorem sum_offsetGroupedInput_mass_region_bound
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    ∑ I ∈ A.filter (fun I ↦ scale I = k),
      ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
      ∑ I ∈ A.filter (fun I ↦ scale I = k),
        ∑ J ∈ (selectedSubintervals S I).filter
          (fun J ↦ scale I - scale J = s),
          ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ := by
  exact sum_integral_norm_offsetGroupedInput_le_sum_region_mass S
    (A.filter (fun I ↦ scale I = k)) scale f s

/-- At one output scale, the central thirds of the retained outputs are
pairwise disjoint. -/
theorem outputScale_centralThird_pairwiseDisjoint
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2)) (k : ℤ) :
    Set.Pairwise (↑(A.filter (fun I ↦ scale I = k)) : Set RealInterval)
      (Disjoint on RealInterval.centralThird) := by
  intro I hI J hJ hne
  exact (outputScale_pairwiseDisjoint hA hlam scale hscale k hI hJ hne).mono
    I.centralThird_subset_carrier J.centralThird_subset_carrier

/-- The fixed-offset masses of all outputs at one common scale are bounded
by the corresponding ambient smallest-region scale input. -/
theorem sum_integral_norm_offsetGroupedInput_fixedScale_le
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) (k : ℤ) :
    ∑ I ∈ A.filter (fun I ↦ scale I = k),
      ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
      ∫ x, ‖smallestScaleInput S scale f (k - s) x‖ := by
  classical
  let T := A.filter (fun I ↦ scale I = k)
  let b := smallestScaleInput S scale f (k - s)
  have hbridge (I : RealInterval) (hI : I ∈ T) :
      offsetGroupedInput S scale f I s = I.centralThird.indicator b := by
    simpa only [T, b, (Finset.mem_filter.mp hI).2] using
      offsetGroupedInput_eq_indicator_smallestScaleInput
      hlam scale hscale (hA (Finset.mem_filter.mp hI).1) (f : ℝ → ℂ) hs
  have hint (I : RealInterval) (hI : I ∈ T) :
      Integrable (fun x ↦ ‖I.centralThird.indicator b x‖) :=
    by
      simpa only [norm_indicator_eq_indicator_norm] using
        (integrable_smallestScaleInput S scale f (k - s)).norm.indicator
          I.measurableSet_centralThird
  calc
    ∑ I ∈ T, ∫ x, ‖offsetGroupedInput S scale f I s x‖ =
        ∑ I ∈ T, ∫ x, ‖I.centralThird.indicator b x‖ := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [hbridge I hI]
    _ = ∫ x, ∑ I ∈ T, ‖I.centralThird.indicator b x‖ := by
          symm
          exact integral_finsetSum T hint
    _ ≤ ∫ x, ‖b x‖ := by
          apply integral_mono
          · exact integrable_finsetSum T hint
          · exact (integrable_smallestScaleInput S scale f (k - s)).norm
          intro x
          by_cases hex : ∃ I ∈ T, x ∈ I.centralThird
          · obtain ⟨I, hI, hxI⟩ := hex
            have hsum : (∑ J ∈ T, ‖J.centralThird.indicator b x‖) =
                ‖I.centralThird.indicator b x‖ := by
              apply Finset.sum_eq_single I
              · intro J hJ hJI
                have hxJ : x ∉ J.centralThird := by
                  intro hxJ
                  exact Set.disjoint_left.mp
                    (outputScale_centralThird_pairwiseDisjoint hA hlam scale hscale k
                      hJ hI hJI)
                    hxJ hxI
                rw [Set.indicator_of_notMem hxJ, norm_zero]
              · intro hnot
                exact (hnot hI).elim
            change (∑ I ∈ T, ‖I.centralThird.indicator b x‖) ≤ ‖b x‖
            rw [hsum, Set.indicator_of_mem hxI]
          · have hzero : ∀ I ∈ T, ‖I.centralThird.indicator b x‖ = 0 := by
              intro I hI
              have hxI : x ∉ I.centralThird := fun hxI ↦ hex ⟨I, hI, hxI⟩
              rw [Set.indicator_of_notMem hxI, norm_zero]
            change (∑ I ∈ T, ‖I.centralThird.indicator b x‖) ≤ ‖b x‖
            rw [Finset.sum_eq_zero hzero]
            exact norm_nonneg _
    _ = _ := by rfl

/-- A nonoccurring smallest-region scale contributes exactly zero. -/
theorem smallestScaleInput_eq_zero_of_not_mem_image
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (m : ℤ) (hm : m ∉ S.image scale) :
    smallestScaleInput S scale f m = 0 := by
  classical
  funext x
  unfold smallestScaleInput
  apply Finset.sum_eq_zero
  intro J hJ
  exact (hm (Finset.mem_image.mpr ⟨J, (Finset.mem_filter.mp hJ).1,
    (Finset.mem_filter.mp hJ).2⟩)).elim

/-- Summing the preceding fixed-scale inequality over all actual output
scales costs no multiplicity: translation `k ↦ k - s` is injective, and
scales absent from the ambient selected family contribute zero. -/
theorem sum_integral_norm_offsetGroupedInput_allScales_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier) :
    ∑ k ∈ A.image scale, ∑ I ∈ A.filter (fun I ↦ scale I = k),
      ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
      ∫ x in I₀.carrier, ‖f x‖ := by
  classical
  let K := A.image scale
  let shift : ℤ → ℤ := fun k ↦ k - s
  let F : ℤ → ℝ := fun m ↦ ∫ x, ‖smallestScaleInput S scale f m x‖
  let U := (K.image shift).filter fun m ↦ m ∈ S.image scale
  have hfixed (k : ℤ) (hk : k ∈ K) :
      ∑ I ∈ A.filter (fun I ↦ scale I = k),
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤ F (shift k) := by
    simpa only [K, F, shift] using
      sum_integral_norm_offsetGroupedInput_fixedScale_le hA hlam scale hscale f hs k
  have hshift_inj : Set.InjOn shift (↑K : Set ℤ) := by
    intro a ha b hb hab
    dsimp only [shift] at hab
    omega
  have himage :
      (∑ k ∈ K, F (shift k)) = ∑ m ∈ K.image shift, F m := by
    symm
    exact Finset.sum_image hshift_inj
  have hzero (m : ℤ) (hm : m ∈ K.image shift) (hmS : m ∉ S.image scale) : F m = 0 := by
    dsimp only [F]
    rw [smallestScaleInput_eq_zero_of_not_mem_image S scale f m hmS]
    simp
  have hfilter : (∑ m ∈ K.image shift, F m) = ∑ m ∈ U, F m := by
    symm
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro m hmK hmnotU
      apply hzero m hmK
      intro hmS
      exact hmnotU (Finset.mem_filter.mpr ⟨hmK, hmS⟩)
  have hUsub : U ⊆ S.image scale := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  calc
    ∑ k ∈ A.image scale, ∑ I ∈ A.filter (fun I ↦ scale I = k),
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
        ∑ k ∈ K, F (shift k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hfixed k hk
    _ = ∑ m ∈ K.image shift, F m := himage
    _ = ∑ m ∈ U, F m := hfilter
    _ ≤ ∑ m ∈ S.image scale, F m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hUsub
          intro m hm hnot
          exact integral_nonneg fun x ↦ norm_nonneg _
    _ ≤ ∫ x in I₀.carrier, ‖f x‖ := by
          exact sum_integral_norm_smallestScaleInput_le hlam scale hsub f

/-- The offset input is supported on its output interval's central third, so
the local mass occurring in the one-piece energy estimate is its full mass. -/
theorem integral_centralThird_norm_offsetGroupedInput_eq
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (I : RealInterval) (s : ℤ) :
    (∫ x in I.centralThird, ‖offsetGroupedInput S scale f I s x‖) =
      ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
  calc
    (∫ x in I.centralThird, ‖offsetGroupedInput S scale f I s x‖) =
        ∫ x, I.centralThird.indicator
          (fun x ↦ ‖offsetGroupedInput S scale f I s x‖) x := by
            symm
            exact integral_indicator I.measurableSet_centralThird
    _ = ∫ x, ‖I.centralThird.indicator (offsetGroupedInput S scale f I s) x‖ := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [norm_indicator_eq_indicator_norm]
    _ = ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ I.centralThird
          · rw [Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx,
              offsetGroupedInput_eq_zero_of_notMem_centralThird S scale f I s hx,
              norm_zero]

/-- The global fixed-offset square-sum energy bound follows by combining
same-scale orthogonality, the concrete one-piece estimate, and the preceding
ambient mass closure. -/
theorem sum_norm_offsetOutputScaleLp_sq_le_root_mass
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale, ∀ I ∈ A.filter (fun I ↦ scale I = k),
      0 ≤ scale I + 2 - s) :
    ∑ k ∈ A.image scale, ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 ≤
      (432 * positiveDyadicAmplitudeBound ^ 2 * M * (2 : ℝ) ^ (-s)) *
        ∫ x in I₀.carrier, ‖f x‖ := by
  let C : ℝ := 432 * positiveDyadicAmplitudeBound ^ 2 * M * (2 : ℝ) ^ (-s)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpiece (k : ℤ) (hk : k ∈ A.image scale) :
      ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 ≤
        C * ∑ I ∈ A.filter (fun I ↦ scale I = k),
          ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
    calc
      ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 ≤
          ∑ I ∈ A.filter (fun I ↦ scale I = k), C *
            ∫ x in I.centralThird, ‖offsetGroupedInput S scale f I s x‖ := by
              simpa only [C] using norm_offsetOutputScaleLp_sq_le_sum_energy_bounds
                hA hlam scale hscale f hs hM hmass k (hgap k hk)
      _ = C * ∑ I ∈ A.filter (fun I ↦ scale I = k),
          ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro I hI
            rw [integral_centralThird_norm_offsetGroupedInput_eq]
  calc
    ∑ k ∈ A.image scale, ‖offsetOutputScaleLp S A scale f k s‖ ^ 2 ≤
        ∑ k ∈ A.image scale,
          C * ∑ I ∈ A.filter (fun I ↦ scale I = k),
            ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hpiece k hk
    _ = C * ∑ k ∈ A.image scale, ∑ I ∈ A.filter (fun I ↦ scale I = k),
          ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
          rw [Finset.mul_sum]
    _ ≤ C * ∫ x in I₀.carrier, ‖f x‖ := by
          exact mul_le_mul_of_nonneg_left
            (sum_integral_norm_offsetGroupedInput_allScales_le_root hA hlam scale hscale
              f hs I₀ hsub) hC


end
end KrauseLaceyQuadraticDirectScaleEnergy
end QuadraticCarleson
