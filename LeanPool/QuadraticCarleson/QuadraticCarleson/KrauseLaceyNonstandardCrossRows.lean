/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardGenerations

/-!
# Summable cross rows for the actual nonstandard bad pieces

The small intervals in a cross row need not be disjoint: their actual
restricted bad-scale inputs have no multiplicity. This removes a potential
generation-count loss from the two-scale correlation estimate.
-/

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

noncomputable def intervalBadMass
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval) : ℝ :=
  ∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖

theorem intervalBadMass_nonneg
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval) :
    0 ≤ intervalBadMass S f I₀ k₀ s scale I :=
  integral_nonneg fun _ ↦ norm_nonneg _

theorem carrier_subset_or_disjoint_of_scale_lt
    {S : Finset RealInterval} (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I J : RealInterval} (hI : I ∈ S) (hJ : J ∈ S)
    (hlenI : I.length = (2 : ℝ) ^ (scale I + 2))
    (hlenJ : J.length = (2 : ℝ) ^ (scale J + 2)) (hlt : scale J < scale I) :
    J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier := by
  have hne : I ≠ J := by intro h; subst J; omega
  have hlen : J.length < I.length := by
    rw [hlenI, hlenJ]
    exact (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)) (by omega)
  rcases hlam hI hJ hne with hsub | hsub | hd
  · have heq := interval_eq_of_carrier_subset_of_length_le hsub hlen.le
    exact (hne heq).elim
  · exact Or.inl hsub
  · exact Or.inr hd

theorem inner_localizedPieceLp_eq_re_crossPairing
    (j k : ℤ) (I J : RealInterval) (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    inner ℝ (localizedPieceLp k I f hf) (localizedPieceLp j J g hg) =
      (∫ x, krauseLaceyLocalizedPiece 1 k I f x *
        conj (krauseLaceyLocalizedPiece 1 j J g x)).re := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (krauseLaceyLocalizedPiece 1 k I f x *
        conj (krauseLaceyLocalizedPiece 1 j J g x)).re := by
      apply integral_congr_ae
      filter_upwards [localizedPieceLp_ae_eq k I f hf, localizedPieceLp_ae_eq j J g hg]
        with x hx hy
      rw [hx, hy, real_inner_comm (krauseLaceyLocalizedPiece 1 j J g x),
        real_inner_eq_re_inner ℂ, RCLike.inner_apply]
      rfl
    _ = _ := integral_re (integrable_krauseLaceyLocalizedPiece_crossPairing j k I J hf hg)

theorem abs_inner_localizedPieceLp_le_crossPairing
    (j k : ℤ) (I J : RealInterval) (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    |inner ℝ (localizedPieceLp k I f hf) (localizedPieceLp j J g hg)| ≤
      ‖∫ x, krauseLaceyLocalizedPiece 1 k I f x *
        conj (krauseLaceyLocalizedPiece 1 j J g x)‖ := by
  rw [inner_localizedPieceLp_eq_re_crossPairing]
  exact Complex.abs_re_le_norm _

theorem inner_badPieceLp_eq_zero_of_scale_eq
    {S : Finset RealInterval} (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I J : RealInterval} (hI : I ∈ nonstandardIntervals S f I₀ k₀ s scale)
    (hJ : J ∈ nonstandardIntervals S f I₀ k₀ s scale)
    (hne : I ≠ J) (heq : scale I = scale J) :
    inner ℝ (badPieceLp S f hf I₀ k₀ s scale I) (badPieceLp S f hf I₀ k₀ s scale J) = 0 := by
  have hlenI := (Finset.mem_filter.mp hI).2.1
  have hlenJ := (Finset.mem_filter.mp hJ).2.1
  have hlen : I.length = J.length := by rw [hlenI, hlenJ, heq]
  have hNS := nonstandardIntervals_subset S f I₀ k₀ s scale
  have hd : Disjoint I.carrier J.carrier := by
    rcases hlam (hNS hI) (hNS hJ) hne with hsub | hsub | hd
    · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)).elim
    · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm).elim
    · exact hd
  exact inner_localizedPieceLp_eq_zero_of_disjoint _ _ _ _ _ _ _ _ hlenI hlenJ hd

/-- Sum of the absolute actual pairings over every separated smaller
interval. The result is uniform in the size and depth of the collection. -/
theorem sum_nonstandard_crossPairing_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ nonstandardIntervals S f I₀ k₀ s scale) :
    (∑ J ∈ N.filter (fun J ↦ scale J + 3 ≤ scale I),
      ‖∫ x, krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x *
        conj (krauseLaceyLocalizedPiece 1 (scale J) J
          (badScaleInput S f I₀ k₀ (scale J + 2 - s)) x)‖) ≤
      (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ / I.length) *
        intervalBadMass S f I₀ k₀ s scale I := by
  let T := N.filter fun J ↦ scale J + 3 ≤ scale I
  let U := T.filter fun J ↦ J.carrier ⊆ I.carrier
  have hNS := nonstandardIntervals_subset S f I₀ k₀ s scale
  have hlenI := (Finset.mem_filter.mp hI).2.1
  have hlenJ (J : RealInterval) (hJ : J ∈ N) := (Finset.mem_filter.mp (hN hJ)).2.1
  let P (J : RealInterval) := ‖∫ x, krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x *
    conj (krauseLaceyLocalizedPiece 1 (scale J) J
      (badScaleInput S f I₀ k₀ (scale J + 2 - s)) x)‖
  have hrestrict : (∑ J ∈ T, P J) = ∑ J ∈ U, P J := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ T)
    intro J hJT hJU
    have hJ := Finset.mem_filter.mp hJT
    have hnot : ¬J.carrier ⊆ I.carrier := by
      intro hs
      exact hJU (Finset.mem_filter.mpr ⟨hJT, hs⟩)
    have hd := (carrier_subset_or_disjoint_of_scale_lt scale hlam (hNS hI)
      (hNS (hN hJ.1)) hlenI (hlenJ J hJ.1) (by omega)).resolve_left hnot
    dsimp [P]
    rw [integral_localizedPiece_cross_eq_zero_of_disjoint _ _ _ _ _ _ hlenI
      (hlenJ J hJ.1) hd, norm_zero]
  have hUS : U ⊆ S := (Finset.filter_subset _ T).trans
    ((Finset.filter_subset _ N).trans (hN.trans hNS))
  have hUN : U ⊆ N := (Finset.filter_subset _ T).trans (Finset.filter_subset _ N)
  have hmass : (∑ J ∈ U, intervalBadMass S f I₀ k₀ s scale J) ≤
      10 * intervalL1Average f I₀ * I.length := by
    apply (sum_intervalBadInput_mass_le_local hf I₀ k₀ s scale hlam U hUS
      (fun J hJ ↦ hlenJ J (hUN hJ)) I
      (fun J hJ ↦ (Finset.mem_filter.mp hJ).2)).trans
    rw [← intervalL1Average_mul_length]
    exact mul_le_mul_of_nonneg_right
      (goodCollection_averages_le hsub (Finset.mem_filter.mp hI).1).1 I.length_pos.le
  have hm := intervalBadMass_nonneg S f I₀ k₀ s scale I
  have hC : 0 ≤ 384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 := by positivity
  change (∑ J ∈ T, P J) ≤ _
  rw [hrestrict]
  calc
    _ ≤ ∑ J ∈ U, (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        intervalBadMass S f I₀ k₀ s scale I * intervalBadMass S f I₀ k₀ s scale J := by
      apply Finset.sum_le_sum
      intro J hJ
      exact krauseLaceyLocalizedPiece_crossPairing_le_length _ _ (hsmall J (hUN hJ))
        (Finset.mem_filter.mp ((Finset.filter_subset _ T) hJ)).2 I J hlenI
        (integrable_badScaleInput S hf I₀ k₀ _) (integrable_badScaleInput S hf I₀ k₀ _)
    _ = (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        intervalBadMass S f I₀ k₀ s scale I *
          ∑ J ∈ U, intervalBadMass S f I₀ k₀ s scale J := (Finset.mul_sum _ _ _).symm
    _ ≤ (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        intervalBadMass S f I₀ k₀ s scale I *
          (10 * intervalL1Average f I₀ * I.length) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hm)
    _ = _ := by field_simp; ring

theorem sum_nonstandard_crossPairing_le_decay
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ nonstandardIntervals S f I₀ k₀ s scale) :
    (∑ J ∈ N.filter (fun J ↦ scale J + 3 ≤ scale I),
      ‖∫ x, krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x *
        conj (krauseLaceyLocalizedPiece 1 (scale J) J
          (badScaleInput S f I₀ k₀ (scale J + 2 - s)) x)‖) ≤
      (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * intervalBadMass S f I₀ k₀ s scale I := by
  apply (sum_nonstandard_crossPairing_le hf I₀ k₀ s scale hlam hsub N hN hsmall hI).trans
  have hi := (Finset.mem_filter.mp hI).2
  have hlen : (2 : ℝ) ^ s ≤ I.length := by
    rw [hi.1]
    exact (zpow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2)) (by omega)
  have hc := div_le_div_of_nonneg_left
    (show 0 ≤ 3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ by
      positivity [intervalL1Average_nonneg f I₀]) (by positivity : 0 < (2 : ℝ) ^ s) hlen
  simp only [div_eq_mul_inv, ← zpow_neg] at hc
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hc (intervalBadMass_nonneg S f I₀ k₀ s scale I)

/-- The actual `L²` cross row inherits the proved oscillatory kernel decay. -/
theorem sum_abs_inner_badPieceLp_le_decay
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ nonstandardIntervals S f I₀ k₀ s scale) :
    (∑ J ∈ N.filter (fun J ↦ scale J + 3 ≤ scale I),
      |inner ℝ (badPieceLp S f hf I₀ k₀ s scale I)
        (badPieceLp S f hf I₀ k₀ s scale J)|) ≤
      (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * intervalBadMass S f I₀ k₀ s scale I := by
  apply le_trans _ (sum_nonstandard_crossPairing_le_decay hf I₀ k₀ s hk₀ scale
    hlam hsub N hN hsmall hI)
  apply Finset.sum_le_sum
  intro J hJ
  exact abs_inner_localizedPieceLp_le_crossPairing _ _ _ _ _ _ _ _


end KrauseLaceyBadScale
end QuadraticCarleson
