/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyEnergyClassification
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardSignedSum

/-!
# Signed sums for the scalar near-energy family

This is the energy-based counterpart of the cross-row and signed-sum
argument. The positive bad-scale inputs and the oscillatory pieces are
unchanged. Only the classification hypothesis changes: the diagonal bound
comes from the proved scalar comparison with the near energy.

The cross-row proofs use geometry, local mass, and the actual correlation
bound, and are reproved below for this family. No inclusion into the older
pointwise nonstandard family is claimed.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson
namespace KrauseLaceyScalarNear

open KrauseLaceyBadScale KrauseLaceyStoppingExtraction KrauseLaceyOrderedEnergy

attribute [local instance] Classical.propDecidable

/-- The scalar near family in a single-filter presentation convenient for
the geometric estimates. Its exact equality with the classifier's family
is proved immediately below. -/
noncomputable def intervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : Finset RealInterval :=
  (goodCollection S f 0 I₀).filter fun I ↦
    I.length = (2 : ℝ) ^ (scale I + 2) ∧ k₀ ≤ scale I + 2 - s ∧
      IsEnergyNonstandard (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))

theorem intervals_eq_energyNonstandardIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) :
    intervals S f I₀ k₀ s scale = energyNonstandardIntervals S f I₀ k₀ s scale := by
  ext I
  constructor
  · intro h
    obtain ⟨hg, hlen, hgap, hn⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hg, hlen, hgap⟩, hn⟩
  · intro h
    obtain ⟨he, hn⟩ := Finset.mem_filter.mp h
    obtain ⟨hg, hlen, hgap⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hg, hlen, hgap, hn⟩

theorem intervals_subset
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : intervals S f I₀ k₀ s scale ⊆ S := by
  intro I hI
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1

theorem inner_badPieceLp_eq_zero_of_scale_eq
    {S : Finset RealInterval} (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I J : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale)
    (hJ : J ∈ intervals S f I₀ k₀ s scale)
    (hne : I ≠ J) (heq : scale I = scale J) :
    inner ℝ (badPieceLp S f hf I₀ k₀ s scale I) (badPieceLp S f hf I₀ k₀ s scale J) = 0 := by
  have hlenI := (Finset.mem_filter.mp hI).2.1
  have hlenJ := (Finset.mem_filter.mp hJ).2.1
  have hlen : I.length = J.length := by rw [hlenI, hlenJ, heq]
  have hNS := intervals_subset S f I₀ k₀ s scale
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
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale) :
    (∑ J ∈ N.filter (fun J ↦ scale J + 3 ≤ scale I),
      ‖∫ x, krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x *
        conj (krauseLaceyLocalizedPiece 1 (scale J) J
          (badScaleInput S f I₀ k₀ (scale J + 2 - s)) x)‖) ≤
      (3840 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ / I.length) *
        intervalBadMass S f I₀ k₀ s scale I := by
  let T := N.filter fun J ↦ scale J + 3 ≤ scale I
  let U := T.filter fun J ↦ J.carrier ⊆ I.carrier
  have hNS := intervals_subset S f I₀ k₀ s scale
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
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale) :
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
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    {I : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale) :
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



theorem norm_signed_badPieceLp_sq_le_of_residue
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    (hmod : ∀ I ∈ N, ∀ J ∈ N, scale I % 3 = scale J % 3)
    (c : RealInterval → ℝ) (hc : ∀ I ∈ N, |c I| ≤ 1) :
    ‖∑ I ∈ N, c I • badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤
      (103680 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∑ I ∈ N, intervalBadMass S f I₀ k₀ s scale I := by
  let m := intervalBadMass S f I₀ k₀ s scale
  let E := positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ * (2 : ℝ) ^ (-s)
  let v := badPieceLp S f hf I₀ k₀ s scale
  have hdiag : (∑ I ∈ N, ‖v I‖ ^ 2) ≤ (96000 * E) * ∑ I ∈ N, m I := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I hI
    have hn := (Finset.mem_filter.mp (hN hI)).2
    rw [show v I = localizedPieceLp (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s))
      (integrable_badScaleInput S hf I₀ k₀ _) from rfl, norm_localizedPieceLp_sq]
    dsimp only [E, m, intervalBadMass]
    simpa only [localizedEnergy, mul_assoc] using
      energyNonstandard_badPiece_diagonalEnergy_le hf I₀ k₀ (scale I) s hlam hparent hsub
        hn.1 (hk₀.trans hn.2.1) hn.2.2
  have hrow (I : RealInterval) (hI : I ∈ N) :
      (∑ J ∈ N.filter (fun J ↦ scale J < scale I), |inner ℝ (v I) (v J)|) ≤
        (3840 * E) * m I := by
    have hfilter : N.filter (fun J ↦ scale J < scale I) =
        N.filter (fun J ↦ scale J + 3 ≤ scale I) := by
      ext J
      simp only [Finset.mem_filter]
      constructor
      · intro hJ
        have hm := hmod I hI J hJ.1
        exact ⟨hJ.1, by omega⟩
      · intro hJ
        exact ⟨hJ.1, by omega⟩
    rw [hfilter]
    simpa only [E, m, v, mul_assoc] using
      sum_abs_inner_badPieceLp_le_decay hf I₀ k₀ s hk₀ scale hlam hsub N hN hsmall (hN hI)
  have hrows := Finset.sum_le_sum hrow
  rw [← Finset.mul_sum] at hrows
  have h := signed_sum_sq_le_diagonal_add_crossRows N v scale
    (fun I hI J hJ hne heq ↦ inner_badPieceLp_eq_zero_of_scale_eq f hf I₀ k₀ s scale
      hlam (hN hI) (hN hJ) hne heq) c hc
  change ‖∑ I ∈ N, c I • v I‖ ^ 2 ≤ _
  calc
    _ ≤ (∑ I ∈ N, ‖v I‖ ^ 2) +
        2 * ∑ I ∈ N, ∑ J ∈ N.filter (fun J ↦ scale J < scale I),
          |inner ℝ (v I) (v J)| := h
    _ ≤ (96000 * E) * (∑ I ∈ N, m I) + 2 * ((3840 * E) * ∑ I ∈ N, m I) :=
      add_le_add hdiag (mul_le_mul_of_nonneg_left hrows (by norm_num))
    _ = _ := by dsimp [E, m]; ring


/-- The full signed-sum estimate is uniform in both the number of
intervals and the number of actual generations. -/
theorem norm_signed_badPieceLp_sq_le_mass
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    (c : RealInterval → ℝ) (hc : ∀ I ∈ N, |c I| ≤ 1) :
    ‖∑ I ∈ N, c I • badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤
      (311040 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∑ I ∈ N, intervalBadMass S f I₀ k₀ s scale I := by
  let R (r : Fin 3) := N.filter fun I ↦ physicalScaleResidue scale I = r
  let w (r : Fin 3) := ∑ I ∈ R r, c I • badPieceLp S f hf I₀ k₀ s scale I
  let C := 103680 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ * (2 : ℝ) ^ (-s)
  have hw (r : Fin 3) : ‖w r‖ ^ 2 ≤
      C * ∑ I ∈ R r, intervalBadMass S f I₀ k₀ s scale I := by
    apply norm_signed_badPieceLp_sq_le_of_residue hf I₀ k₀ s hk₀ scale hlam hparent hsub
      (R r) ((Finset.filter_subset _ N).trans hN)
      (fun J hJ ↦ hsmall J (Finset.mem_filter.mp hJ).1) _ c
      (fun I hI ↦ hc I (Finset.mem_filter.mp hI).1)
    intro I hI J hJ
    exact physicalScaleResidue_eq_imp_mod_eq scale
      ((Finset.mem_filter.mp hI).2.trans (Finset.mem_filter.mp hJ).2.symm)
  have hsum : (∑ I ∈ N, c I • badPieceLp S f hf I₀ k₀ s scale I) = ∑ r : Fin 3, w r := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I (_ : I ∈ N) ↦
      Finset.mem_univ (physicalScaleResidue scale I)) _).symm
  rw [hsum]
  calc
    _ ≤ (∑ r : Fin 3, ‖w r‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ 3 * ∑ r : Fin 3, ‖w r‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun r : Fin 3 ↦ ‖w r‖)
    _ ≤ 3 * ∑ r : Fin 3, C * ∑ I ∈ R r, intervalBadMass S f I₀ k₀ s scale I := by
      gcongr with r
      exact hw r
    _ = _ := by
      rw [← Finset.mul_sum]
      have hm : (∑ r : Fin 3, ∑ I ∈ R r, intervalBadMass S f I₀ k₀ s scale I) =
          ∑ I ∈ N, intervalBadMass S f I₀ k₀ s scale I :=
        Finset.sum_fiberwise_of_maps_to (fun I (_ : I ∈ N) ↦
          Finset.mem_univ (physicalScaleResidue scale I)) _
      rw [hm]
      dsimp [C]
      ring

theorem norm_signed_badPieceLp_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    (c : RealInterval → ℝ) (hc : ∀ I ∈ N, |c I| ≤ 1) :
    ‖∑ I ∈ N, c I • badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤
      (311040 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∫ x, ‖f x‖ := by
  apply (norm_signed_badPieceLp_sq_le_mass hf I₀ k₀ s hk₀ scale hlam hparent hsub N hN
    hsmall c hc).trans
  exact mul_le_mul_of_nonneg_left
    (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam N
      (hN.trans (intervals_subset S f I₀ k₀ s scale))
      (fun I hI ↦ (Finset.mem_filter.mp (hN hI)).2.1))
    (by positivity [intervalL1Average_nonneg f I₀])



end KrauseLaceyScalarNear
end QuadraticCarleson
