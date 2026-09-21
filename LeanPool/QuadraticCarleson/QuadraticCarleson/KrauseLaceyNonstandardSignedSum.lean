/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardCrossRows
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyOrderedEnergy

/-!
# Uniform signed sums of the actual nonstandard bad pieces

Physical scales are split into three residue classes solely to guarantee
the proved two-scale kernel separation. All diagonal and cross-row bounds
are derived for the actual bad inputs, and no signed-sum bound is assumed.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyOrderedEnergy

attribute [local instance] Classical.propDecidable

theorem norm_signed_badPieceLp_sq_le_of_residue
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
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
    simpa only [mul_assoc] using
      nonstandard_badPiece_diagonalEnergy_le hf I₀ k₀ (scale I) s hlam hparent hsub
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

/-- Three physical-scale residues, not the paper's separate sparsification modulus. -/
def physicalScaleResidue (scale : RealInterval → ℤ) (I : RealInterval) : Fin 3 :=
  ⟨(scale I % 3).toNat, by
    have := Int.emod_nonneg (scale I) (by norm_num : (3 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos (scale I) (by norm_num : (0 : ℤ) < 3)
    omega⟩

theorem physicalScaleResidue_eq_imp_mod_eq
    (scale : RealInterval → ℤ) {I J : RealInterval}
    (h : physicalScaleResidue scale I = physicalScaleResidue scale J) :
    scale I % 3 = scale J % 3 := by
  have hv := congrArg Fin.val h
  have hI := Int.emod_nonneg (scale I) (by norm_num : (3 : ℤ) ≠ 0)
  have hJ := Int.emod_nonneg (scale J) (by norm_num : (3 : ℤ) ≠ 0)
  dsimp [physicalScaleResidue] at hv
  omega

/-- The full signed-sum estimate is uniform in both the number of
intervals and the number of actual generations. -/
theorem norm_signed_badPieceLp_sq_le_mass
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
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
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    (c : RealInterval → ℝ) (hc : ∀ I ∈ N, |c I| ≤ 1) :
    ‖∑ I ∈ N, c I • badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤
      (311040 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∫ x, ‖f x‖ := by
  apply (norm_signed_badPieceLp_sq_le_mass hf I₀ k₀ s hk₀ scale hlam hparent hsub N hN
    hsmall c hc).trans
  exact mul_le_mul_of_nonneg_left
    (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam N
      (hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale))
      (fun I hI ↦ (Finset.mem_filter.mp (hN hI)).2.1))
    (by positivity [intervalL1Average_nonneg f I₀])


end KrauseLaceyBadScale
end QuadraticCarleson
