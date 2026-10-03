/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardEnergy
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyGenerationLayers
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyRademacherMenshov

/-!
# Genuine nonstandard generation outputs in `L²`

The functions are the actual localized bad-scale operators, grouped by the
proved minimal-generation construction. Disjoint output supports justify
orthogonality within each generation. No signed-sum estimate is assumed.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers


theorem memLp_localizedPiece_of_integrable (k : ℤ) (I : RealInterval)
    {b : ℝ → ℂ} (hb : Integrable b) : MemLp (krauseLaceyLocalizedPiece 1 k I b) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (integrable_krauseLaceyLocalizedPiece k I hb).aestronglyMeasurable).mpr
  have h := (integrable_krauseLaceyLocalizedPiece_crossPairing k k I I hb hb).norm
  simpa only [norm_mul, RCLike.norm_conj, ← sq] using h

/-- The actual localized piece, represented in the `L²` space. -/
noncomputable def localizedPieceLp (k : ℤ) (I : RealInterval)
    (b : ℝ → ℂ) (hb : Integrable b) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_localizedPiece_of_integrable k I hb).toLp (krauseLaceyLocalizedPiece 1 k I b)

theorem localizedPieceLp_ae_eq (k : ℤ) (I : RealInterval)
    (b : ℝ → ℂ) (hb : Integrable b) :
    localizedPieceLp k I b hb =ᵐ[volume] krauseLaceyLocalizedPiece 1 k I b :=
  (memLp_localizedPiece_of_integrable k I hb).coeFn_toLp

theorem norm_localizedPieceLp_sq (k : ℤ) (I : RealInterval)
    (b : ℝ → ℂ) (hb : Integrable b) :
    ‖localizedPieceLp k I b hb‖ ^ 2 = ∫ x, ‖krauseLaceyLocalizedPiece 1 k I b x‖ ^ 2 := by
  rw [← KrauseLaceyRademacherMenshov.integral_sq_norm_Lp]
  apply integral_congr_ae
  filter_upwards [localizedPieceLp_ae_eq k I b hb] with x hx
  rw [hx]

theorem inner_localizedPieceLp_eq_zero_of_disjoint
    (j k : ℤ) (I J : RealInterval) (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g)
    (hI : I.length = (2 : ℝ) ^ (k + 2))
    (hJ : J.length = (2 : ℝ) ^ (j + 2))
    (hdisj : Disjoint I.carrier J.carrier) :
    inner ℝ (localizedPieceLp k I f hf) (localizedPieceLp j J g hg) = 0 := by
  rw [L2.inner_def]
  have hzero : (fun x ↦ inner ℝ (localizedPieceLp k I f hf x)
      (localizedPieceLp j J g hg x)) =ᵐ[volume] 0 := by
    filter_upwards [localizedPieceLp_ae_eq k I f hf, localizedPieceLp_ae_eq j J g hg]
      with x hx hy
    rw [hx, hy]
    by_cases hxI : x ∈ I.carrier
    · have hxJ : x ∉ J.carrier := fun hxJ ↦ Set.disjoint_left.mp hdisj hxI hxJ
      rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 j J g hJ hxJ, inner_zero_right]
      rfl
    · rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 k I f hI hxI, inner_zero_left]
      rfl
  rw [integral_congr_ae hzero]
  simp

theorem norm_sum_sq_eq_sum_of_inner_zero
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset ι) (v : ι → E)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ S, v i‖ ^ 2 = ∑ i ∈ S, ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hj hji
    exact horth i hi j hj hji.symm
  · intro hn
    exact (hn hi).elim

/-- The actual bad piece at the interval's physical scale. -/
noncomputable def badPieceLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (I : RealInterval) : Lp ℂ 2 (volume : Measure ℝ) :=
  localizedPieceLp (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))
    (integrable_badScaleInput S hf I₀ k₀ _)

/-- The `L²` sum of the bad pieces in generation `n` of the subcollection `N`. -/
noncomputable def badPieceGenerationLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ I ∈ generation N n, badPieceLp S f hf I₀ k₀ s scale I

theorem badPieceGenerationLp_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (n : ℕ) :
    badPieceGenerationLp S f hf I₀ k₀ s scale N n =ᵐ[volume]
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

/-- The genuine generation function `β_n`, as an `L²` element. -/
noncomputable def nonstandardGenerationLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (n : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ I ∈ generation (nonstandardIntervals S f I₀ k₀ s scale) n,
    badPieceLp S f hf I₀ k₀ s scale I

/-- The generation is a.e. equal to its actual finite integral-operator
sum; the `Lp` representative has not changed the mathematical output. -/
theorem nonstandardGenerationLp_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (n : ℕ) :
    nonstandardGenerationLp S f hf I₀ k₀ s scale n =ᵐ[volume]
      krauseLaceyCollectionAction (generation (nonstandardIntervals S f I₀ k₀ s scale) n)
        scale (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by
  have hsum := Lp.coeFn_finsetSum
    (generation (nonstandardIntervals S f I₀ k₀ s scale) n)
    (badPieceLp S f hf I₀ k₀ s scale)
  apply hsum.trans
  have hall : ∀ᵐ x ∂volume, ∀ I ∈ generation (nonstandardIntervals S f I₀ k₀ s scale) n,
      badPieceLp S f hf I₀ k₀ s scale I x =
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x := by
    apply (ae_ball_iff (Finset.countable_toSet _)).mpr
    intro I hI
    exact localizedPieceLp_ae_eq _ _ _ _
  filter_upwards [hall] with x hx
  simp only [Finset.sum_apply, krauseLaceyCollectionAction]
  exact Finset.sum_congr rfl hx

/-- Disjointness of the actual minimal layer gives exact orthogonality,
so its squared norm is the sum of the genuine individual energies. -/
theorem norm_nonstandardGenerationLp_sq_eq
    {S : Finset RealInterval} (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (n : ℕ) :
    ‖nonstandardGenerationLp S f hf I₀ k₀ s scale n‖ ^ 2 =
      ∑ I ∈ generation (nonstandardIntervals S f I₀ k₀ s scale) n,
        ∫ x, ‖krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ^ 2 := by
  classical
  let N := nonstandardIntervals S f I₀ k₀ s scale
  have hN := nonstandardIntervals_subset S f I₀ k₀ s scale
  have hdisj := generation_pairwiseDisjoint
    (S := N) (fun I hI J hJ hne ↦ hlam (hN hI) (hN hJ) hne) n
  rw [nonstandardGenerationLp, norm_sum_sq_eq_sum_of_inner_zero]
  · apply Finset.sum_congr rfl
    intro I hI
    exact norm_localizedPieceLp_sq _ _ _ _
  · intro I hI J hJ hne
    exact inner_localizedPieceLp_eq_zero_of_disjoint _ _ _ _ _ _ _ _
      (Finset.mem_filter.mp (generation_subset N n hI)).2.1
      (Finset.mem_filter.mp (generation_subset N n hJ)).2.1
      (hdisj hI hJ hne)

/-- Each actual nonstandard generation has the derived diagonal energy
bound, uniformly in the number of its intervals and their scales. -/
theorem norm_nonstandardGenerationLp_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier) (n : ℕ) :
    ‖nonstandardGenerationLp S f hf I₀ k₀ s scale n‖ ^ 2 ≤
      (96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∫ x, ‖f x‖ := by
  rw [norm_nonstandardGenerationLp_sq_eq f hf I₀ k₀ s scale hlam n]
  exact sum_nonstandard_badPiece_diagonalEnergy_le hf I₀ k₀ s hk₀ scale hlam hparent hsub
    _ (generation_subset _ n)


end KrauseLaceyBadScale
end QuadraticCarleson
