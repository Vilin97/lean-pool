/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyCrossScalePairing

/-!
# Separated-generation pairings of the actual localized pieces

The geometric input here consists of disjoint small intervals inside one
large interval, their actual local mass bounds, and the source scale gap.
These hypotheses are exactly the facts used after KL18 (4.20); no cross
pairing or signed-sum estimate is an input to the theorem.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson


attribute [local instance] Classical.propDecidable

theorem sum_intervalLength_le_of_disjoint
    (S : Finset RealInterval) (I : RealInterval)
    (hdisj : Set.Pairwise (↑S) (Disjoint on RealInterval.carrier))
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier) :
    (∑ J ∈ S, J.length) ≤ I.length := by
  have hI : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) I.carrier :=
    integrableOn_const (by simp)
  have hunion : (⋃ J ∈ S, J.carrier) ⊆ I.carrier := by
    intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨J, hJ, hxJ⟩
    exact hsub J hJ hxJ
  have hsum : (∑ J ∈ S, ∫ _x in J.carrier, (1 : ℝ)) ≤
      ∫ _x in I.carrier, (1 : ℝ) := by
    rw [← integral_biUnion_finset S (fun J _ ↦ J.measurableSet_carrier) hdisj
      (fun J _ ↦ integrableOn_const (by simp))]
    exact setIntegral_mono_set hI (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
      hunion.eventuallyLE
  have hvol (J : RealInterval) : volume.real J.carrier = J.length :=
    J.volume_carrier_toReal
  simpa only [setIntegral_const, smul_eq_mul, mul_one, hvol] using hsum

/-- The sum over a finite interval collection, with the actual input
allowed to depend on the interval's bad scale. -/
noncomputable def krauseLaceyCollectionAction
    (S : Finset RealInterval) (scale : RealInterval → ℤ)
    (b : RealInterval → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ I ∈ S, krauseLaceyLocalizedPiece 1 (scale I) I (b I) x

/-- Exact finite linearity of the cross pairing against a collection. -/
theorem integral_localizedPiece_cross_collection
    (S : Finset RealInterval) (scale : RealInterval → ℤ)
    (b : RealInterval → ℝ → ℂ) (k : ℤ) (I : RealInterval)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hb : ∀ J ∈ S, Integrable (b J)) :
    (∫ x, krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyCollectionAction S scale b x)) =
      ∑ J ∈ S, ∫ x, krauseLaceyLocalizedPiece 1 k I f x *
        conj (krauseLaceyLocalizedPiece 1 (scale J) J (b J) x) := by
  simp only [krauseLaceyCollectionAction, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun J hJ ↦
    integrable_krauseLaceyLocalizedPiece_crossPairing (scale J) k I J hf (hb J hJ))

/-- The localized two-piece kernel decay is `384 D² / |I|²` when
expressed in the source's parent interval length. -/
theorem krauseLaceyLocalizedPiece_crossPairing_le_length
    (j k : ℤ) (hj : 1 ≤ j) (hjk : j + 3 ≤ k) (I J : RealInterval)
    (hscale : I.length = (2 : ℝ) ^ (k + 2))
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ‖∫ x, krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyLocalizedPiece 1 j J g x)‖ ≤
      (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        (∫ x in I.centralThird, ‖f x‖) * ∫ x in J.centralThird, ‖g x‖ := by
  have h := krauseLaceyLocalizedPiece_crossPairing_le j k hj hjk I J hf hg
  have hc : 6 * positiveDyadicAmplitudeBound ^ 2 / ((2 : ℝ) ^ (k - 1)) ^ 2 =
      384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 := by
    rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
    ring
  rwa [hc] at h

/-- The separated-generation bound after summing the small intervals.
Their number never appears: disjoint length packing supplies the bound. -/
theorem krauseLaceyLocalizedPiece_cross_collection_le
    (S : Finset RealInterval) (scale : RealInterval → ℤ)
    (b : RealInterval → ℝ → ℂ) (k : ℤ) (I : RealInterval)
    (hscale : I.length = (2 : ℝ) ^ (k + 2))
    (hdisj : Set.Pairwise (↑S) (Disjoint on RealInterval.carrier))
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier)
    (hsmall : ∀ J ∈ S, 1 ≤ scale J ∧ scale J + 3 ≤ k)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hb : ∀ J ∈ S, Integrable (b J))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.centralThird, ‖b J x‖) ≤ M * J.length) :
    ‖∫ x, krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyCollectionAction S scale b x)‖ ≤
      (384 * positiveDyadicAmplitudeBound ^ 2 * M / I.length) *
        ∫ x in I.centralThird, ‖f x‖ := by
  let m : ℝ := ∫ x in I.centralThird, ‖f x‖
  have hm : 0 ≤ m := integral_nonneg fun _ ↦ norm_nonneg _
  have hC : 0 ≤ 384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 := by positivity
  rw [integral_localizedPiece_cross_collection S scale b k I hf hb]
  calc
    _ ≤ ∑ J ∈ S, ‖∫ x, krauseLaceyLocalizedPiece 1 k I f x *
        conj (krauseLaceyLocalizedPiece 1 (scale J) J (b J) x)‖ := norm_sum_le _ _
    _ ≤ ∑ J ∈ S, (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        m * (M * J.length) := by
      apply Finset.sum_le_sum
      intro J hJ
      apply (krauseLaceyLocalizedPiece_crossPairing_le_length
        (scale J) k (hsmall J hJ).1 (hsmall J hJ).2 I J hscale hf (hb J hJ)).trans
      exact mul_le_mul_of_nonneg_left (hmass J hJ) (mul_nonneg hC hm)
    _ = (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) * m * M *
        ∑ J ∈ S, J.length := by simp_rw [← mul_assoc, Finset.mul_sum]
    _ ≤ (384 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) * m * M *
        I.length := mul_le_mul_of_nonneg_left (sum_intervalLength_le_of_disjoint S I hdisj hsub)
          (mul_nonneg (mul_nonneg hC hm) hM)
    _ = _ := by dsimp [m]; field_simp

/-- The large generation's length lower bound converts the previous
estimate to the geometric `2^(-u)` factor used in KL18 (4.20). -/
theorem krauseLaceyLocalizedPiece_cross_collection_le_generation
    (S : Finset RealInterval) (scale : RealInterval → ℤ)
    (b : RealInterval → ℝ → ℂ) (k u : ℤ) (I : RealInterval)
    (hscale : I.length = (2 : ℝ) ^ (k + 2))
    (hlen : (2 : ℝ) ^ u ≤ I.length)
    (hdisj : Set.Pairwise (↑S) (Disjoint on RealInterval.carrier))
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier)
    (hsmall : ∀ J ∈ S, 1 ≤ scale J ∧ scale J + 3 ≤ k)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hb : ∀ J ∈ S, Integrable (b J))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.centralThird, ‖b J x‖) ≤ M * J.length) :
    ‖∫ x, krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyCollectionAction S scale b x)‖ ≤
      (384 * positiveDyadicAmplitudeBound ^ 2 * M / (2 : ℝ) ^ u) *
        ∫ x in I.centralThird, ‖f x‖ := by
  apply (krauseLaceyLocalizedPiece_cross_collection_le S scale b k I hscale
    hdisj hsub hsmall hf hb hM hmass).trans
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hlen)
    (integral_nonneg fun _ ↦ norm_nonneg _)

/-- Disjoint parent intervals make the actual localized cross pairing
vanish exactly, independently of any cancellation in the input. -/
theorem integral_localizedPiece_cross_eq_zero_of_disjoint
    (j k : ℤ) (I J : RealInterval) (f g : ℝ → ℂ)
    (hI : I.length = (2 : ℝ) ^ (k + 2))
    (hJ : J.length = (2 : ℝ) ^ (j + 2))
    (hdisj : Disjoint I.carrier J.carrier) :
    (∫ x, krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyLocalizedPiece 1 j J g x)) = 0 := by
  have hz (x : ℝ) : krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyLocalizedPiece 1 j J g x) = 0 := by
    by_cases hx : x ∈ I.carrier
    · have hxJ : x ∉ J.carrier := fun hxJ ↦ Set.disjoint_left.mp hdisj hx hxJ
      rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 j J g hJ hxJ]
      simp
    · rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 k I f hI hx, zero_mul]
  simp_rw [hz, integral_zero]

theorem integral_localizedPiece_cross_collection_eq_filter
    (T : Finset RealInterval) (scale : RealInterval → ℤ)
    (b : RealInterval → ℝ → ℂ) (k : ℤ) (I : RealInterval)
    (hI : I.length = (2 : ℝ) ^ (k + 2))
    (hT : ∀ J ∈ T, J.length = (2 : ℝ) ^ (scale J + 2))
    (hgeometry : ∀ J ∈ T, J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hb : ∀ J ∈ T, Integrable (b J)) :
    (∫ x, krauseLaceyLocalizedPiece 1 k I f x *
      conj (krauseLaceyCollectionAction T scale b x)) =
      ∫ x, krauseLaceyLocalizedPiece 1 k I f x *
        conj (krauseLaceyCollectionAction
          (T.filter fun J ↦ J.carrier ⊆ I.carrier) scale b x) := by
  classical
  rw [integral_localizedPiece_cross_collection T scale b k I hf hb,
    integral_localizedPiece_cross_collection _ scale b k I hf
      (fun J hJ ↦ hb J (Finset.mem_filter.mp hJ).1)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ T)
  intro J hJT hJfilter
  have hnot : ¬J.carrier ⊆ I.carrier := by simpa [hJT] using hJfilter
  exact integral_localizedPiece_cross_eq_zero_of_disjoint (scale J) k I J f (b J)
    hI (hT J hJT) ((hgeometry J hJT).resolve_left hnot)

/-- The genuine separated-generation cross term: length decay of the
large generation times its actual total restricted input mass. The small
generation enters only through disjointness and its local mass bound. -/
theorem krauseLaceyCollectionAction_crossPairing_le_generation
    (S T : Finset RealInterval) (scale : RealInterval → ℤ)
    (a b : RealInterval → ℝ → ℂ) (u : ℤ)
    (hS : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hT : ∀ J ∈ T, J.length = (2 : ℝ) ^ (scale J + 2))
    (hlen : ∀ I ∈ S, (2 : ℝ) ^ u ≤ I.length)
    (hdisj : Set.Pairwise (↑T) (Disjoint on RealInterval.carrier))
    (hgeometry : ∀ I ∈ S, ∀ J ∈ T,
      J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsmall : ∀ I ∈ S, ∀ J ∈ T, J.carrier ⊆ I.carrier →
      1 ≤ scale J ∧ scale J + 3 ≤ scale I)
    (ha : ∀ I ∈ S, Integrable (a I))
    (hb : ∀ J ∈ T, Integrable (b J))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ T, (∫ x in J.centralThird, ‖b J x‖) ≤ M * J.length) :
    ‖∫ x, krauseLaceyCollectionAction S scale a x *
      conj (krauseLaceyCollectionAction T scale b x)‖ ≤
      (384 * positiveDyadicAmplitudeBound ^ 2 * M / (2 : ℝ) ^ u) *
        ∑ I ∈ S, ∫ x in I.centralThird, ‖a I x‖ := by
  classical
  have hi (I : RealInterval) (hI : I ∈ S) :
      Integrable (fun x ↦ krauseLaceyLocalizedPiece 1 (scale I) I (a I) x *
        conj (krauseLaceyCollectionAction T scale b x)) := by
    have hh := integrable_finsetSum T (fun J hJ ↦
      integrable_krauseLaceyLocalizedPiece_crossPairing (scale J) (scale I)
        I J (ha I hI) (hb J hJ))
    simpa only [krauseLaceyCollectionAction, map_sum, Finset.mul_sum] using hh
  have heq : (∫ x, krauseLaceyCollectionAction S scale a x *
      conj (krauseLaceyCollectionAction T scale b x)) =
      ∑ I ∈ S, ∫ x, krauseLaceyLocalizedPiece 1 (scale I) I (a I) x *
        conj (krauseLaceyCollectionAction T scale b x) := by
    change (∫ x, (∑ I ∈ S, krauseLaceyLocalizedPiece 1 (scale I) I (a I) x) * _) = _
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum _ hi
  rw [heq, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [integral_localizedPiece_cross_collection_eq_filter T scale b (scale I) I
    (hS I hI) hT (hgeometry I hI) (ha I hI) hb]
  apply krauseLaceyLocalizedPiece_cross_collection_le_generation
    (T.filter fun J ↦ J.carrier ⊆ I.carrier) scale b (scale I) u I
    (hS I hI) (hlen I hI)
  · intro J hJ K hK hne
    exact hdisj (Finset.mem_filter.mp hJ).1 (Finset.mem_filter.mp hK).1 hne
  · intro J hJ
    exact (Finset.mem_filter.mp hJ).2
  · intro J hJ
    exact hsmall I hI J (Finset.mem_filter.mp hJ).1 (Finset.mem_filter.mp hJ).2
  · exact ha I hI
  · intro J hJ
    exact hb J (Finset.mem_filter.mp hJ).1
  · exact hM
  · intro J hJ
    exact hmass J (Finset.mem_filter.mp hJ).1


end QuadraticCarleson
