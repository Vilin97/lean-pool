/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132N14.DiameterDescent

/-!
# Conditional fourteen-point theorem for Erdős Problem 132

This file eliminates the three classified thirteen-point branches after the
internal diameter descent. The two exceptional templates contradict the
fifteen-pair ceiling. In the regular branch, insertion counts give one rare
distance and two copies of each regular chord; the explicit coordinate
moments then contradict planar Cauchy--Schwarz.

The result is conditional on the two interfaces in `PublishedInputs.lean`.
The planar diameter bound is proved internally. It does not settle Erdős
Problem 132 in general.
-/

namespace LeanPool.Erdos132N14

open scoped BigOperators

noncomputable section

theorem sum_of_one_rare_and_double_chords
    (f : Fin 13 → ℝ) (weight : ℝ → ℝ) (rare : ℝ)
    (hcover : ∀ i, f i ∈ insert rare
      ((Finset.univ : Finset (Fin 6)).image regularTridecagonChord))
    (hrareNotChord : ∀ k, rare ≠ regularTridecagonChord k)
    (hrareCard : ((Finset.univ : Finset (Fin 13)).filter
      (fun i ↦ f i = rare)).card = 1)
    (hchordCard : ∀ k, ((Finset.univ : Finset (Fin 13)).filter
      (fun i ↦ f i = regularTridecagonChord k)).card = 2) :
    ∑ i, weight (f i) =
      weight rare + 2 * ∑ k : Fin 6, weight (regularTridecagonChord k) := by
  let C := insert rare
    ((Finset.univ : Finset (Fin 6)).image regularTridecagonChord)
  let distanceClass : Fin 13 → {d // d ∈ C} := fun i ↦ ⟨f i, hcover i⟩
  have hpartition := Finset.sum_fiberwise
    (Finset.univ : Finset (Fin 13)) distanceClass (fun i ↦ weight (f i))
  have hfiber (d : {d // d ∈ C}) :
      ∑ i ∈ (Finset.univ : Finset (Fin 13)) with distanceClass i = d,
          weight (f i) =
        (((Finset.univ : Finset (Fin 13)).filter
          (fun i ↦ f i = d)).card : ℝ) * weight d := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin 13)) with distanceClass i = d,
          weight (f i) =
          ∑ _i ∈ (Finset.univ : Finset (Fin 13)) with distanceClass _i = d,
            weight d := by
        apply Finset.sum_congr rfl
        intro i hi
        have hid : distanceClass i = d := (Finset.mem_filter.mp hi).2
        exact congrArg weight (congrArg Subtype.val hid)
      _ = (((Finset.univ : Finset (Fin 13)).filter
          (fun i ↦ f i = d)).card : ℝ) * weight d := by
        have hfilter :
            ((Finset.univ : Finset (Fin 13)).filter
              (fun i ↦ distanceClass i = d)) =
            (Finset.univ : Finset (Fin 13)).filter (fun i ↦ f i = d) := by
          ext i
          simp [distanceClass, Subtype.ext_iff]
        rw [hfilter, Finset.sum_const]
        simp
  calc
    ∑ i, weight (f i) =
        ∑ d : {d // d ∈ C},
          ∑ i ∈ (Finset.univ : Finset (Fin 13)) with distanceClass i = d,
            weight (f i) := by simpa using hpartition.symm
    _ = ∑ d : {d // d ∈ C},
        (((Finset.univ : Finset (Fin 13)).filter
          (fun i ↦ f i = d)).card : ℝ) * weight d := by
      apply Finset.sum_congr rfl
      intro d _
      exact hfiber d
    _ = ∑ d ∈ C, (((Finset.univ : Finset (Fin 13)).filter
          (fun i ↦ f i = d)).card : ℝ) * weight d := by
      symm
      apply Finset.sum_subtype
      simp [C]
    _ = weight rare + 2 * ∑ k : Fin 6,
        weight (regularTridecagonChord k) := by
      have hrareImage : rare ∉
          (Finset.univ : Finset (Fin 6)).image regularTridecagonChord := by
        intro h
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
        exact hrareNotChord k hk.symm
      rw [show C = insert rare
        ((Finset.univ : Finset (Fin 6)).image regularTridecagonChord) by rfl]
      rw [Finset.sum_insert hrareImage, hrareCard]
      rw [Finset.sum_image (fun a _ b _ hab ↦
        regularTridecagonChord_injective hab)]
      simp_rw [hchordCard]
      simp only [Nat.cast_one, one_mul, Nat.cast_ofNat, add_right_inj]
      rw [Finset.mul_sum]

theorem regular_scaled_chords_eq_realized
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)
    (h : SimilarTo P profile.remaining regularTridecagon.point) :
    (Finset.univ : Finset (Fin 6)).image
        (fun k ↦ h.similarity.ratio * regularTridecagonChord k) =
      P.realizedDistances profile.remaining := by
  have hscaledInjective : Function.Injective
      (fun k ↦ h.similarity.ratio * regularTridecagonChord k) := by
    intro k l hkl
    apply regularTridecagonChord_injective
    exact mul_left_cancel₀ (ne_of_gt h.similarity.ratio_pos) hkl
  have hsubset :
      (Finset.univ : Finset (Fin 6)).image
          (fun k ↦ h.similarity.ratio * regularTridecagonChord k) ⊆
        P.realizedDistances profile.remaining := by
    intro d hd
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hd
    have hle := h.distanceMultiplicity_le regularTridecagon
      (regularTridecagonChord k)
    rw [regularTridecagon_chord_multiplicity] at hle
    apply (P.distanceMultiplicity_pos_iff profile.remaining _).mp
    omega
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [Finset.card_image_of_injective _ hscaledInjective,
    profile.remaining_realizedDistance_card]
  simp

theorem regular_remaining_chord_multiplicity
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)
    (h : SimilarTo P profile.remaining regularTridecagon.point) (k : Fin 6) :
    P.distanceMultiplicity profile.remaining
      (h.similarity.ratio * regularTridecagonChord k) = 13 := by
  rw [h.distanceMultiplicity_eq regularTridecagon]
  exact regularTridecagon_chord_multiplicity k

theorem classified_template_with_large_class_impossible
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)
    (Q : Configuration (Fin 13))
    (hlarge : 24 ≤ Q.distanceMultiplicity Finset.univ 1)
    (h : SimilarTo P profile.remaining Q.point) : False := by
  let d := h.similarity.ratio
  have hremainingLarge : 24 ≤ P.distanceMultiplicity profile.remaining d := by
    simpa [d] using hlarge.trans (h.distanceMultiplicity_le Q 1)
  have hdRemaining : d ∈ P.realizedDistances profile.remaining := by
    apply (P.distanceMultiplicity_pos_iff profile.remaining d).mp
    omega
  have hdErased := congrArg (fun D ↦ d ∈ D)
    profile.erase_endpoint_realizedDistances_eq_erase
  have hdne : d ≠ profile.rareDistance := by
    rw [hdErased] at hdRemaining
    exact (Finset.mem_erase.mp hdRemaining).1
  have hdFull : d ∈ P.realizedDistances Finset.univ :=
    P.realizedDistances_mono (Finset.subset_univ _) hdRemaining
  have hfull := profile.otherMultiplicity d hdFull hdne
  have hmono := P.distanceMultiplicity_mono
    (Finset.subset_univ profile.remaining) d
  omega

theorem regular_chord_insertion_multiplicity
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)
    (h : SimilarTo P profile.remaining regularTridecagon.point) (k : Fin 6) :
    P.insertionMultiplicity profile.deletedVertex profile.remaining
      (h.similarity.ratio * regularTridecagonChord k) = 2 := by
  let d := h.similarity.ratio * regularTridecagonChord k
  have hdRemaining : d ∈ P.realizedDistances profile.remaining := by
    rw [← regular_scaled_chords_eq_realized profile h]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have hdErased := congrArg (fun D ↦ d ∈ D)
    profile.erase_endpoint_realizedDistances_eq_erase
  have hdne : d ≠ profile.rareDistance := by
    rw [hdErased] at hdRemaining
    exact (Finset.mem_erase.mp hdRemaining).1
  have hdFull : d ∈ P.realizedDistances Finset.univ :=
    P.realizedDistances_mono (Finset.subset_univ _) hdRemaining
  have hfull := profile.otherMultiplicity d hdFull hdne
  have hremaining := regular_remaining_chord_multiplicity profile h k
  change P.distanceMultiplicity profile.remaining d = 13 at hremaining
  have hvNot : profile.deletedVertex ∉ profile.remaining := by
    simp [FourteenFailureExactProfile.remaining]
  have hinsert := P.distanceMultiplicity_insert hvNot d
  have huniv : insert profile.deletedVertex profile.remaining = Finset.univ := by
    simp [FourteenFailureExactProfile.remaining]
  rw [huniv, hfull, hremaining] at hinsert
  change P.insertionMultiplicity profile.deletedVertex profile.remaining d = 2
  omega

theorem rare_insertion_multiplicity
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P) :
    P.insertionMultiplicity profile.deletedVertex profile.remaining
      profile.rareDistance = 1 := by
  have hrareNot : profile.rareDistance ∉ P.realizedDistances profile.remaining := by
    rw [profile.erase_endpoint_realizedDistances_eq_erase]
    simp
  have hremaining :
      P.distanceMultiplicity profile.remaining profile.rareDistance = 0 := by
    by_contra hne
    have hpos : 0 < P.distanceMultiplicity profile.remaining profile.rareDistance := by
      omega
    exact hrareNot
      ((P.distanceMultiplicity_pos_iff profile.remaining profile.rareDistance).mp hpos)
  have hvNot : profile.deletedVertex ∉ profile.remaining := by
    simp [FourteenFailureExactProfile.remaining]
  have hinsert := P.distanceMultiplicity_insert hvNot profile.rareDistance
  have huniv : insert profile.deletedVertex profile.remaining = Finset.univ := by
    simp [FourteenFailureExactProfile.remaining]
  rw [huniv, profile.rareMultiplicity, hremaining] at hinsert
  omega

/-- The deleted point pulled back through a classified similarity. -/
def normalizedDeletedPoint
    {P : Configuration (Fin 14)} {S : Finset (Fin 14)}
    {template : Fin 13 → ℂ} (h : SimilarTo P S template) (v : Fin 14) : ℂ :=
  h.similarity.toEquiv.symm (P.point v)

theorem deleted_distance_eq_scaled
    {P : Configuration (Fin 14)} {S : Finset (Fin 14)}
    {template : Fin 13 → ℂ} (h : SimilarTo P S template)
    (v : Fin 14) (i : Fin 13) :
    dist (P.point v) (P.point (h.reindex i)) =
      h.similarity.ratio * dist (normalizedDeletedPoint h v) (template i) := by
  rw [h.point_eq]
  conv_lhs =>
    lhs
    rw [← h.similarity.toEquiv.apply_symm_apply (P.point v)]
  exact h.similarity.map_dist _ _

theorem normalized_distance_filter_card
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)
    (h : SimilarTo P profile.remaining regularTridecagon.point) (d : ℝ) :
    ((Finset.univ : Finset (Fin 13)).filter fun i ↦
      dist (normalizedDeletedPoint h profile.deletedVertex)
        (regularTridecagon.point i) = d).card =
      P.insertionMultiplicity profile.deletedVertex profile.remaining
        (h.similarity.ratio * d) := by
  rw [Configuration.insertionMultiplicity]
  apply Finset.card_bij (fun i _ ↦ (h.reindex i).val)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨(h.reindex i).property, ?_⟩
    rw [deleted_distance_eq_scaled h profile.deletedVertex i]
    exact congrArg (h.similarity.ratio * ·) (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    apply h.reindex.injective
    exact Subtype.ext hij
  · intro w hw
    let sw : {x // x ∈ profile.remaining} := ⟨w, (Finset.mem_filter.mp hw).1⟩
    let i := h.reindex.symm sw
    refine ⟨i, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      have hscaled := deleted_distance_eq_scaled h profile.deletedVertex i
      have hwDistance := (Finset.mem_filter.mp hw).2
      have hvalue : (h.reindex i).val = w := by
        exact congrArg Subtype.val (h.reindex.apply_symm_apply sw)
      rw [hvalue, hwDistance] at hscaled
      exact mul_left_cancel₀ (ne_of_gt h.similarity.ratio_pos) hscaled.symm
    · exact congrArg Subtype.val (h.reindex.apply_symm_apply sw)

/-- Moment data forced by the internally derived insertion edge counts. -/
structure Regular13ExtensionProfile (v : ℂ) where
  /-- The rare insertion distance after similarity normalization. -/
  rareDistance : ℝ
  /-- The regular vertex joined to the deleted point by the rare edge. -/
  rareIndex : Fin 13
  rareDistance_pos : 0 < rareDistance
  rareDistance_sq :
    Complex.normSq (v - regularTridecagonPoint rareIndex) = rareDistance ^ 2
  second_sum :
    ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) =
      rareDistance ^ 2 + 26
  fourth_sum :
    ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) ^ 2 =
      (rareDistance ^ 2) ^ 2 + 78

theorem regular13_extension_profile_of_failure
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)
    (h : SimilarTo P profile.remaining regularTridecagon.point) :
    Nonempty (Regular13ExtensionProfile
      (normalizedDeletedPoint h profile.deletedVertex)) := by
  let ratio := h.similarity.ratio
  let v := normalizedDeletedPoint h profile.deletedVertex
  let rare := profile.rareDistance / ratio
  let f : Fin 13 → ℝ := fun i ↦ dist v (regularTridecagonPoint i)
  let retained : {x // x ∈ profile.remaining} :=
    ⟨profile.retainedEndpoint, profile.retainedEndpoint_mem_remaining⟩
  let rareIndex := h.reindex.symm retained
  have hratioNe : ratio ≠ 0 := ne_of_gt h.similarity.ratio_pos
  have hscaleRare : ratio * rare = profile.rareDistance := by
    exact mul_div_cancel₀ profile.rareDistance hratioNe
  have hindex : (h.reindex rareIndex).val = profile.retainedEndpoint := by
    exact congrArg Subtype.val (h.reindex.apply_symm_apply retained)
  have hactualRare :
      dist (P.point profile.deletedVertex) (P.point (h.reindex rareIndex)) =
        profile.rareDistance := by
    rw [hindex]
    simpa [Configuration.pairDistance,
      FourteenFailureExactProfile.deletedVertex,
      FourteenFailureExactProfile.retainedEndpoint] using profile.rarePair_distance
  have hnormalizedRare : f rareIndex = rare := by
    have hscaled := deleted_distance_eq_scaled h profile.deletedVertex rareIndex
    change dist (P.point profile.deletedVertex) (P.point (h.reindex rareIndex)) =
      ratio * f rareIndex at hscaled
    rw [hactualRare] at hscaled
    apply (eq_div_iff hratioNe).2
    rw [mul_comm]
    exact hscaled.symm
  have hrareNotChord : ∀ k, rare ≠ regularTridecagonChord k := by
    intro k hk
    have hrareCount := rare_insertion_multiplicity profile
    have hchordCount := regular_chord_insertion_multiplicity profile h k
    have heqActual : ratio * regularTridecagonChord k = profile.rareDistance := by
      rw [← hk]
      exact hscaleRare
    rw [heqActual] at hchordCount
    omega
  have hcover : ∀ i, f i ∈ insert rare
      ((Finset.univ : Finset (Fin 6)).image regularTridecagonChord) := by
    intro i
    by_cases hiRare : f i = rare
    · exact Finset.mem_insert.mpr (Or.inl hiRare)
    · apply Finset.mem_insert.mpr
      right
      have hvNot : profile.deletedVertex ∉ profile.remaining := by
        simp [FourteenFailureExactProfile.remaining]
      have hvertexNe : profile.deletedVertex ≠ (h.reindex i).val := by
        intro heq
        exact hvNot (heq ▸ (h.reindex i).property)
      have hedge := pairWith_mem_pairs
        (Finset.mem_univ profile.deletedVertex)
        (Finset.mem_univ (h.reindex i).val) hvertexNe
      have hscaled := deleted_distance_eq_scaled h profile.deletedVertex i
      change dist (P.point profile.deletedVertex) (P.point (h.reindex i)) =
        ratio * f i at hscaled
      have hfull : ratio * f i ∈ P.realizedDistances Finset.univ := by
        apply (P.mem_realizedDistances_iff Finset.univ _).mpr
        refine ⟨pairWith profile.deletedVertex (h.reindex i).val, hedge, ?_⟩
        rw [P.pairDistance_pairWith, hscaled]
      have hnotRare : ratio * f i ≠ profile.rareDistance := by
        intro heq
        apply hiRare
        apply (eq_div_iff hratioNe).2
        rw [mul_comm]
        exact heq
      have hremaining : ratio * f i ∈ P.realizedDistances profile.remaining := by
        rw [profile.erase_endpoint_realizedDistances_eq_erase]
        exact Finset.mem_erase.mpr ⟨hnotRare, hfull⟩
      rw [← regular_scaled_chords_eq_realized profile h] at hremaining
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hremaining
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_univ k, ?_⟩
      apply mul_left_cancel₀ hratioNe
      exact hk
  have hrareCard : ((Finset.univ : Finset (Fin 13)).filter
      (fun i ↦ f i = rare)).card = 1 := by
    have hcard := normalized_distance_filter_card profile h rare
    change ((Finset.univ : Finset (Fin 13)).filter
      (fun i ↦ f i = rare)).card = _ at hcard
    rw [hscaleRare, rare_insertion_multiplicity profile] at hcard
    exact hcard
  have hchordCard : ∀ k, ((Finset.univ : Finset (Fin 13)).filter
      (fun i ↦ f i = regularTridecagonChord k)).card = 2 := by
    intro k
    have hcard := normalized_distance_filter_card profile h
      (regularTridecagonChord k)
    change ((Finset.univ : Finset (Fin 13)).filter
      (fun i ↦ f i = regularTridecagonChord k)).card = _ at hcard
    rw [regular_chord_insertion_multiplicity profile h k] at hcard
    exact hcard
  have hsecondDistances := sum_of_one_rare_and_double_chords
    f (fun x ↦ x ^ 2) rare hcover hrareNotChord hrareCard hchordCard
  rw [regularTridecagon_chord_second_sum] at hsecondDistances
  have hfourthDistances := sum_of_one_rare_and_double_chords
    f (fun x ↦ (x ^ 2) ^ 2) rare hcover hrareNotChord hrareCard hchordCard
  rw [regularTridecagon_chord_fourth_sum] at hfourthDistances
  refine ⟨{
    rareDistance := rare
    rareIndex := rareIndex
    rareDistance_pos := div_pos
      (P.realizedDistance_pos profile.rareDistance_mem) h.similarity.ratio_pos
    rareDistance_sq := ?_
    second_sum := ?_
    fourth_sum := ?_
  }⟩
  · rw [← Complex.sq_norm, ← Complex.dist_eq, ← hnormalizedRare]
  · change ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) =
      rare ^ 2 + 26
    calc
      ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) =
          ∑ i : Fin 13, f i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [f]
        rw [Complex.dist_eq, Complex.sq_norm]
      _ = rare ^ 2 + 26 := hsecondDistances
  · change ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) ^ 2 =
      (rare ^ 2) ^ 2 + 78
    calc
      ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) ^ 2 =
          ∑ i : Fin 13, (f i ^ 2) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [f]
        rw [Complex.dist_eq, Complex.sq_norm]
      _ = (rare ^ 2) ^ 2 + 78 := hfourthDistances

theorem regular13_extension_moment_certificate
    (r2 D2 ip : ℝ)
    (hDpos : 0 < D2)
    (hSecond : 13 * (r2 + 1) = D2 + 26)
    (hFourth : 13 * (r2 ^ 2 + 4 * r2 + 1) = D2 ^ 2 + 78)
    (hPair : D2 = r2 + 1 - 2 * ip)
    (hCauchy : ip ^ 2 ≤ r2) : False := by
  have hD : D2 = 13 * (r2 - 1) := by
    linarith
  have hFactor : (r2 - 1) * (2 * r2 - 3) = 0 := by
    rw [hD] at hFourth
    nlinarith
  rcases mul_eq_zero.mp hFactor with hUnit | hThreeHalves
  · have hr2 : r2 = 1 := by linarith
    nlinarith
  · have hr2 : r2 = 3 / 2 := by linarith
    have hip : ip = -2 := by nlinarith
    nlinarith

theorem regular13_extension_impossible
    {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)
    (h : SimilarTo P profile.remaining regularTridecagon.point) : False := by
  obtain ⟨extension⟩ := regular13_extension_profile_of_failure profile h
  let v := normalizedDeletedPoint h profile.deletedVertex
  let u := regularTridecagonPoint extension.rareIndex
  let D2 := extension.rareDistance ^ 2
  have hu : Complex.normSq u = 1 :=
    normSq_regularTridecagonPoint extension.rareIndex
  have hDpos : 0 < D2 := by
    dsimp [D2]
    nlinarith [extension.rareDistance_pos]
  have hSecond : 13 * (Complex.normSq v + 1) = D2 + 26 := by
    exact (regularTridecagon_second_moment v).symm.trans extension.second_sum
  have hFourth :
      13 * (Complex.normSq v ^ 2 + 4 * Complex.normSq v + 1) =
        D2 ^ 2 + 78 := by
    exact (regularTridecagon_fourth_moment v).symm.trans extension.fourth_sum
  have hPair : D2 = Complex.normSq v + 1 - 2 * planeDot v u := by
    calc
      D2 = Complex.normSq (v - u) := extension.rareDistance_sq.symm
      _ = Complex.normSq v + Complex.normSq u - 2 * planeDot v u :=
        normSq_sub v u
      _ = Complex.normSq v + 1 - 2 * planeDot v u := by rw [hu]
  have hCauchy : planeDot v u ^ 2 ≤ Complex.normSq v := by
    have hsquare : 0 ≤ (v.re * u.im - v.im * u.re) ^ 2 := sq_nonneg _
    have hfull :
        planeDot v u ^ 2 ≤ Complex.normSq v * Complex.normSq u := by
      simp only [planeDot, Complex.normSq_apply] at hsquare ⊢
      nlinarith
    rw [hu, mul_one] at hfull
    exact hfull
  exact regular13_extension_moment_certificate
    (Complex.normSq v) D2 (planeDot v u) hDpos hSecond hFourth hPair hCauchy

/-- Conditional end-to-end fourteen-point case of Erdős Problem 132. The two
arguments are precisely the remaining named published interfaces; the planar
diameter bound, counting, deletion, classified-case elimination, and moment
steps are proved internally. -/
theorem erdos132_for_fourteen_of_published_inputs
    (publishedCardinality : PublishedAtMostSixDistanceCardinalityBound)
    (classification :
      SzollosiOstergardThirteenPointSixDistanceClassification) :
    ∀ P : Configuration (Fin 14), Erdos132ForFourteen P := by
  intro P
  by_contra hfailure
  obtain ⟨profile⟩ := fourteen_failure_exact_profile
    hopfPannwitzLowMultiplicityDistance14 publishedCardinality P hfailure
  have hclassified := classification P profile.remaining
    profile.remaining_card profile.remaining_realizedDistance_card
  cases hclassified with
  | regular13 hregular =>
      exact regular13_extension_impossible profile hregular
  | dodecagonWithCenter hdodecagon =>
      apply classified_template_with_large_class_impossible profile
        dodecagonWithCenter
      · rw [dodecagonWithCenter_unit_distance_multiplicity]
      · exact hdodecagon
  | hexagramWithCenter hhexagram =>
      exact classified_template_with_large_class_impossible profile
        hexagramWithCenter hexagramWithCenter_unit_distance_multiplicity hhexagram

end

end LeanPool.Erdos132N14
