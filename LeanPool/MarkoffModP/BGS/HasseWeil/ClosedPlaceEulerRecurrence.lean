/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionEffectiveDivisorSplit
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceDegreeFiniteness
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaEuler
import Mathlib.Data.Finsupp.Weight

/-!
# The closed-place Euler recurrence

For a finite family of positive integral weights, an effective divisor is a
finitely supported family of multiplicities.  Marking one occurrence of one
place, together with one of as many labels as the place's weight, gives the
coefficient recurrence obtained by logarithmically differentiating the Euler
product.

This file proves that recurrence by an explicit bijection.  It then uses the
local finiteness of bounded-degree places to apply the finite combinatorial
result to all exhaustive places of a finite extension of `K(X)`.
-/

namespace BGS.HasseWeil

open scoped BigOperators

noncomputable section

section FiniteWeightedFamily

variable {I : Type*} [Fintype I] [DecidableEq I]

private abbrev WeightedEffectiveDivisor (w : I → ℕ) (n : ℕ) :=
  {D : I →₀ ℕ // Finsupp.weight w D = n}

@[reducible] private noncomputable def weightedEffectiveDivisorFintype
    (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    Fintype (WeightedEffectiveDivisor w n) :=
  Set.Finite.fintype (Finsupp.finite_of_nat_weight_eq w hw n)

@[ext]
private structure WeightedMarkedEffectiveDivisor (w : I → ℕ) (n : ℕ) where
  divisor : I →₀ ℕ
  place : I
  occurrence : ℕ
  label : ℕ
  weight_eq : Finsupp.weight w divisor = n
  occurrence_lt : occurrence < divisor place
  label_lt : label < w place

@[ext]
private structure WeightedEulerDecomposition (w : I → ℕ) (n : ℕ) where
  leftDegree : ℕ
  rightDegree : ℕ
  split_eq : leftDegree + rightDegree = n
  divisor : I →₀ ℕ
  divisor_weight : Finsupp.weight w divisor = leftDegree
  place : I
  divides : w place ∣ rightDegree + 1
  label : ℕ
  label_lt : label < w place

private def weightedMarkedToEulerDecomposition
    (w : I → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    WeightedMarkedEffectiveDivisor w (n + 1) →
      WeightedEulerDecomposition w n := by
  intro x
  let t := x.occurrence + 1
  let r := t * w x.place
  have htpos : 0 < t := by simp [t]
  have hrpos : 0 < r := Nat.mul_pos htpos (hw x.place)
  have htcoeff : t ≤ x.divisor x.place := by
    dsimp [t]
    exact x.occurrence_lt
  have hsingle : Finsupp.single x.place t ≤ x.divisor :=
    Finsupp.single_le_iff.mpr htcoeff
  let E := x.divisor - Finsupp.single x.place t
  have hrestore : E + Finsupp.single x.place t = x.divisor :=
    tsub_add_cancel_of_le hsingle
  have hweight : Finsupp.weight w E + r = n + 1 := by
    have h := congrArg (Finsupp.weight w) hrestore
    simpa [E, r, Finsupp.weight_single, add_comm] using
      h.trans x.weight_eq
  have hrle : r ≤ n + 1 := by omega
  have hEweight : Finsupp.weight w E = n + 1 - r := by omega
  refine {
    leftDegree := n + 1 - r
    rightDegree := r - 1
    split_eq := ?_
    divisor := E
    divisor_weight := hEweight
    place := x.place
    divides := ⟨t, ?_⟩
    label := x.label
    label_lt := x.label_lt }
  · omega
  · rw [Nat.sub_add_cancel hrpos]
    simp [r, Nat.mul_comm]

private def weightedEulerDecompositionToMarked
    (w : I → ℕ) (_hw : ∀ i, 0 < w i) (n : ℕ) :
    WeightedEulerDecomposition w n →
      WeightedMarkedEffectiveDivisor w (n + 1) := by
  intro x
  let r := x.rightDegree + 1
  let t := r / w x.place
  have htprod : t * w x.place = r := Nat.div_mul_cancel x.divides
  have htpos : 0 < t := by
    by_contra ht
    have htzero : t = 0 := Nat.eq_zero_of_not_pos ht
    rw [htzero, zero_mul] at htprod
    simp [r] at htprod
  let D := x.divisor + Finsupp.single x.place t
  have hweight : Finsupp.weight w D = n + 1 := by
    rw [show Finsupp.weight w D =
        Finsupp.weight w x.divisor + t * w x.place by
      simp [D, Finsupp.weight_single]]
    rw [x.divisor_weight, htprod]
    dsimp [r]
    have hsplit := x.split_eq
    omega
  have htD : t - 1 < D x.place := by
    simp only [D, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  exact {
    divisor := D
    place := x.place
    occurrence := t - 1
    label := x.label
    weight_eq := hweight
    occurrence_lt := htD
    label_lt := x.label_lt }

private def weightedMarkedEffectiveDivisorEquivEulerDecomposition
    (w : I → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    WeightedMarkedEffectiveDivisor w (n + 1) ≃
      WeightedEulerDecomposition w n where
  toFun := weightedMarkedToEulerDecomposition w hw n
  invFun := weightedEulerDecompositionToMarked w hw n
  left_inv := by
    intro x
    apply WeightedMarkedEffectiveDivisor.ext
    · dsimp [weightedEulerDecompositionToMarked,
        weightedMarkedToEulerDecomposition]
      rw [Nat.sub_add_cancel (Nat.mul_pos (by omega) (hw x.place))]
      rw [Nat.mul_div_cancel (x.occurrence + 1) (hw x.place)]
      exact tsub_add_cancel_of_le
        (Finsupp.single_le_iff.mpr x.occurrence_lt)
    · rfl
    · dsimp [weightedEulerDecompositionToMarked,
        weightedMarkedToEulerDecomposition]
      rw [Nat.sub_add_cancel (Nat.mul_pos (by omega) (hw x.place))]
      rw [Nat.mul_div_cancel (x.occurrence + 1) (hw x.place)]
      omega
    · rfl
  right_inv := by
    intro x
    have htpos : 0 < (x.rightDegree + 1) / w x.place := by
      have hprod := Nat.div_mul_cancel x.divides
      by_contra ht
      have hzero : (x.rightDegree + 1) / w x.place = 0 :=
        Nat.eq_zero_of_not_pos ht
      rw [hzero, zero_mul] at hprod
      omega
    apply WeightedEulerDecomposition.ext
    · dsimp [weightedMarkedToEulerDecomposition,
        weightedEulerDecompositionToMarked]
      rw [Nat.sub_add_cancel htpos]
      rw [Nat.div_mul_cancel x.divides]
      have hsplit := x.split_eq
      omega
    · dsimp [weightedMarkedToEulerDecomposition,
        weightedEulerDecompositionToMarked]
      rw [Nat.sub_add_cancel htpos]
      rw [Nat.div_mul_cancel x.divides]
      exact Nat.add_sub_cancel x.rightDegree 1
    · dsimp [weightedMarkedToEulerDecomposition,
        weightedEulerDecompositionToMarked]
      rw [Nat.sub_add_cancel htpos]
      exact add_tsub_cancel_right _ _
    · rfl
    · rfl

private def weightedMarkedEffectiveDivisorEquivSigma
    (w : I → ℕ) (n : ℕ) :
    WeightedMarkedEffectiveDivisor w n ≃
      Σ D : WeightedEffectiveDivisor w n,
        Σ P : I, Fin (D.1 P) × Fin (w P) where
  toFun x :=
    ⟨⟨x.divisor, x.weight_eq⟩, x.place,
      ⟨x.occurrence, x.occurrence_lt⟩,
      ⟨x.label, x.label_lt⟩⟩
  invFun x := {
    divisor := x.1.1
    place := x.2.1
    occurrence := x.2.2.1.1
    label := x.2.2.2.1
    weight_eq := x.1.2
    occurrence_lt := x.2.2.1.2
    label_lt := x.2.2.2.2 }
  left_inv := by intro x; ext <;> rfl
  right_inv := by intro x; rcases x with ⟨D, P, k, l⟩; rfl

@[reducible] private noncomputable def weightedMarkedEffectiveDivisorFintype
    (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    Fintype (WeightedMarkedEffectiveDivisor w n) := by
  letI := weightedEffectiveDivisorFintype w hw n
  exact Fintype.ofEquiv _ (weightedMarkedEffectiveDivisorEquivSigma w n).symm

/-- The number of natural-valued divisors having weighted degree `n` in a
finite family of nonzero weights. -/
noncomputable def weightedEffectiveDivisorCount
    (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) : ℕ :=
  @Fintype.card _ (weightedEffectiveDivisorFintype w hw n)

omit [DecidableEq I] in
private theorem weightedMarkedEffectiveDivisor_card
    (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    @Fintype.card (WeightedMarkedEffectiveDivisor w n)
        (weightedMarkedEffectiveDivisorFintype w hw n) =
      weightedEffectiveDivisorCount w hw n * n := by
  let := weightedEffectiveDivisorFintype w hw n
  let := weightedMarkedEffectiveDivisorFintype w hw n
  rw [Fintype.card_congr (weightedMarkedEffectiveDivisorEquivSigma w n)]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  simp_rw [show ∀ D : WeightedEffectiveDivisor w n,
      ∑ P : I, D.1 P * w P = n by
    intro D
    calc
      ∑ P : I, D.1 P * w P = Finsupp.weight w D.1 := by
        rw [Finsupp.weight_apply]
        simpa using
          (Finsupp.sum_fintype D.1 (fun i c => c • w i) (by simp)).symm
      _ = n := D.2]
  simp [weightedEffectiveDivisorCount]

private def weightedEulerDecompositionEquivSigma
    (w : I → ℕ) (n : ℕ) :
    WeightedEulerDecomposition w n ≃
      Σ ij : {ij : ℕ × ℕ //
          ij ∈ Finset.HasAntidiagonal.antidiagonal n},
        WeightedEffectiveDivisor w ij.1.1 ×
          Σ P : {P : I // w P ∣ ij.1.2 + 1}, Fin (w P.1) where
  toFun x :=
    ⟨⟨(x.leftDegree, x.rightDegree), by
        simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using x.split_eq⟩,
      ⟨⟨x.divisor, x.divisor_weight⟩,
        ⟨⟨x.place, x.divides⟩, ⟨x.label, x.label_lt⟩⟩⟩⟩
  invFun x := {
    leftDegree := x.1.1.1
    rightDegree := x.1.1.2
    split_eq := by
      simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using x.1.2
    divisor := x.2.1.1
    divisor_weight := x.2.1.2
    place := x.2.2.1.1
    divides := x.2.2.1.2
    label := x.2.2.2.1
    label_lt := x.2.2.2.2 }
  left_inv := by intro x; ext <;> rfl
  right_inv := by intro x; rcases x with ⟨ij, D, P, l⟩; rfl

@[reducible] private noncomputable def weightedEulerDecompositionFintype
    (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    Fintype (WeightedEulerDecomposition w n) := by
  letI (m : ℕ) := weightedEffectiveDivisorFintype w hw m
  exact Fintype.ofEquiv _ (weightedEulerDecompositionEquivSigma w n).symm

/-- The degree-weighted sum of the places whose weights divide `r`. -/
def weightedClosedPlaceExtensionCount (w : I → ℕ) (r : ℕ) : ℕ :=
  ∑ P : I, if w P ∣ r then w P else 0

omit [DecidableEq I] in
private theorem weightedEulerDecomposition_card
    (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    @Fintype.card (WeightedEulerDecomposition w n)
        (weightedEulerDecompositionFintype w hw n) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        weightedEffectiveDivisorCount w hw ij.1 *
          weightedClosedPlaceExtensionCount w (ij.2 + 1) := by
  let (m : ℕ) := weightedEffectiveDivisorFintype w hw m
  let := weightedEulerDecompositionFintype w hw n
  rw [Fintype.card_congr (weightedEulerDecompositionEquivSigma w n)]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin]
  simp only [weightedEffectiveDivisorCount]
  have hplace (r : ℕ) :
      (∑ P : {P : I // w P ∣ r}, w P.1) =
        ∑ P : I, if w P ∣ r then w P else 0 := by
    calc
      (∑ P : {P : I // w P ∣ r}, w P.1) =
          ∑ P ∈ Finset.univ.filter (fun P : I => w P ∣ r), w P := by
            symm
            exact Finset.sum_subtype _ (by simp) _
      _ = ∑ P ∈ Finset.univ, if w P ∣ r then w P else 0 :=
        Finset.sum_filter _ _
      _ = ∑ P : I, if w P ∣ r then w P else 0 := by rfl
  simp_rw [hplace]
  rw [Finset.univ_eq_attach]
  simpa only [weightedClosedPlaceExtensionCount] using
    (Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal n)
      (fun ij : ℕ × ℕ =>
        @Fintype.card (WeightedEffectiveDivisor w ij.1)
            (weightedEffectiveDivisorFintype w hw ij.1) *
          ∑ P : I, if w P ∣ ij.2 + 1 then w P else 0))

omit [DecidableEq I] in
/-- The logarithmic-derivative Euler recurrence for any finite family of
positive integral place weights. -/
theorem weightedEffectiveDivisorPointCountRecurrence
    (w : I → ℕ) (hw : ∀ i, 0 < w i) :
    HasEffectiveDivisorPointCountRecurrence
      (weightedEffectiveDivisorCount w (fun i => (hw i).ne'))
      (weightedClosedPlaceExtensionCount w) := by
  intro n
  let := weightedMarkedEffectiveDivisorFintype w
    (fun i => (hw i).ne') (n + 1)
  let := weightedEulerDecompositionFintype w
    (fun i => (hw i).ne') n
  calc
    weightedEffectiveDivisorCount w (fun i => (hw i).ne') (n + 1) *
          (n + 1) =
        Fintype.card (WeightedMarkedEffectiveDivisor w (n + 1)) :=
      (weightedMarkedEffectiveDivisor_card w (fun i => (hw i).ne')
        (n + 1)).symm
    _ = Fintype.card (WeightedEulerDecomposition w n) :=
      Fintype.card_congr
        (weightedMarkedEffectiveDivisorEquivEulerDecomposition w hw n)
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          weightedEffectiveDivisorCount w (fun i => (hw i).ne') ij.1 *
            weightedClosedPlaceExtensionCount w (ij.2 + 1) :=
      weightedEulerDecomposition_card w (fun i => (hw i).ne') n

end FiniteWeightedFamily

section LocalRestriction

variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in
private theorem weightedEffectiveDivisor_support_subset_degreeLE
    (w : J → ℕ) (n bound : ℕ) (hn : n ≤ bound)
    (D : WeightedEffectiveDivisor w n) :
    (D.1.support : Set J) ⊆
      Set.range (Function.Embedding.subtype fun P : J => w P ≤ bound) := by
  intro P hP
  have hne : D.1 P ≠ 0 := Finsupp.mem_support_iff.mp hP
  have hle : w P ≤ bound := by
    calc
      w P ≤ Finsupp.weight w D.1 :=
        Finsupp.le_weight_of_ne_zero' w hne
      _ = n := D.2
      _ ≤ bound := hn
  exact ⟨⟨P, hle⟩, rfl⟩

omit [DecidableEq J] in
private theorem weightedEffectiveDivisor_embDomain_weight
    (w : J → ℕ) (bound : ℕ)
    (E : {P : J // w P ≤ bound} →₀ ℕ) :
    Finsupp.weight w
        (Finsupp.embDomain
          (Function.Embedding.subtype fun P : J => w P ≤ bound) E) =
      Finsupp.weight (fun P : {P : J // w P ≤ bound} => w P.1) E := by
  rw [Finsupp.weight_apply, Finsupp.sum_embDomain,
    Finsupp.weight_apply]
  apply Finsupp.sum_congr
  intro P _
  rfl

private def weightedEffectiveDivisorRestrictEquiv
    (w : J → ℕ) (n bound : ℕ) (hn : n ≤ bound) :
    WeightedEffectiveDivisor w n ≃
      WeightedEffectiveDivisor
        (fun P : {P : J // w P ≤ bound} => w P.1) n where
  toFun D := by
    let e := Function.Embedding.subtype fun P : J => w P ≤ bound
    let E := Finsupp.comapDomain e D.1 e.injective.injOn
    have hrecover : Finsupp.embDomain e E = D.1 :=
      Finsupp.embDomain_comapDomain
        (weightedEffectiveDivisor_support_subset_degreeLE w n bound hn D)
    exact ⟨E, by
      rw [← weightedEffectiveDivisor_embDomain_weight w bound E,
        hrecover]
      exact D.2⟩
  invFun E := by
    let e := Function.Embedding.subtype fun P : J => w P ≤ bound
    exact ⟨Finsupp.embDomain e E.1,
      (weightedEffectiveDivisor_embDomain_weight w bound E.1).trans E.2⟩
  left_inv D := by
    apply Subtype.ext
    dsimp
    exact Finsupp.embDomain_comapDomain
      (weightedEffectiveDivisor_support_subset_degreeLE w n bound hn D)
  right_inv E := by
    apply Subtype.ext
    exact Finsupp.comapDomain_embDomain
      (Function.Embedding.subtype fun P : J => w P ≤ bound) E.1

end LocalRestriction

section FiniteExtension

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

omit [Fintype K] [FiniteDimensional (RatFunc K) L]
    [Algebra.IsSeparable (RatFunc K) L] in
/-- The repository's effective-divisor degree is `Finsupp.weight` for the
closed-place degree function. -/
theorem finiteExtensionEffectiveDivisorDegree_eq_weight
    (D : FiniteExtensionEffectiveDivisor K L) :
    finiteExtensionEffectiveDivisorDegree K L D =
      Finsupp.weight (finiteExtensionPlaceDegree K L) D := by
  rw [finiteExtensionEffectiveDivisorDegree, Finsupp.weight_apply]
  apply Finsupp.sum_congr
  intro P _
  simp

private def finiteExtensionEffectiveDivisorWeightEquiv (n : ℕ) :
    {D : FiniteExtensionEffectiveDivisor K L //
      finiteExtensionEffectiveDivisorDegree K L D = n} ≃
      WeightedEffectiveDivisor (finiteExtensionPlaceDegree K L) n where
  toFun D := ⟨D.1,
    (finiteExtensionEffectiveDivisorDegree_eq_weight K L D.1).symm.trans D.2⟩
  invFun D := ⟨D.1,
    (finiteExtensionEffectiveDivisorDegree_eq_weight K L D.1).trans D.2⟩
  left_inv D := by apply Subtype.ext; rfl
  right_inv D := by apply Subtype.ext; rfl

private def finiteExtensionEffectiveDivisorRestrictEquiv
    (n bound : ℕ) (hn : n ≤ bound) :
    {D : FiniteExtensionEffectiveDivisor K L //
      finiteExtensionEffectiveDivisorDegree K L D = n} ≃
      WeightedEffectiveDivisor
        (fun P : {P : FiniteExtensionPlace K L //
            finiteExtensionPlaceDegree K L P ≤ bound} =>
          finiteExtensionPlaceDegree K L P.1) n := by
  classical
  exact (finiteExtensionEffectiveDivisorWeightEquiv K L n).trans
    (weightedEffectiveDivisorRestrictEquiv
      (finiteExtensionPlaceDegree K L) n bound hn)

private theorem weightedEffectiveDivisorCount_degreeLE_eq_finiteExtensionCount
    (n bound : ℕ) (hn : n ≤ bound) :
    letI := finiteExtensionPlaceDegreeLEFintype K L bound
    weightedEffectiveDivisorCount
        (fun P : {P : FiniteExtensionPlace K L //
            finiteExtensionPlaceDegree K L P ≤ bound} =>
          finiteExtensionPlaceDegree K L P.1)
        (fun P => (finiteExtensionPlaceDegree_pos K L P.1).ne') n =
      finiteExtensionEffectiveDivisorCount K L n := by
  let := finiteExtensionPlaceDegreeLEFintype K L bound
  let := weightedEffectiveDivisorFintype
    (fun P : {P : FiniteExtensionPlace K L //
        finiteExtensionPlaceDegree K L P ≤ bound} =>
      finiteExtensionPlaceDegree K L P.1)
    (fun P => (finiteExtensionPlaceDegree_pos K L P.1).ne') n
  exact Fintype.card_congr
    (finiteExtensionEffectiveDivisorRestrictEquiv K L n bound hn).symm

/-- The extension point count encoded by closed places: a closed place of
degree `d` contributes `d` exactly when `d ∣ r`. -/
noncomputable def finiteExtensionClosedPlaceExtensionCount (r : ℕ) : ℕ := by
  letI := finiteExtensionPlaceDegreeLEFintype K L r
  exact ∑ P : {P : FiniteExtensionPlace K L //
      finiteExtensionPlaceDegree K L P ≤ r},
    if finiteExtensionPlaceDegree K L P.1 ∣ r then
      finiteExtensionPlaceDegree K L P.1 else 0

/-- The closed-place extension count is equivalently the sum of the degrees
over the bounded subtype of places whose degrees divide the level. -/
theorem finiteExtensionClosedPlaceExtensionCount_eq_sum_degree_dvd
    (r : ℕ) :
    finiteExtensionClosedPlaceExtensionCount K L r =
      letI := finiteExtensionPlaceDegreeLEFintype K L r
      ∑ P : {P : {P : FiniteExtensionPlace K L //
          finiteExtensionPlaceDegree K L P ≤ r} //
        finiteExtensionPlaceDegree K L P.1 ∣ r},
        finiteExtensionPlaceDegree K L P.1.1 := by
  let := finiteExtensionPlaceDegreeLEFintype K L r
  let PlaceLE := {P : FiniteExtensionPlace K L //
    finiteExtensionPlaceDegree K L P ≤ r}
  let PlaceDvd := {P : PlaceLE //
    finiteExtensionPlaceDegree K L P.1 ∣ r}
  let degree : PlaceLE → ℕ := fun P =>
    finiteExtensionPlaceDegree K L P.1
  change (∑ P : PlaceLE, if degree P ∣ r then degree P else 0) =
    ∑ P : PlaceDvd, degree P.1
  calc
    (∑ P : PlaceLE, if degree P ∣ r then degree P else 0) =
        ∑ P ∈ Finset.univ.filter (fun P : PlaceLE => degree P ∣ r),
          degree P := by
      symm
      exact Finset.sum_filter _ _
    _ = ∑ P : PlaceDvd, degree P.1 := by
      exact Finset.sum_subtype _ (by intro P; simp [degree]) degree

@[simp]
theorem finiteExtensionClosedPlaceExtensionCount_zero :
    finiteExtensionClosedPlaceExtensionCount K L 0 = 0 := by
  rw [finiteExtensionClosedPlaceExtensionCount_eq_sum_degree_dvd]
  apply Finset.sum_eq_zero
  intro P _
  have hpos := finiteExtensionPlaceDegree_pos K L P.1.1
  have hle := P.1.2
  omega

private theorem weightedClosedPlaceExtensionCount_degreeLE_eq_finiteExtensionCount
    (bound r : ℕ) (hr : 0 < r) (hrb : r ≤ bound) :
    letI := finiteExtensionPlaceDegreeLEFintype K L bound
    weightedClosedPlaceExtensionCount
        (fun P : {P : FiniteExtensionPlace K L //
            finiteExtensionPlaceDegree K L P ≤ bound} =>
          finiteExtensionPlaceDegree K L P.1) r =
      finiteExtensionClosedPlaceExtensionCount K L r := by
  let := finiteExtensionPlaceDegreeLEFintype K L bound
  let := finiteExtensionPlaceDegreeLEFintype K L r
  let Big := {P : FiniteExtensionPlace K L //
    finiteExtensionPlaceDegree K L P ≤ bound}
  let Small := {P : FiniteExtensionPlace K L //
    finiteExtensionPlaceDegree K L P ≤ r}
  let SmallInBig := {P : Big //
    finiteExtensionPlaceDegree K L P.1 ≤ r}
  let e : SmallInBig ≃ Small := {
    toFun := fun P => ⟨P.1.1, P.2⟩
    invFun := fun P => ⟨⟨P.1, P.2.trans hrb⟩, P.2⟩
    left_inv := by intro P; rcases P with ⟨⟨P, hPb⟩, hPr⟩; rfl
    right_inv := by intro P; rcases P with ⟨P, hPr⟩; rfl }
  let f : Big → ℕ := fun P =>
    if finiteExtensionPlaceDegree K L P.1 ∣ r then
      finiteExtensionPlaceDegree K L P.1 else 0
  let g : Small → ℕ := fun P =>
    if finiteExtensionPlaceDegree K L P.1 ∣ r then
      finiteExtensionPlaceDegree K L P.1 else 0
  change (∑ P : Big, f P) = ∑ P : Small, g P
  calc
    (∑ P : Big, f P) =
        ∑ P : Big,
          if finiteExtensionPlaceDegree K L P.1 ≤ r then f P else 0 := by
      apply Finset.sum_congr rfl
      intro P _
      by_cases hle : finiteExtensionPlaceDegree K L P.1 ≤ r
      · simp [hle]
      · have hndiv : ¬ finiteExtensionPlaceDegree K L P.1 ∣ r := by
          intro hdiv
          exact hle (Nat.le_of_dvd hr hdiv)
        simp [f, hle, hndiv]
    _ = ∑ P ∈ Finset.univ.filter
          (fun P : Big => finiteExtensionPlaceDegree K L P.1 ≤ r), f P := by
      symm
      exact Finset.sum_filter _ _
    _ = ∑ P : SmallInBig, f P.1 := by
      exact Finset.sum_subtype _ (by simp) f
    _ = ∑ P : Small, g P := by
      exact Fintype.sum_equiv e (fun P : SmallInBig => f P.1) g (by
        intro P
        rfl)

/-- The effective-divisor coefficients for the exhaustive closed places of a
finite extension satisfy the exact closed-place Euler recurrence. -/
theorem finiteExtensionEffectiveDivisorPointCountRecurrence :
    HasEffectiveDivisorPointCountRecurrence
      (finiteExtensionEffectiveDivisorCount K L)
      (finiteExtensionClosedPlaceExtensionCount K L) := by
  classical
  intro n
  let PlaceLE := {P : FiniteExtensionPlace K L //
    finiteExtensionPlaceDegree K L P ≤ n + 1}
  let w : PlaceLE → ℕ := fun P => finiteExtensionPlaceDegree K L P.1
  let := finiteExtensionPlaceDegreeLEFintype K L (n + 1)
  have hw : ∀ P : PlaceLE, 0 < w P := fun P =>
    finiteExtensionPlaceDegree_pos K L P.1
  have hlocal := weightedEffectiveDivisorPointCountRecurrence w hw n
  calc
    finiteExtensionEffectiveDivisorCount K L (n + 1) * (n + 1) =
        weightedEffectiveDivisorCount w (fun P => (hw P).ne') (n + 1) *
          (n + 1) := by
      rw [weightedEffectiveDivisorCount_degreeLE_eq_finiteExtensionCount
        K L (n + 1) (n + 1) le_rfl]
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          weightedEffectiveDivisorCount w (fun P => (hw P).ne') ij.1 *
            weightedClosedPlaceExtensionCount w (ij.2 + 1) := hlocal
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          finiteExtensionEffectiveDivisorCount K L ij.1 *
            finiteExtensionClosedPlaceExtensionCount K L (ij.2 + 1) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hsplit : ij.1 + ij.2 = n := by
        simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using hij
      have hleft : ij.1 ≤ n + 1 := by omega
      have hright : ij.2 + 1 ≤ n + 1 := by omega
      rw [weightedEffectiveDivisorCount_degreeLE_eq_finiteExtensionCount
        K L ij.1 (n + 1) hleft]
      rw [weightedClosedPlaceExtensionCount_degreeLE_eq_finiteExtensionCount
        K L (n + 1) (ij.2 + 1) (by omega) hright]

end FiniteExtension

end

end BGS.HasseWeil
