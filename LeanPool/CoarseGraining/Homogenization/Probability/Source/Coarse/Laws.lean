/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse
public import Mathlib.Probability.Independence.Basic

/-! # Laws -/

@[expose] public section

namespace Homogenization.Source.Coarse

open MeasureTheory

def EuclideanUnitSeparated {d : ℕ}
    (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → 1 ≤ euclideanDist x y

def IsStationary {d : ℕ} (P : Measure (Carrier d)) : Prop :=
  ∀ z : Fin d → ℤ, Measure.map (Carrier.translate z) P = P

def IsUnitRangeDependent {d : ℕ} (P : Measure (Carrier d)) : Prop :=
  ∀ (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V),
    EuclideanUnitSeparated U V →
      ProbabilityTheory.Indep (localSigma U hU) (localSigma V hV) P

def IsIsotropicAndAdjointInvariant {d : ℕ}
    (P : Measure (Carrier d)) : Prop :=
  (∀ (R : Mat d) (hR : IsSignedPermutationMatrix R),
      Measure.map (Carrier.rotate R hR) P = P) ∧
    Measure.map Carrier.adjoint P = P

private theorem euclideanUnitSeparated_biUnion_right {d : ℕ} {ι : Type*}
    {U : Set (Vec d)} {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, EuclideanUnitSeparated U (V i)) :
    EuclideanUnitSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact h i hi hx hyi

private theorem measurableSet_biInter_localSigma_biUnion {d : ℕ} {ι : Type*}
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    {f : ι → Set (Carrier d)} {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (Carrier d) (localSigma (U i) (hU i)) (f i)) :
    @MeasurableSet (Carrier d)
      (localSigma (⋃ i ∈ s, U i) (Finset.measurableSet_biUnion s fun i _ => hU i))
      (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ insert i s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ => hU j
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (Carrier d)
            (localSigma (⋃ j ∈ insert i s, U j) hUnion) (f i) :=
        (localSigma_mono (hU i) hUnion hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (Carrier d)
            (localSigma (⋃ j ∈ insert i s, U j) hUnion) (⋂ j ∈ s, f j) :=
        (localSigma_mono
            (Finset.measurableSet_biUnion s fun j _ => hU j) hUnion hsubset_s)
          (⋂ j ∈ s, f j) (ih fun j hj => hf j (by simp [hj]))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

theorem iIndep_localSigma_of_pairwise_euclideanUnitSeparated
    {d : ℕ} {ι : Type*} (P : Measure (Carrier d))
    [IsProbabilityMeasure P] (hP2 : IsUnitRangeDependent P)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => EuclideanUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => localSigma (U i) (hU i)) P := by
  classical
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ => hU j
      have hsep_union : EuclideanUnitSeparated (U i) (⋃ j ∈ s, U j) := by
        refine euclideanUnitSeparated_biUnion_right (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (Carrier d) (localSigma (⋃ j ∈ s, U j) hUnion)
            (⋂ j ∈ s, f j) :=
        measurableSet_biInter_localSigma_biUnion (U := U) hU
          (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := by
        exact (ProbabilityTheory.Indep_iff
          (localSigma (U i) (hU i)) (localSigma (⋃ j ∈ s, U j) hUnion) P).1
            (hP2 (U i) (⋃ j ∈ s, U j) (hU i) hUnion hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        P (⋂ j ∈ insert i s, f j) = P (f i ∩ ⋂ j ∈ s, f j) := by simp
        _ = P (f i) * P (⋂ j ∈ s, f j) := h_inter
        _ = P (f i) * ∏ j ∈ s, P (f j) := by rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, P (f j) := by simp [Finset.prod_insert, hi]

theorem iIndepFun_of_localObservable_of_pairwise_euclideanUnitSeparated
    {d : ℕ} {ι : Type*} (P : Measure (Carrier d))
    [IsProbabilityMeasure P] (hP2 : IsUnitRangeDependent P)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : ∀ i, Carrier d → β i}
    (hX : ∀ i, IsLocalObservable (U i) (hU i) (X i))
    (hsep : Pairwise fun i j => EuclideanUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndepFun X P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  exact (ProbabilityTheory.iIndep_iff (fun i => localSigma (U i) (hU i)) P).1
    (iIndep_localSigma_of_pairwise_euclideanUnitSeparated (P := P) hP2 hU hsep) s
    (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

end Homogenization.Source.Coarse
