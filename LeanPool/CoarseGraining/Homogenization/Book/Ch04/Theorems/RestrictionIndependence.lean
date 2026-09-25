/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionObservable
public import LeanPool.CoarseGraining.Homogenization.Geometry.ScaleColoring

/-! # Restriction Independence -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Restriction-local independence and coloring lemmas

This module owns the finite-family independence consequences of the explicit
restriction-unit-range assumption.  It concerns `RestrictionSigmaR` and
whole-restriction-local random variables only; source-local finite independence
belongs in a separate module.
-/

noncomputable section

open MeasureTheory

/-- Separation from each member of a finite family implies separation from the
union of that family. -/
private theorem areUnitSeparated_biUnion_right {d : ℕ} {ι : Type*} {U : Set (Vec d)}
    {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, AreUnitSeparated U (V i)) :
    AreUnitSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact h i hi hx hyi

/-- Events measurable with respect to finitely many carrier restriction
σ-algebras are measurable with respect to the restriction σ-algebra on the
union of the observation sets. -/
private theorem measurableSet_biInter_restrictionSigmaR_biUnion {d : ℕ} {ι : Type*}
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    {f : ι → Set (RegCoeffField d)} {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (RegCoeffField d) (RestrictionSigmaR (U i) (hU i)) (f i)) :
    @MeasurableSet (RegCoeffField d)
      (RestrictionSigmaR (⋃ i ∈ s, U i) (Finset.measurableSet_biUnion s fun i _ => hU i))
      (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ insert i s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ => hU j
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (RegCoeffField d)
            (RestrictionSigmaR (⋃ j ∈ insert i s, U j) hUnion) (f i) :=
        (RestrictionSigmaR_mono (hU i) hUnion hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (RegCoeffField d)
            (RestrictionSigmaR (⋃ j ∈ insert i s, U j) hUnion) (⋂ j ∈ s, f j) :=
        (RestrictionSigmaR_mono
            (Finset.measurableSet_biUnion s fun j _ => hU j) hUnion hsubset_s)
          (⋂ j ∈ s, f j) (ih fun j hj => hf j (by simp [hj]))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

/-- Restriction-unit-range dependence gives independence of any pairwise
separated finite family of carrier restriction σ-algebras. -/
theorem iIndep_restrictionSigmaR_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {ι : Type*} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {U : ι → Set (Vec d)}
    (hU : ∀ i, MeasurableSet (U i))
    (hP : RestrictionUnitRangeDependentLaw P)
    (hsep : Pairwise fun i j => AreUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => RestrictionSigmaR (U i) (hU i)) P := by
  classical
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ => hU j
      have hsep_union : AreUnitSeparated (U i) (⋃ j ∈ s, U j) := by
        refine areUnitSeparated_biUnion_right (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (RegCoeffField d) (RestrictionSigmaR (⋃ j ∈ s, U j) hUnion)
            (⋂ j ∈ s, f j) :=
        measurableSet_biInter_restrictionSigmaR_biUnion (U := U) hU
          (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := by
        exact (ProbabilityTheory.Indep_iff
          (RestrictionSigmaR (U i) (hU i)) (RestrictionSigmaR (⋃ j ∈ s, U j) hUnion) P).1
            (hP (U i) (⋃ j ∈ s, U j) (hU i) hUnion hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        P (⋂ j ∈ insert i s, f j) = P (f i ∩ ⋂ j ∈ s, f j) := by
          simp
        _ = P (f i) * P (⋂ j ∈ s, f j) := h_inter
        _ = P (f i) * ∏ j ∈ s, P (f j) := by
          rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, P (f j) := by simp [Finset.prod_insert, hi]

/-- Restriction-local random variables indexed by pairwise separated observation
sets are independent under restriction-unit-range dependence. -/
theorem iIndepFun_of_restrictionUnitRangeDependentLaw_of_pairwise_separated
    {d : ℕ} {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {U : ι → Set (Vec d)} {X : ∀ i, RegCoeffField d → β i}
    (hU : ∀ i, MeasurableSet (U i))
    (hP : RestrictionUnitRangeDependentLaw P)
    (hX : ∀ i, IsRestrictionLocalRandomVariable (U i) (hU i) (X i))
    (hsep : Pairwise fun i j => AreUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndepFun X P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  exact (ProbabilityTheory.iIndep_iff (fun i => RestrictionSigmaR (U i) (hU i)) P).1
    (iIndep_restrictionSigmaR_of_restrictionUnitRangeDependentLaw (P := P) hU hP hsep) s
    (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

/-- A single scale-color class of descendant cube observables is an independent
family under the explicit restriction-unit-range dependence assumption. -/
theorem iIndepFun_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {β : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} → Type*}
    [∀ R, MeasurableSpace (β R)]
    {X : ∀ R, RegCoeffField d → β R}
    (hP : RestrictionUnitRangeDependentLaw P)
    (hX : ∀ R,
      IsRestrictionLocalRandomVariable (cubeSet R.1) (measurableSet_cubeSet R.1) (X R)) :
    ProbabilityTheory.iIndepFun X P := by
  classical
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let U : I → Set (Vec d) := fun R => cubeSet R.1
  have hU : ∀ R : I, MeasurableSet (U R) := fun R => measurableSet_cubeSet R.1
  have hXU : ∀ R : I, IsRestrictionLocalRandomVariable (U R) (hU R) (X R) := by
    intro R
    simpa [I, U] using hX R
  have hsep : Pairwise fun R S : I => AreUnitSeparated (U R) (U S) := by
    intro R S hRS x y hx hy
    exact one_le_dist_of_ne_of_mem_descendantsAtScaleScaleColorClass
      (hR := R.2) (hS := S.2)
      (hneq := by
        intro h
        apply hRS
        exact Subtype.ext h)
      hx hy
  simpa [I, U] using
    (iIndepFun_of_restrictionUnitRangeDependentLaw_of_pairwise_separated
      (d := d) (ι := I) (β := β) (P := P) (U := U) (X := X) hU hP hXU hsep)

end

end Ch04
end Book
end Homogenization
