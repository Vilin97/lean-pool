/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.Source.AKL
public import Mathlib.Probability.Independence.Basic

/-!
# AKL laws, locality, and finite independence

The law-facing AKL assumptions use the integral-generated local sigma algebras
of `AKL.localSigma`.
-/

@[expose] public section

namespace Homogenization.Source.AKL

open MeasureTheory ProbabilityTheory

noncomputable section

variable {d : ℕ} {Θ : ℝ}

/-- Two Borel regions are unit separated for the finite-P2 hypothesis when all
cross distances in the ambient sup metric are at least one. -/
def unitSeparated {d : ℕ} (U V : BorelRegion d) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U.1 → y ∈ V.1 → 1 ≤ supDist x y

/-- A law is stationary when every integer translation preserves it. -/
def Stationary {d : ℕ} {Θ : ℝ} (P : Law d Θ) : Prop :=
  letI : MeasurableSpace (Carrier d Θ) := globalSigma d Θ
  ∀ z : Fin d → ℤ, Measure.map (translate (Θ := Θ) z) P = P

/-- A law has unit range when the AKL local sigma algebras of any two
unit-separated Borel regions are independent. -/
def UnitRangeDependent {d : ℕ} {Θ : ℝ} (P : Law d Θ) : Prop :=
  letI : MeasurableSpace (Carrier d Θ) := globalSigma d Θ
  ∀ U V : BorelRegion d, unitSeparated U V →
    ProbabilityTheory.Indep (localSigma U) (localSigma V) P

private def unionRegion {d : ℕ} {ι : Type*} (s : Finset ι)
    (U : ι → BorelRegion d) : BorelRegion d :=
  ⟨⋃ i ∈ s, (U i).1, s.measurableSet_biUnion fun i _ => (U i).2⟩

private theorem subset_unionRegion {d : ℕ} {ι : Type*} (s : Finset ι)
    (U : ι → BorelRegion d) {i : ι} (hi : i ∈ s) :
    (U i).1 ⊆ (unionRegion s U).1 := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hx⟩⟩

private theorem unitSeparated_unionRegion {d : ℕ} {ι : Type*} (s : Finset ι)
    (U : ι → BorelRegion d) {i : ι} (hi : i ∉ s)
    (hsep : Pairwise fun i j => unitSeparated (U i) (U j)) :
    unitSeparated (U i) (unionRegion s U) := by
  intro x y hxi hy
  rcases Set.mem_iUnion.1 hy with ⟨j, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hjs, hyj⟩
  have hij : i ≠ j := by
    intro h
    apply hi
    simpa [h] using hjs
  exact hsep hij hxi hyj

private theorem localSigma_le_unionRegion {d : ℕ} {Θ : ℝ} {ι : Type*}
    (s : Finset ι) (U : ι → BorelRegion d) {i : ι} (hi : i ∈ s) :
    localSigma (Θ := Θ) (U i) ≤ localSigma (Θ := Θ) (unionRegion s U) :=
  localSigma_mono (subset_unionRegion s U hi)

private theorem measurableSet_biInter_localSigma_unionRegion {d : ℕ} {Θ : ℝ}
    {ι : Type*} (s : Finset ι) (U : ι → BorelRegion d)
    {f : ι → Set (Carrier d Θ)}
    (hf : ∀ i, i ∈ s → @MeasurableSet (Carrier d Θ) (localSigma (U i)) (f i)) :
    @MeasurableSet (Carrier d Θ) (localSigma (unionRegion s U)) (⋂ i ∈ s, f i) := by
  apply s.measurableSet_biInter
  intro i hi
  exact (MeasurableSpace.le_def.mp (localSigma_le_unionRegion s U hi)) (f i) (hf i hi)

private theorem measure_biInter_eq_prod_of_unitRangeDependent {d : ℕ} {Θ : ℝ}
    {ι : Type*} (P : Law d Θ) [IsProbabilityMeasure P]
    (hP : UnitRangeDependent P) (U : ι → BorelRegion d)
    (hsep : Pairwise fun i j => unitSeparated (U i) (U j))
    (s : Finset ι) {f : ι → Set (Carrier d Θ)}
    (hf : ∀ i, i ∈ s → @MeasurableSet (Carrier d Θ) (localSigma (U i)) (f i)) :
    P (⋂ i ∈ s, f i) = ∏ i ∈ s, P (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      have hf_i : @MeasurableSet (Carrier d Θ) (localSigma (U i)) (f i) :=
        hf i (by simp)
      have hf_s : ∀ j, j ∈ s → @MeasurableSet (Carrier d Θ) (localSigma (U j)) (f j) := by
        intro j hj
        exact hf j (by simp [hj])
      have hintersection :
          @MeasurableSet (Carrier d Θ) (localSigma (unionRegion s U)) (⋂ j ∈ s, f j) :=
        measurableSet_biInter_localSigma_unionRegion s U hf_s
      have hindep : ProbabilityTheory.Indep (localSigma (U i))
          (localSigma (unionRegion s U)) P :=
        hP (U i) (unionRegion s U) (unitSeparated_unionRegion s U hi hsep)
      have hfactor := (ProbabilityTheory.Indep_iff (localSigma (U i))
          (localSigma (unionRegion s U)) P).1 hindep (f i) (⋂ j ∈ s, f j)
            hf_i hintersection
      rw [Finset.set_biInter_insert, Finset.prod_insert hi]
      calc
        P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := hfactor
        _ = P (f i) * ∏ j ∈ s, P (f j) := by rw [ih hf_s]

theorem iIndep_localSigma_of_unitRangeDependent
    {d : ℕ} {Θ : ℝ} {ι : Type*}
    (P : Law d Θ) [IsProbabilityMeasure P]
    (hP : UnitRangeDependent P) {U : ι → BorelRegion d}
    (hsep : Pairwise fun i j => unitSeparated (U i) (U j)) :
    letI : MeasurableSpace (Carrier d Θ) := globalSigma d Θ
    ProbabilityTheory.iIndep (fun i => localSigma (U i)) P := by
  let : MeasurableSpace (Carrier d Θ) := globalSigma d Θ
  apply (ProbabilityTheory.iIndep_iff (fun i => localSigma (U i)) P).2
  intro s f hf
  exact measure_biInter_eq_prod_of_unitRangeDependent P hP U hsep s hf

theorem iIndepFun_of_sourceLocal_of_unitRangeDependent
    {d : ℕ} {Θ : ℝ} {ι : Type*}
    (P : Law d Θ) [IsProbabilityMeasure P]
    (hP : UnitRangeDependent P) {U : ι → BorelRegion d}
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : ∀ i, Carrier d Θ → β i}
    (hX : ∀ i, IsSourceLocal (U i) (X i))
    (hsep : Pairwise fun i j => unitSeparated (U i) (U j)) :
    letI : MeasurableSpace (Carrier d Θ) := globalSigma d Θ
    ProbabilityTheory.iIndepFun X P := by
  let : MeasurableSpace (Carrier d Θ) := globalSigma d Θ
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  apply (ProbabilityTheory.iIndep_iff (fun i =>
    MeasurableSpace.comap (X i) inferInstance) P).2
  intro s f hf
  apply measure_biInter_eq_prod_of_unitRangeDependent P hP U hsep s
  intro i hi
  exact (MeasurableSpace.le_def.mp (hX i).comap_le) (f i) (hf i hi)

structure ProbabilisticAssumptions {d : ℕ} {Θ : ℝ}
    (law : Law d Θ) [IsProbabilityMeasure law] where
  stationary : Stationary law
  unitRange : UnitRangeDependent law

end

end Homogenization.Source.AKL
