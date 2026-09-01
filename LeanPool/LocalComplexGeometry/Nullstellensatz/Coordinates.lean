/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Coordinates
import LeanPool.LocalComplexGeometry.Noetherian.Ruckert
import LeanPool.LocalComplexGeometry.Nullstellensatz.ZeroSetGerms

/-!
# Coordinate pullback of local set germs

The analytic Nullstellensatz is invariant under invertible complex-linear
coordinates.  This file records that invariance at the predicate-germ level,
without evaluating abstract function germs away from the origin.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

private theorem continuousLinearMap_tendsto_zero {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    Tendsto L (𝓝 0) (𝓝 0) := by
  have h : Tendsto L (𝓝 (0 : ComplexEuclidean n)) (𝓝 (L 0)) :=
    L.continuous.continuousAt
  rw [show L (0 : ComplexEuclidean n) = (0 : ComplexEuclidean m) by exact map_zero L] at h
  exact h

/-- Pull a local predicate germ back along a continuous complex-linear map. -/
def localSetGermPullback {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    LocalSetGerm m → LocalSetGerm n :=
  fun Z ↦ Z.compTendsto L (continuousLinearMap_tendsto_zero L)

@[simp]
theorem localSetGermPullback_top {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    localSetGermPullback L (⊤ : LocalSetGerm m) = ⊤ := by
  rfl

@[simp]
theorem localSetGermPullback_inf {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (Z W : LocalSetGerm m) :
    localSetGermPullback L (Z ⊓ W) =
      localSetGermPullback L Z ⊓ localSetGermPullback L W := by
  refine Filter.Germ.inductionOn₂ Z W ?_
  intro P Q
  rfl

theorem localSetGermPullback_mono {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) :
    Monotone (localSetGermPullback L) := by
  intro Z W hZW
  refine Filter.Germ.inductionOn₂ Z W ?_ hZW
  intro P Q hPQ
  change
    ((P ∘ L : ComplexEuclidean n → Prop) : LocalSetGerm n) ≤
      ((Q ∘ L : ComplexEuclidean n → Prop) : LocalSetGerm n)
  rw [Filter.Germ.coe_le]
  exact (continuousLinearMap_tendsto_zero L).eventually hPQ

@[simp]
theorem localSetGermPullback_zeroLocus {n m : ℕ}
    (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m)
    (f : HolomorphicGerm m) :
    localSetGermPullback L (germZeroLocus f) =
      germZeroLocus (holomorphicGermPullbackHom L f) := by
  change
    (Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm m)).compTendsto L _ =
      Filter.Germ.map (fun z : ℂ ↦ z = 0)
        (functionGermPullbackHom L (f : FunctionGerm m))
  refine Filter.Germ.inductionOn (f : FunctionGerm m) ?_
  intro F
  rfl

/-- Pullback by a continuous-linear equivalence reflects as well as preserves
inclusion of local set germs. -/
theorem localSetGermPullback_le_iff {n m : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean m)
    (Z W : LocalSetGerm m) :
    localSetGermPullback
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) Z ≤
      localSetGermPullback
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) W ↔
      Z ≤ W := by
  constructor
  · intro h
    refine Filter.Germ.inductionOn₂ Z W ?_ h
    intro P Q hPQ
    change
      ((P ∘ L : ComplexEuclidean n → Prop) : LocalSetGerm n) ≤
        ((Q ∘ L : ComplexEuclidean n → Prop) : LocalSetGerm n) at hPQ
    rw [Filter.Germ.coe_le] at hPQ
    rw [Filter.Germ.coe_le]
    have hcomp := (continuousLinearMap_tendsto_zero
      (L.symm : ComplexEuclidean m →L[ℂ] ComplexEuclidean n)).eventually hPQ
    filter_upwards [hcomp] with x hx
    simpa using hx
  · intro h
    exact localSetGermPullback_mono
      (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean m) h

open scoped Classical in
/-- Pullback commutes with a finite common zero set under an invertible
linear coordinate change. -/
theorem localSetGermPullback_finiteCommonZeroSet {n : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean n)
    (S : Finset (HolomorphicGerm n)) :
    localSetGermPullback
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean n)
        (finiteCommonZeroSet S) =
      finiteCommonZeroSet (S.image (coordinatePullback L)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finiteCommonZeroSet]
  | @insert f S hf ih =>
      simp only [finiteCommonZeroSet, Finset.inf_insert,
        localSetGermPullback_inf, localSetGermPullback_zeroLocus,
        Finset.image_insert]
      congr 1

/-- Mapping an ideal by a coordinate pullback maps its local zero-set germ by
the corresponding geometric pullback. -/
theorem idealZeroSetGerm_map_coordinatePullback {n : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean n)
    (I : Ideal (HolomorphicGerm n)) :
    idealZeroSetGerm (I.map (coordinatePullback L).toRingHom) =
      localSetGermPullback
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean n)
        (idealZeroSetGerm I) := by
  classical
  let S := idealGeneratorFinset I
  let T := S.image (coordinatePullback L)
  have hspanT :
      Ideal.span (T : Set (HolomorphicGerm n)) =
        I.map (coordinatePullback L).toRingHom := by
    rw [← span_idealGeneratorFinset I, Ideal.map_span]
    congr 1
    ext f
    simp [T, S]
  calc
    idealZeroSetGerm (I.map (coordinatePullback L).toRingHom) =
        finiteCommonZeroSet T :=
      idealZeroSetGerm_eq_of_span_eq _ T hspanT
    _ = localSetGermPullback
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean n)
        (finiteCommonZeroSet S) :=
      (localSetGermPullback_finiteCommonZeroSet L S).symm
    _ = localSetGermPullback
        (L : ComplexEuclidean n →L[ℂ] ComplexEuclidean n)
        (idealZeroSetGerm I) := rfl

/-- Vanishing-ideal membership is reflected by an invertible linear
coordinate change. -/
theorem coordinatePullback_mem_vanishingIdeal_iff {n : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean n)
    (I : Ideal (HolomorphicGerm n)) (f : HolomorphicGerm n) :
    coordinatePullback L f ∈
        vanishingIdeal
          (idealZeroSetGerm (I.map (coordinatePullback L).toRingHom)) ↔
      f ∈ vanishingIdeal (idealZeroSetGerm I) := by
  rw [mem_vanishingIdeal, mem_vanishingIdeal,
    idealZeroSetGerm_map_coordinatePullback,
    coordinatePullback_apply,
    ← localSetGermPullback_zeroLocus]
  exact localSetGermPullback_le_iff L
    (idealZeroSetGerm I) (germZeroLocus f)

/-- Equality with the vanishing ideal is invariant under invertible linear
coordinate changes. -/
theorem vanishingIdeal_idealZeroSetGerm_eq_iff_coordinateMap {n : ℕ}
    (L : ComplexEuclidean n ≃L[ℂ] ComplexEuclidean n)
    (I : Ideal (HolomorphicGerm n)) :
    vanishingIdeal
        (idealZeroSetGerm (I.map (coordinatePullback L).toRingHom)) =
        I.map (coordinatePullback L).toRingHom ↔
      vanishingIdeal (idealZeroSetGerm I) = I := by
  let e := coordinatePullback L
  constructor
  · intro hmap
    apply Ideal.ext
    intro f
    calc
      f ∈ vanishingIdeal (idealZeroSetGerm I) ↔
          e f ∈ vanishingIdeal
            (idealZeroSetGerm (I.map e.toRingHom)) :=
        (coordinatePullback_mem_vanishingIdeal_iff L I f).symm
      _ ↔ e f ∈ I.map e.toRingHom := by rw [hmap]
      _ ↔ f ∈ I := Ideal.apply_mem_of_equiv_iff
  · intro hI
    apply Ideal.ext
    intro g
    obtain ⟨f, rfl⟩ := e.surjective g
    calc
      e f ∈ vanishingIdeal
          (idealZeroSetGerm (I.map e.toRingHom)) ↔
        f ∈ vanishingIdeal (idealZeroSetGerm I) :=
          coordinatePullback_mem_vanishingIdeal_iff L I f
      _ ↔ f ∈ I := by rw [hI]
      _ ↔ e f ∈ I.map e.toRingHom := Ideal.apply_mem_of_equiv_iff.symm

end

end LocalComplexGeometry
