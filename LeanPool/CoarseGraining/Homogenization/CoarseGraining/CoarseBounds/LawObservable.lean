/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.Sandwich
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.AeBridge
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables

/-! # Law Observable -/

@[expose] public section

namespace Homogenization

/-!
# Law-level measurability and integrability of the coarse observable (item C3)

The scalar coarse observable
`a ↦ P · 𝐀(cubeSet (originCube d n); a) P`
is almost-everywhere-strongly-measurable under any Chapter 4 `RestrictionLawCarrier`, and —
under a `ThetaEllipticLaw` — almost surely lands in `[0, 2(Θ|p|² + |q|²)]` and is
integrable.

The `RestrictionLawCarrier` a.e.-measurability of every coarse block-matrix entry is
already available
(`RestrictionLawCarrier.aemeasurable_coarseBlockMatrix_{upperLeft,upperRight,lowerLeft,
lowerRight}_apply_cubeSet`, all polarizations of `aemeasurable_Mu_cubeSet`); we
wrap those into the scalar quadratic observable.  The a.s. deterministic bound
comes from feeding the a.e.-elliptic realizations through the C2 bridge to an
everywhere-elliptic representative and applying the C1′ scalar sandwich.
-/

open Homogenization.Book.Ch04
open MeasureTheory

variable {d : ℕ}

/-! ## Measurability -/

/-- Bilinear scalar observable of a block-entry-measurable matrix family is
a.e.-measurable. -/
private theorem aemeasurable_vecDot_matVecMul {L : RestrictionCoeffLaw d} {Bfield : RegCoeffField d → Mat d}
    (u v : Vec d) (hB : ∀ i j, AEMeasurable (fun a => Bfield a i j) L) :
    AEMeasurable (fun a => vecDot u (matVecMul (Bfield a) v)) L := by
  have heq :
      (fun a => vecDot u (matVecMul (Bfield a) v)) =
        ∑ i : Fin d, ∑ j : Fin d, fun a => u i * (Bfield a i j * v j) := by
    funext a
    simp only [vecDot, matVecMul, Finset.mul_sum, Finset.sum_apply]
  rw [heq]
  apply Finset.aemeasurable_sum
  intro i _
  apply Finset.aemeasurable_sum
  intro j _
  exact ((hB i j).mul_const (v j)).const_mul (u i)

/-- The scalar quadratic observable of a block matrix family is a.e.-measurable
whenever all four block entries are. -/
private theorem aemeasurable_blockQuadratic {L : RestrictionCoeffLaw d}
    {Mfield : RegCoeffField d → BlockMat d} (P : BlockVec d)
    (hUL : ∀ i j, AEMeasurable (fun a => (Mfield a).upperLeft i j) L)
    (hUR : ∀ i j, AEMeasurable (fun a => (Mfield a).upperRight i j) L)
    (hLL : ∀ i j, AEMeasurable (fun a => (Mfield a).lowerLeft i j) L)
    (hLR : ∀ i j, AEMeasurable (fun a => (Mfield a).lowerRight i j) L) :
    AEMeasurable (fun a => blockVecDot P (blockMatVecMul (Mfield a) P)) L := by
  obtain ⟨p, q⟩ := P
  have heq :
      (fun a => blockVecDot (p, q) (blockMatVecMul (Mfield a) (p, q))) =
        fun a =>
          vecDot p (matVecMul (Mfield a).upperLeft p) +
              vecDot p (matVecMul (Mfield a).upperRight q) +
            (vecDot q (matVecMul (Mfield a).lowerLeft p) +
              vecDot q (matVecMul (Mfield a).lowerRight q)) := by
    funext a
    simp only [blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd, vecDot_add_right]
  rw [heq]
  exact
    ((aemeasurable_vecDot_matVecMul p p hUL).add
        (aemeasurable_vecDot_matVecMul p q hUR)).add
      ((aemeasurable_vecDot_matVecMul q p hLL).add
        (aemeasurable_vecDot_matVecMul q q hLR))

/-- **C3 (measurability).**  The scalar coarse observable
`a ↦ P · 𝐀(cubeSet (originCube d n); a) P` is a.e.-strongly-measurable under any
`RestrictionLawCarrier`. -/
theorem aestronglyMeasurable_coarseBlockQuadratic_cubeSet
    {L : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier L) (n : ℤ) (P : BlockVec d) :
    AEStronglyMeasurable
      (fun a =>
        blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) P)) L := by
  refine (aemeasurable_blockQuadratic P ?_ ?_ ?_ ?_).aestronglyMeasurable
  · exact fun i j => hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet _ i j
  · exact fun i j => hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet _ i j
  · exact fun i j => hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet _ i j
  · exact fun i j => hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet _ i j

/-! ## A.s. bounds and integrability

The `ThetaEllipticLaw` hypothesis provides only a.e.-in-`x` ellipticity of the
realizations, with no spatial measurability, so it cannot be turned into a
per-realization `IsEllipticFieldOn` without an additional
measurable-representative construction (which would descend through
`IsAEEllipticFieldOn` and the C2 truncation with a chosen strongly-measurable
representative).  We therefore deliver the bounds/integrability against the
pointwise substitute
`∀ᵐ a ∂L, IsEllipticFieldOn 1 Θ (cubeSet (originCube d n)) a`, from which the
deterministic C1′ sandwich transfers realization-by-realization. -/

variable [NeZero d]

/-- **C3 (a.s. bounds).**  Under an a.s.-`(1, Θ)`-elliptic law, the coarse
observable a.s. lands in `[0, 2(Θ|p|² + |q|²)]`. -/
theorem coarseBlockQuadratic_ae_bounds_of_ae_isEllipticFieldOn
    {L : RestrictionCoeffLaw d} {Θ : ℝ} (n : ℤ) (P : BlockVec d)
    (hell : ∀ᵐ a ∂L, IsEllipticFieldOn 1 Θ (cubeSet (originCube d n)) a.toFun) :
    ∀ᵐ a ∂L,
      0 ≤ blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) P) ∧
        blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) P) ≤
          2 * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
  filter_upwards [hell] with a ha
  exact ⟨zero_le_blockVecDot_coarseBlockMatrix_cube ha P,
    blockVecDot_coarseBlockMatrix_cube_le ha P⟩

/-- **C3 (integrability).**  Under a `RestrictionLawCarrier` (for measurability) and an
a.s.-`(1, Θ)`-elliptic law (for the deterministic bound), the coarse observable
is integrable. -/
theorem integrable_coarseBlockQuadratic_of_ae_isEllipticFieldOn
    {L : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier L) {Θ : ℝ} (n : ℤ) (P : BlockVec d)
    (hell : ∀ᵐ a ∂L, IsEllipticFieldOn 1 Θ (cubeSet (originCube d n)) a.toFun) :
    Integrable
      (fun a =>
        blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) P)) L := by
  have : IsProbabilityMeasure L := hP.isProbability
  set C : ℝ := 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) with hC
  refine (integrable_const C).mono'
    (aestronglyMeasurable_coarseBlockQuadratic_cubeSet hP n P) ?_
  filter_upwards [coarseBlockQuadratic_ae_bounds_of_ae_isEllipticFieldOn (Θ := Θ) n P hell]
    with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg ha.1]
  exact ha.2

end Homogenization
