/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessUpper

/-! # Lower Variants -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: PositiveExcessLowerAndIntegrability

Lower large-scale estimates and factor integrability from P4.
-/

theorem lowerLargeScalePositiveExcessRoot_le_largeScaleRootCoeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    Ch04.annealedMomentRoot P hP4.xi
      (fun a =>
        section52LargeScaleWeight hP4.sLower m n *
          parents.sup' hparents
            (fun Q =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                  Ch02.matrixNorm
                    ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                      (1 : Mat d)))
                0)) ≤
      ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
        section52LargeScaleRootCoeff d hP4.xi hP4.sLower m n *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
  classical
  intro parents hparents
  let initial : ℝ := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let K : ℝ := 2 * initial
  let B : ℝ := parents.sup' hparents
    (fun Q => section52UnitDescendantRosenthalBudget Q hP4.xi K)
  let parentFactor : ℝ := ((parents.card : ℝ) ^ (1 / (hP4.xi : ℝ)))
  let entryFactor : ℝ := (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)
  let X : RegCoeffField d → ℝ :=
    fun a =>
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0)
  have hn_nonneg : 0 ≤ n := section52LargeScaleSet_mem_nonneg hn
  have hn_le_m : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
  have hn_cast : ((Int.toNat n : ℕ) : ℤ) = n :=
    Int.toNat_of_nonneg hn_nonneg
  have hnm_nat : Int.toNat n ≤ m := by omega
  have hweight_nonneg : 0 ≤ section52LargeScaleWeight hP4.sLower m n :=
    section52LargeScaleWeight_nonneg m hP4.sLower_nonneg n
  have hinitial_nonneg : 0 ≤ initial := by
    simpa [initial] using
      Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hparentFactor_nonneg : 0 ≤ parentFactor := by
    dsimp [parentFactor]
    positivity
  have hentryFactor_nonneg : 0 ≤ entryFactor := by
    dsimp [entryFactor]
    positivity
  have hX_nonneg : ∀ a, 0 ≤ X a := by
    intro a
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right _ _).trans
      (Finset.le_sup'
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0) hQ0)
  have hfluct :
      Ch04.annealedMomentRoot P hP4.xi X ≤ entryFactor * (parentFactor * B) := by
    have h :=
      lowerLargeScaleFiniteParentFluctuation
        hP hStruct hP4 (m := m) (n := Int.toNat n) hnm_nat
    simpa [X, entryFactor, parentFactor, B, K, parents, hn_cast] using h
  have hB_le :
      B ≤ section52UnitDescendantRosenthalBudget (originCube d n) hP4.xi K := by
    dsimp [B]
    refine Finset.sup'_le hparents _ ?_
    intro Q hQ
    have hQscale : Q.scale = n := scale_eq_of_mem_descendantsAtScale hQ
    exact le_of_eq
      (section52UnitDescendantRosenthalBudget_eq_originCube_of_scale_eq
        Q hn_nonneg hQscale hP4.xi K)
  have hweighted :
      Ch04.annealedMomentRoot P hP4.xi
        (fun a => section52LargeScaleWeight hP4.sLower m n * X a) =
          section52LargeScaleWeight hP4.sLower m n *
            Ch04.annealedMomentRoot P hP4.xi X :=
    section52_annealedMomentRoot_const_mul_of_nonneg
      (Nat.succ_le_of_lt hP4.xi_pos) hweight_nonneg hX_nonneg
  have hB_step :
      section52LargeScaleWeight hP4.sLower m n *
          (entryFactor * (parentFactor * B)) ≤
        section52LargeScaleWeight hP4.sLower m n *
          (entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) hP4.xi K)) := by
    have h1 :
        parentFactor * B ≤
          parentFactor *
            section52UnitDescendantRosenthalBudget (originCube d n) hP4.xi K :=
      mul_le_mul_of_nonneg_left hB_le hparentFactor_nonneg
    have h2 :
        entryFactor * (parentFactor * B) ≤
          entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) hP4.xi K) :=
      mul_le_mul_of_nonneg_left h1 hentryFactor_nonneg
    exact mul_le_mul_of_nonneg_left h2 hweight_nonneg
  have hcoeff_eq :
      section52LargeScaleWeight hP4.sLower m n *
          (entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) hP4.xi K)) =
        entryFactor * section52LargeScaleRootCoeff d hP4.xi hP4.sLower m n * initial := by
    simp [section52LargeScaleRootCoeff, section52LargeScaleLpRootCoeff,
      section52LargeScaleSqrtRootCoeff, section52UnitDescendantRosenthalBudget,
      entryFactor, parentFactor, K, initial]
    ring
  calc
    Ch04.annealedMomentRoot P hP4.xi
        (fun a =>
          section52LargeScaleWeight hP4.sLower m n *
            parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))
        = Ch04.annealedMomentRoot P hP4.xi
            (fun a => section52LargeScaleWeight hP4.sLower m n * X a) := by
          rfl
    _ = section52LargeScaleWeight hP4.sLower m n *
          Ch04.annealedMomentRoot P hP4.xi X := hweighted
    _ ≤ section52LargeScaleWeight hP4.sLower m n *
          (entryFactor * (parentFactor * B)) :=
        mul_le_mul_of_nonneg_left hfluct hweight_nonneg
    _ ≤ section52LargeScaleWeight hP4.sLower m n *
          (entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) hP4.xi K)) := hB_step
    _ = entryFactor * section52LargeScaleRootCoeff d hP4.xi hP4.sLower m n *
          initial := hcoeff_eq

theorem lowerLargeScalePositiveExcessRoot_le_largeScaleRootCoeff_source
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {sSource r : ℝ} {ξ : ℕ}
    (hsSource : 0 < sSource) (hr_nonneg : 0 ≤ r)
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hLowerSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) sSource (.finite 1) a)⁻¹) ^ ξ) P)
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    Ch04.annealedMomentRoot P ξ
      (fun a =>
        section52LargeScaleWeight r m n *
          parents.sup' hparents
            (fun Q =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                  Ch02.matrixNorm
                    ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                      (1 : Mat d)))
                0)) ≤
      ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
        section52LargeScaleRootCoeff d ξ r m n *
          Ch04.lambdaInvMomentAtScale P 0 sSource ξ := by
  classical
  intro parents hparents
  let : IsProbabilityMeasure P := hP.isProbability
  let initial : ℝ := Ch04.lambdaInvMomentAtScale P 0 sSource ξ
  let K : ℝ := 2 * initial
  let B : ℝ := parents.sup' hparents
    (fun Q => section52UnitDescendantRosenthalBudget Q ξ K)
  let parentFactor : ℝ := ((parents.card : ℝ) ^ (1 / (ξ : ℝ)))
  let entryFactor : ℝ := (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)
  let X : RegCoeffField d → ℝ :=
    fun a =>
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0)
  have hn_nonneg : 0 ≤ n := section52LargeScaleSet_mem_nonneg hn
  have hn_cast : ((Int.toNat n : ℕ) : ℤ) = n :=
    Int.toNat_of_nonneg hn_nonneg
  have hnm_nat : Int.toNat n ≤ m := by
    have hn_le_m : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
    omega
  have hparent_scale : ∀ Q ∈ parents, (0 : ℤ) ≤ Q.scale := by
    intro Q hQ
    have hscale : Q.scale = n := scale_eq_of_mem_descendantsAtScale hQ
    rw [hscale]
    exact hn_nonneg
  have hweight_nonneg : 0 ≤ section52LargeScaleWeight r m n :=
    section52LargeScaleWeight_nonneg m hr_nonneg n
  have hinitial_nonneg : 0 ≤ initial := by
    simpa [initial] using
      Ch04.lambdaInvMomentAtScale_nonneg P 0 ξ hsSource
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hparentFactor_nonneg : 0 ≤ parentFactor := by
    dsimp [parentFactor]
    positivity
  have hentryFactor_nonneg : 0 ≤ entryFactor := by
    dsimp [entryFactor]
    positivity
  have hbudget_nonneg :
      ∀ Q : TriadicCube d, 0 ≤ section52UnitDescendantRosenthalBudget Q ξ K :=
    fun Q => section52UnitDescendantRosenthalBudget_nonneg Q ξ hK_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    rcases hparents with ⟨Q0, hQ0⟩
    exact (hbudget_nonneg Q0).trans
      (Finset.le_sup'
        (f := fun Q => section52UnitDescendantRosenthalBudget Q ξ K) hQ0)
  have hOrigin :
      ∀ i j : Fin d,
        Integrable
            (fun a =>
              |Ch04.restrictionCenteredOriginObservable P 0
                (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^
                ξ) P ∧
          (∫ a,
              |Ch04.restrictionCenteredOriginObservable P 0
                (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^
                ξ ∂P) ^
              (1 / (ξ : ℝ)) ≤ K := by
    intro i j
    have h :=
      Ch04.RestrictionLawCarrier.restrictionCenteredOriginObservable_lowerRight_entry_momentRoot_le_two_lambdaInvMomentAtScale
        hP hsSource hξ_one hLowerSourceInt i j
    simpa [K, initial] using h
  have hX_nonneg : ∀ a, 0 ≤ X a := by
    intro a
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right _ _).trans
      (Finset.le_sup'
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0) hQ0)
  have hfluct :
      Ch04.annealedMomentRoot P ξ X ≤ entryFactor * (parentFactor * B) := by
    exact
      Ch04.RestrictionLawCarrier.lowerRight_matrixNorm_positiveExcess_finsetSup_momentRoot_le_of_restrictionUnitRangeDependentLaw
        hP hparents le_rfl hparent_scale hStruct.stationary hStruct.unit_range
        ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
          (1 : Mat d))
        (section52_lowerCenter_entries hP hStruct)
        hξ_two hK_nonneg hB_nonneg
        (fun i j => (hOrigin i j).1)
        (fun i j => (hOrigin i j).2)
        (by
          intro Q hQ
          dsimp [B, section52UnitDescendantRosenthalBudget]
          exact Finset.le_sup'
            (f := fun Q => section52UnitDescendantRosenthalBudget Q ξ K) hQ)
  have hB_le :
      B ≤ section52UnitDescendantRosenthalBudget (originCube d n) ξ K := by
    dsimp [B]
    refine Finset.sup'_le hparents _ ?_
    intro Q hQ
    have hQscale : Q.scale = n := scale_eq_of_mem_descendantsAtScale hQ
    exact le_of_eq
      (section52UnitDescendantRosenthalBudget_eq_originCube_of_scale_eq
        Q hn_nonneg hQscale ξ K)
  have hweighted :
      Ch04.annealedMomentRoot P ξ
        (fun a => section52LargeScaleWeight r m n * X a) =
          section52LargeScaleWeight r m n *
            Ch04.annealedMomentRoot P ξ X :=
    section52_annealedMomentRoot_const_mul_of_nonneg
      hξ_one hweight_nonneg hX_nonneg
  have hB_step :
      section52LargeScaleWeight r m n *
          (entryFactor * (parentFactor * B)) ≤
        section52LargeScaleWeight r m n *
          (entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) ξ K)) := by
    have h1 :
        parentFactor * B ≤
          parentFactor *
            section52UnitDescendantRosenthalBudget (originCube d n) ξ K :=
      mul_le_mul_of_nonneg_left hB_le hparentFactor_nonneg
    have h2 :
        entryFactor * (parentFactor * B) ≤
          entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) ξ K) :=
      mul_le_mul_of_nonneg_left h1 hentryFactor_nonneg
    exact mul_le_mul_of_nonneg_left h2 hweight_nonneg
  have hcoeff_eq :
      section52LargeScaleWeight r m n *
          (entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) ξ K)) =
        entryFactor * section52LargeScaleRootCoeff d ξ r m n * initial := by
    simp [section52LargeScaleRootCoeff, section52LargeScaleLpRootCoeff,
      section52LargeScaleSqrtRootCoeff, section52UnitDescendantRosenthalBudget,
      entryFactor, parentFactor, K, initial]
    ring
  calc
    Ch04.annealedMomentRoot P ξ
        (fun a =>
          section52LargeScaleWeight r m n *
            parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))
        = Ch04.annealedMomentRoot P ξ
            (fun a => section52LargeScaleWeight r m n * X a) := by
          rfl
    _ = section52LargeScaleWeight r m n *
          Ch04.annealedMomentRoot P ξ X := hweighted
    _ ≤ section52LargeScaleWeight r m n *
          (entryFactor * (parentFactor * B)) :=
        mul_le_mul_of_nonneg_left hfluct hweight_nonneg
    _ ≤ section52LargeScaleWeight r m n *
          (entryFactor *
            (parentFactor *
              section52UnitDescendantRosenthalBudget (originCube d n) ξ K)) := hB_step
    _ = entryFactor * section52LargeScaleRootCoeff d ξ r m n *
          initial := hcoeff_eq

theorem lowerLargeScalePositiveExcess_integrable_abs_pow
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    Integrable
      (fun a : RegCoeffField d =>
        ‖(section52LargeScaleWeight hP4.sLower m n *
            parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))‖ ^ hP4.xi) P := by
  classical
  intro parents hparents
  let : IsProbabilityMeasure P := hP.isProbability
  have hn_nonneg : 0 ≤ n := section52LargeScaleSet_mem_nonneg hn
  have hparent_scale : ∀ Q ∈ parents, (0 : ℤ) ≤ Q.scale := by
    intro Q hQ
    have hscale : Q.scale = n := scale_eq_of_mem_descendantsAtScale hQ
    rw [hscale]
    exact hn_nonneg
  have hOrigin :
      ∀ i j : Fin d,
        Integrable
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^
              hP4.xi) P := by
    intro i j
    exact
      (Ch04.RestrictionLawCarrier.restrictionCenteredOriginObservable_lowerRight_entry_momentRoot_le_two_lambdaInvMomentAtScale
        hP hP4.sLower_pos (Nat.succ_le_of_lt hP4.xi_pos)
        hP4.lower_inv_moment_integrable i j).1
  have hBase :
      Integrable
        (fun a : RegCoeffField d =>
          ‖(parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))‖ ^ hP4.xi) P := by
    exact
      Ch04.RestrictionLawCarrier.lowerRight_matrixNorm_positiveExcess_finsetSup_integrable_abs_pow_of_stationary
        hP hparents (n := (0 : ℤ)) (ξ := hP4.xi)
        le_rfl hparent_scale hStruct.stationary
        ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
          (1 : Mat d))
        (section52_lowerCenter_entries hP hStruct)
        hP4.two_le_xi hOrigin
  have hconst :
      Integrable
        (fun a : RegCoeffField d =>
          ‖section52LargeScaleWeight hP4.sLower m n‖ ^ hP4.xi *
            ‖(parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))‖ ^ hP4.xi) P :=
    hBase.const_mul _
  refine hconst.congr ?_
  filter_upwards with a
  rw [← mul_pow, ← norm_mul]

theorem lowerLargeScalePositiveExcess_integrable_abs_pow_source
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {sSource r : ℝ} {ξ : ℕ}
    (hsSource : 0 < sSource) (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hLowerSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) sSource (.finite 1) a)⁻¹) ^ ξ) P)
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    Integrable
      (fun a : RegCoeffField d =>
        ‖(section52LargeScaleWeight r m n *
            parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))‖ ^ ξ) P := by
  classical
  intro parents hparents
  let : IsProbabilityMeasure P := hP.isProbability
  have hn_nonneg : 0 ≤ n := section52LargeScaleSet_mem_nonneg hn
  have hparent_scale : ∀ Q ∈ parents, (0 : ℤ) ≤ Q.scale := by
    intro Q hQ
    have hscale : Q.scale = n := scale_eq_of_mem_descendantsAtScale hQ
    rw [hscale]
    exact hn_nonneg
  have hOrigin :
      ∀ i j : Fin d,
        Integrable
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^
              ξ) P := by
    intro i j
    exact
      (Ch04.RestrictionLawCarrier.restrictionCenteredOriginObservable_lowerRight_entry_momentRoot_le_two_lambdaInvMomentAtScale
        hP hsSource hξ_one hLowerSourceInt i j).1
  have hBase :
      Integrable
        (fun a : RegCoeffField d =>
          ‖(parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))‖ ^ ξ) P := by
    exact
      Ch04.RestrictionLawCarrier.lowerRight_matrixNorm_positiveExcess_finsetSup_integrable_abs_pow_of_stationary
        hP hparents (n := (0 : ℤ)) (ξ := ξ)
        le_rfl hparent_scale hStruct.stationary
        ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
          (1 : Mat d))
        (section52_lowerCenter_entries hP hStruct)
        hξ_two hOrigin
  have hconst :
      Integrable
        (fun a : RegCoeffField d =>
          ‖section52LargeScaleWeight r m n‖ ^ ξ *
            ‖(parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm
                      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                        (1 : Mat d)))
                  0))‖ ^ ξ) P :=
    hBase.const_mul _
  refine hconst.congr ?_
  filter_upwards with a
  rw [← mul_pow, ← norm_mul]

theorem lowerLargeScalePositiveExcess_aemeasurable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    AEMeasurable
      (fun a : RegCoeffField d =>
        section52LargeScaleWeight hP4.sLower m n *
          parents.sup' hparents
            (fun Q =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                  Ch02.matrixNorm
                    ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                      (1 : Mat d)))
                0)) P := by
  intro parents hparents
  exact aemeasurable_const.mul
    (Ch04.RestrictionLawCarrier.aemeasurable_lowerRight_matrixNorm_positiveExcess_finsetSup
      hP hparents
      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
        (1 : Mat d)))

theorem lowerLargeScalePositiveExcess_aemeasurable_source
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {r : ℝ} {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    AEMeasurable
      (fun a : RegCoeffField d =>
        section52LargeScaleWeight r m n *
          parents.sup' hparents
            (fun Q =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                  Ch02.matrixNorm
                    ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                      (1 : Mat d)))
                0)) P := by
  intro parents hparents
  exact aemeasurable_const.mul
    (Ch04.RestrictionLawCarrier.aemeasurable_lowerRight_matrixNorm_positiveExcess_finsetSup
      hP hparents
      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
        (1 : Mat d)))

theorem lowerLargeScalePositiveExcess_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m)
    (a : RegCoeffField d) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    0 ≤
      section52LargeScaleWeight hP4.sLower m n *
        parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm
                  ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                    (1 : Mat d)))
              0) := by
  intro parents hparents
  have hweight : 0 ≤ section52LargeScaleWeight hP4.sLower m n :=
    section52LargeScaleWeight_nonneg m hP4.sLower_nonneg n
  have hsup : 0 ≤
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0) := by
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q0) a.toFun).lowerRight -
          Ch02.matrixNorm
            ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
              (1 : Mat d)))
        0).trans
      (Finset.le_sup'
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0) hQ0)
  exact mul_nonneg hweight hsup

theorem lowerLargeScalePositiveExcess_nonneg_source
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {r : ℝ} (hr_nonneg : 0 ≤ r)
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m)
    (a : RegCoeffField d) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) n
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m hn)
    0 ≤
      section52LargeScaleWeight r m n *
        parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm
                  ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                    (1 : Mat d)))
              0) := by
  intro parents hparents
  have hweight : 0 ≤ section52LargeScaleWeight r m n :=
    section52LargeScaleWeight_nonneg m hr_nonneg n
  have hsup : 0 ≤
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0) := by
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q0) a.toFun).lowerRight -
          Ch02.matrixNorm
            ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
              (1 : Mat d)))
        0).trans
      (Finset.le_sup'
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm
                ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                  (1 : Mat d)))
            0) hQ0)
  exact mul_nonneg hweight hsup

end

end Section52
end Ch05
end Book
end Homogenization
