/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.Coefficients

/-! # Fluctuation Bridge -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: FluctuationBridge

Pointwise fluctuation bridges for positive-excess bounds.
-/

theorem finsetSupReal_eq_sup' {α : Type*}
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    Ch02.finsetSupReal s f = s.sup' hs f := by
  apply le_antisymm
  · exact Ch02.finsetSupReal_le s hs (fun x hx => Finset.le_sup' f hx)
  · refine Finset.sup'_le hs f ?_
    intro x hx
    unfold Ch02.finsetSupReal
    have hbdd : BddAbove (f '' (↑s : Set α)) :=
      ((Set.toFinite _).image f).bddAbove
    exact le_csSup hbdd ⟨x, hx, rfl⟩

theorem maxDescendantBMatrixNormCoeffFieldAtScale_eq_sup_upperLeft_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q k a =
      (descendantsAtScale Q k).sup' (descendantsAtScale_nonempty Q hk)
        (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft) := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hterm :
      ∀ R ∈ descendantsAtScale Q k,
        Ch02.coarseBMatrixNorm R F =
          Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft := by
    intro R _hR
    have hEq :
        coarseBlockMatrix (cubeSet R) a.toFun =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R) := by
      simpa [F] using
        Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          ha R
    simp [Ch02.coarseBMatrixNorm, hEq]
  calc
    Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q k a =
        Ch02.maxDescendantBMatrixNormAtScale Q k F := by
          simp [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha, F]
    _ =
        Ch02.finsetSupReal (descendantsAtScale Q k)
          (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft) := by
          simpa [Ch02.maxDescendantBMatrixNormAtScale] using
            Ch02.finsetSupReal_congr (descendantsAtScale Q k) hterm
    _ =
        (descendantsAtScale Q k).sup' (descendantsAtScale_nonempty Q hk)
          (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft) := by
          exact finsetSupReal_eq_sup' (descendantsAtScale Q k)
            (descendantsAtScale_nonempty Q hk) _

theorem maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_sup_lowerRight_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q k a =
      (descendantsAtScale Q k).sup' (descendantsAtScale_nonempty Q hk)
        (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hterm :
      ∀ R ∈ descendantsAtScale Q k,
        Ch02.coarseSigmaStarInvMatrixNorm R F =
          Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight := by
    intro R _hR
    have hEq :
        coarseBlockMatrix (cubeSet R) a.toFun =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R) := by
      simpa [F] using
        Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          ha R
    simp [Ch02.coarseSigmaStarInvMatrixNorm, hEq]
  calc
    Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q k a =
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F := by
          simp [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha, F]
    _ =
        Ch02.finsetSupReal (descendantsAtScale Q k)
          (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) := by
          simpa [Ch02.maxDescendantSigmaStarInvMatrixNormAtScale] using
            Ch02.finsetSupReal_congr (descendantsAtScale Q k) hterm
    _ =
        (descendantsAtScale Q k).sup' (descendantsAtScale_nonempty Q hk)
          (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) := by
          exact finsetSupReal_eq_sup' (descendantsAtScale Q k)
            (descendantsAtScale_nonempty Q hk) _

theorem matrixNorm_smul_one_eq_of_nonneg
    {d : ℕ} [NeZero d] {c : ℝ} (hc : 0 ≤ c) :
    Ch02.matrixNorm (c • (1 : Mat d)) = c := by
  simpa [Ch02.matrixNorm_eq_matrixOperatorNorm] using
    Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg (d := d) hc

theorem upperLargeScaleRaw_sum_le_base_add_positiveExcess_sum
    {d : ℕ} [NeZero d] (m : ℕ) {s base : ℝ} (hs : 0 < s)
    (hbase : 0 ≤ base) (a : RegCoeffField d) :
    (∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) n a) ≤
      base +
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 *
            (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
             let hparents : parents.Nonempty :=
              descendantsAtScale_nonempty (originCube d (m : ℤ))
                (section52LargeScaleSet_mem_le_m n.2)
             parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                    Ch02.matrixNorm (base • (1 : Mat d)))
                  0))) := by
  classical
  let Qm : TriadicCube d := originCube d (m : ℤ)
  let raw : ℤ → ℝ :=
    fun n => Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Qm n a
  let excess : (n : ℤ) → n ∈ section52LargeScaleSet m → ℝ :=
    fun n hn =>
      let parents := descendantsAtScale Qm n
      let hparents : parents.Nonempty :=
        descendantsAtScale_nonempty Qm (section52LargeScaleSet_mem_le_m hn)
      parents.sup' hparents
        (fun R =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft -
              Ch02.matrixNorm (base • (1 : Mat d)))
            0)
  have hweighted :=
    weighted_sum_le_base_add_weighted_positiveExcess
      (s := section52LargeScaleSet m)
      (w := section52LargeScaleWeight s m)
      (f := raw) hbase
      (fun n hn => section52LargeScaleWeight_nonneg m hs.le n)
      (section52LargeScaleWeight_sum_le_one hs m)
  have hterm :
      ∀ (n : ℤ) (hn : n ∈ section52LargeScaleSet m),
        max (raw n - base) 0 ≤ excess n hn := by
    intro n hn
    have hnle : n ≤ Qm.scale := by
      simpa [Qm, originCube] using section52LargeScaleSet_mem_le_m hn
    have hcenter : Ch02.matrixNorm (base • (1 : Mat d)) = base :=
      matrixNorm_smul_one_eq_of_nonneg hbase
    by_cases ha : Ch04.AELocallyUniformlyEllipticField a
    · have hraw_eq :=
        maxDescendantBMatrixNormCoeffFieldAtScale_eq_sup_upperLeft_of_aelocallyUniformlyEllipticField
          (a := a) ha Qm hnle
      simpa [raw, excess, hcenter, hraw_eq] using
        max_sup'_sub_base_le_sup'_max_sub_base
          (descendantsAtScale_nonempty Qm hnle)
          (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)
          base
    · have hraw_zero : raw n = 0 := by
        simp [raw, Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha]
      have hexcess_nonneg : 0 ≤ excess n hn := by
        dsimp [excess]
        let parents := descendantsAtScale Qm n
        let hparents : parents.Nonempty := descendantsAtScale_nonempty Qm hnle
        rcases hparents with ⟨R0, hR0⟩
        exact (le_max_right
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet R0) a.toFun).upperLeft -
              Ch02.matrixNorm (base • (1 : Mat d))) 0).trans
          (Finset.le_sup'
            (s := parents)
            (f := fun R =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft -
                  Ch02.matrixNorm (base • (1 : Mat d)))
                0) hR0)
      simpa [raw, hraw_zero, hbase] using hexcess_nonneg
  have hsum :
      ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 * max (raw n.1 - base) 0) ≤
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 * excess n.1 n.2) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_left (hterm n.1 n.2)
      (section52LargeScaleWeight_nonneg m hs.le n.1)
  calc
    (∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) n a)
        = ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * raw n := by
          simp [raw, Qm]
    _ ≤ base +
          ∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n * max (raw n - base) 0 := hweighted
    _ ≤ base +
          ((section52LargeScaleSet m).attach.sum fun n =>
            section52LargeScaleWeight s m n.1 * excess n.1 n.2) := by
          have hleft :
              (∑ n ∈ section52LargeScaleSet m,
                section52LargeScaleWeight s m n * max (raw n - base) 0) =
                ((section52LargeScaleSet m).attach.sum fun n =>
                  section52LargeScaleWeight s m n.1 * max (raw n.1 - base) 0) := by
            exact (Finset.sum_attach (section52LargeScaleSet m)
              (fun n => section52LargeScaleWeight s m n * max (raw n - base) 0)).symm
          rw [hleft]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hsum base
    _ =
      base +
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 *
            (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
             let hparents : parents.Nonempty :=
              descendantsAtScale_nonempty (originCube d (m : ℤ))
                (section52LargeScaleSet_mem_le_m n.2)
             parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                    Ch02.matrixNorm (base • (1 : Mat d)))
                  0))) := by
          simp [excess, Qm]

theorem upperPositiveExcess_pointwise_le_smallTail_add_largeScalePositiveExcess
    {d : ℕ} [NeZero d] (m : ℕ) {s base : ℝ} (hs : 0 < s)
    (hbase : 0 ≤ base) (a : RegCoeffField d) :
    max
        (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a - base)
        0 ≤
      upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m +
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 *
            (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
             let hparents : parents.Nonempty :=
              descendantsAtScale_nonempty (originCube d (m : ℤ))
                (section52LargeScaleSet_mem_le_m n.2)
             parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                    Ch02.matrixNorm (base • (1 : Mat d)))
                  0))) := by
  classical
  let small : ℝ :=
    upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
      section52SmallTailWeight s m
  let largeRaw : ℝ :=
    ∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) n a
  let largeExcess : ℝ :=
    (section52LargeScaleSet m).attach.sum fun n =>
      section52LargeScaleWeight s m n.1 *
        (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
         let hparents : parents.Nonempty :=
          descendantsAtScale_nonempty (originCube d (m : ℤ))
            (section52LargeScaleSet_mem_le_m n.2)
         parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                Ch02.matrixNorm (base • (1 : Mat d)))
              0))
  have hsmall_nonneg : 0 ≤ small := by
    dsimp [small]
    exact div_nonneg (sq_nonneg _)
      (section52SmallTailWeight_pos hs m).le
  have hlargeExcess_nonneg : 0 ≤ largeExcess := by
    dsimp [largeExcess]
    refine Finset.sum_nonneg ?_
    intro n _hn
    refine mul_nonneg (section52LargeScaleWeight_nonneg m hs.le n.1) ?_
    let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m n.2)
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q0) a.toFun).upperLeft -
          Ch02.matrixNorm (base • (1 : Mat d))) 0).trans
      (Finset.le_sup'
        (s := parents)
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
              Ch02.matrixNorm (base • (1 : Mat d)))
            0) hQ0)
  have hsplit :
      Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a ≤
        small + largeRaw := by
    simpa [small, largeRaw, add_comm] using
      LambdaSqCoeffField_originCube_finite_one_le_upperSmallSqrtTail_sq_div_add_largeScale_sum
        (d := d) m hs a
  have hlarge :
      largeRaw ≤ base + largeExcess := by
    simpa [largeRaw, largeExcess] using
      upperLargeScaleRaw_sum_le_base_add_positiveExcess_sum
        (d := d) m hs hbase a
  have hpoint :
      Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a ≤
        base + (small + largeExcess) := by
    linarith
  have hnonneg : 0 ≤ small + largeExcess := add_nonneg hsmall_nonneg hlargeExcess_nonneg
  exact max_sub_base_zero_le_of_le_base_add_nonneg hnonneg hpoint

theorem lowerLargeScaleRaw_sum_le_base_add_positiveExcess_sum
    {d : ℕ} [NeZero d] (m : ℕ) {s base : ℝ} (hs : 0 < s)
    (hbase : 0 ≤ base) (a : RegCoeffField d) :
    (∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) n a) ≤
      base +
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 *
            (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
             let hparents : parents.Nonempty :=
              descendantsAtScale_nonempty (originCube d (m : ℤ))
                (section52LargeScaleSet_mem_le_m n.2)
             parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm (base • (1 : Mat d)))
                  0))) := by
  classical
  let Qm : TriadicCube d := originCube d (m : ℤ)
  let raw : ℤ → ℝ :=
    fun n => Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Qm n a
  let excess : (n : ℤ) → n ∈ section52LargeScaleSet m → ℝ :=
    fun n hn =>
      let parents := descendantsAtScale Qm n
      let hparents : parents.Nonempty :=
        descendantsAtScale_nonempty Qm (section52LargeScaleSet_mem_le_m hn)
      parents.sup' hparents
        (fun R =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight -
              Ch02.matrixNorm (base • (1 : Mat d)))
            0)
  have hweighted :=
    weighted_sum_le_base_add_weighted_positiveExcess
      (s := section52LargeScaleSet m)
      (w := section52LargeScaleWeight s m)
      (f := raw) hbase
      (fun n hn => section52LargeScaleWeight_nonneg m hs.le n)
      (section52LargeScaleWeight_sum_le_one hs m)
  have hterm :
      ∀ (n : ℤ) (hn : n ∈ section52LargeScaleSet m),
        max (raw n - base) 0 ≤ excess n hn := by
    intro n hn
    have hnle : n ≤ Qm.scale := by
      simpa [Qm, originCube] using section52LargeScaleSet_mem_le_m hn
    have hcenter : Ch02.matrixNorm (base • (1 : Mat d)) = base :=
      matrixNorm_smul_one_eq_of_nonneg hbase
    by_cases ha : Ch04.AELocallyUniformlyEllipticField a
    · have hraw_eq :=
        maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_sup_lowerRight_of_aelocallyUniformlyEllipticField
          (a := a) ha Qm hnle
      simpa [raw, excess, hcenter, hraw_eq] using
        max_sup'_sub_base_le_sup'_max_sub_base
          (descendantsAtScale_nonempty Qm hnle)
          (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)
          base
    · have hraw_zero : raw n = 0 := by
        simp [raw, Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha]
      have hexcess_nonneg : 0 ≤ excess n hn := by
        dsimp [excess]
        let parents := descendantsAtScale Qm n
        let hparents : parents.Nonempty := descendantsAtScale_nonempty Qm hnle
        rcases hparents with ⟨R0, hR0⟩
        exact (le_max_right
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet R0) a.toFun).lowerRight -
              Ch02.matrixNorm (base • (1 : Mat d))) 0).trans
          (Finset.le_sup'
            (s := parents)
            (f := fun R =>
              max
                (Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight -
                  Ch02.matrixNorm (base • (1 : Mat d)))
                0) hR0)
      simpa [raw, hraw_zero, hbase] using hexcess_nonneg
  have hsum :
      ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 * max (raw n.1 - base) 0) ≤
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 * excess n.1 n.2) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_left (hterm n.1 n.2)
      (section52LargeScaleWeight_nonneg m hs.le n.1)
  calc
    (∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) n a)
        = ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * raw n := by
          simp [raw, Qm]
    _ ≤ base +
          ∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n * max (raw n - base) 0 := hweighted
    _ ≤ base +
          ((section52LargeScaleSet m).attach.sum fun n =>
            section52LargeScaleWeight s m n.1 * excess n.1 n.2) := by
          have hleft :
              (∑ n ∈ section52LargeScaleSet m,
                section52LargeScaleWeight s m n * max (raw n - base) 0) =
                ((section52LargeScaleSet m).attach.sum fun n =>
                  section52LargeScaleWeight s m n.1 * max (raw n.1 - base) 0) := by
            exact (Finset.sum_attach (section52LargeScaleSet m)
              (fun n => section52LargeScaleWeight s m n * max (raw n - base) 0)).symm
          rw [hleft]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hsum base
    _ =
      base +
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 *
            (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
             let hparents : parents.Nonempty :=
              descendantsAtScale_nonempty (originCube d (m : ℤ))
                (section52LargeScaleSet_mem_le_m n.2)
             parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm (base • (1 : Mat d)))
                  0))) := by
          simp [excess, Qm]

theorem lowerPositiveExcess_pointwise_le_smallTail_add_largeScalePositiveExcess
    {d : ℕ} [NeZero d] (m : ℕ) {s base : ℝ} (hs : 0 < s)
    (hbase : 0 ≤ base) (a : RegCoeffField d) :
    max
        ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹ - base)
        0 ≤
      lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m +
        ((section52LargeScaleSet m).attach.sum fun n =>
          section52LargeScaleWeight s m n.1 *
            (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
             let hparents : parents.Nonempty :=
              descendantsAtScale_nonempty (originCube d (m : ℤ))
                (section52LargeScaleSet_mem_le_m n.2)
             parents.sup' hparents
              (fun Q =>
                max
                  (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                    Ch02.matrixNorm (base • (1 : Mat d)))
                  0))) := by
  classical
  let small : ℝ :=
    lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
      section52SmallTailWeight s m
  let largeRaw : ℝ :=
    ∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) n a
  let largeExcess : ℝ :=
    (section52LargeScaleSet m).attach.sum fun n =>
      section52LargeScaleWeight s m n.1 *
        (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
         let hparents : parents.Nonempty :=
          descendantsAtScale_nonempty (originCube d (m : ℤ))
            (section52LargeScaleSet_mem_le_m n.2)
         parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm (base • (1 : Mat d)))
              0))
  have hsmall_nonneg : 0 ≤ small := by
    dsimp [small]
    exact div_nonneg (sq_nonneg _)
      (section52SmallTailWeight_pos hs m).le
  have hlargeExcess_nonneg : 0 ≤ largeExcess := by
    dsimp [largeExcess]
    refine Finset.sum_nonneg ?_
    intro n _hn
    refine mul_nonneg (section52LargeScaleWeight_nonneg m hs.le n.1) ?_
    let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (section52LargeScaleSet_mem_le_m n.2)
    rcases hparents with ⟨Q0, hQ0⟩
    exact (le_max_right
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q0) a.toFun).lowerRight -
          Ch02.matrixNorm (base • (1 : Mat d))) 0).trans
      (Finset.le_sup'
        (s := parents)
        (f := fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm (base • (1 : Mat d)))
            0) hQ0)
  have hsplit :
      (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹ ≤
        small + largeRaw := by
    simpa [small, largeRaw, add_comm] using
      lambdaSqCoeffField_originCube_finite_one_inv_le_lowerSmallSqrtTail_sq_div_add_largeScale_sum
        (d := d) m hs a
  have hlarge :
      largeRaw ≤ base + largeExcess := by
    simpa [largeRaw, largeExcess] using
      lowerLargeScaleRaw_sum_le_base_add_positiveExcess_sum
        (d := d) m hs hbase a
  have hpoint :
      (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹ ≤
        base + (small + largeExcess) := by
    linarith
  have hnonneg : 0 ≤ small + largeExcess := add_nonneg hsmall_nonneg hlargeExcess_nonneg
  exact max_sub_base_zero_le_of_le_base_add_nonneg hnonneg hpoint

theorem section52_upperCenter_entries
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (i j : Fin d) :
    (hP.barSigmaAtScale hStruct 0 •
        (1 : Mat d)) i j =
      ∫ b, (coarseBlockMatrix (cubeSet (originCube d (0 : ℤ))) b).upperLeft i j ∂P := by
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let primitive0 := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ)
  have hb :
      Ch04.annealedBAtScale P (0 : ℤ) = primitive0.barB • (1 : Mat d) := by
    simpa [primitive0] using Ch04.Internal.AnnealedPrimitiveScalarizationData.b_eq primitive0
  have hbar : scalarization.barSigma 0 = primitive0.barB := by
    simpa [scalarization, primitive0] using
      Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigma_eq_barB scalarization primitive0
  calc
    (scalarization.barSigma 0 • (1 : Mat d)) i j =
        (primitive0.barB • (1 : Mat d)) i j := by rw [hbar]
    _ = (Ch04.annealedBAtScale P (0 : ℤ)) i j := by rw [hb]
    _ = ∫ b, (coarseBlockMatrix (cubeSet (originCube d (0 : ℤ))) b).upperLeft i j ∂P := by
      rfl

theorem section52_lowerCenter_entries
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (i j : Fin d) :
    ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
        (1 : Mat d)) i j =
      ∫ b, (coarseBlockMatrix (cubeSet (originCube d (0 : ℤ))) b).lowerRight i j ∂P := by
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let primitive0 := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ)
  have hsigma :
      Ch04.annealedSigmaStarInvAtScale P (0 : ℤ) =
        primitive0.barSigmaStarInv • (1 : Mat d) := by
    simpa [primitive0] using Ch04.Internal.AnnealedPrimitiveScalarizationData.sigmaStarInv_eq primitive0
  have hstar :
      scalarization.barSigmaStar 0 =
        (primitive0.barSigmaStarInv)⁻¹ := by
    simpa [scalarization, primitive0] using
      Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_eq_inv_barSigmaStarInv
        scalarization primitive0
  calc
    ((scalarization.barSigmaStar 0)⁻¹ • (1 : Mat d)) i j =
        (primitive0.barSigmaStarInv • (1 : Mat d)) i j := by
      rw [hstar, inv_inv]
    _ = (Ch04.annealedSigmaStarInvAtScale P (0 : ℤ)) i j := by rw [hsigma]
    _ = ∫ b, (coarseBlockMatrix (cubeSet (originCube d (0 : ℤ))) b).lowerRight i j ∂P := by
      rfl

theorem upperLargeScaleFiniteParentFluctuation
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m n : ℕ} (hnm : n ≤ m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (by
          change (n : ℤ) ≤ (m : ℤ)
          exact_mod_cast hnm)
    let K := 2 * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
    let B := parents.sup' hparents
      (fun Q => section52UnitDescendantRosenthalBudget Q hP4.xi K)
    Ch04.annealedMomentRoot P hP4.xi
      (fun a =>
        parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                Ch02.matrixNorm
                  (hP.barSigmaAtScale hStruct 0 •
                    (1 : Mat d)))
              0)) ≤
      ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
        ((parents.card : ℝ) ^ (1 / (hP4.xi : ℝ)) * B) := by
  classical
  intro parents hparents K B
  let : IsProbabilityMeasure P := hP.isProbability
  have hn_nonneg : (0 : ℤ) ≤ 0 := le_rfl
  have hparent_scale : ∀ Q ∈ parents, (0 : ℤ) ≤ Q.scale := by
    intro Q hQ
    have hscale : Q.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hQ
    rw [hscale]
    exact_mod_cast Nat.zero_le n
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num)
      (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
  have hbudget_nonneg :
      ∀ Q : TriadicCube d, 0 ≤ section52UnitDescendantRosenthalBudget Q hP4.xi K :=
    fun Q => section52UnitDescendantRosenthalBudget_nonneg Q hP4.xi hK_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    rcases hparents with ⟨Q0, hQ0⟩
    exact (hbudget_nonneg Q0).trans
      (Finset.le_sup'
        (f := fun Q => section52UnitDescendantRosenthalBudget Q hP4.xi K) hQ0)
  have hOrigin :
      ∀ i j : Fin d,
        Integrable
            (fun a =>
              |Ch04.restrictionCenteredOriginObservable P 0
                (fun U a => (coarseBlockMatrix U a).upperLeft i j) a| ^
                hP4.xi) P ∧
          (∫ a,
              |Ch04.restrictionCenteredOriginObservable P 0
                (fun U a => (coarseBlockMatrix U a).upperLeft i j) a| ^
                hP4.xi ∂P) ^
              (1 / (hP4.xi : ℝ)) ≤ K := by
    intro i j
    have h :=
      Ch04.RestrictionLawCarrier.restrictionCenteredOriginObservable_upperLeft_entry_momentRoot_le_two_LambdaMomentAtScale
        hP hP4.sUpper_pos (Nat.succ_le_of_lt hP4.xi_pos)
        hP4.upper_moment_integrable i j
    simpa [K] using h
  exact
    Ch04.RestrictionLawCarrier.upperLeft_matrixNorm_positiveExcess_finsetSup_momentRoot_le_of_restrictionUnitRangeDependentLaw
      hP hparents hn_nonneg hparent_scale hStruct.stationary hStruct.unit_range
      (hP.barSigmaAtScale hStruct 0 •
        (1 : Mat d))
      (section52_upperCenter_entries hP hStruct)
      hP4.two_le_xi hK_nonneg hB_nonneg
      (fun i j => (hOrigin i j).1)
      (fun i j => (hOrigin i j).2)
      (by
        intro Q hQ
        dsimp [B, section52UnitDescendantRosenthalBudget]
        exact Finset.le_sup'
          (f := fun Q => section52UnitDescendantRosenthalBudget Q hP4.xi K) hQ)

theorem lowerLargeScaleFiniteParentFluctuation
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {m n : ℕ} (hnm : n ≤ m) :
    let parents := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
    let hparents : parents.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ))
        (by
          change (n : ℤ) ≤ (m : ℤ)
          exact_mod_cast hnm)
    let K := 2 * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
    let B := parents.sup' hparents
      (fun Q => section52UnitDescendantRosenthalBudget Q hP4.xi K)
    Ch04.annealedMomentRoot P hP4.xi
      (fun a =>
        parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm
                  ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
                    (1 : Mat d)))
              0)) ≤
      ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
        ((parents.card : ℝ) ^ (1 / (hP4.xi : ℝ)) * B) := by
  classical
  intro parents hparents K B
  let : IsProbabilityMeasure P := hP.isProbability
  have hn_nonneg : (0 : ℤ) ≤ 0 := le_rfl
  have hparent_scale : ∀ Q ∈ parents, (0 : ℤ) ≤ Q.scale := by
    intro Q hQ
    have hscale : Q.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hQ
    rw [hscale]
    exact_mod_cast Nat.zero_le n
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num)
      (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)
  have hbudget_nonneg :
      ∀ Q : TriadicCube d, 0 ≤ section52UnitDescendantRosenthalBudget Q hP4.xi K :=
    fun Q => section52UnitDescendantRosenthalBudget_nonneg Q hP4.xi hK_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    rcases hparents with ⟨Q0, hQ0⟩
    exact (hbudget_nonneg Q0).trans
      (Finset.le_sup'
        (f := fun Q => section52UnitDescendantRosenthalBudget Q hP4.xi K) hQ0)
  have hOrigin :
      ∀ i j : Fin d,
        Integrable
            (fun a =>
              |Ch04.restrictionCenteredOriginObservable P 0
                (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^
                hP4.xi) P ∧
          (∫ a,
              |Ch04.restrictionCenteredOriginObservable P 0
                (fun U a => (coarseBlockMatrix U a).lowerRight i j) a| ^
                hP4.xi ∂P) ^
              (1 / (hP4.xi : ℝ)) ≤ K := by
    intro i j
    have h :=
      Ch04.RestrictionLawCarrier.restrictionCenteredOriginObservable_lowerRight_entry_momentRoot_le_two_lambdaInvMomentAtScale
        hP hP4.sLower_pos (Nat.succ_le_of_lt hP4.xi_pos)
        hP4.lower_inv_moment_integrable i j
    simpa [K] using h
  exact
    Ch04.RestrictionLawCarrier.lowerRight_matrixNorm_positiveExcess_finsetSup_momentRoot_le_of_restrictionUnitRangeDependentLaw
      hP hparents hn_nonneg hparent_scale hStruct.stationary hStruct.unit_range
      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ •
        (1 : Mat d))
      (section52_lowerCenter_entries hP hStruct)
      hP4.two_le_xi hK_nonneg hB_nonneg
      (fun i j => (hOrigin i j).1)
      (fun i j => (hOrigin i j).2)
      (by
        intro Q hQ
        dsimp [B, section52UnitDescendantRosenthalBudget]
        exact Finset.le_sup'
          (f := fun Q => section52UnitDescendantRosenthalBudget Q hP4.xi K) hQ)

end

end Section52
end Ch05
end Book
end Homogenization
