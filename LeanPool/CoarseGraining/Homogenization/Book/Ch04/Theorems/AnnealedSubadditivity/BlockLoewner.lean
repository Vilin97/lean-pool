/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions

/-! # Block Loewner -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Proved annealed subadditivity reductions

This file replaces the old abstract `Annealed*Theory` packages with plain
proved theorems.  The pointwise deterministic/a.e. subadditivity hypotheses and
integrability hypotheses remain explicit; Ch4 owns the expectation, stationarity,
matrix-order, and scalarization consequences.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- Integrating an a.e. quadratic-form comparison gives a matrix Löwner
comparison. -/
theorem matLoewnerLE_of_integral_quadratic_mono
    {d : ℕ} {P : RestrictionCoeffLaw d} {A B : Mat d}
    {F G : Vec d → RegCoeffField d → ℝ}
    (hFint : ∀ x : Vec d, Integrable (F x) P)
    (hGint : ∀ x : Vec d, Integrable (G x) P)
    (hA : ∀ x : Vec d,
      (1 / 2 : ℝ) * vecDot x (matVecMul A x) = ∫ a, F x a ∂P)
    (hB : ∀ x : Vec d,
      ∫ a, G x a ∂P = (1 / 2 : ℝ) * vecDot x (matVecMul B x))
    (hMono : ∀ x : Vec d, F x ≤ᵐ[P] G x) :
    MatLoewnerLE A B := by
  intro x
  calc
    (1 / 2 : ℝ) * vecDot x (matVecMul A x)
        = ∫ a, F x a ∂P := hA x
    _ ≤ ∫ a, G x a ∂P := integral_mono_ae (hFint x) (hGint x) (hMono x)
    _ = (1 / 2 : ℝ) * vecDot x (matVecMul B x) := hB x

/-- Integrating an a.e. doubled quadratic-form comparison gives a block-matrix
Löwner comparison. -/
theorem blockMatLoewnerLE_of_integral_quadratic_mono
    {d : ℕ} {P : RestrictionCoeffLaw d} {A B : BlockMat d}
    {F G : BlockVec d → RegCoeffField d → ℝ}
    (hFint : ∀ X : BlockVec d, Integrable (F X) P)
    (hGint : ∀ X : BlockVec d, Integrable (G X) P)
    (hA : ∀ X : BlockVec d,
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X) = ∫ a, F X a ∂P)
    (hB : ∀ X : BlockVec d,
      ∫ a, G X a ∂P = (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X))
    (hMono : ∀ X : BlockVec d, F X ≤ᵐ[P] G X) :
    BlockMatLoewnerLE A B := by
  intro X
  calc
    (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X)
        = ∫ a, F X a ∂P := hA X
    _ ≤ ∫ a, G X a ∂P := integral_mono_ae (hFint X) (hGint X) (hMono X)
    _ = (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X) := hB X

/-- A block Löwner comparison controls diagonal entries of the upper-left
block. -/
theorem blockMatLoewnerLE_upperLeft_apply {d : ℕ} {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) (i : Fin d) :
    A.upperLeft i i ≤ B.upperLeft i i := by
  have hquad := h (Pi.single i 1, 0)
  have hA :
      blockVecDot (Pi.single i 1, 0)
          (blockMatVecMul A (Pi.single i 1, 0)) = A.upperLeft i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  have hB :
      blockVecDot (Pi.single i 1, 0)
          (blockMatVecMul B (Pi.single i 1, 0)) = B.upperLeft i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  simpa [hA, hB] using hquad

/-- A block Löwner comparison controls diagonal entries of the lower-right
block. -/
theorem blockMatLoewnerLE_lowerRight_apply {d : ℕ} {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) (i : Fin d) :
    A.lowerRight i i ≤ B.lowerRight i i := by
  have hquad := h (0, Pi.single i 1)
  have hA :
      blockVecDot (0, Pi.single i 1)
          (blockMatVecMul A (0, Pi.single i 1)) = A.lowerRight i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  have hB :
      blockVecDot (0, Pi.single i 1)
          (blockMatVecMul B (0, Pi.single i 1)) = B.lowerRight i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  simpa [hA, hB] using hquad

/-- Finite-dimensional matrix quadratic forms are integrable when all entries
are integrable. -/
private theorem integrable_vecDot_matVecMul_of_integrable_entries
    {d : ℕ} {P : RestrictionCoeffLaw d} {M : RegCoeffField d → Mat d}
    (hM : ∀ i j, Integrable (fun a => M a i j) P) (x y : Vec d) :
    Integrable (fun a => vecDot x (matVecMul (M a) y)) P := by
  simp [vecDot, matVecMul]
  exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
    (MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
      (hM i j).mul_const (y j)).const_mul (x i)

/-- Finite-dimensional matrix quadratic forms commute with entrywise
expectation under entrywise integrability. -/
private theorem integral_vecDot_matVecMul_eq_of_integrable_entries
    {d : ℕ} {P : RestrictionCoeffLaw d} {M : RegCoeffField d → Mat d}
    (hM : ∀ i j, Integrable (fun a => M a i j) P) (x y : Vec d) :
    ∫ a, vecDot x (matVecMul (M a) y) ∂P =
      vecDot x (matVecMul (fun i j => ∫ a, M a i j ∂P) y) := by
  simp [vecDot, matVecMul]
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · congr 1
    ext i
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finsetSum Finset.univ]
    · simp_rw [MeasureTheory.integral_mul_const]
    · intro j _hj
      exact (hM i j).mul_const (y j)
  · intro i _hi
    exact (MeasureTheory.integrable_finsetSum Finset.univ fun j _hj =>
      (hM i j).mul_const (y j)).const_mul (x i)

/-- Finite-dimensional block quadratic forms are integrable when all block
entries are integrable. -/
theorem integrable_blockVecDot_blockMatVecMul_of_integrable_entries
    {d : ℕ} {P : RestrictionCoeffLaw d} {B : RegCoeffField d → BlockMat d}
    (hB : ∀ α β, Integrable (fun a => blockMatEntry (B a) α β) P)
    (X Y : BlockVec d) :
    Integrable (fun a => blockVecDot X (blockMatVecMul (B a) Y)) P := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨r, s⟩
  have hUL : ∀ i j, Integrable (fun a => (B a).upperLeft i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inl i) (Sum.inl j)
  have hUR : ∀ i j, Integrable (fun a => (B a).upperRight i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inl i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a => (B a).lowerLeft i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inr i) (Sum.inl j)
  have hLR : ∀ i j, Integrable (fun a => (B a).lowerRight i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inr i) (Sum.inr j)
  have h1 := integrable_vecDot_matVecMul_of_integrable_entries hUL p r
  have h2 := integrable_vecDot_matVecMul_of_integrable_entries hUR p s
  have h3 := integrable_vecDot_matVecMul_of_integrable_entries hLL q r
  have h4 := integrable_vecDot_matVecMul_of_integrable_entries hLR q s
  simpa [blockVecDot, blockMatVecMul, vecDot_add_right, add_assoc] using!
    (h1.add h2).add (h3.add h4)

/-- Finite-dimensional block quadratic forms commute with entrywise expectation
under entrywise integrability. -/
theorem integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
    {d : ℕ} {P : RestrictionCoeffLaw d} {B : RegCoeffField d → BlockMat d}
    (hB : ∀ α β, Integrable (fun a => blockMatEntry (B a) α β) P)
    (X Y : BlockVec d) :
    ∫ a, blockVecDot X (blockMatVecMul (B a) Y) ∂P =
      blockVecDot X
        (blockMatVecMul
          { upperLeft := fun i j => ∫ a, (B a).upperLeft i j ∂P
            upperRight := fun i j => ∫ a, (B a).upperRight i j ∂P
            lowerLeft := fun i j => ∫ a, (B a).lowerLeft i j ∂P
            lowerRight := fun i j => ∫ a, (B a).lowerRight i j ∂P } Y) := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨r, s⟩
  have hUL : ∀ i j, Integrable (fun a => (B a).upperLeft i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inl i) (Sum.inl j)
  have hUR : ∀ i j, Integrable (fun a => (B a).upperRight i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inl i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a => (B a).lowerLeft i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inr i) (Sum.inl j)
  have hLR : ∀ i j, Integrable (fun a => (B a).lowerRight i j) P := by
    intro i j
    simpa [blockMatEntry] using hB (Sum.inr i) (Sum.inr j)
  let f1 : RegCoeffField d → ℝ := fun a => vecDot p (matVecMul (B a).upperLeft r)
  let f2 : RegCoeffField d → ℝ := fun a => vecDot p (matVecMul (B a).upperRight s)
  let f3 : RegCoeffField d → ℝ := fun a => vecDot q (matVecMul (B a).lowerLeft r)
  let f4 : RegCoeffField d → ℝ := fun a => vecDot q (matVecMul (B a).lowerRight s)
  have h1int : Integrable f1 P :=
    integrable_vecDot_matVecMul_of_integrable_entries hUL p r
  have h2int : Integrable f2 P :=
    integrable_vecDot_matVecMul_of_integrable_entries hUR p s
  have h3int : Integrable f3 P :=
    integrable_vecDot_matVecMul_of_integrable_entries hLL q r
  have h4int : Integrable f4 P :=
    integrable_vecDot_matVecMul_of_integrable_entries hLR q s
  have hExpand :
      (fun a => blockVecDot (p, q) (blockMatVecMul (B a) (r, s))) =
        fun a => (f1 a + f2 a) + (f3 a + f4 a) := by
    funext a
    simp [f1, f2, f3, f4, blockVecDot, blockMatVecMul, vecDot_add_right, add_assoc]
  rw [hExpand]
  calc
    ∫ a, (f1 a + f2 a) + (f3 a + f4 a) ∂P
        =
      (∫ a, f1 a ∂P) + (∫ a, f2 a ∂P) +
        ((∫ a, f3 a ∂P) + (∫ a, f4 a ∂P)) := by
        change ∫ a, (f1 + f2) a + (f3 + f4) a ∂P = _
        rw [integral_add (h1int.add h2int) (h3int.add h4int)]
        rw [show ∫ a, (f1 + f2) a ∂P = ∫ a, f1 a ∂P + ∫ a, f2 a ∂P by
          exact integral_add h1int h2int]
        rw [show ∫ a, (f3 + f4) a ∂P = ∫ a, f3 a ∂P + ∫ a, f4 a ∂P by
          exact integral_add h3int h4int]
    _ =
      blockVecDot (p, q)
        (blockMatVecMul
          { upperLeft := fun i j => ∫ a, (B a).upperLeft i j ∂P
            upperRight := fun i j => ∫ a, (B a).upperRight i j ∂P
            lowerLeft := fun i j => ∫ a, (B a).lowerLeft i j ∂P
            lowerRight := fun i j => ∫ a, (B a).lowerRight i j ∂P } (r, s)) := by
        rw [show ∫ a, f1 a ∂P =
            vecDot p (matVecMul (fun i j => ∫ a, (B a).upperLeft i j ∂P) r) from
          integral_vecDot_matVecMul_eq_of_integrable_entries hUL p r]
        rw [show ∫ a, f2 a ∂P =
            vecDot p (matVecMul (fun i j => ∫ a, (B a).upperRight i j ∂P) s) from
          integral_vecDot_matVecMul_eq_of_integrable_entries hUR p s]
        rw [show ∫ a, f3 a ∂P =
            vecDot q (matVecMul (fun i j => ∫ a, (B a).lowerLeft i j ∂P) r) from
          integral_vecDot_matVecMul_eq_of_integrable_entries hLL q r]
        rw [show ∫ a, f4 a ∂P =
            vecDot q (matVecMul (fun i j => ∫ a, (B a).lowerRight i j ∂P) s) from
          integral_vecDot_matVecMul_eq_of_integrable_entries hLR q s]
        simp [blockVecDot, blockMatVecMul, vecDot_add_right, add_assoc]

/-- Reflection of doubled variables preserves block Löwner comparisons. -/
theorem blockMatLoewnerLE_blockReflect {d : ℕ} {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (blockReflect A) (blockReflect B) := by
  intro X
  simpa using h (X.2, X.1)

/-- The lower-right block of a block Löwner comparison is a matrix Löwner
comparison. -/
theorem matLoewnerLE_lowerRight_of_blockMatLoewnerLE {d : ℕ} {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) :
    MatLoewnerLE A.lowerRight B.lowerRight := by
  intro q
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left,
    vecDot_zero_right] using h (0, q)

/-- The upper-left block of a block Löwner comparison is a matrix Löwner
comparison. -/
theorem matLoewnerLE_upperLeft_of_blockMatLoewnerLE {d : ℕ} {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) :
    MatLoewnerLE A.upperLeft B.upperLeft := by
  intro p
  simpa [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left,
    vecDot_zero_right] using h (p, 0)

/-- Pointwise response subadditivity for the Ch4 scalar response observable,
with the a.e. coefficient representative handled by the Chapter 2 coefficient
family. -/
theorem restrictionResponseJObservableCubeSet_le_descendantsAverage_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) {n m : ℤ} (hnm : n ≤ m)
    (p q : Vec d) :
    restrictionResponseJObservableCubeSet (originCube d m) p q a ≤
      descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => restrictionResponseJObservableCubeSet R p q a) := by
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hcell :
      ∀ i : Pcell.Cell, Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    intro i
    have hiScale : i.1 ∈ descendantsAtScale Q n := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q (by simpa [Q] using! hnm)]
      change i.1 ∈ descendantsAtDepth Q j
      exact i.2
    exact F.restrictsTo_descendant (by simpa [Q] using! hnm) hiScale
  have hsub :=
    (Ch02.responseSubadditivityAndScalingTheory (Ch02.cubeDomain Q)
      (F.coeffOn Q)).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => F.coeffOn i.1) hcell p q
  have hParent :
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q =
        restrictionResponseJObservableCubeSet Q p q a := by
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q
          = ResponseJ (openCubeSet Q) p q a.toFun := by
              simpa [F, Q, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain Q) (F.coeffOn Q) p q
      _ = restrictionResponseJObservableCubeSet Q p q a := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a.toFun]
            rfl
  have hTerm :
      (fun R : TriadicCube d =>
          Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q) =
        fun R : TriadicCube d => restrictionResponseJObservableCubeSet R p q a := by
    funext R
    calc
      Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q
          = ResponseJ (openCubeSet R) p q a.toFun := by
              simpa [F, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain R) (F.coeffOn R) p q
      _ = restrictionResponseJObservableCubeSet R p q a := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q a.toFun]
            rfl
  have hAvg :
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (F.coeffOn i.1) p q) =
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) := by
    calc
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (F.coeffOn i.1) p q)
          =
        descendantsAverage Q j
          (fun R : TriadicCube d =>
            Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q) := by
            simpa [Pcell] using
              Ch02.descendantsDomainPartition_weightedAverage Q j
                (fun R : TriadicCube d =>
                  Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q)
      _ = descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) := by
            rw [hTerm]
  calc
    restrictionResponseJObservableCubeSet (originCube d m) p q a
        = restrictionResponseJObservableCubeSet Q p q a := rfl
    _ = Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := hParent.symm
    _ ≤ Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (F.coeffOn i.1) p q) := hsub
    _ = descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) := hAvg
    _ =
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => restrictionResponseJObservableCubeSet R p q a) := rfl

/-- Pointwise response subadditivity on an arbitrary triadic cube for the Ch4
scalar response observable, with the a.e. coefficient representative handled
by the Chapter 2 coefficient family. -/
theorem restrictionResponseJObservableCubeSet_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (p q : Vec d) :
    restrictionResponseJObservableCubeSet Q p q a ≤
      descendantsAverage Q (Int.toNat (Q.scale - k))
        (fun R => restrictionResponseJObservableCubeSet R p q a) := by
  let j : ℕ := Int.toNat (Q.scale - k)
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hcell :
      ∀ i : Pcell.Cell, Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    intro i
    have hiScale : i.1 ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      change i.1 ∈ descendantsAtDepth Q j
      exact i.2
    exact F.restrictsTo_descendant hk hiScale
  have hsub :=
    (Ch02.responseSubadditivityAndScalingTheory (Ch02.cubeDomain Q)
      (F.coeffOn Q)).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => F.coeffOn i.1) hcell p q
  have hParent :
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q =
        restrictionResponseJObservableCubeSet Q p q a := by
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q
          = ResponseJ (openCubeSet Q) p q a.toFun := by
              simpa [F, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain Q) (F.coeffOn Q) p q
      _ = restrictionResponseJObservableCubeSet Q p q a := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a.toFun]
            rfl
  have hTerm :
      (fun R : TriadicCube d =>
          Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q) =
        fun R : TriadicCube d => restrictionResponseJObservableCubeSet R p q a := by
    funext R
    calc
      Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q
          = ResponseJ (openCubeSet R) p q a.toFun := by
              simpa [F, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain R) (F.coeffOn R) p q
      _ = restrictionResponseJObservableCubeSet R p q a := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q a.toFun]
            rfl
  have hAvg :
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (F.coeffOn i.1) p q) =
        descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) := by
    calc
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (F.coeffOn i.1) p q)
          =
        descendantsAverage Q j
          (fun R : TriadicCube d =>
            Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q) := by
            simpa [Pcell] using
              Ch02.descendantsDomainPartition_weightedAverage Q j
                (fun R : TriadicCube d =>
                  Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q)
      _ = descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) := by
            rw [hTerm]
  calc
    restrictionResponseJObservableCubeSet Q p q a
        = Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q := hParent.symm
    _ ≤ Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (F.coeffOn i.1) p q) := hsub
    _ = descendantsAverage Q j (fun R => restrictionResponseJObservableCubeSet R p q a) := hAvg
    _ =
        descendantsAverage Q (Int.toNat (Q.scale - k))
          (fun R => restrictionResponseJObservableCubeSet R p q a) := rfl

/-- Pointwise block coarse-matrix subadditivity on an arbitrary triadic cube
for a locally a.e.-elliptic coefficient field, with the a.e. representative
handled by the Chapter 2 coefficient family. -/
theorem coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    BlockMatLoewnerLE
      (coarseBlockMatrix (cubeSet Q) a.toFun)
      (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
        (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
  let j : ℕ := Int.toNat (Q.scale - k)
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hcell :
      ∀ i : Pcell.Cell, Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    intro i
    have hiScale : i.1 ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      change i.1 ∈ descendantsAtDepth Q j
      exact i.2
    exact F.restrictsTo_descendant hk hiScale
  have hsub :=
    (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q)
      (F.coeffOn Q)).block_matrix_subadditive
        Pcell (fun i : Pcell.Cell => F.coeffOn i.1) hcell
  have hParent :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hTerm :
      (fun R : TriadicCube d =>
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) =
        fun R : TriadicCube d => coarseBlockMatrix (cubeSet R) a.toFun := by
    funext R
    simpa [F] using
      (RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha R).symm
  have hAvg :
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell => Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1)) =
        descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
    calc
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell => Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
          =
        descendantsAverageBlockMat Q j
          (fun R : TriadicCube d =>
            Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) := by
            simpa [Pcell, Ch02.descendantsDomainPartition] using
              Ch02.descendantsDomainPartition_weightedBlockAverage Q j
                (fun R : TriadicCube d =>
                  Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R))
      _ = descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
            rw [hTerm]
  simpa [j, hParent, hAvg] using hsub

/-- Pointwise block coarse-matrix subadditivity for a locally a.e.-elliptic
coefficient field, with the a.e. representative handled by the Chapter 2
coefficient family. -/
theorem coarseBlockMatrix_le_descendantsAverageBlockMat_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) {n m : ℤ} (hnm : n ≤ m) :
    BlockMatLoewnerLE
      (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun)
      (descendantsAverageBlockMat (originCube d m) (Int.toNat (m - n))
        (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
  simpa using!
    coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
      ha (originCube d m) hnm


end

end Ch04
end Book
end Homogenization
