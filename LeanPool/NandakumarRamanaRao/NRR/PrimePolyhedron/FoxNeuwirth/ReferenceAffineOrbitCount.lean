/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Order.Support
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.PrimeOrbitCycle
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceZero
/-!
# The explicit reference affine orbit count

This is Step S5 of the simplest AAK route.  On a non-top Fox--Neuwirth vertex we use the
first-coordinate reference vector: the block-index vector modulo the diagonal.  At a top-cell
vertex this vector is zero, so we perturb it in a rank-dependent direction.  The adjacent gaps of
the perturbation direction are `1, 2, ..., p - 1`.

For a maximal flag, positive barycentric coefficients force the bottom rank to agree with the
final top rank.  Comparing adjacent labels then forces the bars to be removed in the identity
order.  Thus one maximal flag is selected for every top Fox--Neuwirth cell.  The selected flags
form one prime-symmetry orbit for `p = 2` and two equally oriented orbits for odd primes.

At perturbation parameter zero the augmented affine determinant is the oriented maximal-flag
coefficient, up to the constant sign `(-1)^(p-1)`.  Since there are finitely many maximal flags, a
single sufficiently small positive perturbation preserves all determinant signs.  This gives a
regular affine reference map whose orbit zero count is the previously computed nonzero value
`FoxNeuwirth.referenceSignedOrbitCount p`.
-/

namespace NRR

open scoped BigOperators Matrix

variable {p : Nat}

namespace FoxNeuwirthOrderComplex
namespace ReferenceAffineOrbitCount

open MaximalFlagCode TopFlagSubdivision PrimeOrbitCycle

@[simp] theorem stageIndex_val (hp : Nat.Prime p) (i : Fin (p - 1 + 1)) :
    (stageIndex hp i).1 = i.1 := rfl

/-- The fixed label omitted from the difference-coordinate model of the diagonal quotient. -/
def lastLabel (hp : Nat.Prime p) : Fin p :=
  ⟨p - 1, by have := hp.pos; omega⟩

/-- Embed a target coordinate into the label set. -/
def coordinateLabel (hp : Nat.Prime p) (r : Fin (p - 1)) : Fin p :=
  ⟨r.1, by have := hp.two_le; omega⟩

/-- Triangular numbers.  Their consecutive gaps are `1,2,...`. -/
def triangular (n : Nat) : Nat := n * (n + 1) / 2

theorem triangular_two_mul (n : Nat) : 2 * triangular n = n * (n + 1) := by
  unfold triangular
  rw [Nat.mul_div_cancel']
  exact (Nat.even_mul_succ_self n).two_dvd

@[simp] theorem triangular_succ_sub (n : Nat) :
    (triangular (n + 1) : Int) - triangular n = n + 1 := by
  have h1 := triangular_two_mul n
  have h2 := triangular_two_mul (n + 1)
  have e : triangular (n + 1) = triangular n + (n + 1) := by nlinarith [h1, h2]
  rw [e]; push_cast; ring

/-- Triangular numbers are strictly increasing. -/
theorem triangular_strictMono : StrictMono triangular := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := triangular_succ_sub n
  omega

/-- Triangular numbers are injective. -/
theorem triangular_injective : Function.Injective triangular :=
  triangular_strictMono.injective

/-- Sum of an indicator over a finite type is the cardinality of its support, cast to the ring. -/
theorem sum_if_one_zero_eq_card
    {X R : Type*} [Fintype X]  [Semiring R]
    (P : X → Prop) [DecidablePred P] :
    (∑ x : X, if P x then (1 : R) else 0) =
      ((Fintype.card {x : X // P x} : Nat) : R) := by
  classical
  rw [Fintype.card_subtype]
  simp

/-- Block-index vector modulo the diagonal, in the fixed difference coordinates. -/
def blockDifference
    (hp : Nat.Prime p) (c : BarredPermutation p) (r : Fin (p - 1)) : Int :=
  (c.blockIndex (coordinateLabel hp r) : Int) -
    (c.blockIndex (lastLabel hp) : Int)

/-- Generic direction at a top-cell vertex.  In the final rank order its adjacent gaps are
`1,2,...,p-1`. -/
def topDirection
    (hp : Nat.Prime p) (c : BarredPermutation p) (r : Fin (p - 1)) : Int :=
  (triangular (c.rank (coordinateLabel hp r)).1 : Int) -
    (triangular (c.rank (lastLabel hp)).1 : Int)

/-- Unquotiented scalar attached to one label.  The actual target coordinates are its
differences from `lastLabel`.  Introducing this lift is essential when comparing two arbitrary
labels: neither label has to be one of the fixed target-coordinate labels. -/
def liftedVertexValue
    (p : Nat) (epsilon : Real)
    (c : BarredPermutation p) (x : Fin p) : Real :=
  if c.IsTop then
    -epsilon * (triangular (c.rank x).1 : Real)
  else
    (c.blockIndex x : Real)

/-- Piecewise-affine reference map with perturbation parameter `epsilon`. -/
noncomputable def mapAt
    (hp : Nat.Prime p) (epsilon : Real) : AffineVertexMap p (p - 1) where
  vertexValue c r :=
    if c.IsTop then
      -epsilon * (topDirection hp c r : Real)
    else
      (blockDifference hp c r : Real)

/-- Every target coordinate is the difference of the lifted values at its label and at the
omitted label. -/
theorem mapAt_vertexValue_eq_lifted_sub
    (hp : Nat.Prime p) (epsilon : Real)
    (c : BarredPermutation p) (r : Fin (p - 1)) :
    (mapAt hp epsilon).vertexValue c r =
      liftedVertexValue p epsilon c (coordinateLabel hp r) -
        liftedVertexValue p epsilon c (lastLabel hp) := by
  by_cases htop : c.IsTop
  · simp [mapAt, liftedVertexValue, topDirection, htop]
    ring
  · simp [mapAt, liftedVertexValue, blockDifference, htop]

/-- The selected maximal flag over a top permutation: bottom and top ranks agree, and bars are
removed in their natural order. -/
def selectedCode (sigma : Equiv.Perm (Fin p)) : Code p where
  bottom := sigma
  removal := 1
  top := sigma

/-- Selected maximal simplex over a top permutation. -/
noncomputable def selectedSimplex
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) : Simplex p (p - 1) :=
  toSimplex hp (selectedCode sigma)

/-- A maximal simplex is one of the selected reference simplices. -/
def IsSelected
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) : Prop :=
  ∃ sigma : Equiv.Perm (Fin p), s = selectedSimplex hp sigma

noncomputable instance isSelectedDecidable
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) : Decidable (IsSelected hp s) :=
  Classical.dec _

@[simp] theorem selectedCode_bottom (sigma : Equiv.Perm (Fin p)) :
    (selectedCode sigma).bottom = sigma := rfl

@[simp] theorem selectedCode_removal (sigma : Equiv.Perm (Fin p)) :
    (selectedCode sigma).removal = 1 := rfl

@[simp] theorem selectedCode_top (sigma : Equiv.Perm (Fin p)) :
    (selectedCode sigma).top = sigma := rfl

/-- The integer sign of a permutation is always `1` or `-1`. -/
theorem permSignInt_eq_one_or_neg_one
    {n : Nat} (sigma : Equiv.Perm (Fin n)) :
    permSignInt sigma = 1 ∨ permSignInt sigma = -1 := by
  unfold permSignInt
  rcases Int.units_eq_one_or (Equiv.Perm.sign sigma) with h | h
  · left
    simp [h]
  · right
    simp [h]

/-- A coded maximal-flag stage is top-dimensional exactly at the final index. -/
theorem toSimplex_isTop_iff_last
    (hp : Nat.Prime p) (z : Code p) (i : Fin (p - 1 + 1)) :
    (toSimplex hp z i).IsTop ↔ i.1 = p - 1 := by
  classical
  rw [toSimplex_apply]
  unfold BarredPermutation.IsTop stageCell
  constructor
  · intro htop
    by_contra hi
    have hi' : i.1 < p - 1 := by
      have hib := i.2
      omega
    let r : Fin (p - 1) := z.removal ⟨i.1, hi'⟩
    have hr : r ∈ retainedBars z (stageIndex hp i) := by
      rw [mem_retainedBars_iff]
      simp [r]
    have hempty : retainedBars z (stageIndex hp i) = ∅ := htop
    rw [hempty] at hr
    exact Finset.notMem_empty r hr
  · intro hi
    apply Finset.eq_empty_iff_forall_notMem.2
    intro r hr
    rw [mem_retainedBars_iff] at hr
    have hrb := (z.removal.symm r).2
    simp only [stageIndex_val, hi] at hr
    omega

/-- Lower-unit cumulative matrix. -/
def lowerCumulativeMatrix (n : Nat) : Matrix (Fin n) (Fin n) Int :=
  Matrix.of fun i j => if j.1 ≤ i.1 then 1 else 0

/-- The lower cumulative matrix is triangular with diagonal one. -/
theorem det_lowerCumulativeMatrix (n : Nat) :
    Matrix.det (lowerCumulativeMatrix n) = 1 := by
  classical
  rw [Matrix.det_of_isLowerTriangular (lowerCumulativeMatrix n) (by
    intro i j hij
    have hlt : i < j := by simpa using hij
    have hval : i.1 < j.1 := hlt
    simp only [lowerCumulativeMatrix, Matrix.of_apply]
    rw [if_neg (by omega)])]
  simp [lowerCumulativeMatrix]

/-- Cumulative rows ordered by a permutation. -/
def cumulativePermutationMatrix
    {n : Nat} (rho : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) Int :=
  Matrix.of fun k j => if j.1 ≤ (rho.symm k).1 then 1 else 0

/-- The cumulative-permutation determinant is the permutation sign. -/
theorem det_cumulativePermutationMatrix
    {n : Nat} (rho : Equiv.Perm (Fin n)) :
    Matrix.det (cumulativePermutationMatrix rho) = permSignInt rho := by
  classical
  have hmul : cumulativePermutationMatrix rho =
      Equiv.Perm.permMatrix Int rho.symm * lowerCumulativeMatrix n := by
    ext k j
    simp only [cumulativePermutationMatrix, lowerCumulativeMatrix,
      Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq]
    rw [Finset.sum_eq_single (rho.symm k)]
    · simp
    · intro x _ hx
      rw [if_neg (fun h => hx h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hmul, Matrix.det_mul, Matrix.det_permutation,
    det_lowerCumulativeMatrix]
  simp [permSignInt]

/-- The fixed label-coordinate family enumerates every label except `lastLabel`. -/
theorem coordinateLabel_range
    (hp : Nat.Prime p) :
    Set.range (coordinateLabel hp) = {x : Fin p | x ≠ lastLabel hp} := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    simp only [coordinateLabel, lastLabel, Set.mem_ofPred_eq, ne_eq, Fin.mk.injEq]
    have := r.2; omega
  · intro hx
    refine ⟨⟨x.1, ?_⟩, Fin.ext rfl⟩
    have hxlast : x.1 ≠ p - 1 := by
      intro h
      apply hx
      apply Fin.ext
      simpa [lastLabel] using h
    have xb := x.2
    omega

/-- Vanishing of all fixed difference coordinates implies vanishing of the weighted lifted
difference for any two labels.  This is the correct coordinate-free replacement for subtracting
two target equations, and it also handles the omitted label. -/
theorem weighted_lifted_difference_eq_zero
    (hp : Nat.Prime p) (epsilon : Real)
    (s : Simplex p (p - 1)) (w : StandardSimplex (p - 1))
    (hzero : ∀ r, (mapAt hp epsilon).value s w r = 0)
    (x y : Fin p) :
    (∑ i : Fin (p - 1 + 1), w i *
      (liftedVertexValue p epsilon (s i) x -
        liftedVertexValue p epsilon (s i) y)) = 0 := by
  classical
  have hcoordinate (u : Fin p) :
      (∑ i : Fin (p - 1 + 1), w i *
        (liftedVertexValue p epsilon (s i) u -
          liftedVertexValue p epsilon (s i) (lastLabel hp))) = 0 := by
    by_cases hu : u = lastLabel hp
    · subst u
      simp
    · have huRange : u ∈ Set.range (coordinateLabel hp) := by
        rw [coordinateLabel_range hp]
        exact hu
      rcases huRange with ⟨r, rfl⟩
      simpa only [AffineVertexMap.value, mapAt_vertexValue_eq_lifted_sub]
        using hzero r
  calc
    (∑ i : Fin (p - 1 + 1), w i *
        (liftedVertexValue p epsilon (s i) x -
          liftedVertexValue p epsilon (s i) y)) =
        (∑ i : Fin (p - 1 + 1), w i *
          (liftedVertexValue p epsilon (s i) x -
            liftedVertexValue p epsilon (s i) (lastLabel hp))) -
        (∑ i : Fin (p - 1 + 1), w i *
          (liftedVertexValue p epsilon (s i) y -
            liftedVertexValue p epsilon (s i) (lastLabel hp))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 0 := by rw [hcoordinate x, hcoordinate y, sub_self]

/-- Adjacent bottom ranks differ by one block exactly while their separating bar is retained. -/
theorem stageBlock_adjacent_sub
    (hp : Nat.Prime p) (z : Code p) (j : Fin p) (r : Fin (p - 1)) :
    (stageBlock z j (z.bottom.symm (stageIndex hp r.succ)) : Int) -
        stageBlock z j (z.bottom.symm (stageIndex hp r.castSucc)) =
      if j.1 ≤ (z.removal.symm r).1 then 1 else 0 := by
  classical
  let S := retainedBars z j
  have hbottomSucc : z.bottom (z.bottom.symm (stageIndex hp r.succ)) = stageIndex hp r.succ :=
    z.bottom.apply_symm_apply _
  have hbottomCast :
      z.bottom (z.bottom.symm (stageIndex hp r.castSucc)) = stageIndex hp r.castSucc :=
    z.bottom.apply_symm_apply _
  simp only [stageBlock, hbottomSucc, hbottomCast, stageIndex_succ_val,
    stageIndex_castSucc_val]
  change ((S.filter fun q => q.1 < r.1 + 1).card : Int) -
      (S.filter fun q => q.1 < r.1).card =
        if j.1 ≤ (z.removal.symm r).1 then 1 else 0
  by_cases hr : r ∈ S
  · have hfilter :
        S.filter (fun q => q.1 < r.1 + 1) =
          insert r (S.filter fun q => q.1 < r.1) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hqS, hq⟩
        by_cases hqr : q = r
        · exact Or.inl hqr
        · exact Or.inr ⟨hqS, by
            have hvalne : q.1 ≠ r.1 := fun h => hqr (Fin.ext h)
            omega⟩
      · rintro (rfl | ⟨hqS, hq⟩)
        · exact ⟨hr, by omega⟩
        · exact ⟨hqS, by omega⟩
    rw [hfilter, Finset.card_insert_of_notMem (by simp)]
    rw [if_pos ((mem_retainedBars_iff z j r).1 hr)]
    norm_num
  · have hfilter :
        S.filter (fun q => q.1 < r.1 + 1) =
          S.filter (fun q => q.1 < r.1) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hqS, hq⟩
        refine ⟨hqS, ?_⟩
        by_contra hnot
        have hval : q.1 = r.1 := by omega
        exact hr (Fin.ext hval ▸ hqS)
      · rintro ⟨hqS, hq⟩
        exact ⟨hqS, by omega⟩
    rw [hfilter, sub_self]
    rw [if_neg]
    exact fun h => hr ((mem_retainedBars_iff z j r).2 h)

/-- The number of indices in a finite ordinal not exceeding `r`. -/
theorem sum_fin_le_indicator
    {n : Nat} (r : Fin n) :
    (∑ j : Fin n, if j ≤ r then (1 : Int) else 0) =
      ((r.1 + 1 : Nat) : Int) := by
  rw [sum_if_one_zero_eq_card]
  norm_cast
  rw [Fintype.card_subtype]
  have hset :
      Finset.univ.filter (fun j : Fin n => j ≤ r) = Finset.Iic r := by
    ext j
    simp [Finset.mem_Iic]
  rw [hset, Fin.card_Iic]

/-- For a selected flag, the sum of the earlier-stage block numbers of a label is the triangular
number of its rank.  This is the discrete antiderivative of the adjacent retained-bar indicator. -/
theorem selected_stageBlock_sum_rank
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) (x : Fin p) :
    (∑ j : Fin (p - 1),
      (stageBlock (selectedCode sigma) (stageIndex hp j.castSucc) x : Int)) =
      (triangular (sigma x).1 : Int) := by
  classical
  have hgeneral : ∀ m : Nat, ∀ hm : m < p,
      (∑ j : Fin (p - 1),
        (stageBlock (selectedCode sigma) (stageIndex hp j.castSucc)
          (sigma.symm ⟨m, hm⟩) : Int)) =
        (triangular m : Int) := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp [stageBlock, selectedCode]
        change 0 = 0
        rfl
    | succ m ih =>
        intro hm
        have hm0 : m < p := by omega
        let r : Fin (p - 1) := ⟨m, by omega⟩
        let x0 : Fin p := sigma.symm ⟨m, hm0⟩
        let x1 : Fin p := sigma.symm ⟨m + 1, hm⟩
        have hsucc : stageIndex hp r.succ = (⟨m + 1, hm⟩ : Fin p) := by
          apply Fin.ext
          simp [r]
        have hcast : stageIndex hp r.castSucc = (⟨m, hm0⟩ : Fin p) := by
          apply Fin.ext
          simp [r]
        have hdiff (j : Fin (p - 1)) :
            (stageBlock (selectedCode sigma) (stageIndex hp j.castSucc) x1 : Int) -
                stageBlock (selectedCode sigma) (stageIndex hp j.castSucc) x0 =
              if j ≤ r then 1 else 0 := by
          have h := stageBlock_adjacent_sub hp (selectedCode sigma)
            (stageIndex hp j.castSucc) r
          have e1 : (selectedCode sigma).bottom.symm (stageIndex hp r.succ) = x1 := by
            show sigma.symm (stageIndex hp r.succ) = sigma.symm ⟨m + 1, hm⟩
            rw [hsucc]
          have e0 : (selectedCode sigma).bottom.symm (stageIndex hp r.castSucc) = x0 := by
            show sigma.symm (stageIndex hp r.castSucc) = sigma.symm ⟨m, hm0⟩
            rw [hcast]
          rw [e1, e0] at h
          rw [h]
          have hval : ((selectedCode sigma).removal.symm r).1 = r.1 := by
            change ((1 : Equiv.Perm (Fin (p - 1))).symm r).1 = r.1
            rfl
          simp only [hval, stageIndex_val, Fin.le_def, Fin.val_castSucc]
        have hsumdiff :
            (∑ j : Fin (p - 1),
                (stageBlock (selectedCode sigma) (stageIndex hp j.castSucc) x1 : Int)) -
              (∑ j : Fin (p - 1),
                (stageBlock (selectedCode sigma) (stageIndex hp j.castSucc) x0 : Int)) =
              ∑ j : Fin (p - 1), if j ≤ r then (1 : Int) else 0 := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          exact hdiff j
        have hcount :
            (∑ j : Fin (p - 1), if j ≤ r then (1 : Int) else 0) =
              ((m + 1 : Nat) : Int) := by
          simpa [r] using sum_fin_le_indicator r
        calc
          (∑ j : Fin (p - 1),
              (stageBlock (selectedCode sigma) (stageIndex hp j.castSucc)
                (sigma.symm ⟨m + 1, hm⟩) : Int)) =
              (∑ j : Fin (p - 1),
                (stageBlock (selectedCode sigma) (stageIndex hp j.castSucc)
                  (sigma.symm ⟨m, hm0⟩) : Int)) + ((m + 1 : Nat) : Int) := by
                simpa [x0, x1, add_comm] using
                  sub_eq_iff_eq_add.mp (hsumdiff.trans hcount)
          _ = (triangular m : Int) + ((m + 1 : Nat) : Int) := by
                rw [ih hm0]
          _ = (triangular (m + 1) : Int) := by
                have htri := triangular_succ_sub m
                omega
  simpa using hgeneral (sigma x).1 (sigma x).2

/-- Summing the non-top vertices of a selected flag gives precisely its triangular top direction. -/
theorem sum_blockDifference_selected
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) (r : Fin (p - 1)) :
    (∑ j : Fin (p - 1),
      blockDifference hp (selectedSimplex hp sigma j.castSucc) r) =
      topDirection hp (selectedSimplex hp sigma (Fin.last (p - 1))) r := by
  simp only [blockDifference, selectedSimplex, toSimplex_apply,
    stageCell_blockIndex]
  rw [Finset.sum_sub_distrib,
    selected_stageBlock_sum_rank hp sigma (coordinateLabel hp r),
    selected_stageBlock_sum_rank hp sigma (lastLabel hp)]
  simp [topDirection, selectedSimplex, toSimplex_apply, stageIndex_last,
    stageCell, stageRank_last hp]

/-- Type-A cut-basis matrix in the fixed diagonal-quotient coordinates. -/
def cutBasisMatrix
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) Int :=
  Matrix.of fun r k =>
    (if (sigma (coordinateLabel hp r)).1 > k.1 then 1 else 0) -
      (if (sigma (lastLabel hp)).1 > k.1 then 1 else 0)

/-- Determinant of the standard type-A cut basis.

The proof augments the difference matrix by the constant column.  Reindexing rows by `sigma`
turns the augmented matrix into the lower cumulative matrix.  Expansion along the omitted-label
row gives the stated cofactor sign. -/
theorem det_cutBasisMatrix
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) :
    Matrix.det (cutBasisMatrix hp sigma) =
      (-1 : Int) ^ (p - 1) * permSignInt sigma := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let A : Matrix (Fin p) (Fin p) Int := Matrix.of fun x j =>
    if j.1 ≤ (sigma x).1 then 1 else 0
  let T : Matrix (Fin p) (Fin p) Int := Matrix.of fun i j =>
    if i = lastLabel hp then
      if j = lastLabel hp then 1 else 0
    else if j = i then 1 else if j = lastLabel hp then -1 else 0
  let B : Matrix (Fin p) (Fin p) Int := T * A
  have hTtri : T.BlockTriangular id := by
    intro i j hji
    have hji2 : j.1 < i.1 := hji
    have hjlast : j ≠ lastLabel hp := by
      intro h; subst h
      have hll : (lastLabel hp).1 = p - 1 := rfl
      have hi2 : i.1 < p := i.2
      omega
    simp only [T, Matrix.of_apply]
    by_cases hi : i = lastLabel hp
    · rw [if_pos hi, if_neg hjlast]
    · rw [if_neg hi]
      have hji' : j ≠ i := by intro h; rw [h] at hji2; exact lt_irrefl _ hji2
      rw [if_neg hji', if_neg hjlast]
  have hdetT : Matrix.det T = 1 := by
    rw [Matrix.det_of_isUpperTriangular hTtri]
    simp [T]
  have hA : A = Equiv.Perm.permMatrix Int sigma * lowerCumulativeMatrix p := by
    ext i j
    simp only [A, lowerCumulativeMatrix,
      Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq]
    rw [Finset.sum_eq_single (sigma i)]
    · simp
    · intro x _ hx
      rw [if_neg (fun h => hx h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hdetA : Matrix.det A = permSignInt sigma := by
    rw [hA, Matrix.det_mul, Matrix.det_permutation,
      det_lowerCumulativeMatrix]
    simp [permSignInt]
  have hdetB : Matrix.det B = permSignInt sigma := by
    show Matrix.det (T * A) = permSignInt sigma
    rw [Matrix.det_mul, hdetT, one_mul, hdetA]
  have hcol : ∀ x : Fin p, A x 0 = 1 := by
    intro x; simp [A]
  have hBfirst (i : Fin p) :
      B i 0 = if i = lastLabel hp then 1 else 0 := by
    show (T * A) i 0 = _
    by_cases hi : i = lastLabel hp
    · simp only [Matrix.mul_apply, T, Matrix.of_apply, hcol, mul_one, if_pos hi]
      simp [Finset.sum_ite_eq']
    · simp only [Matrix.mul_apply, T, Matrix.of_apply, hcol, mul_one, if_neg hi]
      have hrw : ∀ x : Fin p,
          (if x = i then (1:Int) else if x = lastLabel hp then -1 else 0)
            = (if x = i then 1 else 0) + (if x = lastLabel hp then -1 else 0) := by
        intro x
        by_cases hxi : x = i
        · subst hxi; simp [hi]
        · by_cases hxl : x = lastLabel hp
          · subst hxl; simp [hxi]
          · simp [hxi, hxl]
      simp_rw [hrw]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp
  let e : Fin (p - 1 + 1) ≃ Fin p :=
    (Fin.castOrderIso (FoxNeuwirthChain.maximalIndex_eq hp)).toEquiv
  let B' : Matrix (Fin (p - 1 + 1)) (Fin (p - 1 + 1)) Int :=
    B.submatrix e e
  have he_zero : e 0 = 0 := by
    apply Fin.ext
    simp [e, Fin.castOrderIso]
  have he_last : e (Fin.last (p - 1)) = lastLabel hp := by
    apply Fin.ext
    simp [e, Fin.castOrderIso, lastLabel]
  have hdetB' : Matrix.det B' = permSignInt sigma := by
    simpa [B'] using hdetB
  have hB'first (i : Fin (p - 1 + 1)) :
      B' i 0 = if i = Fin.last (p - 1) then 1 else 0 := by
    have hiff : e i = lastLabel hp ↔ i = Fin.last (p - 1) := by
      rw [← he_last]; exact e.injective.eq_iff
    rw [show B' i 0 = B (e i) 0 from by simp [B', Matrix.submatrix_apply, he_zero]]
    rw [hBfirst]
    simp only [hiff]
  have hminor' :
      (B'.submatrix (Fin.last (p - 1)).succAbove Fin.succ).det =
        Matrix.det (cutBasisMatrix hp sigma) := by
    congr 1
    ext r k
    have hlast : coordinateLabel hp r ≠ lastLabel hp := by
      apply Fin.ne_of_val_ne
      have := r.2
      simp only [coordinateLabel, lastLabel]
      omega
    have hval : (e (Fin.succ k)).1 = k.1 + 1 := by
      simp [e, Fin.castOrderIso]
    have her : e ((Fin.last (p - 1)).succAbove r) = coordinateLabel hp r := by
      apply Fin.ext
      simp [e, Fin.castOrderIso, coordinateLabel, Fin.succAbove_last]
    have key : ∀ (a : Fin p) (f : Fin p → Int), a ≠ lastLabel hp →
        (∑ x, (if x = a then (1:Int) else if x = lastLabel hp then -1 else 0) * f x)
          = f a - f (lastLabel hp) := by
      intro a f ha
      have hrw : ∀ x : Fin p,
          (if x = a then (1:Int) else if x = lastLabel hp then -1 else 0) * f x
            = (if x = a then f a else 0) + (if x = lastLabel hp then -f (lastLabel hp) else 0) := by
        intro x
        by_cases hxa : x = a
        · subst hxa; simp [ha]
        · by_cases hxl : x = lastLabel hp
          · subst hxl; simp [hxa]
          · simp [hxa, hxl]
      simp_rw [hrw]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp [sub_eq_add_neg]
    simp only [B', Matrix.submatrix_apply, her]
    show (T * A) (coordinateLabel hp r) (e (Fin.succ k)) = cutBasisMatrix hp sigma r k
    rw [Matrix.mul_apply]
    simp only [T, Matrix.of_apply, if_neg hlast]
    have hkey := key (coordinateLabel hp r) (fun x => A x (e (Fin.succ k))) hlast
    rw [hkey]
    simp only [A, Matrix.of_apply, cutBasisMatrix, hval]
    split_ifs <;> omega
  have hsum :
      (∑ i : Fin (p - 1 + 1),
        (-1 : Int) ^ i.1 * B' i 0 *
          (B'.submatrix i.succAbove Fin.succ).det) =
        (-1 : Int) ^ (p - 1) *
          Matrix.det (cutBasisMatrix hp sigma) := by
    rw [Finset.sum_eq_single (Fin.last (p - 1))]
    · rw [hB'first, if_pos rfl, Fin.val_last, hminor']
      ring
    · intro i hi hne
      simp [hB'first, hne]
    · simp
  have hcofactor :
      permSignInt sigma = (-1 : Int) ^ (p - 1) *
        Matrix.det (cutBasisMatrix hp sigma) := by
    calc
      permSignInt sigma = Matrix.det B' := hdetB'.symm
      _ = ∑ i : Fin (p - 1 + 1),
          (-1 : Int) ^ i.1 * B' i 0 *
            (B'.submatrix i.succAbove Fin.succ).det :=
        Matrix.det_succ_column_zero B'
      _ = (-1 : Int) ^ (p - 1) *
          Matrix.det (cutBasisMatrix hp sigma) := hsum
  have hunit : ((-1 : Int) ^ (p - 1)) * ((-1 : Int) ^ (p - 1)) = 1 := by
    rw [← pow_add]
    simp [two_mul]
  calc
    Matrix.det (cutBasisMatrix hp sigma)
        = 1 * Matrix.det (cutBasisMatrix hp sigma) := by simp
    _ = (((-1 : Int) ^ (p - 1)) * ((-1 : Int) ^ (p - 1))) *
          Matrix.det (cutBasisMatrix hp sigma) := by rw [hunit]
    _ = (-1 : Int) ^ (p - 1) * permSignInt sigma := by
      rw [hcofactor]
      ring

theorem selectedSimplex_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (sigma : Equiv.Perm (Fin p)) :
    g • selectedSimplex hp sigma =
      selectedSimplex hp ((PrimeSymmetry.toPerm p g).symm.trans sigma) := by
  classical
  let tau : Equiv.Perm (Fin p) := PrimeSymmetry.toPerm p g
  let sigma' : Equiv.Perm (Fin p) := tau.symm.trans sigma
  apply Simplex.ext
  intro i
  change (stageCell (selectedCode sigma) (stageIndex hp i)).relabel tau =
    stageCell (selectedCode sigma') (stageIndex hp i)
  apply BarredPermutation.ext
  · change tau.symm.trans (stageRank (selectedCode sigma) (stageIndex hp i)) =
      stageRank (selectedCode sigma') (stageIndex hp i)
    symm
    apply perm_eq_of_lt_iff
    intro x y
    change
      (stageRank (selectedCode sigma') (stageIndex hp i) x).1 <
          (stageRank (selectedCode sigma') (stageIndex hp i) y).1 ↔
        (stageRank (selectedCode sigma) (stageIndex hp i) (tau.symm x)).1 <
          (stageRank (selectedCode sigma) (stageIndex hp i) (tau.symm y)).1
    rw [stageRank_lt_iff, stageRank_lt_iff]
    congr 1;
      simp [stageKey, stageBlock, selectedCode, sigma', tau, retainedBars,
        removedBefore]
    rfl
  · rfl

theorem isSelected_toSimplex_iff
    (hp : Nat.Prime p) (z : Code p) :
    IsSelected hp (toSimplex hp z) ↔ z.bottom = z.top ∧ z.removal = 1 := by
  constructor
  · rintro ⟨sigma, hs⟩
    have hz : z = selectedCode sigma :=
      (toSimplex_injective hp) hs
    subst z
    simp
  · rintro ⟨hbt, hr⟩
    refine ⟨z.top, ?_⟩
    apply congrArg (toSimplex hp)
    apply Code.ext <;> simp [selectedCode, hbt, hr]

/-- At parameter zero, the top vertex is zero and all earlier vertices are block-difference
vectors. -/
theorem mapAt_zero_value_toSimplex
    (hp : Nat.Prime p) (z : Code p)
    (i : Fin (p - 1 + 1)) (r : Fin (p - 1)) :
    (mapAt hp 0).vertexValue (toSimplex hp z i) r =
      if i.1 = p - 1 then 0
      else (blockDifference hp (toSimplex hp z i) r : Real) := by
  by_cases hi : i.1 = p - 1
  · have htop : (stageCell z (stageIndex hp i)).IsTop :=
      (toSimplex_isTop_iff_last hp z i).2 hi
    simp [mapAt, htop, hi]
  · have hnot : ¬(stageCell z (stageIndex hp i)).IsTop :=
      fun htop => hi ((toSimplex_isTop_iff_last hp z i).1 htop)
    simp [mapAt, hnot, hi]

/-- Matrix of the non-top block-difference vertices of a coded maximal flag. -/
noncomputable def blockVertexMatrix
    (hp : Nat.Prime p) (z : Code p) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) Int :=
  fun r j => blockDifference hp (toSimplex hp z j.castSucc) r

/-- The block-vertex determinant is the code orientation, with the fixed difference-coordinate
orientation factor.  This is the integral braid-fan basis calculation. -/
theorem det_blockVertexMatrix
    (hp : Nat.Prime p) (z : Code p) :
    Matrix.det (blockVertexMatrix hp z) =
      (-1 : Int) ^ (p - 1) * coefficient z := by
  classical
  -- Taking adjacent differences in the final rank order changes the fixed label-difference
  -- basis by `(-1)^(p-1) * sign(bottom)`.  Taking successive column differences changes the
  -- retained-bar matrix into `removal.symm.permMatrix`, whose determinant is `sign(removal)`.
  have hfactor : blockVertexMatrix hp z =
      (cutBasisMatrix hp z.bottom) *
        (cumulativePermutationMatrix z.removal) := by
    ext r j
    have hblock (x : Fin p) :
        (stageBlock z (stageIndex hp j.castSucc) x : Int) =
          ∑ k : Fin (p - 1),
            if j ≤ z.removal.symm k ∧ k.1 < (z.bottom x).1 then 1 else 0 := by
      rw [sum_if_one_zero_eq_card]
      norm_cast
      rw [Fintype.card_subtype]
      unfold stageBlock
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        mem_retainedBars_iff, stageIndex_val, Fin.val_castSucc, Fin.le_def]
    simp only [blockVertexMatrix, blockDifference, toSimplex_apply,
      stageCell_blockIndex, Matrix.mul_apply, cutBasisMatrix,
      cumulativePermutationMatrix, Matrix.of_apply]
    rw [hblock (coordinateLabel hp r), hblock (lastLabel hp),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> omega
  rw [hfactor]
  rw [Matrix.det_mul]
  rw [det_cutBasisMatrix hp z.bottom]
  rw [det_cumulativePermutationMatrix z.removal]
  simp [coefficient, mul_assoc, mul_left_comm, mul_comm]

/-- At parameter zero, expansion along the final vertex column identifies the affine
augmented determinant with the real cast of the integral block-vertex determinant. -/
theorem determinant_zero_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    (mapAt hp 0).determinant (toSimplex hp z) =
      ((Matrix.det (blockVertexMatrix hp z) : Int) : Real) := by
  classical
  unfold AffineVertexMap.determinant
  let A := (mapAt hp 0).augmentedMatrix (toSimplex hp z)
  have hminor :
      A.submatrix (Fin.last (p - 1)).succAbove (Fin.last (p - 1)).succAbove =
        (Int.castRingHom Real).mapMatrix (blockVertexMatrix hp z) := by
    ext r j
    have hnot : ¬ (stageCell z (stageIndex hp j.castSucc)).IsTop := by
      have h := toSimplex_isTop_iff_last hp z j.castSucc
      rw [toSimplex_apply] at h
      rw [h]
      have := j.isLt; simp only [Fin.val_castSucc]; omega
    simp [A, AffineVertexMap.augmentedMatrix, blockVertexMatrix,
      Fin.succAbove_last_apply, mapAt, hnot]
  rw [Matrix.det_succ_column A (Fin.last (p - 1))]
  rw [Finset.sum_eq_single (Fin.last (p - 1))]
  · rw [hminor, ← RingHom.map_det]
    have hsq : ((-1 : Real)) ^ (p - 1) * (-1) ^ (p - 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    simp [A, AffineVertexMap.augmentedMatrix, hsq]
  · intro i hi hne
    rcases Fin.eq_castSucc_or_eq_last i with ⟨q, rfl⟩ | rfl
    · have htop : (stageCell z (lastStage hp)).IsTop := by
        have h : (toSimplex hp z (Fin.last (p - 1))).IsTop :=
          (toSimplex_isTop_iff_last hp z (Fin.last (p - 1))).2 (by simp)
        simpa using h
      simp [A, AffineVertexMap.augmentedMatrix, mapAt, htop]
    · exact (hne rfl).elim
  · simp

theorem determinant_zero_ne_zero
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    (mapAt hp 0).determinant s ≠ 0 := by
  let z := simplexToCode hp s
  have hs : toSimplex hp z = s := toSimplex_simplexToCode hp s
  rw [← hs]
  have hdet : Matrix.det (blockVertexMatrix hp z) ≠ 0 := by
    rw [det_blockVertexMatrix hp z]
    rcases permSignInt_eq_one_or_neg_one z.bottom with hb | hb <;>
      rcases permSignInt_eq_one_or_neg_one z.removal with hr | hr <;>
      simp [coefficient, hb, hr]
  rw [determinant_zero_toSimplex hp z]
  exact_mod_cast hdet

theorem continuous_determinant_mapAt
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    Continuous fun epsilon : Real => (mapAt hp epsilon).determinant s := by
  unfold AffineVertexMap.determinant
  have hcont : Continuous fun epsilon : Real =>
      (mapAt hp epsilon).augmentedMatrix s := by
    refine continuous_matrix fun r i => ?_
    simp only [AffineVertexMap.augmentedMatrix]
    refine Fin.lastCases ?_ (fun q => ?_) r
    · simp only [Fin.lastCases_last]
      exact continuous_const
    · simp only [Fin.lastCases_castSucc, mapAt]
      by_cases htop : (s i).IsTop
      · simp only [if_pos htop]; fun_prop
      · simp only [if_neg htop]; fun_prop
  exact hcont.matrix_det

/-- A finite family of continuous nonzero values at zero has a common positive neighborhood on
which every sign is unchanged. -/
theorem exists_common_positive_sign_neighborhood
    {ι : Type*} [Fintype ι]
    (f : ι → Real → Real)
    (hf : ∀ i, Continuous (f i))
    (h0 : ∀ i, f i 0 ≠ 0) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ i, (0 < f i epsilon ↔ 0 < f i 0) ∧
        (f i epsilon < 0 ↔ f i 0 < 0) := by
  classical
  let U : Set Real := {x | ∀ i,
    (0 < f i x ↔ 0 < f i 0) ∧ (f i x < 0 ↔ f i 0 < 0)}
  have hUopen : IsOpen U := by
    unfold U
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    rcases lt_or_gt_of_ne (h0 i) with hneg | hpos
    · have hset :
          {x | (0 < f i x ↔ 0 < f i 0) ∧ (f i x < 0 ↔ f i 0 < 0)} =
            {x | f i x < 0} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨_, h2⟩; exact h2.2 hneg
        · intro hx
          exact ⟨⟨fun h => by linarith, fun h => by linarith⟩,
            ⟨fun _ => hneg, fun _ => hx⟩⟩
      rw [hset]
      exact isOpen_lt (hf i) continuous_const
    · have hset :
          {x | (0 < f i x ↔ 0 < f i 0) ∧ (f i x < 0 ↔ f i 0 < 0)} =
            {x | 0 < f i x} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, _⟩; exact h1.2 hpos
        · intro hx
          exact ⟨⟨fun _ => hpos, fun _ => hx⟩,
            ⟨fun h => by linarith, fun h => by linarith⟩⟩
      rw [hset]
      exact isOpen_lt continuous_const (hf i)
  have h0U : 0 ∈ U := by
    intro i
    constructor <;> rfl
  rcases Metric.isOpen_iff.mp hUopen 0 h0U with ⟨delta, hdelta, hball⟩
  refine ⟨delta / 2, half_pos hdelta, ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  simpa using (abs_lt.2 ⟨by linarith, by linarith⟩)

/-- A common positive perturbation scale preserving the signs of all reference determinants. -/
noncomputable def epsilon (hp : Nat.Prime p) : Real :=
  Classical.choose (exists_common_positive_sign_neighborhood
    (fun (s : Simplex p (p - 1)) (e : Real) => (mapAt hp e).determinant s)
    (continuous_determinant_mapAt hp)
    (determinant_zero_ne_zero hp))

theorem epsilon_pos (hp : Nat.Prime p) : 0 < epsilon hp :=
  (Classical.choose_spec (exists_common_positive_sign_neighborhood
    (fun (s : Simplex p (p - 1)) (e : Real) => (mapAt hp e).determinant s)
    (continuous_determinant_mapAt hp)
    (determinant_zero_ne_zero hp))).1

/-- Determinant signs are preserved by the chosen perturbation. -/
theorem determinant_sign_preserved
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    (0 < (mapAt hp (epsilon hp)).determinant s ↔
      0 < (mapAt hp 0).determinant s) ∧
    ((mapAt hp (epsilon hp)).determinant s < 0 ↔
      (mapAt hp 0).determinant s < 0) :=
  (Classical.choose_spec (exists_common_positive_sign_neighborhood
    (fun (s : Simplex p (p - 1)) (e : Real) => (mapAt hp e).determinant s)
    (continuous_determinant_mapAt hp)
    (determinant_zero_ne_zero hp))).2 s

/-- The chosen affine reference map is regular on every maximal simplex. -/
noncomputable def referenceMap
    (hp : Nat.Prime p) : AffineVertexMap p (p - 1) :=
  mapAt hp (epsilon hp)

theorem referenceMap_regular
    (hp : Nat.Prime p) : (referenceMap hp).IsRegular := by
  intro s
  have h0 := determinant_zero_ne_zero hp s
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · exact ne_of_lt ((determinant_sign_preserved hp s).2.2 hneg)
  · exact ne_of_gt ((determinant_sign_preserved hp s).1.2 hpos)

/-- A square real matrix with nonzero determinant has trivial `mulVec` kernel. -/
theorem eq_zero_of_mulVec_eq_zero_of_det_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Real) (hdet : Matrix.det A ≠ 0)
    {v : n → Real} (hmul : A *ᵥ v = 0) : v = 0 := by
  by_contra hv
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hmul⟩)

/-- On a regular affine simplex, barycentric coordinates of a zero are unique, even before
requiring positivity of every coordinate. -/
theorem zero_barycentric_unique
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    (w v : StandardSimplex (p - 1))
    (hw : ∀ r, (referenceMap hp).value s w r = 0)
    (hv : ∀ r, (referenceMap hp).value s v r = 0) :
    w = v := by
  classical
  let d : Fin (p - 1 + 1) → Real := fun i => w i - v i
  have hmul : (referenceMap hp).augmentedMatrix s *ᵥ d = 0 := by
    funext r
    refine Fin.lastCases ?_ (fun q => ?_) r
    · simp only [Matrix.mulVec, AffineVertexMap.augmentedMatrix, Fin.lastCases_last,
        dotProduct, one_mul, d, Finset.sum_sub_distrib, StandardSimplex.sum_eq_one,
        sub_self, Pi.zero_apply]
    · have hcast : ((referenceMap hp).augmentedMatrix s *ᵥ d) q.castSucc =
          (referenceMap hp).value s w q - (referenceMap hp).value s v q := by
        simp only [Matrix.mulVec, AffineVertexMap.augmentedMatrix, Fin.lastCases_castSucc,
          dotProduct, AffineVertexMap.value, d]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hcast, hw q, hv q]
      simp
  have hdet : Matrix.det ((referenceMap hp).augmentedMatrix s) ≠ 0 := by
    have hreg := referenceMap_regular hp s
    change Matrix.det ((referenceMap hp).augmentedMatrix s) ≠ 0 at hreg
    exact hreg
  have hd : d = 0 :=
    eq_zero_of_mulVec_eq_zero_of_det_ne_zero
      ((referenceMap hp).augmentedMatrix s) hdet hmul
  apply Subtype.ext
  funext i
  have hi := congr_fun hd i
  exact sub_eq_zero.mp (by simpa [d] using hi)

theorem perm_eq_one_of_strictMono
    {n : Nat} (sigma : Equiv.Perm (Fin n))
    (hmono : StrictMono sigma) : sigma = 1 := by
  let e : Fin n ≃o Fin n :=
    StrictMono.orderIsoOfSurjective sigma hmono sigma.surjective
  apply Equiv.ext
  intro i
  apply Fin.ext
  simpa [e] using Fin.coe_orderIso_apply e i

/-- Any barycentric zero of the perturbed reference map has positive coefficient at the final
top-cell vertex.  If that coefficient vanished, the invertible block-vertex matrix would force all
earlier coefficients to vanish as well, contradicting that barycentric coordinates sum to one. -/
theorem top_weight_pos_of_zero
    (hp : Nat.Prime p) (z : Code p) (w : StandardSimplex (p - 1))
    (hzero : ∀ r, (referenceMap hp).value (toSimplex hp z) w r = 0) :
    0 < w (Fin.last (p - 1)) := by
  classical
  by_contra hnot
  have hwlast : w (Fin.last (p - 1)) = 0 :=
    le_antisymm (le_of_not_gt hnot) (StandardSimplex.nonneg w _)
  let A : Matrix (Fin (p - 1)) (Fin (p - 1)) Real :=
    fun r j => (blockVertexMatrix hp z r j : Real)
  let v : Fin (p - 1) → Real := fun j => w j.castSucc
  have hnotTop : ∀ j : Fin (p - 1), ¬(toSimplex hp z j.castSucc).IsTop := by
    intro j hj
    have h := (toSimplex_isTop_iff_last hp z j.castSucc).1 hj
    simp only [Fin.val_castSucc] at h
    have := j.2; omega
  have hmul : A *ᵥ v = 0 := by
    funext r
    have hr := hzero r
    rw [AffineVertexMap.value, Fin.sum_univ_castSucc, hwlast] at hr
    simp only [zero_mul, add_zero] at hr
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← hr]
    apply Finset.sum_congr rfl
    intro j _
    have hvv : (referenceMap hp).vertexValue (toSimplex hp z j.castSucc) r
        = (blockDifference hp (toSimplex hp z j.castSucc) r : Real) := by
      simp only [referenceMap, mapAt]
      rw [if_neg (hnotTop j)]
    show A r j * v j = w j.castSucc * (referenceMap hp).vertexValue (toSimplex hp z j.castSucc) r
    rw [hvv]
    simp only [A, v, blockVertexMatrix]
    ring
  have hdetInt : Matrix.det (blockVertexMatrix hp z) ≠ 0 := by
    rw [det_blockVertexMatrix hp z]
    rcases permSignInt_eq_one_or_neg_one z.bottom with hb | hb <;>
      rcases permSignInt_eq_one_or_neg_one z.removal with hr | hr <;>
      simp [coefficient, hb, hr]
  have hdetCast : Matrix.det A =
      ((Matrix.det (blockVertexMatrix hp z) : Int) : Real) := by
    have hAeq : A = (Int.castRingHom Real).mapMatrix (blockVertexMatrix hp z) := rfl
    rw [hAeq, ← RingHom.map_det]
    rfl
  have hdet : Matrix.det A ≠ 0 := by
    rw [hdetCast]
    exact_mod_cast hdetInt
  have hv : v = 0 :=
    eq_zero_of_mulVec_eq_zero_of_det_ne_zero A hdet hmul
  have hsum : ∑ i : Fin (p - 1 + 1), w i = 0 := by
    rw [Fin.sum_univ_castSucc]
    have : ∀ j : Fin (p - 1), w j.castSucc = 0 := fun j => congr_fun hv j
    simp only [this, Finset.sum_const_zero, hwlast, add_zero]
  rw [StandardSimplex.sum_eq_one] at hsum
  norm_num at hsum

theorem strictOrder_eq_of_top_weight_pos
    (hp : Nat.Prime p) (z : Code p) (w : StandardSimplex (p - 1))
    (hwtop : 0 < w (Fin.last (p - 1)))
    (hzero : ∀ r, (referenceMap hp).value (toSimplex hp z) w r = 0)
    (label : Fin p) : z.bottom label = z.top label := by
  have hnotTopT : ∀ j : Fin (p - 1), ¬(toSimplex hp z j.castSucc).IsTop := by
    intro j htop
    have hj := (toSimplex_isTop_iff_last hp z j.castSucc).1 htop
    simp only [Fin.val_castSucc] at hj
    have := j.2; omega
  have htopLastT : (toSimplex hp z (Fin.last (p - 1))).IsTop :=
    (toSimplex_isTop_iff_last hp z (Fin.last (p - 1))).2 (by simp)
  have hliftNonTop : ∀ (j : Fin (p - 1)) (u : Fin p),
      liftedVertexValue p (epsilon hp) (toSimplex hp z j.castSucc) u
        = ((toSimplex hp z j.castSucc).blockIndex u : Real) := by
    intro j u
    simp only [liftedVertexValue, if_neg (hnotTopT j)]
  have hliftLast : ∀ (u : Fin p),
      liftedVertexValue p (epsilon hp) (toSimplex hp z (Fin.last (p - 1))) u
        = -(epsilon hp) * (triangular (z.top u).1 : Real) := by
    intro u
    simp only [liftedVertexValue, if_pos htopLastT]
    have hrank : ((toSimplex hp z (Fin.last (p - 1))).rank u) = z.top u := by
      simp only [toSimplex_apply, stageCell, stageIndex_last, stageRank_last hp]
    rw [hrank]
  have hadj : ∀ k : Fin (p - 1),
      z.top (z.bottom.symm (stageIndex hp k.castSucc)) <
        z.top (z.bottom.symm (stageIndex hp k.succ)) := by
    intro k
    set x := z.bottom.symm (stageIndex hp k.castSucc) with hxdef
    set y := z.bottom.symm (stageIndex hp k.succ) with hydef
    have hbottom_xy : (z.bottom x).1 ≤ (z.bottom y).1 := by
      simp only [hxdef, hydef, Equiv.apply_symm_apply, stageIndex_val,
        Fin.val_castSucc, Fin.val_succ]
      omega
    have hnonnegative : 0 ≤ ∑ j : Fin (p - 1),
        w j.castSucc * (((toSimplex hp z j.castSucc).blockIndex y : Real) -
          (toSimplex hp z j.castSucc).blockIndex x) := by
      apply Finset.sum_nonneg
      intro j hj
      apply mul_nonneg (StandardSimplex.nonneg w _)
      apply sub_nonneg.mpr
      have hblocks :
          (toSimplex hp z j.castSucc).blockIndex x ≤
            (toSimplex hp z j.castSucc).blockIndex y := by
        simpa only [toSimplex_apply, stageCell_blockIndex] using
          stageBlock_mono z (stageIndex hp j.castSucc) hbottom_xy
      exact_mod_cast hblocks
    have hraw := weighted_lifted_difference_eq_zero hp (epsilon hp)
      (toSimplex hp z) w hzero y x
    rw [Fin.sum_univ_castSucc] at hraw
    have hraw2 :
        (∑ j : Fin (p - 1),
          w j.castSucc * (((toSimplex hp z j.castSucc).blockIndex y : Real) -
            (toSimplex hp z j.castSucc).blockIndex x)) +
          w (Fin.last (p - 1)) *
            (-(epsilon hp) * (triangular (z.top y).1 : Real) -
              -(epsilon hp) * (triangular (z.top x).1 : Real)) = 0 := by
      have hcongr :
          (∑ j : Fin (p - 1),
            w j.castSucc * (((toSimplex hp z j.castSucc).blockIndex y : Real) -
              (toSimplex hp z j.castSucc).blockIndex x)) +
            w (Fin.last (p - 1)) *
              (-(epsilon hp) * (triangular (z.top y).1 : Real) -
                -(epsilon hp) * (triangular (z.top x).1 : Real)) =
          (∑ i : Fin (p - 1),
            w i.castSucc *
              (liftedVertexValue p (epsilon hp) (toSimplex hp z i.castSucc) y -
                liftedVertexValue p (epsilon hp) (toSimplex hp z i.castSucc) x)) +
            w (Fin.last (p - 1)) *
              (liftedVertexValue p (epsilon hp) (toSimplex hp z (Fin.last (p - 1))) y -
                liftedVertexValue p (epsilon hp) (toSimplex hp z (Fin.last (p - 1))) x) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          rw [hliftNonTop j y, hliftNonTop j x]
        · rw [hliftLast y, hliftLast x]
      rw [hcongr]
      exact hraw
    have hsum_eq :
        (∑ j : Fin (p - 1),
          w j.castSucc * (((toSimplex hp z j.castSucc).blockIndex y : Real) -
            (toSimplex hp z j.castSucc).blockIndex x)) =
          epsilon hp * w (Fin.last (p - 1)) *
            ((triangular (z.top y).1 : Real) - triangular (z.top x).1) := by
      linear_combination hraw2
    have hscale : 0 < epsilon hp * w (Fin.last (p - 1)) :=
      mul_pos (epsilon_pos hp) hwtop
    have hle : (triangular (z.top x).1 : Real) ≤ triangular (z.top y).1 := by
      nlinarith [hnonnegative, hsum_eq, hscale]
    have hxy : x ≠ y := by
      intro hxy
      have hcontra := congrArg z.bottom hxy
      simp only [hxdef, hydef, Equiv.apply_symm_apply] at hcontra
      have hval : (stageIndex hp k.castSucc).1 = (stageIndex hp k.succ).1 := by
        rw [hcontra]
      simp only [stageIndex_val, Fin.val_castSucc, Fin.val_succ] at hval
      omega
    have hne : (z.top x).1 ≠ (z.top y).1 := fun h =>
      hxy (z.top.injective (Fin.ext h))
    have hlt : (triangular (z.top x).1 : Real) < triangular (z.top y).1 :=
      lt_of_le_of_ne hle (fun h => hne (triangular_injective (by exact_mod_cast h)))
    have htriNat : triangular (z.top x).1 < triangular (z.top y).1 := by
      exact_mod_cast hlt
    apply Fin.lt_def.mpr
    by_contra hnot
    have hyx : (z.top y).1 ≤ (z.top x).1 := Nat.le_of_not_gt hnot
    have htriLe := triangular_strictMono.monotone hyx
    omega
  let e : Fin (p - 1 + 1) ≃o Fin p := Fin.castOrderIso (FoxNeuwirthChain.maximalIndex_eq hp)
  let tau : Equiv.Perm (Fin p) := z.bottom.symm.trans z.top
  have hcomp : StrictMono (tau ∘ e) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    have hk := hadj k
    have he1 : e k.castSucc = stageIndex hp k.castSucc := by
      apply Fin.ext; simp [e, Fin.castOrderIso, stageIndex_val]
    have he2 : e k.succ = stageIndex hp k.succ := by
      apply Fin.ext; simp [e, Fin.castOrderIso, stageIndex_val]
    simp only [Function.comp, he1, he2]
    show tau (stageIndex hp k.castSucc) < tau (stageIndex hp k.succ)
    simpa only [tau, Equiv.coe_trans, Function.comp] using hk
  have htau : StrictMono tau := by
    intro a b hab
    have := hcomp (a := e.symm a) (b := e.symm b) (e.symm.strictMono hab)
    simpa only [Function.comp, Equiv.apply_symm_apply, OrderIso.apply_symm_apply] using this
  have htauone : tau = 1 := perm_eq_one_of_strictMono tau htau
  have hperm : z.bottom = z.top := by
    apply Equiv.ext
    intro x
    have hc := congrArg (fun ee : Equiv.Perm (Fin p) => ee (z.bottom x)) htauone
    have hc2 : z.top x = z.bottom x := by simpa [tau] using hc
    exact hc2.symm
  exact congrArg (fun ee : Equiv.Perm (Fin p) => ee label) hperm

theorem strictOrder_eq_of_positive_blockCombination
    (hp : Nat.Prime p) (z : Code p) (w : StandardSimplex (p - 1))
    (hwint : StandardSimplex.IsInterior w)
    (hzero : ∀ r, (referenceMap hp).value (toSimplex hp z) w r = 0)
    (label : Fin p) : z.bottom label = z.top label :=
  strictOrder_eq_of_top_weight_pos hp z w (hwint _) hzero label

/-- Once the bottom and top orders agree, positivity of the final top weight makes the prefix
sums strictly increasing, forcing the bar-removal schedule to be the identity. -/
theorem removal_eq_identity_of_top_weight_pos
    (hp : Nat.Prime p) (z : Code p) (w : StandardSimplex (p - 1))
    (hwtop : 0 < w (Fin.last (p - 1)))
    (hzero : ∀ r, (referenceMap hp).value (toSimplex hp z) w r = 0)
    (horder : z.bottom = z.top) (k : Fin (p - 1)) : z.removal k = k := by
  have hprefix : ∀ r : Fin (p - 1),
      (∑ j : Fin (p - 1),
        if j ≤ z.removal.symm r then w j.castSucc else 0) =
        epsilon hp * w (Fin.last (p - 1)) * (r.1 + 1) := by
    intro r
    let x := z.bottom.symm (stageIndex hp r.castSucc)
    let y := z.bottom.symm (stageIndex hp r.succ)
    have hnotTop : ∀ j : Fin (p - 1),
        ¬(toSimplex hp z j.castSucc).IsTop := by
      intro j htop
      have hj := (toSimplex_isTop_iff_last hp z j.castSucc).1 htop
      simp only [Fin.val_castSucc] at hj
      have := j.isLt
      omega
    have htopLast : (toSimplex hp z (Fin.last (p - 1))).IsTop :=
      (toSimplex_isTop_iff_last hp z (Fin.last (p - 1))).2 (by simp)
    have hnonTopDiff (j : Fin (p - 1)) :
        liftedVertexValue p (epsilon hp) (toSimplex hp z j.castSucc) y -
            liftedVertexValue p (epsilon hp) (toSimplex hp z j.castSucc) x =
          if j ≤ z.removal.symm r then 1 else 0 := by
      have hstage := stageBlock_adjacent_sub hp z (stageIndex hp j.castSucc) r
      simp only [stageIndex_val, Fin.val_castSucc] at hstage
      simp only [liftedVertexValue]
      rw [if_neg (hnotTop j), if_neg (hnotTop j)]
      simp only [toSimplex_apply, stageCell_blockIndex, x, y, Fin.le_def]
      exact_mod_cast hstage
    have htopDiff :
        liftedVertexValue p (epsilon hp)
              (toSimplex hp z (Fin.last (p - 1))) y -
            liftedVertexValue p (epsilon hp)
              (toSimplex hp z (Fin.last (p - 1))) x =
          -(epsilon hp) * (r.1 + 1) := by
      simp only [liftedVertexValue]
      rw [if_pos htopLast, if_pos htopLast]
      simp only [toSimplex_apply, stageIndex_last, stageCell, stageRank_last hp, x, y,
        horder, Equiv.apply_symm_apply, stageIndex_succ_val, stageIndex_castSucc_val]
      have htri : (triangular (r.1 + 1) : ℝ) - triangular r.1 = (r.1 : ℝ) + 1 := by
        exact_mod_cast triangular_succ_sub r.1
      linear_combination -(epsilon hp) * htri
    have hraw := weighted_lifted_difference_eq_zero hp (epsilon hp)
      (toSimplex hp z) w hzero y x
    rw [Fin.sum_univ_castSucc] at hraw
    have hcongr :
        (∑ j : Fin (p - 1),
              w j.castSucc *
                (liftedVertexValue p (epsilon hp) (toSimplex hp z j.castSucc) y -
                  liftedVertexValue p (epsilon hp) (toSimplex hp z j.castSucc) x)) +
            w (Fin.last (p - 1)) *
              (liftedVertexValue p (epsilon hp)
                    (toSimplex hp z (Fin.last (p - 1))) y -
                liftedVertexValue p (epsilon hp)
                    (toSimplex hp z (Fin.last (p - 1))) x) =
          (∑ j : Fin (p - 1),
              if j ≤ z.removal.symm r then w j.castSucc else 0) -
            epsilon hp * w (Fin.last (p - 1)) * (r.1 + 1) := by
      rw [htopDiff]
      rw [show (∑ j : Fin (p - 1), w j.castSucc *
              (liftedVertexValue p (epsilon hp) (toSimplex hp z j.castSucc) y -
                liftedVertexValue p (epsilon hp) (toSimplex hp z j.castSucc) x))
            = ∑ j : Fin (p - 1), if j ≤ z.removal.symm r then w j.castSucc else 0 from by
          apply Finset.sum_congr rfl
          intro j _
          rw [hnonTopDiff j]
          split_ifs <;> ring]
      ring
    rw [hcongr] at hraw
    nlinarith
  have hstrict : StrictMono z.removal.symm := by
    intro a b hab
    by_contra hnot
    have hleFin : z.removal.symm b ≤ z.removal.symm a :=
      le_of_not_gt hnot
    have hsumle :
        (∑ j : Fin (p - 1),
          if j ≤ z.removal.symm b then w j.castSucc else 0) ≤
        (∑ j : Fin (p - 1),
          if j ≤ z.removal.symm a then w j.castSucc else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hjb hja
      · exact le_rfl
      · exact False.elim (hja (le_trans hjb hleFin))
      · exact StandardSimplex.nonneg w j.castSucc
      · exact le_rfl
    rw [hprefix a, hprefix b] at hsumle
    have heps : 0 < epsilon hp * w (Fin.last (p - 1)) :=
      mul_pos (epsilon_pos hp) hwtop
    have hab' : (a.1 : ℝ) < (b.1 : ℝ) := by
      have : a.1 < b.1 := hab
      exact_mod_cast this
    nlinarith [hsumle, heps, hab', mul_pos heps (sub_pos.mpr hab')]
  have hone : z.removal.symm = 1 :=
    perm_eq_one_of_strictMono z.removal.symm hstrict
  have := congrArg (fun e : Equiv.Perm (Fin (p - 1)) => e k) hone
  have hinv : z.removal.symm k = k := by simpa using this
  have hforward := congrArg z.removal hinv
  simpa using hforward.symm

theorem removal_eq_identity_of_triangular_gaps
    (hp : Nat.Prime p) (z : Code p) (w : StandardSimplex (p - 1))
    (hwint : StandardSimplex.IsInterior w)
    (hzero : ∀ r, (referenceMap hp).value (toSimplex hp z) w r = 0)
    (horder : z.bottom = z.top) (k : Fin (p - 1)) : z.removal k = k :=
  removal_eq_identity_of_top_weight_pos hp z w (hwint _) hzero horder k

/-- Positive barycentric solutions of the perturbed reference equation are exactly the selected
maximal flags. -/
theorem hasInteriorZero_toSimplex_iff
    (hp : Nat.Prime p) (z : Code p) :
    (referenceMap hp).HasInteriorZero (toSimplex hp z) ↔
      z.bottom = z.top ∧ z.removal = 1 := by
  classical
  constructor
  · rintro ⟨w, hwint, hzero⟩
    have horder : z.bottom = z.top := by
      apply Equiv.ext
      intro label
      -- The positive bottom-vertex coefficient makes the block-coordinate combination strictly
      -- increasing in `bottom` order.  Equality with the triangular top direction forces the
      -- same strict order as `top`.
      exact strictOrder_eq_of_positive_blockCombination hp z w hwint hzero label
    have hremoval : z.removal = 1 := by
      apply Equiv.ext
      intro k
      -- Adjacent differences give the strictly increasing partial sums
      -- `sum_{j ≤ removal⁻¹(k)} w_j = epsilon * w_top * (k+1)`.
      exact removal_eq_identity_of_triangular_gaps hp z w hwint hzero horder k
    exact ⟨horder, hremoval⟩
  · rintro ⟨hbottom, hremoval⟩
    let sigma : Equiv.Perm (Fin p) := z.top
    have hz : z = selectedCode sigma := by
      apply Code.ext
      · simpa [sigma, selectedCode] using hbottom
      · simpa [selectedCode] using hremoval
      · simp [sigma, selectedCode]
    rw [hz]
    let denom : Real := 1 + (p - 1 : Real) * epsilon hp
    have hple : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have hdenom : 0 < denom := by
      have heps := epsilon_pos hp
      have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      dsimp only [denom]
      nlinarith
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    have hjnot : ∀ j : Fin (p - 1), j.castSucc.1 ≠ p - 1 := by
      intro j; have := j.isLt; simp only [Fin.val_castSucc]; omega
    let w : StandardSimplex (p - 1) :=
      ⟨fun i => if i.1 = p - 1 then 1 / denom else epsilon hp / denom, by
        refine ⟨?_, ?_⟩
        · intro i
          dsimp only
          split_ifs
          · exact div_nonneg (by norm_num) hdenom.le
          · exact div_nonneg (epsilon_pos hp).le hdenom.le
        · rw [Fin.sum_univ_castSucc]
          simp only [hjnot, Fin.val_last, if_true, if_false, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hcast]
          field_simp
          ring⟩
    refine ⟨w, ?_, ?_⟩
    · intro i
      show 0 < if i.1 = p - 1 then 1 / denom else epsilon hp / denom
      split_ifs
      · exact div_pos (by norm_num) hdenom
      · exact div_pos (epsilon_pos hp) hdenom
    · intro r
      have hnotTop : ∀ j : Fin (p - 1),
          ¬(selectedSimplex hp sigma j.castSucc).IsTop := by
        intro j htop
        have hj :=
          (toSimplex_isTop_iff_last hp (selectedCode sigma) j.castSucc).1 htop
        simp only [Fin.val_castSucc] at hj
        have := j.isLt; omega
      have htopLast :
          (selectedSimplex hp sigma (Fin.last (p - 1))).IsTop :=
        (toSimplex_isTop_iff_last hp (selectedCode sigma)
          (Fin.last (p - 1))).2 (by simp)
      have hsumReal :
          (∑ j : Fin (p - 1),
            (blockDifference hp (selectedSimplex hp sigma j.castSucc) r : Real)) =
            (topDirection hp
              (selectedSimplex hp sigma (Fin.last (p - 1))) r : Real) := by
        exact_mod_cast sum_blockDifference_selected hp sigma r
      calc
        (referenceMap hp).value (selectedSimplex hp sigma) w r =
            (epsilon hp / denom) *
                (∑ j : Fin (p - 1),
                  (blockDifference hp
                    (selectedSimplex hp sigma j.castSucc) r : Real)) +
              (1 / denom) *
                (-epsilon hp *
                  (topDirection hp
                    (selectedSimplex hp sigma (Fin.last (p - 1))) r : Real)) := by
              rw [AffineVertexMap.value, Fin.sum_univ_castSucc]
              have hxne : ∀ x : Fin (p - 1), x.1 ≠ p - 1 := fun x => by
                have := x.isLt; omega
              simp [w, referenceMap, mapAt, hnotTop, htopLast, hjnot, hxne, Fin.val_last,
                Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
        _ = (epsilon hp / denom) *
                (topDirection hp
                  (selectedSimplex hp sigma (Fin.last (p - 1))) r : Real) +
              (1 / denom) *
                (-epsilon hp *
                  (topDirection hp
                    (selectedSimplex hp sigma (Fin.last (p - 1))) r : Real)) := by
              rw [hsumReal]
        _ = 0 := by ring

theorem zero_isInterior_toSimplex
    (hp : Nat.Prime p) (z : Code p) (w : StandardSimplex (p - 1))
    (hzero : ∀ r, (referenceMap hp).value (toSimplex hp z) w r = 0) :
    StandardSimplex.IsInterior w := by
  have hwtop := top_weight_pos_of_zero hp z w hzero
  have horder : z.bottom = z.top := by
    apply Equiv.ext
    intro label
    exact strictOrder_eq_of_top_weight_pos hp z w hwtop hzero label
  have hremoval : z.removal = 1 := by
    apply Equiv.ext
    intro k
    exact removal_eq_identity_of_top_weight_pos hp z w hwtop hzero horder k
  obtain ⟨v, hvint, hvzero⟩ :=
    (hasInteriorZero_toSimplex_iff hp z).2 ⟨horder, hremoval⟩
  have hwv := zero_barycentric_unique hp (toSimplex hp z) w v hzero hvzero
  rw [hwv]
  exact hvint

/-- Every barycentric zero on an arbitrary maximal simplex is interior. -/
theorem zero_isInterior
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    (w : StandardSimplex (p - 1))
    (hzero : ∀ r, (referenceMap hp).value s w r = 0) :
    StandardSimplex.IsInterior w := by
  exact zero_isInterior_toSimplex hp (simplexToCode hp s) w
    (by rw [toSimplex_simplexToCode hp s]; exact hzero)

/-- Relative-interior zero characterization for an arbitrary maximal simplex. -/
theorem hasInteriorZero_iff_selected
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    (referenceMap hp).HasInteriorZero s ↔ IsSelected hp s := by
  have hs : toSimplex hp (simplexToCode hp s) = s := toSimplex_simplexToCode hp s
  exact hs ▸ (hasInteriorZero_toSimplex_iff hp (simplexToCode hp s)).trans
    (isSelected_toSimplex_iff hp (simplexToCode hp s)).symm

/-- Determinant sign at zero in code coordinates. -/
theorem determinantIndex_zero_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    AffineVertexMap.determinantIndex (p := p)
      ((mapAt hp 0).determinant (toSimplex hp z)) =
      ((((-1 : Int) ^ (p - 1) * coefficient z : Int) : ZMod p)) := by
  rw [determinant_zero_toSimplex hp z, det_blockVertexMatrix hp z]
  have hv : (-1 : Int) ^ (p - 1) * coefficient z = 1 ∨
      (-1 : Int) ^ (p - 1) * coefficient z = -1 := by
    have hpow : (-1 : Int) ^ (p - 1) = 1 ∨ (-1 : Int) ^ (p - 1) = -1 := by
      rcases Nat.even_or_odd (p - 1) with he | ho
      · exact Or.inl he.neg_one_pow
      · exact Or.inr ho.neg_one_pow
    have hcoeff : coefficient z = 1 ∨ coefficient z = -1 := by
      rcases permSignInt_eq_one_or_neg_one z.bottom with hb | hb <;>
        rcases permSignInt_eq_one_or_neg_one z.removal with hr | hr <;>
        simp [coefficient, hb, hr]
    rcases hpow with hp1 | hp1 <;> rcases hcoeff with hc1 | hc1 <;>
      simp [hp1, hc1]
  rcases hv with hvv | hvv <;> rw [hvv] <;>
    norm_num [AffineVertexMap.determinantIndex]

theorem localZeroIndex_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    (referenceMap hp).localZeroIndex (toSimplex hp z) =
      if z.bottom = z.top ∧ z.removal = 1 then
        (coefficient z : ZMod p)
      else 0 := by
  classical
  unfold AffineVertexMap.localZeroIndex
  rw [hasInteriorZero_toSimplex_iff hp z]
  split_ifs with hsel
  · have hsign := determinant_sign_preserved hp (toSimplex hp z)
    have hindex :
        AffineVertexMap.determinantIndex (p := p)
            ((referenceMap hp).determinant (toSimplex hp z)) =
          AffineVertexMap.determinantIndex (p := p)
            ((mapAt hp 0).determinant (toSimplex hp z)) := by
      unfold AffineVertexMap.determinantIndex referenceMap
      simp only [hsign.1, hsign.2]
    have hparity : (((-1 : Int) ^ (p - 1) : Int) : ZMod p) = 1 := by
      by_cases h2 : p = 2
      · subst p
        decide
      · have heven : Even (p - 1) := by
          have hodd : Odd p := hp.odd_of_ne_two h2
          rcases hodd with ⟨m, rfl⟩
          exact ⟨m, by omega⟩
        simpa [Even.neg_one_pow heven]
    calc
      AffineVertexMap.determinantIndex (p := p)
          ((referenceMap hp).determinant (toSimplex hp z)) =
          AffineVertexMap.determinantIndex (p := p)
            ((mapAt hp 0).determinant (toSimplex hp z)) := hindex
      _ = ((((-1 : Int) ^ (p - 1) * coefficient z : Int) : ZMod p)) :=
        determinantIndex_zero_toSimplex hp z
      _ = (coefficient z : ZMod p) := by
        rw [Int.cast_mul, hparity, one_mul]
  · simp [hsel]

/-- The covering top cell has dimension `p - 1`. -/
theorem coveringTopCell_eq (hp : Nat.Prime p) :
    (PrimeOrbitCycle.coveringCycle hp).TopCell = Simplex p (p - 1) := by
  show Simplex p (p - 2 + 1) = Simplex p (p - 1)
  have := hp.two_le
  congr 1
  omega

/-- Canonical top-orbit representative, cast to the dimension `p - 1` used by the reference map. -/
noncomputable def topRepr
    (hp : Nat.Prime p) (q : PrimeOrbitCycle.TopOrbit hp) : Simplex p (p - 1) :=
  (coveringTopCell_eq hp) ▸ PrimeOrbitCycle.topRepresentative hp q

/-- The selected maximal flag associated with a top cell's label ordering. -/
noncomputable def selectedFlagOfTopCell
    (hp : Nat.Prime p) (c : BarredPermutation.TopCell p) : Simplex p (p - 1) :=
  selectedSimplex hp c.1.rank

/-- Selected flags are equivariant. -/
theorem selectedFlagOfTopCell_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (c : BarredPermutation.TopCell p) :
    selectedFlagOfTopCell hp (g • c) = g • selectedFlagOfTopCell hp c := by
  change selectedSimplex hp (g • c).1.rank =
    g • selectedSimplex hp c.1.rank
  have hrank : (g • c).1.rank =
      (PrimeSymmetry.toPerm p g).symm.trans c.1.rank := rfl
  rw [hrank]
  exact (selectedSimplex_smul hp g c.1.rank).symm

/-- Quotient of the selected reference flags. -/
abbrev SelectedOrbit (p : Nat) :=
  MulAction.orbitRel.Quotient (PrimeSymmetry p) (BarredPermutation.TopCell p)

noncomputable instance selectedOrbitFintype (p : Nat) :
    Fintype (SelectedOrbit p) := Fintype.ofFinite _

/-- Relabelling commutes with a dimension recast of order-complex simplices. -/
theorem smul_castDim (p : Nat) (g : PrimeSymmetry p)
    {d d' : ℕ} (hd : d = d') (s : Simplex p d) :
    g • (congrArg (Simplex p) hd ▸ s) = congrArg (Simplex p) hd ▸ (g • s) := by
  subst hd; rfl

/-- Selected top-cell orbits and selected top-simplex orbits are canonically equivalent. -/
noncomputable def selectedOrbitEquivTopSupport
    (hp : Nat.Prime p) :
    SelectedOrbit p ≃
      {q : PrimeOrbitCycle.TopOrbit hp //
        IsSelected hp (topRepr hp q)} := by
  classical
  let toTop : SelectedOrbit p → PrimeOrbitCycle.TopOrbit hp :=
    Quotient.map
      (fun c : BarredPermutation.TopCell p =>
        (coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp c)
      (by
        intro a b hab
        rcases hab with ⟨g, rfl⟩
        refine ⟨g, ?_⟩
        simp only [selectedFlagOfTopCell_smul]
        exact smul_castDim p g (by have := hp.two_le; omega)
          (selectedFlagOfTopCell hp b))
  have toTop_selected (q : SelectedOrbit p) :
      IsSelected hp (topRepr hp (toTop q)) := by
    obtain ⟨c, rfl⟩ := Quotient.exists_rep q
    have hclass :
        (Quotient.mk'' ((coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp c) :
            PrimeOrbitCycle.TopOrbit hp) =
          Quotient.mk'' (Quotient.out (toTop (Quotient.mk'' c))) := by
      rw [Quotient.out_eq']
      rfl
    rcases Quotient.exact hclass with ⟨g, hg⟩
    -- `orbitRel a b` means that a group element sends `b` to `a`.  Thus `hg` sends
    -- the chosen quotient representative to the selected flag, and its inverse sends the
    -- selected flag back to the representative.
    have hselected : IsSelected hp (g⁻¹ • selectedFlagOfTopCell hp c) := by
      rcases c with ⟨c, hc⟩
      refine ⟨((PrimeSymmetry.toPerm p g⁻¹).symm.trans c.rank), ?_⟩
      simpa [selectedFlagOfTopCell, selectedSimplex_smul]
    have hd : p - 2 + 1 = p - 1 := by have := hp.two_le; omega
    have hgcast :
        g • topRepr hp (toTop (Quotient.mk'' c)) =
          selectedFlagOfTopCell hp c := by
      calc
        g • topRepr hp (toTop (Quotient.mk'' c)) =
            (coveringTopCell_eq hp) ▸
              (g • Quotient.out (toTop (Quotient.mk'' c))) := by
          change g • ((coveringTopCell_eq hp) ▸
              Quotient.out (toTop (Quotient.mk'' c))) =
            (coveringTopCell_eq hp) ▸
              (g • Quotient.out (toTop (Quotient.mk'' c)))
          have hproof : congrArg (Simplex p) hd = coveringTopCell_eq hp :=
            Subsingleton.elim _ _
          rw [← hproof]
          exact smul_castDim p g hd (Quotient.out (toTop (Quotient.mk'' c)))
        _ = (coveringTopCell_eq hp) ▸
              ((coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp c) := by
          exact congrArg
            (fun s : (PrimeOrbitCycle.coveringCycle hp).TopCell =>
              (coveringTopCell_eq hp) ▸ s) hg
        _ = selectedFlagOfTopCell hp c := by
          exact (Equiv.cast (coveringTopCell_eq hp).symm).symm_apply_apply
            (selectedFlagOfTopCell hp c)
    have hcast :
        g⁻¹ • selectedFlagOfTopCell hp c =
          topRepr hp (toTop (Quotient.mk'' c)) := by
      have h := congrArg (fun s : Simplex p (p - 1) => g⁻¹ • s) hgcast
      simpa using h.symm
    simpa [hcast] using hselected
  refine Equiv.ofBijective
    (fun q => ⟨toTop q, toTop_selected q⟩) ?_
  constructor
  · intro qa qb hab
    obtain ⟨a, rfl⟩ := Quotient.exists_rep qa
    obtain ⟨b, rfl⟩ := Quotient.exists_rep qb
    have hquot :
        (Quotient.mk'' ((coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp a) :
          PrimeOrbitCycle.TopOrbit hp) =
        Quotient.mk'' ((coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp b) := by
      exact congrArg Subtype.val hab
    rcases Quotient.exact hquot with ⟨g, hg⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    have hd' : p - 1 = p - 2 + 1 := by have := hp.two_le; omega
    have hsmul :
        g • ((coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp b) =
          (coveringTopCell_eq hp).symm ▸
            (g • selectedFlagOfTopCell hp b) := by
      change g • (congrArg (Simplex p) hd' ▸ selectedFlagOfTopCell hp b) =
        congrArg (Simplex p) hd' ▸ (g • selectedFlagOfTopCell hp b)
      exact smul_castDim p g hd' (selectedFlagOfTopCell hp b)
    have hback :
        (coveringTopCell_eq hp).symm ▸
            (g • selectedFlagOfTopCell hp b) =
          (coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp a :=
      hsmul.symm.trans hg
    have hflags :
        g • selectedFlagOfTopCell hp b = selectedFlagOfTopCell hp a := by
      exact (Equiv.cast (coveringTopCell_eq hp).symm).injective hback
    apply Subtype.ext
    have hterminal (c : BarredPermutation.TopCell p) :
        selectedFlagOfTopCell hp c (Fin.last (p - 1)) = c.1 := by
      change stageCell (selectedCode c.1.rank)
        (stageIndex hp (Fin.last (p - 1))) = c.1
      rw [stageIndex_last, stageCell_last]
      apply BarredPermutation.ext
      · simp
      · simpa [BarredPermutation.IsTop] using c.2.symm
    have htop := congrArg
      (fun s : Simplex p (p - 1) => s (Fin.last (p - 1))) hflags
    change g • selectedFlagOfTopCell hp b (Fin.last (p - 1)) =
      selectedFlagOfTopCell hp a (Fin.last (p - 1)) at htop
    rw [hterminal b, hterminal a] at htop
    have hrank := congrArg BarredPermutation.rank htop
    apply BarredPermutation.ext
    · exact hrank
    · exact b.2.trans a.2.symm
  · rintro ⟨q, hq⟩
    rcases hq with ⟨sigma, hsigma⟩
    let c : BarredPermutation.TopCell p := BarredPermutation.TopCell.ofPerm sigma
    refine ⟨Quotient.mk'' c, ?_⟩
    apply Subtype.ext
    change Quotient.mk''
      ((coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp c) = q
    rw [← Quotient.out_eq' q]
    apply Quotient.sound
    have hrepr :
        (coveringTopCell_eq hp) ▸ Quotient.out q = selectedFlagOfTopCell hp c := by
      simpa [topRepr, PrimeOrbitCycle.topRepresentative,
        FiniteIncidenceCycle.topRepresentative, c, selectedFlagOfTopCell] using hsigma
    have hback :
        Quotient.out q =
          (coveringTopCell_eq hp).symm ▸ selectedFlagOfTopCell hp c := by
      apply eq_of_heq
      exact (((cast_heq (coveringTopCell_eq hp) (Quotient.out q)).symm.trans
        (heq_of_eq hrepr)).trans
        (cast_heq (coveringTopCell_eq hp).symm (selectedFlagOfTopCell hp c)).symm)
    exact ⟨1, by simp only [one_smul]; exact hback⟩

theorem card_selectedOrbit
    (p : Nat) :
    Fintype.card (SelectedOrbit p) = FoxNeuwirth.referenceOrbitMultiplicity p := by
  classical
  let X := BarredPermutation.TopCell p
  -- Relabelling makes the top cells a torsor for the full permutation group.
  letI fullPermAction : MulAction (Equiv.Perm (Fin p)) X := {
    smul sigma c :=
      ⟨c.1.relabel sigma,
        (BarredPermutation.isTop_relabel sigma c.1).2 c.2⟩
    one_smul c := by
      apply Subtype.ext
      exact BarredPermutation.relabel_one c.1
    mul_smul sigma tau c := by
      apply Subtype.ext
      apply BarredPermutation.ext
      · ext i
        rfl
      · rfl }
  let x0 : X := BarredPermutation.TopCell.evenRepresentative
  letI : MulAction.IsPretransitive (Equiv.Perm (Fin p)) X := by
    constructor
    intro a b
    refine ⟨a.1.rank.trans b.1.rank.symm, ?_⟩
    change (⟨a.1.relabel (a.1.rank.trans b.1.rank.symm),
      (BarredPermutation.isTop_relabel (a.1.rank.trans b.1.rank.symm) a.1).2 a.2⟩ : X) = b
    apply Subtype.ext
    apply BarredPermutation.ext
    · ext i
      simp [BarredPermutation.relabel]
    · exact a.2.trans b.2.symm
  letI : IsCancelSMul (Equiv.Perm (Fin p)) X := {
    toIsLeftCancelSMul := inferInstance
    right_cancel' sigma tau c h := by
      have hrank := congrArg (fun d : X => d.1.rank) h
      change sigma.symm.trans c.1.rank = tau.symm.trans c.1.rank at hrank
      have hinv : sigma.symm = tau.symm := by
        apply Equiv.ext
        intro i
        apply c.1.rank.injective
        exact congrArg (fun e : Equiv.Perm (Fin p) => e i) hrank
      have h := congrArg (fun e : Equiv.Perm (Fin p) => e.symm) hinv
      simpa using h }
  let e : SelectedOrbit p ≃
      (Equiv.Perm (Fin p) ⧸ primeSymmetrySubgroup p) :=
    MulAction.equivSubgroupOrbitsQuotientGroup x0
      (primeSymmetrySubgroup p)
  change Fintype.card (SelectedOrbit p) =
    Nat.card ((Equiv.Perm (Fin p)) ⧸ primeSymmetrySubgroup p)
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr e

/-- The local zero index of the reference map on each selected orbit representative. -/
noncomputable def referenceIndex
    (hp : Nat.Prime p) : PrimeOrbitCycle.TopOrbit hp → ZMod p :=
  fun q => (referenceMap hp).localZeroIndex (topRepr hp q)

/-- The quotient-cycle coefficient at a top orbit equals the code coefficient of the canonical
representative flag, reduced to `ZMod p`. -/
theorem orbitCycle_coefficient_eq
    (hp : Nat.Prime p) (q : PrimeOrbitCycle.TopOrbit hp) :
    (PrimeOrbitCycle.orbitCycle hp).coefficient q =
      (coefficient (simplexToCode hp (topRepr hp q)) : ZMod p) := by
  classical
  have hdim : p - 1 = (p - 2) + 1 := by have := hp.two_le; omega
  have h1 : (PrimeOrbitCycle.orbitCycle hp).coefficient q
      = (hdim ▸ TopFlagSubdivision.chain)
          (PrimeOrbitCycle.topRepresentative hp q) := rfl
  have hcast : Equiv.cast (congrArg (Simplex p) hdim) (topRepr hp q)
      = PrimeOrbitCycle.topRepresentative hp q := by
    apply eq_of_heq
    exact (cast_heq (congrArg (Simplex p) hdim) (topRepr hp q)).trans
      (cast_heq (coveringTopCell_eq hp)
        (PrimeOrbitCycle.topRepresentative hp q))
  rw [h1, ← hcast, transport_chain_apply hdim TopFlagSubdivision.chain (topRepr hp q),
    TopFlagSubdivision.chain_apply]
  congr 1
  rw [← integralCoefficient_toSimplex hp (simplexToCode hp (topRepr hp q)),
    toSimplex_simplexToCode]

/-- On the selected support, cycle coefficient times local index is one; off the support it is
zero. -/
theorem coefficient_mul_referenceIndex
    (hp : Nat.Prime p) (q : PrimeOrbitCycle.TopOrbit hp) :
    (PrimeOrbitCycle.orbitCycle hp).coefficient q * referenceIndex hp q =
      if IsSelected hp (topRepr hp q) then 1 else 0 := by
  classical
  let s := topRepr hp q
  let z := simplexToCode hp s
  have hs : toSimplex hp z = s := toSimplex_simplexToCode hp s
  rw [show referenceIndex hp q =
      (referenceMap hp).localZeroIndex (toSimplex hp z) by
        simp only [referenceIndex]; rw [hs]]
  rw [localZeroIndex_toSimplex hp z]
  have hiff : IsSelected hp (topRepr hp q) ↔ (z.bottom = z.top ∧ z.removal = 1) := by
    have h := isSelected_toSimplex_iff hp z
    rwa [hs] at h
  simp only [hiff]
  split_ifs with hsel
  · have hcoef : (PrimeOrbitCycle.orbitCycle hp).coefficient q =
        (coefficient z : ZMod p) := by
      exact orbitCycle_coefficient_eq hp q
    rw [hcoef]
    rcases permSignInt_eq_one_or_neg_one z.bottom with hb | hb <;>
      rcases permSignInt_eq_one_or_neg_one z.removal with hr | hr <;>
      simp [coefficient, hb, hr]
  · simp [hsel]

theorem referenceZeroCount_eq
    (hp : Nat.Prime p) :
    (PrimeOrbitCycle.orbitCycle hp).zeroCount (referenceIndex hp) =
      FoxNeuwirth.referenceSignedOrbitCount p := by
  classical
  unfold FiniteIncidenceCycle.zeroCount
  rw [show (∑ q : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient q * referenceIndex hp q) =
      Fintype.card {q : PrimeOrbitCycle.TopOrbit hp //
        IsSelected hp (topRepr hp q)} by
    simp_rw [coefficient_mul_referenceIndex hp]
    exact sum_if_one_zero_eq_card _]
  rw [Fintype.card_congr (selectedOrbitEquivTopSupport hp).symm]
  rw [card_selectedOrbit p]
  rfl

/-- The finite orbit zero-count model supplied by the reference affine construction. -/
noncomputable def model
    (hp : Nat.Prime p) : FiniteOrbitZeroCountModel hp where
  cycle := PrimeOrbitCycle.orbitCycle hp
  topSimplex := topRepr hp
  referenceMap := referenceMap hp
  referenceRegular := referenceMap_regular hp
  referenceIndex := referenceIndex hp
  referenceIndex_eq := by intro q; rfl
  referenceCount_eq := referenceZeroCount_eq hp

/-- The explicit reference orbit count is nonzero. -/
theorem referenceZeroCount_ne_zero
    (hp : Nat.Prime p) :
    (PrimeOrbitCycle.orbitCycle hp).zeroCount (referenceIndex hp) ≠ 0 := by
  rw [referenceZeroCount_eq hp]
  exact FoxNeuwirth.referenceSignedOrbitCount_ne_zero hp

end ReferenceAffineOrbitCount
end FoxNeuwirthOrderComplex

namespace AAK

/-- Step S5: the prime-orbit cycle carries an explicit regular affine reference map with nonzero
signed orbit count. -/
theorem simplestRoute_referenceAffineCount_complete :
    ∀ {p : Nat} (hp : Nat.Prime p),
      Nonempty (FiniteOrbitZeroCountModel hp) :=
  fun hp => ⟨FoxNeuwirthOrderComplex.ReferenceAffineOrbitCount.model hp⟩

end AAK
end NRR
