/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part02

/-! # Quantum parallel repetition, part 03 -/

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part three. -/
noncomputable local instance matrixComplexContinuousENormPartThree
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

private def dSVDensityRationalPhysicalProjector
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

theorem dSVDensityRationalPhysicalProjector_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

theorem dSVDensityRationalPhysicalProjector_projective
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    dSVDensityRationalPhysicalProjector w ξ k *
        dSVDensityRationalPhysicalProjector w ξ k =
      dSVDensityRationalPhysicalProjector w ξ k := by
  exact dSVDensityRationalProjectiveThresholdPOVM_projective
    w N k (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ) true

theorem dSVDensityRationalPhysicalProjector_complement_pos
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalPhysicalProjector w ξ k).PosSemidef :=
  dSVProjectorComplement_posSemidef
    (dSVDensityRationalPhysicalProjector w ξ k)
    (dSVDensityRationalPhysicalProjector_pos w ξ k)
    (dSVDensityRationalPhysicalProjector_projective w ξ k)

private def dSVDensityRationalPhysicalGlobalPOVM
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)

theorem dSVDensityRationalPhysicalProjectorSquare_eq_atomMismatch
    {d N : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) (k : Fin N) :
    (Matrix.trace
      ((dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k) *
       (dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k))).re =
      ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) =
            dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues j)
        then 0
        else spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j := by
  classical
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  let f : Fin d → Bool := fun i =>
    dSVDensityRationalProjectiveThresholdBin w N k
      (hF.isHermitian.eigenvalues i)
  let g : Fin d → Bool := fun j =>
    dSVDensityRationalProjectiveThresholdBin w N k
      (hG.isHermitian.eigenvalues j)
  let P := (spectralPartitionPOVM F hF f).effect true
  let R := (spectralPartitionPOVM G hG g).effect true
  have deficit :=
    spectralPartitionPOVM_weighted_trace_deficit_eq_mismatch
      F G hF hG f g (fun _ : Bool => (1 : ℝ))
  simp only [one_pow, one_mul] at deficit
  have ffalse := dSVUniformDensityBinarySpectral_false_eq_complement
    F hF f
  have gfalse := dSVUniformDensityBinarySpectral_false_eq_complement
    G hG g
  have hp : P * P = P :=
    spectralPartitionPOVM_projective F hF f true
  have hr : R * R = R :=
    spectralPartitionPOVM_projective G hG g true
  change (Matrix.trace ((P - R) * (P - R))).re = _
  change
    (∑ b : Bool, (Matrix.trace
      ((spectralPartitionPOVM G hG g).effect b)).re) -
      (∑ b : Bool, (Matrix.trace
        ((spectralPartitionPOVM F hF f).effect b *
          (spectralPartitionPOVM G hG g).effect b)).re) =
      ∑ i : Fin d, ∑ j : Fin d,
        if f i = g j then 0
        else spectralAtomOverlap F G hF hG i j at deficit
  rw [← deficit]
  simp only [Fintype.sum_bool]
  rw [ffalse, gfalse]
  change (Matrix.trace ((P - R) * (P - R))).re =
    (Matrix.trace R).re + (Matrix.trace (1 - R)).re -
      ((Matrix.trace (P * R)).re +
        (Matrix.trace ((1 - P) * (1 - R))).re)
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, hp, hr]
  rw [Matrix.trace_mul_comm R P]
  ring

theorem dSVDensityRationalPhysicalProjectorSquare_grid_eq
    {d N : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ k : Fin N,
      (Matrix.trace
        ((dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k) *
         (dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k))).re) /
        (N : ℝ) =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ := by
  classical
  simp_rw [dSVDensityRationalPhysicalProjectorSquare_eq_atomMismatch]
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  let overlap := spectralAtomOverlap F G hF hG
  have commute :
      (∑ k : Fin N, ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
              (hF.isHermitian.eigenvalues i) =
            dSVDensityRationalProjectiveThresholdBin w N k
              (hG.isHermitian.eigenvalues j)
        then 0 else overlap i j) =
      ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin N,
        if dSVDensityRationalProjectiveThresholdBin w N k
              (hF.isHermitian.eigenvalues i) =
            dSVDensityRationalProjectiveThresholdBin w N k
              (hG.isHermitian.eigenvalues j)
        then 0 else overlap i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  change
    (∑ k : Fin N, ∑ i : Fin d, ∑ j : Fin d,
      if dSVDensityRationalProjectiveThresholdBin w N k
            (hF.isHermitian.eigenvalues i) =
          dSVDensityRationalProjectiveThresholdBin w N k
            (hG.isHermitian.eigenvalues j)
      then 0 else overlap i j) / (N : ℝ) = _
  rw [commute]
  unfold dSVDensityRationalLeftProjectiveThresholdAtomMismatch
  change
    (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin N,
      if dSVDensityRationalProjectiveThresholdBin w N k
            (hF.isHermitian.eigenvalues i) =
          dSVDensityRationalProjectiveThresholdBin w N k
            (hG.isHermitian.eigenvalues j)
      then 0 else overlap i j) / (N : ℝ) =
      ∑ i : Fin d, ∑ j : Fin d,
        overlap i j * dSVUniformDensityThresholdMismatch N
          (dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i))
          (dSVRationalSoftPass w
            (hG.isHermitian.eigenvalues j))
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold dSVUniformDensityThresholdMismatch
    dSVUniformDensityThresholdWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold dSVDensityRationalProjectiveThresholdBin
  by_cases left : dSVUniformDensityThresholdGrid N k ≤
      dSVRationalSoftPass w (hF.isHermitian.eigenvalues i)
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤
        dSVRationalSoftPass w (hG.isHermitian.eigenvalues j)
    · simp only [left, decide_true, right, ↓reduceIte, zero_div, one_div, mul_zero]
    · simp only [left, decide_true, right, decide_false, Bool.true_eq_false, ↓reduceIte,
        div_eq_mul_inv, one_mul, iff_false, not_true_eq_false, mul_one]
  · by_cases right : dSVUniformDensityThresholdGrid N k ≤
        dSVRationalSoftPass w (hG.isHermitian.eigenvalues j)
    · simp only [left, decide_false, right, decide_true, Bool.false_eq_true, ↓reduceIte,
        div_eq_mul_inv, one_mul, iff_true, mul_one]
    · simp only [left, decide_false, right, ↓reduceIte, zero_div, one_div, mul_zero]

theorem dSVDensityRationalPhysicalProjector_weighted_rank_eq
    {d N : ℕ} (w : ℝ) (ξ : BipartiteUnitVector d) :
    (∑ k : Fin N, dSVUniformDensityThresholdWeight N k *
      (Matrix.trace
        (dSVDensityRationalPhysicalProjector w ξ k)).re) =
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  classical
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  change
    (∑ k : Fin N, dSVUniformDensityThresholdWeight N k *
      (Matrix.trace
        ((spectralPartitionPOVM F hF
          (fun i : Fin d =>
            dSVDensityRationalProjectiveThresholdBin w N k
              (hF.isHermitian.eigenvalues i))).effect true)).re) =
      ∑ i : Fin d, dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i))
  simp_rw [spectralPartitionPOVM_trace_eq_atom_count]
  unfold dSVUniformDensityGridPrefix
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  unfold dSVDensityRationalProjectiveThresholdBin
  by_cases accepted : dSVUniformDensityThresholdGrid N k ≤
      dSVRationalSoftPass w
        (hF.isHermitian.eigenvalues i)
  · simp only [accepted, decide_true, ↓reduceIte, mul_one]
  · simp only [accepted, decide_false, Bool.false_eq_true, ↓reduceIte, mul_zero]

/--
The DSV density rational physical diagonal born success construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPhysicalDiagonalBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ξ))

theorem dSVDensityRationalPhysicalDiagonalBornSuccess_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ =
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ /
        (d : ℝ) := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  unfold dSVDensityRationalPhysicalDiagonalBornSuccess
    dSVDensityRationalPhysicalGlobalPOVM
  rw [dSVUniformDensityThresholdShared_diagonalBorn_eq
    grid dimension
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)]
  rw [← dSVDensityRationalPhysicalProjector_weighted_rank_eq w ξ]
  unfold dSVUniformDensityThresholdWeight
  rw [← Finset.mul_sum]
  field_simp

/--
The DSV density rational physical projector cross hazard construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPhysicalProjectorCrossHazard
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ k : Fin N,
    (Matrix.trace
      ((dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k) *
       (dSVDensityRationalPhysicalProjector w ξ k -
        dSVDensityRationalPhysicalProjector w ζ k))).re) /
      ((d : ℝ) * (N : ℝ))

theorem dSVDensityRationalPhysicalProjectorCrossHazard_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ / (d : ℝ) := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  calc
    (∑ k : Fin N,
      (Matrix.trace
        ((dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k) *
         (dSVDensityRationalPhysicalProjector w ξ k -
          dSVDensityRationalPhysicalProjector w ζ k))).re) /
        ((d : ℝ) * (N : ℝ)) =
      ((∑ k : Fin N,
        (Matrix.trace
          ((dSVDensityRationalPhysicalProjector w ξ k -
            dSVDensityRationalPhysicalProjector w ζ k) *
           (dSVDensityRationalPhysicalProjector w ξ k -
            dSVDensityRationalPhysicalProjector w ζ k))).re) /
          (N : ℝ)) / (d : ℝ) := by
      field_simp
    _ = dSVDensityRationalLeftProjectiveThresholdAtomMismatch
          w N ξ ζ / (d : ℝ) := by
      rw [dSVDensityRationalPhysicalProjectorSquare_grid_eq w ξ ζ]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def dSVDensityRationalCompleteProjectiveThresholdProjector
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).effect true

theorem dSVDensityRationalCompleteProjectiveThresholdProjector_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef :=
  (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive true

theorem dSVDensityRationalCompleteProjectiveThresholdEffect_projective
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d)
    (k : Fin N) (a : Bool) :
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect a *
      (dSVDensityRationalLeftProjectiveThresholdPOVM
        w N k ξ).effect a =
      (dSVDensityRationalLeftProjectiveThresholdPOVM
        w N k ξ).effect a := by
  exact dSVDensityRationalProjectiveThresholdPOVM_projective
    w N k
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ) a

theorem dSVDensityRationalCompleteProjectiveThresholdEffect_false
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect false =
      1 - dSVDensityRationalCompleteProjectiveThresholdProjector
        w N ξ k := by
  have complete :=
    (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).complete
  rw [Fintype.sum_bool, add_comm] at complete
  exact eq_sub_of_add_eq complete

theorem
    dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (k : Fin N) :
    (1 - dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ k).PosSemidef := by
  rw [← dSVDensityRationalCompleteProjectiveThresholdEffect_false]
  exact (dSVDensityRationalLeftProjectiveThresholdPOVM
    w N k ξ).positive false

/--
The positive operator-valued measurement implementing DSV density rational complete projective
binary.
-/
def dSVDensityRationalCompleteProjectiveBinaryPOVM
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    POVM Bool (DSVUniformDensityThresholdLocalIndex N d) :=
  dSVGlobalProjectorBinaryPOVM
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_pos
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
      w N ξ)

theorem dSVDensityRationalCompleteProjectiveBinaryPOVM_effect
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (a : Bool) :
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ).effect a =
      Matrix.blockDiagonal' (fun k : Fin N =>
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).effect a) := by
  cases a
  · change
      Matrix.blockDiagonal' (fun k : Fin N =>
        1 - dSVDensityRationalCompleteProjectiveThresholdProjector
          w N ξ k) = _
    congr 1
    funext k
    exact
      (dSVDensityRationalCompleteProjectiveThresholdEffect_false
        w N ξ k).symm
  · rfl

theorem dSVDensityRationalCompleteProjectiveBinaryPOVM_projective
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (a : Bool) :
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ).effect a *
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect a =
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect a := by
  exact dSVGlobalProjectorBinaryPOVM_projective
    (dSVDensityRationalCompleteProjectiveThresholdProjector
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_pos
      w N ξ)
    (dSVDensityRationalCompleteProjectiveThresholdProjector_complement_pos
      w N ξ)
    (fun k =>
      dSVDensityRationalCompleteProjectiveThresholdEffect_projective
        w N ξ k true)
    a

/-- The finite outcome encoding for DSV density rational complete projective. -/
def dSVDensityRationalCompleteProjectiveOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  coherentBinaryJointOutcome
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ξ)
    (transposePOVM
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ζ))
    (dSVUniformDensityThresholdSharedState N d) a b

theorem dSVDensityRationalCompleteProjectiveOutcome_eq_block_action
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b =
      toLp 2
        ((Matrix.blockDiagonal'
            (fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                w N k ξ).effect a) ⊗ₖ
          (Matrix.blockDiagonal'
            (fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                w N k ζ).effect b)).transpose).mulVec
          (ofLp
            (dSVUniformDensityThresholdSharedState N d))) := by
  unfold dSVDensityRationalCompleteProjectiveOutcome
    coherentBinaryJointOutcome
  change
    toLp 2
      (((dSVDensityRationalCompleteProjectiveBinaryPOVM
            w N ξ).effect a ⊗ₖ
         ((dSVDensityRationalCompleteProjectiveBinaryPOVM
            w N ζ).effect b).transpose).mulVec
        (ofLp (dSVUniformDensityThresholdSharedState N d))) = _
  rw [dSVDensityRationalCompleteProjectiveBinaryPOVM_effect,
    dSVDensityRationalCompleteProjectiveBinaryPOVM_effect]

theorem dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b =
      (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) •
        toLp 2
          (Matrix.vec
            ((Matrix.blockDiagonal' fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ξ).effect a *
                (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ζ).effect b).transpose)) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_block_action]
  let τ : Fin N → ℝ := fun _ => 1
  let P : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect a
  let R : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ζ).effect b
  let M : Matrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    Matrix.blockDiagonal' P ⊗ₖ
      (Matrix.blockDiagonal' R).transpose
  change
    Matrix.toEuclideanLin M
      (sharedThresholdResource (d := Fin d) τ) = _
  rw [sharedThresholdResource,
    (Matrix.toEuclideanLin M).map_smul_of_tower]
  congr 1
  have raw := sharedThresholdResourceRaw_block_action τ P R
  change
    toLp 2
      (M.mulVec
        (ofLp (sharedThresholdResourceRaw (d := Fin d) τ))) =
      toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N => P k * R k).transpose))
  simpa only [M, P, R, τ, Complex.ofReal_one, one_smul] using raw

theorem dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b‖ ^ 2 =
      (∑ k : Fin N,
        (Matrix.trace
          ((dSVDensityRationalLeftProjectiveThresholdPOVM
              w N k ξ).effect a *
           (dSVDensityRationalLeftProjectiveThresholdPOVM
              w N k ζ).effect b)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_block_action]
  let τ : Fin N → ℝ := fun _ => 1
  let P : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect a
  let R : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ζ).effect b
  change
    ‖toLp 2
      ((Matrix.blockDiagonal' P ⊗ₖ
        (Matrix.blockDiagonal' R).transpose).mulVec
          (ofLp (sharedThresholdResource (d := Fin d) τ)))‖ ^ 2 =
      (∑ k : Fin N, (Matrix.trace (P k * R k)).re) /
        ((d : ℝ) * (N : ℝ))
  simpa [τ] using
    sharedThresholdResource_block_action_norm_sq
      τ P R
      (fun k =>
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).positive a)
      (fun k =>
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ζ).positive b)
      (fun k =>
        dSVDensityRationalCompleteProjectiveThresholdEffect_projective
          w N ξ k a)
      (fun k =>
        dSVDensityRationalCompleteProjectiveThresholdEffect_projective
          w N ζ k b)

end

section

open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalGridPrefix_nonneg
    (N : ℕ) (a : ℝ) :
    0 ≤ dSVUniformDensityGridPrefix N a := by
  unfold dSVUniformDensityGridPrefix
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg
    (dSVUniformDensityThresholdWeight_nonneg N k)
    (by split <;> norm_num)

theorem dSVDensityRationalSoftPass_rescaled_le_density
    {w a : ℝ} (width : 0 < w) (nonnegative : 0 ≤ a) :
    w * dSVRationalSoftPass w a ≤ a := by
  have denominator : 0 < a + w := by linarith
  unfold dSVRationalSoftPass
  calc
    w * (a / (a + w)) = w * a / (a + w) := by ring
    _ ≤ a := (div_le_iff₀ denominator).mpr (by
      linarith [sq_nonneg a])

theorem dSVDensityRationalSoftPass_density_defect_le
    {w a : ℝ} (width : 0 < w)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - w * dSVRationalSoftPass w a ≤ a / w := by
  have denominator : 0 < a + w := by linarith
  calc
    a - w * dSVRationalSoftPass w a =
        a ^ 2 / (a + w) := by
      unfold dSVRationalSoftPass
      field_simp
      ring
    _ ≤ a / w := by
      apply (div_le_div_iff₀ denominator width).mpr
      linarith [mul_nonneg (mul_nonneg nonnegative width.le)
        (sub_nonneg.mpr bounded), sq_nonneg a]

theorem dSVDensityRationalGrid_rescaled_le_density
    {N : ℕ} {w a : ℝ} (width : 0 < w) (grid : 0 < N)
    (nonnegative : 0 ≤ a) :
    w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) ≤ a := by
  obtain ⟨pass_nonnegative, pass_bounded⟩ :=
    dSVRationalSoftPass_mem_unit width nonnegative
  calc
    w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) ≤
      w * dSVRationalSoftPass w a :=
        mul_le_mul_of_nonneg_left
          (dSVUniformDensityGridPrefix_le_density grid
            pass_nonnegative pass_bounded) width.le
    _ ≤ a :=
      dSVDensityRationalSoftPass_rescaled_le_density
        width nonnegative

theorem dSVDensityRationalGrid_density_defect_le
    {N : ℕ} {w a : ℝ} (width : 0 < w) (grid : 0 < N)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) ≤
      a / w + w / (N : ℝ) := by
  obtain ⟨pass_nonnegative, pass_bounded⟩ :=
    dSVRationalSoftPass_mem_unit width nonnegative
  have cell_bound :
      dSVRationalSoftPass w a -
        dSVUniformDensityGridPrefix N
          (dSVRationalSoftPass w a) ≤ 1 / (N : ℝ) :=
    (dSVUniformDensityGridPrefix_density_sub_lt grid
      pass_nonnegative pass_bounded).le
  have scaled := mul_le_mul_of_nonneg_left cell_bound width.le
  have rational := dSVDensityRationalSoftPass_density_defect_le
    width nonnegative bounded
  calc
    a - w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w a) =
      (a - w * dSVRationalSoftPass w a) +
        w * (dSVRationalSoftPass w a -
          dSVUniformDensityGridPrefix N
            (dSVRationalSoftPass w a)) := by ring
    _ ≤ a / w + w * (1 / (N : ℝ)) :=
      add_le_add rational scaled
    _ = a / w + w / (N : ℝ) := by ring

/--
The DSV density rational canonical accepted coefficient construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalCanonicalAcceptedCoefficient
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) : ℝ :=
  Real.sqrt (w * dSVUniformDensityGridPrefix N
    (dSVRationalSoftPass w
      ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)))

theorem dSVDensityRationalCanonicalAcceptedCoefficient_nonneg
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    0 ≤ dSVDensityRationalCanonicalAcceptedCoefficient
      w N ξ i := Real.sqrt_nonneg _

theorem dSVDensityRationalCanonicalAcceptedCoefficient_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)) := by
  unfold dSVDensityRationalCanonicalAcceptedCoefficient
  apply Real.sq_sqrt
  exact mul_nonneg width.le
    (dSVDensityRationalGridPrefix_nonneg _ _)

/--
The DSV density rational canonical alice basis construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalCanonicalAliceBasis
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  Classical.choose
    (exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt ξ)

theorem dSVDensityRationalCanonicalAliceBasis_target
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ξ.val = schmidtVector
      (dSVUniformDensityPolarLeftSchmidtCoefficient ξ)
      (dSVDensityRationalCanonicalAliceBasis ξ)
      (dSVUniformDensityThresholdLeftBobBasis ξ) :=
  Classical.choose_spec
    (exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt ξ)

/-- The target object for DSV density rational canonical accepted. -/
def dSVDensityRationalCanonicalAcceptedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  schmidtVector
    (dSVDensityRationalCanonicalAcceptedCoefficient w N ξ)
    (dSVDensityRationalCanonicalAliceBasis ξ)
    (dSVUniformDensityThresholdLeftBobBasis ξ)

theorem dSVDensityRationalCanonicalAcceptedTarget_norm_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 =
      w * dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [schmidtVector_norm_sq]
  simp_rw [dSVDensityRationalCanonicalAcceptedCoefficient_sq width]
  unfold dSVDensityRationalLeftProjectiveDiagonalMass
  rw [Finset.mul_sum]

theorem dSVDensityRationalCanonicalAcceptedTarget_distance_sq_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
      w N ξ‖ ^ 2 =
      ∑ i : Fin d,
        (dSVUniformDensityPolarLeftSchmidtCoefficient ξ i -
          dSVDensityRationalCanonicalAcceptedCoefficient
            w N ξ i) ^ 2 := by
  rw [dSVDensityRationalCanonicalAliceBasis_target ξ]
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [dSVUniformDensitySchmidtVector_sub,
    schmidtVector_norm_sq]

theorem dSVDensityRationalCanonicalAcceptedCoefficient_error_sq_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVUniformDensityPolarLeftSchmidtCoefficient ξ i -
        dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i) ^ 2 ≤
      ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i) / w +
        w / (N : ℝ) := by
  let a :=
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)
  let b := w * dSVUniformDensityGridPrefix N
    (dSVRationalSoftPass w a)
  have ha : 0 ≤ a :=
    (dSVSoftBobLeftReducedDensity_posSemidef ξ).eigenvalues_nonneg i
  have ha_one : a ≤ 1 :=
    dSVSoftBobLeftReducedDensity_eigenvalue_le_one ξ i
  have hb : 0 ≤ b := mul_nonneg width.le
    (dSVDensityRationalGridPrefix_nonneg N _)
  have below : b ≤ a :=
    dSVDensityRationalGrid_rescaled_le_density width grid ha
  have roots := dSVAdaptiveSoft_sqrt_sub_sq_le_abs a b ha hb
  rw [abs_of_nonneg (sub_nonneg.mpr below)] at roots
  have defect := dSVDensityRationalGrid_density_defect_le
    width grid ha ha_one
  change (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a / w + w / (N : ℝ)
  exact roots.trans defect

theorem dSVDensityRationalCanonicalAcceptedTarget_distance_sq_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
        w N ξ‖ ^ 2 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
  rw [dSVDensityRationalCanonicalAcceptedTarget_distance_sq_eq]
  calc
    (∑ i : Fin d,
      (dSVUniformDensityPolarLeftSchmidtCoefficient ξ i -
        dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i) ^ 2) ≤
      ∑ i : Fin d,
        (((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i) / w +
          w / (N : ℝ)) :=
      Finset.sum_le_sum (fun i _ =>
        dSVDensityRationalCanonicalAcceptedCoefficient_error_sq_le
          width grid ξ i)
    _ = 1 / w + (d : ℝ) * w / (N : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      rw [positiveDensity_eigenvalues_sum
        (dSVSoftBobLeftReducedDensity ξ)
        (dSVSoftBobLeftReducedDensity_posSemidef ξ)
        (dSVSoftBobLeftReducedDensity_trace ξ)]
      simp only [one_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, add_right_inj]
      ring

theorem dSVDensityRationalCanonicalAcceptedTarget_distance_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
        w N ξ‖ ≤
      Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  have nonnegative : 0 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
    positivity
  have squared :=
    dSVDensityRationalCanonicalAcceptedTarget_distance_sq_le
      width grid ξ
  have exact_sqrt := Real.sq_sqrt nonnegative
  nlinarith [norm_nonneg
    (ξ.val - dSVDensityRationalCanonicalAcceptedTarget w N ξ),
    Real.sqrt_nonneg (1 / w + (d : ℝ) * w / (N : ℝ))]

theorem dSVDensityRationalCanonicalAcceptedTarget_ne_zero
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalAcceptedTarget w N ξ ≠ 0 := by
  intro zero
  have actual :=
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N ξ
  rw [zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at actual
  have lower :=
    dSVDensityRationalLeftProjectiveDiagonalMass_lower
      width grid ξ
  nlinarith

private def dSVDensityRationalCanonicalNormalizedTarget
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  NormedSpace.normalize
    (dSVDensityRationalCanonicalAcceptedTarget w N ξ)

theorem dSVDensityRationalCanonicalNormalizedTarget_norm
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCanonicalNormalizedTarget
      w N ξ‖ = 1 := by
  unfold dSVDensityRationalCanonicalNormalizedTarget
  exact NormedSpace.norm_normalize
    (dSVDensityRationalCanonicalAcceptedTarget_ne_zero
      width grid fine ξ)

theorem dSVDensityRationalCanonicalNormalizedTarget_distance_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val - dSVDensityRationalCanonicalNormalizedTarget
        w N ξ‖ ≤
      2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  let v := dSVDensityRationalCanonicalAcceptedTarget w N ξ
  have nonzero : v ≠ 0 :=
    dSVDensityRationalCanonicalAcceptedTarget_ne_zero
      width grid fine ξ
  have reverse : |1 - ‖v‖| ≤ ‖ξ.val - v‖ := by
    have actual := abs_norm_sub_norm_le ξ.val v
    simpa only [ge_iff_le, ξ.property] using actual
  have movement :
      ‖v - NormedSpace.normalize v‖ = |1 - ‖v‖| := by
    rw [norm_sub_rev]
    exact dSVUniformDensity_normalize_sub_self_norm v nonzero
  change ‖ξ.val - NormedSpace.normalize v‖ ≤ _
  calc
    ‖ξ.val - NormedSpace.normalize v‖ =
      ‖(ξ.val - v) + (v - NormedSpace.normalize v)‖ := by
        congr 1
        abel
    _ ≤ ‖ξ.val - v‖ + ‖v - NormedSpace.normalize v‖ :=
      norm_add_le _ _
    _ ≤ 2 * ‖ξ.val - v‖ := by
      rw [movement]
      linarith
    _ ≤ 2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) := by
      gcongr
      exact dSVDensityRationalCanonicalAcceptedTarget_distance_le
        width grid ξ

/-- The target object for DSV density rational canonical accepted unit. -/
def dSVDensityRationalCanonicalAcceptedUnitTarget
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVDensityRationalCanonicalNormalizedTarget w N ξ,
    dSVDensityRationalCanonicalNormalizedTarget_norm
      width grid fine ξ⟩

theorem dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (ξ : BipartiteUnitVector d) :
    ‖ξ.val -
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine ξ).val‖ ≤
      2 * Real.sqrt (1 / w + (d : ℝ) * w / (N : ℝ)) :=
  dSVDensityRationalCanonicalNormalizedTarget_distance_le
    width grid fine ξ

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalLargeWidthDiagonalMass_half
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    1 / (2 * (w + 1)) ≤
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  have denominator : 0 < w + 1 := by linarith
  have arithmetic :
      1 / (2 * (w + 1)) ≤ 1 / (w + 1) - (d : ℝ) / N := by
    have identity :
        1 / (w + 1) - 1 / (2 * (w + 1)) =
          1 / (2 * (w + 1)) := by
      field_simp; ring
    linarith
  exact arithmetic.trans
    (dSVDensityRationalLeftProjectiveDiagonalMass_lower
      width grid ξ)

theorem dSVDensityRationalLargeWidthDiagonalMass_pos
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    0 < dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  have lower := dSVDensityRationalLargeWidthDiagonalMass_half
    width grid fine ξ
  have positive : 0 < 1 / (2 * (w + 1)) := by positivity
  exact positive.trans_le lower

theorem
    dSVDensityRationalLargeWidthRelativeMismatch_le_discrepancy
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
      2 * (w + 1) *
        (dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
          (d : ℝ) / N) := by
  let M := dSVDensityRationalLeftProjectiveDiagonalMass w N ξ
  let D := dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
    (d : ℝ) / N
  have mass_positive : 0 < M :=
    dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ
  have mass_floor : 1 / (2 * (w + 1)) ≤ M :=
    dSVDensityRationalLargeWidthDiagonalMass_half
      width grid fine ξ
  have difference_nonnegative :
      0 ≤ dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ := by
    unfold dSVUniformLeftDensitySpectralAtomDiscrepancy
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (abs_nonneg _)
      (spectralAtomOverlap_nonneg _ _ _ _ i j)
  have defect_nonnegative : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (div_nonneg difference_nonnegative width.le) (by positivity)
  have actual :=
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch_le_discrepancy
      width grid ξ ζ
  change
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ / M ≤ 2 * (w + 1) * D
  apply (div_le_iff₀ mass_positive).mpr
  have floor_scaled : 1 ≤ 2 * (w + 1) * M := by
    have denominator : 0 < 2 * (w + 1) := by positivity
    have crossed := (div_le_iff₀ denominator).mp mass_floor
    linarith
  change
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
      w N ξ ζ ≤ (2 * (w + 1) * D) * M
  calc
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ ≤ D := actual
    _ ≤ D * (2 * (w + 1) * M) := by
      linarith [mul_nonneg defect_nonnegative
        (show 0 ≤ 2 * (w + 1) * M - 1 by linarith)]
    _ = (2 * (w + 1) * D) * M := by ring

theorem
    dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
    {d N : ℕ} {w : ℝ} (large : 1 ≤ w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
        8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
          2 * (w + 1) * ((d : ℝ) / N) := by
  have width : 0 < w := lt_of_lt_of_le (by norm_num) large
  have distance := dSVUniformLeftDensitySpectralAtomDiscrepancy_le
    ξ ζ
  have root : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have distance_nonnegative : 0 ≤ ‖ξ.val - ζ.val‖ := norm_nonneg _
  have denominator : 0 < w := width
  have ratio : (w + 1) / w ≤ 2 := by
    apply (div_le_iff₀ denominator).mpr
    linarith
  calc
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
        2 * (w + 1) *
          (dSVUniformLeftDensitySpectralAtomDiscrepancy ξ ζ / w +
            (d : ℝ) / N) :=
      dSVDensityRationalLargeWidthRelativeMismatch_le_discrepancy
        width grid fine ξ ζ
    _ ≤ 2 * (w + 1) *
          ((2 * Real.sqrt 2 * ‖ξ.val - ζ.val‖) / w +
            (d : ℝ) / N) := by
      gcongr
    _ = 4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ * ((w + 1) / w) +
          2 * (w + 1) * ((d : ℝ) / N) := by
      field_simp; ring
    _ ≤ (4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖) * 2 +
          2 * (w + 1) * ((d : ℝ) / N) := by
      have scale_nonnegative :
          0 ≤ 4 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ := by positivity
      have scaled := mul_le_mul_of_nonneg_left ratio scale_nonnegative
      exact add_le_add scaled (le_refl _)
    _ = 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
          2 * (w + 1) * ((d : ℝ) / N) := by
      ring

theorem dSVDensityRationalLargeWidth_exists_fine_grid
    (d : ℕ) (dimension : 0 < d)
    (w : ℝ) (width : 0 < w)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      2 * (w + 1) * ((d : ℝ) / N) ≤ ε := by
  have denominator : 0 < ε / (2 * (w + 1)) := by positivity
  obtain ⟨N, large⟩ :=
    exists_nat_gt ((d : ℝ) / (ε / (2 * (w + 1))))
  have real_dimension : 0 < (d : ℝ) := by exact_mod_cast dimension
  have real_grid : 0 < (N : ℝ) :=
    lt_trans (div_pos real_dimension denominator) large
  have grid : 0 < N := by exact_mod_cast real_grid
  refine ⟨N, grid, ?_⟩
  have crossed := (div_lt_iff₀ denominator).mp large
  have small : (d : ℝ) / N < ε / (2 * (w + 1)) := by
    apply (div_lt_iff₀ real_grid).mpr
    linarith
  have positive : 0 < 2 * (w + 1) := by positivity
  have scaled := (lt_div_iff₀ positive).mp small
  linarith

theorem dSVDensityRationalLargeWidth_exists_sourceUniformParameters
    (d : ℕ) (dimension : 0 < d)
    (ε : ℝ) (precision : 0 < ε) (small : ε ≤ 1) :
    ∃ (w : ℝ) (N : ℕ),
      1 ≤ w ∧ 0 < N ∧
      2 * (w + 1) * ((d : ℝ) / N) ≤ ε ∧
      (1 / w + w * ((d : ℝ) / N) ≤ 3 * ε / 2) ∧
      (∀ ξ : BipartiteUnitVector d,
        0 < dSVDensityRationalLeftProjectiveDiagonalMass
          w N ξ) ∧
      (∀ ξ ζ : BipartiteUnitVector d,
        dSVDensityRationalLeftProjectiveThresholdAtomMismatch
            w N ξ ζ /
          dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
            8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ + ε) := by
  let w : ℝ := 1 / ε
  have width : 0 < w := by dsimp [w]; positivity
  have large : 1 ≤ w := by
    dsimp [w]
    exact (le_div_iff₀ precision).mpr (by simpa only [one_mul] using small)
  obtain ⟨N, grid, budget⟩ :=
    dSVDensityRationalLargeWidth_exists_fine_grid
      d dimension w width ε precision
  have fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)) := by
    have denominator : 0 < 2 * (w + 1) := by positivity
    apply (le_div_iff₀ denominator).mpr
    linarith
  have inverse : 1 / w = ε := by
    dsimp [w]
    field_simp
  have rounding : 1 / w + w * ((d : ℝ) / N) ≤ 3 * ε / 2 := by
    have grid_cost : w * ((d : ℝ) / N) ≤ ε / 2 := by
      have weight : 0 ≤ (d : ℝ) / N := by positivity
      linarith
    rw [inverse]
    linarith
  refine ⟨w, N, large, grid, budget, rounding, ?_, ?_⟩
  · intro ξ
    exact dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ
  · intro ξ ζ
    exact
      (dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
        large grid fine ξ ζ).trans (by gcongr)

theorem dSVDensityRationalLargeWidthPhysicalDiagonalBornSuccess_pos
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ : BipartiteUnitVector d) :
    0 < dSVDensityRationalPhysicalDiagonalBornSuccess
      grid dimension w ξ := by
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq
    grid dimension w ξ]
  exact div_pos
    (dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ)
    (by exact_mod_cast dimension)

theorem dSVDensityRationalLargeWidthPhysicalRelativeHazard_eq
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ /
        dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  rw [dSVDensityRationalPhysicalProjectorCrossHazard_eq
    grid dimension w ξ ζ,
    dSVDensityRationalPhysicalDiagonalBornSuccess_eq
      grid dimension w ξ]
  have dimension_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have mass_ne :
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≠ 0 :=
    ne_of_gt (dSVDensityRationalLargeWidthDiagonalMass_pos
      width grid fine ξ)
  field_simp

theorem dSVDensityRationalLargeWidthPhysicalRelativeHazard_le
    {d N : ℕ} (dimension : 0 < d) {w : ℝ}
    (large : 1 ≤ w) (grid : 0 < N)
    (fine : (d : ℝ) / N ≤ 1 / (2 * (w + 1)))
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (w + 1) * ((d : ℝ) / N) := by
  have width : 0 < w := lt_of_lt_of_le (by norm_num) large
  rw [dSVDensityRationalLargeWidthPhysicalRelativeHazard_eq
    dimension width grid fine ξ ζ]
  exact
    dSVDensityRationalLargeWidthRelativeMismatch_le_targetDistance
      large grid fine ξ ζ

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def dSVDensityRationalPhysicalMixedBornSuccess
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) : ℝ :=
  binaryJointSuccessProbability
    (dSVUniformDensityThresholdSharedDensity grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ζ))

theorem dSVDensityRationalPhysicalMixedBornSuccess_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ =
      (∑ k : Fin N, (Matrix.trace
        (dSVDensityRationalPhysicalProjector w ξ k *
          dSVDensityRationalPhysicalProjector w ζ k)).re) /
        ((d : ℝ) * (N : ℝ)) := by
  unfold dSVDensityRationalPhysicalMixedBornSuccess
    dSVDensityRationalPhysicalGlobalPOVM
  exact dSVUniformDensityThresholdShared_mixedBorn_eq
    grid dimension
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector w ζ)
    (dSVDensityRationalPhysicalProjector_pos w ξ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ζ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ζ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ζ)

theorem dSVDensityRationalPhysicalMixedBornSuccess_loss_le
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ -
      dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ ≤
      dSVDensityRationalPhysicalProjectorCrossHazard
        N w ξ ζ := by
  have denominator : 0 < (d : ℝ) * (N : ℝ) := by
    exact mul_pos (by exact_mod_cast dimension)
      (by exact_mod_cast grid)
  have diagonal :
      dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension w ξ =
        (∑ k : Fin N,
          (Matrix.trace
            (dSVDensityRationalPhysicalProjector w ξ k)).re) /
          ((d : ℝ) * (N : ℝ)) := by
    unfold dSVDensityRationalPhysicalDiagonalBornSuccess
      dSVDensityRationalPhysicalGlobalPOVM
    exact dSVUniformDensityThresholdShared_diagonalBorn_eq
      grid dimension
      (dSVDensityRationalPhysicalProjector w ξ)
      (dSVDensityRationalPhysicalProjector_pos w ξ)
      (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
      (dSVDensityRationalPhysicalProjector_projective w ξ)
  have ledger := dSVWeightedMixedProjectorSuccessLoss_le_square
    (fun _ : Fin N => (1 : ℝ)) (fun _ => zero_le_one)
    (dSVDensityRationalPhysicalProjector w ξ)
    (dSVDensityRationalPhysicalProjector w ζ)
    (dSVDensityRationalPhysicalProjector_complement_pos w ξ)
    (dSVDensityRationalPhysicalProjector_pos w ζ)
    (dSVDensityRationalPhysicalProjector_projective w ξ)
    (dSVDensityRationalPhysicalProjector_projective w ζ)
  simp only [one_mul] at ledger
  rw [diagonal,
    dSVDensityRationalPhysicalMixedBornSuccess_eq
      grid dimension w ξ ζ]
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  rw [← sub_div]
  exact (div_le_div_iff_of_pos_right denominator).mpr ledger

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

private def dSVDensityRationalActualMixedSuccessMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true‖ ^ 2

private def dSVDensityRationalActualMixedContinueMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ false false‖ ^ 2

private def dSVDensityRationalActualMixedAsynchronousMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ true false‖ ^ 2 +
    ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ false true‖ ^ 2

theorem dSVDensityRationalActualMixedSuccessMass_eq
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedSuccessMass w N ξ ζ =
      dSVDensityRationalPhysicalMixedBornSuccess
        grid dimension w ξ ζ := by
  unfold dSVDensityRationalActualMixedSuccessMass
  rw [dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq,
    dSVDensityRationalPhysicalMixedBornSuccess_eq
      grid dimension w ξ ζ]
  rfl

theorem dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) :
    ‖dSVDensityRationalCompleteProjectiveOutcome
      w N ξ ζ a b‖ ^ 2 =
      binaryBornProbability
        (dSVUniformDensityThresholdSharedDensity
          grid dimension)
        (dSVDensityRationalPhysicalGlobalPOVM w ξ)
        (transposePOVM
          (dSVDensityRationalPhysicalGlobalPOVM w ζ)) a b := by
  let A := dSVDensityRationalCompleteProjectiveBinaryPOVM
    w N ξ
  let B := dSVDensityRationalCompleteProjectiveBinaryPOVM
    w N ζ
  let z := dSVUniformDensityThresholdSharedState N d
  have alice_physical :
      A = dSVDensityRationalPhysicalGlobalPOVM w ξ := by
    rfl
  have bob_physical :
      B = dSVDensityRationalPhysicalGlobalPOVM w ζ := by
    rfl
  have actual := coherentBinaryJointOutcome_norm_sq
    A (transposePOVM B)
    (dSVDensityRationalCompleteProjectiveBinaryPOVM_projective
      w N ξ)
    (transposePOVM_projective B
      (dSVDensityRationalCompleteProjectiveBinaryPOVM_projective
        w N ζ))
    z (dSVUniformDensityThresholdSharedState_norm
      grid dimension) a b
  rw [alice_physical, bob_physical] at actual
  simpa only [dSVDensityRationalCompleteProjectiveOutcome, binaryBornProbability,
    dSVUniformDensityThresholdSharedDensity, ← alice_physical, ← bob_physical] using actual

theorem dSVDensityRationalActualMixedContinueMass_eq_born
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedContinueMass w N ξ ζ =
      binaryContinueProbability
        (dSVUniformDensityThresholdSharedDensity
          grid dimension)
        (dSVDensityRationalPhysicalGlobalPOVM w ξ)
        (transposePOVM
          (dSVDensityRationalPhysicalGlobalPOVM w ζ)) := by
  unfold dSVDensityRationalActualMixedContinueMass
    binaryContinueProbability
  exact dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
    grid dimension w ξ ζ false false

theorem dSVDensityRationalActualMixedAsynchronousMass_eq_born
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedAsynchronousMass w N ξ ζ =
      binaryMismatchProbability
        (dSVUniformDensityThresholdSharedDensity
          grid dimension)
        (dSVDensityRationalPhysicalGlobalPOVM w ξ)
        (transposePOVM
          (dSVDensityRationalPhysicalGlobalPOVM w ζ)) := by
  unfold dSVDensityRationalActualMixedAsynchronousMass
    binaryMismatchProbability
  rw [dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
    grid dimension w ξ ζ true false,
    dSVDensityRationalActualMixedOutcome_norm_sq_eq_born
      grid dimension w ξ ζ false true]

theorem dSVDensityRationalActualMixed_mass_partition
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedContinueMass w N ξ ζ +
      dSVDensityRationalActualMixedSuccessMass w N ξ ζ +
      dSVDensityRationalActualMixedAsynchronousMass
        w N ξ ζ = 1 := by
  rw [dSVDensityRationalActualMixedContinueMass_eq_born
    grid dimension w ξ ζ,
    dSVDensityRationalActualMixedSuccessMass_eq
      grid dimension w ξ ζ,
    dSVDensityRationalActualMixedAsynchronousMass_eq_born
      grid dimension w ξ ζ]
  unfold dSVDensityRationalPhysicalMixedBornSuccess
  exact binaryStoppingPartition
    (dSVUniformDensityThresholdSharedDensity
      grid dimension)
    (dSVDensityRationalPhysicalGlobalPOVM w ξ)
    (transposePOVM
      (dSVDensityRationalPhysicalGlobalPOVM w ζ))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV density rational complete physical stopping copy accepted construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    {N d : ℕ} (w : ℝ) (ξ : BipartiteUnitVector d)
    (q : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalProjectiveThresholdBin w N q.1
    ((dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvalues q.2) = true

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The finite outcome encoding for DSV density rational physical accepted. -/
def dSVDensityRationalPhysicalAcceptedOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteProjectiveOutcome
    w N ξ ζ true true

/-- The rank map for DSV density rational physical accepted. -/
def dSVDensityRationalPhysicalAcceptedRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Fin (N + 1) :=
  let selected : Finset (Fin N) :=
    Finset.univ.filter fun k : Fin N =>
      dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true
  ⟨selected.card, by
    have bounded : selected.card ≤ N := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ selected
    omega⟩

theorem dSVDensityRationalPhysicalAcceptedRank_gridPrefix
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVUniformDensityGridPrefix N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i)) =
      ((dSVDensityRationalPhysicalAcceptedRank
        w N ξ i).val : ℝ) / (N : ℝ) := by
  classical
  rw [dSVUniformDensityGridPrefix_eq_count]
  simp only [dSVDensityRationalPhysicalAcceptedRank, dSVDensityRationalProjectiveThresholdBin,
    decide_eq_true_eq]

theorem dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * ((dSVDensityRationalPhysicalAcceptedRank
        w N ξ i).val : ℝ) / (N : ℝ) := by
  rw [dSVDensityRationalCanonicalAcceptedCoefficient_sq
    width N ξ i,
    dSVDensityRationalPhysicalAcceptedRank_gridPrefix]
  ring

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

theorem dSVUniformDensityGridPrefix_mono
    (N : ℕ) {a b : ℝ} (ordered : a ≤ b) :
    dSVUniformDensityGridPrefix N a ≤
      dSVUniformDensityGridPrefix N b := by
  unfold dSVUniformDensityGridPrefix
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _
    (dSVUniformDensityThresholdWeight_nonneg N k)
  by_cases low : dSVUniformDensityThresholdGrid N k ≤ a
  · have high : dSVUniformDensityThresholdGrid N k ≤ b :=
      low.trans ordered
    simp only [low, ↓reduceIte, high, Std.le_refl]
  · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
    · simp only [low, ↓reduceIte, high, zero_le_one]
    · simp only [low, ↓reduceIte, high, Std.le_refl]

theorem dSVUniformDensityThresholdMismatch_eq_sub_of_le
    (N : ℕ) {a b : ℝ} (ordered : a ≤ b) :
    dSVUniformDensityThresholdMismatch N a b =
      dSVUniformDensityGridPrefix N b -
        dSVUniformDensityGridPrefix N a := by
  unfold dSVUniformDensityThresholdMismatch
    dSVUniformDensityGridPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases low : dSVUniformDensityThresholdGrid N k ≤ a
  · have high : dSVUniformDensityThresholdGrid N k ≤ b :=
      low.trans ordered
    simp only [low, high, ↓reduceIte, mul_zero, mul_one, sub_self]
  · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
    · simp only [low, high, iff_true, ↓reduceIte, mul_one, mul_zero, sub_zero]
    · simp only [low, high, ↓reduceIte, mul_zero, sub_self]

theorem dSVUniformDensityThresholdMismatch_eq_abs_gridPrefix
    (N : ℕ) (a b : ℝ) :
    dSVUniformDensityThresholdMismatch N a b =
      |dSVUniformDensityGridPrefix N a -
        dSVUniformDensityGridPrefix N b| := by
  rcases le_total a b with ordered | ordered
  · rw [dSVUniformDensityThresholdMismatch_eq_sub_of_le
      N ordered]
    rw [abs_of_nonpos (sub_nonpos.mpr
      (dSVUniformDensityGridPrefix_mono N ordered))]
    ring
  · have symmetric :
        dSVUniformDensityThresholdMismatch N a b =
          dSVUniformDensityThresholdMismatch N b a := by
      unfold dSVUniformDensityThresholdMismatch
      apply Finset.sum_congr rfl
      intro k _
      by_cases low : dSVUniformDensityThresholdGrid N k ≤ a
      · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
        · simp only [low, high, ↓reduceIte, mul_zero]
        · simp only [low, high, iff_false, not_true_eq_false, ↓reduceIte, mul_one, iff_true]
      · by_cases high : dSVUniformDensityThresholdGrid N k ≤ b
        · simp only [low, high, iff_true, ↓reduceIte, mul_one, iff_false, not_true_eq_false]
        · simp only [low, high, ↓reduceIte, mul_zero]
    rw [symmetric,
      dSVUniformDensityThresholdMismatch_eq_sub_of_le
        N ordered,
      abs_of_nonneg (sub_nonneg.mpr
        (dSVUniformDensityGridPrefix_mono N ordered))]

theorem
    dSVDensityRationalPhysicalAcceptedRankMismatch_eq_thresholdMismatch
    {d N : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    |((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) -
      ((dSVDensityRationalPhysicalAcceptedRank
          w N ζ j).val : ℝ)| / (N : ℝ) =
      dSVUniformDensityThresholdMismatch N
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i))
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j)) := by
  rw [dSVUniformDensityThresholdMismatch_eq_abs_gridPrefix,
    dSVDensityRationalPhysicalAcceptedRank_gridPrefix,
    dSVDensityRationalPhysicalAcceptedRank_gridPrefix,
    ← sub_div, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)]

/--
The DSV density rational prefix rank mismatch construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPrefixRankMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap
      (dSVSoftBobLeftReducedDensity ξ)
      (dSVSoftBobLeftReducedDensity ζ)
      (dSVSoftBobLeftReducedDensity_posSemidef ξ)
      (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j *
      |((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) -
        ((dSVDensityRationalPhysicalAcceptedRank
            w N ζ j).val : ℝ)|) / (N : ℝ)

theorem dSVDensityRationalPrefixRankMismatch_eq_atomMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPrefixRankMismatch w N ξ ζ =
      dSVDensityRationalLeftProjectiveThresholdAtomMismatch
        w N ξ ζ := by
  unfold dSVDensityRationalPrefixRankMismatch
    dSVDensityRationalLeftProjectiveThresholdAtomMismatch
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_div_assoc,
    dSVDensityRationalPhysicalAcceptedRankMismatch_eq_thresholdMismatch]

theorem dSVDensityRationalPrefixRankMismatch_physicalHazard
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPrefixRankMismatch w N ξ ζ / (d : ℝ) =
      dSVDensityRationalPhysicalProjectorCrossHazard
        N w ξ ζ := by
  rw [dSVDensityRationalPrefixRankMismatch_eq_atomMismatch,
    dSVDensityRationalPhysicalProjectorCrossHazard_eq
      grid dimension w ξ ζ]

end

section

open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalPhysicalAcceptedRank_eq_floor
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVDensityRationalPhysicalAcceptedRank
      w N ξ i).val =
      Nat.floor
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) * (N : ℝ)) := by
  have unit := dSVRationalSoftPass_mem_unit width
    ((dSVSoftBobLeftReducedDensity_posSemidef
      ξ).eigenvalues_nonneg i)
  simpa only [dSVDensityRationalPhysicalAcceptedRank, dSVDensityRationalProjectiveThresholdBin,
    decide_eq_true_eq] using
    (dSVUniformDensityThresholdGrid_count_eq_floor grid
      (dSVRationalSoftPass w
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i)) unit.1 unit.2)

theorem dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d)
    (i : Fin d) (k : Fin N) :
    dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true ↔
      k.val <
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val := by
  have real_grid : (0 : ℝ) < N := by exact_mod_cast grid
  have pass_nonnegative :=
    (dSVRationalSoftPass_mem_unit width
      ((dSVSoftBobLeftReducedDensity_posSemidef
        ξ).eigenvalues_nonneg i)).1
  have product_nonnegative :
      0 ≤ dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) * (N : ℝ) :=
    mul_nonneg pass_nonnegative real_grid.le
  rw [dSVDensityRationalPhysicalAcceptedRank_eq_floor
    width grid ξ i]
  unfold dSVDensityRationalProjectiveThresholdBin
  simp only [decide_eq_true_eq]
  rw [dSVUniformDensityThresholdGrid_apply grid,
    div_le_iff₀ real_grid]
  constructor
  · intro accepted
    have cast :
        ((k.val + 1 : ℕ) : ℝ) ≤
          dSVRationalSoftPass w
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) * (N : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using accepted
    have below := (Nat.le_floor_iff product_nonnegative).2 cast
    omega
  · intro below
    have integer :
        k.val + 1 ≤
          Nat.floor
            (dSVRationalSoftPass w
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) * (N : ℝ)) := by
      omega
    have cast := (Nat.le_floor_iff product_nonnegative).1 integer
    simpa only [ge_iff_le, Nat.cast_add, Nat.cast_one] using cast

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

private def dSVDensityRationalMixedSpectralAtomBlock
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    if dSVDensityRationalProjectiveThresholdBin w N k
        (hF.isHermitian.eigenvalues i) = a ∧
      dSVDensityRationalProjectiveThresholdBin w N k
        (hG.isHermitian.eigenvalues j) = b
    then positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j
    else 0

theorem dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) :
    dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k =
      (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).effect a *
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ζ).effect b := by
  classical
  unfold dSVDensityRationalMixedSpectralAtomBlock
    dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
    spectralPartitionPOVM
  simp only [Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases alice : dSVDensityRationalProjectiveThresholdBin w N k
      ((dSVSoftBobLeftReducedDensity_posSemidef
        ξ).isHermitian.eigenvalues i) = a
  · by_cases bob : dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = b
    · simp only [alice, bob, and_self, ↓reduceIte]
    · simp only [alice, bob, and_false, ↓reduceIte, mul_zero]
  · by_cases bob : dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = b
    · simp only [alice, bob, and_true, ↓reduceIte, zero_mul]
    · simp only [alice, bob, and_self, ↓reduceIte, mul_zero]

theorem dSVDensityRationalMixedSpectralAtomBlock_trace_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) :
    (Matrix.trace
      (dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k)).re =
      ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = a ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = b
        then spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j
        else 0 := by
  unfold dSVDensityRationalMixedSpectralAtomBlock
  simp only [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [spectralAtomOverlap]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalActualMixedAsynchronousMass
        w N ξ ζ =
      dSVDensityRationalPhysicalProjectorCrossHazard
        N w ξ ζ := by
  classical
  unfold dSVDensityRationalActualMixedAsynchronousMass
  rw [dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq,
    dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq]
  unfold dSVDensityRationalPhysicalProjectorCrossHazard
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [dSVDensityRationalCompleteProjectiveThresholdEffect_false
    w N ζ k,
    dSVDensityRationalCompleteProjectiveThresholdEffect_false
      w N ξ k]
  let P := dSVDensityRationalPhysicalProjector w ξ k
  let R := dSVDensityRationalPhysicalProjector w ζ k
  change
    (Matrix.trace (P * (1 - R))).re +
        (Matrix.trace ((1 - P) * R)).re =
      (Matrix.trace ((P - R) * (P - R))).re
  have square := dSVProjectorSquaredDifference_trace P R
    (dSVDensityRationalPhysicalProjector_projective w ξ k)
    (dSVDensityRationalPhysicalProjector_projective w ζ k)
  rw [square]
  simp only [Matrix.mul_sub, mul_one, trace_sub, sub_re, Matrix.sub_mul, one_mul]
  ring

theorem dSVDensityRationalActualMixed_escape_ge_diagonal
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ ≤
      dSVDensityRationalActualMixedSuccessMass w N ξ ζ +
        dSVDensityRationalActualMixedAsynchronousMass
          w N ξ ζ := by
  have loss := dSVDensityRationalPhysicalMixedBornSuccess_loss_le
    grid dimension w ξ ζ
  rw [← dSVDensityRationalActualMixedSuccessMass_eq
      grid dimension w ξ ζ,
    ← dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
      w N ξ ζ] at loss
  linarith

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/-- The rank map for DSV density rational physical mixed accepted intersection. -/
def dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : Fin (N + 1) :=
  ⟨min
      (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val
      (dSVDensityRationalPhysicalAcceptedRank w N ζ j).val,
    by
      have left :=
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).isLt
      have right :=
        (dSVDensityRationalPhysicalAcceptedRank w N ζ j).isLt
      omega⟩

theorem dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) (k : Fin N) :
    (dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true ∧
      dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = true) ↔
      k.val <
        (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
          w N ξ ζ i j).val := by
  rw [dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
    width grid ξ i k,
    dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
      width grid ζ j k]
  change _ ↔ k.val < min
    (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val
    (dSVDensityRationalPhysicalAcceptedRank w N ζ j).val
  omega

theorem dSVDensityRationalPhysicalMixedAcceptedThreshold_count
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    (Finset.univ.filter fun k : Fin N =>
      dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true).card =
      (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j).val := by
  let rank :=
    dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j
  have bound : rank.val ≤ N := by
    have actual := rank.isLt
    omega
  have same :
      (Finset.univ.filter fun k : Fin N =>
        dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = true ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true) =
        Finset.univ.filter fun k : Fin N => k.val < rank.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
      width grid ξ ζ i j k
  rw [same, Fin.card_filter_val_lt, min_eq_right bound]

theorem dSVDensityRationalMixedAcceptedPrefix_norm_sq
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d) :
    ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ true true‖ ^ 2 =
      (∑ i : Fin d, ∑ j : Fin d,
        spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j *
          ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
            w N ξ ζ i j).val : ℝ)) /
        ((d : ℝ) * (N : ℝ)) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveOutcome_norm_sq_eq]
  congr 1
  let overlap := spectralAtomOverlap
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ)
  have expand (k : Fin N) :
      (Matrix.trace
        ((dSVDensityRationalLeftProjectiveThresholdPOVM
            w N k ξ).effect true *
         (dSVDensityRationalLeftProjectiveThresholdPOVM
            w N k ζ).effect true)).re =
        ∑ i : Fin d, ∑ j : Fin d,
          if dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) = true ∧
            dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues j) = true
          then overlap i j else 0 := by
    rw [← dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct]
    exact dSVDensityRationalMixedSpectralAtomBlock_trace_eq
      w N ξ ζ true true k
  simp_rw [expand]
  calc
    (∑ k : Fin N, ∑ i : Fin d, ∑ j : Fin d,
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true
      then overlap i j else 0) =
      ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin N,
        if dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = true ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true
        then overlap i j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, ∑ j : Fin d,
        overlap i j *
          ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
            w N ξ ζ i j).val : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have counted := congrArg (fun r : ℕ => (r : ℝ))
        (dSVDensityRationalPhysicalMixedAcceptedThreshold_count
          width grid ξ ζ i j)
      calc
        (∑ k : Fin N,
          if dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) = true ∧
            dSVDensityRationalProjectiveThresholdBin w N k
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues j) = true
          then overlap i j else 0) =
          overlap i j *
            ((Finset.univ.filter fun k : Fin N =>
              dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = true ∧
                dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ζ).isHermitian.eigenvalues j) = true).card : ℝ) := by
            rw [← Finset.sum_boole]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            split_ifs <;> simp
        _ = _ := by rw [counted]

/--
The DSV density rational physical mixed accepted prefix work construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPhysicalMixedAcceptedPrefixWork
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    EuclideanSpace ℂ (Fin N × Fin N) :=
  dSVCanonicalFailurePrefix
    (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j)

theorem dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    ‖dSVDensityRationalPhysicalMixedAcceptedPrefixWork
        w N ξ ζ i j‖ ^ 2 =
      ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j).val : ℝ) := by
  exact dSVCanonicalFailurePrefix_norm_sq
    (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def dSVDensityRationalCanonicalPrefixMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true
      then (1 : ℂ) else 0

theorem dSVDensityRationalCanonicalPrefixMask_transpose
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    (dSVDensityRationalCanonicalPrefixMask
      w N ξ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ξ := by
  classical
  simp only [dSVDensityRationalCanonicalPrefixMask, blockDiagonal'_diagonal, diagonal_transpose]

theorem dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Matrix.blockDiagonal'
        (dSVDensityRationalPhysicalProjector w ξ) =
      (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalCanonicalPrefixMask w N ξ *
        (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal'
      (dSVDensityRationalPhysicalProjector w ξ) =
      Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ)) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            Matrix.diagonal fun i : Fin d =>
              if dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = true
              then (1 : ℂ) else 0) *
        Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
              Matrix.unitaryGroup (Fin d) ℂ) :
                Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  apply congrArg Matrix.blockDiagonal'
  funext k
  unfold dSVDensityRationalPhysicalProjector
    dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
  rw [spectralPartitionPOVM_effect_eq_spectralDiagonal]
  rfl

/-- The finite outcome encoding for DSV density rational canonical prefix spectral. -/
def dSVDensityRationalCanonicalPrefixSpectralOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) ⊗ₖ
      (((dSVUniformDensityBobHistoryCopyBasis
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).mulVec
      (ofLp (dSVDensityRationalPhysicalAcceptedOutcome
        w N ξ ζ)))

/-- The measurement effect for DSV density rational complete stopped optional local. -/
def dSVDensityRationalCompleteStoppedOptionalLocalEffect
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    Option Bool → Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ
  | none => 1
  | some outcome =>
      (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect outcome

/-- The finite outcome encoding for DSV density rational complete stopped optional. -/
def dSVDensityRationalCompleteStoppedOptionalOutcome
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (alice bob : Option Bool) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (((dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ξ alice) ⊗ₖ
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ζ bob).transpose).mulVec
      (ofLp (dSVUniformDensityThresholdSharedState N d)))

theorem dSVDensityRationalCompleteStoppedOptionalOutcome_some_some
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (alice bob : Bool) :
    dSVDensityRationalCompleteStoppedOptionalOutcome
        w N ξ ζ (some alice) (some bob) =
      dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ alice bob := by
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_block_action]
  simp only [dSVDensityRationalCompleteStoppedOptionalOutcome,
    dSVDensityRationalCompleteStoppedOptionalLocalEffect,
    dSVDensityRationalCompleteProjectiveBinaryPOVM_effect, blockDiagonal'_transpose]

theorem dSVDensityRationalCompleteStoppedOptionalOutcome_none_none
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalCompleteStoppedOptionalOutcome
        w N ξ ζ none none =
      dSVUniformDensityThresholdSharedState N d := by
  simp only [dSVDensityRationalCompleteStoppedOptionalOutcome,
    dSVDensityRationalCompleteStoppedOptionalLocalEffect, transpose_one, zero_mul, implies_true,
    mul_zero, mul_one, kroneckerMap_one_one, one_mulVec, toLp_ofLp]

/-- The finite schedule for DSV density rational complete stopped optional local. -/
def dSVDensityRationalCompleteStoppedOptionalLocalSchedule
    (L : ℕ) (hit copy : Fin (L + 1)) : Option Bool :=
  if copy.val < L then
    if hit = 0 then some false
    else if copy.val + 1 < hit.val then some false
    else if copy.val + 1 = hit.val then some true
    else none
  else none

theorem dSVDensityRationalCompleteStoppedOptionalLocalSchedule_zero
    (L : ℕ) (copy : Fin (L + 1)) :
    dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L 0 copy =
      if copy.val < L then some false else none := by
  simp only [dSVDensityRationalCompleteStoppedOptionalLocalSchedule, ↓reduceIte]

theorem dSVDensityRationalCompleteStoppedOptionalLocalSchedule_hit
    {L : ℕ} (j : Fin L) :
    dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ j.castSucc = some true := by
  simp only [dSVDensityRationalCompleteStoppedOptionalLocalSchedule, Fin.val_castSucc, j.isLt,
    ↓reduceIte, Fin.succ_ne_zero, Fin.val_succ, lt_self_iff_false]

end

section

open scoped Kronecker ComplexOrder MatrixOrder

/--
The DSV density rational first accept local spectral mask construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalFirstAcceptLocalSpectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  Matrix.blockDiagonal' fun k : Fin N =>
    Matrix.diagonal fun i : Fin d =>
      if dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = outcome
      then (1 : ℂ) else 0

theorem dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    (dSVDensityRationalCompleteProjectiveBinaryPOVM
        w N ξ).effect outcome =
      (((dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalFirstAcceptLocalSpectralMask
          w N ξ outcome *
        (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ξ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveBinaryPOVM_effect,
    dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal'
        (fun k : Fin N =>
          (dSVDensityRationalLeftProjectiveThresholdPOVM
            w N k ξ).effect outcome) =
      Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ)) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            Matrix.diagonal fun i : Fin d =>
              if dSVDensityRationalProjectiveThresholdBin w N k
                  ((dSVSoftBobLeftReducedDensity_posSemidef
                    ξ).isHermitian.eigenvalues i) = outcome
              then (1 : ℂ) else 0) *
        Matrix.blockDiagonal'
          (fun _ : Fin N =>
            (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
              Matrix.unitaryGroup (Fin d) ℂ) :
                Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  apply congrArg Matrix.blockDiagonal'
  funext k
  unfold dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
  rw [spectralPartitionPOVM_effect_eq_spectralDiagonal]
  rfl

theorem dSVDensityRationalFirstAcceptLocalSpectralMask_transpose
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    (dSVDensityRationalFirstAcceptLocalSpectralMask
      w N ξ outcome).transpose =
      dSVDensityRationalFirstAcceptLocalSpectralMask
        w N ξ outcome := by
  classical
  simp only [dSVDensityRationalFirstAcceptLocalSpectralMask, blockDiagonal'_diagonal,
    diagonal_transpose]

theorem
    dSVDensityRationalFirstAcceptPhysicalBobEffect_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ζ : BipartiteUnitVector d) (outcome : Bool) :
    (transposePOVM
        (dSVDensityRationalCompleteProjectiveBinaryPOVM
          w N ζ)).effect outcome =
      (dSVUniformDensityBobHistoryCopyBasis
          (N := N) ζ :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        dSVDensityRationalFirstAcceptLocalSpectralMask
          w N ζ outcome *
        (((dSVUniformDensityBobHistoryCopyBasis
            (N := N) ζ)⁻¹ : Matrix.unitaryGroup
              (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
            Matrix (DSVUniformDensityThresholdLocalIndex N d)
              (DSVUniformDensityThresholdLocalIndex N d) ℂ) := by
  change
    ((dSVDensityRationalCompleteProjectiveBinaryPOVM
      w N ζ).effect outcome).transpose = _
  rw [dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
    w N ζ outcome, Matrix.transpose_mul, Matrix.transpose_mul,
    dSVDensityRationalFirstAcceptLocalSpectralMask_transpose,
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose,
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose]
  simp only [UnitaryGroup.inv_val, Matrix.mul_assoc]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV density rational first accept actual tensor basis construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalFirstAcceptActualTensorBasis
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  controlledFiniteTensorLocalUnitary
    (fun (_stop : Fin (L + 1)) (_copy : Fin (L + 1)) => U)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem tensorEmbezzlementTarget_sub_norm
    {d n : ℕ} (positive : 0 < n)
    (ξ ζ : BipartiteUnitVector d) :
    ‖tensorEmbezzlementTarget (n := n) ξ -
      tensorEmbezzlementTarget (n := n) ζ‖ =
      ‖ξ.val - ζ.val‖ := by
  classical
  let e : ((Fin d × Fin d) × (Fin n × Fin n)) ≃
      (Fin (d * n) × Fin (d * n)) :=
    (Equiv.prodProdProdComm (Fin d) (Fin d) (Fin n) (Fin n)).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  have point (q : (Fin d × Fin d) × (Fin n × Fin n)) :
      (tensorEmbezzlementTarget (n := n) ξ -
        tensorEmbezzlementTarget (n := n) ζ) (e q) =
        (ξ.val q.1 - ζ.val q.1) *
          embezzlementState n q.2 := by
    rcases q with ⟨⟨a, b⟩, ⟨i, j⟩⟩
    change
      ξ.val
          ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).1,
            (finProdFinEquiv.symm (finProdFinEquiv (b, j))).1) *
          embezzlementState n
            ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).2,
              (finProdFinEquiv.symm (finProdFinEquiv (b, j))).2) -
        ζ.val
          ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).1,
            (finProdFinEquiv.symm (finProdFinEquiv (b, j))).1) *
          embezzlementState n
            ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).2,
              (finProdFinEquiv.symm (finProdFinEquiv (b, j))).2) = _
    simp only [Equiv.symm_apply_apply]
    ring
  have reindex :
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖(tensorEmbezzlementTarget (n := n) ξ -
          tensorEmbezzlementTarget (n := n) ζ) q‖ ^ 2) =
        ∑ q : (Fin d × Fin d) × (Fin n × Fin n),
          ‖(ξ.val q.1 - ζ.val q.1) *
            embezzlementState n q.2‖ ^ 2 := by
    calc
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖(tensorEmbezzlementTarget (n := n) ξ -
          tensorEmbezzlementTarget (n := n) ζ) q‖ ^ 2) =
          ∑ q : (Fin d × Fin d) × (Fin n × Fin n),
            ‖(tensorEmbezzlementTarget (n := n) ξ -
              tensorEmbezzlementTarget (n := n) ζ)
                (e q)‖ ^ 2 :=
            (Equiv.sum_comp e
              (fun q : Fin (d * n) × Fin (d * n) =>
                ‖(tensorEmbezzlementTarget (n := n) ξ -
                  tensorEmbezzlementTarget (n := n) ζ)
                    q‖ ^ 2)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        rw [point q]
  have factor :
      (∑ q : (Fin d × Fin d) × (Fin n × Fin n),
        ‖(ξ.val q.1 - ζ.val q.1) *
          embezzlementState n q.2‖ ^ 2) =
        (∑ q : Fin d × Fin d, ‖(ξ.val - ζ.val) q‖ ^ 2) *
          (∑ q : Fin n × Fin n,
            ‖embezzlementState n q‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [norm_mul, mul_pow]
    exact (Fintype.sum_mul_sum
      (fun q : Fin d × Fin d => ‖(ξ.val - ζ.val) q‖ ^ 2)
      (fun q : Fin n × Fin n =>
        ‖embezzlementState n q‖ ^ 2)).symm
  have squares :
      ‖tensorEmbezzlementTarget (n := n) ξ -
        tensorEmbezzlementTarget (n := n) ζ‖ ^ 2 =
        ‖ξ.val - ζ.val‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, reindex, factor,
      ← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq,
      embezzlementState_norm n positive]
    ring
  nlinarith [norm_nonneg
    (tensorEmbezzlementTarget (n := n) ξ -
      tensorEmbezzlementTarget (n := n) ζ),
    norm_nonneg (ξ.val - ζ.val)]

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVBobTargetLocalHarmonicCleanup_stable
    {d n : ℕ} (hn : 0 < n)
    (U V : Matrix.unitaryGroup (Fin (d * n)) ℂ)
    (ξ ζ : BipartiteUnitVector d)
    (ε : ℝ)
    (clean :
      ‖localUnitaryAction U V
          (tensorEmbezzlementTarget (n := n) ζ) -
        embezzlementState (d * n)‖ ≤ ε) :
    ‖localUnitaryAction U V
        (tensorEmbezzlementTarget (n := n) ξ) -
      embezzlementState (d * n)‖ ≤
        ‖ξ.val - ζ.val‖ + ε := by
  let source := localUnitaryAction U V
    (tensorEmbezzlementTarget (n := n) ξ)
  let reference := localUnitaryAction U V
    (tensorEmbezzlementTarget (n := n) ζ)
  let residual := embezzlementState (d * n)
  have preserved : ‖source - reference‖ = ‖ξ.val - ζ.val‖ := by
    dsimp [source, reference]
    rw [← localUnitaryAction_sub,
      localUnitaryAction_norm,
      tensorEmbezzlementTarget_sub_norm hn]
  have triangle : ‖source - residual‖ ≤
      ‖source - reference‖ + ‖reference - residual‖ := by
    simpa only [dist_eq_norm] using dist_triangle source reference residual
  change ‖source - residual‖ ≤ ‖ξ.val - ζ.val‖ + ε
  calc
    ‖source - residual‖ ≤
        ‖source - reference‖ + ‖reference - residual‖ := triangle
    _ ≤ ‖ξ.val - ζ.val‖ + ε := by
      rw [preserved]
      simpa only [add_comm] using add_le_add_left
        (show ‖reference - residual‖ ≤ ε by
          simpa only [reference, residual] using clean)
        ‖ξ.val - ζ.val‖

theorem dSVBobTargetLocalUniformHarmonicWorkCleanup
    {T : Type*}
    (d : ℕ) (dimension : 0 < d)
    (work : T → BipartiteUnitVector d)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ (A B : T → Matrix.unitaryGroup (Fin (d * n)) ℂ),
        (∀ ζ : T,
          ‖localUnitaryAction (A ζ) (B ζ)
              (tensorEmbezzlementTarget (n := n) (work ζ)) -
            embezzlementState (d * n)‖ ≤ ε) ∧
        (∀ ξ ζ : T,
          ‖localUnitaryAction (A ζ) (B ζ)
              (tensorEmbezzlementTarget (n := n) (work ξ)) -
            embezzlementState (d * n)‖ ≤
              ‖(work ξ).val - (work ζ).val‖ + ε) := by
  classical
  obtain ⟨n, positive, universal⟩ :=
    exists_proofUniversalHarmonicCatalyst
      d dimension ε precision
  have each (ζ : T) :
      ∃ U V : Matrix.unitaryGroup (Fin (d * n)) ℂ,
        ‖localUnitaryAction U V
            (embezzlementState (d * n)) -
          tensorEmbezzlementTarget (n := n)
            (work ζ)‖ ≤ ε :=
    universal (work ζ)
  choose U V prepared using each
  refine ⟨n, positive,
    (fun ζ => (U ζ)⁻¹),
    (fun ζ => (V ζ)⁻¹), ?_, ?_⟩
  · intro ζ
    rw [harmonicCoherentSharedResource_inverseAbsorption_distance]
    exact prepared ζ
  · intro ξ ζ
    apply dSVBobTargetLocalHarmonicCleanup_stable
      positive ((U ζ)⁻¹) ((V ζ)⁻¹)
      (work ξ) (work ζ) ε
    rw [harmonicCoherentSharedResource_inverseAbsorption_distance]
    exact prepared ζ

theorem dSVDensityRationalCanonicalUnitPrefix_relative_distance_sq
    {N : ℕ} (grid : 0 < N) (r s : Fin (N + 1)) :
    ‖(dSVCanonicalFailureUnitRankFamily N grid r).val -
        (dSVCanonicalFailureUnitRankFamily N grid s).val‖ ^ 2 ≤
      4 * |(r.val : ℝ) - (s.val : ℝ)| /
        (max 1 (min r.val s.val) : ℕ) := by
  classical
  let x : ℝ :=
    ‖(dSVCanonicalFailureUnitRankFamily N grid r).val -
      (dSVCanonicalFailureUnitRankFamily N grid s).val‖
  let y : ℝ :=
    ‖dSVCanonicalFailurePrefix r -
      dSVCanonicalFailurePrefix s‖
  have x_nonnegative : 0 ≤ x := norm_nonneg _
  have y_nonnegative : 0 ≤ y := norm_nonneg _
  have y_squared : y ^ 2 = |(r.val : ℝ) - (s.val : ℝ)| :=
    dSVCanonicalFailurePrefix_sub_norm_sq r s
  by_cases zero : r.val = 0
  · by_cases zero_s : s.val = 0
    · have same : r = s := Fin.ext (zero.trans zero_s.symm)
      subst s
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        abs_zero, mul_zero, min_self, Nat.cast_max, Nat.cast_one, zero_div, Std.le_refl]
    · have s_positive : 0 < s.val := Nat.pos_of_ne_zero zero_s
      have s_one : (1 : ℝ) ≤ (s.val : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr zero_s)
      have x_two : x ≤ 2 := by
        dsimp [x]
        calc
          _ ≤ ‖(dSVCanonicalFailureUnitRankFamily
                N grid r).val‖ +
              ‖(dSVCanonicalFailureUnitRankFamily
                N grid s).val‖ := norm_sub_le _ _
          _ = 2 := by
            rw [(dSVCanonicalFailureUnitRankFamily
              N grid r).property,
              (dSVCanonicalFailureUnitRankFamily
                N grid s).property]
            norm_num
      have magnitude :
          |(r.val : ℝ) - (s.val : ℝ)| = (s.val : ℝ) := by
        simp only [zero, CharP.cast_eq_zero, zero_sub, abs_neg, Nat.abs_cast]
      have denominator : max 1 (min r.val s.val) = 1 := by
        simp only [zero, zero_le, inf_of_le_left, sup_of_le_left]
      change x ^ 2 ≤ _
      rw [magnitude, denominator]
      norm_num only [Nat.cast_one, div_one]
      nlinarith [sq_nonneg x]
  · have r_positive_nat : 0 < r.val := Nat.pos_of_ne_zero zero
    have r_positive : (0 : ℝ) < r.val := by
      exact_mod_cast r_positive_nat
    have root_positive : 0 < Real.sqrt (r.val : ℝ) :=
      Real.sqrt_pos.mpr r_positive
    have raw_nonzero : dSVCanonicalFailurePrefix r ≠ 0 := by
      intro vanished
      have mass := dSVCanonicalFailurePrefix_norm_sq r
      rw [vanished] at mass
      norm_num at mass
      exact zero (by exact_mod_cast mass.symm)
    have normalized := normalizeOrDefault_sub_le
      (embezzlementState N)
      (dSVCanonicalFailurePrefix r)
      (dSVCanonicalFailurePrefix s)
      (embezzlementState_norm N grid)
      raw_nonzero
    change x ≤ 2 * y /
      ‖dSVCanonicalFailurePrefix r‖ at normalized
    rw [dSVCanonicalFailurePrefix_norm_eq_sqrt]
      at normalized
    have linear : x * Real.sqrt (r.val : ℝ) ≤ 2 * y :=
      (le_div_iff₀ root_positive).mp normalized
    have square := mul_self_le_mul_self
      (mul_nonneg x_nonnegative root_positive.le) linear
    have weighted : x ^ 2 * (r.val : ℝ) ≤
        4 * |(r.val : ℝ) - (s.val : ℝ)| := by
      have root_square := Real.sq_sqrt r_positive.le
      nlinarith [y_squared]
    have rank_relative :
        x ^ 2 ≤ 4 * |(r.val : ℝ) - (s.val : ℝ)| /
          (r.val : ℝ) :=
      (le_div_iff₀ r_positive).mpr weighted
    have denominator_positive :
        (0 : ℝ) < (max 1 (min r.val s.val) : ℕ) := by
      exact_mod_cast (show 0 < max 1 (min r.val s.val) by omega)
    have denominator_le :
        ((max 1 (min r.val s.val) : ℕ) : ℝ) ≤ (r.val : ℝ) := by
      exact_mod_cast
        (max_le (Nat.one_le_iff_ne_zero.mpr zero)
          (min_le_left r.val s.val))
    change x ^ 2 ≤ _
    calc
      x ^ 2 ≤ 4 * |(r.val : ℝ) - (s.val : ℝ)| /
          (r.val : ℝ) := rank_relative
      _ ≤ 4 * |(r.val : ℝ) - (s.val : ℝ)| /
          (max 1 (min r.val s.val) : ℕ) := by
            apply (div_le_div_iff₀ r_positive denominator_positive).mpr
            exact mul_le_mul_of_nonneg_left denominator_le
              (mul_nonneg (by norm_num) (abs_nonneg _))

theorem dSVDensityRationalPublicBucketLocalHarmonicCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N D : ℕ} (dimension : 0 < N)
    (work : Fin D → BipartiteUnitVector N)
    (bucket : Ω → Fin D → I)
    (representative : Ω → I → Fin D)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin D),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (tensorEmbezzlementTarget (n := n) (work r)) -
            embezzlementState (N * n)‖ ^ 2 ≤
              2 * ε ^ 2 +
              2 * ‖(work r).val -
                (work (representative phase (bucket phase r))).val‖ ^ 2 +
              4 * (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1) := by
  classical
  obtain ⟨n, positive, A, B, diagonal, _stable⟩ :=
    dSVBobTargetLocalUniformHarmonicWorkCleanup
      N dimension
      (fun q : Ω × I => work (representative q.1 q.2))
      ε precision
  refine ⟨n, positive,
    fun phase label => A (phase, label),
    fun phase label => B (phase, label), ?_⟩
  intro phase r s
  by_cases same : bucket phase r = bucket phase s
  · have clean := diagonal (phase, bucket phase r)
    have stable := dSVBobTargetLocalHarmonicCleanup_stable
      positive
      (A (phase, bucket phase r))
      (B (phase, bucket phase r))
      (work r)
      (work (representative phase (bucket phase r)))
      ε clean
    have actual :
        ‖localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)‖ ≤
            ‖(work r).val -
              (work (representative phase (bucket phase r))).val‖ + ε := by
      simpa only [same] using stable
    simp only [ite_eq_left same, mul_zero, add_zero]
    nlinarith [
      norm_nonneg
        (localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)),
      norm_nonneg ((work r).val -
        (work (representative phase (bucket phase r))).val),
      sq_nonneg
        (‖(work r).val -
          (work (representative phase (bucket phase r))).val‖ - ε)]
  · have bound :
        ‖localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)‖ ≤ 2 := by
      calc
        _ ≤ ‖localUnitaryAction
              (A (phase, bucket phase r))
              (B (phase, bucket phase s))
              (tensorEmbezzlementTarget (n := n) (work r))‖ +
            ‖embezzlementState (N * n)‖ := norm_sub_le _ _
        _ = 2 := by
          rw [localUnitaryAction_norm,
            tensorEmbezzlementTarget_norm positive,
            embezzlementState_norm (N * n)
              (Nat.mul_pos dimension positive)]
          norm_num
    simp only [ite_eq_right same, mul_one]
    nlinarith [
      norm_nonneg
        (localUnitaryAction
            (A (phase, bucket phase r))
            (B (phase, bucket phase s))
            (tensorEmbezzlementTarget (n := n) (work r)) -
          embezzlementState (N * n)),
      sq_nonneg ε,
      sq_nonneg
        ‖(work r).val -
          (work (representative phase (bucket phase r))).val‖]

theorem dSVDensityRationalPublicBucketCanonicalPrefixCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N : ℕ} (grid : 0 < N)
    (bucket : Ω → Fin (N + 1) → I)
    (representative : Ω → I → Fin (N + 1))
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin (N + 1)),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (tensorEmbezzlementTarget (n := n)
                (dSVCanonicalFailureUnitRankFamily N grid r)) -
            embezzlementState (N * n)‖ ^ 2 ≤
              2 * ε ^ 2 +
              8 * |(r.val : ℝ) -
                ((representative phase (bucket phase r)).val : ℝ)| /
                (max 1
                  (min r.val
                    (representative phase (bucket phase r)).val) : ℕ) +
              4 * (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1) := by
  obtain ⟨n, positive, A, B, accurate⟩ :=
    dSVDensityRationalPublicBucketLocalHarmonicCleanup_sq
      grid (dSVCanonicalFailureUnitRankFamily N grid)
      bucket representative ε precision
  refine ⟨n, positive, A, B, ?_⟩
  intro phase r s
  have actual := accurate phase r s
  have relative :=
    dSVDensityRationalCanonicalUnitPrefix_relative_distance_sq
      grid r (representative phase (bucket phase r))
  calc
    _ ≤ 2 * ε ^ 2 +
        2 * ‖(dSVCanonicalFailureUnitRankFamily N grid r).val -
          (dSVCanonicalFailureUnitRankFamily N grid
            (representative phase (bucket phase r))).val‖ ^ 2 +
        4 * (if bucket phase r = bucket phase s
          then (0 : ℝ) else 1) := actual
    _ ≤ 2 * ε ^ 2 +
        2 * (4 * |(r.val : ℝ) -
          ((representative phase (bucket phase r)).val : ℝ)| /
            (max 1
              (min r.val
                (representative phase (bucket phase r)).val) : ℕ)) +
        4 * (if bucket phase r = bucket phase s
          then (0 : ℝ) else 1) := by
      gcongr
    _ = _ := by ring

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The transcript representation for DSV density rational public bucket coherent phase. -/
def dSVDensityRationalPublicBucketCoherentPhaseHistory
    {H : Type*} (B : ℕ)
    (history : EuclideanSpace ℂ (H × H)) :
    EuclideanSpace ℂ ((Fin B × H) × (Fin B × H)) :=
  toLp 2 fun q : (Fin B × H) × (Fin B × H) =>
    ePRState B (q.1.1, q.2.1) *
      history (q.1.2, q.2.2)

theorem dSVDensityRationalPublicBucketCoherentPhaseHistory_apply
    {H : Type*} (B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (φ ψ : Fin B) (a b : H) :
    dSVDensityRationalPublicBucketCoherentPhaseHistory
        B history ((φ, a), (ψ, b)) =
      ePRState B (φ, ψ) * history (a, b) := by
  rfl

theorem dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
    {H : Type*} {B : ℕ}
    (positive : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (φ ψ : Fin B) (a b : H) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseHistory
        B history ((φ, a), (ψ, b))‖ ^ 2 =
      (if φ = ψ then (B : ℝ)⁻¹ else 0) *
        ‖history (a, b)‖ ^ 2 := by
  rw [dSVDensityRationalPublicBucketCoherentPhaseHistory_apply,
    norm_mul, mul_pow]
  by_cases same : φ = ψ
  · subst ψ
    simp only [ePRState, ↓reduceIte]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ B)]
  · simp only [ePRState, ofReal_inv, same, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul]

/-- The quantum state representing DSV density rational public bucket coherent phase sigma. -/
def dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    {H : Type*} {m : ℕ} (B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (work : Fin B → H → H →
      EuclideanSpace ℂ (Fin m × Fin m)) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × H, Fin m) ×
       (Σ _ : Fin B × H, Fin m)) :=
  dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    (dSVDensityRationalPublicBucketCoherentPhaseHistory
      B history)
    (fun a b => work a.1 a.2 b.2)

/-- The unitary operator implementing DSV density rational public bucket coherent phase local. -/
def dSVDensityRationalPublicBucketCoherentPhaseLocalUnitary
    {H I : Type*} [Fintype H] [DecidableEq H]
     {B D m : ℕ}
    (rank : H → Fin D)
    (bucket : Fin B → Fin D → I)
    (A : Fin B → I → Matrix.unitaryGroup (Fin m) ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin B × H, Fin m) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun q : Fin B × H => A q.1 (bucket q.1 (rank q.2)))

theorem dSVDensityRationalPublicBucketCoherentPhaseSigmaReset_distance_sq
    {H I : Type*} [Fintype H] [DecidableEq H]
    {B D m : ℕ}
    (phase_positive : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (rankA rankB : H → Fin D)
    (bucket : Fin B → Fin D → I)
    (A C : Fin B → I → Matrix.unitaryGroup (Fin m) ℂ)
    (work target : Fin B → H → H →
      EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVUniformDensityPhysicalAsyncSigmaContinuation
          (fun q : Fin B × H =>
            A q.1 (bucket q.1 (rankA q.2)))
          (fun q : Fin B × H =>
            C q.1 (bucket q.1 (rankB q.2)))
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B history work) -
        dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B history target‖ ^ 2 =
      (∑ φ : Fin B, ∑ a : H, ∑ b : H,
        ‖history (a, b)‖ ^ 2 *
          ‖localUnitaryAction
              (A φ (bucket φ (rankA a)))
              (C φ (bucket φ (rankB b)))
              (work φ a b) - target φ a b‖ ^ 2) /
        (B : ℝ) := by
  classical
  unfold dSVDensityRationalPublicBucketCoherentPhaseSigmaState
  rw [dSVUniformDensityCorrectedMatchedSigmaControlledReset_distance_sq]
  simp_rw [Fintype.sum_prod_type]
  change
    (∑ φ : Fin B, ∑ a : H,
      ∑ ψ : Fin B, ∑ b : H,
        ‖dSVDensityRationalPublicBucketCoherentPhaseHistory
            B history ((φ, a), (ψ, b))‖ ^ 2 *
          ‖localUnitaryAction
              (A φ (bucket φ (rankA a)))
              (C ψ (bucket ψ (rankB b)))
              (work φ a b) - target φ a b‖ ^ 2) = _
  simp_rw [
    dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
      phase_positive]
  calc
    (∑ φ : Fin B, ∑ a : H,
      ∑ ψ : Fin B, ∑ b : H,
        ((if φ = ψ then (B : ℝ)⁻¹ else 0) *
          ‖history (a, b)‖ ^ 2) *
          ‖localUnitaryAction
              (A φ (bucket φ (rankA a)))
              (C ψ (bucket ψ (rankB b)))
              (work φ a b) - target φ a b‖ ^ 2) =
      ∑ φ : Fin B, ∑ a : H, ∑ b : H,
        (B : ℝ)⁻¹ *
          (‖history (a, b)‖ ^ 2 *
            ‖localUnitaryAction
                (A φ (bucket φ (rankA a)))
                (C φ (bucket φ (rankB b)))
                (work φ a b) - target φ a b‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro φ _
      apply Finset.sum_congr rfl
      intro a _
      simp only [ite_mul, zero_mul, mul_assoc, sum_ite_irrel, sum_const_zero, sum_ite_eq,
        mem_univ, ↓reduceIte]
    _ = (B : ℝ)⁻¹ *
        (∑ φ : Fin B, ∑ a : H, ∑ b : H,
          ‖history (a, b)‖ ^ 2 *
            ‖localUnitaryAction
                (A φ (bucket φ (rankA a)))
                (C φ (bucket φ (rankB b)))
                (work φ a b) - target φ a b‖ ^ 2) := by
      simp_rw [Finset.mul_sum]
    _ = _ := by ring

end

section

open scoped BigOperators ComplexOrder MatrixOrder

theorem dSVDensityRationalPublicLogRank_real_log_bound
    {r s : ℝ} (positive_r : 0 < r) (positive_s : 0 < s) :
    min r s * |Real.log r - Real.log s| ≤ |r - s| := by
  have in_order :
      ∀ {x y : ℝ}, 0 < x → 0 < y → x ≤ y →
        min x y * |Real.log x - Real.log y| ≤ |x - y| := by
    intro x y positive_x positive_y ordered
    have logarithmic :=
      Real.log_le_sub_one_of_pos (div_pos positive_y positive_x)
    have monotone := Real.log_le_log positive_x ordered
    have bound : x * (Real.log y - Real.log x) ≤ y - x := by
      calc
        x * (Real.log y - Real.log x) =
            x * Real.log (y / x) := by
          rw [Real.log_div positive_y.ne' positive_x.ne']
        _ ≤ x * (y / x - 1) :=
          mul_le_mul_of_nonneg_left logarithmic positive_x.le
        _ = y - x := by
          field_simp
    calc
      min x y * |Real.log x - Real.log y| =
          x * (Real.log y - Real.log x) := by
        rw [min_eq_left ordered,
          abs_of_nonpos (sub_nonpos.mpr monotone)]
        ring
      _ ≤ y - x := bound
      _ = |x - y| := by
        rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
        ring
  rcases le_total r s with ordered | ordered
  · exact in_order positive_r positive_s ordered
  · simpa only [ge_iff_le, min_comm, abs_sub_comm] using
      in_order positive_s positive_r ordered

theorem dSVDensityRationalPublicLogRank_zeroSafe_nat_bound
    (r s : ℕ) :
    min (r : ℝ) (s : ℝ) *
        |Real.log ((max 1 r : ℕ) : ℝ) -
          Real.log ((max 1 s : ℕ) : ℝ)| ≤
      |(r : ℝ) - (s : ℝ)| := by
  by_cases zero_r : r = 0
  · simp only [zero_r, CharP.cast_eq_zero, Nat.cast_nonneg, inf_of_le_left, zero_le,
      sup_of_le_left, Nat.cast_one, Real.log_one, Nat.cast_max, zero_sub, abs_neg, zero_mul,
      Nat.abs_cast]
  by_cases zero_s : s = 0
  · simp only [zero_s, CharP.cast_eq_zero, Nat.cast_nonneg, inf_of_le_right, Nat.cast_max,
      Nat.cast_one, zero_le, sup_of_le_left, Real.log_one, sub_zero, zero_mul, Nat.abs_cast]
  have positive_r : 0 < r := Nat.pos_of_ne_zero zero_r
  have positive_s : 0 < s := Nat.pos_of_ne_zero zero_s
  have one_r : 1 ≤ r := positive_r
  have one_s : 1 ≤ s := positive_s
  simpa only [max_eq_right one_r, max_eq_right one_s, ge_iff_le] using
    (dSVDensityRationalPublicLogRank_real_log_bound
      (by exact_mod_cast positive_r : (0 : ℝ) < r)
      (by exact_mod_cast positive_s : (0 : ℝ) < s))

theorem dSVDensityRationalPublicLogRank_zeroSafe_fin_bound
    {N : ℕ} (r s : Fin (N + 1)) :
    min (r.val : ℝ) (s.val : ℝ) *
        |Real.log ((max 1 r.val : ℕ) : ℝ) -
          Real.log ((max 1 s.val : ℕ) : ℝ)| ≤
      |(r.val : ℝ) - (s.val : ℝ)| :=
  dSVDensityRationalPublicLogRank_zeroSafe_nat_bound
    r.val s.val

/--
The DSV density rational public log rank fine label construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPublicLogRankFineLabel
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) : ℕ :=
  Nat.floor ((Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ))

/-- The probability weight for DSV density rational public log rank phase. -/
def dSVDensityRationalPublicLogRankPhaseWeight
    (B : ℕ) (_ : Fin B) : ℝ :=
  1 / (B : ℝ)

theorem dSVDensityRationalPublicLogRankPhaseWeight_sum
    {B : ℕ} (positive : 0 < B) :
    (∑ phase : Fin B,
      dSVDensityRationalPublicLogRankPhaseWeight B phase) = 1 := by
  have real_positive : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast positive
  simp only [dSVDensityRationalPublicLogRankPhaseWeight, one_div, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, ne_eq, real_positive.ne', not_false_eq_true, mul_inv_cancel₀]

/--
The DSV density rational public log rank bucket construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPublicLogRankBucket
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) : Option ℕ :=
  if r.val = 0 then none
  else some
    ((dSVDensityRationalPublicLogRankFineLabel Q r + phase.val) / B)

theorem dSVDensityRationalPublicLogRankBucket_fineLabel_sub_lt
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r s : Fin (N + 1))
    (nonzero_r : r.val ≠ 0) (nonzero_s : s.val ≠ 0)
    (same :
      dSVDensityRationalPublicLogRankBucket Q phase r =
        dSVDensityRationalPublicLogRankBucket Q phase s) :
    |(dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) -
      (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ)| <
      (B : ℝ) := by
  have positive : 0 < B := by
    have bound := phase.isLt
    omega
  have quotient :
      (dSVDensityRationalPublicLogRankFineLabel Q r +
        phase.val) / B =
      (dSVDensityRationalPublicLogRankFineLabel Q s +
        phase.val) / B := by
    simpa only [dSVDensityRationalPublicLogRankBucket, nonzero_r, ↓reduceIte, nonzero_s,
      Option.some.injEq] using same
  have remainder_r := Nat.mod_lt
    (dSVDensityRationalPublicLogRankFineLabel Q r + phase.val)
    positive
  have remainder_s := Nat.mod_lt
    (dSVDensityRationalPublicLogRankFineLabel Q s + phase.val)
    positive
  have reconstruction_r := Nat.mod_add_div
    (dSVDensityRationalPublicLogRankFineLabel Q r + phase.val) B
  have reconstruction_s := Nat.mod_add_div
    (dSVDensityRationalPublicLogRankFineLabel Q s + phase.val) B
  rw [quotient] at reconstruction_r
  rcases le_total
    (dSVDensityRationalPublicLogRankFineLabel Q r)
    (dSVDensityRationalPublicLogRankFineLabel Q s)
    with ordered | ordered
  · have difference :
        dSVDensityRationalPublicLogRankFineLabel Q s -
          dSVDensityRationalPublicLogRankFineLabel Q r < B := by
      omega
    have real_difference :
        (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ) -
          (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) <
            (B : ℝ) := by
      exact_mod_cast difference
    rw [abs_of_nonpos
      (sub_nonpos.mpr (by exact_mod_cast ordered))]
    linarith
  · have difference :
        dSVDensityRationalPublicLogRankFineLabel Q r -
          dSVDensityRationalPublicLogRankFineLabel Q s < B := by
      omega
    have real_difference :
        (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) -
          (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ) <
            (B : ℝ) := by
      exact_mod_cast difference
    rw [abs_of_nonneg
      (sub_nonneg.mpr (by exact_mod_cast ordered))]
    exact real_difference

theorem dSVDensityRationalPublicLogRank_logCoordinate_nonneg
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) :
    0 ≤ (Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) := by
  apply mul_nonneg (Nat.cast_nonneg Q)
  apply Real.log_nonneg
  exact_mod_cast (le_max_left 1 r.val)

theorem dSVDensityRationalPublicLogRankFineLabel_bounds
    {N : ℕ} (Q : ℕ) (r : Fin (N + 1)) :
    (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) ≤
        (Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) ∧
      (Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) <
        (dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) + 1 := by
  constructor
  · exact Nat.floor_le
      (dSVDensityRationalPublicLogRank_logCoordinate_nonneg Q r)
  · exact Nat.lt_floor_add_one _

theorem dSVDensityRationalPublicLogRankBucket_log_sub_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r s : Fin (N + 1))
    (nonzero_r : r.val ≠ 0) (nonzero_s : s.val ≠ 0)
    (same :
      dSVDensityRationalPublicLogRankBucket Q phase r =
        dSVDensityRationalPublicLogRankBucket Q phase s) :
    |Real.log ((max 1 r.val : ℕ) : ℝ) -
      Real.log ((max 1 s.val : ℕ) : ℝ)| <
      ((B : ℝ) + 1) / (Q : ℝ) := by
  have real_Q : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast positive_Q
  have rank_bounds :=
    dSVDensityRationalPublicLogRankFineLabel_bounds Q r
  have other_bounds :=
    dSVDensityRationalPublicLogRankFineLabel_bounds Q s
  have bucket_bounds :=
    dSVDensityRationalPublicLogRankBucket_fineLabel_sub_lt
      Q phase r s nonzero_r nonzero_s same
  apply (lt_div_iff₀ real_Q).2
  rcases le_total
      (Real.log ((max 1 r.val : ℕ) : ℝ))
      (Real.log ((max 1 s.val : ℕ) : ℝ)) with ordered | ordered
  · rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
    have integer_order := (abs_lt.mp bucket_bounds).1
    linarith [rank_bounds.1, other_bounds.2]
  · rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
    have integer_order := (abs_lt.mp bucket_bounds).2
    linarith [rank_bounds.2, other_bounds.1]

private def dSVDensityRationalPublicLogRankBucketFiber
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun r : Fin (N + 1) =>
    r.val ≠ 0 ∧
      dSVDensityRationalPublicLogRankBucket Q phase r = label

theorem dSVDensityRationalPublicLogRankBucketFiber_mem
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ)
    (r : Fin (N + 1)) :
    r ∈ dSVDensityRationalPublicLogRankBucketFiber
        Q phase label ↔
      r.val ≠ 0 ∧
        dSVDensityRationalPublicLogRankBucket Q phase r = label := by
  simp only [dSVDensityRationalPublicLogRankBucketFiber, ne_eq, Fin.val_eq_zero_iff, mem_filter,
    mem_univ, true_and]

/--
The DSV density rational public log rank bucket representative construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPublicLogRankBucketRepresentative
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ) :
    Fin (N + 1) :=
  if present :
    (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).Nonempty
  then (dSVDensityRationalPublicLogRankBucketFiber
      Q phase label).min' present
  else 0

theorem dSVDensityRationalPublicLogRankBucketRepresentative_mem
    {N B : ℕ} (Q : ℕ) (phase : Fin B) (label : Option ℕ)
    (present :
      (dSVDensityRationalPublicLogRankBucketFiber
        (N := N) Q phase label).Nonempty) :
    dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase label ∈
      dSVDensityRationalPublicLogRankBucketFiber
        (N := N) Q phase label := by
  simpa only [dSVDensityRationalPublicLogRankBucketRepresentative, present, ↓reduceDIte] using
    (Finset.min'_mem
      (dSVDensityRationalPublicLogRankBucketFiber
        (N := N) Q phase label) present)

theorem dSVDensityRationalPublicLogRankBucketRepresentative_same
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    (dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).val ≠ 0 ∧
      dSVDensityRationalPublicLogRankBucket Q phase
        (dSVDensityRationalPublicLogRankBucketRepresentative
          (N := N) Q phase
            (dSVDensityRationalPublicLogRankBucket
              Q phase r)) =
        dSVDensityRationalPublicLogRankBucket Q phase r := by
  have member :
      r ∈ dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r) :=
    (dSVDensityRationalPublicLogRankBucketFiber_mem
      Q phase _ r).mpr ⟨nonzero, rfl⟩
  have present :
      (dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).Nonempty := ⟨r, member⟩
  exact
    (dSVDensityRationalPublicLogRankBucketFiber_mem
      Q phase _ _).mp
      (dSVDensityRationalPublicLogRankBucketRepresentative_mem
        (N := N) Q phase _ present)

theorem dSVDensityRationalPublicLogRankBucketRepresentative_le
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r) ≤ r := by
  have member :
      r ∈ dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r) :=
    (dSVDensityRationalPublicLogRankBucketFiber_mem
      Q phase _ r).mpr ⟨nonzero, rfl⟩
  have present :
      (dSVDensityRationalPublicLogRankBucketFiber
        Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).Nonempty := ⟨r, member⟩
  simp only
    [dSVDensityRationalPublicLogRankBucketRepresentative,
      dite_eq_left present]
  exact Finset.min'_le _ r member

theorem dSVDensityRationalPublicLogRankBucketRepresentative_log_sub_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    |Real.log ((max 1 r.val : ℕ) : ℝ) -
      Real.log
        ((max 1
          (dSVDensityRationalPublicLogRankBucketRepresentative
            (N := N) Q phase
              (dSVDensityRationalPublicLogRankBucket
                Q phase r)).val : ℕ) : ℝ)| <
      ((B : ℝ) + 1) / (Q : ℝ) := by
  have same :=
    dSVDensityRationalPublicLogRankBucketRepresentative_same
      Q phase r nonzero
  exact dSVDensityRationalPublicLogRankBucket_log_sub_lt
    positive_Q phase r _ nonzero same.1 same.2.symm

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent DSV density rational public multiscale phase in the exact sampling
construction.
-/
abbrev DSVDensityRationalPublicMultiscalePhase
    (S B : ℕ) :=
  Fin S → Fin B

/--
The type used to represent DSV density rational public multiscale phase index in the exact
sampling construction.
-/
abbrev DSVDensityRationalPublicMultiscalePhaseIndex
    (S B : ℕ) :=
  Fin (Fintype.card
    (DSVDensityRationalPublicMultiscalePhase S B))

theorem dSVDensityRationalPublicMultiscalePhase_card
    (S B : ℕ) :
    Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B) =
      B ^ S := by
  simp only [DSVDensityRationalPublicMultiscalePhase, Fintype.card_pi, Fintype.card_fin,
    prod_const, card_univ]

theorem dSVDensityRationalPublicMultiscalePhase_card_pos
    {S B : ℕ} (positive : 0 < B) :
    0 < Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B) := by
  rw [dSVDensityRationalPublicMultiscalePhase_card]
  exact pow_pos positive S

/-- The overlap quantity for DSV density rational prefix harmonic spectral. -/
def dSVDensityRationalPrefixHarmonicSpectralOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℝ :=
  spectralAtomOverlap
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

theorem dSVDensityRationalPrefixHarmonicSpectralOverlap_nonneg
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    0 ≤ dSVDensityRationalPrefixHarmonicSpectralOverlap
      ξ ζ i j :=
  spectralAtomOverlap_nonneg _ _ _ _ i j

/-- The overlap quantity for DSV density rational local spectral pair basis. -/
def dSVDensityRationalLocalSpectralPairBasisOverlap
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℂ :=
  unitaryBasisOverlap
    (dSVSoftBobLeftReducedDensity_posSemidef
      ξ).isHermitian.eigenvectorUnitary
    (dSVSoftBobLeftReducedDensity_posSemidef
      ζ).isHermitian.eigenvectorUnitary i j

theorem dSVDensityRationalLocalSpectralPairBasisOverlap_norm_sq
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    ‖dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ i j‖ ^ 2 =
      dSVDensityRationalPrefixHarmonicSpectralOverlap
        ξ ζ i j := by
  unfold dSVDensityRationalLocalSpectralPairBasisOverlap
    dSVDensityRationalPrefixHarmonicSpectralOverlap
  exact (targetSpectralAtomOverlap_eq_basis_norm_sq
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity ζ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j).symm

/-- The transcript representation for DSV density rational local spectral pair. -/
def dSVDensityRationalLocalSpectralPairHistory
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    ((‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ q.1 q.2

theorem dSVDensityRationalLocalSpectralPairHistory_apply_norm_sq
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    ‖dSVDensityRationalLocalSpectralPairHistory
        N ξ ζ (i, j)‖ ^ 2 =
      dSVDensityRationalPrefixHarmonicSpectralOverlap
        ξ ζ i j / ((d : ℝ) * (N : ℝ)) := by
  unfold dSVDensityRationalLocalSpectralPairHistory
  change
    ‖((‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap
        ξ ζ i j‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs,
    dSVDensityRationalLocalSpectralPairBasisOverlap_norm_sq,
    inv_pow, dSVUniformDensityThresholdRaw_norm_sq]
  ring

private def dSVDensityRationalMixedCanonicalCrossMatrix
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    Matrix (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  (Matrix.blockDiagonal' fun _ : Fin N =>
    (unitaryBasisOverlap
      (dSVSoftBobLeftReducedDensity_posSemidef
        ξ).isHermitian.eigenvectorUnitary
      (dSVSoftBobLeftReducedDensity_posSemidef
        ζ).isHermitian.eigenvectorUnitary :
      Matrix (Fin d) (Fin d) ℂ)).transpose

theorem dSVDensityRationalMixedCanonicalCrossGauge_eq
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      (dSVUniformDensityBobHistoryCopyBasis
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) =
      dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ := by
  rw [← dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose ζ,
    ← dSVUniformDensityPhysicalSpectralAliceCopy_transpose ξ,
    ← Matrix.transpose_mul]
  unfold dSVDensityRationalMixedCanonicalCrossMatrix
  congr 1
  rw [dSVUniformDensityPhysicalSpectralAliceCopy_inv]
  change
    Matrix.blockDiagonal' (fun _ : Fin N =>
      (((dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹ :
        Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) *
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (dSVUniformDensityThresholdLeftBobBasis ζ :
          Matrix (Fin d) (Fin d) ℂ)) =
      Matrix.blockDiagonal' (fun _ : Fin N =>
        (unitaryBasisOverlap
          (dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvectorUnitary
          (dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvectorUnitary :
          Matrix (Fin d) (Fin d) ℂ))
  rw [← Matrix.blockDiagonal'_mul]
  rfl

theorem dSVDensityRationalCanonicalPrefixMask_eq_diagonal
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalPrefixMask w N ξ =
      Matrix.diagonal
        (fun q : DSVUniformDensityThresholdLocalIndex N d =>
          if dSVDensityRationalProjectiveThresholdBin w N q.1
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues q.2) = true
          then (1 : ℂ) else 0) := by
  unfold dSVDensityRationalCanonicalPrefixMask
  rw [Matrix.blockDiagonal'_diagonal]

/-- The source object for DSV density rational mixed canonical raw. -/
def dSVDensityRationalMixedCanonicalRawSource
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  toLp 2
    (Matrix.vec
      (dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ))

theorem dSVDensityRationalMixedCanonicalRawSource_apply
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (k l : Fin N) (i j : Fin d) :
    dSVDensityRationalMixedCanonicalRawSource
        w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) =
      if k = l ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N l
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true
      then
        dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j
      else 0 := by
  classical
  unfold dSVDensityRationalMixedCanonicalRawSource
  rw [dSVDensityRationalCanonicalPrefixMask_eq_diagonal w N ζ,
    dSVDensityRationalCanonicalPrefixMask_eq_diagonal w N ξ]
  change
    (Matrix.diagonal
        (fun q : DSVUniformDensityThresholdLocalIndex N d =>
          if dSVDensityRationalProjectiveThresholdBin w N q.1
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ζ).isHermitian.eigenvalues q.2) = true
          then (1 : ℂ) else 0) *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        Matrix.diagonal
          (fun q : DSVUniformDensityThresholdLocalIndex N d =>
            if dSVDensityRationalProjectiveThresholdBin w N q.1
                ((dSVSoftBobLeftReducedDensity_posSemidef
                  ξ).isHermitian.eigenvalues q.2) = true
            then (1 : ℂ) else 0)) ⟨l, j⟩ ⟨k, i⟩ = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases flags : k = l
  · subst l
    by_cases alice :
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true
    · by_cases bob :
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true
      · simp only [bob, ↓reduceIte, dSVDensityRationalMixedCanonicalCrossMatrix, transpose_apply,
          blockDiagonal'_apply, ↓reduceDIte, cast_eq, unitaryBasisOverlap_apply, one_mul, alice,
          mul_one, and_self, dSVDensityRationalLocalSpectralPairBasisOverlap]
      · simp only [bob, Bool.false_eq_true, ↓reduceIte, zero_mul, mul_ite, mul_one, mul_zero,
          ite_self, and_false]
    · simp only [ite_mul, one_mul, zero_mul, alice, Bool.false_eq_true, ↓reduceIte, mul_zero,
        false_and, and_false]
  · simp only [dSVDensityRationalMixedCanonicalCrossMatrix, transpose_apply, blockDiagonal'_apply,
      flags, ↓reduceDIte, mul_zero, mul_ite, mul_one, ite_self, false_and, ↓reduceIte]

theorem dSVDensityRationalMixedCanonicalProjectorMatrix_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    (((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ζ *
        dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
        dSVDensityRationalCanonicalPrefixMask w N ξ := by
  let S : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let X : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ξ
  let Z : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let XI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((X⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let ZI : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    ((Z⁻¹ : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
      Matrix (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ)
  let M : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ξ
  let R : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVDensityRationalCanonicalPrefixMask w N ζ
  have physical_x :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) =
        (((S⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          M * (S : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ξ
  have physical_z :
      Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k) =
        ((((dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ)⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) *
          R * (dSVUniformDensityAliceHistorySpectralCopy
            (N := N) ζ : Matrix _ _ ℂ) :=
    dSVDensityRationalPhysicalAcceptedProjector_eq_spectralMask
      w N ζ
  have transpose_x :
      (S : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ξ
  have transpose_z :
      (dSVUniformDensityAliceHistorySpectralCopy
          (N := N) ζ : Matrix
            (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ).transpose =
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_transpose
      (N := N) ζ
  have inverse_x :
      (((S⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((X⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ξ
  have inverse_z :
      ((((dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ζ)⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ)).transpose =
        (((Z⁻¹ : Matrix.unitaryGroup
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
          Matrix (DSVUniformDensityThresholdLocalIndex N d)
            (DSVUniformDensityThresholdLocalIndex N d) ℂ)) :=
    dSVUniformDensityPhysicalSpectralAliceCopy_inv_transpose
      (N := N) ζ
  have cancel_x :
      XI * (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (X : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (X : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp X.property
  have cancel_z :
      ZI * (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1 := by
    change
      star (Z : Matrix
        (DSVUniformDensityThresholdLocalIndex N d)
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) *
        (Z : Matrix
          (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ) = 1
    exact (Matrix.mem_unitaryGroup_iff').mp Z.property
  change
    ZI *
      ((Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k) *
        Matrix.blockDiagonal'
          (fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ζ k)).transpose) *
      (S : Matrix _ _ ℂ).transpose =
        R * dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ * M
  calc
    _ = ((ZI * (Z : Matrix _ _ ℂ)) * R) *
        (ZI * (X : Matrix _ _ ℂ)) *
        (M * (XI * (X : Matrix _ _ ℂ))) := by
          rw [physical_x, physical_z]
          dsimp only [XI, ZI]
          simp only [Matrix.transpose_mul,
            dSVDensityRationalCanonicalPrefixMask_transpose,
            transpose_x, transpose_z, inverse_x, inverse_z,
            Matrix.mul_assoc, M, R]
    _ = R * (ZI * (X : Matrix _ _ ℂ)) * M := by
          rw [cancel_x, cancel_z]
          simp only [one_mul, mul_one]
    _ = _ := by
      dsimp only [ZI]
      rw [dSVDensityRationalMixedCanonicalCrossGauge_eq N ξ ζ]

theorem dSVDensityRationalMixedCanonicalSpectralOutcome_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalPrefixSpectralOutcome
        w N ξ ζ =
      (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) •
        dSVDensityRationalMixedCanonicalRawSource w N ξ ζ := by
  classical
  let S : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let T : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let c : ℝ :=
    ‖sharedThresholdResourceRaw (d := Fin d)
      (fun _ : Fin N => (1 : ℝ))‖⁻¹
  let K : Matrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    (S : Matrix _ _ ℂ) ⊗ₖ
      (((T⁻¹ : Matrix.unitaryGroup
        (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
        Matrix (DSVUniformDensityThresholdLocalIndex N d)
          (DSVUniformDensityThresholdLocalIndex N d) ℂ))
  unfold dSVDensityRationalCanonicalPrefixSpectralOutcome
    dSVDensityRationalPhysicalAcceptedOutcome
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector]
  unfold dSVDensityRationalMixedCanonicalRawSource
  change
    Matrix.toEuclideanLin K
      (c • toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k *
              dSVDensityRationalPhysicalProjector
                w ζ k).transpose))) =
      c • toLp 2
        (Matrix.vec
          (dSVDensityRationalCanonicalPrefixMask w N ζ *
            dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
            dSVDensityRationalCanonicalPrefixMask w N ξ))
  rw [(Matrix.toEuclideanLin K).map_smul_of_tower]
  congr 1
  apply WithLp.ofLp_injective
  change
    K.mulVec
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N =>
            dSVDensityRationalPhysicalProjector w ξ k *
              dSVDensityRationalPhysicalProjector
                w ζ k).transpose)) =
      Matrix.vec
        (dSVDensityRationalCanonicalPrefixMask w N ζ *
          dSVDensityRationalMixedCanonicalCrossMatrix N ξ ζ *
          dSVDensityRationalCanonicalPrefixMask w N ξ)
  dsimp [K]
  rw [Matrix.kronecker_mulVec_vec]
  apply congrArg Matrix.vec
  rw [Matrix.blockDiagonal'_mul]
  exact dSVDensityRationalMixedCanonicalProjectorMatrix_eq
    w N ξ ζ

private def dSVDensityRationalPublicLogBilateralPureTensor
    {ι κ : Type*}
    (v : EuclideanSpace ℂ (ι × ι))
    (u : EuclideanSpace ℂ (κ × κ)) :
    EuclideanSpace ℂ ((ι × κ) × (ι × κ)) :=
  toLp 2 fun q : (ι × κ) × (ι × κ) =>
    v (q.1.1, q.2.1) * u (q.1.2, q.2.2)

theorem dSVDensityRationalPublicLogBilateralPureTensor_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : EuclideanSpace ℂ (ι × ι))
    (u : EuclideanSpace ℂ (κ × κ)) :
    ‖dSVDensityRationalPublicLogBilateralPureTensor v u‖ ^ 2 =
      ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  change
    (∑ q : (ι × κ) × (ι × κ),
      ‖v (q.1.1, q.2.1) * u (q.1.2, q.2.2)‖ ^ 2) =
      (∑ q : ι × ι, ‖v q‖ ^ 2) *
        (∑ q : κ × κ, ‖u q‖ ^ 2)
  simp only [Fintype.sum_prod_type, norm_mul, mul_pow]
  calc
    (∑ a : ι, ∑ x : κ, ∑ b : ι, ∑ y : κ,
      ‖v (a, b)‖ ^ 2 * ‖u (x, y)‖ ^ 2) =
      ∑ a : ι, ∑ b : ι, ∑ x : κ, ∑ y : κ,
        ‖v (a, b)‖ ^ 2 * ‖u (x, y)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = (∑ a : ι, ∑ b : ι, ‖v (a, b)‖ ^ 2) *
          (∑ x : κ, ∑ y : κ, ‖u (x, y)‖ ^ 2) := by
            symm
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]

/--
The type used to represent DSV density rational public log phase history local index in the
exact sampling construction.
-/
abbrev DSVDensityRationalPublicLogPhaseHistoryLocalIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

private def dSVDensityRationalPublicLogPhasePureSource
    (B N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ×
       DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (ePRState B)
    (dSVUniformDensityThresholdWholeHistorySharedState N d L)

theorem dSVDensityRationalPublicLogPhasePureSource_apply
    (B N d L : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalPublicLogPhasePureSource
        B N d L ((φ, a), (ψ, b)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) := by
  simp only [dSVDensityRationalPublicLogPhasePureSource,
    dSVDensityRationalPublicLogBilateralPureTensor, ePRState, ofReal_inv, ite_mul, zero_mul]

theorem dSVDensityRationalPublicLogPhasePureSource_norm
    {B N d L : ℕ}
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVDensityRationalPublicLogPhasePureSource
      B N d L‖ = 1 := by
  have squared :
      ‖dSVDensityRationalPublicLogPhasePureSource
        B N d L‖ ^ 2 = 1 := by
    unfold dSVDensityRationalPublicLogPhasePureSource
    rw [dSVDensityRationalPublicLogBilateralPureTensor_norm_sq,
      ePRState_norm B phases,
      dSVUniformDensityThresholdWholeHistorySharedState_norm
        grid dimension L]
    norm_num
  nlinarith [norm_nonneg
    (dSVDensityRationalPublicLogPhasePureSource B N d L)]

private def dSVDensityRationalPublicLogPhaseHarmonicPureSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m) ×
       (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L × Fin m)) :=
  dSVDensityRationalPublicLogBilateralPureTensor
    (dSVDensityRationalPublicLogPhasePureSource B N d L)
    (embezzlementState m)

theorem dSVDensityRationalPublicLogPhaseHarmonicPureSource_apply
    (B N d L m : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseHarmonicPureSource
        B N d L m (((φ, a), i), ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) *
        embezzlementState m (i, j) := by
  change
    dSVDensityRationalPublicLogPhasePureSource
        B N d L ((φ, a), (ψ, b)) *
      embezzlementState m (i, j) = _
  rw [dSVDensityRationalPublicLogPhasePureSource_apply]

theorem dSVDensityRationalPublicLogPhaseHarmonicPureSource_norm
    {B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m‖ = 1 := by
  have squared :
      ‖dSVDensityRationalPublicLogPhaseHarmonicPureSource
        B N d L m‖ ^ 2 = 1 := by
    unfold dSVDensityRationalPublicLogPhaseHarmonicPureSource
    rw [dSVDensityRationalPublicLogBilateralPureTensor_norm_sq,
      dSVDensityRationalPublicLogPhasePureSource_norm
        phases grid dimension,
      embezzlementState_norm m harmonic]
    norm_num
  nlinarith [norm_nonneg
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m)]

private abbrev DSVDensityRationalPublicLogPhaseCatalystIndex
    (B N d L : ℕ) :=
  Fin B × DSVUniformDensityThresholdWholeHistoryCatalystIndex N d L

private def dSVDensityRationalPublicLogPhaseTargetSplitEquiv
    (B N d L : ℕ) :
    DSVDensityRationalPublicLogPhaseHistoryLocalIndex B N d L ≃
      (Fin d ×
        DSVDensityRationalPublicLogPhaseCatalystIndex B N d L) where
  toFun q :=
    let actual :=
      dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L q.2
    (actual.1, (q.1, actual.2))
  invFun q :=
    (q.2.1,
      (dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
        N d L).symm (q.1, q.2.2))
  left_inv := by
    rintro ⟨phase, history⟩
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨target, phase, catalyst⟩
    simp only [Equiv.apply_symm_apply]

/--
The DSV density rational public log phase residual construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalPublicLogPhaseResidual
    (B N d L m : ℕ) : ℕ :=
  Fintype.card
      (DSVDensityRationalPublicLogPhaseCatalystIndex
        B N d L) * m

/-- The finite equivalence encoding DSV density rational public log phase target first index. -/
def dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (B N d L m : ℕ) :
    (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) :=
  (Equiv.prodCongr
    (dSVDensityRationalPublicLogPhaseTargetSplitEquiv B N d L)
    (Equiv.refl (Fin m))).trans
      (dSVRankControlledTargetCatalystIndexEquiv
        (ι := DSVDensityRationalPublicLogPhaseCatalystIndex
          B N d L) d m)

/-- The source object for DSV density rational public log phase target first prepared. -/
def dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m))
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource
      B N d L m)

theorem dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
    (B N d L m : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
        B N d L m
        (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((φ, a), i),
          dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) *
        embezzlementState m (i, j) := by
  unfold dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
  simpa only [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, eq_rec_constant, Equiv.coe_fn_mk, Prod.map_apply,
    Equiv.symm_apply_apply, ofReal_inv, ite_mul, zero_mul] using
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource_apply
      B N d L m φ ψ a b i j)

theorem dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_norm
    {B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
      B N d L m‖ = 1 := by
  unfold dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
  rw [LinearIsometryEquiv.norm_map]
  exact dSVDensityRationalPublicLogPhaseHarmonicPureSource_norm
    phases grid dimension harmonic

/--
The type used to represent DSV density rational public multiscale phase history local index in
the exact sampling construction.
-/
abbrev DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
    (S B N d L : ℕ) :=
  DSVDensityRationalPublicMultiscalePhaseIndex S B ×
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L

/--
The DSV density rational public multiscale phase residual construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalPublicMultiscalePhaseResidual
    (S B N d L m : ℕ) : ℕ :=
  dSVDensityRationalPublicLogPhaseResidual
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

/--
The finite equivalence encoding DSV density rational public multiscale phase target first index.
-/
def dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
    (S B N d L m : ℕ) :
    (DSVDensityRationalPublicMultiscalePhaseHistoryLocalIndex
      S B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) :=
  dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

/-- The source object for DSV density rational public multiscale phase target first prepared. -/
def dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m) ×
       Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m)) :=
  dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m

theorem
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource_norm
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
      S B N d L m‖ = 1 := by
  unfold
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
  exact
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_norm
      (dSVDensityRationalPublicMultiscalePhase_card_pos phases)
      grid dimension harmonic

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/--
The DSV density rational public log phase actual target first local lift construction used in
the quantum parallel-repetition argument.
-/
def dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ) :
    Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m)) ℂ := by
  classical
  let whole : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
          B N d L × Fin m) ℂ :=
    ⟨U.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ),
      Matrix.kronecker_mem_unitary U.property
        (Matrix.unitaryGroup (Fin m) ℂ).one_mem⟩
  exact dSVOriginalComputationalReindexedUnitary
    (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
      B N d L m) whole

theorem
    dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ)
    (a b : DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m U
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (a, i))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (b, j)) =
      if i = j then U a b else 0 := by
  classical
  change
    (Matrix.reindex
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m)
      (U.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (a, i))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (b, j)) = _
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The unitary operator implementing DSV density rational public log phase physical history. -/
def dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
    (B : ℕ) {N d L : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ) :
    Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ := by
  classical
  exact ⟨(1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ U.val,
    Matrix.kronecker_mem_unitary
      (Matrix.unitaryGroup (Fin B) ℂ).one_mem U.property⟩

theorem dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply
    (B : ℕ) {N d L : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
        B U (φ, a) (ψ, b) =
      if φ = ψ then U a b else 0 := by
  classical
  change
    ((1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ U.val)
      (φ, a) (ψ, b) = _
  simp only [kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

private def dSVDensityRationalHeterogeneousActualAcceptSet
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun j : Fin L =>
    accepted j (history j.castSucc)

/--
The DSV density rational heterogeneous actual first accepted construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousActualFirstAccepted
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Fin (L + 1) := by
  classical
  let hits := dSVDensityRationalHeterogeneousActualAcceptSet
    accepted history
  exact if nonempty : hits.Nonempty then
    (hits.min' nonempty).succ
  else 0

theorem dSVDensityRationalHeterogeneousActualFirstAccepted_prefix_iff
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) (j : Fin L) :
    dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted history = j.succ ↔
      accepted j (history j.castSucc) ∧
        ∀ i : Fin L, i < j →
          ¬ accepted i (history i.castSucc) := by
  classical
  unfold dSVDensityRationalHeterogeneousActualFirstAccepted
  simpa only [dSVDensityRationalHeterogeneousActualAcceptSet, mem_filter, mem_univ,
    true_and] using
    dSVUniformDensityFirstAcceptFinitePrefix
      (dSVDensityRationalHeterogeneousActualAcceptSet
        accepted history) j

theorem dSVDensityRationalHeterogeneousActualFirstAccepted_zero_iff
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) :
    dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted history = 0 ↔
      ∀ i : Fin L, ¬ accepted i (history i.castSucc) := by
  classical
  unfold dSVDensityRationalHeterogeneousActualFirstAccepted
  let hits := dSVDensityRationalHeterogeneousActualAcceptSet
    accepted history
  change (if h : hits.Nonempty then (hits.min' h).succ else 0) = 0 ↔ _
  by_cases nonempty : hits.Nonempty
  · rw [dite_eq_left nonempty]
    constructor
    · intro impossible
      exact (Fin.succ_ne_zero _ impossible).elim
    · intro none
      obtain ⟨j, member⟩ := nonempty
      have hit : accepted j (history j.castSucc) := by
        simpa [hits,
          dSVDensityRationalHeterogeneousActualAcceptSet]
          using member
      exact (none j hit).elim
  · rw [dite_eq_right nonempty]
    simp only [true_iff]
    intro j hit
    apply nonempty
    refine ⟨j, ?_⟩
    simpa [hits,
      dSVDensityRationalHeterogeneousActualAcceptSet] using hit

private def dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop) :
    Equiv.Perm (Σ _ : Fin (L + 1), Fin (L + 1) → β) where
  toFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  invFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    simp only [Equiv.swap_apply_self]
  right_inv := by
    rintro ⟨flag, history⟩
    simp only [Equiv.swap_apply_self]

/-- The unitary operator implementing DSV density rational heterogeneous actual first accept. -/
def dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  permutationUnitary
    (dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
      accepted)

theorem dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_mulVec
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (v : (Σ _ : Fin (L + 1), Fin (L + 1) → β) → ℂ)
    (flag : Fin (L + 1)) (history : Fin (L + 1) → β) :
    ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
        accepted :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)).mulVec
        v ⟨flag, history⟩ =
      v ⟨(Equiv.swap (0 : Fin (L + 1))
        (dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history)) flag, history⟩ := by
  rw [dSVDensityRationalHeterogeneousActualFirstAcceptUnitary,
    permutationUnitary_val, Matrix.permMatrix_mulVec]
  rfl

theorem
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_zeroFlag
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (v : (Fin (L + 1) → β) → ℂ)
    (flag : Fin (L + 1)) (history : Fin (L + 1) → β) :
    ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
        accepted :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)).mulVec
        (fun q => if q.1 = 0 then v q.2 else 0)
        ⟨flag, history⟩ =
      if flag =
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history
      then v history else 0 := by
  rw [dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_mulVec]
  let selected :=
    dSVDensityRationalHeterogeneousActualFirstAccepted
      accepted history
  change
    (if (Equiv.swap (0 : Fin (L + 1)) selected) flag = 0
    then v history else 0) =
    if flag = selected then v history else 0
  congr 1
  apply propext
  constructor
  · intro zero
    have injective :=
      (Equiv.swap (0 : Fin (L + 1)) selected).injective
    apply injective
    simpa only [Equiv.swap_apply_right] using zero
  · intro same
    subst flag
    simp only [Equiv.swap_apply_right]

/--
The DSV density rational heterogeneous actual copy accepted construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousActualCopyAccepted
    {S N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (j : Fin L)
    (atom : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    (width (schedule j)) ξ atom

/--
The DSV density rational heterogeneous actual copy condition construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousActualCopyCondition
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (flag : Fin (L + 1)) (i : Fin (L + 1)) (atom : β) : Prop :=
  if active : i.val < L then
    if flag = 0 then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 < flag.val then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 = flag.val then
      accepted ⟨i.val, active⟩ atom
    else True
  else True

theorem
    dSVDensityRationalHeterogeneousActualFirstAccepted_allFlags_iff
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) (flag : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted history = flag ↔
      ∀ i : Fin (L + 1),
        dSVDensityRationalHeterogeneousActualCopyCondition
          accepted flag i (history i) := by
  induction flag using Fin.cases with
  | zero =>
      rw [dSVDensityRationalHeterogeneousActualFirstAccepted_zero_iff]
      constructor
      · intro failed i
        by_cases active : i.val < L
        · have actual := failed (⟨i.val, active⟩ : Fin L)
          simpa only [dSVDensityRationalHeterogeneousActualCopyCondition, active, ↓reduceDIte,
            ↓reduceIte, Fin.castSucc_mk, Fin.eta] using actual
        · simp only [dSVDensityRationalHeterogeneousActualCopyCondition, active, ↓reduceDIte]
      · intro all i
        have actual := all i.castSucc
        simpa only [dSVDensityRationalHeterogeneousActualCopyCondition, Fin.val_castSucc, i.isLt,
          ↓reduceDIte, ↓reduceIte, Fin.eta] using actual
  | succ j =>
      rw [dSVDensityRationalHeterogeneousActualFirstAccepted_prefix_iff]
      constructor
      · rintro ⟨hit, earlier⟩ i
        by_cases active : i.val < L
        · by_cases before : i.val < j.val
          · have failure := earlier
              (⟨i.val, active⟩ : Fin L) (by exact before)
            simpa only [dSVDensityRationalHeterogeneousActualCopyCondition, active, ↓reduceDIte,
              Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ, Order.lt_add_one_iff,
              Order.add_one_le_iff, before, Fin.castSucc_mk, Fin.eta] using failure
          · by_cases equal : i.val = j.val
            · have same : i = j.castSucc := Fin.ext equal
              subst i
              simpa only [dSVDensityRationalHeterogeneousActualCopyCondition, Fin.val_castSucc,
                j.isLt, ↓reduceDIte, Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ,
                lt_self_iff_false, Nat.add_left_cancel_iff, Fin.eta] using hit
            · simp only [dSVDensityRationalHeterogeneousActualCopyCondition, active, ↓reduceDIte,
                Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ, Order.lt_add_one_iff,
                Order.add_one_le_iff, before, Nat.add_right_cancel_iff, equal]
        · simp only [dSVDensityRationalHeterogeneousActualCopyCondition, active, ↓reduceDIte]
      · intro all
        constructor
        · have actual := all j.castSucc
          simpa only [dSVDensityRationalHeterogeneousActualCopyCondition, Fin.val_castSucc,
            j.isLt, ↓reduceDIte, Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ, lt_self_iff_false,
            Nat.add_left_cancel_iff, Fin.eta] using actual
        · intro i before
          have actual := all i.castSucc
          simpa only [dSVDensityRationalHeterogeneousActualCopyCondition, Fin.val_castSucc,
            i.isLt, ↓reduceDIte, Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ, Order.lt_add_one_iff,
            Order.add_one_le_iff, Fin.val_fin_lt, before, Fin.eta] using actual

theorem
    dSVDensityRationalHeterogeneousActualFirstAccepted_sourceProduct
    {β : Type*} [Fintype β] {L : ℕ}
    (accepted : Fin L → β → Prop)
    (flag : Fin (L + 1))
    (A D : Fin (L + 1) → β → ℂ) :
    (∑ history : Fin (L + 1) → β,
      (∏ i : Fin (L + 1), A i (history i)) *
        (if flag =
          dSVDensityRationalHeterogeneousActualFirstAccepted
            accepted history
        then ∏ i : Fin (L + 1), D i (history i)
        else 0)) =
      ∏ i : Fin (L + 1),
        ∑ atom : β, A i atom *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom
          then D i atom else 0) := by
  classical
  have single (history : Fin (L + 1) → β) :
      (∏ i : Fin (L + 1), A i (history i)) *
          (if flag =
            dSVDensityRationalHeterogeneousActualFirstAccepted
              accepted history
          then ∏ i : Fin (L + 1), D i (history i)
          else 0) =
        ∏ i : Fin (L + 1),
          (A i (history i) *
            (if dSVDensityRationalHeterogeneousActualCopyCondition
                accepted flag i (history i)
            then D i (history i) else 0)) := by
    by_cases selected :
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history = flag
    · have all :=
        (dSVDensityRationalHeterogeneousActualFirstAccepted_allFlags_iff
          accepted history flag).mp selected
      rw [ite_eq_left selected.symm, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [ite_eq_left (all i)]
    · have absent : ¬ ∀ i : Fin (L + 1),
          dSVDensityRationalHeterogeneousActualCopyCondition
            accepted flag i (history i) := by
        intro all
        exact selected
          ((dSVDensityRationalHeterogeneousActualFirstAccepted_allFlags_iff
            accepted history flag).mpr all)
      push Not at absent
      obtain ⟨i, rejected⟩ := absent
      have zero :
          (∏ k : Fin (L + 1),
            A k (history k) *
              (if dSVDensityRationalHeterogeneousActualCopyCondition
                  accepted flag k (history k)
              then D k (history k) else 0)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [rejected, ↓reduceIte, mul_zero]
      rw [ite_eq_right (Ne.symm selected), mul_zero, zero]
  calc
    _ = ∑ history : Fin (L + 1) → β,
      ∏ i : Fin (L + 1),
        (A i (history i) *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i (history i)
          then D i (history i) else 0)) := by
        apply Finset.sum_congr rfl
        intro history _
        exact single history
    _ = _ :=
      (Fintype.prod_sum fun i : Fin (L + 1) => fun atom : β =>
        A i atom *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom
          then D i atom else 0)).symm

/-- The unitary operator implementing DSV density rational heterogeneous actual physical local. -/
def dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  (dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U)⁻¹ *
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
      accepted *
    dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U

/-- The unitary operator implementing DSV density rational heterogeneous actual alice. -/
def dSVDensityRationalHeterogeneousActualAliceUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ξ)
    (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)

/-- The unitary operator implementing DSV density rational heterogeneous actual bob. -/
def dSVDensityRationalHeterogeneousActualBobUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ζ)
    ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)

/-- The quantum state representing DSV density rational heterogeneous actual physical. -/
def dSVDensityRationalHeterogeneousActualPhysicalState
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
       DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  toLp 2
    ((((dSVDensityRationalHeterogeneousActualAliceUnitary
          N width schedule ξ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) ⊗ₖ
        (dSVDensityRationalHeterogeneousActualBobUnitary
          N width schedule ζ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ)).mulVec
      (ofLp
        (dSVUniformDensityThresholdWholeHistorySharedState
          N d L))))

theorem dSVDensityRationalHeterogeneousActualPhysicalState_norm
    {S N d L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    ‖dSVDensityRationalHeterogeneousActualPhysicalState
      N width schedule ξ ζ‖ = 1 := by
  unfold dSVDensityRationalHeterogeneousActualPhysicalState
  rw [dSVUniformDensityMixedProtocolLocalAction_norm]
  exact dSVUniformDensityThresholdWholeHistorySharedState_norm
    grid dimension L

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/-- The finite outcome encoding for DSV density rational heterogeneous physical stage. -/
def dSVDensityRationalHeterogeneousPhysicalStageOutcome
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (k : ℕ) (alice bob : Bool) : ℝ :=
  if active : k < L then
    ‖dSVDensityRationalCompleteProjectiveOutcome
      (width (schedule ⟨k, active⟩)) N ξ ζ alice bob‖ ^ 2
  else if alice = false ∧ bob = false then 1 else 0

/--
The DSV density rational heterogeneous physical stage continue construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalStageContinue
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k false false

/--
The DSV density rational heterogeneous physical stage success construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalStageSuccess
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k true true

/--
The DSV density rational heterogeneous physical stage asynchronous construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k true false +
    dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k false true

theorem dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (k : ℕ) (alice bob : Bool) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k alice bob := by
  unfold dSVDensityRationalHeterogeneousPhysicalStageOutcome
  split_ifs <;> positivity

theorem dSVDensityRationalHeterogeneousPhysicalStage_partition
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    dSVDensityRationalHeterogeneousPhysicalStageContinue
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k = 1 := by
  by_cases active : k < L
  · simpa only [dSVDensityRationalHeterogeneousPhysicalStageContinue,
      dSVDensityRationalHeterogeneousPhysicalStageOutcome, active, ↓reduceDIte,
      dSVDensityRationalHeterogeneousPhysicalStageSuccess,
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
      dSVDensityRationalActualMixedContinueMass, dSVDensityRationalActualMixedSuccessMass,
      dSVDensityRationalActualMixedAsynchronousMass] using
        (dSVDensityRationalActualMixed_mass_partition
          grid dimension (width (schedule ⟨k, active⟩)) ξ ζ)
  · simp only [dSVDensityRationalHeterogeneousPhysicalStageContinue,
      dSVDensityRationalHeterogeneousPhysicalStageOutcome, active, ↓reduceDIte, and_self,
      ↓reduceIte, dSVDensityRationalHeterogeneousPhysicalStageSuccess, Bool.true_eq_false,
      add_zero, dSVDensityRationalHeterogeneousPhysicalStageAsynchronous, and_true, and_false]

theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val =
      dSVDensityRationalPhysicalProjectorCrossHazard
        N (width (schedule k)) ξ ζ := by
  simpa only [dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome, k.isLt, ↓reduceDIte, Fin.eta,
    dSVDensityRationalActualMixedAsynchronousMass] using
      (dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
        (width (schedule k)) N ξ ζ)

/--
The DSV density rational heterogeneous physical survival construction used in the quantum
parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousPhysicalSurvival
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVHeterogeneousRealPrefix
    (dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ) k

theorem dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalSurvival
      N width schedule ξ ζ k := by
  unfold dSVDensityRationalHeterogeneousPhysicalSurvival
  apply dSVHeterogeneousRealPrefix_nonneg
  intro j
  exact dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
    N width schedule ξ ζ j false false

/-- The total probability mass of DSV density rational heterogeneous physical stopped success. -/
def dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k

/--
The total probability mass of DSV density rational heterogeneous physical stopped asynchronous.
-/
def dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k

/-- The total probability mass of DSV density rational heterogeneous physical terminal. -/
def dSVDensityRationalHeterogeneousPhysicalTerminalMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival
    N width schedule ξ ζ L

theorem
    dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
        N width schedule ξ ζ +
      dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule ξ ζ +
      dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule ξ ζ = 1 := by
  let continuation :=
    dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ
  let success :=
    dSVDensityRationalHeterogeneousPhysicalStageSuccess
      N width schedule ξ ζ
  let asynchronous :=
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
      N width schedule ξ ζ
  have stage (k : ℕ) :
      success k + asynchronous k = 1 - continuation k := by
    dsimp [continuation, success, asynchronous]
    linarith [
      dSVDensityRationalHeterogeneousPhysicalStage_partition
        grid dimension width schedule ξ ζ k]
  have escape :=
    dSVHeterogeneousRealStopping_escape_identity
      continuation L
  change
    (∑ k ∈ Finset.range L,
      dSVHeterogeneousRealPrefix continuation k * success k) +
      (∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k *
          asynchronous k) +
      dSVHeterogeneousRealPrefix continuation L = 1
  have combined :
      (∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k * success k) +
      (∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k *
          asynchronous k) =
      ∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k *
          (1 - continuation k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_add, stage k]
  rw [combined, escape]
  ring

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_hazard
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ =
      ∑ k : Fin L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k.val *
          dSVDensityRationalPhysicalProjectorCrossHazard
            N (width (schedule k)) ξ ζ := by
  classical
  unfold
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
  calc
    (∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k) =
      ∑ k : Fin L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k.val *
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k.val := by
          simpa only using
            (Fin.sum_univ_eq_sum_range
              (fun k : ℕ =>
                dSVDensityRationalHeterogeneousPhysicalSurvival
                    N width schedule ξ ζ k *
                  dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
                    N width schedule ξ ζ k) L).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
          N width schedule ξ ζ k]

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    0 ≤
      dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ := by
  unfold
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg
    (dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
      N width schedule ξ ζ k)
  exact add_nonneg
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true false)
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k false true)

theorem dSVDensityRationalHeterogeneousPhysicalTerminalMass_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalTerminalMass
      N width schedule ξ ζ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
    N width schedule ξ ζ L

private def dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
      N width schedule ξ ζ k /
    (dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k)

theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_escape_mul_ratio
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k =
      (dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k +
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k) *
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
          N width schedule ξ ζ k := by
  let p := dSVDensityRationalHeterogeneousPhysicalStageSuccess
    N width schedule ξ ζ k
  let h := dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
    N width schedule ξ ζ k
  have p_nonnegative : 0 ≤ p :=
    dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true true
  have h_nonnegative : 0 ≤ h := add_nonneg
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true false)
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k false true)
  change h = (p + h) * (h / (p + h))
  by_cases vanished : p + h = 0
  · have h_zero : h = 0 := by linarith
    simp only [h_zero, add_zero, zero_div, mul_zero]
  · field_simp

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_ratioLedger
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ =
      ∑ k ∈ Finset.range L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          (dSVDensityRationalHeterogeneousPhysicalStageSuccess
              N width schedule ξ ζ k +
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k) *
          dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
            N width schedule ξ ζ k := by
  unfold
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
  apply Finset.sum_congr rfl
  intro k _
  calc
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        ((dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) *
          dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
            N width schedule ξ ζ k) :=
      congrArg
        (fun x : ℝ =>
          dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k * x)
        (dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_escape_mul_ratio
          N width schedule ξ ζ k)
    _ = _ := by ring

theorem
    dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_lower
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) (k : Fin L) :
    1 / (2 * (width (schedule k) + 1) * (d : ℝ)) ≤
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ := by
  have width_positive : 0 < width (schedule k) :=
    lt_of_lt_of_le (by norm_num) (large (schedule k))
  have mass := dSVDensityRationalLargeWidthDiagonalMass_half
    width_positive grid (fine (schedule k)) ξ
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  calc
    1 / (2 * (width (schedule k) + 1) * (d : ℝ)) =
      (1 / (2 * (width (schedule k) + 1))) / (d : ℝ) := by
        rw [div_div]
    _ ≤ dSVDensityRationalLeftProjectiveDiagonalMass
        (width (schedule k)) N ξ / (d : ℝ) :=
      (div_le_div_iff_of_pos_right dimension_real).mpr mass
    _ = dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ := by
      rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq]

theorem
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ ≤
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k.val +
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val := by
  simpa only [dSVDensityRationalHeterogeneousPhysicalStageSuccess,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome, k.isLt, ↓reduceDIte, Fin.eta,
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
    dSVDensityRationalActualMixedSuccessMass, dSVDensityRationalActualMixedAsynchronousMass]
    using dSVDensityRationalActualMixed_escape_ge_diagonal
      grid dimension (width (schedule k)) ξ ζ

theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_relative_diagonal_le
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (width (schedule k) + 1) * ((d : ℝ) / N) := by
  rw [
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
      N width schedule ξ ζ k]
  exact dSVDensityRationalLargeWidthPhysicalRelativeHazard_le
    dimension (large (schedule k)) grid (fine (schedule k)) ξ ζ

theorem
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_relative_diagonal
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
        N width schedule ξ ζ k.val ≤
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val /
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ := by
  have width_positive : 0 < width (schedule k) :=
    lt_of_lt_of_le (by norm_num) (large (schedule k))
  have self_positive :=
    dSVDensityRationalLargeWidthPhysicalDiagonalBornSuccess_pos
      dimension width_positive grid (fine (schedule k)) ξ
  have self_lower :=
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
      grid dimension width schedule ξ ζ k
  have asynchronous_nonnegative :
      0 ≤ dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val := by
    exact add_nonneg
      (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k.val true false)
      (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k.val false true)
  unfold dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
  exact div_le_div_of_nonneg_left
    asynchronous_nonnegative self_positive self_lower

theorem
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_targetDistance
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
        N width schedule ξ ζ k.val ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
  calc
    _ ≤ dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val /
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ :=
      dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_relative_diagonal
        grid dimension width large fine schedule ξ ζ k
    _ ≤ 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (width (schedule k) + 1) * ((d : ℝ) / N) :=
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_relative_diagonal_le
        grid dimension width large fine schedule ξ ζ k
    _ ≤ 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
      have scale := upper (schedule k)
      have grid_cost : 0 ≤ (d : ℝ) / N := by positivity
      linarith [mul_nonneg grid_cost (sub_nonneg.mpr scale)]

theorem dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k)) ≤ 1 := by
  let continuation :=
    dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ
  let escape : ℕ → ℝ := fun k =>
    dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k
  have continuation_nonnegative : ∀ k, 0 ≤ continuation k := by
    intro k
    exact
      dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k false false
  have stage : ∀ k, continuation k + escape k ≤ 1 := by
    intro k
    have actual :=
      dSVDensityRationalHeterogeneousPhysicalStage_partition
        grid dimension width schedule ξ ζ k
    dsimp [continuation, escape]
    linarith
  simpa only [dSVDensityRationalHeterogeneousPhysicalSurvival, ge_iff_le]
    using dSVHeterogeneousRealStopping_escape_budget
      continuation escape continuation_nonnegative stage L

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_le_targetDistance
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (upper : ∀ s, width s ≤ W) (W_nonnegative : 0 ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
  let bound : ℝ :=
    8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
      2 * (W + 1) * ((d : ℝ) / N)
  have bound_nonnegative : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have escape_budget :=
    dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
      grid dimension width schedule ξ ζ
  rw [
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_ratioLedger]
  change
    (∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) *
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
          N width schedule ξ ζ k) ≤ bound
  calc
    _ ≤ ∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) * bound := by
      apply Finset.sum_le_sum
      intro k member
      have active : k < L := Finset.mem_range.mp member
      let stage : Fin L := ⟨k, active⟩
      have ratio :=
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_targetDistance
          grid dimension width large fine upper schedule ξ ζ stage
      have survival_nonnegative :=
        dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
          N width schedule ξ ζ k
      have success_nonnegative :=
        dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
          N width schedule ξ ζ k true true
      have asynchronous_nonnegative :
          0 ≤
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k := by
        exact add_nonneg
          (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
            N width schedule ξ ζ k true false)
          (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
            N width schedule ξ ζ k false true)
      have coefficient_nonnegative :
          0 ≤
            dSVDensityRationalHeterogeneousPhysicalSurvival
                N width schedule ξ ζ k *
              (dSVDensityRationalHeterogeneousPhysicalStageSuccess
                  N width schedule ξ ζ k +
                dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
                  N width schedule ξ ζ k) :=
        mul_nonneg survival_nonnegative
          (add_nonneg success_nonnegative asynchronous_nonnegative)
      apply mul_le_mul_of_nonneg_left _ coefficient_nonnegative
      simpa only [bound] using ratio
    _ =
      (∑ k ∈ Finset.range L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          (dSVDensityRationalHeterogeneousPhysicalStageSuccess
              N width schedule ξ ζ k +
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k)) * bound := by
      rw [Finset.sum_mul]
    _ ≤ bound := by
      linarith [mul_nonneg bound_nonnegative
        (sub_nonneg.mpr escape_budget)]

/-- The error rate associated with DSV density rational heterogeneous physical uniform escape. -/
def dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
    (d : ℕ) (W : ℝ) : ℝ :=
  1 / (2 * (W + 1) * (d : ℝ))

theorem
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_pos
    {d : ℕ} (dimension : 0 < d)
    {W : ℝ} (W_nonnegative : 0 ≤ W) :
    0 < dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
      d W := by
  unfold dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
  positivity

theorem
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_le_half
    {d : ℕ} (dimension : 0 < d)
    {W : ℝ} (W_nonnegative : 0 ≤ W) :
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
      d W ≤ (1 / 2 : ℝ) := by
  have real_dimension : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have dimension_one : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt dimension))
  have denominator : 0 < 2 * (W + 1) * (d : ℝ) := by
    positivity
  unfold dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
  apply (div_le_div_iff₀ denominator (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [mul_nonneg W_nonnegative real_dimension.le]

theorem
    dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_ge_uniform
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
        d W ≤
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ := by
  have real_dimension : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have width_positive : 0 < width (schedule k) :=
    lt_of_lt_of_le (by norm_num) (large (schedule k))
  have wide_positive : 0 < 2 * (W + 1) * (d : ℝ) := by
    positivity
  have stage_positive :
      0 < 2 * (width (schedule k) + 1) * (d : ℝ) := by
    positivity
  have width_bound := upper (schedule k)
  calc
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
        d W = 1 / (2 * (W + 1) * (d : ℝ)) := rfl
    _ ≤ 1 / (2 * (width (schedule k) + 1) * (d : ℝ)) := by
      apply (div_le_div_iff₀ wide_positive stage_positive).mpr
      linarith [mul_nonneg real_dimension.le
        (sub_nonneg.mpr width_bound)]
    _ ≤ dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ :=
      dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_lower
        grid dimension width large fine schedule ξ k

theorem
    dSVDensityRationalHeterogeneousPhysicalStageContinue_le_uniform
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageContinue
        N width schedule ξ ζ k.val ≤
      1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W := by
  have floor :=
    dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_ge_uniform
      grid dimension width large fine W_nonnegative upper schedule ξ k
  have escape :=
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
      grid dimension width schedule ξ ζ k
  have partition :=
    dSVDensityRationalHeterogeneousPhysicalStage_partition
      grid dimension width schedule ξ ζ k.val
  linarith

theorem
    dSVDensityRationalHeterogeneousPhysicalTerminalMass_le_pow
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalTerminalMass
        N width schedule ξ ζ ≤
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ L := by
  let continuation :=
    dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ
  let c : ℝ :=
    1 - dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
      d W
  have rate_bounded :=
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_le_half
      dimension W_nonnegative
  have c_nonnegative : 0 ≤ c := by
    dsimp [c]
    linarith
  have continuation_nonnegative : ∀ k, 0 ≤ continuation k := by
    intro k
    exact
      dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k false false
  have prefix_bound : ∀ k : ℕ, k ≤ L →
      dSVHeterogeneousRealPrefix continuation k ≤ c ^ k := by
    intro k
    induction k with
    | zero =>
        intro _
        simp only [dSVHeterogeneousRealPrefix, range_zero, prod_empty, pow_zero, Std.le_refl]
    | succ k induction =>
        intro within
        have active : k < L := by omega
        have previous := induction (by omega : k ≤ L)
        let stage : Fin L := ⟨k, active⟩
        have next :=
          dSVDensityRationalHeterogeneousPhysicalStageContinue_le_uniform
            grid dimension width large fine W_nonnegative upper
            schedule ξ ζ stage
        change continuation k ≤ c at next
        rw [dSVHeterogeneousRealPrefix_succ, pow_succ]
        exact mul_le_mul previous next
          (continuation_nonnegative k) (pow_nonneg c_nonnegative k)
  change dSVHeterogeneousRealPrefix continuation L ≤ c ^ L
  exact prefix_bound L (le_refl L)

theorem
    dSVDensityRationalHeterogeneousPhysical_exists_positive_horizon
    {d : ℕ} (dimension : 0 < d)
    {W ε : ℝ} (W_nonnegative : 0 ≤ W) (precision : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ L ≤ ε ^ 2 := by
  have rate :=
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_pos
      dimension W_nonnegative
  have bounded :=
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_le_half
      dimension W_nonnegative
  have continuation : 0 ≤
      1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W := by
    linarith
  have square : 0 < ε ^ 2 := sq_pos_of_pos precision
  obtain ⟨k, tail⟩ := exists_pow_lt_of_lt_one square
    (show
      1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W < 1 by linarith)
  refine ⟨k + 1, by omega, ?_⟩
  calc
    (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ (k + 1) ≤
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ k := by
      rw [pow_succ]
      nlinarith [pow_nonneg continuation k]
    _ ≤ ε ^ 2 := tail.le

theorem
    dSVDensityRationalHeterogeneousPhysicalTerminalMass_le_horizon
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W ε : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (tail :
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ L ≤ ε ^ 2)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalTerminalMass
        N width schedule ξ ζ ≤ ε ^ 2 :=
  (dSVDensityRationalHeterogeneousPhysicalTerminalMass_le_pow
    grid dimension width large fine W_nonnegative upper
    schedule ξ ζ).trans tail

end

section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The probability weight for fair partition. -/
def fairPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  ((2 : ℝ) ^ Fintype.card α)⁻¹

/-- The probability weight for reverse partition. -/
def reversePartitionWeight (s : Finset α) : ℝ :=
  fairPartitionWeight α *
    (2 * (s.card : ℝ) / (Fintype.card α : ℝ))

/-- The probability weight for forward marked partition. -/
def forwardMarkedPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  2 * fairPartitionWeight α / (Fintype.card α : ℝ)

/-- The probability weight for reverse marked partition. -/
def reverseMarkedPartitionWeight (s : Finset α) (i : α) : ℝ :=
  if i ∈ s then reversePartitionWeight s / (s.card : ℝ) else 0

omit [DecidableEq α] in
theorem fairPartitionWeight_pos : 0 < fairPartitionWeight α := by
  unfold fairPartitionWeight
  positivity

omit [DecidableEq α] in
theorem fairPartitionWeight_nonneg : 0 ≤ fairPartitionWeight α :=
  fairPartitionWeight_pos.le

omit [DecidableEq α] in
theorem fairPartitionWeight_sum :
    (∑ _s : Finset α, fairPartitionWeight α) = 1 := by
  simp only [fairPartitionWeight, sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
    not_false_eq_true, mul_inv_cancel₀]

omit [DecidableEq α] in
theorem reversePartitionWeight_nonneg (s : Finset α) :
    0 ≤ reversePartitionWeight s := by
  unfold reversePartitionWeight
  exact mul_nonneg fairPartitionWeight_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le s.card))
      (by exact_mod_cast Nat.zero_le (Fintype.card α)))

omit [DecidableEq α] in
@[simp] theorem reversePartitionWeight_empty :
    reversePartitionWeight (α := α) ∅ = 0 := by
  simp only [reversePartitionWeight, card_empty, CharP.cast_eq_zero, mul_zero, zero_div]

omit [DecidableEq α] in
theorem reversePartitionWeight_pos_iff
    (hα : 0 < Fintype.card α) (s : Finset α) :
    0 < reversePartitionWeight s ↔ s.Nonempty := by
  constructor
  · intro hs
    apply Finset.card_pos.mp
    by_contra hcard
    have hzero : s.card = 0 := Nat.eq_zero_of_not_pos hcard
    simp only [reversePartitionWeight, hzero, CharP.cast_eq_zero, mul_zero, zero_div,
      lt_self_iff_false] at hs
  · intro hs
    unfold reversePartitionWeight
    have hcard : 0 < s.card := Finset.card_pos.mpr hs
    exact mul_pos fairPartitionWeight_pos
      (div_pos
        (mul_pos (by norm_num) (by exact_mod_cast hcard))
        (by exact_mod_cast hα))

theorem reverseMarkedPartitionWeight_eq_forward
    {s : Finset α} {i : α} (hi : i ∈ s) :
    reverseMarkedPartitionWeight s i =
      forwardMarkedPartitionWeight α := by
  have hs : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr ⟨i, hi⟩))
  simp only [reverseMarkedPartitionWeight, ite_eq_left hi,
    reversePartitionWeight, forwardMarkedPartitionWeight]
  field_simp

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


private def rightSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
     [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dB) : ℝ :=
  bornTracePairing ρ.matrix F
    (positiveMatrixSpectralAtom G hG i)

theorem rightSpectralBornWeight_nonneg
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
     [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dB) :
    0 ≤ rightSpectralBornWeight ρ F G hG i := by
  exact trace_mul_posSemidef_nonneg ρ.positive
    (hF.kronecker (positiveMatrixSpectralAtom_posSemidef G hG i))

theorem rightSpectralBornWeight_sum
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
     [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    (∑ i : dB, rightSpectralBornWeight ρ F G hG i) =
      bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
  unfold rightSpectralBornWeight
  calc
    (∑ i : dB,
      bornTracePairing ρ.matrix F
        (positiveMatrixSpectralAtom G hG i)) =
      bornTracePairing ρ.matrix F
        (∑ i : dB, positiveMatrixSpectralAtom G hG i) := by
          simp only [map_sum]
    _ = bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
      rw [positiveMatrixSpectralAtom_sum]

theorem rightSpectralBornWeight_moment
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
     [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    (∑ i : dB,
      rightSpectralBornWeight ρ F G hG i *
        hG.isHermitian.eigenvalues i) =
      bornTracePairing ρ.matrix F G := by
  have hspectral : G =
      ∑ i : dB,
        hG.isHermitian.eigenvalues i •
          positiveMatrixSpectralAtom G hG i := by
    calc
      G = cfc (fun z : ℝ => z) G :=
        (cfc_id' ℝ G hG.isHermitian).symm
      _ = _ := positiveMatrix_cfc_spectral_sum G hG (fun z : ℝ => z)
  have h := congrArg (bornTracePairing ρ.matrix F) hspectral
  simp only [map_sum, map_smul, smul_eq_mul] at h
  calc
    (∑ i : dB,
      rightSpectralBornWeight ρ F G hG i *
        hG.isHermitian.eigenvalues i) =
      ∑ i : dB,
        hG.isHermitian.eigenvalues i *
          bornTracePairing ρ.matrix F
            (positiveMatrixSpectralAtom G hG i) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold rightSpectralBornWeight
        ring
    _ = bornTracePairing ρ.matrix F G := h.symm

theorem rightSpectralBornWeight_entropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
     [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) =
      ∑ i : dB,
        rightSpectralBornWeight ρ F G hG i *
          (hG.isHermitian.eigenvalues i *
            Real.log (hG.isHermitian.eigenvalues i)) := by
  have hspectral := positiveMatrix_cfc_spectral_sum G hG
    (fun z : ℝ => z * Real.log z)
  have h := congrArg (bornTracePairing ρ.matrix F) hspectral
  simp only [map_sum, map_smul, smul_eq_mul] at h
  calc
    bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) =
      ∑ i : dB,
        (hG.isHermitian.eigenvalues i *
          Real.log (hG.isHermitian.eigenvalues i)) *
          bornTracePairing ρ.matrix F
            (positiveMatrixSpectralAtom G hG i) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      unfold rightSpectralBornWeight
      ring

theorem rightSpectralBornWeight_negEntropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
     [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) =
      ∑ i : dB,
        rightSpectralBornWeight ρ F G hG i *
          Real.negMulLog (hG.isHermitian.eigenvalues i) := by
  rw [rightSpectralBornWeight_entropy ρ F G hG,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.negMulLog, neg_mul, mul_neg]

theorem bornTracePairing_le_one_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (hFcomplement : (1 - F).PosSemidef) :
    bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) ≤ 1 := by
  have hpositive : 0 ≤ bornTracePairing ρ.matrix
      (1 - F) (1 : Matrix dB dB ℂ) :=
    trace_mul_posSemidef_nonneg ρ.positive
      (hFcomplement.kronecker Matrix.PosSemidef.one)
  have hdiff : bornTracePairing ρ.matrix
      (1 - F) (1 : Matrix dB dB ℂ) =
      bornTracePairing ρ.matrix
        (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) -
      bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
    simp only [map_sub, LinearMap.sub_apply]
  rw [hdiff, bornTracePairing_one_one] at hpositive
  linarith

theorem matrixLogEntropy_born_lower_bound_right
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) := by
  classical
  have hp_nonneg : 0 ≤ bornTracePairing ρ.matrix F G :=
    trace_mul_posSemidef_nonneg ρ.positive (hF.kronecker hG)
  have hmass_le :
      bornTracePairing ρ.matrix F G ≤
        bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
    calc
      bornTracePairing ρ.matrix F G =
        ∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            hG.isHermitian.eigenvalues i :=
          (rightSpectralBornWeight_moment ρ F G hG).symm
      _ ≤ ∑ i : dB, rightSpectralBornWeight ρ F G hG i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right
          (rightSpectralBornWeight_nonneg ρ F hF G hG i)
          (positiveContraction_eigenvalue_le_one G hG hGcomplement i)
      _ = bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) :=
        rightSpectralBornWeight_sum ρ F G hG
  by_cases hp : bornTracePairing ρ.matrix F G = 0
  · have hzero :
        (∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            hG.isHermitian.eigenvalues i) = 0 := by
        rw [rightSpectralBornWeight_moment, hp]
    have hterm (i : dB) :
        rightSpectralBornWeight ρ F G hG i *
          hG.isHermitian.eigenvalues i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg
          (rightSpectralBornWeight_nonneg ρ F hF G hG j)
          (hG.eigenvalues_nonneg j))).mp hzero i (Finset.mem_univ i)
    have hentropy :
        (∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            Real.negMulLog (hG.isHermitian.eigenvalues i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases mul_eq_zero.mp (hterm i) with hw | he
      · simp only [hw, zero_mul]
      · simp only [he, Real.negMulLog_zero, mul_zero]
    calc
      -bornTracePairing ρ.matrix F
          (cfc (fun z : ℝ => z * Real.log z) G) =
        ∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            Real.negMulLog (hG.isHermitian.eigenvalues i) :=
          rightSpectralBornWeight_negEntropy ρ F G hG
      _ = 0 := hentropy
      _ ≤ Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [hp]
        simp only [Real.negMulLog_zero, Std.le_refl]
  · have hp_pos : 0 < bornTracePairing ρ.matrix F G :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hp)
    have hW_pos : 0 <
        bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) :=
      lt_of_lt_of_le hp_pos hmass_le
    have hscalar := finite_weighted_entropy_le_of_weight_bound
      (Finset.univ : Finset dB)
      (rightSpectralBornWeight ρ F G hG)
      hG.isHermitian.eigenvalues
      (W := bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ))
      (N := (1 : ℝ))
      (p := bornTracePairing ρ.matrix F G)
      (fun i _ => rightSpectralBornWeight_nonneg ρ F hF G hG i)
      (fun i _ => hG.eigenvalues_nonneg i)
      hW_pos hp_pos
      (rightSpectralBornWeight_sum ρ F G hG)
      (rightSpectralBornWeight_moment ρ F G hG)
      (bornTracePairing_le_one_one ρ F hFcomplement)
    calc
      -bornTracePairing ρ.matrix F
          (cfc (fun z : ℝ => z * Real.log z) G) =
        ∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            Real.negMulLog (hG.isHermitian.eigenvalues i) :=
        rightSpectralBornWeight_negEntropy ρ F G hG
      _ ≤ bornTracePairing ρ.matrix F G *
          Real.log (1 / bornTracePairing ρ.matrix F G) := hscalar
      _ = Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [one_div, Real.log_inv]
        simp only [mul_neg, Real.negMulLog, neg_mul]

section HistoryNormalization

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def fullSubsetHistoryFieldEquiv
    {n : ℕ} (D L : Finset (Fin n)) :
    FullSubsetHistory X Y n D L ≃
      (({i : Fin n // i ∈ D} → X × Y) ×
       ({i : Fin n // i ∈ L} → X) ×
       ({i : Fin n // i ∈ fullHistoryRemaining n D L} → Y)) where
  toFun h :=
    (fun i => (h.aliceConditioned i, h.bobConditioned i),
      h.aliceRevealed, h.bobRemaining)
  invFun t :=
    ⟨fun i => (t.1 i).1,
      fun i => (t.1 i).2,
      t.2.1, t.2.2⟩
  left_inv h := by
    apply FullSubsetHistory.ext <;> rfl
  right_inv t := by
    rcases t with ⟨q, x, y⟩
    simp only [Prod.mk.eta]

theorem fullHistoryWeight_sum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) :
    (∑ h : FullSubsetHistory X Y n D L,
      fullHistoryWeight G h) = 1 := by
  classical
  let Dsub := {i : Fin n // i ∈ D}
  let Lsub := {i : Fin n // i ∈ L}
  let Rsub := {i : Fin n // i ∈ fullHistoryRemaining n D L}
  have hD :
      (∑ q : Dsub → X × Y,
        ∏ i : Dsub, G.questionWeight (q i).1 (q i).2) = 1 := by
    calc
      (∑ q : Dsub → X × Y,
        ∏ i : Dsub, G.questionWeight (q i).1 (q i).2) =
        ∏ _i : Dsub, ∑ z : X × Y,
          G.questionWeight z.1 z.2 := by
          exact (Fintype.prod_sum
            (fun _i : Dsub => fun z : X × Y =>
              G.questionWeight z.1 z.2)).symm
      _ = ∏ _i : Dsub, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Fintype.sum_prod_type]
        exact G.weight_normalized
      _ = 1 := by simp only [prod_const_one]
  have hL :
      (∑ x : Lsub → X,
        ∏ i : Lsub, G.marginalX (x i)) = 1 := by
    calc
      (∑ x : Lsub → X,
        ∏ i : Lsub, G.marginalX (x i)) =
        ∏ _i : Lsub, ∑ z : X, G.marginalX z := by
          exact (Fintype.prod_sum
            (fun _i : Lsub => fun z : X => G.marginalX z)).symm
      _ = 1 := by simp only [G.marginalX_normalized, prod_const_one]
  have hR :
      (∑ y : Rsub → Y,
        ∏ i : Rsub, G.marginalY (y i)) = 1 := by
    calc
      (∑ y : Rsub → Y,
        ∏ i : Rsub, G.marginalY (y i)) =
        ∏ _i : Rsub, ∑ z : Y, G.marginalY z := by
          exact (Fintype.prod_sum
            (fun _i : Rsub => fun z : Y => G.marginalY z)).symm
      _ = 1 := by simp only [G.marginalY_normalized, prod_const_one]
  let f : (Dsub → X × Y) × (Lsub → X) × (Rsub → Y) → ℝ :=
    fun t =>
      (∏ i : Dsub, G.questionWeight (t.1 i).1 (t.1 i).2) *
      (∏ i : Lsub, G.marginalX (t.2.1 i)) *
      (∏ i : Rsub, G.marginalY (t.2.2 i))
  calc
    (∑ h : FullSubsetHistory X Y n D L,
      fullHistoryWeight G h) =
      ∑ q : Dsub → X × Y,
      ∑ x : Lsub → X,
      ∑ y : Rsub → Y,
        (∏ i : Dsub, G.questionWeight (q i).1 (q i).2) *
        (∏ i : Lsub, G.marginalX (x i)) *
        (∏ i : Rsub, G.marginalY (y i)) := by
        simpa only [fullHistoryWeight, fullSubsetHistoryFieldEquiv,
          Equiv.coe_fn_mk, Fintype.sum_prod_type,
          f, Dsub, Lsub, Rsub] using
          (fullSubsetHistoryFieldEquiv (X := X) (Y := Y) D L).sum_comp f
    _ =
      (∑ q : Dsub → X × Y,
        ∏ i : Dsub, G.questionWeight (q i).1 (q i).2) *
      (∑ x : Lsub → X,
        ∏ i : Lsub, G.marginalX (x i)) *
      (∑ y : Rsub → Y,
        ∏ i : Rsub, G.marginalY (y i)) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      congr 1
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ = 1 := by rw [hD, hL, hR]; norm_num

theorem fullHistoryWinIndicator_le_one
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    fullHistoryWinIndicator G h α β ≤ 1 := by
  classical
  unfold fullHistoryWinIndicator
  split <;> norm_num

end HistoryNormalization

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The full history answer count construction used in the quantum parallel-repetition argument. -/
def fullHistoryAnswerCount
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (Fintype.card ({i : Fin n // i ∈ D} → A) : ℝ) *
    (Fintype.card ({i : Fin n // i ∈ D} → B) : ℝ)

theorem fullHistoryAnswerCount_eq
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :
    fullHistoryAnswerCount (A := A) (B := B) D =
      (Fintype.card A : ℝ) ^ D.card *
        (Fintype.card B : ℝ) ^ D.card := by
  classical
  simp only [fullHistoryAnswerCount, Fintype.card_pi, univ_eq_attach, prod_const, card_attach,
    Nat.cast_pow]

/-- The type used to represent full history entropy atom in the exact sampling construction. -/
abbrev FullHistoryEntropyAtom
    (X Y A B : Type*)
    (n : ℕ) (D L : Finset (Fin n)) :=
  FullSubsetHistory X Y n D L ×
    ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

/-- The probability weight for full history atom counting. -/
def fullHistoryAtomCountingWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  fullHistoryWeight G t.1 *
    fullHistoryWinIndicator G t.1 t.2.1 t.2.2

/-- The total probability mass of full history atom born. -/
def fullHistoryAtomBornMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  bornTracePairing S.state.matrix
    (fullHistoryAliceFilter G n S D L t.1 t.2.1)
    (fullHistoryBobFilter G n S D L t.1 t.2.2)

theorem fullHistoryAtomCountingWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) :
    0 ≤ fullHistoryAtomCountingWeight G D L t := by
  exact mul_nonneg (fullHistoryWeight_nonneg G t.1)
    (fullHistoryWinIndicator_nonneg G t.1 t.2.1 t.2.2)

theorem fullHistoryAtomBornMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) :
    0 ≤ fullHistoryAtomBornMass G n S D L t := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    ((fullHistoryAliceFilter_posSemidef G n S D L t.1 t.2.1).kronecker
      (fullHistoryBobFilter_posSemidef G n S D L t.1 t.2.2))

theorem bornTracePairing_contractions_le_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    bornTracePairing ρ.matrix F G ≤ 1 := by
  have hpositive : 0 ≤
      bornTracePairing ρ.matrix (1 - F) G :=
    trace_mul_posSemidef_nonneg ρ.positive
      (hFcomplement.kronecker hG)
  have hdiff : bornTracePairing ρ.matrix (1 - F) G =
      bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G -
        bornTracePairing ρ.matrix F G := by
    simp only [map_sub, LinearMap.sub_apply]
  rw [hdiff] at hpositive
  have hone := bornTracePairing_one_le_one ρ G hGcomplement
  linarith

theorem fullHistoryAtomBornMass_le_one
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) :
    fullHistoryAtomBornMass G n S D L t ≤ 1 := by
  exact bornTracePairing_contractions_le_one S.state
    (fullHistoryAliceFilter G n S D L t.1 t.2.1)
    (fullHistoryAliceFilter_complement_posSemidef G n S D L t.1 t.2.1)
    (fullHistoryBobFilter G n S D L t.1 t.2.2)
    (fullHistoryBobFilter_posSemidef G n S D L t.1 t.2.2)
    (fullHistoryBobFilter_complement_posSemidef G n S D L t.1 t.2.2)

theorem fullHistoryAtomCountingWeight_sum_le
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) :
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t) ≤
      fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  calc
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t) =
      ∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β := by
        simp only [fullHistoryAtomCountingWeight, Fintype.sum_prod_type]
    _ ≤ ∑ h : FullSubsetHistory X Y n D L,
        ∑ _α : {i : Fin n // i ∈ D} → A,
        ∑ _β : {i : Fin n // i ∈ D} → B,
          fullHistoryWeight G h := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro α _
      apply Finset.sum_le_sum
      intro β _
      exact mul_le_of_le_one_right
        (fullHistoryWeight_nonneg G h)
        (fullHistoryWinIndicator_le_one G h α β)
    _ = fullHistoryAnswerCount (A := A) (B := B) D *
        (∑ h : FullSubsetHistory X Y n D L,
          fullHistoryWeight G h) := by
      simp only [sum_const, card_univ, Fintype.card_pi, univ_eq_attach, prod_const, card_attach,
        nsmul_eq_mul, Nat.cast_pow, fullHistoryAnswerCount, mul_sum, mul_assoc]
    _ = fullHistoryAnswerCount (A := A) (B := B) D := by
      rw [fullHistoryWeight_sum G D L]
      ring

theorem fullHistoryAtomBornMass_sum
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t *
        fullHistoryAtomBornMass G n S D L t) =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) := by
  classical
  simpa only [fullHistoryAtomCountingWeight, fullHistoryAtomBornMass, Fintype.sum_prod_type] using
    fullSubsetHistory_mass_eq_postselection G n S D L hL

theorem fullHistoryAtomEntropy_le
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t *
        Real.negMulLog (fullHistoryAtomBornMass G n S D L t)) ≤
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
        Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D /
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) := by
  classical
  let p := (strategyEventLaw (G.repeat n) S).eventMass
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
  let w := fullHistoryAtomCountingWeight G D L
  let q := fullHistoryAtomBornMass G n S D L
  let W : ℝ := ∑ t : FullHistoryEntropyAtom X Y A B n D L, w t
  have hmass :
      (∑ t : FullHistoryEntropyAtom X Y A B n D L,
        w t * q t) = p :=
    fullHistoryAtomBornMass_sum G n S D L hL
  have hpW : p ≤ W := by
    calc
      p = ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          w t * q t := hmass.symm
      _ ≤ ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          w t := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_of_le_one_right
          (fullHistoryAtomCountingWeight_nonneg G D L t)
          (fullHistoryAtomBornMass_le_one G n S D L t)
      _ = W := rfl
  have hW : 0 < W := lt_of_lt_of_le hp hpW
  have hbound : W ≤ fullHistoryAnswerCount (A := A) (B := B) D :=
    fullHistoryAtomCountingWeight_sum_le G D L
  exact finite_weighted_entropy_le_of_weight_bound
    (Finset.univ : Finset (FullHistoryEntropyAtom X Y A B n D L))
    w q
    (fun t _ => fullHistoryAtomCountingWeight_nonneg G D L t)
    (fun t _ => fullHistoryAtomBornMass_nonneg G n S D L t)
    hW hp rfl hmass hbound

theorem fullHistoryAliceEntropyPotential_lower_bound
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    -((strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
      Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D))) ≤
      fullHistoryAliceEntropyPotential G n S D L := by
  classical
  have hpoint :
      -fullHistoryAliceEntropyPotential G n S D L ≤
        ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          fullHistoryAtomCountingWeight G D L t *
            Real.negMulLog (fullHistoryAtomBornMass G n S D L t) := by
    simp only [fullHistoryAliceEntropyPotential,
      fullHistoryAtomCountingWeight, fullHistoryAtomBornMass,
      Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro h _
    apply Finset.sum_le_sum
    intro α _
    apply Finset.sum_le_sum
    intro β _
    have hw := mul_nonneg (fullHistoryWeight_nonneg G h)
      (fullHistoryWinIndicator_nonneg G h α β)
    have hlocal := matrixLogEntropy_born_lower_bound_left S.state
      (fullHistoryAliceFilter G n S D L h α)
      (fullHistoryAliceFilter_posSemidef G n S D L h α)
      (fullHistoryAliceFilter_complement_posSemidef G n S D L h α)
      (fullHistoryBobFilter G n S D L h β)
      (fullHistoryBobFilter_posSemidef G n S D L h β)
      (fullHistoryBobFilter_complement_posSemidef G n S D L h β)
    linarith [mul_le_mul_of_nonneg_left hlocal hw]
  have hscalar := fullHistoryAtomEntropy_le G n S D L hL hp
  linarith

end

section

open scoped BigOperators

/-- A transcript in which one additional coordinate is being revealed. -/
@[ext (iff := false)] structure FullCoordinateRevealHistory
    (X Y : Type*)
    (n : ℕ) (D L : Finset (Fin n)) (i : Fin n) where
  /-- Alice's conditioned part of the transcript. -/
  aliceConditioned : {j : Fin n // j ∈ D} → X
  /-- Bob's conditioned part of the transcript. -/
  bobConditioned : {j : Fin n // j ∈ D} → Y
  /-- Alice's already revealed questions. -/
  aliceRevealed : {j : Fin n // j ∈ L} → X
  /-- Bob's questions outside the revealed coordinates. -/
  bobRemaining :
    {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → Y
  deriving Fintype

theorem fullHistoryRemaining_insert_subset
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n D (insert i L) ⊆
      fullHistoryRemaining n D L := by
  intro j hj
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
  exact ⟨hj.1, fun h => hj.2 (Or.inr h)⟩

private def fullCoordinateBaseOfOldHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D L) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := h.aliceRevealed
  bobRemaining := fun j => h.bobRemaining
    ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩

/-- The transcript representation for full coordinate old. -/
def fullCoordinateOldHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (y : Y) : FullSubsetHistory X Y n D L := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned, h.aliceRevealed,
    fun j => if hj : (j : Fin n) = i then y else
      h.bobRemaining ⟨j, ?_⟩⟩
  have hjD : (j : Fin n) ∉ D :=
    (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp j.property).1).2
  have hjL : (j : Fin n) ∉ L :=
    (Finset.mem_sdiff.mp j.property).2
  simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hjD, not_false_eq_true, and_self,
    mem_insert, hj, hjL, or_self]

private def fullCoordinateBaseOfNewHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D (insert i L)) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := fun j => h.aliceRevealed
    ⟨j, Finset.mem_insert_of_mem j.property⟩
  bobRemaining := h.bobRemaining

/-- The transcript representation for full coordinate new. -/
def fullCoordinateNewHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (x : X) : FullSubsetHistory X Y n D (insert i L) := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned,
    fun j => if hj : (j : Fin n) = i then x else
      h.aliceRevealed ⟨j, ?_⟩,
    h.bobRemaining⟩
  exact (Finset.mem_insert.mp j.property).resolve_left hj

private def fullCoordinateOldHistoryEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    FullSubsetHistory X Y n D L ≃
      FullCoordinateRevealHistory X Y n D L i × Y where
  toFun h :=
    (fullCoordinateBaseOfOldHistory D L i h,
      h.bobRemaining
        ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD, not_false_eq_true,
                 and_self, hiL]⟩)
  invFun t := fullCoordinateOldHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · subst i
        simp only [fullCoordinateOldHistory, fullCoordinateBaseOfOldHistory, SetLike.coe_eq_coe,
          Subtype.coe_eta, dite_eq_ite, ↓reduceIte]
      · simp only [fullCoordinateOldHistory, fullCoordinateBaseOfOldHistory, Subtype.coe_eta,
          dite_eq_ite, hj, ↓reduceIte]
  right_inv t := by
    rcases t with ⟨h, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          have hnot : (j : Fin n) ∉ insert i L :=
            (Finset.mem_sdiff.mp j.property).2
          apply hnot
          simp only [he, mem_insert, true_or]
        simp only [fullCoordinateBaseOfOldHistory, fullCoordinateOldHistory, hj]
        split <;> simp_all
    · simp only [fullCoordinateOldHistory, ↓reduceDIte]

private def fullCoordinateNewHistoryEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L) :
    FullSubsetHistory X Y n D (insert i L) ≃
      FullCoordinateRevealHistory X Y n D L i × X where
  toFun h :=
    (fullCoordinateBaseOfNewHistory D L i h,
      h.aliceRevealed ⟨i, Finset.mem_insert_self i L⟩)
  invFun t := fullCoordinateNewHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i L⟩ :
              {j : Fin n // j ∈ insert i L}) :=
          Subtype.ext hj
        subst j
        simp only [fullCoordinateNewHistory, fullCoordinateBaseOfNewHistory, Subtype.coe_eta,
          dite_eq_ite, ↓reduceIte]
      · simp only [fullCoordinateNewHistory, fullCoordinateBaseOfNewHistory, Subtype.coe_eta,
          dite_eq_ite, hj, ↓reduceIte]
    · rfl
  right_inv t := by
    rcases t with ⟨h, x⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiL (he ▸ j.property)
        simp only [fullCoordinateBaseOfNewHistory, fullCoordinateNewHistory, Subtype.coe_eta,
          dite_eq_ite, hj, ↓reduceIte]
      · rfl
    · simp only [fullCoordinateNewHistory, ↓reduceDIte]

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


theorem finsetSubtype_prod_insert
    {ι T : Type*} [DecidableEq ι] [CommMonoid T]
    (s : Finset ι) (i : ι) (hi : i ∉ s)
    (f : {j : ι // j ∈ insert i s} → T) :
    (∏ j : {j : ι // j ∈ insert i s}, f j) =
      f ⟨i, Finset.mem_insert_self i s⟩ *
        ∏ j : {j : ι // j ∈ s},
          f ⟨j, Finset.mem_insert_of_mem j.property⟩ := by
  classical
  let e := Finset.subtypeInsertEquivOption hi
  let g : Option {j : ι // j ∈ s} → T
    | none => f ⟨i, Finset.mem_insert_self i s⟩
    | some j => f ⟨j, Finset.mem_insert_of_mem j.property⟩
  have hcomp (j : {j : ι // j ∈ insert i s}) :
      g (e j) = f j := by
    rcases j with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      simp only [subtypeInsertEquivOption, Equiv.coe_fn_mk, ↓reduceDIte, g, e]
    · simp only [subtypeInsertEquivOption, Equiv.coe_fn_mk, hji, ↓reduceDIte, g, e]
  calc
    (∏ j : {j : ι // j ∈ insert i s}, f j) =
      ∏ j : {j : ι // j ∈ insert i s}, g (e j) := by
        apply Finset.prod_congr rfl
        intro j _
        exact (hcomp j).symm
    _ = ∏ j : Option {j : ι // j ∈ s}, g j := e.prod_comp g
    _ = g none * ∏ j : {j : ι // j ∈ s}, g (some j) :=
      Fintype.prod_option g
    _ = _ := rfl

private def fullHistoryRemainingCoordinateEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} ≃
      Option {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} where
  toFun j :=
    if hj : (j : Fin n) = i then none
    else some ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hjD, not_false_eq_true, and_self,
        mem_insert, hj, hjL, or_self]⟩
  invFun
    | none => ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD, not_false_eq_true,
                       and_self, hiL]⟩
    | some j =>
      ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩
  left_inv j := by
    apply Subtype.ext
    by_cases hj : (j : Fin n) = i
    · simp only [hj, ↓reduceDIte]
    · simp only [hj, ↓reduceDIte, Subtype.coe_eta]
  right_inv j := by
    cases j with
    | none => simp
    | some j =>
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp only [he, mem_insert, true_or]
      simp only [hj, ↓reduceDIte]

theorem fullHistoryRemaining_prod_split
    {n : ℕ} {T : Type*} [CommMonoid T]
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (f : {j : Fin n // j ∈ fullHistoryRemaining n D L} → T) :
    (∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L}, f j) =
      f ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD, not_false_eq_true,
                 and_self, hiL]⟩ *
        ∏ j : {j : Fin n //
          j ∈ fullHistoryRemaining n D (insert i L)},
          f ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩ := by
  classical
  let e := fullHistoryRemainingCoordinateEquiv D L i hiD hiL
  let g : Option {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → T
    | none => f ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD,
                         not_false_eq_true, and_self, hiL]⟩
    | some j =>
      f ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩
  have hcomp (j : {j : Fin n //
      j ∈ fullHistoryRemaining n D L}) :
      g (e j) = f j := by
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD,
                        not_false_eq_true, and_self, hiL]⟩ :
            {j : Fin n // j ∈ fullHistoryRemaining n D L}) :=
        Subtype.ext hj
      subst j
      simp only [fullHistoryRemainingCoordinateEquiv, Equiv.coe_fn_mk, ↓reduceDIte, g, e]
    · simp only [fullHistoryRemainingCoordinateEquiv, Equiv.coe_fn_mk, hj, ↓reduceDIte,
        Subtype.coe_eta, g, e]
  calc
    (∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L}, f j) =
      ∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L},
        g (e j) := by
          apply Finset.prod_congr rfl
          intro j _
          exact (hcomp j).symm
    _ = ∏ j : Option {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)}, g j :=
      e.prod_comp g
    _ = g none * ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)}, g (some j) :=
      Fintype.prod_option g
    _ = _ := rfl

section CoordinateWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The probability weight for full coordinate base. -/
def fullCoordinateBaseWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i) : ℝ :=
  (∏ j : {j : Fin n // j ∈ D},
    G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
  (∏ j : {j : Fin n // j ∈ L},
    G.marginalX (h.aliceRevealed j)) *
  (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)},
    G.marginalY (h.bobRemaining j))

theorem fullCoordinateBaseWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i) :
    0 ≤ fullCoordinateBaseWeight G D L i h := by
  unfold fullCoordinateBaseWeight
  exact mul_nonneg
    (mul_nonneg
      (Finset.prod_nonneg fun j _ =>
        G.weight_nonneg (h.aliceConditioned j) (h.bobConditioned j))
      (Finset.prod_nonneg fun j _ =>
        G.marginalX_nonneg (h.aliceRevealed j)))
    (Finset.prod_nonneg fun j _ => G.marginalY_nonneg (h.bobRemaining j))

theorem fullCoordinateOldHistory_weight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (h : FullCoordinateRevealHistory X Y n D L i) (y : Y) :
    fullHistoryWeight G (fullCoordinateOldHistory D L i h y) =
      fullCoordinateBaseWeight G D L i h * G.marginalY y := by
  classical
  have hold (j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)}) :
      (fullCoordinateOldHistory D L i h y).bobRemaining
        ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩ =
      h.bobRemaining j := by
    have hj : (j : Fin n) ≠ i := by
      intro he
      have hnot : (j : Fin n) ∉ insert i L :=
        (Finset.mem_sdiff.mp j.property).2
      apply hnot
      simp only [he, mem_insert, true_or]
    simp only [fullCoordinateOldHistory, hj, ↓reduceDIte]
  unfold fullHistoryWeight fullCoordinateBaseWeight
  change
    (∏ j : {j : Fin n // j ∈ D},
      G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
    (∏ j : {j : Fin n // j ∈ L},
      G.marginalX (h.aliceRevealed j)) *
    (∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L},
      G.marginalY
        ((fullCoordinateOldHistory D L i h y).bobRemaining j)) = _
  rw [fullHistoryRemaining_prod_split D L i hiD hiL]
  simp_rw [hold]
  simp only [univ_eq_attach, fullCoordinateOldHistory, ↓reduceDIte]
  ring

theorem fullCoordinateNewHistory_weight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (h : FullCoordinateRevealHistory X Y n D L i) (x : X) :
    fullHistoryWeight G (fullCoordinateNewHistory D L i h x) =
      fullCoordinateBaseWeight G D L i h * G.marginalX x := by
  classical
  have hnew (j : {j : Fin n // j ∈ L}) :
      (fullCoordinateNewHistory D L i h x).aliceRevealed
        ⟨j, Finset.mem_insert_of_mem j.property⟩ =
      h.aliceRevealed j := by
    have hj : (j : Fin n) ≠ i := by
      intro he
      exact hiL (he ▸ j.property)
    simp only [fullCoordinateNewHistory, hj, ↓reduceDIte, Subtype.coe_eta]
  unfold fullHistoryWeight fullCoordinateBaseWeight
  change
    (∏ j : {j : Fin n // j ∈ D},
      G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
    (∏ j : {j : Fin n // j ∈ insert i L},
      G.marginalX
        ((fullCoordinateNewHistory D L i h x).aliceRevealed j)) *
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)},
      G.marginalY (h.bobRemaining j)) = _
  rw [finsetSubtype_prod_insert L i hiL]
  simp_rw [hnew]
  simp only [univ_eq_attach, fullCoordinateNewHistory, ↓reduceDIte]
  ring

end CoordinateWeights

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finitePurificationMatrix_pair_difference_gram_apply
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a b : ι) (i j : d) :
    ((finitePurificationMatrix F M positive hM a -
          finitePurificationMatrix F M positive hM b).conjTranspose *
        (finitePurificationMatrix F M positive hM a -
          finitePurificationMatrix F M positive hM b)) i j =
      ∑ r : d,
        inner ℂ
          (ensemblePurificationSubspaceEntry F M positive hM a r i -
            ensemblePurificationSubspaceEntry F M positive hM b r i)
          (ensemblePurificationSubspaceEntry F M positive hM a r j -
            ensemblePurificationSubspaceEntry F M positive hM b r j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sub_apply, finitePurificationMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  let basis := commonPurificationOrthonormalBasis F M positive hM
  let u := ensemblePurificationSubspaceEntry F M positive hM a r i
  let u₀ := ensemblePurificationSubspaceEntry F M positive hM b r i
  let v := ensemblePurificationSubspaceEntry F M positive hM a r j
  let v₀ := ensemblePurificationSubspaceEntry F M positive hM b r j
  have hisometry := basis.repr.inner_map_map (u - u₀) (v - v₀)
  change
    (∑ k, star (basis.repr u k - basis.repr u₀ k) *
      (basis.repr v k - basis.repr v₀ k)) =
      inner ℂ (u - u₀) (v - v₀)
  rw [← hisometry, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_sub, RCLike.star_def, mul_comm, dotProduct, map_sub, PiLp.sub_apply,
    WithLp.ofLp_sub, Pi.star_apply, Pi.sub_apply]

theorem ensemblePurificationSubspaceEntry_pair_difference_inner_eq_integral
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a b : ι) (r i j : d) :
    inner ℂ
      (ensemblePurificationSubspaceEntry F M positive hM a r i -
        ensemblePurificationSubspaceEntry F M positive hM b r i)
      (ensemblePurificationSubspaceEntry F M positive hM a r j -
        ensemblePurificationSubspaceEntry F M positive hM b r j) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s r i -
          spectralPurificationFilter (F b) (positive b) s r i) *
        (spectralPurificationFilter (F a) (positive a) s r j -
          spectralPurificationFilter (F b) (positive b) s r j) := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  let fi := spectralPurificationFilterEntryLp
    (F a) (positive a) r i
  let gi := spectralPurificationFilterEntryLp
    (F b) (positive b) r i
  let fj := spectralPurificationFilterEntryLp
    (F a) (positive a) r j
  let gj := spectralPurificationFilterEntryLp
    (F b) (positive b) r j
  have hsubi := Lp.coeFn_sub fi gi
  have hsubj := Lp.coeFn_sub fj gj
  have hfi := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r i
  have hgi := spectralPurificationFilterEntryLp_coeFn
    (F b) (positive b) r i
  have hfj := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r j
  have hgj := spectralPurificationFilterEntryLp_coeFn
    (F b) (positive b) r j
  filter_upwards [hsubi, hsubj, hfi, hgi, hfj, hgj]
    with s hi hj hfi' hgi' hfj' hgj'
  change inner ℂ ((fi - gi) s) ((fj - gj) s) = _
  rw [hi, hj]
  change inner ℂ (fi s - gi s) (fj s - gj s) = _
  change
    inner ℂ
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r i : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp
          (F b) (positive b) r i : ℝ → ℂ) s)
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r j : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp
          (F b) (positive b) r j : ℝ → ℂ) s) = _
  rw [hfi', hgi', hfj', hgj']
  simp only [RCLike.inner_apply, map_sub, star_sub, RCLike.star_def, mul_comm]

theorem finitePurificationMatrix_pair_difference_gram_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a b : ι) :
    (finitePurificationMatrix F M positive hM a -
        finitePurificationMatrix F M positive hM b).conjTranspose *
      (finitePurificationMatrix F M positive hM a -
        finitePurificationMatrix F M positive hM b) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s) := by
  classical
  have hdelta :
      MemLp (fun s : ℝ =>
        spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s)
        2 (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_memLp_two (F a) (positive a)).sub
      (spectralPurificationFilter_memLp_two (F b) (positive b))
  have hmatrix := spectralPurificationFilter_difference_gram_integrable
    (F a) (F b) (positive a) (positive b)
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ =>
            (star (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter (F b) (positive b) s) *
              (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter (F b) (positive b) s)) i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  ext i j
  rw [finitePurificationMatrix_pair_difference_gram_apply]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s)) i j =
      (∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter (F b) (positive b) s) *
          (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter (F b) (positive b) s)) i) j from
        congrArg (fun row : d → ℂ => row j)
          (MeasureTheory.eval_integral hrows i)]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      (star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s)) i) j =
      ∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter (F b) (positive b) s) *
          (spectralPurificationFilter (F a) (positive a) s -
            spectralPurificationFilter (F b) (positive b) s)) i j from
        MeasureTheory.eval_integral (fun k => (hrows i).eval k) j]
  simp_rw [ensemblePurificationSubspaceEntry_pair_difference_inner_eq_integral]
  have hproduct (r : d) :
      Integrable
        (fun s : ℝ =>
          star (spectralPurificationFilter (F a) (positive a) s r i -
            spectralPurificationFilter (F b) (positive b) s r i) *
          (spectralPurificationFilter (F a) (positive a) s r j -
            spectralPurificationFilter (F b) (positive b) s r j))
        (volume.restrict (Ioi 0)) :=
    (((hdelta.eval r).eval i).star).integrable_mul
      ((hdelta.eval r).eval j)
  rw [← integral_finsetSum Finset.univ (fun r _ => hproduct r)]
  apply integral_congr_ae
  filter_upwards with s
  simp only [star_sub, RCLike.star_def, Matrix.mul_apply, Matrix.sub_apply, star_apply]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem finiteLocalPurificationVector_sub_left
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (KA KA' : Matrix eA S.Alice ℂ)
    (KB : Matrix eB S.Bob ℂ) :
    finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA' KB =
      finiteLocalPurificationVector S (KA - KA') KB := by
  have hmatrix :
      finiteLocalPurificationJointMatrix S KA KB -
        finiteLocalPurificationJointMatrix S KA' KB =
      finiteLocalPurificationJointMatrix S (KA - KA') KB := by
    ext ⟨⟨a, k⟩, b⟩ ⟨⟨a', k'⟩, b'⟩
    simp only [finiteLocalPurificationJointMatrix, Matrix.sub_apply, kroneckerMap_apply, sub_mul]
  unfold finiteLocalPurificationVector
  rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec, hmatrix]

theorem finiteLocalPurificationVector_sub_right
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ)
    (KB KB' : Matrix eB S.Bob ℂ) :
    finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA KB' =
      finiteLocalPurificationVector S KA (KB - KB') := by
  have hmatrix :
      finiteLocalPurificationJointMatrix S KA KB -
        finiteLocalPurificationJointMatrix S KA KB' =
      finiteLocalPurificationJointMatrix S KA (KB - KB') := by
    ext ⟨⟨a, k⟩, b⟩ ⟨⟨a', k'⟩, b'⟩
    simp only [finiteLocalPurificationJointMatrix, Matrix.sub_apply, kroneckerMap_apply, mul_sub]
  unfold finiteLocalPurificationVector
  rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec, hmatrix]

theorem finiteLocalPurificationVector_sub_left_norm_sq
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA KA' : Matrix eA S.Alice ℂ)
    (KB : Matrix eB S.Bob ℂ) :
    ‖finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA' KB‖ ^ 2 =
      bornTracePairing S.state.matrix
        ((KA - KA').conjTranspose * (KA - KA'))
        (KB.conjTranspose * KB) := by
  rw [finiteLocalPurificationVector_sub_left,
    finiteLocalPurificationVector_norm_sq]
  rfl

theorem finiteLocalPurificationVector_sub_right_norm_sq
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ)
    (KB KB' : Matrix eB S.Bob ℂ) :
    ‖finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA KB'‖ ^ 2 =
      bornTracePairing S.state.matrix
        (KA.conjTranspose * KA)
        ((KB - KB').conjTranspose * (KB - KB')) := by
  rw [finiteLocalPurificationVector_sub_right,
    finiteLocalPurificationVector_norm_sq]
  rfl

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def fullCoordinateAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (x : X) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α

private def fullCoordinateAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (y : Y) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D L
    (fullCoordinateOldHistory D L i r y) α

private def fullCoordinateBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (y : Y) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D L
    (fullCoordinateOldHistory D L i r y) β

private def fullCoordinateBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (x : X) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) β

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


private def fullCoordinateAssembleHiddenAlice
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (x : X)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} → X := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact x
  · exact hidden ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hjD, not_false_eq_true, and_self,
        mem_insert, hj, hjL, or_self]⟩

private def fullCoordinateHiddenAliceEquiv
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ fullHistoryRemaining n D L} → X) ≃
      X × ({j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden :=
    (hidden ⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD, not_false_eq_true,
                     and_self, hiL]⟩,
      fun j => hidden
        ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩)
  invFun t := fullCoordinateAssembleHiddenAlice D L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, by simp only [fullHistoryRemaining, mem_sdiff, mem_univ, hiD,
                        not_false_eq_true, and_self, hiL]⟩ :
            {j : Fin n // j ∈ fullHistoryRemaining n D L}) :=
        Subtype.ext hj
      subst j
      simp only [fullCoordinateAssembleHiddenAlice, ↓reduceDIte]
    · simp only [fullCoordinateAssembleHiddenAlice, hj, ↓reduceDIte, Subtype.coe_eta]
  right_inv t := by
    rcases t with ⟨x, hidden⟩
    apply Prod.ext
    · simp only [fullCoordinateAssembleHiddenAlice, ↓reduceDIte]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp only [he, mem_insert, true_or]
      simp only [fullCoordinateAssembleHiddenAlice, hj, ↓reduceDIte]

private def fullCoordinateAssembleHiddenBob
    {Y : Type*} {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n)
    (y : Y) (hidden : {j : Fin n // j ∈ L} → Y) :
    {j : Fin n // j ∈ insert i L} → Y := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact y
  · exact hidden
      ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

private def fullCoordinateHiddenBobEquiv
    {Y : Type*} {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ insert i L} → Y) ≃
      Y × ({j : Fin n // j ∈ L} → Y) where
  toFun hidden :=
    (hidden ⟨i, Finset.mem_insert_self i L⟩,
      fun j => hidden ⟨j, Finset.mem_insert_of_mem j.property⟩)
  invFun t := fullCoordinateAssembleHiddenBob L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i L⟩ :
            {j : Fin n // j ∈ insert i L}) :=
        Subtype.ext hj
      subst j
      simp only [fullCoordinateAssembleHiddenBob, ↓reduceDIte]
    · simp only [fullCoordinateAssembleHiddenBob, hj, ↓reduceDIte, Subtype.coe_eta]
  right_inv t := by
    rcases t with ⟨y, hidden⟩
    apply Prod.ext
    · simp only [fullCoordinateAssembleHiddenBob, ↓reduceDIte]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiL (he ▸ j.property)
      simp only [fullCoordinateAssembleHiddenBob, hj, ↓reduceDIte, Subtype.coe_eta]

section CoordinateFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

omit [Fintype X] [Fintype Y] in
theorem fullCoordinateAliceQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryAliceQuestion
        (fullCoordinateOldHistory D L i r y)
        (fullCoordinateAssembleHiddenAlice D L i x hidden) =
      fullHistoryAliceQuestion
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · simp only [fullHistoryAliceQuestion, hjD, ↓reduceDIte, fullCoordinateOldHistory,
      fullCoordinateNewHistory]
  · by_cases hjL : j ∈ L
    · have hji : j ≠ i := by
        intro he
        exact hiL (he ▸ hjL)
      simp only [fullHistoryAliceQuestion, hjD, ↓reduceDIte, hjL, fullCoordinateOldHistory,
        mem_insert, hji, or_true, fullCoordinateNewHistory]
    · by_cases hji : j = i
      · subst j
        simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte, hiL,
          fullCoordinateAssembleHiddenAlice, mem_insert, or_false, fullCoordinateNewHistory]
      · simp only [fullHistoryAliceQuestion, hjD, ↓reduceDIte, hjL,
          fullCoordinateAssembleHiddenAlice, hji, mem_insert, or_self]

omit [Fintype X] [Fintype Y] in
theorem fullCoordinateBobQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryBobQuestion
        (fullCoordinateNewHistory D L i r x)
        (fullCoordinateAssembleHiddenBob L i y hidden) =
      fullHistoryBobQuestion
        (fullCoordinateOldHistory D L i r y) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · simp only [fullHistoryBobQuestion, hjD, ↓reduceDIte, fullCoordinateNewHistory,
      fullCoordinateOldHistory]
  · by_cases hjL : j ∈ L
    · have hji : j ≠ i := by
        intro he
        exact hiL (he ▸ hjL)
      simp only [fullHistoryBobQuestion, hjD, ↓reduceDIte, mem_insert, hji, hjL, or_true,
        fullCoordinateAssembleHiddenBob]
    · by_cases hji : j = i
      · subst j
        simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte, mem_insert, hiL, or_false,
          fullCoordinateAssembleHiddenBob, fullCoordinateOldHistory]
      · simp only [fullHistoryBobQuestion, hjD, ↓reduceDIte, mem_insert, hji, hjL, or_self,
          fullCoordinateNewHistory, fullCoordinateOldHistory]

theorem fullCoordinateHiddenAliceWeight_split
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryHiddenAliceWeight G
        (fullCoordinateOldHistory D L i r y)
        (fullCoordinateAssembleHiddenAlice D L i x hidden) =
      G.conditionalXGivenY y x *
        fullHistoryHiddenAliceWeight G
          (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  unfold fullHistoryHiddenAliceWeight
  rw [fullHistoryRemaining_prod_split D L i hiD hiL]
  simp only [fullCoordinateOldHistory,
    fullCoordinateAssembleHiddenAlice, dite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hj : (j : Fin n) ≠ i := by
    intro he
    have hnot : (j : Fin n) ∉ insert i L :=
      (Finset.mem_sdiff.mp j.property).2
    apply hnot
    simp only [he, mem_insert, true_or]
  simp only [hj, ↓reduceDIte, fullCoordinateNewHistory]

theorem fullCoordinateHiddenBobWeight_split
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryHiddenBobWeight G
        (fullCoordinateNewHistory D L i r x)
        (fullCoordinateAssembleHiddenBob L i y hidden) =
      G.conditionalYGivenX x y *
        fullHistoryHiddenBobWeight G
          (fullCoordinateOldHistory D L i r y) hidden := by
  classical
  unfold fullHistoryHiddenBobWeight
  rw [finsetSubtype_prod_insert L i hiL]
  simp only [fullCoordinateNewHistory,
    fullCoordinateAssembleHiddenBob, dite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hj : (j : Fin n) ≠ i := by
    intro he
    exact hiL (he ▸ j.property)
  simp only [hj, ↓reduceDIte, Subtype.coe_eta, fullCoordinateOldHistory]

theorem fullCoordinateAliceFilter_conditional_mean
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (y : Y) :
    fullCoordinateAliceMeanFilter G n S D L i r α y =
      conditionalAliceAverage G
        (fullCoordinateAliceQuestionFilter G n S D L i r α) y := by
  classical
  let e := fullCoordinateHiddenAliceEquiv
    (X := X) D L i hiD hiL
  let f : X × ({j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) →
      Matrix S.Alice S.Alice ℂ := fun t =>
    (G.conditionalXGivenY y t.1 *
      fullHistoryHiddenAliceWeight G
        (fullCoordinateNewHistory D L i r t.1) t.2) •
      conditionedAliceEffect G n S D α
        (fullHistoryAliceQuestion
          (fullCoordinateNewHistory D L i r t.1) t.2)
  unfold fullCoordinateAliceMeanFilter
    fullCoordinateAliceQuestionFilter
  calc
    fullHistoryAliceFilter G n S D L
      (fullCoordinateOldHistory D L i r y) α =
      ∑ hidden : ({j : Fin n //
        j ∈ fullHistoryRemaining n D L} → X), f (e hidden) := by
        unfold fullHistoryAliceFilter
        apply Finset.sum_congr rfl
        intro hidden _
        have he := e.symm_apply_apply hidden
        change fullCoordinateAssembleHiddenAlice
          D L i (e hidden).1 (e hidden).2 = hidden at he
        conv_lhs => rw [← he]
        rw [fullCoordinateHiddenAliceWeight_split
          G D L i hiD hiL r (e hidden).1 y (e hidden).2]
        rw [fullCoordinateAliceQuestion_eq
          D L i hiD hiL r (e hidden).1 y (e hidden).2]
    _ = ∑ t : X × ({j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X),
          f t := e.sum_comp f
    _ = conditionalAliceAverage G
        (fun x => fullHistoryAliceFilter G n S D (insert i L)
          (fullCoordinateNewHistory D L i r x) α) y := by
      simp only [Fintype.sum_prod_type, conditionalAliceAverage, fullHistoryAliceFilter, smul_sum,
        smul_smul, f]

theorem fullCoordinateBobFilter_conditional_mean
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B)
    (x : X) :
    fullCoordinateBobMeanFilter G n S D L i r β x =
      conditionalBobAverage G
        (fullCoordinateBobQuestionFilter G n S D L i r β) x := by
  classical
  let e := fullCoordinateHiddenBobEquiv
    (Y := Y) L i hiL
  let f : Y × ({j : Fin n // j ∈ L} → Y) →
      Matrix S.Bob S.Bob ℂ := fun t =>
    (G.conditionalYGivenX x t.1 *
      fullHistoryHiddenBobWeight G
        (fullCoordinateOldHistory D L i r t.1) t.2) •
      conditionedBobEffect G n S D β
        (fullHistoryBobQuestion
          (fullCoordinateOldHistory D L i r t.1) t.2)
  unfold fullCoordinateBobMeanFilter
    fullCoordinateBobQuestionFilter
  calc
    fullHistoryBobFilter G n S D (insert i L)
      (fullCoordinateNewHistory D L i r x) β =
      ∑ hidden : ({j : Fin n // j ∈ insert i L} → Y),
        f (e hidden) := by
        unfold fullHistoryBobFilter
        apply Finset.sum_congr rfl
        intro hidden _
        have he := e.symm_apply_apply hidden
        change fullCoordinateAssembleHiddenBob
          L i (e hidden).1 (e hidden).2 = hidden at he
        conv_lhs => rw [← he]
        rw [fullCoordinateHiddenBobWeight_split
          G D L i hiL r x (e hidden).1 (e hidden).2]
        rw [fullCoordinateBobQuestion_eq
          D L i hiD hiL r x (e hidden).1 (e hidden).2]
    _ = ∑ t : Y × ({j : Fin n // j ∈ L} → Y), f t :=
      e.sum_comp f
    _ = conditionalBobAverage G
        (fun y => fullHistoryBobFilter G n S D L
          (fullCoordinateOldHistory D L i r y) β) x := by
      simp only [Fintype.sum_prod_type, conditionalBobAverage, fullHistoryBobFilter, smul_sum,
        smul_smul, f]

end CoordinateFilters

theorem matrixLogEntropy_weighted_jensen_posSemidef
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M).PosSemidef := by
  classical
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have hgap := finite_purification_log_entropy_jensen
    weight F M nonnegative normalized mean positive
  change
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ i : ι, weight i •
        ((finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM).conjTranspose *
          (finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM)))).PosSemidef
    at hgap
  have hvariance :
      (∑ i : ι, weight i •
        ((finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM).conjTranspose *
          (finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM))).PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro i _
    exact (Matrix.posSemidef_conjTranspose_mul_self
      (finitePurificationMatrix F M positive hM i -
        meanFinitePurificationMatrix F M positive hM)).smul
      (nonnegative i)
  convert hgap.add hvariance using 1 ; module

section ConditionalJensen

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem conditionalAlice_matrixLogEntropy_gap_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (G : Game X Y A B)
    (H : X → Matrix d d ℂ)
    (hH : ∀ x, (H x).PosSemidef)
    (y : Y) (hy : 0 < G.marginalY y) :
    (conditionalAliceAverage G
        (fun x => cfc (fun z : ℝ => z * Real.log z) (H x)) y -
      cfc (fun z : ℝ => z * Real.log z)
        (conditionalAliceAverage G H y)).PosSemidef := by
  exact matrixLogEntropy_weighted_jensen_posSemidef
    (G.conditionalXGivenY y) H
    (conditionalAliceAverage G H y)
    (fun x => G.conditionalXGivenY_nonneg y x)
    (G.conditionalXGivenY_sum y hy)
    rfl hH

private def fullCoordinateAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (conditionalAliceAverage G
        (fun x => cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceQuestionFilter G n S D L i r α x)) y -
        cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceMeanFilter G n S D L i r α y))
      (fullCoordinateBobQuestionFilter G n S D L i r β y)

theorem fullCoordinateAliceEntropyIncrement_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    (∑ x : X, G.marginalX x *
      bornTracePairing S.state.matrix
        (cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceQuestionFilter G n S D L i r α x))
        (fullCoordinateBobMeanFilter G n S D L i r β x)) -
    (∑ y : Y, G.marginalY y *
      bornTracePairing S.state.matrix
        (cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceMeanFilter G n S D L i r α y))
        (fullCoordinateBobQuestionFilter G n S D L i r β y)) =
      fullCoordinateAliceEntropyIncrement G n S D L i r α β := by
  have h := alice_reveal_increment G
    (bornTracePairing S.state.matrix)
    (fullCoordinateAliceQuestionFilter G n S D L i r α)
    (fullCoordinateAliceMeanFilter G n S D L i r α)
    (fullCoordinateBobQuestionFilter G n S D L i r β)
    (fun F => cfc (fun z : ℝ => z * Real.log z) F)
  simp_rw [← fullCoordinateBobFilter_conditional_mean
    G n S D L i hiD hiL r β] at h
  exact h

theorem fullCoordinateAliceEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    0 ≤ fullCoordinateAliceEntropyIncrement G n S D L i r α β := by
  unfold fullCoordinateAliceEntropyIncrement
  apply Finset.sum_nonneg
  intro y _
  by_cases hy : G.marginalY y = 0
  · simp only [hy, map_sub, LinearMap.sub_apply, zero_mul, Std.le_refl]
  · have hypos : 0 < G.marginalY y :=
      lt_of_le_of_ne (G.marginalY_nonneg y) (Ne.symm hy)
    have hmean := fullCoordinateAliceFilter_conditional_mean
      G n S D L i hiD hiL r α y
    have hgap :
        (conditionalAliceAverage G
          (fun x => cfc (fun z : ℝ => z * Real.log z)
            (fullCoordinateAliceQuestionFilter G n S D L i r α x)) y -
          cfc (fun z : ℝ => z * Real.log z)
            (fullCoordinateAliceMeanFilter G n S D L i r α y)).PosSemidef := by
      rw [hmean]
      exact conditionalAlice_matrixLogEntropy_gap_posSemidef G
        (fullCoordinateAliceQuestionFilter G n S D L i r α)
        (fun x => fullHistoryAliceFilter_posSemidef G n S D
          (insert i L) (fullCoordinateNewHistory D L i r x) α)
        y hypos
    exact mul_nonneg (G.marginalY_nonneg y)
      (trace_mul_posSemidef_nonneg S.state.positive
        (hgap.kronecker
          (fullHistoryBobFilter_posSemidef G n S D L
            (fullCoordinateOldHistory D L i r y) β)))

end ConditionalJensen

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The indicator function for full coordinate base win. -/
def fullCoordinateBaseWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ := by
  classical
  exact if ∀ j : {j : Fin n // j ∈ D},
    G.predicate (r.aliceConditioned j) (r.bobConditioned j)
      (α j) (β j) = true then 1 else 0

theorem fullCoordinateBaseWinIndicator_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    0 ≤ fullCoordinateBaseWinIndicator G D L i r α β := by
  classical
  unfold fullCoordinateBaseWinIndicator
  split <;> norm_num

theorem fullCoordinateOldHistory_winIndicator_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (y : Y)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    fullHistoryWinIndicator G
      (fullCoordinateOldHistory D L i r y) α β =
      fullCoordinateBaseWinIndicator G D L i r α β := by
  classical
  simp only [fullHistoryWinIndicator, fullCoordinateOldHistory, Subtype.forall,
    fullCoordinateBaseWinIndicator]

theorem fullCoordinateNewHistory_winIndicator_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    fullHistoryWinIndicator G
      (fullCoordinateNewHistory D L i r x) α β =
      fullCoordinateBaseWinIndicator G D L i r α β := by
  classical
  simp only [fullHistoryWinIndicator, fullCoordinateNewHistory, Subtype.forall,
    fullCoordinateBaseWinIndicator]

theorem fullCoordinate_three_sum_rotate
    {I J K T : Type*}
    [Fintype I] [Fintype J] [Fintype K] [AddCommMonoid T]
    (f : I → J → K → T) :
    (∑ i : I, ∑ j : J, ∑ k : K, f i j k) =
      ∑ j : J, ∑ k : K, ∑ i : I, f i j k := by
  calc
    (∑ i : I, ∑ j : J, ∑ k : K, f i j k) =
      ∑ j : J, ∑ i : I, ∑ k : K, f i j k := by
        rw [Finset.sum_comm]
    _ = ∑ j : J, ∑ k : K, ∑ i : I, f i j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

theorem fullCoordinateOldHistory_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (f : FullSubsetHistory X Y n D L → T) :
    (∑ h : FullSubsetHistory X Y n D L, f h) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ y : Y, f (fullCoordinateOldHistory D L i r y) := by
  classical
  simpa only [fullCoordinateOldHistoryEquiv, Equiv.symm_mk, Equiv.coe_fn_mk,
    Fintype.sum_prod_type]
    using ((fullCoordinateOldHistoryEquiv
      (X := X) (Y := Y) D L i hiD hiL).symm.sum_comp f).symm

theorem fullCoordinateNewHistory_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (f : FullSubsetHistory X Y n D (insert i L) → T) :
    (∑ h : FullSubsetHistory X Y n D (insert i L), f h) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, f (fullCoordinateNewHistory D L i r x) := by
  classical
  simpa only [fullCoordinateNewHistoryEquiv, Equiv.symm_mk, Equiv.coe_fn_mk,
    Fintype.sum_prod_type]
    using ((fullCoordinateNewHistoryEquiv
      (X := X) (Y := Y) D L i hiL).symm.sum_comp f).symm

theorem fullCoordinateWeightedOldSum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (value : (h : FullSubsetHistory X Y n D L) →
      ({j : Fin n // j ∈ D} → A) →
      ({j : Fin n // j ∈ D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ y : Y, G.marginalY y *
            value (fullCoordinateOldHistory D L i r y) α β) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G (fullCoordinateOldHistory D L i r y) *
          fullHistoryWinIndicator G
            (fullCoordinateOldHistory D L i r y) α β *
          value (fullCoordinateOldHistory D L i r y) α β :=
      fullCoordinateOldHistory_sum D L i hiD hiL
        (fun h => ∑ α : {j : Fin n // j ∈ D} → A,
          ∑ β : {j : Fin n // j ∈ D} → B,
            fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
              value h α β)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [fullCoordinate_three_sum_rotate]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [fullCoordinateOldHistory_weight G D L i hiD hiL r y,
        fullCoordinateOldHistory_winIndicator_eq G D L i r y α β]
      ring

theorem fullCoordinateWeightedNewSum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (value : (h : FullSubsetHistory X Y n D (insert i L)) →
      ({j : Fin n // j ∈ D} → A) →
      ({j : Fin n // j ∈ D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n D (insert i L),
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ x : X, G.marginalX x *
            value (fullCoordinateNewHistory D L i r x) α β) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n D (insert i L),
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G (fullCoordinateNewHistory D L i r x) *
          fullHistoryWinIndicator G
            (fullCoordinateNewHistory D L i r x) α β *
          value (fullCoordinateNewHistory D L i r x) α β :=
      fullCoordinateNewHistory_sum D L i hiL
        (fun h => ∑ α : {j : Fin n // j ∈ D} → A,
          ∑ β : {j : Fin n // j ∈ D} → B,
            fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
              value h α β)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [fullCoordinate_three_sum_rotate]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [fullCoordinateNewHistory_weight G D L i hiL r x,
        fullCoordinateNewHistory_winIndicator_eq G D L i r x α β]
      ring

/-- The information increment contributed by full coordinate alice total entropy. -/
def fullCoordinateAliceTotalEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      fullCoordinateAliceEntropyIncrement G n S D L i r α β

theorem fullHistoryAliceEntropyPotential_increment
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    fullHistoryAliceEntropyPotential G n S D (insert i L) -
        fullHistoryAliceEntropyPotential G n S D L =
      fullCoordinateAliceTotalEntropyIncrement G n S D L i := by
  classical
  unfold fullHistoryAliceEntropyPotential
    fullCoordinateAliceTotalEntropyIncrement
  rw [fullCoordinateWeightedNewSum G D L i hiL
    (fun h α β => bornTracePairing S.state.matrix
      (cfc (fun z : ℝ => z * Real.log z)
        (fullHistoryAliceFilter G n S D (insert i L) h α))
      (fullHistoryBobFilter G n S D (insert i L) h β))]
  rw [fullCoordinateWeightedOldSum G D L i hiD hiL
    (fun h α β => bornTracePairing S.state.matrix
      (cfc (fun z : ℝ => z * Real.log z)
        (fullHistoryAliceFilter G n S D L h α))
      (fullHistoryBobFilter G n S D L h β))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro β _
  rw [← mul_sub]
  congr 1
  exact fullCoordinateAliceEntropyIncrement_eq
    G n S D L i hiD hiL r α β

theorem fullCoordinateAliceTotalEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    0 ≤ fullCoordinateAliceTotalEntropyIncrement G n S D L i := by
  unfold fullCoordinateAliceTotalEntropyIncrement
  exact Finset.sum_nonneg fun r _ =>
    Finset.sum_nonneg fun α _ =>
      Finset.sum_nonneg fun β _ =>
        mul_nonneg
          (mul_nonneg (fullCoordinateBaseWeight_nonneg G D L i r)
            (fullCoordinateBaseWinIndicator_nonneg G D L i r α β))
          (fullCoordinateAliceEntropyIncrement_nonneg
            G n S D L i hiD hiL r α β)

end

end QuantumParallelRepetition

end
