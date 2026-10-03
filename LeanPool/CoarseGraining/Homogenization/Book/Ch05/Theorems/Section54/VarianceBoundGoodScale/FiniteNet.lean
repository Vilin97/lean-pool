/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScalarReduction

/-! # Finite Net -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

noncomputable section

/-!
# Finite-dimensional probes for full-block matrices

This file starts the deterministic finite-dimensional upgrade used in the
variance bound.  The eventual argument controls the Euclidean operator norm of
a symmetric full-block matrix by finitely many quadratic probes.
-/

/-- Coordinate probe in the full-block space. -/
def fullBlockCoordinateProbe {d : ℕ} (α : BlockCoord d) : FullBlockVec d :=
  Pi.single α 1

/-- The quadratic form on a coordinate probe reads off a diagonal entry. -/
@[simp]
theorem fullBlockQuadratic_coordinateProbe
    {d : ℕ} (M : FullBlockMat d) (α : BlockCoord d) :
    fullBlockQuadratic M (fullBlockCoordinateProbe α) = M α α := by
  classical
  unfold fullBlockQuadratic fullBlockCoordinateProbe
  rw [dotProduct, Finset.sum_eq_single α]
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single α]
    · simp
    · intro β _hβ hβα
      simp [Pi.single_eq_of_ne hβα]
    · simp
  · intro β _hβ hβα
    simp [Pi.single_eq_of_ne hβα]
  · simp

/-- The plus-pair probe used in the polarization step. -/
def fullBlockPlusProbe {d : ℕ} (α β : BlockCoord d) : FullBlockVec d :=
  fullBlockCoordinateProbe α + fullBlockCoordinateProbe β

/-- The minus-pair probe used in the polarization step. -/
def fullBlockMinusProbe {d : ℕ} (α β : BlockCoord d) : FullBlockVec d :=
  fullBlockCoordinateProbe α - fullBlockCoordinateProbe β

/-- Off-diagonal plus-probe expansion for a symmetric full-block matrix. -/
theorem fullBlockQuadratic_plusProbe_of_ne
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    fullBlockQuadratic M (fullBlockPlusProbe α β) =
      M α α + 2 * M α β + M β β := by
  classical
  have hβα : β ≠ α := hαβ.symm
  have hsymm : M β α = M α β := (hM.apply β α).symm
  unfold fullBlockQuadratic fullBlockPlusProbe fullBlockCoordinateProbe
  rw [dotProduct, Fintype.sum_eq_add α β hαβ]
  · rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add α β hαβ]
    · rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add α β hαβ]
      · simp [Pi.single_eq_same, Pi.single_eq_of_ne, hαβ, hβα, hsymm]
        ring
      · intro γ hγ
        simp [Pi.single_eq_of_ne hγ.1, Pi.single_eq_of_ne hγ.2]
    · intro γ hγ
      simp [Pi.single_eq_of_ne hγ.1, Pi.single_eq_of_ne hγ.2]
  · intro γ hγ
    simp [Pi.single_eq_of_ne hγ.1, Pi.single_eq_of_ne hγ.2]

/-- Off-diagonal minus-probe expansion for a symmetric full-block matrix. -/
theorem fullBlockQuadratic_minusProbe_of_ne
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    fullBlockQuadratic M (fullBlockMinusProbe α β) =
      M α α - 2 * M α β + M β β := by
  classical
  have hβα : β ≠ α := hαβ.symm
  have hsymm : M β α = M α β := (hM.apply β α).symm
  unfold fullBlockQuadratic fullBlockMinusProbe fullBlockCoordinateProbe
  rw [dotProduct, Fintype.sum_eq_add α β hαβ]
  · rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add α β hαβ]
    · rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add α β hαβ]
      · simp [Pi.single_eq_same, Pi.single_eq_of_ne, hαβ, hβα, hsymm]
        ring
      · intro γ hγ
        simp [Pi.single_eq_of_ne hγ.1, Pi.single_eq_of_ne hγ.2]
    · intro γ hγ
      simp [Pi.single_eq_of_ne hγ.1, Pi.single_eq_of_ne hγ.2]
  · intro γ hγ
    simp [Pi.single_eq_of_ne hγ.1, Pi.single_eq_of_ne hγ.2]

/-- Polarization recovers an off-diagonal entry from the plus and minus
quadratic probes. -/
theorem fullBlock_entry_eq_quarter_plus_sub_minus_of_ne
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    M α β =
      (1 / 4 : ℝ) *
        (fullBlockQuadratic M (fullBlockPlusProbe α β) -
          fullBlockQuadratic M (fullBlockMinusProbe α β)) := by
  rw [fullBlockQuadratic_plusProbe_of_ne hM hαβ,
    fullBlockQuadratic_minusProbe_of_ne hM hαβ]
  ring

/-- A finite sum of coordinate and pair probes controlling all entries of a
symmetric full-block matrix. -/
noncomputable def fullBlockProbeAbsSum {d : ℕ} (M : FullBlockMat d) : ℝ :=
  ∑ α : BlockCoord d, ∑ β : BlockCoord d,
    (|fullBlockQuadratic M (fullBlockCoordinateProbe α)| +
      |fullBlockQuadratic M (fullBlockPlusProbe α β)| +
      |fullBlockQuadratic M (fullBlockMinusProbe α β)|)

theorem fullBlockProbeAbsSum_nonneg {d : ℕ} (M : FullBlockMat d) :
    0 ≤ fullBlockProbeAbsSum M := by
  unfold fullBlockProbeAbsSum
  positivity

private theorem fullBlock_entry_abs_le_probe_abs
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm)
    (α β : BlockCoord d) :
    |M α β| ≤
      |fullBlockQuadratic M (fullBlockCoordinateProbe α)| +
        |fullBlockQuadratic M (fullBlockPlusProbe α β)| +
        |fullBlockQuadratic M (fullBlockMinusProbe α β)| := by
  by_cases hαβ : α = β
  · subst β
    rw [fullBlockQuadratic_coordinateProbe]
    nlinarith [abs_nonneg (fullBlockQuadratic M (fullBlockPlusProbe α α)),
      abs_nonneg (fullBlockQuadratic M (fullBlockMinusProbe α α))]
  · have hpol := fullBlock_entry_eq_quarter_plus_sub_minus_of_ne hM hαβ
    let P := fullBlockQuadratic M (fullBlockPlusProbe α β)
    let N := fullBlockQuadratic M (fullBlockMinusProbe α β)
    have habs_sub : |P - N| ≤ |P| + |N| := by
      calc
        |P - N| = |P + -N| := by rw [sub_eq_add_neg]
        _ ≤ |P| + |-N| := abs_add_le P (-N)
        _ = |P| + |N| := by rw [abs_neg]
    have hquarter : |(1 / 4 : ℝ) * (P - N)| ≤ |P| + |N| := by
      calc
        |(1 / 4 : ℝ) * (P - N)| = (1 / 4 : ℝ) * |P - N| := by
          simp [abs_mul]
        _ ≤ 1 * |P - N| := by
          exact mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
        _ ≤ |P| + |N| := by simpa using habs_sub
    calc
      |M α β| = |(1 / 4 : ℝ) * (P - N)| := by rw [hpol]
      _ ≤ |P| + |N| := hquarter
      _ ≤ |fullBlockQuadratic M (fullBlockCoordinateProbe α)| + |P| + |N| := by
        nlinarith [abs_nonneg (fullBlockQuadratic M (fullBlockCoordinateProbe α))]

private theorem norm_toEuclideanCLM_le_sum_abs_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M‖ ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, |M i j| := by
  classical
  let S : ℝ := ∑ i : ι, ∑ j : ι, |M i j|
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) ?_
  intro x
  have hcoord :
      ∀ i : ι,
        ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ≤
          S * ‖x‖ := by
    intro i
    calc
      ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖
          = |∑ j : ι, M i j * x.ofLp j| := by
              simp [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
      _ ≤ ∑ j : ι, |M i j * x.ofLp j| :=
            Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun j => M i j * x.ofLp j)
      _ = ∑ j : ι, |M i j| * ‖x.ofLp j‖ := by
            simp [abs_mul, Real.norm_eq_abs]
      _ ≤ ∑ j : ι, |M i j| * ‖x‖ := by
            exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (abs_nonneg _)
      _ = (∑ j : ι, |M i j|) * ‖x‖ := by
            rw [Finset.sum_mul]
      _ ≤ S * ‖x‖ := by
            exact mul_le_mul_of_nonneg_right
              (Finset.single_le_sum
                (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (M k j))
                (Finset.mem_univ i))
              (norm_nonneg x)
  have hnorm_sq :
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2 ≤
        (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
    calc
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2
          = ∑ i : ι,
              ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]
      _ ≤ ∑ i : ι, (S * ‖x‖) ^ 2 := by
            exact Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ ≤ (∑ _i : ι, S * ‖x‖) ^ 2 := by
            exact Finset.sum_sq_le_sq_sum_of_nonneg
              (fun _ _ => mul_nonneg hS_nonneg (norm_nonneg x))
      _ = (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
            simp [Finset.sum_const]
            ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) (norm_nonneg x))).mp hnorm_sq

/-- The Euclidean operator norm of a symmetric full-block matrix is controlled
by finitely many coordinate and pair quadratic probes. -/
theorem fullBlock_operatorNorm_le_probeAbsSum
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ≤
      (Fintype.card (BlockCoord d) : ℝ) * fullBlockProbeAbsSum M := by
  classical
  have hentry_sum :
      (∑ α : BlockCoord d, ∑ β : BlockCoord d, |M α β|) ≤
        fullBlockProbeAbsSum M := by
    calc
      (∑ α : BlockCoord d, ∑ β : BlockCoord d, |M α β|)
          ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d,
              (|fullBlockQuadratic M (fullBlockCoordinateProbe α)| +
                |fullBlockQuadratic M (fullBlockPlusProbe α β)| +
                |fullBlockQuadratic M (fullBlockMinusProbe α β)|) := by
            exact Finset.sum_le_sum fun α _ =>
              Finset.sum_le_sum fun β _ =>
                fullBlock_entry_abs_le_probe_abs hM α β
      _ =
          ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            (|fullBlockQuadratic M (fullBlockCoordinateProbe α)| +
              |fullBlockQuadratic M (fullBlockPlusProbe α β)| +
              |fullBlockQuadratic M (fullBlockMinusProbe α β)|) := rfl
      _ = fullBlockProbeAbsSum M := by
            rfl
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖
        ≤ (Fintype.card (BlockCoord d) : ℝ) *
            ∑ α : BlockCoord d, ∑ β : BlockCoord d, |M α β| :=
          norm_toEuclideanCLM_le_sum_abs_entries M
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) * fullBlockProbeAbsSum M :=
          mul_le_mul_of_nonneg_left hentry_sum (Nat.cast_nonneg _)

/-- Squared version of `fullBlock_operatorNorm_le_probeAbsSum`. -/
theorem fullBlock_operatorNorm_sq_le_probeAbsSum_sq
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ 2 ≤
      ((Fintype.card (BlockCoord d) : ℝ) * fullBlockProbeAbsSum M) ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (fullBlock_operatorNorm_le_probeAbsSum hM) 2

/-- Dimension-weighted square budget for the finite coordinate and pair probes.
This is intentionally generous; constants are harmless in the final
dimension-dependent variance constant. -/
noncomputable def fullBlockProbeSqBudget {d : ℕ} (M : FullBlockMat d) : ℝ :=
  (Fintype.card (BlockCoord d) : ℝ) *
    (∑ α : BlockCoord d,
      (Fintype.card (BlockCoord d) : ℝ) * ∑ β : BlockCoord d,
        3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
          (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
          (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ)))

private theorem three_abs_sum_sq_le_three_sq_sum (a b c : ℝ) :
    (|a| + |b| + |c|) ^ (2 : ℕ) ≤
      3 * (a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
  nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - |c|),
    sq_nonneg (|b| - |c|), sq_abs a, sq_abs b, sq_abs c]

/-- The finite-probe absolute sum is controlled by the square budget. -/
theorem fullBlockProbeAbsSum_sq_le_probeSqBudget
    {d : ℕ} (M : FullBlockMat d) :
    (fullBlockProbeAbsSum M) ^ (2 : ℕ) ≤ fullBlockProbeSqBudget M := by
  classical
  let g : BlockCoord d → BlockCoord d → ℝ := fun α β =>
    |fullBlockQuadratic M (fullBlockCoordinateProbe α)| +
      |fullBlockQuadratic M (fullBlockPlusProbe α β)| +
      |fullBlockQuadratic M (fullBlockMinusProbe α β)|
  have houter :=
    sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (BlockCoord d)))
      (f := fun α => ∑ β : BlockCoord d, g α β)
  have hinner :
      (∑ α : BlockCoord d, (∑ β : BlockCoord d, g α β) ^ (2 : ℕ)) ≤
        ∑ α : BlockCoord d,
          (Fintype.card (BlockCoord d) : ℝ) * ∑ β : BlockCoord d,
            (g α β) ^ (2 : ℕ) := by
    refine Finset.sum_le_sum ?_
    intro α _hα
    exact
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (BlockCoord d)))
        (f := fun β => g α β)
  have hpoint :
      (∑ α : BlockCoord d,
          (Fintype.card (BlockCoord d) : ℝ) * ∑ β : BlockCoord d,
            (g α β) ^ (2 : ℕ)) ≤
        ∑ α : BlockCoord d,
          (Fintype.card (BlockCoord d) : ℝ) * ∑ β : BlockCoord d,
            3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
              (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ)) := by
    refine Finset.sum_le_sum ?_
    intro α _hα
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum ?_
    intro β _hβ
    simpa [g] using three_abs_sum_sq_le_three_sq_sum
      (fullBlockQuadratic M (fullBlockCoordinateProbe α))
      (fullBlockQuadratic M (fullBlockPlusProbe α β))
      (fullBlockQuadratic M (fullBlockMinusProbe α β))
  calc
    (fullBlockProbeAbsSum M) ^ (2 : ℕ)
        = (∑ α : BlockCoord d, ∑ β : BlockCoord d, g α β) ^ (2 : ℕ) := by
          simp [fullBlockProbeAbsSum, g]
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d, (∑ β : BlockCoord d, g α β) ^ (2 : ℕ) := houter
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          (∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) * ∑ β : BlockCoord d,
              (g α β) ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          (∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) * ∑ β : BlockCoord d,
              3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
                (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
                (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left hpoint (Nat.cast_nonneg _)
    _ = fullBlockProbeSqBudget M := by rfl

/-- Squared operator-norm control by the finite quadratic-probe square
budget. -/
theorem fullBlock_operatorNorm_sq_le_probeSqBudget
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ 2 ≤
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        fullBlockProbeSqBudget M := by
  have h1 := fullBlock_operatorNorm_sq_le_probeAbsSum_sq hM
  have h2 := fullBlockProbeAbsSum_sq_le_probeSqBudget M
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ 2
        ≤ ((Fintype.card (BlockCoord d) : ℝ) * fullBlockProbeAbsSum M) ^ (2 : ℕ) :=
          h1
    _ = ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
          (fullBlockProbeAbsSum M) ^ (2 : ℕ) := by ring
    _ ≤ ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
          fullBlockProbeSqBudget M :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- Almost-sure finite-probe control of the Ch4 normalized full-block
fluctuation observable on a cube. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) :
    (fun a : RegCoeffField d =>
      Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center Q a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        fullBlockProbeSqBudget
          (fullBlockNormalizedFluctuationMatrix hP hStruct center (cubeSet Q) a) := by
  filter_upwards [fullBlockNormalizedFluctuationMatrix_isSymm_ae hP hStruct center Q] with a hM
  rw [Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
    fullBlockNormalizedFluctuationOperatorNormSq_eq_norm_sq]
  exact fullBlock_operatorNorm_sq_le_probeSqBudget hM

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
