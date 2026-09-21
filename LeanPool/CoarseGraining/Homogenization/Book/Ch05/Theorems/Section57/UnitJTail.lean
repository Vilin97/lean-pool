/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LimitNormalization
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ConcentrationAEMeasurable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds.FactorBounds

/-! # Unit JTail -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped BigOperators

/-!
# Unit-scale tail for the limiting-normalized block response

This file begins the deterministic unit-scale input for Corollary
`c.first.quenched.estimate`: a Γσ tail for
`J(□_0,\overline A^{-1/2}e,\overline A^{1/2}e)`.
-/

noncomputable section

/-- A full-block quadratic form whose entries are uniformly bounded is
controlled by a dimension-only constant on coordinatewise unit vectors. -/
theorem abs_fullBlockQuadraticCh04_le_card_sq_mul_of_entry_abs_le
    {d : ℕ} (M : FullBlockMat d) (x : FullBlockVec d) {F : ℝ}
    (hF : 0 ≤ F) (hentry : ∀ α β : BlockCoord d, |M α β| ≤ F)
    (hx : ∀ α : BlockCoord d, |x α| ≤ 1) :
    |Ch04.fullBlockQuadraticCh04 M x| ≤
      (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) * F := by
  classical
  have hrow :
      ∀ α : BlockCoord d,
        |Matrix.mulVec M x α| ≤ ∑ _β : BlockCoord d, F := by
    intro α
    calc
      |Matrix.mulVec M x α| = |∑ β : BlockCoord d, M α β * x β| := by
        simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ β : BlockCoord d, |M α β * x β| :=
        Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (f := fun β : BlockCoord d => M α β * x β)
      _ ≤ ∑ _β : BlockCoord d, F :=
        Finset.sum_le_sum fun β _hβ => by
          calc
            |M α β * x β| = |M α β| * |x β| := by rw [abs_mul]
            _ ≤ F * 1 :=
              mul_le_mul (hentry α β) (hx β) (abs_nonneg _) hF
            _ = F := by ring
  have hcoord :
      ∀ α : BlockCoord d,
        |x α * Matrix.mulVec M x α| ≤ ∑ _β : BlockCoord d, F := by
    intro α
    calc
      |x α * Matrix.mulVec M x α| = |x α| * |Matrix.mulVec M x α| := by
        rw [abs_mul]
      _ ≤ 1 * (∑ _β : BlockCoord d, F) :=
        mul_le_mul (hx α) (hrow α) (abs_nonneg _) (by norm_num)
      _ = ∑ _β : BlockCoord d, F := by ring
  calc
    |Ch04.fullBlockQuadraticCh04 M x|
        = |∑ α : BlockCoord d, x α * Matrix.mulVec M x α| := by
          simp [Ch04.fullBlockQuadraticCh04, dotProduct]
    _ ≤ ∑ α : BlockCoord d, |x α * Matrix.mulVec M x α| :=
      Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun α : BlockCoord d => x α * Matrix.mulVec M x α)
    _ ≤ ∑ _α : BlockCoord d, ∑ _β : BlockCoord d, F :=
      Finset.sum_le_sum fun α _ =>
        hcoord α
    _ = (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) * F := by
      simp
      ring

/-- A weighted two-coordinate block vector is nonzero if its two coordinates
are distinct. -/
private theorem blockBasis_add_smul_ne_zero_of_ne
    {d : ℕ} {α β : BlockCoord d} (c : ℝ) (hαβ : α ≠ β) :
    blockBasis α + c • blockBasis β ≠ (0 : BlockVec d) := by
  intro hzero
  have hcoord := congrArg (fun X : BlockVec d => toFullBlockVec X α) hzero
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord
      | inr j =>
          simp [blockBasis, toFullBlockVec] at hcoord
  | inr i =>
      cases β with
      | inl j =>
          simp [blockBasis, toFullBlockVec] at hcoord
      | inr j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord

/-- Expansion of a two-coordinate weighted block quadratic. -/
private theorem blockBasis_add_smul_pairing
    {d : ℕ} (A : BlockMat d) (α β : BlockCoord d) (c : ℝ) :
    blockVecDot (blockBasis α + c • blockBasis β)
        (blockMatVecMul A (blockBasis α + c • blockBasis β)) =
      blockMatEntry A α α + c * blockMatEntry A α β +
        c * blockMatEntry A β α + c ^ (2 : ℕ) * blockMatEntry A β β := by
  calc
    blockVecDot (blockBasis α + c • blockBasis β)
        (blockMatVecMul A (blockBasis α + c • blockBasis β))
        =
      blockVecDot (blockBasis α + c • blockBasis β)
        (blockMatVecMul A (blockBasis α) +
          c • blockMatVecMul A (blockBasis β)) := by
          rw [blockMatVecMul_add, blockMatVecMul_smul]
    _ =
      blockVecDot (blockBasis α + c • blockBasis β)
        (blockMatVecMul A (blockBasis α)) +
        blockVecDot (blockBasis α + c • blockBasis β)
          (c • blockMatVecMul A (blockBasis β)) := by
          rw [blockVecDot_add_right]
    _ =
      (blockVecDot (blockBasis α) (blockMatVecMul A (blockBasis α)) +
          c * blockVecDot (blockBasis β) (blockMatVecMul A (blockBasis α))) +
        c *
          (blockVecDot (blockBasis α) (blockMatVecMul A (blockBasis β)) +
            c * blockVecDot (blockBasis β) (blockMatVecMul A (blockBasis β))) := by
          rw [blockVecDot_add_left, blockVecDot_add_left,
            blockVecDot_smul_left, blockVecDot_smul_left,
            blockVecDot_smul_right]
          simp [blockVecDot_smul_right]
          ring
    _ =
      blockMatEntry A α α + c * blockMatEntry A α β +
        c * blockMatEntry A β α + c ^ (2 : ℕ) * blockMatEntry A β β := by
          rw [blockBasis_pairing, blockBasis_pairing, blockBasis_pairing,
            blockBasis_pairing]
          ring

/-- Weighted cross-entry control for a symmetric positive doubled block
matrix. -/
private theorem abs_blockMatEntry_le_weighted_diag_sum_of_symm_blockPosDef
    {d : ℕ} {A : BlockMat d} (hSymm : IsSymmetricBlockMat A)
    (hPos : Ch02.BlockPosDef A) {α β : BlockCoord d} (hαβ : α ≠ β)
    {b : ℝ} (hb : 0 < b) :
    |blockMatEntry A α β| ≤
      (blockMatEntry A α α + b ^ (2 : ℕ) * blockMatEntry A β β) /
        (2 * b) := by
  have hplus_pos :
      0 <
        blockVecDot (blockBasis α + b • blockBasis β)
          (blockMatVecMul A (blockBasis α + b • blockBasis β)) :=
    hPos (blockBasis α + b • blockBasis β)
      (blockBasis_add_smul_ne_zero_of_ne b hαβ)
  have hminus_pos :
      0 <
        blockVecDot (blockBasis α + (-b) • blockBasis β)
          (blockMatVecMul A (blockBasis α + (-b) • blockBasis β)) :=
    hPos (blockBasis α + (-b) • blockBasis β)
      (blockBasis_add_smul_ne_zero_of_ne (-b) hαβ)
  have hsymm : blockMatEntry A β α = blockMatEntry A α β := (hSymm α β).symm
  have hplus :
      0 <
        blockMatEntry A α α + b * blockMatEntry A α β +
          b * blockMatEntry A β α +
            b ^ (2 : ℕ) * blockMatEntry A β β := by
    have hpair := blockBasis_add_smul_pairing A α β b
    rwa [hpair] at hplus_pos
  have hminus :
      0 <
        blockMatEntry A α α + (-b) * blockMatEntry A α β +
          (-b) * blockMatEntry A β α +
            (-b) ^ (2 : ℕ) * blockMatEntry A β β := by
    have hpair := blockBasis_add_smul_pairing A α β (-b)
    rwa [hpair] at hminus_pos
  rw [hsymm] at hplus hminus
  have hden_pos : 0 < 2 * b := by positivity
  let x : ℝ := blockMatEntry A α β
  let S : ℝ := blockMatEntry A α α + b ^ (2 : ℕ) * blockMatEntry A β β
  have hupper_mul : x * (2 * b) ≤ S := by
    dsimp [x, S]
    nlinarith
  have hlower_mul : -S ≤ x * (2 * b) := by
    dsimp [x, S]
    nlinarith
  have hupper : x ≤ S / (2 * b) :=
    (le_div_iff₀ hden_pos).2 hupper_mul
  have hlower : -(S / (2 * b)) ≤ x := by
    have hdiv : (-S) / (2 * b) ≤ x :=
      (div_le_iff₀ hden_pos).2 hlower_mul
    simpa [neg_div] using hdiv
  exact abs_le.2 ⟨by simpa [x, S] using hlower, by simpa [x, S] using hupper⟩

private theorem diagonal_toFullBlockMat_diagonal_apply
    {d : ℕ} (r : BlockCoord d → ℝ) (A : BlockMat d)
    (α β : BlockCoord d) :
    (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r) α β =
      r α * blockMatEntry A α β * r β := by
  simp [Matrix.mul_apply, Matrix.diagonal, toFullBlockMat, blockMatEntry]

private theorem scalarFullBlockInvSqrtDiag_upper_abs_mul_self
    {d : ℕ} {L : ℝ} (hL : 0 < L) (i j : Fin d) :
    |Ch04.scalarFullBlockInvSqrtDiag (d := d) L L (Sum.inl i)| *
        |Ch04.scalarFullBlockInvSqrtDiag (d := d) L L (Sum.inl j)| =
      L⁻¹ := by
  have hs : 0 < √L := Real.sqrt_pos.2 hL
  simp [Ch04.scalarFullBlockInvSqrtDiag, abs_of_pos (inv_pos.mpr hs)]
  field_simp [hs.ne', hL.ne']
  rw [Real.sq_sqrt hL.le]

private theorem scalarFullBlockInvSqrtDiag_lower_abs_mul_self
    {d : ℕ} {L : ℝ} (hL : 0 < L) (i j : Fin d) :
    |Ch04.scalarFullBlockInvSqrtDiag (d := d) L L (Sum.inr i)| *
        |Ch04.scalarFullBlockInvSqrtDiag (d := d) L L (Sum.inr j)| =
      L := by
  simp [Ch04.scalarFullBlockInvSqrtDiag, abs_of_nonneg (Real.sqrt_nonneg L)]
  rw [← pow_two, Real.sq_sqrt hL.le]

private theorem scalarFullBlockInvSqrtDiag_cross_abs_mul
    {d : ℕ} {L : ℝ} (hL : 0 < L) (i j : Fin d) :
    |Ch04.scalarFullBlockInvSqrtDiag (d := d) L L (Sum.inl i)| *
        |Ch04.scalarFullBlockInvSqrtDiag (d := d) L L (Sum.inr j)| =
      1 := by
  have hs : 0 < √L := Real.sqrt_pos.2 hL
  simp [Ch04.scalarFullBlockInvSqrtDiag, abs_of_pos hs,
    abs_of_pos (inv_pos.mpr hs), hs.ne']

/-- Entrywise control of a scalar-normalized doubled block matrix by the
weighted upper/lower ellipticity factors. -/
theorem abs_invSqrtConj_toFullBlockMat_entry_le_weighted
    {d : ℕ} {A : BlockMat d} {L Λ I : ℝ}
    (hSymm : IsSymmetricBlockMat A) (hPos : Ch02.BlockPosDef A)
    (hL : 0 < L) (hΛ : 0 ≤ Λ) (hI : 0 ≤ I)
    (hUL : ∀ i j : Fin d, |A.upperLeft i j| ≤ Λ)
    (hLR : ∀ i j : Fin d, |A.lowerRight i j| ≤ I)
    (α β : BlockCoord d) :
    |(Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag (d := d) L L) *
        toFullBlockMat A *
          Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag (d := d) L L))
        α β| ≤
      L⁻¹ * Λ + L * I := by
  let r : BlockCoord d → ℝ := Ch04.scalarFullBlockInvSqrtDiag (d := d) L L
  have hW_nonneg : 0 ≤ L⁻¹ * Λ + L * I := by
    exact add_nonneg (mul_nonneg (inv_pos.mpr hL).le hΛ)
      (mul_nonneg hL.le hI)
  have hentry :
      ∀ α β : BlockCoord d,
        (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r) α β =
          r α * blockMatEntry A α β * r β :=
    diagonal_toFullBlockMat_diagonal_apply r A
  have hcross_bound :
      ∀ i j : Fin d,
        |A.upperRight i j| ≤ L⁻¹ * Λ + L * I := by
    intro i j
    have hcross :=
      abs_blockMatEntry_le_weighted_diag_sum_of_symm_blockPosDef
        (A := A) hSymm hPos
        (α := Sum.inl i) (β := Sum.inr j)
        (by intro h; cases h) hL
    have hdiag_upper : A.upperLeft i i ≤ Λ :=
      (le_abs_self (A.upperLeft i i)).trans (hUL i i)
    have hdiag_lower : A.lowerRight j j ≤ I :=
      (le_abs_self (A.lowerRight j j)).trans (hLR j j)
    have hS_le :
        A.upperLeft i i + L ^ (2 : ℕ) * A.lowerRight j j ≤
          Λ + L ^ (2 : ℕ) * I :=
      add_le_add hdiag_upper
        (mul_le_mul_of_nonneg_left hdiag_lower (sq_nonneg L))
    have hden_nonneg : 0 ≤ 2 * L := by positivity
    have hhalf :
        (A.upperLeft i i + L ^ (2 : ℕ) * A.lowerRight j j) / (2 * L) ≤
          (Λ + L ^ (2 : ℕ) * I) / (2 * L) :=
      div_le_div_of_nonneg_right hS_le hden_nonneg
    have hrewrite :
        (Λ + L ^ (2 : ℕ) * I) / (2 * L) =
          (1 / 2 : ℝ) * (L⁻¹ * Λ + L * I) := by
      field_simp [hL.ne']
    have hhalf_le_weight :
        (1 / 2 : ℝ) * (L⁻¹ * Λ + L * I) ≤ L⁻¹ * Λ + L * I := by
      nlinarith
    calc
      |A.upperRight i j| ≤
          (A.upperLeft i i + L ^ (2 : ℕ) * A.lowerRight j j) / (2 * L) := by
            simpa [blockMatEntry] using hcross
      _ ≤ (Λ + L ^ (2 : ℕ) * I) / (2 * L) := hhalf
      _ = (1 / 2 : ℝ) * (L⁻¹ * Λ + L * I) := hrewrite
      _ ≤ L⁻¹ * Λ + L * I := hhalf_le_weight
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          calc
            |(Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
                (Sum.inl i) (Sum.inl j)|
                = L⁻¹ * |A.upperLeft i j| := by
                  rw [hentry]
                  simp only [r, blockMatEntry]
                  rw [abs_mul, abs_mul]
                  calc
                    |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl i)| *
                          |A.upperLeft i j| *
                        |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl j)| =
                        (|Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl i)| *
                            |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl j)|) *
                          |A.upperLeft i j| := by ring
                    _ = L⁻¹ * |A.upperLeft i j| := by
                      rw [scalarFullBlockInvSqrtDiag_upper_abs_mul_self hL i j]
            _ ≤ L⁻¹ * Λ :=
              mul_le_mul_of_nonneg_left (hUL i j) (inv_pos.mpr hL).le
            _ ≤ L⁻¹ * Λ + L * I :=
              le_add_of_nonneg_right (mul_nonneg hL.le hI)
      | inr j =>
          calc
            |(Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
                (Sum.inl i) (Sum.inr j)|
                = |A.upperRight i j| := by
                  rw [hentry]
                  simp only [r, blockMatEntry]
                  rw [abs_mul, abs_mul]
                  calc
                    |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl i)| *
                          |A.upperRight i j| *
                        |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr j)| =
                        (|Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl i)| *
                            |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr j)|) *
                          |A.upperRight i j| := by ring
                    _ = |A.upperRight i j| := by
                      rw [scalarFullBlockInvSqrtDiag_cross_abs_mul hL i j]
                      ring
            _ ≤ L⁻¹ * Λ + L * I := hcross_bound i j
  | inr i =>
      cases β with
      | inl j =>
          calc
            |(Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
                (Sum.inr i) (Sum.inl j)|
                = |A.lowerLeft i j| := by
                  rw [hentry]
                  have hcross := scalarFullBlockInvSqrtDiag_cross_abs_mul (d := d)
                    (L := L) hL j i
                  simp only [r, blockMatEntry]
                  rw [abs_mul, abs_mul]
                  calc
                    |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr i)| *
                          |A.lowerLeft i j| *
                        |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl j)| =
                        (|Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inl j)| *
                            |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr i)|) *
                          |A.lowerLeft i j| := by ring
                    _ = |A.lowerLeft i j| := by
                      rw [hcross]
                      ring
            _ = |A.upperRight j i| := by
              rw [abs_eq_abs]
              exact Or.inl (by simpa [blockMatEntry] using (hSymm (Sum.inr i) (Sum.inl j)))
            _ ≤ L⁻¹ * Λ + L * I := hcross_bound j i
      | inr j =>
          calc
            |(Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
                (Sum.inr i) (Sum.inr j)|
                = L * |A.lowerRight i j| := by
                  rw [hentry]
                  simp only [r, blockMatEntry]
                  rw [abs_mul, abs_mul]
                  calc
                    |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr i)| *
                          |A.lowerRight i j| *
                        |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr j)| =
                        (|Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr i)| *
                            |Ch04.scalarFullBlockInvSqrtDiag L L (Sum.inr j)|) *
                          |A.lowerRight i j| := by ring
                    _ = L * |A.lowerRight i j| := by
                      rw [scalarFullBlockInvSqrtDiag_lower_abs_mul_self hL i j]
            _ ≤ L * I :=
              mul_le_mul_of_nonneg_left (hLR i j) hL.le
            _ ≤ L⁻¹ * Λ + L * I :=
              le_add_of_nonneg_left (mul_nonneg (inv_pos.mpr hL).le hΛ)

/-- Diagonal conjugation of a block matrix is the same quadratic form as
evaluating the original block matrix on the diagonally normalized vector. -/
theorem fullBlockQuadraticCh04_diagonal_toFullBlockMat
    {d : ℕ} (r : BlockCoord d → ℝ) (A : BlockMat d) (q : FullBlockVec d) :
    Ch04.fullBlockQuadraticCh04 (toFullBlockMat A)
        (Matrix.mulVec (Matrix.diagonal r) q) =
      Ch04.fullBlockQuadraticCh04
        (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r) q := by
  have hleft :=
    Ch04.fullBlockQuadraticCh04_toFullBlockMat A
      (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q))
  have hright :=
    Section54.VarianceBoundGoodScale.fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
      r A q
  rw [toFullBlockVec_ofFullBlockVec] at hleft
  calc
    Ch04.fullBlockQuadraticCh04 (toFullBlockMat A)
        (Matrix.mulVec (Matrix.diagonal r) q)
        =
      blockVecDot (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q))
        (blockMatVecMul A (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q))) :=
        hleft
    _ =
      Section54.VarianceBoundGoodScale.fullBlockQuadratic
        (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r) q :=
        hright.symm
    _ =
      Ch04.fullBlockQuadraticCh04
        (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r) q := by
        rfl

/-- Reflection preserves doubled-block positive definiteness. -/
theorem blockPosDef_blockReflect {d : ℕ} {A : BlockMat d}
    (hA : Ch02.BlockPosDef A) :
    Ch02.BlockPosDef (blockReflect A) := by
  intro X hX
  have hswap : (X.2, X.1) ≠ (0 : BlockVec d) := by
    intro hzero
    exact hX (Prod.ext (congrArg Prod.snd hzero) (congrArg Prod.fst hzero))
  simpa using hA (X.2, X.1) hswap

/-- The square-root scalar diagonal is the inverse-square-root diagonal with
the reciprocal scalar. -/
private theorem scalarFullBlockSqrtDiag_eq_invSqrtDiag_inv
    {d : ℕ} (L : ℝ) :
    Section56.scalarFullBlockSqrtDiag (d := d) L L =
      Ch04.scalarFullBlockInvSqrtDiag (d := d) L⁻¹ L⁻¹ := by
  funext α
  cases α <;> simp [Section56.scalarFullBlockSqrtDiag,
    Ch04.scalarFullBlockInvSqrtDiag, Real.sqrt_inv]

/-- Entrywise control for the reflected scalar square-root normalization. -/
theorem abs_sqrtConj_reflect_toFullBlockMat_entry_le_weighted
    {d : ℕ} {A : BlockMat d} {L Λ I : ℝ}
    (hSymm : IsSymmetricBlockMat A) (hPos : Ch02.BlockPosDef A)
    (hL : 0 < L) (hΛ : 0 ≤ Λ) (hI : 0 ≤ I)
    (hUL : ∀ i j : Fin d, |A.upperLeft i j| ≤ Λ)
    (hLR : ∀ i j : Fin d, |A.lowerRight i j| ≤ I)
    (α β : BlockCoord d) :
    |(Matrix.diagonal (Section56.scalarFullBlockSqrtDiag (d := d) L L) *
        toFullBlockMat (blockReflect A) *
          Matrix.diagonal (Section56.scalarFullBlockSqrtDiag (d := d) L L))
        α β| ≤
      L⁻¹ * Λ + L * I := by
  have h :=
    abs_invSqrtConj_toFullBlockMat_entry_le_weighted
      (A := blockReflect A) (L := L⁻¹) (Λ := I) (I := Λ)
      (isSymmetricBlockMat_blockReflect hSymm)
      (blockPosDef_blockReflect hPos)
      (inv_pos.mpr hL) hI hΛ
      (by intro i j; simpa [blockReflect] using hLR i j)
      (by intro i j; simpa [blockReflect] using hUL i j) α β
  have hsqrt := scalarFullBlockSqrtDiag_eq_invSqrtDiag_inv (d := d) L
  calc
    |(Matrix.diagonal (Section56.scalarFullBlockSqrtDiag (d := d) L L) *
        toFullBlockMat (blockReflect A) *
          Matrix.diagonal (Section56.scalarFullBlockSqrtDiag (d := d) L L))
        α β|
        =
      |(Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag (d := d) L⁻¹ L⁻¹) *
        toFullBlockMat (blockReflect A) *
          Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag (d := d) L⁻¹ L⁻¹))
        α β| := by
        rw [hsqrt]
    _ ≤ (L⁻¹)⁻¹ * I + L⁻¹ * Λ := h
    _ = L⁻¹ * Λ + L * I := by
      field_simp [hL.ne']
      ring

namespace GammaSigmaCoarseGrainedEllipticity

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

private theorem limitWeightedUnitEllipticityObservable_nonneg
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (a : RegCoeffField d) :
    0 ≤ limitWeightedUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower a := by
  have hL_pos : 0 < barSigmaLimit hP hStruct := hΓ.barSigmaLimit_pos
  have hΛ_nonneg :
      0 ≤ Ch04.LambdaSqCoeffField (originCube d 0)
        hΓ.params.sUpper (.finite 1) a :=
    Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
      hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg :
      0 ≤ (Ch04.lambdaSqCoeffField (originCube d 0)
        hΓ.params.sLower (.finite 1) a)⁻¹ :=
    inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  dsimp [limitWeightedUnitEllipticityObservable]
  exact add_nonneg
    (mul_nonneg (inv_pos.mpr hL_pos).le hΛ_nonneg)
    (mul_nonneg hL_pos.le hI_nonneg)

/-- The first normalized quadratic term in the unit-scale `J` observable is
controlled by the limiting weighted unit ellipticity observable. -/
private theorem abs_limitInvSqrt_quadratic_le_card_sq_mul_weighted_ae
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (e : FullBlockVec d) (he : ∀ α : BlockCoord d, |e α| ≤ 1) :
    (fun a : RegCoeffField d =>
      |Ch04.fullBlockQuadraticCh04
        (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d 0)) a))
        (toFullBlockVec (scalarLimitInvSqrtBlockVec hP hStruct e))|) ≤ᵐ[P]
      fun a =>
        (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
          limitWeightedUnitEllipticityObservable hP hStruct
            hΓ.params.sUpper hΓ.params.sLower a := by
  let L : ℝ := barSigmaLimit hP hStruct
  let r : BlockCoord d → ℝ := Ch04.scalarFullBlockInvSqrtDiag (d := d) L L
  let D : FullBlockMat d := Matrix.diagonal r
  let Y : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hL_pos : 0 < L := by simpa [L] using hΓ.barSigmaLimit_pos
  have hUL_ae :
      ∀ᵐ a ∂P, ∀ i j : Fin d,
        |(coarseBlockMatrix (cubeSet (originCube d 0)) a.toFun).upperLeft i j| ≤
          Ch04.LambdaSqCoeffField (originCube d 0)
            hΓ.params.sUpper (.finite 1) a := by
    filter_upwards
      [Ch04.ae_forall_mem_finset_nested (P := P) Finset.univ
        (fun _ : Fin d => Finset.univ)
        (fun i _hi j _hj =>
          Ch04.RestrictionLawCarrier.upperLeft_abs_entry_le_LambdaSqCoeffField_ae
            hP (originCube d 0) hΓ.sUpper_pos i j)] with a h i j
    exact h i (by simp) j (by simp)
  have hLR_ae :
      ∀ᵐ a ∂P, ∀ i j : Fin d,
        |(coarseBlockMatrix (cubeSet (originCube d 0)) a.toFun).lowerRight i j| ≤
          (Ch04.lambdaSqCoeffField (originCube d 0)
            hΓ.params.sLower (.finite 1) a)⁻¹ := by
    filter_upwards
      [Ch04.ae_forall_mem_finset_nested (P := P) Finset.univ
        (fun _ : Fin d => Finset.univ)
        (fun i _hi j _hj =>
          Ch04.RestrictionLawCarrier.lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae
            hP (originCube d 0) hΓ.sLower_pos i j)] with a h i j
    exact h i (by simp) j (by simp)
  filter_upwards [hP.ae_locallyUniformlyEllipticField, hUL_ae, hLR_ae]
    with a ha hUL hLR
  let A : BlockMat d := coarseBlockMatrix (cubeSet (originCube d 0)) a
  let Λ : ℝ :=
    Ch04.LambdaSqCoeffField (originCube d 0)
      hΓ.params.sUpper (.finite 1) a
  let I : ℝ :=
    (Ch04.lambdaSqCoeffField (originCube d 0)
      hΓ.params.sLower (.finite 1) a)⁻¹
  have hΛ_nonneg : 0 ≤ Λ := by
    dsimp [Λ]
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
      hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  have hEq :
      A = Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d 0))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (originCube d 0)) := by
    simpa [A] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha (originCube d 0)
  have hSymm : IsSymmetricBlockMat A := by
    rw [hEq]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain (originCube d 0))
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
        (originCube d 0))
  have hPos : Ch02.BlockPosDef A := by
    rw [hEq]
    exact
      (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain (originCube d 0))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (originCube d 0))).block_matrix_posDef
  have hentry_bound :
      ∀ α β : BlockCoord d, |(D * toFullBlockMat A * D) α β| ≤ Y a := by
    intro α β
    have h := abs_invSqrtConj_toFullBlockMat_entry_le_weighted
      (A := A) (L := L) (Λ := Λ) (I := I)
      hSymm hPos hL_pos hΛ_nonneg hI_nonneg
      (by intro i j; simpa [A, Λ] using hUL i j)
      (by intro i j; simpa [A, I] using hLR i j) α β
    simpa [Y, limitWeightedUnitEllipticityObservable, L, Λ, I, D, r] using h
  have hquad :
      Ch04.fullBlockQuadraticCh04 (toFullBlockMat A)
          (toFullBlockVec (scalarLimitInvSqrtBlockVec hP hStruct e)) =
        Ch04.fullBlockQuadraticCh04 (D * toFullBlockMat A * D) e := by
    simp only [scalarLimitInvSqrtBlockVec, toFullBlockVec_ofFullBlockVec,
      scalarLimitInvSqrtMatrix]
    simpa [D, r, L] using
      fullBlockQuadraticCh04_diagonal_toFullBlockMat r A e
  calc
    |Ch04.fullBlockQuadraticCh04
        (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d 0)) a))
        (toFullBlockVec (scalarLimitInvSqrtBlockVec hP hStruct e))|
        = |Ch04.fullBlockQuadraticCh04 (D * toFullBlockMat A * D) e| := by
          simpa [A] using congrArg abs hquad
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) * Y a :=
      abs_fullBlockQuadraticCh04_le_card_sq_mul_of_entry_abs_le
        (D * toFullBlockMat A * D) e
        (hΓ.limitWeightedUnitEllipticityObservable_nonneg a)
        hentry_bound he
    _ =
      (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
        limitWeightedUnitEllipticityObservable hP hStruct
          hΓ.params.sUpper hΓ.params.sLower a := by
        rfl

/-- The reflected square-root quadratic term in the unit-scale `J` observable
is controlled by the same limiting weighted unit ellipticity observable. -/
private theorem abs_limitSqrt_reflect_quadratic_le_card_sq_mul_weighted_ae
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (e : FullBlockVec d) (he : ∀ α : BlockCoord d, |e α| ≤ 1) :
    (fun a : RegCoeffField d =>
      |Ch04.fullBlockQuadraticCh04
        (Ch04.fullBlockReflect
          (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d 0)) a)))
        (toFullBlockVec (scalarLimitSqrtBlockVec hP hStruct e))|) ≤ᵐ[P]
      fun a =>
        (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
          limitWeightedUnitEllipticityObservable hP hStruct
            hΓ.params.sUpper hΓ.params.sLower a := by
  let L : ℝ := barSigmaLimit hP hStruct
  let r : BlockCoord d → ℝ := Section56.scalarFullBlockSqrtDiag (d := d) L L
  let T : FullBlockMat d := Matrix.diagonal r
  let Y : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hL_pos : 0 < L := by simpa [L] using hΓ.barSigmaLimit_pos
  have hUL_ae :
      ∀ᵐ a ∂P, ∀ i j : Fin d,
        |(coarseBlockMatrix (cubeSet (originCube d 0)) a.toFun).upperLeft i j| ≤
          Ch04.LambdaSqCoeffField (originCube d 0)
            hΓ.params.sUpper (.finite 1) a := by
    filter_upwards
      [Ch04.ae_forall_mem_finset_nested (P := P) Finset.univ
        (fun _ : Fin d => Finset.univ)
        (fun i _hi j _hj =>
          Ch04.RestrictionLawCarrier.upperLeft_abs_entry_le_LambdaSqCoeffField_ae
            hP (originCube d 0) hΓ.sUpper_pos i j)] with a h i j
    exact h i (by simp) j (by simp)
  have hLR_ae :
      ∀ᵐ a ∂P, ∀ i j : Fin d,
        |(coarseBlockMatrix (cubeSet (originCube d 0)) a.toFun).lowerRight i j| ≤
          (Ch04.lambdaSqCoeffField (originCube d 0)
            hΓ.params.sLower (.finite 1) a)⁻¹ := by
    filter_upwards
      [Ch04.ae_forall_mem_finset_nested (P := P) Finset.univ
        (fun _ : Fin d => Finset.univ)
        (fun i _hi j _hj =>
          Ch04.RestrictionLawCarrier.lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae
            hP (originCube d 0) hΓ.sLower_pos i j)] with a h i j
    exact h i (by simp) j (by simp)
  filter_upwards [hP.ae_locallyUniformlyEllipticField, hUL_ae, hLR_ae]
    with a ha hUL hLR
  let A : BlockMat d := coarseBlockMatrix (cubeSet (originCube d 0)) a
  let Λ : ℝ :=
    Ch04.LambdaSqCoeffField (originCube d 0)
      hΓ.params.sUpper (.finite 1) a
  let I : ℝ :=
    (Ch04.lambdaSqCoeffField (originCube d 0)
      hΓ.params.sLower (.finite 1) a)⁻¹
  have hΛ_nonneg : 0 ≤ Λ := by
    dsimp [Λ]
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
      hΓ.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hΓ.sLower_pos (by norm_num : (1 : ℝ) ≤ 1))
  have hEq :
      A = Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d 0))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (originCube d 0)) := by
    simpa [A] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha (originCube d 0)
  have hSymm : IsSymmetricBlockMat A := by
    rw [hEq]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain (originCube d 0))
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
        (originCube d 0))
  have hPos : Ch02.BlockPosDef A := by
    rw [hEq]
    exact
      (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain (originCube d 0))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (originCube d 0))).block_matrix_posDef
  have hentry_bound :
      ∀ α β : BlockCoord d, |(T * toFullBlockMat (blockReflect A) * T) α β| ≤ Y a := by
    intro α β
    have h := abs_sqrtConj_reflect_toFullBlockMat_entry_le_weighted
      (A := A) (L := L) (Λ := Λ) (I := I)
      hSymm hPos hL_pos hΛ_nonneg hI_nonneg
      (by intro i j; simpa [A, Λ] using hUL i j)
      (by intro i j; simpa [A, I] using hLR i j) α β
    simpa [Y, limitWeightedUnitEllipticityObservable, L, Λ, I, T, r] using h
  have hquad :
      Ch04.fullBlockQuadraticCh04 (Ch04.fullBlockReflect (toFullBlockMat A))
          (toFullBlockVec (scalarLimitSqrtBlockVec hP hStruct e)) =
        Ch04.fullBlockQuadraticCh04 (T * toFullBlockMat (blockReflect A) * T) e := by
    rw [Ch04.fullBlockReflect_toFullBlockMat A]
    simp only [scalarLimitSqrtBlockVec, toFullBlockVec_ofFullBlockVec,
      scalarLimitSqrtMatrix]
    simpa [T, r, L] using
      fullBlockQuadraticCh04_diagonal_toFullBlockMat r (blockReflect A) e
  calc
    |Ch04.fullBlockQuadraticCh04
        (Ch04.fullBlockReflect
          (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d 0)) a)))
        (toFullBlockVec (scalarLimitSqrtBlockVec hP hStruct e))|
        = |Ch04.fullBlockQuadraticCh04 (T * toFullBlockMat (blockReflect A) * T) e| := by
          simpa [A] using congrArg abs hquad
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) * Y a :=
      abs_fullBlockQuadraticCh04_le_card_sq_mul_of_entry_abs_le
        (T * toFullBlockMat (blockReflect A) * T) e
        (hΓ.limitWeightedUnitEllipticityObservable_nonneg a)
        hentry_bound he
    _ =
      (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
        limitWeightedUnitEllipticityObservable hP hStruct
          hΓ.params.sUpper hΓ.params.sLower a := by
        rfl

/-- Unit-scale limiting-normalized `J` is pointwise dominated, a.e., by the
limiting weighted unit ellipticity observable. -/
theorem limitNormalizedBlockJObservable_le_card_sq_mul_weighted_ae
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (e : FullBlockVec d) (he : ∀ α : BlockCoord d, |e α| ≤ 1) :
    (limitNormalizedBlockJObservable hP hStruct (originCube d 0) e) ≤ᵐ[P]
      fun a =>
        (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
          limitWeightedUnitEllipticityObservable hP hStruct
            hΓ.params.sUpper hΓ.params.sLower a := by
  let C : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let Y : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hInv :=
    hΓ.abs_limitInvSqrt_quadratic_le_card_sq_mul_weighted_ae e he
  have hSqrt :=
    hΓ.abs_limitSqrt_reflect_quadratic_le_card_sq_mul_weighted_ae e he
  have hJae :
      limitNormalizedBlockJObservable hP hStruct (originCube d 0) e =ᵐ[P]
        fun a : RegCoeffField d =>
          Ch04.blockJQuadraticFullBlockMat
            (toFullBlockMat
              (coarseBlockMatrix (cubeSet (originCube d 0)) a))
            (scalarLimitInvSqrtBlockVec hP hStruct e)
            (scalarLimitSqrtBlockVec hP hStruct e) := by
    simpa [limitNormalizedBlockJObservable] using
      Ch04.blockJObservableCubeSetBlockVec_ae_eq_blockJQuadraticFullBlockMat
        hP (originCube d 0)
        (scalarLimitInvSqrtBlockVec hP hStruct e)
        (scalarLimitSqrtBlockVec hP hStruct e)
  filter_upwards [hJae, hInv, hSqrt] with a hJ hInv_a hSqrt_a
  let M : FullBlockMat d :=
    toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d 0)) a)
  let Pvec : BlockVec d := scalarLimitInvSqrtBlockVec hP hStruct e
  let Qvec : BlockVec d := scalarLimitSqrtBlockVec hP hStruct e
  let q₁ : ℝ := Ch04.fullBlockQuadraticCh04 M (toFullBlockVec Pvec)
  let q₂ : ℝ := Ch04.fullBlockQuadraticCh04 (Ch04.fullBlockReflect M)
    (toFullBlockVec Qvec)
  let pairing : ℝ := blockVecDot Pvec Qvec
  have hq₁_le : q₁ ≤ C * Y a := by
    exact (le_abs_self q₁).trans (by
      simpa [q₁, M, Pvec, C, Y] using hInv_a)
  have hq₂_le : q₂ ≤ C * Y a := by
    exact (le_abs_self q₂).trans (by
      simpa [q₂, M, Qvec, C, Y] using hSqrt_a)
  have hpair_nonneg : 0 ≤ pairing := by
    dsimp [pairing, Pvec, Qvec]
    rw [hΓ.scalarLimit_normalizers_pairing_eq_dotProduct]
    exact Section54.VarianceBoundGoodScale.dotProduct_self_nonneg e
  calc
    limitNormalizedBlockJObservable hP hStruct (originCube d 0) e a
        =
      Ch04.blockJQuadraticFullBlockMat M Pvec Qvec := by
        simpa [M, Pvec, Qvec] using hJ
    _ ≤ C * Y a := by
      change (1 / 2 : ℝ) * q₁ + (1 / 2 : ℝ) * q₂ - pairing ≤ C * Y a
      linarith

/-- The unit-cube limiting-normalized `J` observable inherits the Γσ tail from
the strengthened unit ellipticity assumption. -/
theorem limitNormalizedBlockJObservable_unit_isBigO
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (e : FullBlockVec d) (he : ∀ α : BlockCoord d, |e α| ≤ 1) :
    IsBigO P (gammaSigma hΓ.sigma)
      (limitNormalizedBlockJObservable hP hStruct (originCube d 0) e)
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
        (thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat)) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let C : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let Y : RegCoeffField d → ℝ :=
    limitWeightedUnitEllipticityObservable hP hStruct
      hΓ.params.sUpper hΓ.params.sLower
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have htailY :
      IsBigO P (gammaSigma hΓ.sigma) Y
        (thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat) := by
    simpa [Y] using hΓ.limitWeightedUnitEllipticityObservable_isBigO
  have htailCY :
      IsBigO P (gammaSigma hΓ.sigma) (fun a => C * Y a)
        (C * (thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat)) := by
    exact IndependentSums.IsBigO.const_mul
      (μ := P) (Ψ := gammaSigma hΓ.sigma)
      (X := Y)
      (A := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat)
      hC_nonneg htailY
  have hle_ae :=
    hΓ.limitNormalizedBlockJObservable_le_card_sq_mul_weighted_ae e he
  change IsBigOWith P (gammaSigma hΓ.sigma)
    (fun a : RegCoeffField d =>
      |limitNormalizedBlockJObservable hP hStruct (originCube d 0) e a|)
    (C * (thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat))
  refine Ch04.isBigOWith_of_ae_le
    (μ := P) (Ψ := gammaSigma hΓ.sigma)
    (X := fun a : RegCoeffField d => |C * Y a|)
    (Y := fun a : RegCoeffField d =>
      |limitNormalizedBlockJObservable hP hStruct (originCube d 0) e a|)
    htailCY ?_
  filter_upwards [hle_ae] with a hle
  have hJ_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct (originCube d 0) e a := by
    simpa [limitNormalizedBlockJObservable] using
      Ch04.blockJObservableCubeSetBlockVec_nonneg (originCube d 0)
        (scalarLimitInvSqrtBlockVec hP hStruct e)
        (scalarLimitSqrtBlockVec hP hStruct e) a
  have hCY_nonneg : 0 ≤ C * Y a := by
    exact mul_nonneg hC_nonneg
      (by simpa [Y] using hΓ.limitWeightedUnitEllipticityObservable_nonneg a)
  rw [abs_of_nonneg hJ_nonneg, abs_of_nonneg hCY_nonneg]
  simpa [C, Y] using hle

end GammaSigmaCoarseGrainedEllipticity

end

end Section57
end Ch05
end Book
end Homogenization
