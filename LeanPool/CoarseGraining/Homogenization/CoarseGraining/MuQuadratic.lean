/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.HilbertFinite
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions

/-! # Mu Quadratic -/

namespace Homogenization

noncomputable def blockPairingIntegrand {d : ℕ} (a : CoeffField d)
    (X Y : BlockState d) : Vec d → ℝ :=
  fun x => blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (Y.eval x))

noncomputable def blockEnergyAverage {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (X : BlockState d) : ℝ :=
  volumeAverage U (blockEnergyDensity a X)

noncomputable def blockPairingAverage {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (X Y : BlockState d) : ℝ :=
  volumeAverage U (blockPairingIntegrand a X Y)

theorem blockPairingIntegrand_eq_hilbertInner {d : ℕ} (a : CoeffField d)
    (X Y : BlockState d) :
    blockPairingIntegrand a X Y =
      fun x =>
        inner ℝ (HilbertBlockVec.ofBlockVec (X.eval x))
          (HilbertBlockVec.applyBlockMat (blockCoeffField a x)
            (HilbertBlockVec.ofBlockVec (Y.eval x))) := by
  funext x
  simp [blockPairingIntegrand]

theorem blockEnergyAverage_eq_half_blockPairingAverage_self {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (X : BlockState d) :
    blockEnergyAverage U a X = (1 / 2 : ℝ) * blockPairingAverage U a X X := by
  unfold blockEnergyAverage blockPairingAverage volumeAverage blockEnergyDensity blockPairingIntegrand
  rw [show (fun x => (1 / 2 : ℝ) * blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))) =
      fun x => (1 / 2 : ℝ) • blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) by
        funext x
        simp [smul_eq_mul]]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul, mul_assoc, mul_comm]

theorem blockEnergyDensity_eq_hilbertQuadratic {d : ℕ} (a : CoeffField d)
    (X : BlockState d) :
    blockEnergyDensity a X =
      fun x =>
        (1 / 2 : ℝ) *
          inner ℝ (HilbertBlockVec.ofBlockVec (X.eval x))
            (HilbertBlockVec.applyBlockMat (blockCoeffField a x)
              (HilbertBlockVec.ofBlockVec (X.eval x))) := by
  funext x
  rw [show blockEnergyDensity a X x =
      (1 / 2 : ℝ) * blockPairingIntegrand a X X x by
        simp [blockEnergyDensity, blockPairingIntegrand]]
  rw [blockPairingIntegrand_eq_hilbertInner]

theorem blockPairingIntegrand_add_left {d : ℕ} (a : CoeffField d)
    (X Y Z : BlockState d) :
    blockPairingIntegrand a (X + Y) Z =
      fun x => blockPairingIntegrand a X Z x + blockPairingIntegrand a Y Z x := by
  funext x
  simp [blockPairingIntegrand, blockVecDot_add_left]

theorem blockPairingIntegrand_add_right {d : ℕ} (a : CoeffField d)
    (X Y Z : BlockState d) :
    blockPairingIntegrand a X (Y + Z) =
      fun x => blockPairingIntegrand a X Y x + blockPairingIntegrand a X Z x := by
  funext x
  simp [blockPairingIntegrand, blockMatVecMul_add, blockVecDot_add_right]

theorem blockPairingIntegrand_smul_left {d : ℕ} (a : CoeffField d)
    (c : ℝ) (X Y : BlockState d) :
    blockPairingIntegrand a (c • X) Y =
      fun x => c * blockPairingIntegrand a X Y x := by
  funext x
  simp [blockPairingIntegrand, blockVecDot_smul_left]

theorem blockPairingIntegrand_smul_right {d : ℕ} (a : CoeffField d)
    (X Y : BlockState d) (c : ℝ) :
    blockPairingIntegrand a X (c • Y) =
      fun x => c * blockPairingIntegrand a X Y x := by
  funext x
  simp [blockPairingIntegrand, blockMatVecMul_smul, blockVecDot_smul_right]

theorem blockPairingAverage_add_left {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (X Y Z : BlockState d)
    (hXZ : MeasureTheory.IntegrableOn (blockPairingIntegrand a X Z) U)
    (hYZ : MeasureTheory.IntegrableOn (blockPairingIntegrand a Y Z) U) :
    blockPairingAverage U a (X + Y) Z =
      blockPairingAverage U a X Z + blockPairingAverage U a Y Z := by
  unfold blockPairingAverage volumeAverage
  rw [blockPairingIntegrand_add_left]
  rw [MeasureTheory.integral_add hXZ hYZ]
  simp [mul_add]

theorem blockPairingAverage_add_right {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (X Y Z : BlockState d)
    (hXY : MeasureTheory.IntegrableOn (blockPairingIntegrand a X Y) U)
    (hXZ : MeasureTheory.IntegrableOn (blockPairingIntegrand a X Z) U) :
    blockPairingAverage U a X (Y + Z) =
      blockPairingAverage U a X Y + blockPairingAverage U a X Z := by
  unfold blockPairingAverage volumeAverage
  rw [blockPairingIntegrand_add_right]
  rw [MeasureTheory.integral_add hXY hXZ]
  simp [mul_add]

theorem blockPairingAverage_smul_left {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (c : ℝ) (X Y : BlockState d) :
    blockPairingAverage U a (c • X) Y = c * blockPairingAverage U a X Y := by
  unfold blockPairingAverage volumeAverage
  rw [blockPairingIntegrand_smul_left]
  rw [show (fun x => c * blockPairingIntegrand a X Y x) =
      fun x => c • blockPairingIntegrand a X Y x by
        funext x
        simp [smul_eq_mul]]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul, mul_assoc, mul_comm]

theorem blockPairingAverage_smul_right {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (X Y : BlockState d) (c : ℝ) :
    blockPairingAverage U a X (c • Y) = c * blockPairingAverage U a X Y := by
  unfold blockPairingAverage volumeAverage
  rw [blockPairingIntegrand_smul_right]
  rw [show (fun x => c * blockPairingIntegrand a X Y x) =
      fun x => c • blockPairingIntegrand a X Y x by
        funext x
        simp [smul_eq_mul]]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul, mul_assoc, mul_comm]

/--
A linear family of minimizers for the doubled `μ`-problem. This isolates the
analytic content of the notes: once such a family is available, `μ(U,·;a)` is
automatically quadratic, hence the coarse block matrix exists canonically.
-/
structure LinearMuMinimizerFamily {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  field : BlockVec d → BlockState d
  map_add : ∀ P Q : BlockVec d, field (P + Q) = field P + field Q
  map_smul : ∀ (c : ℝ) (P : BlockVec d), field (c • P) = c • field P
  admissible : ∀ P : BlockVec d, IsBlockMuAdmissible U P (field P)
  pairingIntegrable :
    ∀ P Q : BlockVec d, MeasureTheory.IntegrableOn (blockPairingIntegrand a (field P) (field Q)) U
  realizes : ∀ P : BlockVec d, Mu U P a = blockEnergyAverage U a (field P)

namespace LinearMuMinimizerFamily

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

noncomputable def toBilin (F : LinearMuMinimizerFamily U a) :
    FullBlockVec d →ₗ[ℝ] FullBlockVec d →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => blockPairingAverage U a (F.field (ofFullBlockVec x)) (F.field (ofFullBlockVec y))
      map_add' := by
        intro y z
        simpa [ofFullBlockVec_add, F.map_add] using
          (blockPairingAverage_add_right U a
            (F.field (ofFullBlockVec x))
            (F.field (ofFullBlockVec y))
            (F.field (ofFullBlockVec z))
            (F.pairingIntegrable (ofFullBlockVec x) (ofFullBlockVec y))
            (F.pairingIntegrable (ofFullBlockVec x) (ofFullBlockVec z)))
      map_smul' := by
        intro c y
        simpa [ofFullBlockVec_smul, F.map_smul] using
          (blockPairingAverage_smul_right U a
            (F.field (ofFullBlockVec x))
            (F.field (ofFullBlockVec y))
            c) }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simpa [ofFullBlockVec_add, F.map_add] using
      (blockPairingAverage_add_left U a
        (F.field (ofFullBlockVec x))
        (F.field (ofFullBlockVec y))
        (F.field (ofFullBlockVec z))
        (F.pairingIntegrable (ofFullBlockVec x) (ofFullBlockVec z))
        (F.pairingIntegrable (ofFullBlockVec y) (ofFullBlockVec z)))
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro z
    simpa [ofFullBlockVec_smul, F.map_smul] using
      (blockPairingAverage_smul_left U a
        c
        (F.field (ofFullBlockVec x))
        (F.field (ofFullBlockVec z)))

noncomputable def quadraticForm (F : LinearMuMinimizerFamily U a) :
    QuadraticForm ℝ (FullBlockVec d) :=
  LinearMap.BilinMap.toQuadraticMap F.toBilin

theorem quadraticForm_apply (F : LinearMuMinimizerFamily U a) (P : BlockVec d) :
    F.quadraticForm (toFullBlockVec P) =
      blockPairingAverage U a (F.field P) (F.field P) := by
  simp [quadraticForm, toBilin]

theorem hasQuadraticMu (F : LinearMuMinimizerFamily U a) :
    HasQuadraticMu U a := by
  refine ⟨F.quadraticForm, ?_⟩
  intro P
  rw [F.realizes P, blockEnergyAverage_eq_half_blockPairingAverage_self]
  rw [F.quadraticForm_apply]

theorem exists_coarseBlockMatrix (F : LinearMuMinimizerFamily U a) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  exists_coarseBlockMatrix_of_hasQuadraticMu F.hasQuadraticMu

theorem existsUnique_coarseBlockMatrix (F : LinearMuMinimizerFamily U a) :
    ∃! Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  existsUnique_coarseBlockMatrix_of_hasQuadraticMu F.hasQuadraticMu

theorem mu_eq_half_blockVecDot_coarseBlockMatrix
    (F : LinearMuMinimizerFamily U a) (P : BlockVec d) :
    Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
  Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu F.hasQuadraticMu P

end LinearMuMinimizerFamily

end Homogenization
