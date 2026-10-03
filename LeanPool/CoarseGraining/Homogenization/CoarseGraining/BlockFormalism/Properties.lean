/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.EllipticBounds

/-! # Properties -/

@[expose] public section

namespace Homogenization

/-!
# Block formalism -- block-state properties and admissibility

IsBlockPotentialOn / IsBlockPotentialZeroTraceOn / IsBlockSolenoidalOn /
IsBlockSolenoidalZeroNormalTraceOn / IsBlockTestOn / BlockResponseSpace and
IsBlockMuAdmissible definitions plus the IsBlockMuAdmissible namespace with
its potentialCorrection / isPotentialZeroTrace bridges.
-/

def IsBlockPotentialOn {d : ℕ} (U : Set (Vec d)) (X : BlockState d) : Prop :=
  IsPotentialOn U X.potential

def IsBlockPotentialZeroTraceOn {d : ℕ} (U : Set (Vec d)) (X : BlockState d) : Prop :=
  IsPotentialZeroTraceOn U X.potential

def IsBlockSolenoidalOn {d : ℕ} (U : Set (Vec d)) (X : BlockState d) : Prop :=
  IsSolenoidalOn U X.flux

def IsBlockSolenoidalZeroNormalTraceOn {d : ℕ} (U : Set (Vec d)) (X : BlockState d) : Prop :=
  IsSolenoidalZeroNormalTraceOn U X.flux

def IsBlockTestOn {d : ℕ} (U : Set (Vec d)) (Y : BlockState d) : Prop :=
  IsBlockPotentialZeroTraceOn U Y ∧ IsBlockSolenoidalZeroNormalTraceOn U Y

def BlockResponseSpace {d : ℕ} (a : CoeffField d) (U : Set (Vec d)) (X : BlockState d) : Prop :=
  IsBlockPotentialOn U X ∧
    IsBlockSolenoidalOn U X ∧
    ∀ Y : BlockState d, IsBlockTestOn U Y →
      ∫ x in U,
        blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
          ∂MeasureTheory.volume = 0

def IsBlockMuAdmissible {d : ℕ} (U : Set (Vec d)) (P : BlockVec d) (X : BlockState d) : Prop :=
  MemVectorL2 U (fun x => X.potential x - P.1) ∧
    IsPotentialZeroTraceOn U (fun x => X.potential x - P.1) ∧
      MemVectorL2 U (fun x => X.flux x - P.2) ∧
        IsSolenoidalZeroNormalTraceOn U (fun x => X.flux x - P.2)

namespace IsBlockMuAdmissible

theorem potentialCorrection_memL2 {d : ℕ} {U : Set (Vec d)} {P : BlockVec d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    MemVectorL2 U (fun x => X.potential x - P.1) :=
  hX.1

theorem isPotentialZeroTrace {d : ℕ} {U : Set (Vec d)} {P : BlockVec d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    IsPotentialZeroTraceOn U (fun x => X.potential x - P.1) :=
  hX.2.1

theorem fluxCorrection_memL2 {d : ℕ} {U : Set (Vec d)} {P : BlockVec d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    MemVectorL2 U (fun x => X.flux x - P.2) :=
  hX.2.2.1

theorem isSolenoidalZeroNormalTrace {d : ℕ} {U : Set (Vec d)} {P : BlockVec d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    IsSolenoidalZeroNormalTraceOn U (fun x => X.flux x - P.2) :=
  hX.2.2.2

end IsBlockMuAdmissible

noncomputable def blockEnergyDensity {d : ℕ} (a : CoeffField d) (X : BlockState d) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))

theorem blockEnergyDensity_ge_vecDot_of_isEllipticFieldOn {d : ℕ}
    {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (X : BlockState d) {x : Vec d} (hx : x ∈ U) :
    vecDot (X.potential x) (X.flux x) ≤ blockEnergyDensity a X x := by
  unfold blockEnergyDensity
  simpa [BlockState.eval] using!
    blockMatrixOfCoeff_half_quadratic_ge_vecDot_of_isEllipticMatrix
      (hEll.2 x hx) (X.potential x) (X.flux x)

theorem blockEnergyDensity_matTranspose_flipFlux {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (x : Vec d) :
    blockEnergyDensity (fun y => matTranspose (a y)) X.flipFlux x =
      blockEnergyDensity a X x := by
  unfold blockEnergyDensity blockCoeffField
  simpa [BlockState.eval_flipFlux] using!
    congrArg (fun t => (1 / 2 : ℝ) * t)
      (blockMatrixOfCoeff_quadratic_matTranspose_flipFlux
        (A := a x) (p := X.potential x) (q := X.flux x))

theorem blockEnergyDensity_mapMatrix_conj_of_transpose_eq_self_of_mul_self_eq_one {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (R : Mat d)
    (hR : matTranspose R = R) (hR2 : R * R = 1) (x : Vec d) :
    blockEnergyDensity (fun y => R * a y * R) (X.mapMatrix R) x =
      blockEnergyDensity a X x := by
  unfold blockEnergyDensity blockCoeffField
  simpa [BlockState.eval_mapMatrix, blockVecConj] using!
    congrArg (fun t => (1 / 2 : ℝ) * t)
      (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_conj_of_transpose_eq_self_of_mul_self_eq_one
        (R := R) (A := a x) hR hR2 (X := X.eval x))

theorem blockEnergyDensity_mapMatrix_signFlipMatrix_conj {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (i : Fin d) (x : Vec d) :
    blockEnergyDensity (fun y => signFlipMatrix i * a y * signFlipMatrix i)
      (X.mapMatrix (signFlipMatrix i)) x =
        blockEnergyDensity a X x := by
  exact blockEnergyDensity_mapMatrix_conj_of_transpose_eq_self_of_mul_self_eq_one
    (a := a) (X := X) (R := signFlipMatrix i)
    (matTranspose_signFlipMatrix i) (signFlipMatrix_mul_self i) x

theorem blockEnergyDensity_mapMatrix_swap_conj {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (i j : Fin d) (x : Vec d) :
    blockEnergyDensity (fun y => Matrix.swap ℝ i j * a y * Matrix.swap ℝ i j)
      (X.mapMatrix (Matrix.swap ℝ i j)) x =
        blockEnergyDensity a X x := by
  exact blockEnergyDensity_mapMatrix_conj_of_transpose_eq_self_of_mul_self_eq_one
    (a := a) (X := X) (R := Matrix.swap ℝ i j)
    (by simp [matTranspose])
    (Matrix.swap_mul_self (R := ℝ) i j) x


end Homogenization
