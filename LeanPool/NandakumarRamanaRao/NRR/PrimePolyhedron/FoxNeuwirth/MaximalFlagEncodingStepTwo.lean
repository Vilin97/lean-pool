/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagClassification
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagSourceCancellation
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Step 2: the maximal-flag determinant sign

For an explicitly coded maximal flag, the successive bar-removal matrix is the permutation
matrix of the inverse removal permutation.  Its determinant is therefore the sign of the removal
permutation.  Together with the bottom-cell permutation orientation, this identifies the
subdivision coefficient with `MaximalFlagCode.coefficient`.

Combining this identity with the bijection proved in Step 1 constructs `CompleteEncoding`, closes
the rank-two cancellation theorem, and proves that the top-flag subdivision chain is a genuine
mod-`p` simplicial cycle.
-/

@[expose] public section

namespace NRR

variable {p : Nat}

namespace FoxNeuwirthOrderComplex
namespace MaximalFlagCode

open TopFlagSubdivision

@[simp] theorem stageIndex_castSucc_val
    (hp : Nat.Prime p) (k : Fin (p - 1)) :
    (stageIndex hp k.castSucc).1 = k.1 :=
  rfl

@[simp] theorem stageIndex_succ_val
    (hp : Nat.Prime p) (k : Fin (p - 1)) :
    (stageIndex hp k.succ).1 = k.1 + 1 :=
  rfl

/-- One successive bar difference is the Kronecker coefficient recording the removed bar. -/
theorem barDifferenceMatrix_toSimplex_apply
    (hp : Nat.Prime p) (z : Code p) (r k : Fin (p - 1)) :
    barDifferenceMatrix (toSimplex hp z) r k =
      (Equiv.Perm.permMatrix Int z.removal.symm) r k := by
  classical
  simp only [barDifferenceMatrix, toSimplex_apply, stageCell,
    barIndicator, mem_retainedBars_iff, stageIndex_castSucc_val,
    stageIndex_succ_val, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  by_cases h : z.removal.symm r = k
  · subst h
    simp
  · have hkne : ¬ k = z.removal.symm r := fun hh => h hh.symm
    have hvne : (k : ℕ) ≠ (z.removal.symm r : ℕ) := fun hh => hkne (Fin.ext hh)
    rw [ite_eq_right hkne]
    rcases Nat.lt_or_ge (k : ℕ) (z.removal.symm r : ℕ) with hlt | hge
    · rw [ite_eq_left (le_of_lt hlt), ite_eq_left (by omega)]
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      ring

/-- The complete bar-removal matrix is the inverse-removal permutation matrix. -/
theorem barDifferenceMatrix_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    barDifferenceMatrix (toSimplex hp z) =
      Equiv.Perm.permMatrix Int z.removal.symm := by
  ext r k
  exact barDifferenceMatrix_toSimplex_apply hp z r k

/-- The bar-removal determinant is the sign of the removal permutation. -/
theorem barRemovalDeterminant_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    barRemovalDeterminant (toSimplex hp z) = permSignInt z.removal := by
  unfold barRemovalDeterminant permSignInt
  rw [barDifferenceMatrix_toSimplex hp z, Matrix.det_permutation]
  simp

/-- The determinant subdivision coefficient agrees with the explicit code coefficient. -/
theorem integralCoefficient_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    integralCoefficient (toSimplex hp z) = coefficient z := by
  unfold integralCoefficient coefficient permutationOrientationSign
  rw [barRemovalDeterminant_toSimplex hp z]
  congr 1
  have hzero : (toSimplex hp z 0).rank = z.bottom := by
    change stageRank z (stageIndex hp 0) = z.bottom
    have hindex : stageIndex hp 0 = firstStage hp := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact stageRank_zero hp z
  exact congrArg
    (fun sigma : Equiv.Perm (Fin p) => ((Equiv.Perm.sign sigma : ℤˣ) : ℤ)) hzero

/-- Step 1 plus the determinant calculation gives the complete maximal-flag encoding. -/
theorem completeEncoding (hp : Nat.Prime p) : CompleteEncoding hp where
  bijective_toSimplex := toSimplex_bijective hp
  coefficient_eq := integralCoefficient_toSimplex hp

/-- The internal rank-two source sums vanish for the actual simplicial chain. -/
theorem rankTwoCancellation : TopFlagSubdivision.RankTwoCancellationTheorem :=
  rankTwoCancellation_of_completeEncoding completeEncoding

/-- The top-flag subdivision is an unconditional mod-`p` simplicial cycle. -/
theorem topFlagCycle :
    ∀ {p : Nat} (hp : Nat.Prime p), TopFlagSubdivision.boundary hp = 0 :=
  topFlagCycle_of_completeEncoding completeEncoding

end MaximalFlagCode
end FoxNeuwirthOrderComplex

namespace AAK

/-- The best next move after maximal-flag classification: identify the determinant sign and close
all finite-combinatorial S3 obligations. -/
theorem simplestRoute_topFlagCycle_complete :
    ∀ {p : Nat} (hp : Nat.Prime p),
      FoxNeuwirthOrderComplex.TopFlagSubdivision.boundary hp = 0 :=
  FoxNeuwirthOrderComplex.MaximalFlagCode.topFlagCycle

end AAK

end NRR
