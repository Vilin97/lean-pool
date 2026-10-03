/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCube
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Multiscale Quantities -/

@[expose] public section

open scoped BigOperators
open scoped MatrixOrder

namespace Homogenization

inductive MultiscaleExponent where
  | finite (value : ℝ)
  | infinity

def fullBlockVecNormSq {d : ℕ} (x : FullBlockVec d) : ℝ :=
  ∑ i, x i ^ 2

def matNormSq {d : ℕ} (A : Mat d) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

noncomputable def matNorm {d : ℕ} (A : Mat d) : ℝ :=
  Real.sqrt (matNormSq A)

noncomputable def finsetAverage {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  ((s.card : ℝ)⁻¹) * s.sum f

noncomputable def finsetSsup {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  sSup (f '' (↑s : Set α))

noncomputable def coarseBBlockNorm {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) : ℝ :=
  matNorm (coarseBlockMatrix (cubeSet Q) a).upperLeft

noncomputable def coarseSigmaStarInvBlockNorm {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) : ℝ :=
  matNorm (coarseBlockMatrix (cubeSet Q) a).lowerRight

noncomputable def maxDescendantBBlockNormAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : CoeffField d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => coarseBBlockNorm R a)

noncomputable def maxDescendantSigmaStarInvNormAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : CoeffField d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => coarseSigmaStarInvBlockNorm R a)

noncomputable def geometricDiscount (s q : ℝ) : ℝ :=
  1 - Real.rpow (3 : ℝ) (-s * q)

noncomputable def geometricWeight (s q : ℝ) (n : ℕ) : ℝ :=
  geometricDiscount s q * Real.rpow (3 : ℝ) (-s * q * (n : ℝ))

noncomputable def LambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : CoeffField d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
    (2 / q)

noncomputable def lambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : CoeffField d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
    (-2 / q)

noncomputable def LambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : CoeffField d) : ℝ :=
  sSup
    { m | ∃ n : ℕ,
        m =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a }

noncomputable def lambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : CoeffField d) : ℝ :=
  (sSup
    { m | ∃ n : ℕ,
        m =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a })⁻¹

noncomputable def LambdaSq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) (a : CoeffField d) : ℝ :=
  match q with
  | .finite q => LambdaSqFinite Q s q a
  | .infinity => LambdaSqInfinity Q s a

noncomputable def lambdaSq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) (a : CoeffField d) : ℝ :=
  match q with
  | .finite q => lambdaSqFinite Q s q a
  | .infinity => lambdaSqInfinity Q s a

/--
Deterministic cube-level contrast ratio `Λ_{s,1}(Q) / λ_{t,1}(Q)`.
This is not the annealed Chapter-5 sequence `Θ_n`.
-/
noncomputable def ThetaRatio {d : ℕ} (Q : TriadicCube d) (s t : ℝ)
    (a : CoeffField d) : ℝ :=
  LambdaSq Q s (.finite 1) a / lambdaSq Q t (.finite 1) a

noncomputable def constantFullBlockMatrix {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  toFullBlockMat (blockMatrixOfCoeff a0)

noncomputable def constantFullBlockMatrixSqrt {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  CFC.sqrt (constantFullBlockMatrix a0)

noncomputable def constantFullBlockMatrixInvSqrt {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  (constantFullBlockMatrixSqrt a0)⁻¹

noncomputable def normalizedBlockResponseValueSet {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) : Set ℝ :=
  { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
      m =
        BlockJ (cubeSet Q)
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
          a }

noncomputable def normalizedBlockResponseMax {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) : ℝ :=
  sSup (normalizedBlockResponseValueSet Q a a0)

noncomputable def maxDescendantNormalizedBlockResponseAtScale {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => normalizedBlockResponseMax R a a0)

noncomputable def scaleResponseAtScale {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    (p : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  match p with
  | .finite p =>
      Real.rpow
        (finsetAverage (descendantsAtScale Q k)
          (fun R => Real.rpow (normalizedBlockResponseMax R a a0) (p / 2)))
        (1 / p)
  | .infinity =>
      Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q k a a0) (1 / 2)

noncomputable def HomogenizationErrorFinite {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p : MultiscaleExponent) (q : ℝ) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  Real.rpow
    (∑' l : ℕ,
      geometricWeight s q l *
        Real.rpow (scaleResponseAtScale Q (n - (l : ℤ)) p a a0) q)
    (1 / q)

noncomputable def HomogenizationErrorInfinity {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  sSup
    { m | ∃ l : ℕ,
        m =
          Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            scaleResponseAtScale Q (n - (l : ℤ)) p a a0 }

noncomputable def HomogenizationError {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p q : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  match q with
  | .finite q => HomogenizationErrorFinite Q n s p q a a0
  | .infinity => HomogenizationErrorInfinity Q n s p a a0

noncomputable def HomogenizationErrorOnCube {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  HomogenizationError Q Q.scale s p q a a0

end Homogenization
