/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Block
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Multiscale Ellipticity -/

open scoped BigOperators

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Chapter 2.5 Multiscale Ellipticity Constants

This file locks the public definitions from Section 2.5 of the notes.  The
multiscale quantities are deliberately built from the Chapter 2 `CoeffOn`
interface on open cube domains, and the compatibility of a coefficient field
across nested cubes is recorded almost everywhere.
-/

noncomputable section

/-- The open realization of a triadic cube is a nonempty public Chapter 2
domain. -/
theorem openCubeSet_nonempty {d : ℕ} (Q : TriadicCube d) :
    (openCubeSet Q).Nonempty := by
  refine ⟨cubeCenter Q, ?_⟩
  rw [← ball_cubeCenter_eq_openCubeSet]
  simpa using Metric.mem_ball_self (x := cubeCenter Q) (cubeRadius_pos Q)

/-- The public Chapter 2 domain associated with an open triadic cube. -/
noncomputable def cubeDomain {d : ℕ} (Q : TriadicCube d) : Domain d where
  carrier := openCubeSet Q
  isDomain := isOpenBoundedConvexDomain_openCubeSet Q
  nonempty := openCubeSet_nonempty Q

@[simp] theorem cubeDomain_coe {d : ℕ} (Q : TriadicCube d) :
    ((cubeDomain Q : Domain d) : Set (Vec d)) = openCubeSet Q :=
  rfl

/-- A coefficient field on the triadic cube hierarchy.

For each open triadic cube it provides a `CoeffOn` object, hence ellipticity and
measurability are a.e. on that cube.  The `restrictsTo_of_subset` field says
that the representatives are compatible across nested cubes only modulo null
sets; this is the public replacement for old representative-level cube
restrictions. -/
structure TriadicCoeffFamily (d : ℕ) where
  coeffOn : (Q : TriadicCube d) → CoeffOn (cubeDomain Q)
  restrictsTo_of_subset :
    ∀ {Q R : TriadicCube d}, openCubeSet R ⊆ openCubeSet Q →
      CoeffOn.RestrictsTo (coeffOn Q) (coeffOn R)

namespace TriadicCoeffFamily

/-- Two triadic coefficient families are equal when their cube representatives
agree a.e. on every open triadic cube. -/
def AEEq {d : ℕ} (a b : TriadicCoeffFamily d) : Prop :=
  ∀ Q : TriadicCube d, CoeffOn.AEEq (a.coeffOn Q) (b.coeffOn Q)

theorem restrictsTo_self {d : ℕ} (a : TriadicCoeffFamily d) (Q : TriadicCube d) :
    CoeffOn.RestrictsTo (a.coeffOn Q) (a.coeffOn Q) :=
  a.restrictsTo_of_subset Set.Subset.rfl

/-- Compatibility of a triadic coefficient family with a descendant cube,
expressed a.e. on the descendant open cube. -/
theorem restrictsTo_descendant {d : ℕ} (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k) :
    CoeffOn.RestrictsTo (a.coeffOn Q) (a.coeffOn R) := by
  refine a.restrictsTo_of_subset ?_
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
  exact openCubeSet_subset_of_mem_descendantsAtDepth hR

namespace AEEq

theorem refl {d : ℕ} (a : TriadicCoeffFamily d) : AEEq a a :=
  fun Q => CoeffOn.AEEq.refl (a.coeffOn Q)

theorem symm {d : ℕ} {a b : TriadicCoeffFamily d} (h : AEEq a b) :
    AEEq b a :=
  fun Q => (h Q).symm

theorem trans {d : ℕ} {a b c : TriadicCoeffFamily d}
    (hab : AEEq a b) (hbc : AEEq b c) : AEEq a c :=
  fun Q => (hab Q).trans (hbc Q)

end AEEq

end TriadicCoeffFamily

/-- Exponents used in the multiscale ellipticity constants: finite `q` and the
endpoint `q = infinity`. -/
inductive MultiscaleExponent where
  | finite (value : ℝ)
  | infinity
deriving DecidableEq

namespace MultiscaleExponent

/-- Admissible exponents in the public Sec. 2.5 definitions: finite `q ≥ 1`
or the endpoint `q = infinity`. -/
def IsAdmissible : MultiscaleExponent → Prop
  | .finite q => 1 ≤ q
  | .infinity => True

@[simp] theorem isAdmissible_finite {q : ℝ} :
    IsAdmissible (.finite q) ↔ 1 ≤ q :=
  Iff.rfl

@[simp] theorem isAdmissible_infinity :
    IsAdmissible .infinity :=
  trivial

end MultiscaleExponent

/-- Legacy Frobenius-style squared matrix norm retained for compatibility with
older deterministic infrastructure. -/
def matrixNormSq {d : ℕ} (A : Mat d) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Euclidean/L2 operator norm used for `|b|` and `|sigma_*^{-1}|` in the
public Sec. 2.5 definitions. -/
noncomputable def matrixNorm {d : ℕ} (A : Mat d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

/-- Supremum of a real-valued function over a finite set.

The old deterministic files use the same `sSup` convention, which leaves the
definition total even when the finite set is empty. -/
noncomputable def finsetSupReal {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  sSup (f '' (↑s : Set α))

/-- The scale factor `3^{2s(m-k)}` appearing in one-cube descendant bounds. -/
noncomputable def multiscaleDescendantWeight {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (2 * s * (((Q.scale - k : ℤ) : ℝ)))

/-- One-cube norm `|b(Q; a)|`, where `b` is the canonical public coarse matrix
on the open cube. -/
noncomputable def coarseBMatrixNorm {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) : ℝ :=
  matrixNorm (bCoarse (cubeDomain Q) (a.coeffOn Q))

/-- One-cube norm `|sigma_*^{-1}(Q; a)|`, where `sigma_*^{-1}` is the canonical
public coarse matrix on the open cube. -/
noncomputable def coarseSigmaStarInvMatrixNorm {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) : ℝ :=
  matrixNorm (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q))

/-- The maximum of `|b(R; a)|` over descendants of `Q` at scale `k`. -/
noncomputable def maxDescendantBMatrixNormAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : TriadicCoeffFamily d) : ℝ :=
  finsetSupReal (descendantsAtScale Q k) fun R => coarseBMatrixNorm R a

/-- The maximum of `|sigma_*^{-1}(R; a)|` over descendants of `Q` at scale
`k`. -/
noncomputable def maxDescendantSigmaStarInvMatrixNormAtScale {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (a : TriadicCoeffFamily d) : ℝ :=
  finsetSupReal (descendantsAtScale Q k) fun R =>
    coarseSigmaStarInvMatrixNorm R a

/-- Geometric normalization `c_{s,q} = 1 - 3^{-s q}` for finite exponents. -/
noncomputable def geometricDiscount (s q : ℝ) : ℝ :=
  1 - Real.rpow (3 : ℝ) (-s * q)

/-- The finite-exponent geometric weight
`c_{s,q} 3^{-s q n}`. -/
noncomputable def geometricWeight (s q : ℝ) (n : ℕ) : ℝ :=
  geometricDiscount s q * Real.rpow (3 : ℝ) (-s * q * (n : ℝ))

/-- Finite-exponent coarse-grained upper ellipticity
`\Lambda_{s,q}(Q; a)`. -/
noncomputable def LambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : TriadicCoeffFamily d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow
          (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
    (2 / q)

/-- Finite-exponent coarse-grained lower ellipticity
`\lambda_{s,q}(Q; a)`. -/
noncomputable def lambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : TriadicCoeffFamily d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2))
    (-(2 / q))

/-- Endpoint coarse-grained upper ellipticity
`\Lambda_{s,\infty}(Q; a)`. -/
noncomputable def LambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : TriadicCoeffFamily d) : ℝ :=
  sSup
    { M : ℝ | ∃ n : ℕ,
        M =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a }

/-- Endpoint coarse-grained lower ellipticity
`\lambda_{s,\infty}(Q; a)`. -/
noncomputable def lambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : TriadicCoeffFamily d) : ℝ :=
  (sSup
    { M : ℝ | ∃ n : ℕ,
        M =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a })⁻¹

/-- Coarse-grained upper ellipticity for finite `q` and `q = infinity`. -/
noncomputable def LambdaSq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) (a : TriadicCoeffFamily d) : ℝ :=
  match q with
  | .finite q => LambdaSqFinite Q s q a
  | .infinity => LambdaSqInfinity Q s a

/-- Coarse-grained lower ellipticity for finite `q` and `q = infinity`. -/
noncomputable def lambdaSq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) (a : TriadicCoeffFamily d) : ℝ :=
  match q with
  | .finite q => lambdaSqFinite Q s q a
  | .infinity => lambdaSqInfinity Q s a

@[simp] theorem LambdaSq_finite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : TriadicCoeffFamily d) :
    LambdaSq Q s (.finite q) a = LambdaSqFinite Q s q a :=
  rfl

@[simp] theorem LambdaSq_infinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : TriadicCoeffFamily d) :
    LambdaSq Q s .infinity a = LambdaSqInfinity Q s a :=
  rfl

@[simp] theorem lambdaSq_finite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : TriadicCoeffFamily d) :
    lambdaSq Q s (.finite q) a = lambdaSqFinite Q s q a :=
  rfl

@[simp] theorem lambdaSq_infinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : TriadicCoeffFamily d) :
    lambdaSq Q s .infinity a = lambdaSqInfinity Q s a :=
  rfl

/-- The maximum of `\Lambda_{s,q}(R; a)` over descendants of `Q` at scale
`k`. -/
noncomputable def maxDescendantUpperEllipticityAtScale {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (s : ℝ) (q : MultiscaleExponent)
    (a : TriadicCoeffFamily d) : ℝ :=
  finsetSupReal (descendantsAtScale Q k) fun R => LambdaSq R s q a

/-- The maximum of `\lambda_{s,q}(R; a)^{-1}` over descendants of `Q` at scale
`k`. -/
noncomputable def maxDescendantLowerEllipticityInvAtScale {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (s : ℝ) (q : MultiscaleExponent)
    (a : TriadicCoeffFamily d) : ℝ :=
  finsetSupReal (descendantsAtScale Q k) fun R => (lambdaSq R s q a)⁻¹

/-- The default finite-exponent convention `q = 1` for `\Lambda_s`. -/
noncomputable def LambdaS {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : TriadicCoeffFamily d) : ℝ :=
  LambdaSq Q s (.finite 1) a

/-- The default finite-exponent convention `q = 1` for `\lambda_s`. -/
noncomputable def lambdaS {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : TriadicCoeffFamily d) : ℝ :=
  lambdaSq Q s (.finite 1) a

/-- Coarse-grained ellipticity ratio
`\Theta_{s,t}(Q; a) = \Lambda_{s,1}(Q; a) / \lambda_{t,1}(Q; a)`. -/
noncomputable def ThetaRatio {d : ℕ} (Q : TriadicCube d) (s t : ℝ)
    (a : TriadicCoeffFamily d) : ℝ :=
  LambdaS Q s a / lambdaS Q t a

end

end Ch02
end Book
end Homogenization
