/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DiagonalOperator
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Convex.Majorization
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Symmetric gauges of square specializations

Diagonal evaluation and operator absolute value use endomorphisms. They specialize
the rectangular seminorm to identical domain and codomain; there is no square structure.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : ℕ}

namespace UnitarilyInvariantSeminorm

variable (N : UnitarilyInvariantSeminorm 𝕜 E E)

/-! ### The symmetric gauge -/

/-- The **symmetric gauge** of a unitarily invariant norm relative to an
orthonormal basis `b`: the norm of the diagonal operator with diagonal `x`.
Defined on *all* real vectors, not only sorted nonnegative ones — the
T-transform descent exploits its subadditivity, homogeneity, permutation
invariance, and single-coordinate sign invariance on arbitrary vectors. -/
noncomputable def gauge (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : ℝ :=
  N (diagOp b x)

/-- The induced vector gauge is subadditive, inherited from the norm through `diagOp_add`. -/
theorem gauge_add_le (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    N.gauge b (x + y) ≤ N.gauge b x + N.gauge b y := by
  rw [gauge, diagOp_add]
  exact N.add_le' _ _

/-- The induced vector gauge is absolutely homogeneous over `ℝ`. -/
theorem gauge_real_smul (b : OrthonormalBasis (Fin n) 𝕜 E) (c : ℝ)
    (x : Fin n → ℝ) : N.gauge b (c • x) = |c| * N.gauge b x := by
  rw [gauge, diagOp_real_smul, N.smul_eq, RCLike.norm_ofReal]
  rfl

/-- Permutation invariance of the gauge: conjugating the diagonal operator by
the basis-permutation unitary permutes the diagonal. -/
theorem gauge_perm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : N.gauge b (x ∘ π) = N.gauge b x := by
  have hconj : diagOp b (x ∘ π)
      = (b.equiv b π).symm.toLinearMap ∘ₗ diagOp b x
        ∘ₗ (b.equiv b π).toLinearMap := by
    refine b.toBasis.ext fun j => ?_
    change diagOp b (x ∘ π) (b j) =
      (b.equiv b π).symm (diagOp b x ((b.equiv b π) (b j)))
    simp only [OrthonormalBasis.equiv_apply_basis, diagOp_apply_basis,
      map_smul, Function.comp_apply]
    congr 1
    rw [← OrthonormalBasis.equiv_apply_basis b b π j,
      LinearIsometryEquiv.symm_apply_apply]
  rw [gauge, hconj, N.invariant]
  rfl

/-- Single-coordinate sign flip invariance of the gauge: flipping the sign of
the `j`-th diagonal entry composes the diagonal operator with the reflection
through `(𝕜 ∙ b j)ᗮ`, a unitary. -/
theorem gauge_neg_single (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (j : Fin n) :
    N.gauge b (Function.update x j (-(x j))) = N.gauge b x := by
  have hcomp : diagOp b (Function.update x j (-(x j)))
      = diagOp b x ∘ₗ ((𝕜 ∙ b j)ᗮ).reflection.toLinearMap := by
    refine b.toBasis.ext fun i => ?_
    change diagOp b (Function.update x j (-(x j))) (b i) =
      diagOp b x (((𝕜 ∙ b j)ᗮ).reflection (b i))
    rcases eq_or_ne i j with rfl | hij
    · simp only [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
        map_neg, diagOp_apply_basis, Function.update_self, neg_smul]
    · have hmem : b i ∈ (𝕜 ∙ b j)ᗮ :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
          (b.orthonormal.2 (Ne.symm hij))
      rw [Submodule.reflection_mem_subspace_eq_self hmem, diagOp_apply_basis,
        diagOp_apply_basis, Function.update_of_ne hij]
  rw [gauge, hcomp, N.invariant_right]
  rfl

/-- **The gauge representation**: a unitarily invariant norm is the gauge of
the singular values, via the operator SVD. -/
theorem apply_eq_gauge (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E) :
    N A = N.gauge b fun i => A.singularValues (i : ℕ) := by
  obtain ⟨U, V, hUV⟩ := exists_unitary_diagOp_factorization hn b A
  conv_lhs => rw [hUV]
  exact N.invariant U V _

/-! ### Monotonicity of the gauge -/

/-- The gauge of a unitarily invariant norm, packaged as a `FiniteSymmetricGauge`.  Its four
fields are exactly `gauge_add_le`, `gauge_real_smul`, `gauge_perm` and `gauge_neg_single`,
which is what makes the Hardy--Littlewood--Pólya transfer theory
(`ForTauCeti.Analysis.Convex.Majorization`) apply verbatim: everything below is that theory
read through this packaging, not a second proof of it. -/
noncomputable def finiteSymmetricGauge (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) : FiniteSymmetricGauge n where
  toFun := N.gauge b
  add_le' := N.gauge_add_le b
  real_smul' := N.gauge_real_smul b
  perm' := N.gauge_perm b
  neg_single' := N.gauge_neg_single b

/-- The induced finite symmetric gauge, unfolded. -/
@[simp] theorem finiteSymmetricGauge_apply (b : OrthonormalBasis (Fin n) 𝕜 E)
    (x : Fin n → ℝ) : N.finiteSymmetricGauge b x = N.gauge b x := (rfl)

/-- Shrinking one coordinate of `y` (in absolute value) does not increase the
gauge: `update y j t` with `|t| ≤ y j` is a convex combination of `y` and its
`j`-th sign flip. -/
theorem gauge_update_le (b : OrthonormalBasis (Fin n) 𝕜 E) {y : Fin n → ℝ}
    {j : Fin n} {t : ℝ} (ht : |t| ≤ y j) :
    N.gauge b (Function.update y j t) ≤ N.gauge b y :=
  (N.finiteSymmetricGauge b).update_le ht

/-- **Coordinatewise monotonicity of the gauge** on nonnegative vectors. -/
theorem gauge_mono (b : OrthonormalBasis (Fin n) 𝕜 E) {x y : Fin n → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    N.gauge b x ≤ N.gauge b y :=
  (N.finiteSymmetricGauge b).mono hx0 hxy

/-! ### The T-transform descent -/

/-- **The T-transform descent on the gauge** — the engine of Fan dominance.
If `z` is antitone and nonnegative, `y` is nonnegative, and every prefix sum
of `z` is dominated by the corresponding prefix sum of `y`, then
`Φ_N(z) ≤ Φ_N(y)`.

No total-sum equality is assumed, no majorization completion and no
separation theorem is used: this is
`TauCeti.FiniteSymmetricGauge.le_of_prefixSum_le`, whose descent averages `y` with a
transposition of itself, at a cost of one triangle inequality, one homogeneity, and one
swap invariance of the gauge per step. -/
theorem gauge_le_gauge_of_prefix_sums_le (b : OrthonormalBasis (Fin n) 𝕜 E)
    {z y : Fin n → ℝ} (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y i) :
    N.gauge b z ≤ N.gauge b y :=
  (N.finiteSymmetricGauge b).le_of_prefixSum_le hz_anti hz0 hy0 hpre

/-! ### The Fan dominance principle -/


/-- A square seminorm is unchanged by taking the adjoint. -/
theorem apply_adjoint (A : E →ₗ[𝕜] E) : N A.adjoint = N A :=
  N.eq_of_same_singularValues (LinearMap.singularValues_adjoint A)

/-- A square seminorm is unchanged by taking the operator absolute value. -/
theorem apply_operatorAbs (A : E →ₗ[𝕜] E) : N (operatorAbs A) = N A := by
  conv_rhs => rw [polar_decomposition_choosePolarUnitary A]
  exact (N.invariant_left (choosePolarUnitary A) (operatorAbs A)).symm


end UnitarilyInvariantSeminorm

end TauCeti
