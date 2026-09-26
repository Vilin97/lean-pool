/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Majorization

/-!
# Orthogonal block sums of rectangular maps

The block-diagonal sum of two maps, its singular values and Ky Fan sums, and the
majorization statements that transfer to it.

## Provenance

Adapted from the rectangular majorization and block-sum modules in the Davis--Kahan/DKPS
formalization (Kitware, Inc.). The vector majorization descent remains in
`ForTauCeti.Analysis.Convex.Majorization`.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

namespace UnitarilyInvariantSeminorm

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/- `Module ℝ (E →ₗ[𝕜] F)` is a *local* instance in `Basic`, so it does not survive the
import.  Re-enable it here; making it global would put a second `Module ℝ` structure on
every `𝕜`-linear map space, which is why it is local in the first place. -/
attribute [local instance] realModuleLinearMap


/-- Orthogonal block sum of two rectangular maps on Hilbert `L²` products.

The construction is the linear lift of `LinearMap.prodMap`; it sends
`(x₁,x₂)` to `(A x₁,B x₂)`.  It is used to assemble the two directed sine
blocks without a triangle inequality and therefore without losing the sharp
constant. -/
@[expose]
noncomputable def orthogonalBlockSum
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂) :
    WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (F₁ × F₂) :=
  LinearMap.withLpMap 2 (A.prodMap B)

/-- The block sum acts componentwise: `A` on the first summand, `B` on the
second. -/
@[simp] theorem orthogonalBlockSum_apply
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂)
    (x : WithLp 2 (E₁ × E₂)) :
    orthogonalBlockSum A B x = WithLp.toLp 2 (A x.fst, B x.snd) :=
  (rfl)

/-- Scaling one block scales the block sum. -/
@[simp] theorem orthogonalBlockSum_smul
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (a : 𝕜) (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂) :
    orthogonalBlockSum (a • A) (a • B) =
      a • orthogonalBlockSum A B := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [orthogonalBlockSum]

/-- Subtraction of compatible orthogonal block sums is blockwise. -/
@[simp] theorem orthogonalBlockSum_sub
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (A C : E₁ →ₗ[𝕜] F₁) (B D : E₂ →ₗ[𝕜] F₂) :
    orthogonalBlockSum (A - C) (B - D) =
      orthogonalBlockSum A B - orthogonalBlockSum C D := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [orthogonalBlockSum_apply]

/-- **Doubling a map onto the diagonal of a block sum, as a linear map.**
`A ↦ A ⊕ A`.

Linear because `orthogonalBlockSum` is additive and homogeneous in each
argument separately.  Stated as a definition because it was built twice inside
proofs — as a `let` with its `map_add'` and `map_smul'` obligations discharged
inline, twelve identical lines each time, in the two
`finiteUnitaryOrbitCertificate_orthogonalBlockSum_of_*` theorems.  Nothing about
it depends on the certificate machinery those proofs are doing. -/
@[expose]
noncomputable def orthogonalBlockSumDiagonal
    {E₁ F₁ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] :
    (E₁ →ₗ[𝕜] F₁) →ₗ[𝕜] (WithLp 2 (E₁ × E₁) →ₗ[𝕜] WithLp 2 (F₁ × F₁)) where
  toFun A := orthogonalBlockSum A A
  map_add' A B := by
    ext x
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp [orthogonalBlockSum_apply]
  map_smul' r A := orthogonalBlockSum_smul r A A

/-- The adjoint of an orthogonal block sum is the block sum of the adjoints. -/
@[simp] theorem orthogonalBlockSum_adjoint
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂) :
    (orthogonalBlockSum A B).adjoint =
      orthogonalBlockSum A.adjoint B.adjoint := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [orthogonalBlockSum_apply, WithLp.prod_inner_apply,
    LinearMap.adjoint_inner_left]
  rfl

/-- Symmetry of square operators is preserved by orthogonal block sum. -/
theorem orthogonalBlockSum_isSymmetric
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    {A : E₁ →ₗ[𝕜] E₁} {B : E₂ →ₗ[𝕜] E₂}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (orthogonalBlockSum A B).IsSymmetric := by
  intro x y
  simp only [orthogonalBlockSum_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_fst, WithLp.ofLp_snd]
  rw [hA x.fst y.fst, hB x.snd y.snd]

/-- Positivity of square operators is preserved by orthogonal block sum. -/
theorem orthogonalBlockSum_isPositive
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    {A : E₁ →ₗ[𝕜] E₁} {B : E₂ →ₗ[𝕜] E₂}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    (orthogonalBlockSum A B).IsPositive := by
  refine ⟨orthogonalBlockSum_isSymmetric hA.isSymmetric hB.isSymmetric, ?_⟩
  intro x
  rw [orthogonalBlockSum_apply, WithLp.prod_inner_apply]
  have hsum :
      0 ≤ RCLike.re ⟪A x.fst, x.fst⟫_𝕜 + RCLike.re ⟪B x.snd, x.snd⟫_𝕜 :=
    add_nonneg (hA.re_inner_nonneg_left x.fst) (hB.re_inner_nonneg_left x.snd)
  simpa only [WithLp.ofLp_fst, WithLp.ofLp_snd, map_add] using hsum

/-- Composition of compatible orthogonal block sums is blockwise. -/
@[simp] theorem orthogonalBlockSum_comp
    {E₁ E₂ F₁ F₂ G₁ G₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    [NormedAddCommGroup G₁] [InnerProductSpace 𝕜 G₁]
    [NormedAddCommGroup G₂] [InnerProductSpace 𝕜 G₂]
    (A : F₁ →ₗ[𝕜] G₁) (B : F₂ →ₗ[𝕜] G₂)
    (C : E₁ →ₗ[𝕜] F₁) (D : E₂ →ₗ[𝕜] F₂) :
    orthogonalBlockSum A B ∘ₗ orthogonalBlockSum C D =
      orthogonalBlockSum (A ∘ₗ C) (B ∘ₗ D) := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [orthogonalBlockSum, LinearMap.comp_apply]

/-- The operator modulus of a block-diagonal map is block-diagonal. -/
theorem operatorAbs_orthogonalBlockSum
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    operatorAbs (orthogonalBlockSum A B) =
      orthogonalBlockSum (operatorAbs A) (operatorAbs B) := by
  symm
  change orthogonalBlockSum (operatorAbs A) (operatorAbs B) =
    (LinearMap.isPositive_adjoint_comp_self (orthogonalBlockSum A B)).sqrt
  refine (LinearMap.isPositive_adjoint_comp_self (orthogonalBlockSum A B)).sqrt_unique
    (orthogonalBlockSum_isPositive (isPositive_operatorAbs A) (isPositive_operatorAbs B)) ?_
  rw [orthogonalBlockSum_comp, operatorAbs_mul_self, operatorAbs_mul_self,
    orthogonalBlockSum_adjoint, orthogonalBlockSum_comp]

/-- The orthogonal block sum of two unitaries is the `L²` product unitary.  This is what makes
the block sum compatible with the two-sided unitary invariance the singular-value calculus
rests on. -/
theorem orthogonalBlockSum_linearIsometryEquiv
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (U : E₁ ≃ₗᵢ[𝕜] F₁) (V : E₂ ≃ₗᵢ[𝕜] F₂) :
    orthogonalBlockSum U.toLinearMap V.toLinearMap =
      (LinearIsometryEquiv.withLpProdCongr 2 U V).toLinearMap := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [orthogonalBlockSum]

/-- **The orthogonal block sum of two subspaces**, as a submodule of the Hilbert `L²` product.

This is the subspace-level partner of `orthogonalBlockSum`.  Without it a direct-sum statement
is a statement about a block matrix; with it -- through
`starProjection_orthogonalBlockSumSubmodule` -- it becomes a statement about an actual pair of
subspaces of `WithLp 2 (E₁ × E₂)`. -/
noncomputable def orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂) :
    Submodule 𝕜 (WithLp 2 (E₁ × E₂)) :=
  (U₁.prod U₂).comap (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).toLinearMap

/-- Membership in the block sum of two subspaces is blockwise. -/
@[simp] theorem mem_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    {U₁ : Submodule 𝕜 E₁} {U₂ : Submodule 𝕜 E₂} {x : WithLp 2 (E₁ × E₂)} :
    x ∈ orthogonalBlockSumSubmodule U₁ U₂ ↔ x.fst ∈ U₁ ∧ x.snd ∈ U₂ := Iff.rfl

/-- **The orthogonal projector onto a block sum of subspaces is the block sum of the
projectors.**

This is the bookkeeping that turns the direct-sum equality theorems -- which are stated on
`orthogonalBlockSum` of two plane angle operators -- into statements about the pair of
subspaces `U₁ ⊞ U₂` and `V₁ ⊞ V₂`.  Iteration to `m` blocks composes this lemma and is left to
the consumer. -/
theorem starProjection_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂) :
    (((orthogonalBlockSumSubmodule U₁ U₂).starProjection :
        WithLp 2 (E₁ × E₂) →L[𝕜] WithLp 2 (E₁ × E₂)) :
        WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (E₁ × E₂)) =
      orthogonalBlockSum ((U₁.starProjection : E₁ →L[𝕜] E₁) : E₁ →ₗ[𝕜] E₁)
        ((U₂.starProjection : E₂ →L[𝕜] E₂) : E₂ →ₗ[𝕜] E₂) := by
  refine LinearMap.ext fun x => ?_
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [mem_orthogonalBlockSumSubmodule]
    exact ⟨U₁.starProjection_apply_mem _, U₂.starProjection_apply_mem _⟩
  · intro y hy
    rw [mem_orthogonalBlockSumSubmodule] at hy
    rw [WithLp.prod_inner_apply]
    have h₁ := Submodule.starProjection_inner_eq_zero (K := U₁)
      (WithLp.ofLp x).1 (WithLp.ofLp y).1 hy.1
    have h₂ := Submodule.starProjection_inner_eq_zero (K := U₂)
      (WithLp.ofLp x).2 (WithLp.ofLp y).2 hy.2
    change ⟪(WithLp.ofLp x).1 - U₁.starProjection (WithLp.ofLp x).1,
        (WithLp.ofLp y).1⟫_𝕜 +
      ⟪(WithLp.ofLp x).2 - U₂.starProjection (WithLp.ofLp x).2,
        (WithLp.ofLp y).2⟫_𝕜 = 0
    rw [h₁, h₂, add_zero]

/-- **Blockwise singular-value data determines the singular-value data of the block sum.**

No merge formula for the two sorted lists is needed: equal singular values in a block mean the
two blocks differ by unitaries on each side
(`exists_unitary_factorization_of_singularValues_eq`), and the block sums of those unitaries are
again unitaries, which the singular values do not see.  This is the concatenation fact the
finite direct-sum extremal constructions use, in the only form they need. -/
theorem singularValues_orthogonalBlockSum_congr
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    {A₁ A₂ : E₁ →ₗ[𝕜] F₁} {B₁ B₂ : E₂ →ₗ[𝕜] F₂}
    (hA : A₁.singularValues = A₂.singularValues)
    (hB : B₁.singularValues = B₂.singularValues) :
    (orthogonalBlockSum A₁ B₁).singularValues =
      (orthogonalBlockSum A₂ B₂).singularValues := by
  obtain ⟨UA, VA, hA'⟩ := exists_unitary_factorization_of_singularValues_eq hA
  obtain ⟨UB, VB, hB'⟩ := exists_unitary_factorization_of_singularValues_eq hB
  rw [hA', hB', ← orthogonalBlockSum_comp, ← orthogonalBlockSum_comp,
    orthogonalBlockSum_linearIsometryEquiv, orthogonalBlockSum_linearIsometryEquiv,
    singularValues_unitary_comp, singularValues_comp_unitary]

/-- **A blockwise scalar singular-value identity transfers to every unitarily invariant
seminorm on the block sum.**

If the singular values of `c • Sⱼ` are those of `Pⱼ` in each block, then `c • (S₁ ⊕ S₂)` and
`P₁ ⊕ P₂` have the same singular values, so every unitarily invariant seminorm sees the same
proportionality.  This is the mechanism by which finite orthogonal direct sums of planar
extremizers keep attaining equality at every unitarily invariant seminorm at once. -/
theorem apply_orthogonalBlockSum_eq_of_singularValues_smul_eq
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)))
    {c : ℝ} (hc : 0 ≤ c)
    {S₁ P₁ : E₁ →ₗ[𝕜] E₁} {S₂ P₂ : E₂ →ₗ[𝕜] E₂}
    (h₁ : ((c : 𝕜) • S₁).singularValues = P₁.singularValues)
    (h₂ : ((c : 𝕜) • S₂).singularValues = P₂.singularValues) :
    c * N (orthogonalBlockSum S₁ S₂) = N (orthogonalBlockSum P₁ P₂) := by
  have hblock := singularValues_orthogonalBlockSum_congr h₁ h₂
  rw [orthogonalBlockSum_smul] at hblock
  calc
    c * N (orthogonalBlockSum S₁ S₂)
        = N ((c : 𝕜) • orthogonalBlockSum S₁ S₂) := by
          rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc]
    _ = N (orthogonalBlockSum P₁ P₂) := N.eq_of_same_singularValues hblock

/-- Doubling a rectangular map in an orthogonal block sum repeats every
singular value twice.  The quotient `i / 2` expresses the interleaved sorted
order of the two identical copies. -/
theorem singularValues_orthogonalBlockSum_self
    {E₀ F₀ : Type*}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 E₀] [FiniteDimensional 𝕜 F₀]
    (A : E₀ →ₗ[𝕜] F₀) (i : ℕ) :
    (orthogonalBlockSum A A).singularValues i = A.singularValues (i / 2) := by
  classical
  let n := finrank 𝕜 E₀
  have hn : finrank 𝕜 (WithLp 2 (E₀ × E₀)) = n * 2 := by
    calc
      finrank 𝕜 (WithLp 2 (E₀ × E₀)) = finrank 𝕜 (E₀ × E₀) :=
        (WithLp.linearEquiv 2 𝕜 (E₀ × E₀)).finrank_eq
      _ = n + n := by simp [n, Module.finrank_prod]
      _ = n * 2 := by omega
  rcases lt_or_ge i (n * 2) with hi | hi
  · let S : E₀ →ₗ[𝕜] E₀ := A.adjoint ∘ₗ A
    let hS : S.IsSymmetric := A.isSymmetric_adjoint_comp_self
    let b : OrthonormalBasis (Fin n) 𝕜 E₀ := hS.eigenvectorBasis rfl
    let pairToSum : Fin n × Fin 2 ≃ Fin n ⊕ Fin n :=
      (Equiv.prodComm (Fin n) (Fin 2)).trans <|
        (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin n))).trans <|
          Equiv.boolProdEquivSum (Fin n)
    let e : (Fin n ⊕ Fin n) ≃ Fin (n * 2) :=
      pairToSum.symm.trans finProdFinEquiv
    let b₂ : OrthonormalBasis (Fin (n * 2)) 𝕜 (WithLp 2 (E₀ × E₀)) :=
      (b.prod b).reindex e
    let μ : Fin (n * 2) → ℝ := fun j =>
      hS.eigenvalues rfl (finProdFinEquiv.symm j).1
    have hμ : Antitone μ := by
      intro j k hjk
      apply hS.eigenvalues_antitone
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change j.val / 2 ≤ k.val / 2
      exact Nat.div_le_div_right (Fin.le_def.mp hjk)
    have hgram :
        (orthogonalBlockSum A A).adjoint ∘ₗ orthogonalBlockSum A A =
          orthogonalBlockSum S S := by
      simp only [orthogonalBlockSum_adjoint, orthogonalBlockSum_comp, S]
    have heigen :
        (orthogonalBlockSum A A).isSymmetric_adjoint_comp_self.eigenvalues hn = μ := by
      apply LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ hn b₂ hμ
      intro j
      rw [hgram]
      simp only [b₂, OrthonormalBasis.reindex_apply]
      obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective j
      fin_cases r
      · simp only [finTwoEquiv, Fin.isValue, Equiv.symm_trans, Equiv.prodCongr_symm,
          Equiv.symm_mk, Equiv.refl_symm, Equiv.prodComm_symm, Equiv.symm_symm, Fin.zero_eta,
          Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
          Equiv.prodCongr_apply, Equiv.coe_fn_mk, Equiv.coe_refl, Prod.map_apply, Fin.reduceBEq,
          id_eq, Equiv.boolProdEquivSum_apply, Bool.false_eq_true, ↓reduceIte,
          OrthonormalBasis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inl,
          Function.comp_apply, orthogonalBlockSum_apply, WithLp.toLp_fst,
          hS.apply_eigenvectorBasis, WithLp.toLp_snd, map_zero,
          finProdFinEquiv_symm_apply, S, b, e, pairToSum, μ]
        have hidx : (finProdFinEquiv (q, (0 : Fin 2))).divNat = q :=
          congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (q, (0 : Fin 2)))
        rw [hidx]
        apply WithLp.ofLp_injective 2
        simp
      · simp only [finTwoEquiv, Fin.isValue, Equiv.symm_trans, Equiv.prodCongr_symm,
          Equiv.symm_mk, Equiv.refl_symm, Equiv.prodComm_symm, Equiv.symm_symm, Fin.mk_one,
          Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
          Equiv.prodCongr_apply, Equiv.coe_fn_mk, Equiv.coe_refl, Prod.map_apply, BEq.rfl, id_eq,
          Equiv.boolProdEquivSum_apply, ↓reduceIte, OrthonormalBasis.prod_apply, LinearMap.coe_inl,
          LinearMap.coe_inr, Sum.elim_inr, Function.comp_apply, orthogonalBlockSum_apply,
          WithLp.toLp_fst, map_zero, WithLp.toLp_snd,
          hS.apply_eigenvectorBasis, finProdFinEquiv_symm_apply, S, b, e, pairToSum, μ]
        have hidx : (finProdFinEquiv (q, (1 : Fin 2))).divNat = q :=
          congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (q, (1 : Fin 2)))
        rw [hidx]
        apply WithLp.ofLp_injective 2
        simp
    rw [(orthogonalBlockSum A A).singularValues_of_lt hn hi,
      congrFun heigen ⟨i, hi⟩]
    have hdiv : i / 2 < n := (Nat.div_lt_iff_lt_mul (by omega)).2 hi
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change √(A.isSymmetric_adjoint_comp_self.eigenvalues rfl
      ⟨i / 2, hdiv⟩) = A.singularValues (i / 2)
    rw [A.singularValues_of_lt rfl hdiv]
  · rw [(orthogonalBlockSum A A).singularValues_of_finrank_le (hn.symm ▸ hi)]
    have hdiv : n ≤ i / 2 := (Nat.le_div_iff_mul_le (by omega)).2 (by
      simpa [two_mul] using hi)
    rw [A.singularValues_of_finrank_le hdiv]

/-- Every Ky Fan prefix doubles on the orthogonal sum of two identical maps. -/
theorem kyFanSum_orthogonalBlockSum_self
    {E₀ F₀ : Type*}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 E₀] [FiniteDimensional 𝕜 F₀]
    (A : E₀ →ₗ[𝕜] F₀) (k : ℕ) :
    kyFanSum (2 * k) (orthogonalBlockSum A A) =
      2 * kyFanSum k A := by
  classical
  let e : Fin k × Fin 2 ≃ Fin (2 * k) :=
    finProdFinEquiv.trans (finCongr (by omega))
  unfold kyFanSum
  calc
    ∑ j : Fin (2 * k), (orthogonalBlockSum A A).singularValues (j : ℕ) =
        ∑ p : Fin k × Fin 2,
          (orthogonalBlockSum A A).singularValues (e p : ℕ) := by
      exact (e.sum_comp fun j => (orthogonalBlockSum A A).singularValues (j : ℕ)).symm
    _ = ∑ p : Fin k × Fin 2, A.singularValues (p.1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [singularValues_orthogonalBlockSum_self]
      congr 1
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change (p.2.val + 2 * p.1.val) / 2 = p.1.val
      omega
    _ = ∑ i : Fin k, ∑ _r : Fin 2, A.singularValues (i : ℕ) := by
      rw [Fintype.sum_prod_type]
    _ = 2 * ∑ i : Fin k, A.singularValues (i : ℕ) := by
      simp only [Fin.sum_univ_two]
      rw [Finset.sum_add_distrib]
      ring

/-- The restricted real action on `𝕜`-linear maps is scalar multiplication by the coerced
real.  Immediate from `realModuleLinearMap = Module.compHom _ (algebraMap ℝ 𝕜)`, but it is
needed at three different pairs of spaces in the proof below — the two summands and the
block — so it is stated once here rather than three times there. -/
private theorem real_smul_linearMap_eq {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (r : ℝ) (T : X →ₗ[𝕜] Y) : r • T = ((r : 𝕜)) • T := by
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change (algebraMap ℝ 𝕜 r) • T = ((r : 𝕜)) • T
  rfl

/-- Real orbit-convex domination is stable under orthogonal block sums.

This is the sharp coupling seam needed by the symmetric projector theorem:
it combines two one-sided sine estimates without adding their norms. -/
theorem orthogonalBlockSum_mem_convexHull_twoSidedUnitaryOrbit
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
     
     
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : A ∈ convexHull ℝ (twoSidedUnitaryOrbit C))
    (hB : B ∈ convexHull ℝ (twoSidedUnitaryOrbit D)) :
    orthogonalBlockSum A B ∈
      convexHull ℝ (twoSidedUnitaryOrbit (orthogonalBlockSum C D)) := by
  classical
  rcases mem_convexHull_iff_exists_fintype.mp hA with
    ⟨ι, instι, w, z, hw, hwsum, hz, hzsum⟩
  rcases mem_convexHull_iff_exists_fintype.mp hB with
    ⟨κ, instκ, v, t, hv, hvsum, ht, htsum⟩
  let : Fintype ι := instι
  let : Fintype κ := instκ
  refine mem_convexHull_iff_exists_fintype.mpr
    ⟨ι × κ, inferInstance, (fun p => w p.1 * v p.2),
      (fun p => orthogonalBlockSum (z p.1) (t p.2)), ?_, ?_, ?_, ?_⟩
  · intro p
    exact mul_nonneg (hw p.1) (hv p.2)
  · rw [Fintype.sum_prod_type]
    calc
      ∑ i, ∑ j, w i * v j = ∑ i, w i * ∑ j, v j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i, w i := by simp [hvsum]
      _ = 1 := hwsum
  · intro p
    rcases hz p.1 with ⟨U₁, V₁, hp₁⟩
    rcases ht p.2 with ⟨U₂, V₂, hp₂⟩
    refine ⟨LinearIsometryEquiv.withLpProdCongr 2 U₁ U₂,
      LinearIsometryEquiv.withLpProdCongr 2 V₁ V₂, ?_⟩
    ext x
    all_goals simp [orthogonalBlockSum, hp₁, hp₂, LinearMap.comp_apply]
  · have hfirst :
        (∑ p : ι × κ, (w p.1 * v p.2) • z p.1) = A := by
      rw [Fintype.sum_prod_type]
      calc
        ∑ i, ∑ j, (w i * v j) • z i =
            ∑ i, w i • z i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_smul, ← Finset.mul_sum, hvsum, mul_one]
        _ = A := hzsum
    have hsecond :
        (∑ p : ι × κ, (w p.1 * v p.2) • t p.2) = B := by
      rw [Fintype.sum_prod_type]
      calc
        ∑ i, ∑ j, (w i * v j) • t j =
            ∑ j, v j • t j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_smul, ← Finset.sum_mul, hwsum, one_mul]
        _ = B := htsum
    have hfirst' :
        (∑ p : ι × κ, (((w p.1 * v p.2 : ℝ) : 𝕜)) • z p.1) = A := by
      calc
        ∑ p : ι × κ, (((w p.1 * v p.2 : ℝ) : 𝕜)) • z p.1 =
            ∑ p : ι × κ, (w p.1 * v p.2) • z p.1 := by
          apply Finset.sum_congr rfl
          intro p _
          exact (real_smul_linearMap_eq (w p.1 * v p.2) (z p.1)).symm
        _ = A := hfirst
    have hsecond' :
        (∑ p : ι × κ, (((w p.1 * v p.2 : ℝ) : 𝕜)) • t p.2) = B := by
      calc
        ∑ p : ι × κ, (((w p.1 * v p.2 : ℝ) : 𝕜)) • t p.2 =
            ∑ p : ι × κ, (w p.1 * v p.2) • t p.2 := by
          apply Finset.sum_congr rfl
          intro p _
          exact (real_smul_linearMap_eq (w p.1 * v p.2) (t p.2)).symm
        _ = B := hsecond
    calc
      ∑ p : ι × κ, (w p.1 * v p.2) •
          orthogonalBlockSum (z p.1) (t p.2) =
          ∑ p : ι × κ, (((w p.1 * v p.2 : ℝ) : 𝕜)) •
            orthogonalBlockSum (z p.1) (t p.2) := by
        apply Finset.sum_congr rfl
        intro p _
        exact real_smul_linearMap_eq (w p.1 * v p.2)
          (orthogonalBlockSum (z p.1) (t p.2))
      _ = orthogonalBlockSum
          (∑ p : ι × κ, (((w p.1 * v p.2 : ℝ) : 𝕜)) • z p.1)
          (∑ p : ι × κ, (((w p.1 * v p.2 : ℝ) : 𝕜)) • t p.2) := by
        ext x
        apply WithLp.ofLp_injective 2
        simp only [LinearMap.sum_apply, LinearMap.smul_apply,
          orthogonalBlockSum_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
          WithLp.ofLp_toLp]
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]
          exact Finset.sum_congr rfl fun p _ => Prod.smul_fst ..
        · rw [Prod.snd_sum]
          exact Finset.sum_congr rfl fun p _ => Prod.smul_snd ..
      _ = orthogonalBlockSum A B := by rw [hfirst', hsecond']

/-- Two simultaneous rectangular Ky Fan majorizations combine sharply on the
orthogonal block sum.

The real convex-hull argument is intentionally internal to this file, where
`realModuleLinearMap` provides the restricted scalar action.  Callers only
supply field-native Ky Fan inequalities and receive a norm inequality, so no
`Module ℝ` instance leaks across module boundaries. -/
theorem orthogonalBlockSum_apply_le_of_kyFanSum_le
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    (NB : UnitarilyInvariantSeminorm 𝕜
      (WithLp 2 (E₁ × E₂)) (WithLp 2 (F₁ × F₂)))
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : ∀ k, kyFanSum k A ≤ kyFanSum k C)
    (hB : ∀ k, kyFanSum k B ≤ kyFanSum k D) :
    NB (orthogonalBlockSum A B) ≤ NB (orthogonalBlockSum C D) := by
  apply NB.apply_le_of_mem_convexHull_twoSidedUnitaryOrbit
  exact orthogonalBlockSum_mem_convexHull_twoSidedUnitaryOrbit
    (mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le hA)
    (mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le hB)

/-- Pointwise singular-value dominance implies norm dominance.
-/
theorem apply_le_of_singularValues_le {A B : E →ₗ[𝕜] F}
    (h : ∀ i, A.singularValues i ≤ B.singularValues i) : N A ≤ N B := by
  apply N.apply_le_of_kyFanSum_le
  intro k
  unfold kyFanSum
  exact Finset.sum_le_sum fun i _ => h (i : ℕ)


end UnitarilyInvariantSeminorm


end TauCeti
