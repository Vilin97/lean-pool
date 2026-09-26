/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.Davis1963.RotationBound
public import LeanPool.DavisKahan.DavisKahan.Sources.Davis1963.DoubleAngle
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Core.OperatorBlocks
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# Davis's 1963 finite-dimensional rotation theory

Literature map:

* `prose/core-arguments/Davis-1963-core-arguments.tex`, all sections.
* `papers/formalization_comparisons/DavisKahan-formalized-vs-literature.tex`, paragraphs
  "Davis's sharper total-rotation estimate" and
  "The per-eigenvector sin2theta/tan2theta theorem".

These declarations provide basis-independent endpoints around the existing
`RotationBound.lean` and `RotationSharp.lean` proofs.
-/

@[expose] public section


/-! ## Remaining construction plan

Define `totalRotationEnergy P Q hnd` by choosing an orthonormal basis adapted
blockwise to `P`, summing `OrthoProjFamily.sqSinAngle hnd`, and proving basis
independence from the Frobenius norm of the off-diagonal part of the canonical
intertwining unitary.  Once this bridge is available, specialize the existing
rank-one overlap theorem in `RotationBound.lean` blockwise and use Frobenius
orthogonality to prove the family-level Davis 1963 statements.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Squared total rotation for the canonical matching of the eigenvector
bases of two self-adjoint operators.

This is the finite simple-spectrum quantity appearing in Davis's Theorem 3.2:
`Σᵢ (1 - |⟪vᵢ,xᵢ⟫|²)`, expressed through the canonical intertwining unitary of
the two rank-one spectral families.  The earlier arbitrary-block signature was
not mathematically sound: `PointSpectrumIn` alone neither makes a block reducing nor
forces scalar action on it, and unweighted block labels mishandle multiplicity.
-/
noncomputable def totalRotationEnergy
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n)
    (hover : ∀ i, ⟪hB.eigenvectorBasis hn i, hA.eigenvectorBasis hn i⟫_𝕜 ≠ 0) : ℝ :=
  ∑ i, OrthoProjFamily.sqSinAngle
    (nonDegenerate_ofOrthonormalBasis hover) (hA.eigenvectorBasis hn) i

/-- Sum of squared eigenvalue motions under the sorted canonical matching. -/
noncomputable def eigenvalueMotionEnergy {n : ℕ}
    (lam μ : Fin n → ℝ) : ℝ :=
  ∑ i, (lam i - μ i) ^ 2

/-- Squared Frobenius energy of the diagonal of `H` in the eigenbasis of `A`. -/
noncomputable def eigenbasisPinchEnergy
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {n : ℕ}
    (hn : finrank 𝕜 E = n) (H : E →ₗ[𝕜] E) : ℝ :=
  ∑ i, RCLike.re
    ⟪hA.eigenvectorBasis hn i, H (hA.eigenvectorBasis hn i)⟫_𝕜 ^ 2

/-- Squared Frobenius energy outside the diagonal in the eigenbasis of `A`. -/
noncomputable def eigenbasisOffDiagonalEnergy
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {n : ℕ}
    (hn : finrank 𝕜 E = n) (H : E →ₗ[𝕜] E) : ℝ :=
  UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) H ^ 2 -
    eigenbasisPinchEnergy hA hn H

/-- Davis 1963, Theorem 3.2: sharpened total-rotation bound with eigenvalue
motion subtracted from the available perturbation energy, for the canonical
sorted eigenvector matching.

This corrected statement is the mathematically meaningful theorem supported by
the repository's completed rank-one spectral-resolution development.  An
arbitrary block-family version requires explicit reducing/scalar-action
hypotheses and rank-weighted eigenvalue motion; it cannot be obtained from the
old `PointSpectrumIn` hypotheses.
-/
theorem totalRotation_add_eigenvalueMotion_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n)
    (hover : ∀ i, ⟪hB.eigenvectorBasis hn i, hA.eigenvectorBasis hn i⟫_𝕜 ≠ 0)
    {γ : ℝ}
    (hsep : ∀ i j, i ≠ j →
      γ ^ 2 + (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 ≤
        (hA.eigenvalues hn i - hB.eigenvalues hn j) ^ 2) :
    γ ^ 2 * totalRotationEnergy hA hB hn hover +
        eigenvalueMotionEnergy (hA.eigenvalues hn) (hB.eigenvalues hn) ≤
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A) ^ 2 := by
  have h := rotation_add_displacement_le_hilbertSchmidt_intertwining
    hA hB hn hover hsep
  rw [UnitarilyInvariantSeminorm.frobenius_sq (𝕜 := 𝕜) (E := E) (B - A) hn
    (hA.eigenvectorBasis hn)]
  simpa [totalRotationEnergy, eigenvalueMotionEnergy] using h

/-- Davis 1963, Theorem 4.1: the squared eigenvalue motion dominates diagonal
perturbation energy minus off-diagonal perturbation energy.

The corrected hypothesis controls the **diagonal** (pinched) energy, exactly as
in Davis's theorem and `sum_sq_eigenvalues_sub_ge`.  The previous declaration
controlled the off-diagonal energy and used arbitrary block labels; that form
was not the theorem proved in the literature and was false without additional
multiplicity and reducing-block hypotheses.
-/
theorem diagonalPerturbation_sub_offDiagonal_le_eigenvalueMotion
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hsepB : ∀ i j, i ≠ j →
      γ ≤ |hB.eigenvalues hn i - hB.eigenvalues hn j|)
    (hpinchSmall : eigenbasisPinchEnergy hA hn (B - A) ≤
      (γ / Real.sqrt 2) ^ 2) :
    eigenbasisPinchEnergy hA hn (B - A) -
        eigenbasisOffDiagonalEnergy hA hn (B - A) ≤
      eigenvalueMotionEnergy (hA.eigenvalues hn) (hB.eigenvalues hn) := by
  have hmotion := sum_sq_eigenvalues_sub_ge hA hB hn hγ hsepB hpinchSmall
  have hoff := sum_sq_eigenvalues_sub_diag_eq hA hB hn
  have hsymm :
      (∑ i, (hB.eigenvalues hn i - hA.eigenvalues hn i) ^ 2) =
        ∑ i, (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsymm] at hmotion
  rw [hoff] at hmotion
  unfold eigenbasisOffDiagonalEnergy eigenvalueMotionEnergy
  rw [UnitarilyInvariantSeminorm.frobenius_sq (𝕜 := 𝕜) (E := E) (B - A) hn
    (hA.eigenvectorBasis hn)]
  simpa only [eigenbasisPinchEnergy] using hmotion

/-- Davis's off-diagonal corollary for total rotation in the canonical sorted
eigenvector matching.
-/
theorem totalRotation_le_two_mul_offDiagonal
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n)
    {γ γ' : ℝ} (hγ : 0 ≤ γ)
    (hsepB : ∀ i j, i ≠ j →
      γ ≤ |hB.eigenvalues hn i - hB.eigenvalues hn j|)
    (hpinchSmall : eigenbasisPinchEnergy hA hn (B - A) ≤
      (γ / Real.sqrt 2) ^ 2)
    (hover : ∀ i, ⟪hB.eigenvectorBasis hn i, hA.eigenvectorBasis hn i⟫_𝕜 ≠ 0)
    (hsepMixed : ∀ i j, i ≠ j →
      γ' ^ 2 + (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 ≤
        (hA.eigenvalues hn i - hB.eigenvalues hn j) ^ 2) :
    γ' ^ 2 * totalRotationEnergy hA hB hn hover ≤
      2 * eigenbasisOffDiagonalEnergy hA hn (B - A) := by
  have h := rotation_le_two_mul_offDiag hA hB hn hγ hsepB hpinchSmall
    hover hsepMixed
  unfold totalRotationEnergy eigenbasisOffDiagonalEnergy eigenbasisPinchEnergy
  rw [UnitarilyInvariantSeminorm.frobenius_sq (𝕜 := 𝕜) (E := E) (B - A) hn
    (hA.eigenvectorBasis hn)]
  exact h

/-- **An operator-norm bound gives a pointwise bound.**

Derived twice below from the same three lines. -/
private theorem norm_apply_le_of_opNorm_le {H : E →ₗ[𝕜] E} {ε : ℝ}
    (hHnorm : ‖H.toContinuousLinearMap‖ ≤ ε) (v : E) : ‖H v‖ ≤ ε * ‖v‖ := by
  calc
    ‖H v‖ ≤ ‖H.toContinuousLinearMap‖ * ‖v‖ :=
      H.toContinuousLinearMap.le_opNorm v
    _ ≤ ε * ‖v‖ := by gcongr

/-- Sharp two-subspace product estimate, the 1963 ancestor of `sin 2Θ`.
-/
theorem sinTwoTheta_eigenvector_product_le
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U) {a b ε lam : ℝ} (_hab : a < b)
    (hupper : ∀ z ∈ Uᗮ, RCLike.re ⟪A z, z⟫_𝕜 ≤ a * ‖z‖ ^ 2)
    (hlower : ∀ y ∈ U, b * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    {x : E} (hx : ‖x‖ = 1) (heig : (A + H) x = (lam : 𝕜) • x)
    (hHnorm : ‖H.toContinuousLinearMap‖ ≤ ε) :
    (b - a) * ‖projection U x‖ * ‖complementaryProjection U x‖ ≤ ε := by
  have hHbound : ∀ v : E, ‖H v‖ ≤ ε * ‖v‖ :=
    norm_apply_le_of_opNorm_le hHnorm
  have heig' : A x + H x = (lam : 𝕜) • x := by
    simpa using heig
  simpa [projection, complementaryProjection, mul_assoc] using
    sin_two_theta_le hA hH hU hlower hupper hHbound hx heig'

/-- Vanishing-pinch product estimate, the 1963 ancestor of `tan 2Θ`.
-/
theorem tanTwoTheta_eigenvector_product_le
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U) (hoff : IsOffDiagonal U H)
    {a b ε lam : ℝ} (_hab : a < b)
    (hupper : ∀ z ∈ Uᗮ, RCLike.re ⟪A z, z⟫_𝕜 ≤ a * ‖z‖ ^ 2)
    (hlower : ∀ y ∈ U, b * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    {x : E} (hx : ‖x‖ = 1) (heig : (A + H) x = (lam : 𝕜) • x)
    (hHnorm : ‖H.toContinuousLinearMap‖ ≤ ε) :
    (b - a) * ‖projection U x‖ * ‖complementaryProjection U x‖ ≤
      |‖projection U x‖ ^ 2 - ‖complementaryProjection U x‖ ^ 2| * ε := by
  have hHbound : ∀ v : E, ‖H v‖ ≤ ε * ‖v‖ :=
    norm_apply_le_of_opNorm_le hHnorm
  obtain ⟨hHU, hHUperp⟩ := inner_blocks_eq_zero_of_isOffDiagonal U H hoff
  have heig' : A x + H x = (lam : 𝕜) • x := by
    simpa using heig
  simpa [projection, complementaryProjection, mul_assoc] using
    tan_two_theta_le hA hH hU hlower hupper hHbound hHU hHUperp hx heig'

end DavisKahan.FiniteDimensional
end TauCeti
