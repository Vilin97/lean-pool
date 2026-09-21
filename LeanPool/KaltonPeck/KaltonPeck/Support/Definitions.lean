/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Core operator and symplectic definitions

This file defines continuous alternating and strong symplectic forms, together with the
Fredholm, finite-rank, complex-structure, and hyperplane notions used throughout the project.
-/

namespace KaltonPeck.Support

noncomputable section

/-- A possibly degenerate continuous alternating form on a real normed space.

Blueprint: `def:weak-form`; audit: `DEF-WEAK-ALT-FORM`, `DEF-INDUCED-OPERATOR`. -/
structure ContinuousAlternatingForm (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- The curried continuous operator induced by the form. -/
  toDual : X →L[ℝ] StrongDual ℝ X
  /-- The form vanishes on the diagonal. -/
  alternating : ∀ x, toDual x x = 0

/-- The symplectic orthogonal of a subspace for a continuous alternating form.

Blueprint: `def:weak-form`; audit: `DEF-SYMPLECTIC-ORTHOGONAL`. -/
def ContinuousAlternatingForm.orthogonal {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (b : ContinuousAlternatingForm X) (E : Submodule ℝ X) :
    Submodule ℝ X := by
  exact (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ E X ℝ)) E.subtypeL).comp
    b.toDual).toLinearMap.ker

/-- The radical, equivalently the kernel of the operator induced by the form.

Blueprint: `def:weak-form`; audit: `DEF-RADICAL`. -/
def ContinuousAlternatingForm.radical {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (b : ContinuousAlternatingForm X) : Submodule ℝ X := by
  exact b.toDual.toLinearMap.ker

/-- The radical is the kernel of the continuous operator induced by the form.

Blueprint: `def:weak-form`; audit: `DEF-RADICAL`. -/
theorem ContinuousAlternatingForm.radical_eq_ker {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (b : ContinuousAlternatingForm X) :
    b.radical = b.toDual.toLinearMap.ker := by
  rfl

/-- The radical of a continuous alternating form is closed.

Blueprint: `def:weak-form`; audit: `DEF-RADICAL`. This is an instance so quotient norms by the
radical elaborate without a redundant closedness binder. -/
@[instance]
theorem ContinuousAlternatingForm.radical_isClosed {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (b : ContinuousAlternatingForm X) :
    IsClosed (b.radical : Set X) := by
  exact b.toDual.isClosed_ker

/-- The restriction of a continuous alternating form to a linear subspace.

Blueprint: `def:weak-form`; audit: `DEF-RESTRICTED-RADICAL`. -/
def ContinuousAlternatingForm.restrict {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (b : ContinuousAlternatingForm X) (E : Submodule ℝ X) :
    ContinuousAlternatingForm E := by
  exact
    { toDual :=
        ((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ E X ℝ)) E.subtypeL).comp
          (b.toDual.comp E.subtypeL)
      alternating := fun x => b.alternating x }

/-- The radical of the restriction of a continuous alternating form to a subspace.

Blueprint: `def:weak-form`; audit: `DEF-RESTRICTED-RADICAL`. -/
def ContinuousAlternatingForm.restrictedRadical {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (b : ContinuousAlternatingForm X) (E : Submodule ℝ X) :
    Submodule ℝ X := by
  exact E ⊓ b.orthogonal E

/-- A strong continuous alternating form on a real normed space. -/
structure StrongSymplecticForm (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- The continuous linear equivalence induced by the strong symplectic form. -/
  toDual : X ≃L[ℝ] StrongDual ℝ X
  alternating : ∀ x, toDual x x = 0

/-- Regard a strong symplectic form as a possibly degenerate continuous alternating form.

This is the implementation bridge into the weak-form API.
Blueprint: `def:weak-form`; audit: `DEF-WEAK-ALT-FORM`, `DEF-STRONG-SYMPLECTIC`. -/
def StrongSymplecticForm.toContinuousAlternatingForm {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (b : StrongSymplecticForm X) :
    ContinuousAlternatingForm X := by
  exact { toDual := b.toDual.toContinuousLinearMap, alternating := b.alternating }

/-- The transpose of a bounded linear map between real normed spaces. -/
def transpose {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) :
    StrongDual ℝ Y →L[ℝ] StrongDual ℝ X :=
  (ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ X Y ℝ)) T

/-- The adjoint of a bounded operator with respect to a strong symplectic form. -/
def StrongSymplecticForm.adjoint {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ω : StrongSymplecticForm X) (T : X →L[ℝ] X) : X →L[ℝ] X :=
  ω.toDual.symm.toContinuousLinearMap.comp
    ((transpose T).comp ω.toDual.toContinuousLinearMap)

/-- A bounded linear map is Fredholm when it has finite-dimensional kernel, closed range,
and finite-dimensional cokernel. -/
def IsFredholm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : Prop :=
  FiniteDimensional ℝ T.toLinearMap.ker ∧
    IsClosed (T.toLinearMap.range : Set Y) ∧
      FiniteDimensional ℝ (Y ⧸ T.toLinearMap.range)

/-- A bounded linear map has finite rank when its algebraic range is finite-dimensional. -/
def HasFiniteRank {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : Prop :=
  FiniteDimensional ℝ T.toLinearMap.range

/-- The rank of a bounded linear map, used when its range is finite-dimensional. -/
def operatorRank {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : ℕ :=
  Module.finrank ℝ T.toLinearMap.range

/-- The dimension of the kernel of a bounded linear map, used when the kernel is
finite-dimensional. -/
def nullity {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : ℕ :=
  Module.finrank ℝ T.toLinearMap.ker

/-- The Fredholm index is nullity minus the finrank of the quotient by the range, with both
natural dimensions coerced to integers. It is interpreted as a dimension difference under the
finite-dimensional hypotheses in `IsFredholm`.

Blueprint: `def:fredholm-rank`; audit: `DEF-FREDHOLM-INDEX`. -/
def fredholmIndex {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) : ℤ := by
  exact (nullity T : ℤ) - (Module.finrank ℝ (Y ⧸ T.toLinearMap.range) : ℤ)

/-- A complex structure on a real normed space is a bounded operator squaring to `-I`. -/
def IsComplexStructure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : X →L[ℝ] X) : Prop :=
  J ^ 2 = -1

/-- A closed codimension-one linear subspace. -/
def IsHyperplane {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Submodule ℝ X) : Prop :=
  IsClosed (H : Set X) ∧ Module.finrank ℝ (X ⧸ H) = 1

end

end KaltonPeck.Support

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
