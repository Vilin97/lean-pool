/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.SelectedBranch

/-! # Compression Repulsion -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.1(i): compression-repulsion algebra

The source derives its first eigenvalue-repulsion inequality from two exact
facts about the direct-rotation blocks:

* the old compression is the sum of the two rotated restricted quadratic
  forms; and
* the sine and cosine blocks satisfy a Pythagorean partition.

This module isolates that algebra from the still-missing direct-rotation
instantiation.  The records below are proof certificates, not assumptions
installed globally and not axioms.  Once the concrete Section 3 block
identities are connected to them, the inequalities follow without any further
spectral argument.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

universe v

section CompressionAlgebra

variable {E : Type v} [NormedAddCommGroup E]

/-- Quadratic-form data for the upper-compression identity
`A₁ = S Λ₀ S⋆ + C Λ₁ C⋆`, stated at exactly the abstraction level needed by
Theorem 8.1(i). -/
structure UpperCompressionRepulsionData
    (qA1 qLambda0 qLambda1 : E → ℝ) (Sstar Cstar : E → E) : Prop where
  decomposition : ∀ x,
    qA1 x = qLambda0 (Sstar x) + qLambda1 (Cstar x)
  pythagoras : ∀ x,
    ‖Sstar x‖ ^ 2 + ‖Cstar x‖ ^ 2 = ‖x‖ ^ 2

/-- The upper compression-repulsion inequality.  This is the quadratic-form
content of
`A₁ - α ≤ C₁ (Λ₁ - α) C₁`
once the direct-rotation block identity is supplied. -/
theorem upperCompressionRepulsion_of_data
    {qA1 qLambda0 qLambda1 : E → ℝ} {Sstar Cstar : E → E}
    (D : UpperCompressionRepulsionData qA1 qLambda0 qLambda1 Sstar Cstar)
    {alpha : ℝ}
    (hLambda0 : ∀ y, qLambda0 y ≤ alpha * ‖y‖ ^ 2)
    (x : E) :
    qA1 x - alpha * ‖x‖ ^ 2 ≤
      qLambda1 (Cstar x) - alpha * ‖Cstar x‖ ^ 2 := by
  calc
    qA1 x - alpha * ‖x‖ ^ 2 =
        (qLambda0 (Sstar x) - alpha * ‖Sstar x‖ ^ 2) +
          (qLambda1 (Cstar x) - alpha * ‖Cstar x‖ ^ 2) := by
      rw [D.decomposition x, ← D.pythagoras x]
      ring
    _ ≤ 0 + (qLambda1 (Cstar x) - alpha * ‖Cstar x‖ ^ 2) := by
      exact add_le_add (sub_nonpos.mpr (hLambda0 (Sstar x))) le_rfl
    _ = qLambda1 (Cstar x) - alpha * ‖Cstar x‖ ^ 2 := zero_add _

/-- Quadratic-form data for the lower-compression companion
`A₀ = C Λ₀ C⋆ + S Λ₁ S⋆`. -/
structure LowerCompressionRepulsionData
    (qA0 qLambda0 qLambda1 : E → ℝ) (Cstar Sstar : E → E) : Prop where
  decomposition : ∀ x,
    qA0 x = qLambda0 (Cstar x) + qLambda1 (Sstar x)
  pythagoras : ∀ x,
    ‖Cstar x‖ ^ 2 + ‖Sstar x‖ ^ 2 = ‖x‖ ^ 2

/-- The lower-block companion of Theorem 8.1(i).  If the complementary
restricted form lies above the cut, then the downward displacement of the old
lower compression is controlled by the cosine-sandwiched displacement of the
new lower restriction. -/
theorem lowerCompressionRepulsion_of_data
    {qA0 qLambda0 qLambda1 : E → ℝ} {Cstar Sstar : E → E}
    (D : LowerCompressionRepulsionData qA0 qLambda0 qLambda1 Cstar Sstar)
    {alpha : ℝ}
    (hLambda1 : ∀ y, alpha * ‖y‖ ^ 2 ≤ qLambda1 y)
    (x : E) :
    alpha * ‖x‖ ^ 2 - qA0 x ≤
      alpha * ‖Cstar x‖ ^ 2 - qLambda0 (Cstar x) := by
  calc
    alpha * ‖x‖ ^ 2 - qA0 x =
        (alpha * ‖Cstar x‖ ^ 2 - qLambda0 (Cstar x)) +
          (alpha * ‖Sstar x‖ ^ 2 - qLambda1 (Sstar x)) := by
      rw [D.decomposition x, ← D.pythagoras x]
      ring
    _ ≤ (alpha * ‖Cstar x‖ ^ 2 - qLambda0 (Cstar x)) + 0 := by
      exact add_le_add le_rfl (sub_nonpos.mpr (hLambda1 (Sstar x)))
    _ = alpha * ‖Cstar x‖ ^ 2 - qLambda0 (Cstar x) := add_zero _

end CompressionAlgebra

/-! ### Paper-facing names for the algebraic cores

These take an abstract quadratic-data record rather than the concrete
direct-rotation blocks, so they are the algebraic cores of Theorem 8.1(i) and
not evidence about the printed theorem; the source-facing statements are in
`Section8/Presentation.lean`. -/

/-- Algebraic core of Theorem 8.1(i), before the abstract quadratic data is
instantiated with the direct-rotation sine and cosine blocks. -/
alias theorem8_1_upperCompressionRepulsion_of_rotatedBlockData :=
  upperCompressionRepulsion_of_data

/-- Lower-block companion of the compression-repulsion inequality. -/
alias theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData :=
  lowerCompressionRepulsion_of_data


end Section8
end DavisKahan1970
end TauCeti
