/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunction
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionBasic

/-!
# `NRR.Geometry.ConvexBody` — the width function

This module introduces the **width function** of a `ConvexBody` `K` in a real inner product
space `E`:

```text
w_K(u) = h_K(u) + h_K(-u),
```

defined on *all* vectors `u`, not only unit vectors. Geometrically, `w_K(u)` measures the extent
of `K` in the direction `u` (the distance between the two supporting hyperplanes with outer
normals `u` and `-u`, scaled by `‖u‖`).

## Design notes

* The width function is built directly on top of the support-function interface
 (`supportFunction`, `inner_le_supportFunction`, `supportFunction_mono`,
 `supportFunction_smul_direction_of_nonneg`) from `SupportFunction.lean` and
 `SupportFunctionBasic.lean`. No `sSup` or structure internals are unfolded here.
* The basic algebraic properties are: evenness (`widthFunction_neg`), vanishing at zero
 (`widthFunction_zero`), nonnegativity (`widthFunction_nonneg`), monotonicity
 (`widthFunction_mono`), and positive homogeneity (`widthFunction_smul_direction_of_nonneg`).

## Import policy

`SupportFunction.lean` (via `Basic.lean`) already pulls in `import Mathlib`, so no extra imports
are required here.
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **width function** of a convex body `K` in direction `u`:
`w_K(u) = h_K(u) + h_K(-u)`. Defined for all vectors `u`, not only unit vectors. -/
noncomputable def widthFunction (K : ConvexBody E) (u : E) : ℝ :=
  supportFunction K u + supportFunction K (-u)

/-- Unfolding lemma for the width function. -/
@[simp] theorem widthFunction_def (K : ConvexBody E) (u : E) :
    widthFunction K u = supportFunction K u + supportFunction K (-u) :=
  rfl

/-- **Evenness.** The width function is invariant under negation of the direction. -/
theorem widthFunction_neg (K : ConvexBody E) (u : E) :
    widthFunction K (-u) = widthFunction K u := by
  simp only [widthFunction_def, neg_neg]
  ring

/-- **Zero direction.** The width function vanishes in the zero direction. -/
theorem widthFunction_zero (K : ConvexBody E) :
    widthFunction K 0 = 0 := by
  simp [widthFunction_def]

/-- **Nonnegativity.** The width function is always nonnegative. -/
theorem widthFunction_nonneg (K : ConvexBody E) (u : E) :
    0 ≤ widthFunction K u := by
  obtain ⟨x, hx⟩ := K.nonempty
  have h₁ : (inner ℝ x u : ℝ) ≤ supportFunction K u := K.inner_le_supportFunction hx
  have h₂ : (inner ℝ x (-u) : ℝ) ≤ supportFunction K (-u) := K.inner_le_supportFunction hx
  have hsum := add_le_add h₁ h₂
  simp only [inner_neg_right, add_neg_cancel] at hsum
  simpa [widthFunction_def] using hsum

/-- **Monotonicity.** A larger body has a larger width in every direction. -/
theorem widthFunction_mono {K L : ConvexBody E}
    (hKL : (K : Set E) ⊆ (L : Set E)) (u : E) :
    widthFunction K u ≤ widthFunction L u := by
  simp only [widthFunction_def]
  exact add_le_add (supportFunction_mono hKL u) (supportFunction_mono hKL (-u))

/-- **Positive homogeneity (nonnegative scalar).** `w_K(c u) = c · w_K(u)` for `0 ≤ c`. -/
theorem widthFunction_smul_direction_of_nonneg
    (K : ConvexBody E) {c : ℝ} (hc : 0 ≤ c) (u : E) :
    widthFunction K (c • u) = c * widthFunction K u := by
  simp only [widthFunction_def, ← smul_neg,
    K.supportFunction_smul_direction_of_nonneg hc]
  ring

end ConvexBody

end NRR.Geometry
