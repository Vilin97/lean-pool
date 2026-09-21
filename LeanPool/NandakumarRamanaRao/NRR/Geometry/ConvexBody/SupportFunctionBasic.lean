/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunction
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.AffineOps
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.LinearImage

/-!
# `NRR.Geometry.ConvexBody` — algebraic and geometric properties of the support function

This module strengthens the support-function API introduced in
`NRR.Geometry.ConvexBody.SupportFunction`. It provides the properties needed for the
later development of width, perimeter, and transformations of convex bodies, so that downstream
files never have to reason directly with `sSup`.

## Contents

* **Attainment / support points** — `exists_supportPoint` (re-exposed from the base module) and
 `supportFunction_isMax`.
* **Positive homogeneity** — `supportFunction_smul_direction_of_nonneg` (`@[simp]`) and its
 strictly-positive variant `supportFunction_smul_direction_of_pos`.
* **Subadditivity** — `supportFunction_add_direction_le`.
* **Monotonicity** — `supportFunction_mono`.
* **Translation** — `supportFunction_translate` (`@[simp]`).
* **Scaling** — `supportFunction_scalePos` (`@[simp]`).
* **Linear equivalence** — `supportFunction_imageLinearEquiv`, stated via the *adjoint*
 `ContinuousLinearMap.adjoint`, which is the mathematically correct direction for an inner
 product space (the naive `e.symm` form is false unless `e` is an isometry).
* **Boundedness estimates** — `supportFunction_le_radius` and `supportFunction_abs_le`.

## Design notes

All proofs go through the two order-theoretic interfaces from the base module,
`inner_le_supportFunction` (upper bound) and `supportFunction_le` (least upper bound), together
with the attainment lemma `exists_supportPoint`. No `sSup` appears in any statement here.

For homogeneity, subadditivity, monotonicity, translation and scaling the ambient space is only
assumed to be a real inner product space. The linear-equivalence lemma additionally requires the
domain and codomain to be complete (so that the adjoint exists); this is automatic in finite
dimensions.
-/

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Attainment and support points -/

/-- **Support maximiser.** For every direction `u` there is a point of `K` attaining the support
function, and it is a maximiser of `x ↦ ⟪x, u⟫` over `K`. -/
theorem supportFunction_isMax (K : ConvexBody E) (u : E) :
    ∃ x ∈ (K : Set E),
      (inner ℝ x u : ℝ) = supportFunction K u ∧
      ∀ y ∈ (K : Set E), (inner ℝ y u : ℝ) ≤ (inner ℝ x u : ℝ) := by
  obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint u
  refine ⟨x, hx, hxeq, fun y hy => ?_⟩
  rw [hxeq]
  exact K.inner_le_supportFunction hy

/-! ### Positive homogeneity -/

/-- **Positive homogeneity (nonnegative scalar).** `h_K(c u) = c · h_K(u)` for `0 ≤ c`. -/
@[simp] theorem supportFunction_smul_direction_of_nonneg
    (K : ConvexBody E) {c : ℝ} (hc : 0 ≤ c) (u : E) :
    supportFunction K (c • u) = c * supportFunction K u := by
  apply le_antisymm
  · -- `h_K(c u) ≤ c · h_K(u)`
    apply K.supportFunction_le
    intro x hx
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (K.inner_le_supportFunction hx) hc
  · -- `c · h_K(u) ≤ h_K(c u)` via a support point in direction `u`
    obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint u
    calc c * supportFunction K u = c * (inner ℝ x u : ℝ) := by rw [hxeq]
      _ = (inner ℝ x (c • u) : ℝ) := by rw [real_inner_smul_right]
      _ ≤ supportFunction K (c • u) := K.inner_le_supportFunction hx

/-- **Positive homogeneity (positive scalar).** `h_K(c u) = c · h_K(u)` for `0 < c`. -/
theorem supportFunction_smul_direction_of_pos
    (K : ConvexBody E) {c : ℝ} (hc : 0 < c) (u : E) :
    supportFunction K (c • u) = c * supportFunction K u :=
  K.supportFunction_smul_direction_of_nonneg hc.le u

/-! ### Subadditivity -/

/-- **Subadditivity in the direction.** `h_K(u + v) ≤ h_K(u) + h_K(v)`. Note that equality does
*not* hold in general. -/
theorem supportFunction_add_direction_le
    (K : ConvexBody E) (u v : E) :
    supportFunction K (u + v) ≤ supportFunction K u + supportFunction K v := by
  apply K.supportFunction_le
  intro x hx
  rw [inner_add_right]
  exact add_le_add (K.inner_le_supportFunction hx) (K.inner_le_supportFunction hx)

/-! ### Monotonicity -/

/-- **Monotonicity.** A larger body has a larger support function in every direction. -/
theorem supportFunction_mono
    {K L : ConvexBody E}
    (hKL : (K : Set E) ⊆ (L : Set E)) (u : E) :
    supportFunction K u ≤ supportFunction L u := by
  apply K.supportFunction_le
  intro x hx
  exact L.inner_le_supportFunction (hKL hx)

/-! ### Translation -/

/-- **Translation.** `h_{K + a}(u) = ⟪a, u⟫ + h_K(u)`. -/
@[simp] theorem supportFunction_translate
    (K : ConvexBody E) (a u : E) :
    supportFunction (K.translate a) u =
      (inner ℝ a u : ℝ) + supportFunction K u := by
  apply le_antisymm
  · apply (K.translate a).supportFunction_le
    intro y hy
    rw [mem_translate] at hy
    have : (inner ℝ y u : ℝ) = (inner ℝ a u : ℝ) + (inner ℝ (y - a) u : ℝ) := by
      rw [← inner_add_left]; congr 1; abel
    rw [this]
    have := K.inner_le_supportFunction (u := u) hy
    linarith
  · obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint u
    have hmem : a + x ∈ (K.translate a : Set E) := by
      rw [mem_translate]; simpa using hx
    calc (inner ℝ a u : ℝ) + supportFunction K u
        = (inner ℝ a u : ℝ) + (inner ℝ x u : ℝ) := by rw [hxeq]
      _ = (inner ℝ (a + x) u : ℝ) := by rw [inner_add_left]
      _ ≤ supportFunction (K.translate a) u := (K.translate a).inner_le_supportFunction hmem

/-! ### Scaling -/

/-- **Positive scaling.** `h_{r K}(u) = r · h_K(u)` for `0 < r`. -/
@[simp] theorem supportFunction_scalePos
    (K : ConvexBody E) {r : ℝ} (hr : 0 < r) (u : E) :
    supportFunction (K.scalePos r hr) u =
      r * supportFunction K u := by
  apply le_antisymm
  · apply (K.scalePos r hr).supportFunction_le
    intro y hy
    rw [mem_scalePos] at hy
    have hy' : y = r • (r⁻¹ • y) := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hy', real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (K.inner_le_supportFunction hy) hr.le
  · obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint u
    have hmem : r • x ∈ (K.scalePos r hr : Set E) := by
      rw [mem_scalePos, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]; exact hx
    calc r * supportFunction K u = r * (inner ℝ x u : ℝ) := by rw [hxeq]
      _ = (inner ℝ (r • x) u : ℝ) := by rw [real_inner_smul_left]
      _ ≤ supportFunction (K.scalePos r hr) u :=
          (K.scalePos r hr).inner_le_supportFunction hmem

/-! ### Linear equivalence

For an inner product space the correct pullback of the direction is through the **adjoint** of
the linear map, not `e.symm`. We state and prove the mathematically correct identity
`h_{eK}(u) = h_K(eᵀ u)`, where `eᵀ = ContinuousLinearMap.adjoint (e : E →L[ℝ] F)`. This requires
`E` and `F` to be complete inner product spaces (automatic in finite dimensions). -/

/-- **Image under a continuous linear equivalence.** `h_{eK}(u) = h_K(eᵀ u)`, where `eᵀ` is the
adjoint of `e`. -/
theorem supportFunction_imageLinearEquiv
    [CompleteSpace E] [CompleteSpace F]
    (K : ConvexBody E) (e : E ≃L[ℝ] F) (u : F) :
    supportFunction (K.imageLinearEquiv e) u =
      supportFunction K (ContinuousLinearMap.adjoint (e : E →L[ℝ] F) u) := by
  have key : ∀ x : E, (inner ℝ (e x) u : ℝ)
      = inner ℝ x (ContinuousLinearMap.adjoint (e : E →L[ℝ] F) u) := by
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right]; simp [ContinuousLinearEquiv.coe_coe]
  apply le_antisymm
  · apply (K.imageLinearEquiv e).supportFunction_le
    intro y hy
    rw [mem_imageLinearEquiv] at hy
    have hthis : (inner ℝ y u : ℝ)
        = inner ℝ (e.symm y) (ContinuousLinearMap.adjoint (e : E →L[ℝ] F) u) := by
      rw [← key (e.symm y)]; simp
    rw [hthis]
    exact K.inner_le_supportFunction hy
  · obtain ⟨x, hx, hxeq⟩ :=
      K.exists_supportPoint (ContinuousLinearMap.adjoint (e : E →L[ℝ] F) u)
    have hmem : e x ∈ (K.imageLinearEquiv e : Set F) := by
      rw [mem_imageLinearEquiv]; simpa using hx
    calc supportFunction K (ContinuousLinearMap.adjoint (e : E →L[ℝ] F) u)
        = (inner ℝ x (ContinuousLinearMap.adjoint (e : E →L[ℝ] F) u) : ℝ) := hxeq.symm
      _ = (inner ℝ (e x) u : ℝ) := (key x).symm
      _ ≤ supportFunction (K.imageLinearEquiv e) u :=
          (K.imageLinearEquiv e).inner_le_supportFunction hmem

/-! ### Boundedness estimates -/

/-- **Radius bound.** If every point of `K` has norm at most `R`, then `h_K(u) ≤ R ‖u‖`. -/
theorem supportFunction_le_radius
    (K : ConvexBody E) {R : ℝ}
    (hR : ∀ x ∈ (K : Set E), ‖x‖ ≤ R) (u : E) :
    supportFunction K u ≤ R * ‖u‖ := by
  apply K.supportFunction_le
  intro x hx
  calc (inner ℝ x u : ℝ) ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
    _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg u)

/-- **Uniform bound.** There is a constant `C ≥ 0` with `|h_K(u)| ≤ C ‖u‖` for all directions
`u`. This is the estimate needed for continuity/integrability of the support function. -/
theorem supportFunction_abs_le
    (K : ConvexBody E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E, |supportFunction K u| ≤ C * ‖u‖ := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hR' : ∀ x ∈ (K : Set E), ‖x‖ ≤ R := by
    intro x hx
    have := hR hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hRnn : 0 ≤ R := by
    obtain ⟨x, hx⟩ := K.nonempty
    exact le_trans (norm_nonneg x) (hR' x hx)
  refine ⟨R, hRnn, fun u => ?_⟩
  rw [abs_le]
  constructor
  · -- lower bound: use a support point (in direction `u`) and Cauchy–Schwarz
    obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint u
    rw [← hxeq]
    calc -(R * ‖u‖) ≤ -(‖x‖ * ‖u‖) := by
            apply neg_le_neg
            exact mul_le_mul_of_nonneg_right (hR' x hx) (norm_nonneg u)
      _ = -‖x‖ * ‖u‖ := by ring
      _ ≤ (inner ℝ x u : ℝ) := by
            have h := abs_real_inner_le_norm x u
            rw [abs_le] at h
            calc -‖x‖ * ‖u‖ = -(‖x‖ * ‖u‖) := by ring
              _ ≤ (inner ℝ x u : ℝ) := h.1
  · exact K.supportFunction_le_radius hR' u

end ConvexBody

end NRR.Geometry
