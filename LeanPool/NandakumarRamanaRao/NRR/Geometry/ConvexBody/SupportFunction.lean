/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Analysis.InnerProductSpace.Continuous
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Basic
public import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.Topology

/-!
# `NRR.Geometry.ConvexBody` — the support function

This module introduces the **support function** of a `ConvexBody` `K` in a real inner product
space `E`:

```text
h_K(u) = sup { ⟪x, u⟫ | x ∈ K }.
```

For a compact nonempty `K` and any direction `u`, the linear functional `x ↦ ⟪x, u⟫` is
continuous, so it attains its maximum on `K`; hence the supremum is finite and *attained*. The
support function is the canonical analytic interface to a convex body: width and perimeter are
later expressed through it.

## Design notes

* The definition uses `sSup` of the image of `K` under `x ↦ ⟪x, u⟫`, matching the mathematical
 formula. All order-theoretic boilerplate is discharged once, via the compactness maximizer
 `IsCompact.exists_isMaxOn`, which produces an `IsGreatest` witness for the image; from that the
 `sSup` characterisation, the attained maximum, the upper bound, and the least-upper-bound
 property all follow without hand-written epsilon arguments.
* The public API (`inner_le_supportFunction`, `supportFunction_le`, `exists_supportPoint`,
 the `sSup` characterisation, the zero-direction value, and congruence) does not expose the
 implementation detail that `sSup` is used; downstream files can treat `supportFunction` through
 these lemmas alone.
* We follow the library convention `inner ℝ x u` for the real inner product.

## Import policy

Following the library-wide policy, `Basic.lean` already pulls in `import Mathlib`, so no extra
imports are required here. The decisive Mathlib results used are `IsCompact.exists_isMaxOn`,
`IsGreatest.csSup_eq`, `le_csSup`, `csSup_le`, and continuity of the inner product.
-/

@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **support function** of a convex body `K` in direction `u`:
`h_K(u) = sup { ⟪x, u⟫ | x ∈ K }`. For compact nonempty `K` the supremum is finite and
attained (see `exists_supportPoint`). -/
noncomputable def supportFunction (K : ConvexBody E) (u : E) : ℝ :=
  sSup ((fun x : E => (inner ℝ x u : ℝ)) '' (K : Set E))

/-- Unfolding lemma: the support function is the supremum of the inner products over `K`. -/
theorem supportFunction_eq_sSup (K : ConvexBody E) (u : E) :
    supportFunction K u = sSup ((fun x : E => (inner ℝ x u : ℝ)) '' (K : Set E)) :=
  rfl

/-- The linear functional `x ↦ ⟪x, u⟫` attains its maximum on the (compact, nonempty) body `K`:
there is a point of `K` that is a maximiser. This is the compactness core of the API. -/
theorem exists_isMaxOn_inner (K : ConvexBody E) (u : E) :
    ∃ x ∈ (K : Set E), IsMaxOn (fun y : E => (inner ℝ y u : ℝ)) (K : Set E) x :=
  K.isCompact.exists_isMaxOn K.nonempty (by fun_prop)

/-- The image of `K` under `x ↦ ⟪x, u⟫` has a greatest element, attained at a support point. -/
theorem exists_isGreatest_image (K : ConvexBody E) (u : E) :
    ∃ x ∈ (K : Set E),
      IsGreatest ((fun x : E => (inner ℝ x u : ℝ)) '' (K : Set E)) (inner ℝ x u) := by
  obtain ⟨x, hx, hmax⟩ := K.exists_isMaxOn_inner u
  refine ⟨x, hx, ⟨⟨x, hx, rfl⟩, ?_⟩⟩
  rintro b ⟨y, hy, rfl⟩
  exact hmax hy

/-- **Existence of a support point.** For every direction `u` there is a point of `K` at which the
inner product equals the support function; equivalently, the supremum is attained. -/
theorem exists_supportPoint (K : ConvexBody E) (u : E) :
    ∃ x ∈ (K : Set E), (inner ℝ x u : ℝ) = supportFunction K u := by
  obtain ⟨x, hx, hgr⟩ := K.exists_isGreatest_image u
  exact ⟨x, hx, (hgr.csSup_eq).symm⟩

/-- The support function lies in the image, i.e. is attained as an inner product. -/
theorem supportFunction_mem_image (K : ConvexBody E) (u : E) :
    supportFunction K u ∈ ((fun x : E => (inner ℝ x u : ℝ)) '' (K : Set E)) := by
  obtain ⟨x, hx, hxeq⟩ := K.exists_supportPoint u
  exact ⟨x, hx, hxeq⟩

/-- **Upper bound.** Every inner product `⟪x, u⟫` for `x ∈ K` is at most the support function. -/
theorem inner_le_supportFunction (K : ConvexBody E) {x u : E} (hx : x ∈ (K : Set E)) :
    (inner ℝ x u : ℝ) ≤ supportFunction K u := by
  obtain ⟨y, _, hgr⟩ := K.exists_isGreatest_image u
  have : supportFunction K u = inner ℝ y u := hgr.csSup_eq
  rw [this]
  exact hgr.2 ⟨x, hx, rfl⟩

/-- **Least upper bound.** If `a` bounds every inner product over `K`, then it bounds the support
function. -/
theorem supportFunction_le (K : ConvexBody E) {u : E} {a : ℝ}
    (ha : ∀ x ∈ (K : Set E), (inner ℝ x u : ℝ) ≤ a) :
    supportFunction K u ≤ a := by
  refine csSup_le (K.nonempty.image _) ?_
  rintro b ⟨x, hx, rfl⟩
  exact ha x hx

/-- **Extensionality compatibility.** The support function only depends on the carrier set. -/
theorem supportFunction_congr {K L : ConvexBody E} (h : (K : Set E) = (L : Set E)) (u : E) :
    supportFunction K u = supportFunction L u := by
  rw [supportFunction_eq_sSup, supportFunction_eq_sSup, h]

/-- **Zero direction.** The support function in the zero direction is zero. -/
@[simp] theorem supportFunction_zero_direction (K : ConvexBody E) :
    supportFunction K 0 = 0 := by
  apply le_antisymm
  · exact K.supportFunction_le (fun x _ => by simp)
  · obtain ⟨x, hx⟩ := K.nonempty
    have := K.inner_le_supportFunction (x := x) (u := 0) hx
    simpa using this

end ConvexBody

end NRR.Geometry
