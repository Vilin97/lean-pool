/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.CrossedDefectGap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Bilateral Shift Example -/

open TauCeti.DavisKahan.Sylvester

/-!
# The bilateral shift and its coordinate half-spaces

Let `H` be a Hilbert space carrying a Hilbert basis indexed by `ℤ` -- that is,
the two-sided square-summable sequences `(…, a₋₁, a₀, a₁, …)` presented
coordinate-free, with `aₙ = ⟪bₙ, x⟫`.  For an integer `k` the *coordinate
half-space* `coordinateHalfSpace b k` is the closed subspace of vectors whose
coordinates vanish below `k`, and the *bilateral shift* is the unitary sending
`bₙ` to `bₙ₊₁`.

The shift carries each half-space onto the next, so any two of them are
unitarily equivalent along with their complements.  Their crossed
intersections, however, are *not* equivalent: for the pair cut at `0` and `1`
the source crossed defect `U ⊓ Vᗮ` is the line `span {b 0}` while the target
crossed defect `Uᗮ ⊓ V` is zero.

That asymmetry is what makes this pair the canonical separating example of the
Halmos development:

* it satisfies the ambient dimension hypothesis (1.5) -- the two subspaces are
  isometric and so are their complements -- while failing the crossed-defect
  hypothesis (3.5), so (1.5) does not imply (3.5);
* its two directed gaps are `1` and `0`, which refutes
  `directedGap_comm_of_crossedDefectsEquivalent` and
  `subspaceGap_eq_directedGap_of_crossedDefectsEquivalent` once (3.5) is
  dropped, and so shows that hypothesis to be load-bearing.

Everything here is generic two-subspace geometry: no Davis--Kahan source
numbering appears.  The paper-facing Remark that consumes it -- the Remark after
Davis--Kahan 1970, Proposition 3.2 -- lives in
`DavisKahan/Sources/DavisKahan1970/Section3Proposition32.lean`.

The scalar field is an arbitrary `RCLike` field; nothing below uses the complex
structure, so the real sequence space is the `𝕜 = ℝ` instance.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan



universe u

section BilateralShift

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Transport of an orthogonal projection along a surjective isometry.** -/
theorem starProjection_of_map_eq {K L : Submodule 𝕜 H}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (e : H ≃ₗᵢ[𝕜] H)
    (h : K.map (e.toLinearEquiv : H →ₗ[𝕜] H) = L) (y : H) :
    L.starProjection (e y) = e (K.starProjection y) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [← h]
    exact Submodule.mem_map_of_mem (K.starProjection_apply_mem y)
  · intro w hw
    rw [← h] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    change ⟪e y - e (K.starProjection y), e u⟫_𝕜 = 0
    rw [← map_sub, e.inner_map_map]
    exact K.starProjection_inner_eq_zero y u hu

/-! ### The coordinate half-spaces -/

/-- **The coordinate half-space cut at `k`.**

For a Hilbert basis of `H` indexed by `ℤ` this is the closed subspace of
vectors whose coordinates `aₙ = ⟪bₙ, x⟫` vanish for every `n < k`. -/
noncomputable abbrev coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    Submodule 𝕜 H :=
  (Submodule.span 𝕜 (b '' {n : ℤ | n < k}))ᗮ

omit [CompleteSpace H] in
/-- Coordinate description of a coordinate half-space. -/
theorem mem_coordinateHalfSpace {b : HilbertBasis ℤ 𝕜 H} {k : ℤ} {x : H} :
    x ∈ coordinateHalfSpace b k ↔ ∀ n : ℤ, n < k → ⟪b n, x⟫_𝕜 = 0 := by
  rw [mem_orthogonal_span]
  constructor
  · intro h n hn
    exact h (b n) ⟨n, hn, rfl⟩
  · rintro h _ ⟨n, hn, rfl⟩
    exact h n hn

omit [CompleteSpace H] in
/-- The orthogonal complement of a coordinate half-space kills every coordinate
at or above the cut. -/
theorem inner_eq_zero_of_mem_orthogonal_coordinateHalfSpace
    {b : HilbertBasis ℤ 𝕜 H} {k : ℤ} {x : H}
    (hx : x ∈ (coordinateHalfSpace b k)ᗮ) {n : ℤ} (hn : k ≤ n) :
    ⟪b n, x⟫_𝕜 = 0 := by
  have hle : Submodule.span 𝕜 (b '' {m : ℤ | m < k}) ≤
      (Submodule.span 𝕜 (b '' {m : ℤ | k ≤ m}))ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    refine mem_orthogonal_span.mpr ?_
    rintro _ ⟨p, hp, rfl⟩
    simp only [Set.mem_ofPred_eq] at hm hp
    exact b.orthonormal.2 (by omega)
  have hmono := Submodule.orthogonal_orthogonal_monotone hle
  rw [Submodule.triorthogonal_eq_orthogonal] at hmono
  exact mem_orthogonal_span.mp (hmono hx) (b n) ⟨n, hn, rfl⟩

omit [CompleteSpace H] in
/-- The later coordinate half-space sits inside the earlier one. -/
theorem coordinateHalfSpace_le_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H)
    {j k : ℤ} (hjk : j ≤ k) :
    coordinateHalfSpace b k ≤ coordinateHalfSpace b j := fun x hx =>
  mem_coordinateHalfSpace.mpr fun n hn =>
    mem_coordinateHalfSpace.mp hx n (by omega)

/-! ### The shift -/

omit [CompleteSpace H] in
/-- Shifting the index by one permutes a Hilbert basis, so the shifted family
has the same range. -/
theorem range_comp_add_one (b : HilbertBasis ℤ 𝕜 H) :
    Set.range (fun n : ℤ => b (n + 1)) = Set.range b := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n - 1, by simp⟩

/-- The Hilbert basis obtained from `b` by shifting the index by one. -/
noncomputable def shiftedBasis (b : HilbertBasis ℤ 𝕜 H) : HilbertBasis ℤ 𝕜 H :=
  HilbertBasis.mk (v := fun n : ℤ => b (n + 1))
    (b.orthonormal.comp (fun n : ℤ => n + 1) fun m n h => by simpa using h)
    (by
      rw [range_comp_add_one b]
      exact b.dense_span.ge)

/-- The shifted basis is the shift of the basis. -/
theorem shiftedBasis_apply (b : HilbertBasis ℤ 𝕜 H) (n : ℤ) :
    shiftedBasis b n = b (n + 1) :=
  congrFun (HilbertBasis.coe_mk _ _) n

/-- **The bilateral shift.**

The unitary carrying the `n`-th basis vector to the `(n+1)`-st; in sequence
coordinates this is `V (aₙ) = (bₙ)` with `bₙ = aₙ₋₁`. -/
noncomputable def bilateralShift (b : HilbertBasis ℤ 𝕜 H) : H ≃ₗᵢ[𝕜] H :=
  b.repr.trans (shiftedBasis b).repr.symm

/-- The bilateral shift moves each basis vector one step up. -/
theorem bilateralShift_apply_basis (b : HilbertBasis ℤ 𝕜 H) (n : ℤ) :
    bilateralShift b (b n) = b (n + 1) := by
  classical
  have h : (shiftedBasis b).repr.symm (b.repr (b n)) = shiftedBasis b n := by
    rw [b.repr_self]
    exact (shiftedBasis b).repr_symm_single n
  rw [bilateralShift, LinearIsometryEquiv.trans_apply, h, shiftedBasis_apply]

/-- The bilateral shift as a bounded operator. -/
noncomputable def bilateralShiftL (b : HilbertBasis ℤ 𝕜 H) : H →L[𝕜] H :=
  (bilateralShift b : H →L[𝕜] H)

/-- The bilateral shift is unitary. -/
theorem bilateralShiftL_mem_unitary (b : HilbertBasis ℤ 𝕜 H) :
    bilateralShiftL b ∈ unitary (H →L[𝕜] H) :=
  (Unitary.linearIsometryEquiv.symm (bilateralShift b)).property

/-- **The bilateral shift carries each coordinate half-space onto the next.** -/
theorem map_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    (coordinateHalfSpace b k).map
        ((bilateralShift b).toLinearEquiv : H →ₗ[𝕜] H) =
      coordinateHalfSpace b (k + 1) := by
  rw [Submodule.map_orthogonal_equiv, Submodule.map_span]
  congr 2
  ext x
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨n + 1, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hn ⊢
      omega
    · exact (bilateralShift_apply_basis b n).symm
  · rintro ⟨n, hn, rfl⟩
    refine ⟨b (n - 1), ⟨n - 1, ?_, rfl⟩, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hn ⊢
      omega
    · change (bilateralShift b) (b (n - 1)) = b n
      rw [bilateralShift_apply_basis, sub_add_cancel]

/-- **The shift intertwines the two projections.**

`V P = Q V`, with `P` the projector onto the cut at `k` and `Q` the projector
onto the cut at `k+1`.  This is the hypothesis printed as (1.4) in
Davis--Kahan 1970. -/
theorem bilateralShiftL_intertwines (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    bilateralShiftL b * Submodule.starProjection (coordinateHalfSpace b k) =
      Submodule.starProjection (coordinateHalfSpace b (k + 1)) * bilateralShiftL b := by
  ext y
  simp only [mul_apply_eq_comp]
  exact (starProjection_of_map_eq (bilateralShift b)
    (map_coordinateHalfSpace b k) y).symm

/-- **Consecutive coordinate half-spaces have the same ambient dimension data**,
in the cardinal-free form used throughout this development: the two subspaces
are isometrically equivalent, and so are their orthogonal complements.  This is
the hypothesis printed as (1.5) in Davis--Kahan 1970. -/
theorem coordinateHalfSpace_dimensions_agree (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    Nonempty (coordinateHalfSpace b k ≃ₗᵢ[𝕜] coordinateHalfSpace b (k + 1)) ∧
      Nonempty ((coordinateHalfSpace b k)ᗮ ≃ₗᵢ[𝕜]
        (coordinateHalfSpace b (k + 1))ᗮ) := by
  constructor
  · exact ⟨((bilateralShift b).submoduleMap (coordinateHalfSpace b k)).trans
      (LinearIsometryEquiv.ofEq _ _ (map_coordinateHalfSpace b k))⟩
  · refine ⟨((bilateralShift b).submoduleMap (coordinateHalfSpace b k)ᗮ).trans
      (LinearIsometryEquiv.ofEq _ _ ?_)⟩
    have h := Submodule.map_orthogonal_equiv (K := coordinateHalfSpace b k)
      (bilateralShift b)
    rw [map_coordinateHalfSpace] at h
    exact h

/-! ### The two crossed defects of the shift pair -/

omit [CompleteSpace H] in
/-- **The source crossed intersection of the shift pair is a line.**

`U ⊓ Vᗮ` is exactly the set of sequences supported at `n = 0`. -/
theorem halmosSourceDefect_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) :
    halmosSourceDefect (coordinateHalfSpace b 0) (coordinateHalfSpace b 1) =
      Submodule.span 𝕜 {b 0} := by
  apply le_antisymm
  · rintro x ⟨hxU, hxV⟩
    have hsupp : ∀ n : ℤ, n ≠ 0 → b.repr x n • b n = 0 := by
      intro n hn
      rcases lt_or_gt_of_ne hn with h | h
      · rw [b.repr_apply_apply, mem_coordinateHalfSpace.mp hxU n (by omega),
          zero_smul]
      · rw [b.repr_apply_apply,
          inner_eq_zero_of_mem_orthogonal_coordinateHalfSpace hxV (by omega),
          zero_smul]
    have hx : x = b.repr x 0 • b 0 :=
      (b.hasSum_repr x).unique (hasSum_single 0 hsupp)
    exact Submodule.mem_span_singleton.mpr ⟨b.repr x 0, hx.symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine mem_halmosSourceDefect.mpr
      ⟨mem_coordinateHalfSpace.mpr fun n hn => b.orthonormal.2 (by omega), ?_⟩
    exact Submodule.le_orthogonal_orthogonal _
      (Submodule.subset_span ⟨0, by norm_num, rfl⟩)

omit [CompleteSpace H] in
/-- **The source crossed intersection of the shift pair is nonzero.** -/
theorem halmosSourceDefect_coordinateHalfSpace_ne_bot (b : HilbertBasis ℤ 𝕜 H) :
    halmosSourceDefect (coordinateHalfSpace b 0) (coordinateHalfSpace b 1)
      ≠ ⊥ := by
  rw [halmosSourceDefect_coordinateHalfSpace]
  intro hbot
  have hb : b 0 = 0 := (Submodule.eq_bot_iff _).mp hbot (b 0)
    (Submodule.mem_span_singleton_self _)
  have hnorm : ‖b 0‖ = 0 := by rw [hb, norm_zero]
  rw [b.orthonormal.1 0] at hnorm
  exact one_ne_zero hnorm

omit [CompleteSpace H] in
/-- **The target crossed intersection of the shift pair is zero.**

`Uᗮ ⊓ V` is trivial. -/
theorem halmosTargetDefect_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) :
    halmosTargetDefect (coordinateHalfSpace b 0) (coordinateHalfSpace b 1) =
      ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨hxU, hxV⟩
  have hall : ∀ n : ℤ, b.repr x n = 0 := by
    intro n
    rw [b.repr_apply_apply]
    by_cases h : 0 ≤ n
    · exact inner_eq_zero_of_mem_orthogonal_coordinateHalfSpace hxU h
    · exact mem_coordinateHalfSpace.mp hxV n (by omega)
  have hrepr : b.repr x = 0 := by
    ext n
    simpa using hall n
  exact b.repr.injective (hrepr.trans (map_zero b.repr).symm)

/-- **The crossed-defect hypothesis fails for the shift pair.**

The two crossed intersections cannot be isometrically identified: one is a line
and the other is zero.  This is the failure of the condition printed as (3.5)
in Davis--Kahan 1970. -/
theorem not_crossedDefectsEquivalent_coordinateHalfSpace
    (b : HilbertBasis ℤ 𝕜 H) :
    ¬ CrossedDefectsEquivalent (coordinateHalfSpace b 0)
        (coordinateHalfSpace b 1) := by
  rintro ⟨J⟩
  have hb0 : b 0 ∈ halmosSourceDefect (coordinateHalfSpace b 0)
      (coordinateHalfSpace b 1) := by
    rw [halmosSourceDefect_coordinateHalfSpace]
    exact Submodule.mem_span_singleton_self _
  have hJz : J ⟨b 0, hb0⟩ = 0 :=
    Subtype.ext ((Submodule.eq_bot_iff _).mp
      (halmosTargetDefect_coordinateHalfSpace b) _ (J ⟨b 0, hb0⟩).2)
  have hnorm : ‖b 0‖ = 0 := by
    have h := J.norm_map ⟨b 0, hb0⟩
    rw [hJz, norm_zero] at h
    exact h.symm
  rw [b.orthonormal.1 0] at hnorm
  exact one_ne_zero hnorm

/-! ### The shift pair as a falsifier for the crossed-defect-qualified gap
identity -/

/-- **The shift pair refutes the crossed-defect-qualified gap identity when that
hypothesis is dropped.**

The two directed gaps of the shift pair are `1` and `0`: the source crossed
defect is the line `span {b 0}`, which pins `directedGap U V` at `1`, while
`V ≤ U` makes `directedGap V U` vanish.  So

* `directedGap_comm_of_crossedDefectsEquivalent` is false here -- its two sides
  are `1` and `0`; and
* `subspaceGap_eq_directedGap_of_crossedDefectsEquivalent`, read at the pair in
  the order `(V, U)`, asserts `1 = 0`.

Since the pair satisfies the ambient dimension hypothesis
(`coordinateHalfSpace_dimensions_agree`) and fails the crossed-defect
hypothesis (`not_crossedDefectsEquivalent_coordinateHalfSpace`), this is the
machine-checked statement that the crossed-defect hypothesis in those two
theorems is load-bearing and is not implied by the ambient dimension
hypothesis.

Read in the order `(U, V)` the symmetric identity happens to hold, because the
defect sits on the side that already realizes the maximum; the refutation is
therefore stated in the order that exposes it. -/
theorem directedGap_asymmetric_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) :
    Submodule.directedProjectionGap (coordinateHalfSpace b 0) (coordinateHalfSpace b 1) = 1 ∧
      Submodule.directedProjectionGap (coordinateHalfSpace b 1) (coordinateHalfSpace b 0) = 0 ∧
      Submodule.projectionGap (coordinateHalfSpace b 1) (coordinateHalfSpace b 0) ≠
        Submodule.directedProjectionGap (coordinateHalfSpace b 1) (coordinateHalfSpace b 0) := by
  have hone : Submodule.directedProjectionGap (coordinateHalfSpace b 0) (coordinateHalfSpace b 1)
    = 1 :=
    Submodule.directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot _ _
      (halmosSourceDefect_coordinateHalfSpace_ne_bot b)
  have hzero : Submodule.directedProjectionGap (coordinateHalfSpace b 1) (coordinateHalfSpace b 0)
    = 0 :=
    Submodule.directedProjectionGap_eq_zero_of_le
      (coordinateHalfSpace_le_coordinateHalfSpace b (by norm_num))
  refine ⟨hone, hzero, ?_⟩
  have hmax : Submodule.projectionGap (coordinateHalfSpace b 1) (coordinateHalfSpace b 0)
      = max (Submodule.directedProjectionGap (coordinateHalfSpace b 1) (coordinateHalfSpace b 0))
        (Submodule.directedProjectionGap (coordinateHalfSpace b 0) (coordinateHalfSpace b 1)) :=
    Submodule.projectionGap_eq_max_directedProjectionGap _ _
  rw [hmax, hone, hzero]
  norm_num

end BilateralShift

end DavisKahan
end TauCeti
