/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt

/-!
# Hartogs sets and their fibers

The product `E × ℂ` specifies a base and a distinguished complex fiber coordinate. `IsHartogs`
is rotational invariance in that coordinate; `IsCompleteHartogs` also allows contraction toward
zero. Openness, nonemptiness and connectedness of the total set are separate assumptions.
`HasPreconnectedFibers` is a further, independent property: empty fibers are allowed, and every
nonempty fiber is then connected.

Complete Hartogs sets have star-convex, hence preconnected, fibers. Their base is exactly their
zero section. No symmetry or contraction in the base is required. To change the fiber center to
`a`, apply the predicates to `{p | (p.1, a + p.2) ∈ U}`.

References: [Shabat][Shabat1991] (1991), I §1.2, pp. 9–10; [Range][Range1986] (1986), Chapter I,
E.1.10 and E.5.5. Hartogs series are treated separately in `HartogsSeries`.

## Main definitions

* `hartogsFiber`: The complex fiber of a set over a specified base point.
* `hartogsBase`: The base consists of the points with nonempty fiber.
* `IsHartogs`: Hartogs symmetry is invariance under rotations of the fiber coordinate about zero.
* `IsCompleteHartogs`: Complete Hartogs sets also contain every smaller fiber modulus, including
  zero.
* `HasPreconnectedFibers`: Each fiber is preconnected.

## Main results

* `IsCompleteHartogs.isHartogs`: Complete Hartogs sets have Hartogs symmetry.
* `IsCompleteHartogs.hasPreconnectedFibers`: Complete Hartogs sets have preconnected fibers; empty
  fibers need no exception.
* `hasPreconnectedFibers_iff`: Preconnected fibers are equivalently connected fibers at every point
  of the base.
* `IsReinhardt.isHartogs_option`: Selecting the `none` coordinate in a Reinhardt set gives Hartogs
  symmetry.
* `IsCompleteReinhardt.isCompleteHartogs_option`: Selecting the `none` coordinate in a complete
  Reinhardt set gives complete Hartogs.
* `isOpen_hartogsBase`: The base of an open set in a product is open.
* `isPreconnected_hartogsBase`: The base of a preconnected set is preconnected.

## References

* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [B. V. Shabat, *Introduction to Complex Analysis, Part II: Functions of Several
  Variables*][Shabat1991]
-/

public section

open Set

namespace SeveralComplexVariables

variable {E E' : Type*} {U V : Set (E × ℂ)}

/-- The complex fiber of a set over a specified base point. -/
@[expose] def hartogsFiber (U : Set (E × ℂ)) (z : E) : Set ℂ :=
  {w | (z, w) ∈ U}

/-- The base consists of the points with nonempty fiber. -/
@[expose] def hartogsBase (U : Set (E × ℂ)) : Set E := Prod.fst '' U

/-- Hartogs symmetry is invariance under rotations of the fiber coordinate about zero. -/
@[expose] def IsHartogs (U : Set (E × ℂ)) : Prop :=
  ∀ ⦃z w⦄, (z, w) ∈ U → ∀ ⦃v⦄, ‖v‖ = ‖w‖ → (z, v) ∈ U

/-- Complete Hartogs sets also contain every smaller fiber modulus, including zero. -/
@[expose] def IsCompleteHartogs (U : Set (E × ℂ)) : Prop :=
  ∀ ⦃z w⦄, (z, w) ∈ U → ∀ ⦃v⦄, ‖v‖ ≤ ‖w‖ → (z, v) ∈ U

/-- Each fiber is preconnected. Equivalently, every nonempty fiber is connected. This does not
require Hartogs symmetry, openness, or connectedness of the total set. -/
@[expose] def HasPreconnectedFibers (U : Set (E × ℂ)) : Prop :=
  ∀ z, IsPreconnected (hartogsFiber U z)

/-- Membership in the base is equivalent to nonemptiness of the fiber. -/
theorem mem_hartogsBase_iff {z : E} : z ∈ hartogsBase U ↔ (hartogsFiber U z).Nonempty := by
  constructor
  · rintro ⟨⟨x, w⟩, hw, rfl⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨(z, w), hw, rfl⟩

/-- The empty set has Hartogs symmetry. -/
@[simp] theorem isHartogs_empty : IsHartogs (∅ : Set (E × ℂ)) :=
  fun _ _ h => h.elim

/-- The whole product has Hartogs symmetry. -/
@[simp] theorem isHartogs_univ : IsHartogs (univ : Set (E × ℂ)) :=
  fun _ _ _ _ _ => mem_univ _

/-- The empty set is complete Hartogs. -/
@[simp] theorem isCompleteHartogs_empty : IsCompleteHartogs (∅ : Set (E × ℂ)) :=
  fun _ _ h => h.elim

/-- The whole product is complete Hartogs. -/
@[simp] theorem isCompleteHartogs_univ : IsCompleteHartogs (univ : Set (E × ℂ)) :=
  fun _ _ _ _ _ => mem_univ _

/-- Complete Hartogs sets have Hartogs symmetry. -/
theorem IsCompleteHartogs.isHartogs (hU : IsCompleteHartogs U) : IsHartogs U :=
  fun _ _ hw _ hv => hU hw hv.le

/-- Intersections preserve Hartogs symmetry. -/
theorem IsHartogs.inter (hU : IsHartogs U) (hV : IsHartogs V) : IsHartogs (U ∩ V) :=
  fun _ _ hw _ hv => ⟨hU hw.1 hv, hV hw.2 hv⟩

/-- Unions preserve Hartogs symmetry, without requiring connected fibers. -/
theorem IsHartogs.union (hU : IsHartogs U) (hV : IsHartogs V) : IsHartogs (U ∪ V) :=
  fun _ _ hw _ hv => hw.elim (fun h => Or.inl (hU h hv)) (fun h => Or.inr (hV h hv))

/-- Intersections preserve the complete Hartogs property. -/
theorem IsCompleteHartogs.inter (hU : IsCompleteHartogs U) (hV : IsCompleteHartogs V) :
    IsCompleteHartogs (U ∩ V) :=
  fun _ _ hw _ hv => ⟨hU hw.1 hv, hV hw.2 hv⟩

/-- Unions preserve the complete Hartogs property. -/
theorem IsCompleteHartogs.union (hU : IsCompleteHartogs U) (hV : IsCompleteHartogs V) :
    IsCompleteHartogs (U ∪ V) :=
  fun _ _ hw _ hv => hw.elim (fun h => Or.inl (hU h hv)) (fun h => Or.inr (hV h hv))

/-- Any change of base preserves Hartogs symmetry. -/
theorem IsHartogs.preimage_base (hU : IsHartogs U) (g : E' → E) :
    IsHartogs {p : E' × ℂ | (g p.1, p.2) ∈ U} :=
  fun _ _ hw _ hv => hU hw hv

/-- Any change of base preserves the complete Hartogs property. -/
theorem IsCompleteHartogs.preimage_base (hU : IsCompleteHartogs U) (g : E' → E) :
    IsCompleteHartogs {p : E' × ℂ | (g p.1, p.2) ∈ U} :=
  fun _ _ hw _ hv => hU hw hv

/-- Multiplication of a fiber coordinate by a unit-modulus scalar preserves membership. -/
theorem IsHartogs.mul_mem (hU : IsHartogs U) {z : E} {w a : ℂ}
    (hw : (z, w) ∈ U) (ha : ‖a‖ = 1) : (z, a * w) ∈ U :=
  hU hw (by simp [ha])

/-- Multiplication of a fiber coordinate by a complex contraction preserves membership. -/
theorem IsCompleteHartogs.mul_mem (hU : IsCompleteHartogs U) {z : E} {w a : ℂ}
    (hw : (z, w) ∈ U) (ha : ‖a‖ ≤ 1) : (z, a * w) ∈ U := by
  apply hU hw
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ha

/-- Every nonempty fiber of a complete Hartogs set contains zero. -/
theorem IsCompleteHartogs.zero_mem_fiber (hU : IsCompleteHartogs U) {z : E}
    (hz : z ∈ hartogsBase U) : (z, 0) ∈ U := by
  obtain ⟨w, hw⟩ := mem_hartogsBase_iff.mp hz
  exact hU hw (by simp)

/-- The base of a complete Hartogs set equals its zero section. -/
theorem IsCompleteHartogs.mem_base_iff (hU : IsCompleteHartogs U) {z : E} :
    z ∈ hartogsBase U ↔ (z, 0) ∈ U :=
  ⟨hU.zero_mem_fiber, fun hz => mem_hartogsBase_iff.mpr ⟨0, hz⟩⟩

/-- Fibers of a complete Hartogs set are star-convex about zero, including empty fibers. -/
theorem IsCompleteHartogs.starConvex_fiber (hU : IsCompleteHartogs U) (z : E) :
    StarConvex ℝ 0 (hartogsFiber U z) := by
  intro w hw a b ha hb hab
  simp only [smul_zero, zero_add]
  apply hU hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- Nonempty fibers of complete Hartogs sets are path connected. -/
theorem IsCompleteHartogs.isPathConnected_fiber (hU : IsCompleteHartogs U) {z : E}
    (hz : z ∈ hartogsBase U) : IsPathConnected (hartogsFiber U z) :=
  (hU.starConvex_fiber z).isPathConnected (hU.zero_mem_fiber hz)

/-- Complete Hartogs sets have preconnected fibers; empty fibers need no exception. -/
theorem IsCompleteHartogs.hasPreconnectedFibers (hU : IsCompleteHartogs U) :
    HasPreconnectedFibers U := by
  intro z
  rcases (hartogsFiber U z).eq_empty_or_nonempty with h | h
  · rw [h]
    exact isPreconnected_empty
  · exact (hU.isPathConnected_fiber (mem_hartogsBase_iff.mpr h)).isConnected.isPreconnected

/-- Fiber preconnectedness gives connectedness at every point of the projected base. -/
theorem HasPreconnectedFibers.isConnected_fiber (hU : HasPreconnectedFibers U) {z : E}
    (hz : z ∈ hartogsBase U) : IsConnected (hartogsFiber U z) :=
  ⟨mem_hartogsBase_iff.mp hz, hU z⟩

/-- Preconnected fibers are equivalently connected fibers at every point of the base. -/
theorem hasPreconnectedFibers_iff : HasPreconnectedFibers U ↔
    ∀ z ∈ hartogsBase U, IsConnected (hartogsFiber U z) := by
  constructor
  · exact fun h _ hz => h.isConnected_fiber hz
  · intro h z
    rcases (hartogsFiber U z).eq_empty_or_nonempty with hz | hz
    · rw [hz]
      exact isPreconnected_empty
    · exact (h z (mem_hartogsBase_iff.mpr hz)).isPreconnected

/-- Products with centered discs are complete Hartogs, with no condition on the base. -/
theorem isCompleteHartogs_prod_ball (B : Set E) (r : ℝ) :
    IsCompleteHartogs (B ×ˢ Metric.ball (0 : ℂ) r) := by
  intro z w hw v hv
  refine ⟨hw.1, ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right] using
    hv.trans_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hw.2)

/-- Products with centered annuli have Hartogs symmetry, including degenerate annuli. -/
theorem isHartogs_prod_annulus (B : Set E) (r R : ℝ) :
    IsHartogs (B ×ˢ {w : ℂ | r < ‖w‖ ∧ ‖w‖ < R}) := by
  intro z w hw v hv
  exact ⟨hw.1, by simpa only [mem_ofPred_eq, hv] using hw.2⟩

/-- Selecting the `none` coordinate in a Reinhardt set gives Hartogs symmetry. -/
theorem IsReinhardt.isHartogs_option {ι : Type*} {S : Set (Option ι → ℂ)}
    (hS : IsReinhardt S) :
    IsHartogs {p : (ι → ℂ) × ℂ | (fun i => i.elim p.2 p.1) ∈ S} := by
  intro z w hw v hv
  apply hS hw
  intro i
  cases i with
  | none => exact hv
  | some i => rfl

/-- Selecting the `none` coordinate in a complete Reinhardt set gives complete Hartogs. -/
theorem IsCompleteReinhardt.isCompleteHartogs_option {ι : Type*}
    {S : Set (Option ι → ℂ)} (hS : IsCompleteReinhardt S) :
    IsCompleteHartogs {p : (ι → ℂ) × ℂ | (fun i => i.elim p.2 p.1) ∈ S} := by
  intro z w hw v hv
  apply hS hw
  intro i
  cases i with
  | none => exact hv
  | some i => exact le_rfl

section Topology

variable [TopologicalSpace E]

/-- The base of an open set in a product is open. -/
theorem isOpen_hartogsBase (hU : IsOpen U) : IsOpen (hartogsBase U) :=
  isOpenMap_fst U hU

/-- Fibers of an open set in a product are open. -/
theorem isOpen_hartogsFiber (hU : IsOpen U) (z : E) : IsOpen (hartogsFiber U z) :=
  hU.preimage (continuous_const.prodMk continuous_id)

/-- The base of a preconnected set is preconnected. -/
theorem isPreconnected_hartogsBase (hU : IsPreconnected U) :
    IsPreconnected (hartogsBase U) :=
  hU.image _ continuous_fst.continuousOn

end Topology

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
