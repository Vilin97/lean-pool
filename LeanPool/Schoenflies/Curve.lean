/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Plane
public import Mathlib.Topology.UnitInterval

/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

public section

open Set unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-- A simple arc: the image of a continuous injective map on `[0, 1]`. -/
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A

/-- An arc between two named points: the set-level reading, and the form gluing and cutting
are stated in. -/
def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

/-- A loop: continuous on `[0, 1]`, returning to its start, and injective before it does. -/
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : InjOn f (Ico 0 1)

/-- A Jordan curve: the image of a loop. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

/-! ### The unit interval, as a subset of `ℝ` -/

theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_refl 0, zero_le_one⟩

theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_refl 1⟩

theorem isCompact_I : IsCompact I := isCompact_Icc

theorem isConnected_I : IsConnected I := isConnected_Icc zero_le_one

/-- The image of a relatively closed piece of the parameter interval is compact. This is
what makes a parametrisation a closed map onto its arc, and hence its inverse continuous. -/
theorem isCompact_image_of_subset_I {f : ℝ → Plane} (hf : ContinuousOn f I)
    {S : Set ℝ} (hS : S ⊆ I) (hSc : IsClosed S) : IsCompact (f '' S) :=
  (isCompact_I.of_isClosed_subset hSc hS).image_of_continuousOn (hf.mono hS)

/-! ### Elementary properties -/

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

theorem isArc (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hc, hi, him, -, -⟩ := h
  exact ⟨f, hc, hi, him⟩

theorem left_mem (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, -, rfl, rfl, -⟩ := h
  exact mem_image_of_mem f zero_mem_I

theorem right_mem (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, -, rfl, -, rfl⟩ := h
  exact mem_image_of_mem f one_mem_I

/-- Running a piece the other way round. -/
theorem reverse (h : IsArcBetween A p q) : IsArcBetween A q p := by
  obtain ⟨f, hc, hi, him, hp, hq⟩ := h
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, by simpa using hq, by simpa using hp⟩
  · -- `t ↦ 1 - t` maps the interval to itself, continuously.
    refine hc.comp (by fun_prop) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have hs' : 1 - s ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hi hs' ht' hst
    linarith
  · rw [← him]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

end IsArcBetween

namespace IsArc

variable {A : Set Plane}

theorem isCompact (h : IsArc A) : IsCompact A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hc

theorem isConnected (h : IsArc A) : IsConnected A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isConnected_I.image f hc

theorem nonempty (h : IsArc A) : A.Nonempty := h.isConnected.nonempty

theorem isClosed (h : IsArc A) : IsClosed A := h.isCompact.isClosed

/-- Every arc is an arc between its two endpoints. -/
theorem exists_isArcBetween (h : IsArc A) : ∃ p q, IsArcBetween A p q := by
  obtain ⟨f, hc, hi, him⟩ := h
  exact ⟨f 0, f 1, f, hc, hi, him, rfl, rfl⟩

end IsArc

namespace IsJordanCurve

variable {C : Set Plane}

theorem isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hf.continuousOn

theorem isConnected (h : IsJordanCurve C) : IsConnected C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isConnected_I.image f hf.continuousOn

theorem nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

theorem isClosed (h : IsJordanCurve C) : IsClosed C := h.isCompact.isClosed

end IsJordanCurve

end Schoenflies
