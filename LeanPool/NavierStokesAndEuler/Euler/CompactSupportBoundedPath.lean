/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! Continuous families with a common compact spatial support give continuous paths in the
space of bounded continuous functions, equipped with the uniform norm. -/

@[expose] public section


open Set Filter Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace EulerComparator

variable {A E V : Type*} [TopologicalSpace A] [TopologicalSpace E]
  [NormedAddCommGroup V]

/-- A continuous, compactly supported function, regarded as a bounded continuous function. -/
def boundedOfCompactSupport (f : E → V) (hf : Continuous f)
    (hs : HasCompactSupport f) : E →ᵇ V where
  toFun := f
  continuous_toFun := hf
  map_bounded' := Metric.isBounded_range_iff.mp (hs.isCompact_range hf).isBounded

@[simp] theorem boundedOfCompactSupport_apply (f : E → V) (hf : Continuous f)
    (hs : HasCompactSupport f) (x : E) : boundedOfCompactSupport f hf hs x = f x := rfl

/-- Uniformly compact spatial support upgrades joint continuity to continuity in the
bounded-continuous-function norm. No compactness assumption on the parameter space is needed. -/
theorem continuous_boundedOfCompactSupport
    (u : A × E → V) (hu : Continuous u) (K : Set E) (hK : IsCompact K)
    (hs : ∀ t, tsupport (fun x => u (t, x)) ⊆ K) :
    Continuous (fun t => boundedOfCompactSupport (fun x => u (t, x))
      (hu.comp (continuous_const.prodMk continuous_id))
      (hK.of_isClosed_subset (isClosed_tsupport _) (hs t))) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨U, hU, hclose⟩ := hK.mem_uniformity_of_prod
    (f := fun t x => u (t, x)) (s := Set.univ) hu.continuousOn
    (Set.mem_univ t) (Metric.dist_mem_uniformity hε2)
  rw [nhdsWithin_univ] at hU
  filter_upwards [hU] with s hsU
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.dist_le hε2.le).mpr
  intro x
  change dist (u (s, x)) (u (t, x)) ≤ ε / 2
  by_cases hx : x ∈ K
  · exact (hclose s hsU x hx).le
  · have hsx : u (s, x) = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y => u (s, y)) (fun h => hx (hs s h))
    have htx : u (t, x) = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y => u (t, y)) (fun h => hx (hs t h))
    simpa [hsx, htx] using hε2.le

/-- A continuous family with one common compact spatial support, bundled as a continuous
path of bounded continuous functions. -/
def compactSupportBoundedPath
    (u : A × E → V) (hu : Continuous u) (K : Set E) (hK : IsCompact K)
    (hs : ∀ t, tsupport (fun x => u (t, x)) ⊆ K) : C(A, E →ᵇ V) where
  toFun t := boundedOfCompactSupport (fun x => u (t, x))
    (hu.comp (continuous_const.prodMk continuous_id))
    (hK.of_isClosed_subset (isClosed_tsupport _) (hs t))
  continuous_toFun := continuous_boundedOfCompactSupport u hu K hK hs

@[simp] theorem compactSupportBoundedPath_apply
    (u : A × E → V) (hu : Continuous u) (K : Set E) (hK : IsCompact K)
    (hs : ∀ t, tsupport (fun x => u (t, x)) ⊆ K) (t : A) (x : E) :
    compactSupportBoundedPath u hu K hK hs t x = u (t, x) := rfl

end EulerComparator
