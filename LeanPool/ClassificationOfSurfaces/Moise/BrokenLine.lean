/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Thickening
import LeanPool.ClassificationOfSurfaces.Moise.PlaneComplex

/-!
# Broken-line connectivity of open connected sets in the plane

Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 1: any two points of an open connected
subset of the plane are joined by a broken line (a finite polygonal chain of straight segments)
lying in the set.  This is the elementary input to the PL-approximation chapter (Thm 6.1); see
the docstrings of `ClassificationOfSurfaces/Moise/PLApproximation.lean` for the wider context.

`JoinedByBrokenLine U a b` records a chain of `n` segments inside `U` from `a` to `b`, as a
vertex list `v : Fin (n + 1) → Plane` whose consecutive closed segments all lie in `U`.  The
relation is reflexive (at points of `U`), symmetric, transitive, and monotone in `U`.

The main theorem `IsPreconnected.joinedByBrokenLine` is the standard clopen-chain argument:
for fixed `a`, both `{x ∈ U | JoinedByBrokenLine U a x}` and its complement in `U` are open,
because any metric ball inside `U` is convex, so the segment from a ball's centre to any of its
points extends or truncates a broken line by one segment.  Preconnectedness of `U` then forces
the complement to be empty.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- `a` and `b` are joined by a broken line inside `U`: there is a finite chain of vertices
starting at `a` and ending at `b` such that every consecutive closed segment lies in `U`. -/
def JoinedByBrokenLine (U : Set Plane) (a b : Plane) : Prop :=
  ∃ (n : ℕ) (v : Fin (n + 1) → Plane), v 0 = a ∧ v (Fin.last n) = b ∧
    ∀ i : Fin n, segment ℝ (v i.castSucc) (v i.succ) ⊆ U

namespace JoinedByBrokenLine

/-- A single segment inside `U` is a broken line. -/
theorem of_segment {U : Set Plane} {a b : Plane} (h : segment ℝ a b ⊆ U) :
    JoinedByBrokenLine U a b :=
  ⟨1, ![a, b], rfl, rfl, fun i => by fin_cases i; simpa using h⟩

/-- Any point of `U` is joined to itself by a (degenerate) broken line in `U`. -/
protected theorem refl {U : Set Plane} {a : Plane} (ha : a ∈ U) :
    JoinedByBrokenLine U a a :=
  of_segment (by rw [segment_same]; exact Set.singleton_subset_iff.2 ha)

/-- Broken-line connectivity is symmetric: traverse the chain backwards. -/
protected theorem symm {U : Set Plane} {a b : Plane} (h : JoinedByBrokenLine U a b) :
    JoinedByBrokenLine U b a := by
  obtain ⟨n, v, hv0, hvl, hvseg⟩ := h
  refine ⟨n, fun i => v i.rev, ?_, ?_, fun i => ?_⟩
  · simp only [Fin.rev_zero]
    exact hvl
  · simp only [Fin.rev_last]
    exact hv0
  · simp only [Fin.rev_castSucc, Fin.rev_succ]
    rw [segment_symm]
    exact hvseg i.rev

/-- Extend a broken line from `a` to `b` by one further segment from `b` to `c` inside `U`. -/
theorem snoc {U : Set Plane} {a b c : Plane} (hab : JoinedByBrokenLine U a b)
    (hseg : segment ℝ b c ⊆ U) : JoinedByBrokenLine U a c := by
  obtain ⟨n, v, hv0, hvl, hvseg⟩ := hab
  refine ⟨n + 1, Fin.snoc v c, ?_, Fin.snoc_last _ _, fun i => ?_⟩
  · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, hv0]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_castSucc, hvl, Fin.succ_last, Fin.snoc_last]
      exact hseg
    · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hvseg j

/-- Broken-line connectivity is transitive: concatenate the two chains. -/
protected theorem trans {U : Set Plane} {a b c : Plane} (hab : JoinedByBrokenLine U a b)
    (hbc : JoinedByBrokenLine U b c) : JoinedByBrokenLine U a c := by
  have aux : ∀ m (w : Fin (m + 1) → Plane), w 0 = b →
      (∀ i : Fin m, segment ℝ (w i.castSucc) (w i.succ) ⊆ U) →
      JoinedByBrokenLine U a (w (Fin.last m)) := by
    intro m
    induction m with
    | zero =>
      intro w hw0 _
      rw [Fin.last_zero, hw0]
      exact hab
    | succ m ih =>
      intro w hw0 hwseg
      have h1 : JoinedByBrokenLine U a (w (Fin.last m).castSucc) :=
        ih (fun j => w j.castSucc)
          (by simp only [Fin.castSucc_zero]; exact hw0)
          (fun j => by
            simp only [← Fin.succ_castSucc]
            exact hwseg j.castSucc)
      have h2 := h1.snoc (hwseg (Fin.last m))
      rwa [Fin.succ_last] at h2
  obtain ⟨m, w, hw0, hwl, hwseg⟩ := hbc
  have h := aux m w hw0 hwseg
  rwa [hwl] at h

/-- Transport a broken line along an inclusion `U ⊆ V`. -/
theorem mono {U V : Set Plane} {a b : Plane} (h : JoinedByBrokenLine U a b) (hUV : U ⊆ V) :
    JoinedByBrokenLine V a b := by
  obtain ⟨n, v, hv0, hvl, hvseg⟩ := h
  exact ⟨n, v, hv0, hvl, fun i => (hvseg i).trans hUV⟩

end JoinedByBrokenLine

/-- **Broken-line connectivity** (Moise, Ch. 1): any two points of an open preconnected subset
of the plane are joined by a broken line lying in the set. -/
theorem IsPreconnected.joinedByBrokenLine {U : Set Plane} (hU : IsOpen U)
    (hconn : IsPreconnected U) {a b : Plane} (ha : a ∈ U) (hb : b ∈ U) :
    JoinedByBrokenLine U a b := by
  classical
  -- The set of points of `U` joined to `a`, and its complement in `U`.
  set W : Set Plane := {x | x ∈ U ∧ JoinedByBrokenLine U a x} with hW
  set W' : Set Plane := {x | x ∈ U ∧ ¬JoinedByBrokenLine U a x} with hW'
  -- `W` is open: a ball around `x ∈ W` inside `U` is convex, so each of its points is joined
  -- to `x` by a single segment in `U`, hence to `a`.
  have hWopen : IsOpen W := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxJ⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
    refine ⟨ε, hε, fun y hy => ⟨hball hy, hxJ.trans (.of_segment ?_)⟩⟩
    exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) hy).trans hball
  -- `W'` is open: if some point of a convex ball around `x ∈ W'` inside `U` were joined to
  -- `a`, then so would `x` be, via one more segment in the ball.
  have hW'open : IsOpen W' := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxN⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
    refine ⟨ε, hε, fun y hy => ⟨hball hy, fun hyJ => hxN (hyJ.trans (.of_segment ?_))⟩⟩
    exact ((convex_ball x ε).segment_subset hy (Metric.mem_ball_self hε)).trans hball
  -- Apply preconnectedness to the open cover `W ∪ W'` of `U`.
  by_contra hbN
  have hsub : U ⊆ W ∪ W' := fun x hx => by
    by_cases hx' : JoinedByBrokenLine U a x
    · exact Or.inl ⟨hx, hx'⟩
    · exact Or.inr ⟨hx, hx'⟩
  have hne : (U ∩ W).Nonempty := ⟨a, ha, ha, .refl ha⟩
  have hne' : (U ∩ W').Nonempty := ⟨b, hb, hb, hbN⟩
  obtain ⟨x, -, ⟨-, hxJ⟩, ⟨-, hxN⟩⟩ := hconn W W' hWopen hW'open hsub hne hne'
  exact hxN hxJ

/-- A positive metric thickening of a preconnected plane set is preconnected. -/
theorem IsPreconnected.thickening {A : Set Plane} (hA : IsPreconnected A)
    {ε : ℝ} (_ : 0 < ε) : IsPreconnected (Metric.thickening ε A) := by
  let add : Plane × Plane → Plane := fun p => p.1 + p.2
  have hball : IsPreconnected (Metric.ball (0 : Plane) ε) :=
    (convex_ball (0 : Plane) ε).isPreconnected
  have hprod : IsPreconnected (A ×ˢ Metric.ball (0 : Plane) ε) :=
    IsPreconnected.prod hA hball
  have hadd : Continuous add := continuous_fst.add continuous_snd
  have himage : add '' (A ×ˢ Metric.ball 0 ε) = Metric.thickening ε A := by
    rw [Metric.thickening_eq_biUnion_ball]
    ext x
    simp only [Set.mem_image, Set.mem_prod, Metric.mem_ball, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨a, v⟩, ⟨ha, hv⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      simpa [add, dist_eq_norm] using hv
    · rintro ⟨a, ha, hxa⟩
      refine ⟨(a, x - a), ⟨ha, ?_⟩, ?_⟩
      · simpa [dist_eq_norm] using hxa
      · simp [add]
  rw [← himage]
  exact IsPreconnected.image hprod add hadd.continuousOn

/-- Moise Chapter 6, Theorem 1: the endpoints of an embedded edge can be joined by a broken
line in every positive metric neighborhood of its image. -/
theorem brokenLine_in_thickening_of_preconnected {A : Set Plane}
    (hA : IsPreconnected A) {a b : Plane} (ha : a ∈ A) (hb : b ∈ A)
    {ε : ℝ} (hε : 0 < ε) :
    JoinedByBrokenLine (Metric.thickening ε A) a b := by
  apply IsPreconnected.joinedByBrokenLine Metric.isOpen_thickening
    (IsPreconnected.thickening hA hε)
  · exact Metric.self_subset_thickening hε A ha
  · exact Metric.self_subset_thickening hε A hb

/-- A preconnected set admits broken-line approximations whose vertices stay in its convex hull.

The thickening supplies room for the polygonal chain, while convex-hull containment records the
extra fact needed to preserve convex target regions such as a half-plane. -/
theorem brokenLine_in_thickening_inter_convexHull_of_preconnected {A : Set Plane}
    (hA : IsPreconnected A) {a b : Plane} (ha : a ∈ A) (hb : b ∈ A)
    {ε : ℝ} (hε : 0 < ε) :
    JoinedByBrokenLine (Metric.thickening ε A ∩ convexHull ℝ A) a b := by
  let U := Metric.thickening ε A ∩ convexHull ℝ A
  apply hA.induction₂ (fun x y => JoinedByBrokenLine U x y)
  · intro x hx
    filter_upwards [inter_mem_nhdsWithin A (Metric.ball_mem_nhds x hε)] with y hy
    apply JoinedByBrokenLine.of_segment
    intro z hz
    refine ⟨?_, segment_subset_convexHull hx hy.1 hz⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    exact (convex_ball x ε).segment_subset (Metric.mem_ball_self hε) hy.2 hz
  · intro x y z _ _ _ hxy hyz
    exact hxy.trans hyz
  · intro x y _ _ hxy
    exact hxy.symm
  · exact ha
  · exact hb

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
