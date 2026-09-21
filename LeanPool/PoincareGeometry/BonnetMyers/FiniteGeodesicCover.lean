/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.GlobalGeodesic

/-!
# Finite local-geodesic covers

The global extension construction stores a geodesic as compatible local
tangent-bundle-state germs.  On a compact time interval those germs admit a
finite subcover.  This module records that compactness step explicitly: each
chosen local geodesic carries a certified state-agreement neighbourhood, and
the finite family covers every time in the interval.

The result is deliberately a cover, not a claimed global parallel transport
or a smooth minimizing segment.  It is the finite chartwise datum needed
before either construction can be glued rigorously.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

namespace IntrinsicGeodesic
namespace GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- A finite family of local geodesic germs which covers a closed time
interval of a global geodesic.  The state equality deliberately lives in the
tangent-bundle total space, so it identifies both the base curve and its
actual tangent velocity across every selected local chart. -/
structure FiniteLocalGeodesicCover
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (a b : ℝ) where
  centers : Finset ℝ
  localGeodesic : ∀ t : {s : ℝ // s ∈ centers},
    LocalGeodesic (I := I) (M := M) cov (curve γ t.1) (velocity γ t.1)
  radius : {s : ℝ // s ∈ centers} → ℝ
  radius_pos : ∀ t, 0 < radius t
  radius_le_local_radius : ∀ t, radius t ≤ (localGeodesic t).solution.radius
  state_agrees : ∀ (t : {s : ℝ // s ∈ centers}) (s : ℝ),
    s - t.1 ∈ Metric.ball (0 : ℝ) (radius t) →
      γ.state s = localState (localGeodesic t) (s - t.1)
  covers : ∀ s ∈ Icc a b, ∃ t : {q : ℝ // q ∈ centers},
    s - t.1 ∈ Metric.ball (0 : ℝ) (radius t)

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)] in
/-- Each membership certificate of a finite cover lies inside the natural
ODE interval of the corresponding local geodesic.  Thus downstream local
curve, velocity, and parallel-field facts may be used at every covered time
without silently leaving the local solution's domain. -/
theorem FiniteLocalGeodesicCover.localTime_mem_solutionDomain
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    {t : {q : ℝ // q ∈ C.centers}} {s : ℝ}
    (hs : s - t.1 ∈ Metric.ball (0 : ℝ) (C.radius t)) :
    s - t.1 ∈ Ioo (-(C.localGeodesic t).solution.radius)
      (C.localGeodesic t).solution.radius := by
  have habs : |s - t.1| < C.radius t := by
    simpa [Real.dist_eq] using hs
  rcases abs_lt.mp habs with ⟨hleft, hright⟩
  exact ⟨lt_of_le_of_lt (neg_le_neg (C.radius_le_local_radius t)) hleft,
    lt_of_lt_of_le hright (C.radius_le_local_radius t)⟩

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)] in
/-- On every selected cover neighbourhood, the local geodesic's base curve
is literally the global geodesic curve after the certified time shift. -/
theorem FiniteLocalGeodesicCover.curve_eq_of_mem
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {a b : ℝ}
    (C : FiniteLocalGeodesicCover (I := I) (M := M) γ a b)
    (t : {q : ℝ // q ∈ C.centers}) (s : ℝ)
    (hs : s - t.1 ∈ Metric.ball (0 : ℝ) (C.radius t)) :
    curve γ s = LocalGeodesic.curve (C.localGeodesic t) (s - t.1) := by
  have hstate := C.state_agrees t s hs
  exact congrArg Bundle.TotalSpace.proj hstate

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)] in
/-- Every finite time interval of a global geodesic is covered by finitely
many certified local geodesic state germs.  The proof uses only the local
germs stored in `GlobalGeodesic` and compactness of `Icc a b`; it introduces
no global chart, transport, or minimization assumption. -/
theorem exists_finiteLocalGeodesicCover
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (a b : ℝ) :
    Nonempty (FiniteLocalGeodesicCover (I := I) (M := M) γ a b) := by
  classical
  choose α hα using γ.local_germ
  have hsmall : ∀ t : ℝ, ∃ r > (0 : ℝ),
      Metric.ball (0 : ℝ) r ⊆
        {s | γ.state (t + s) = localState (α t) s} := by
    intro t
    exact Metric.mem_nhds_iff.mp (hα t)
  choose δ hδ hδlocal using hsmall
  let r : ℝ → ℝ := fun t ↦ min (δ t) (α t).solution.radius
  have hr : ∀ t : ℝ, 0 < r t := by
    intro t
    exact lt_min (hδ t) (α t).solution.radius_pos
  have hrδ : ∀ t : ℝ, r t ≤ δ t := by
    intro t
    exact min_le_left _ _
  have hrlocalRadius : ∀ t : ℝ, r t ≤ (α t).solution.radius := by
    intro t
    exact min_le_right _ _
  have hlocal : ∀ t : ℝ, Metric.ball (0 : ℝ) (r t) ⊆
      {s | γ.state (t + s) = localState (α t) s} := by
    intro t s hs
    apply hδlocal t
    exact lt_of_lt_of_le hs (hrδ t)
  let U : ℝ → Set ℝ := fun t ↦
    (fun s : ℝ ↦ s - t) ⁻¹' Metric.ball (0 : ℝ) (r t)
  have hUopen : ∀ t : ℝ, IsOpen (U t) := by
    intro t
    exact IsOpen.preimage (continuous_id.sub continuous_const) Metric.isOpen_ball
  have hUcover : Icc a b ⊆ ⋃ t : ℝ, U t := by
    intro s hs
    refine mem_iUnion.2 ⟨s, ?_⟩
    change s - s ∈ Metric.ball (0 : ℝ) (r s)
    simpa using (Metric.mem_ball_self (x := (0 : ℝ)) (hr s))
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover U hUopen hUcover
  have hcover : ∀ s ∈ Icc a b, ∃ t : {q : ℝ // q ∈ T},
      s - t.1 ∈ Metric.ball (0 : ℝ) (r t.1) := by
    intro s hs
    rcases mem_iUnion₂.1 (hT hs) with ⟨t, ht, hst⟩
    exact ⟨⟨t, ht⟩, hst⟩
  refine ⟨{
    centers := T
    localGeodesic := fun t ↦ α t.1
    radius := fun t ↦ r t.1
    radius_pos := fun t ↦ hr t.1
    radius_le_local_radius := fun t ↦ hrlocalRadius t.1
    state_agrees := ?_
    covers := hcover }⟩
  intro t s hs
  have hstate := hlocal t.1 hs
  change γ.state (t.1 + (s - t.1)) =
    localState (α t.1) (s - t.1) at hstate
  rw [show t.1 + (s - t.1) = s by ring] at hstate
  exact hstate

end GlobalGeodesic
end IntrinsicGeodesic

end BonnetMyersEntry
