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

import LeanPool.PoincareGeometry.BonnetMyers.GlobalParallel

/-!
# Time reflection for local parallel germs

This module makes the time-reversal construction for local parallel transport
explicit at the level of tangent-bundle total spaces.  A local germ on the
reversed complete geodesic can therefore be reflected to a genuine local germ
on the original complete geodesic.  Every dependent-fibre reindexing is kept
visible through an equality of total tangent-bundle states.
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

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic.GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- Reindex a free tangent vector across equality of two complete initial
tangent-bundle states. -/
noncomputable def reindexInitialVector
    {x y : M} {vx : TM x} {vy : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (z : TM y) : TM x :=
  cast (congrArg (TangentSpace I)
    (congrArg Bundle.TotalSpace.proj hstate).symm) z

/-- Total-space form of `reindexInitialVector`. -/
theorem reindexInitialVector_totalState
    {x y : M} {vx : TM x} {vy : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (z : TM y) :
    (⟨x, reindexInitialVector hstate z⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, z⟩ := by
  cases hstate
  rfl

/-- Reindex a canonical coordinate parallel solution along equality of the
complete initial geodesic state. -/
noncomputable def reindexParallelSolution
    {x y : M} {vx : TM x} {vy : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (α : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov y vy)
    {z : TM y}
    (sol : LocalLinearTransportSolution
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov y (IntrinsicGeodesic.canonicalBasis (E := E))
        (α.solution.coordinate s) (α.solution.velocity s)) 0
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) y z)) :
    LocalLinearTransportSolution
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x (IntrinsicGeodesic.canonicalBasis (E := E))
        ((castInitialState hstate α).solution.coordinate s)
        ((castInitialState hstate α).solution.velocity s)) 0
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x
        (reindexInitialVector hstate z)) := by
  cases hstate
  exact sol

/-- Canonical tangent-valued parallel fields are invariant, as total-space
values, under an explicit reindexing of their initial geodesic state. -/
theorem canonicalFrameParallel_reindex_totalState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x y : M} {vx : TM x} {vy : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (α : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov y vy)
    {z : TM y}
    (sol : LocalLinearTransportSolution
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov y (IntrinsicGeodesic.canonicalBasis (E := E))
        (α.solution.coordinate s) (α.solution.velocity s)) 0
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) y z))
    (t : ℝ) :
    (⟨IntrinsicGeodesic.LocalGeodesic.curve (castInitialState hstate α) t,
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (castInitialState hstate α)
        (reindexParallelSolution hstate α sol) t⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨IntrinsicGeodesic.LocalGeodesic.curve α t,
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel α sol t⟩ := by
  cases hstate
  rfl

/-- The original global state at `t₀ - r` is the reflected tangent-bundle
state of `reverseAt γ t₀` at `r`. -/
theorem reverseAt_reflectState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ r : ℝ) :
    γ.state (t₀ - r) =
      (⟨curve (reverseAt γ t₀) r,
        -velocity (reverseAt γ t₀) r⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) := by
  change γ.state (t₀ - r) =
    ⟨((reverseAt γ t₀).state r).proj,
      -((reverseAt γ t₀).state r).snd⟩
  rw [reverseAt_state]
  simp

/-- Reflect the initial vector of a germ on `reverseAt γ t₀` back to the
corresponding tangent fibre of `γ`. -/
noncomputable def reindexedReflectInitial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ r : ℝ) (w : TM (curve (reverseAt γ t₀) r)) :
    TM (curve γ (t₀ - r)) :=
  reindexInitialVector (reverseAt_reflectState γ t₀ r) w

/-- Reflect a parallel germ on an anchored reversed global geodesic to a
parallel germ on the original global geodesic.  The proof reverses the local
coordinate transport equation and then reindexes its complete initial state;
it does not identify distinct tangent fibres by definition. -/
noncomputable def ParallelGerm.reflectReverseAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ r : ℝ) {w : TM (curve (reverseAt γ t₀) r)}
    (q : ParallelGerm (I := I) (M := M) (reverseAt γ t₀) r w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ParallelGerm (I := I) (M := M) γ (t₀ - r)
      (reindexedReflectInitial γ t₀ r w) := by
  let hstate := reverseAt_reflectState γ t₀ r
  let α : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov
      (curve γ (t₀ - r)) (velocity γ (t₀ - r)) :=
    castInitialState hstate
      (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic)
  let solRaw := IntrinsicGeodesic.LocalGeodesic.reverseParallelSolution
    q.localGeodesic q.coordinateSolution
  let sol := reindexParallelSolution hstate
    (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic) solRaw
  refine {
    localGeodesic := α
    coordinateSolution := sol
    agrees := ?_
    initial := ?_
    parallel := ?_ }
  · have hneg : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ -s) 0 :=
        (continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) 0).neg
      simpa using hcont.tendsto
    have hqneg := q.agrees.comp_tendsto hneg
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ),
        s ∈ Ioo (-q.localGeodesic.solution.radius)
          q.localGeodesic.solution.radius :=
      Ioo_mem_nhds (by linarith [q.localGeodesic.solution.radius_pos])
        (by linarith [q.localGeodesic.solution.radius_pos])
    filter_upwards [hqneg, hsmall] with s hs hsr
    change γ.state ((t₀ - r) + s) =
      IntrinsicGeodesic.localState
        (castInitialState hstate
          (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic)) s
    rw [localState_castInitialState]
    have hvel := IntrinsicGeodesic.LocalGeodesic.reverse_actual_velocity
      q.localGeodesic hsr
    calc
      γ.state ((t₀ - r) + s) =
          ⟨((reverseAt γ t₀).state (r + -s)).proj,
            -((reverseAt γ t₀).state (r + -s)).snd⟩ := by
        change γ.state ((t₀ - r) + s) =
          ⟨(γ.state (t₀ - (r + -s))).proj,
            -(-(γ.state (t₀ - (r + -s))).snd)⟩
        rw [show t₀ - (r + -s) = (t₀ - r) + s by ring]
        simp
      _ = ⟨(IntrinsicGeodesic.localState q.localGeodesic (-s)).proj,
            -(IntrinsicGeodesic.localState q.localGeodesic (-s)).snd⟩ :=
          congrArg (fun z : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
            (⟨z.proj, -z.snd⟩ :
              Bundle.TotalSpace E (TangentSpace I : M → Type _))) hs
      _ = IntrinsicGeodesic.localState
          (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic) s := by
        simp only [IntrinsicGeodesic.localState]
        rw [IntrinsicGeodesic.LocalGeodesic.reverse_curve, hvel]
        rfl
  · have hαtotal :
      (⟨IntrinsicGeodesic.LocalGeodesic.curve α 0,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel α sol 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve
          (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic) 0,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic)
          solRaw 0⟩ := by
        dsimp only [α, sol]
        exact canonicalFrameParallel_reindex_totalState hstate
          (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic) solRaw 0
    have hreverse :
      (⟨IntrinsicGeodesic.LocalGeodesic.curve
          (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic) 0,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic)
          solRaw 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          q.localGeodesic q.coordinateSolution 0⟩ := by
        dsimp only [solRaw]
        have h := IntrinsicGeodesic.LocalGeodesic.reverse_canonicalFrameParallel_totalState
          q.localGeodesic q.coordinateSolution 0
        have hzero : -(0 : ℝ) = 0 := by ring
        rw [hzero] at h
        exact h
    have hqinitial :
      (⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          q.localGeodesic q.coordinateSolution 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (reverseAt γ t₀) r, w⟩ := by
      rw [IntrinsicGeodesic.LocalGeodesic.curve_initial q.localGeodesic,
        q.initial]
    have htarget :
      (⟨curve γ (t₀ - r), reindexedReflectInitial γ t₀ r w⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (reverseAt γ t₀) r, w⟩ := by
      change (⟨(γ.state (t₀ - r)).proj,
        reindexedReflectInitial γ t₀ r w⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (reverseAt γ t₀) r, w⟩
      exact reindexInitialVector_totalState hstate w
    have htotal := hαtotal.trans (hreverse.trans (hqinitial.trans htarget.symm))
    rw [IntrinsicGeodesic.LocalGeodesic.curve_initial α] at htotal
    exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
      (curve γ (t₀ - r))
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel α sol 0)
      (reindexedReflectInitial γ t₀ r w)).mp htotal
  · exact IntrinsicGeodesic.LocalGeodesic.eventually_isCovariantAccelerationAt_canonicalFrameParallel_zero
      α sol hmetric

/-- On a neighbourhood of the reflected time origin, the actual tangent-bundle
field of a reflected germ is the original germ's actual field read at the
opposite time.  This is the overlap law needed to turn one-sided transport on
the reversed geodesic into backward transport on the original geodesic. -/
theorem ParallelGerm.reflectReverseAt_shiftedField_eventuallyEq
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ r : ℝ) {w : TM (curve (reverseAt γ t₀) r)}
    (q : ParallelGerm (I := I) (M := M) (reverseAt γ t₀) r w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    (fun s ↦ (⟨curve (shift γ (t₀ - r)) s,
      (q.reflectReverseAt γ t₀ r hmetric).shiftedField s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) =ᶠ[𝓝 (0 : ℝ)]
      fun s ↦ ⟨curve (shift (reverseAt γ t₀) r) (-s), q.shiftedField (-s)⟩ := by
  let p := q.reflectReverseAt γ t₀ r hmetric
  have hneg : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ -s) 0 :=
      (continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) 0).neg
    simpa using hcont.tendsto
  have hqneg := q.agrees.comp_tendsto hneg
  filter_upwards [p.agrees, hqneg] with s hp hq
  have hpstate : (shift γ (t₀ - r)).state s =
      IntrinsicGeodesic.localState p.localGeodesic s := by
    simpa [shift_state] using hp
  have hqstate : (shift (reverseAt γ t₀) r).state (-s) =
      IntrinsicGeodesic.localState q.localGeodesic (-s) := by
    simpa [shift_state] using hq
  have hptotal := p.shiftedField_totalState_eq_of_state_eq s hpstate
  have hqtotal := q.shiftedField_totalState_eq_of_state_eq (-s) hqstate
  have hlocal :
      (⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          p.localGeodesic p.coordinateSolution s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic (-s),
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          q.localGeodesic q.coordinateSolution (-s)⟩ := by
    dsimp only [p, ParallelGerm.reflectReverseAt]
    exact (canonicalFrameParallel_reindex_totalState
      (reverseAt_reflectState γ t₀ r)
      (IntrinsicGeodesic.LocalGeodesic.reverse q.localGeodesic)
      (IntrinsicGeodesic.LocalGeodesic.reverseParallelSolution
        q.localGeodesic q.coordinateSolution) s).trans
      (IntrinsicGeodesic.LocalGeodesic.reverse_canonicalFrameParallel_totalState
        q.localGeodesic q.coordinateSolution s)
  exact hptotal.trans (hlocal.trans hqtotal.symm)

end IntrinsicGeodesic.GlobalGeodesic
end BonnetMyersEntry
