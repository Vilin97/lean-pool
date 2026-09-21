/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.GlobalGeodesic
import LeanPool.PoincareGeometry.BonnetMyers.GlobalIntrinsicGeodesic
import LeanPool.PoincareGeometry.BonnetMyers.ParallelConnection
import LeanPool.PoincareGeometry.BonnetMyers.Algebra

/-!
# Parallel germs along complete geodesics

`GlobalGeodesic` supplies a chart-independent geodesic state at every time,
while `ParallelConnection` supplies an intrinsically parallel field on a
single local geodesic chart.  This module records their precise interface:
at every time on a global geodesic, an arbitrary tangent vector has a local
parallel germ whose base geodesic agrees with the global state germ.  The
field is deliberately retained on its certified local curve; transporting it
across the equality of dependent tangent fibres is a separate gluing step.
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

namespace IntrinsicGeodesic
namespace GlobalGeodesic

open CurveConnection

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- Every tangent fibre has the model-space dimension, by the canonical
tangent-bundle trivialization at that point. -/
theorem tangent_finrank_eq_model (x : M) :
    Module.finrank ℝ (TM x) = Module.finrank ℝ E := by
  exact LinearEquiv.finrank_eq
    ((trivializationAt E TM x).linearEquivAt ℝ x
      (mem_baseSet_trivializationAt E TM x))

/-- In particular, any two tangent fibres of the manifold have equal finite
dimension. -/
theorem tangent_finrank_eq (x y : M) :
    Module.finrank ℝ (TM x) = Module.finrank ℝ (TM y) :=
  (tangent_finrank_eq_model (I := I) (M := M) x).trans
    (tangent_finrank_eq_model (I := I) (M := M) y).symm

/-- A parallel germ based at time `t₀` of a global geodesic.  Its local
geodesic is not an arbitrary surrogate: `agrees` identifies its complete
tangent-bundle state with the prescribed global state near zero. -/
structure ParallelGerm
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w : TM (curve γ t₀)) where
  localGeodesic : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov
    (curve γ t₀) (velocity γ t₀)
  agrees : (fun s ↦ γ.state (t₀ + s)) =ᶠ[𝓝 (0 : ℝ)]
    IntrinsicGeodesic.localState localGeodesic
  coordinateSolution : LocalLinearTransportSolution
    (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E))
      (localGeodesic.solution.coordinate s) (localGeodesic.solution.velocity s)) 0
    (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E)
      (curve γ t₀) w)
  initial : IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
    (I := I) (M := M) localGeodesic coordinateSolution 0 = w
  parallel : ∀ᶠ s in 𝓝 (0 : ℝ),
    IsCovariantAccelerationAt cov
      (IntrinsicGeodesic.LocalGeodesic.curve localGeodesic)
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) localGeodesic coordinateSolution) s
      (IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (localGeodesic.solution.velocity s)
        (IntrinsicGeodesic.LocalGeodesic.curve localGeodesic s)) 0

/-- A finite parallel-frame germ based at a time of a global geodesic.  The
single common radius carries the entire Gram matrix, which is the local datum
needed for transverse-frame arguments in second variation.  As with
`ParallelGerm`, the fields deliberately remain over their certified local
geodesic until a separate dependent-fibre gluing theorem is proved. -/
structure ParallelFamilyGerm
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w : ι → TM (curve γ t₀)) where
  localGeodesic : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov
    (curve γ t₀) (velocity γ t₀)
  agrees : (fun s ↦ γ.state (t₀ + s)) =ᶠ[𝓝 (0 : ℝ)]
    IntrinsicGeodesic.localState localGeodesic
  coordinateSolution : ∀ i, LocalLinearTransportSolution
    (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E))
      (localGeodesic.solution.coordinate s) (localGeodesic.solution.velocity s)) 0
    (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E)
      (curve γ t₀) (w i))
  initial : ∀ i, IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
    (I := I) (M := M) localGeodesic (coordinateSolution i) 0 = w i
  parallel : ∀ i, ∀ᶠ s in 𝓝 (0 : ℝ),
    IsCovariantAccelerationAt cov
      (IntrinsicGeodesic.LocalGeodesic.curve localGeodesic)
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) localGeodesic (coordinateSolution i)) s
      (IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun k => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) k)
        (localGeodesic.solution.velocity s)
        (IntrinsicGeodesic.LocalGeodesic.curve localGeodesic s)) 0
  radius : ℝ
  radius_pos : 0 < radius
  gram : ∀ i j s, s ∈ Ioo (-radius) radius →
    inner ℝ
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) localGeodesic (coordinateSolution i) s)
          (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) localGeodesic (coordinateSolution j) s) =
      inner ℝ (w i) (w j)

/-- Extract one member of a finite parallel-frame germ as an ordinary
parallel germ.  This keeps the common-family Gram certificate while exposing
the individual field to the dependent-fibre reindexing API. -/
def ParallelFamilyGerm.toParallelGerm
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w) (i : ι) :
    ParallelGerm (I := I) (M := M) γ t₀ (w i) where
  localGeodesic := p.localGeodesic
  agrees := p.agrees
  coordinateSolution := p.coordinateSolution i
  initial := p.initial i
  parallel := p.parallel i

/-- Read a local canonical parallel field along the time-shifted global
geodesic based at the same restart time.  Outside the certified state-germ
agreement neighbourhood it is deliberately zero.  Thus the dependent-fibre
cast is explicit, while all geometric assertions use only the germ at zero. -/
noncomputable def ParallelGerm.shiftedField
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (s : ℝ) :
    TM (curve (shift γ t₀) s) := by
  classical
  exact if h : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s then
    cast (congrArg (TangentSpace I) h.symm)
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic p.coordinateSolution s)
  else 0

/-- On the state-germ overlap, `shiftedField` is exactly the certified
dependent-fibre cast of the local canonical field. -/
theorem ParallelGerm.shiftedField_eq_of_curve_eq
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (s : ℝ)
    (hcurve : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s) :
    p.shiftedField s =
      cast (congrArg (TangentSpace I) hcurve.symm)
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution s) := by
  simp [ParallelGerm.shiftedField, hcurve]

/-- Read one member of a finite parallel-frame germ along the actual shifted
global geodesic. -/
def ParallelFamilyGerm.shiftedField
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w)
    (i : ι) (s : ℝ) : TM (curve (shift γ t₀) s) :=
  (p.toParallelGerm i).shiftedField s

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
private theorem cast_parallel_inner_section_of_curve_eq
    {x y : M} (hxy : x = y) (u : TM y)
    (W : (z : M) → TM z) :
    inner ℝ (cast (congrArg (TangentSpace I) hxy.symm) u) (W x) =
      inner ℝ u (W y) := by
  subst y
  rfl

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
private theorem cast_parallel_rhs_of_state_eq
    {x y : M} {vx : TM x} {vy : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (u : TM y) (W : (z : M) → TM z) :
    inner ℝ 0 (W y) + inner ℝ u (cov W y vy) =
      inner ℝ 0 (W x) +
        inner ℝ
          (cast (congrArg (TangentSpace I)
            (congrArg Bundle.TotalSpace.proj hstate).symm) u)
          (cov W x vx) := by
  cases hstate
  rfl

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- A complete tangent-bundle state equality transports the explicit
frame-coordinate parallel equation to the other presentation of the same
curve point.  This is the dependent-fibre step needed when a restarted local
geodesic is compared with the old one on a state-germ overlap. -/
theorem frameAcceleration_eq_zero_of_totalState_eq
    {x y : M} {vx : TM x} {vy : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (z : M) → TM z)
    (u a : E)
    (hzero : IntrinsicAcceleration.frameField (I := I) (M := M) b S a y +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S u) y vy = 0) :
    IntrinsicAcceleration.frameField (I := I) (M := M) b S a x +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S u) x vx = 0 := by
  cases hstate
  exact hzero

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Reindexing a time-frame value through an equality of its base points is
exactly the same as evaluating that frame at the reindexed point.  The lemma
keeps the necessary dependent cast visible for transport-gluing proofs. -/
theorem timeFrameField_eq_cast_of_eq
    {x y : M} (hxy : x = y)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (z : M) → TM z)
    (u : ℝ → E) (t : ℝ) :
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S
      u t x =
      cast (congrArg (TangentSpace I) hxy.symm)
        (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S
          u t y) := by
  cases hxy
  rfl

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Equality of two frame values after reindexing to a common tangent fibre
gives equality of their original tangent-bundle total-space values.  It is a
small but essential dependent-type bridge for applying interval uniqueness to
two local-geodesic charts. -/
theorem totalState_timeFrameField_eq_of_totalState_eq
    {x y z : M} {vx : TM x} {vy : TM y} {vz : TM z}
    (hxy : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (hxz : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨z, vz⟩)
    (b c : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (q : M) → TM q)
    (u w : ℝ → E) (t : ℝ)
    (hfield : IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t x =
      IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t x) :
    (⟨y, IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t y⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨z, IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t z⟩ := by
  cases hxy
  cases hxz
  simpa using congrArg (fun q : TM x ↦
    (⟨x, q⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _))) hfield

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Conversely, equality of the two original time-frame total-space values
can be read in a chosen common tangent fibre once both base states are
identified with that fibre. -/
theorem timeFrameField_eq_of_totalState_eq
    {x y z : M} {vx : TM x} {vy : TM y} {vz : TM z}
    (hxy : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (hxz : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨z, vz⟩)
    (b c : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (q : M) → TM q)
    (u w : ℝ → E) (t : ℝ)
    (hfield : (⟨y, IntrinsicAcceleration.timeFrameField (I := I) (M := M)
      b S u t y⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨z, IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t z⟩) :
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t x =
      IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t x := by
  cases hxy
  cases hxz
  simpa only [Bundle.TotalSpace.mk_inj] using hfield

/-- A local canonical parallel field transfers to a genuine zero-covariant-
derivative germ along the shifted global geodesic.  The proof uses the scalar
characterization of covariant acceleration and the certified equality of the
complete tangent-bundle state; it does not assume cross-restart field gluing. -/
theorem ParallelGerm.isCovariantAccelerationAt_shiftedField_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) :
    IsCovariantAccelerationAt cov (curve (shift γ t₀)) p.shiftedField 0
      (velocity (shift γ t₀) 0) 0 := by
  unfold IsCovariantAccelerationAt
  intro W hW
  have hscalar :
      (fun s ↦ inner ℝ (p.shiftedField s) (W (curve (shift γ t₀) s))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s ↦ inner ℝ
          (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) p.localGeodesic p.coordinateSolution s)
          (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s))) := by
    filter_upwards [p.agrees] with s hs
    have hcurve : curve (shift γ t₀) s =
        IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s := by
      simpa [curve, IntrinsicGeodesic.localState] using
        congrArg Bundle.TotalSpace.proj hs
    rw [p.shiftedField_eq_of_curve_eq s hcurve]
    exact cast_parallel_inner_section_of_curve_eq (I := I) (M := M) hcurve
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic p.coordinateSolution s) W
  have hlocal := p.parallel.self_of_nhds
  change IsCovariantAccelerationAt cov
    (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic)
    (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
      (I := I) (M := M) p.localGeodesic p.coordinateSolution) 0
    (CurveConnection.canonicalFrameVelocity p.localGeodesic 0) 0 at hlocal
  have hlocalVelocity :=
    CurveConnection.localGeodesic_eventually_canonicalFrameVelocity_eq_velocity
      (I := I) (M := M) p.localGeodesic
  rw [hlocalVelocity.self_of_nhds] at hlocal
  have hstate0 : (shift γ t₀).state 0 =
      IntrinsicGeodesic.localState p.localGeodesic 0 := by
    simpa [shift_state] using p.agrees.self_of_nhds
  have hWlocal : MDiffAt (T% W)
      (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic 0) := by
    change MDiffAt (T% W) (IntrinsicGeodesic.localState p.localGeodesic 0).proj
    rw [← hstate0]
    exact hW
  calc
    CurveConnection.curveScalarDeriv
        (fun s ↦ inner ℝ (p.shiftedField s) (W (curve (shift γ t₀) s))) 0 =
      CurveConnection.curveScalarDeriv (fun s ↦ inner ℝ
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution s)
        (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s))) 0 :=
      CurveConnection.curveScalarDeriv_congr_of_eventuallyEq hscalar
    _ = inner ℝ 0 (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic 0)) +
          inner ℝ
            (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) p.localGeodesic p.coordinateSolution 0)
            (cov W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic 0)
              (IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic 0)) :=
      hlocal W hWlocal
    _ = inner ℝ 0 (W (curve (shift γ t₀) 0)) +
          inner ℝ (p.shiftedField 0)
            (cov W (curve (shift γ t₀) 0) (velocity (shift γ t₀) 0)) := by
      have hcurve0 : curve (shift γ t₀) 0 =
          IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic 0 := by
        simpa [curve, IntrinsicGeodesic.localState] using
          congrArg Bundle.TotalSpace.proj hstate0
      rw [p.shiftedField_eq_of_curve_eq 0 hcurve0]
      change
        inner ℝ 0
            (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic 0)) +
          inner ℝ
            (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) p.localGeodesic p.coordinateSolution 0)
            (cov W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic 0)
              (IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic 0)) =
          inner ℝ 0 (W ((shift γ t₀).state 0).proj) +
            inner ℝ
              (cast (congrArg (TangentSpace I)
                (congrArg Bundle.TotalSpace.proj hstate0).symm)
                (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
                  (I := I) (M := M) p.localGeodesic p.coordinateSolution 0))
              (cov W ((shift γ t₀).state 0).proj ((shift γ t₀).state 0).snd)
      exact cast_parallel_rhs_of_state_eq (I := I) (M := M) (cov := cov)
        hstate0
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution 0) W

/-- Transfer an intrinsic parallel equation from a local geodesic to the
actual shifted global geodesic at any time for which the full state germs
agree.  This is the time-local form of the zero-time transfer above and keeps
the required neighbourhood equality explicit. -/
theorem ParallelGerm.isCovariantAccelerationAt_shiftedField_of_state_germ
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (t : ℝ)
    (hstateNear : (shift γ t₀).state =ᶠ[𝓝 t]
      IntrinsicGeodesic.localState p.localGeodesic)
    (hstate : (shift γ t₀).state t =
      IntrinsicGeodesic.localState p.localGeodesic t)
    (hlocal : IsCovariantAccelerationAt cov
      (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic)
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic p.coordinateSolution) t
      (IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic t) 0) :
    IsCovariantAccelerationAt cov (curve (shift γ t₀)) p.shiftedField t
      (velocity (shift γ t₀) t) 0 := by
  unfold IsCovariantAccelerationAt
  intro W hW
  have hscalar :
      (fun s ↦ inner ℝ (p.shiftedField s) (W (curve (shift γ t₀) s))) =ᶠ[𝓝 t]
        (fun s ↦ inner ℝ
          (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) p.localGeodesic p.coordinateSolution s)
          (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s))) := by
    filter_upwards [hstateNear] with s hs
    have hcurve : curve (shift γ t₀) s =
        IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s := by
      simpa [curve, IntrinsicGeodesic.localState] using
        congrArg Bundle.TotalSpace.proj hs
    rw [p.shiftedField_eq_of_curve_eq s hcurve]
    exact cast_parallel_inner_section_of_curve_eq (I := I) (M := M) hcurve
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic p.coordinateSolution s) W
  have hWlocal : MDiffAt (T% W)
      (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic t) := by
    change MDiffAt (T% W) (IntrinsicGeodesic.localState p.localGeodesic t).proj
    rw [← hstate]
    exact hW
  calc
    CurveConnection.curveScalarDeriv
        (fun s ↦ inner ℝ (p.shiftedField s) (W (curve (shift γ t₀) s))) t =
      CurveConnection.curveScalarDeriv (fun s ↦ inner ℝ
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution s)
        (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s))) t :=
      CurveConnection.curveScalarDeriv_congr_of_eventuallyEq hscalar
    _ = inner ℝ 0 (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic t)) +
          inner ℝ
            (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) p.localGeodesic p.coordinateSolution t)
            (cov W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic t)
              (IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic t)) :=
      hlocal W hWlocal
    _ = inner ℝ 0 (W (curve (shift γ t₀) t)) +
          inner ℝ (p.shiftedField t)
            (cov W (curve (shift γ t₀) t) (velocity (shift γ t₀) t)) := by
      have hcurve : curve (shift γ t₀) t =
          IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic t := by
        simpa [curve, IntrinsicGeodesic.localState] using
          congrArg Bundle.TotalSpace.proj hstate
      rw [p.shiftedField_eq_of_curve_eq t hcurve]
      change
        inner ℝ 0
            (W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic t)) +
          inner ℝ
            (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) p.localGeodesic p.coordinateSolution t)
            (cov W (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic t)
              (IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic t)) =
          inner ℝ 0 (W ((shift γ t₀).state t).proj) +
            inner ℝ
              (cast (congrArg (TangentSpace I)
                (congrArg Bundle.TotalSpace.proj hstate).symm)
                (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
                  (I := I) (M := M) p.localGeodesic p.coordinateSolution t))
              (cov W ((shift γ t₀).state t).proj ((shift γ t₀).state t).snd)
      exact cast_parallel_rhs_of_state_eq (I := I) (M := M) (cov := cov)
        hstate
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution t) W

private theorem exists_pos_radius_of_eventually {P : ℝ → Prop}
    (hP : ∀ᶠ s in 𝓝 (0 : ℝ), P s) :
    ∃ r > (0 : ℝ), ∀ s ∈ Ioo (-r) r, P s := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨r, hr, ?_⟩
  intro s hs
  apply hsub
  rw [Metric.mem_ball]
  simpa [dist_zero_right, abs_lt] using hs

/-- A parallel germ is covariantly constant on one explicit nonempty interval
of the actual shifted global geodesic.  Unlike the pointwise transfer theorem,
this packages a common interval on which both state agreement and the local
parallel certificate hold, so it is suitable for continuation arguments. -/
theorem ParallelGerm.exists_interval_isCovariantAccelerationAt_shiftedField_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) :
    ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      IsCovariantAccelerationAt cov (curve (shift γ t₀)) p.shiftedField t
        (velocity (shift γ t₀) t) 0 := by
  obtain ⟨rstate, hrstate, hstate⟩ :=
    exists_pos_radius_of_eventually p.agrees
  obtain ⟨rparallel, hrparallel, hparallel⟩ :=
    exists_pos_radius_of_eventually p.parallel
  have hvelocityGerm :=
    CurveConnection.localGeodesic_eventually_canonicalFrameVelocity_eq_velocity
      (I := I) (M := M) p.localGeodesic
  obtain ⟨rvelocity, hrvelocity, hvelocity⟩ :=
    exists_pos_radius_of_eventually hvelocityGerm
  let r : ℝ := min rstate (min rparallel rvelocity)
  have hr : 0 < r := lt_min hrstate (lt_min hrparallel hrvelocity)
  refine ⟨r, hr, ?_⟩
  intro t ht
  have htrstate : t ∈ Ioo (-rstate) rstate := by
    have hle : r ≤ rstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have htrparallel : t ∈ Ioo (-rparallel) rparallel := by
    have hle : r ≤ rparallel := le_trans (min_le_right _ _) (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have htrvelocity : t ∈ Ioo (-rvelocity) rvelocity := by
    have hle : r ≤ rvelocity := le_trans (min_le_right _ _) (min_le_right _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have hstateAt : (shift γ t₀).state t =
      IntrinsicGeodesic.localState p.localGeodesic t := by
    simpa [shift_state] using hstate t htrstate
  have hstateNear : (shift γ t₀).state =ᶠ[𝓝 t]
      IntrinsicGeodesic.localState p.localGeodesic := by
    have hneighborhood : Ioo (-rstate) rstate ∈ 𝓝 t :=
      Ioo_mem_nhds htrstate.1 htrstate.2
    filter_upwards [hneighborhood] with s hs
    simpa [shift_state] using hstate s hs
  have hlocal := hparallel t htrparallel
  change IsCovariantAccelerationAt cov
    (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic)
    (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
      (I := I) (M := M) p.localGeodesic p.coordinateSolution) t
    (CurveConnection.canonicalFrameVelocity p.localGeodesic t) 0 at hlocal
  rw [hvelocity t htrvelocity] at hlocal
  exact p.isCovariantAccelerationAt_shiftedField_of_state_germ t
    hstateNear hstateAt hlocal

private theorem cast_tangent_inner_of_eq {x y : M}
    (hxy : x = y) (u v : TM y) :
    inner ℝ (cast (congrArg (TangentSpace I) hxy.symm) u)
        (cast (congrArg (TangentSpace I) hxy.symm) v) = inner ℝ u v := by
  subst y
  rfl

/-- The norm conservation proved for a local canonical parallel field holds
on an explicit interval for its dependent-fibre reindexing to the actual
shifted global geodesic. -/
theorem ParallelGerm.exists_interval_shiftedField_inner_self_eq
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      inner ℝ (p.shiftedField t) (p.shiftedField t) = inner ℝ w w := by
  obtain ⟨rstate, hrstate, hstate⟩ :=
    exists_pos_radius_of_eventually p.agrees
  obtain ⟨rnorm, hrnorm, _hrbound, hnorm⟩ :=
    BonnetMyersEntry.IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel_inner_self_constant_near_zero
      (I := I) (M := M) (cov := cov) (x₀ := curve γ t₀)
      (v₀ := velocity γ t₀) p.localGeodesic p.coordinateSolution hmetric
  let r : ℝ := min rstate rnorm
  have hr : 0 < r := lt_min hrstate hrnorm
  refine ⟨r, hr, ?_⟩
  intro t ht
  have htstate : t ∈ Ioo (-rstate) rstate := by
    have hle : r ≤ rstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have htnorm : t ∈ Ioo (-rnorm) rnorm := by
    have hle : r ≤ rnorm := min_le_right _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have hcurve : curve (shift γ t₀) t =
      IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic t := by
    have hstateAt := hstate t htstate
    simpa [curve, IntrinsicGeodesic.localState, shift_state] using
      congrArg Bundle.TotalSpace.proj hstateAt
  rw [p.shiftedField_eq_of_curve_eq t hcurve]
  rw [cast_tangent_inner_of_eq (I := I) (M := M) hcurve]
  rw [hnorm t htnorm]
  rw [IntrinsicGeodesic.LocalGeodesic.curve_initial p.localGeodesic]
  rw [p.initial]

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
private theorem cast_tangent_heq_of_eq
    {x y : M} (hxy : x = y) (u : TM y) :
    HEq (cast (congrArg (TangentSpace I) hxy.symm) u) u := by
  subst y
  rfl

/-- On a state-germ overlap, the reindexed parallel field and its local
canonical representative are the same point of the tangent bundle. -/
theorem ParallelGerm.shiftedField_totalState_eq_of_state_eq
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (s : ℝ)
    (hstate : (shift γ t₀).state s =
      IntrinsicGeodesic.localState p.localGeodesic s) :
    (⟨curve (shift γ t₀) s, p.shiftedField s⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution s⟩ := by
  have hcurve : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s := by
    simpa [curve, IntrinsicGeodesic.localState] using
      congrArg Bundle.TotalSpace.proj hstate
  apply Bundle.TotalSpace.ext hcurve
  rw [p.shiftedField_eq_of_curve_eq s hcurve]
  exact cast_tangent_heq_of_eq (I := I) (M := M) hcurve
    (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
      (I := I) (M := M) p.localGeodesic p.coordinateSolution s)

/-- A reindexed parallel germ is continuous as an actual tangent-bundle
curve at its restart time.  The local canonical field has a genuine ODE
coordinate readout; the state-germ equality then transfers that continuity
to the shifted global geodesic without identifying tangent fibres by
definition. -/
theorem ParallelGerm.continuousAt_shiftedField_totalState_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) :
    ContinuousAt (fun s ↦
      (⟨curve (shift γ t₀) s, p.shiftedField s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) 0 := by
  have hlocal :=
    IntrinsicGeodesic.LocalGeodesic.continuousAt_canonicalFrameParallel_totalState_zero
      (I := I) (M := M) p.localGeodesic p.coordinateSolution
  have hnear : (fun s ↦
      (⟨curve (shift γ t₀) s, p.shiftedField s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦
        (⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s,
          IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) p.localGeodesic p.coordinateSolution s⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
    filter_upwards [p.agrees] with s hs
    have hstate : (shift γ t₀).state s =
        IntrinsicGeodesic.localState p.localGeodesic s := by
      simpa [shift_state] using hs
    exact p.shiftedField_totalState_eq_of_state_eq s hstate
  exact hlocal.congr_of_eventuallyEq hnear

/-- Reading a restarted parallel field through the same fixed
tangent-bundle trivialization that supplied its local transport equation
recovers its model-fibre coordinate solution as a germ.  This links actual
dependent-fibre transport to the ODE value without identifying fibres by
definition. -/
theorem ParallelGerm.eventually_coordinateReadout_eq_coordinateSolution
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      (trivializationAt E (TangentSpace I : M → Type _) (curve γ t₀)).continuousLinearMapAt ℝ
        (curve (shift γ t₀) s) (p.shiftedField s) =
        p.coordinateSolution.curve s := by
  obtain ⟨r, hr, hradius, hframe⟩ :=
    IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel_eq_coordinateFrameCombination_near_zero
      (I := I) (M := M) p.localGeodesic p.coordinateSolution
  have hinterval : Ioo (-r) r ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [hr]) (by linarith [hr])
  filter_upwards [p.agrees, hinterval] with s hstate hs
  have hstate' : (shift γ t₀).state s =
      IntrinsicGeodesic.localState p.localGeodesic s := by
    simpa [shift_state] using hstate
  have htotal := p.shiftedField_totalState_eq_of_state_eq s hstate'
  have hcurve : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s := by
    simpa [curve, IntrinsicGeodesic.localState] using
      congrArg Bundle.TotalSpace.proj hstate'
  have htsol : s ∈ Ioo (-p.localGeodesic.solution.radius)
      p.localGeodesic.solution.radius := by
    have hle : r ≤ p.localGeodesic.solution.radius :=
      le_trans hradius (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have htarget := p.localGeodesic.solution.coordinate_mem_target s htsol
  have hsource : IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s ∈
      (chartAt H (curve γ t₀)).source := by
    rw [← extChartAt_source (I := I) (curve γ t₀)]
    change (extChartAt I (curve γ t₀)).symm
      (p.localGeodesic.solution.coordinate s) ∈
        (extChartAt I (curve γ t₀)).source
    exact (extChartAt I (curve γ t₀)).map_target htarget
  have hbase : IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s ∈
      (trivializationAt E (TangentSpace I : M → Type _) (curve γ t₀)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) (curve γ t₀),
      ← extChartAt_source (I := I) (curve γ t₀)]
    rw [← extChartAt_source (I := I) (curve γ t₀)] at hsource
    exact hsource
  let read : Bundle.TotalSpace E (TangentSpace I : M → Type _) → E × E := fun z ↦
    (extChartAt I (curve γ t₀) z.proj,
      (trivializationAt E (TangentSpace I : M → Type _) (curve γ t₀)).continuousLinearMapAt ℝ
        z.proj z.snd)
  have hread := congrArg read htotal
  calc
    (trivializationAt E (TangentSpace I : M → Type _) (curve γ t₀)).continuousLinearMapAt ℝ
        (curve (shift γ t₀) s) (p.shiftedField s) =
      (trivializationAt E (TangentSpace I : M → Type _) (curve γ t₀)).continuousLinearMapAt ℝ
          (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s)
          (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) p.localGeodesic p.coordinateSolution s) :=
      congrArg Prod.snd hread
    _ = (trivializationAt E (TangentSpace I : M → Type _) (curve γ t₀)).continuousLinearMapAt ℝ
          (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s)
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E))
            (p.coordinateSolution.curve s)
            (IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s)) := by
      rw [hframe s hs]
    _ = p.coordinateSolution.curve s := by
      rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
        (I := I) (M := M) (x₀ := curve γ t₀)
        (IntrinsicGeodesic.canonicalBasis (E := E)) hsource]
      exact (trivializationAt E (TangentSpace I : M → Type _) (curve γ t₀)).continuousLinearMapAt_symmL
        hbase (p.coordinateSolution.curve s)

/-- At the restart time, the reindexed field is exactly its prescribed
initial tangent vector as a point of the total tangent bundle.  Recording the
identity at total-space level is essential here: the two fibres have equal
bases by the state-germ certificate but are not definitionally the same
dependent type. -/
theorem ParallelGerm.shiftedField_initial_totalState
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) :
    (⟨curve (shift γ t₀) 0, p.shiftedField 0⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ t₀, w⟩ := by
  have hstate : (shift γ t₀).state 0 =
      IntrinsicGeodesic.localState p.localGeodesic 0 := by
    simpa [shift_state] using p.agrees.self_of_nhds
  calc
    (⟨curve (shift γ t₀) 0, p.shiftedField 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic 0,
          IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) p.localGeodesic p.coordinateSolution 0⟩ :=
      p.shiftedField_totalState_eq_of_state_eq 0 hstate
    _ = ⟨curve γ t₀, w⟩ := by
      rw [IntrinsicGeodesic.LocalGeodesic.curve_initial p.localGeodesic,
        p.initial]

/-- Parallel-germ fields with the same initial tangent vector agree on their
actual shifted global-geodesic overlap.  This is the chart-independent
uniqueness result needed to glue restart data: it is derived from local
geodesic uniqueness, germ equality of the transport coefficients, and ODE
uniqueness, rather than treating separately chosen charts as definitionally
equal. -/
theorem ParallelGerm.shiftedField_eventuallyEq_of_same_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p q : ParallelGerm (I := I) (M := M) γ t₀ w) :
    ∀ᶠ s in 𝓝 (0 : ℝ), p.shiftedField s = q.shiftedField s := by
  have hlocal :=
    BonnetMyersEntry.IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel_eventuallyEq_totalState_of_same_initial
      (I := I) (M := M) (E := E) (H := H)
      p.localGeodesic q.localGeodesic p.coordinateSolution q.coordinateSolution
  filter_upwards [p.agrees, q.agrees, hlocal] with s hp hq hlocal
  have hpstate : (shift γ t₀).state s =
      IntrinsicGeodesic.localState p.localGeodesic s := by
    simpa [shift_state] using hp
  have hqstate : (shift γ t₀).state s =
      IntrinsicGeodesic.localState q.localGeodesic s := by
    simpa [shift_state] using hq
  have hptotal := p.shiftedField_totalState_eq_of_state_eq s hpstate
  have hqtotal := q.shiftedField_totalState_eq_of_state_eq s hqstate
  have htotal :
      (⟨curve (shift γ t₀) s, p.shiftedField s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ t₀) s, q.shiftedField s⟩ :=
    hptotal.trans (hlocal.trans hqtotal.symm)
  simpa only [Bundle.TotalSpace.mk_inj] using htotal

/-- If a restarted parallel germ begins with the geodesic velocity, its
reindexed field is the actual velocity of the shifted global geodesic as a
tangent-valued germ.  This transfers the local ODE uniqueness statement
through the certified equality of complete states. -/
theorem ParallelGerm.shiftedField_eventuallyEq_velocity_of_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hinit : w = velocity γ t₀) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      p.shiftedField s = velocity (shift γ t₀) s := by
  have hstate0 : γ.state t₀ = IntrinsicGeodesic.localState p.localGeodesic 0 := by
    simpa using p.agrees.self_of_nhds
  have hvelocity0 : velocity γ t₀ =
      IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic 0 := by
    change (γ.state t₀).snd =
      (IntrinsicGeodesic.localState p.localGeodesic 0).snd
    rw [hstate0]
  have hlocalInitial :
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic p.coordinateSolution 0 =
        IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic 0 :=
    p.initial.trans (hinit.trans hvelocity0)
  have hlocal :=
    IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel_eventuallyEq_velocity_of_initial
      (I := I) (M := M) p.localGeodesic p.coordinateSolution hlocalInitial
  filter_upwards [p.agrees, hlocal] with s hstate hfield
  have hstate' : (shift γ t₀).state s =
      IntrinsicGeodesic.localState p.localGeodesic s := by
    simpa [shift_state] using hstate
  have htotal := p.shiftedField_totalState_eq_of_state_eq s hstate'
  have hfieldTotal :
      (⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s,
        IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic s⟩ := by
    rw [hfield]
  have hglobal :
      (⟨curve (shift γ t₀) s, p.shiftedField s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ t₀) s, velocity (shift γ t₀) s⟩ := by
    calc
      (⟨curve (shift γ t₀) s, p.shiftedField s⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s,
          IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) p.localGeodesic p.coordinateSolution s⟩ := htotal
      _ = ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s,
          IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic s⟩ := hfieldTotal
      _ = (shift γ t₀).state s := by
        simpa [IntrinsicGeodesic.localState] using hstate'.symm
      _ = ⟨curve (shift γ t₀) s, velocity (shift γ t₀) s⟩ := by
        rfl
  simpa only [Bundle.TotalSpace.mk_inj] using hglobal

/-- Local intrinsic parallel transport can be restarted at any time on a
global geodesic.  The theorem makes the overlap with the global geodesic
explicit, which is the datum required for a subsequent uniqueness-and-gluing
argument rather than an implicit change of chart. -/
theorem exists_parallelGerm
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w : TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    Nonempty (ParallelGerm (I := I) (M := M) γ t₀ w) := by
  obtain ⟨localGeodesic, hagrees⟩ := γ.local_germ t₀
  obtain ⟨coordinateSolution, hinitial, hparallel⟩ :=
    IntrinsicGeodesic.LocalGeodesic.exists_canonicalFrameParallel
      (I := I) (M := M) localGeodesic w hmetric
  exact ⟨{
    localGeodesic := localGeodesic
    agrees := hagrees
    coordinateSolution := coordinateSolution
    initial := hinitial
    parallel := hparallel }⟩

/-- A finite tangent family at any point of a complete global geodesic has a
local intrinsic parallel-frame germ with one Gram-preserving interval.  The
construction uses finite choice only to select the already-proved individual
ODE solutions; all pairwise metric identities are then made uniform by the
finite-family theorem in `ParallelConnection`. -/
theorem exists_parallelFamilyGerm
    {ι : Type*} [Fintype ι] [Nonempty ι]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w : ι → TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    Nonempty (ParallelFamilyGerm (I := I) (M := M) γ t₀ w) := by
  obtain ⟨localGeodesic, hagrees⟩ := γ.local_germ t₀
  obtain ⟨coordinateSolution, hinitial, r, hr, hgram⟩ :=
    IntrinsicGeodesic.LocalGeodesic.exists_canonicalFrameParallel_family
      (I := I) (M := M) localGeodesic w hmetric
  have hparallel : ∀ i, ∀ᶠ s in 𝓝 (0 : ℝ),
      IsCovariantAccelerationAt cov
        (IntrinsicGeodesic.LocalGeodesic.curve localGeodesic)
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) localGeodesic (coordinateSolution i)) s
        (IntrinsicAcceleration.frameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun k => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
            (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) k)
          (localGeodesic.solution.velocity s)
          (IntrinsicGeodesic.LocalGeodesic.curve localGeodesic s)) 0 := by
    intro i
    exact IntrinsicGeodesic.LocalGeodesic.eventually_isCovariantAccelerationAt_canonicalFrameParallel_zero
      (I := I) (M := M) localGeodesic (coordinateSolution i) hmetric
  exact ⟨{
    localGeodesic := localGeodesic
    agrees := hagrees
    coordinateSolution := coordinateSolution
    initial := hinitial
    parallel := hparallel
    radius := r
    radius_pos := hr
    gram := hgram }⟩

/-- A restarted intrinsic parallel germ preserves the squared norm of its
actual tangent vectors on a certified neighbourhood.  In particular, this is
not just conservation of the coordinate coefficients used to construct the
germ. -/
theorem ParallelGerm.inner_self_constant_near_zero
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), r ≤ min p.localGeodesic.solution.radius
        p.coordinateSolution.radius ∧
      ∀ s ∈ Ioo (-r) r,
        inner ℝ
            (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) p.localGeodesic p.coordinateSolution s)
            (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) p.localGeodesic p.coordinateSolution s) =
          inner ℝ w w := by
  obtain ⟨r, hr, hradius, hnorm⟩ :=
    IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel_inner_self_constant_near_zero
      (I := I) (M := M) (cov := cov) (x₀ := curve γ t₀)
      (v₀ := velocity γ t₀) p.localGeodesic p.coordinateSolution hmetric
  refine ⟨r, hr, hradius, ?_⟩
  intro s hs
  rw [hnorm s hs]
  rw [IntrinsicGeodesic.LocalGeodesic.curve_initial p.localGeodesic]
  rw [p.initial]

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- A finite orthonormal family remains orthonormal on the common certified
interval of a restarted parallel family germ.  This upgrades pairwise Gram
preservation to the exact local frame property used by transverse
second-variation fields. -/
theorem ParallelFamilyGerm.orthonormal_near_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w)
    (hw : Orthonormal ℝ w) :
    ∀ s ∈ Ioo (-p.radius) p.radius,
      Orthonormal ℝ (fun i ↦
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic (p.coordinateSolution i) s) := by
  classical
  intro s hs
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  rw [p.gram i j s hs]
  exact hw i j

/-- The finitely many reindexed fields of a parallel-frame germ are all
covariantly constant on one common interval of the actual shifted global
geodesic.  Finiteness is used only to take the minimum of the already
certified individual intervals. -/
theorem ParallelFamilyGerm.exists_interval_shiftedField_isCovariantAccelerationAt_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w) :
    ∃ r > (0 : ℝ), ∀ i s, s ∈ Ioo (-r) r →
      IsCovariantAccelerationAt cov (curve (shift γ t₀)) (p.shiftedField i) s
        (velocity (shift γ t₀) s) 0 := by
  classical
  have hmember : ∀ i, ∃ r > (0 : ℝ), ∀ s ∈ Ioo (-r) r,
      IsCovariantAccelerationAt cov (curve (shift γ t₀))
        ((p.toParallelGerm i).shiftedField) s
        (velocity (shift γ t₀) s) 0 := by
    intro i
    exact (p.toParallelGerm i).exists_interval_isCovariantAccelerationAt_shiftedField_zero
  choose rField hrField hField using hmember
  let r : ℝ := (Finset.univ : Finset ι).inf' Finset.univ_nonempty rField
  have hr : 0 < r := by
    dsimp [r]
    refine (Finset.lt_inf'_iff _).2 ?_
    intro i hi
    exact hrField i
  refine ⟨r, hr, ?_⟩
  intro i s hs
  have hle : r ≤ rField i := by
    dsimp [r]
    exact Finset.inf'_le rField (Finset.mem_univ i)
  have hsfield : s ∈ Ioo (-(rField i)) (rField i) := by
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  change IsCovariantAccelerationAt cov (curve (shift γ t₀))
    ((p.toParallelGerm i).shiftedField) s (velocity (shift γ t₀) s) 0
  exact hField i s hsfield

/-- The full Gram matrix of a finite local parallel family is preserved after
its members are reindexed to the actual global geodesic.  This is the
coordinate-independent form of the local metric-compatibility calculation:
it applies to arbitrary finite initial vectors, not only to an orthonormal
frame. -/
theorem ParallelFamilyGerm.exists_interval_shiftedField_inner_eq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w) :
    ∃ r > (0 : ℝ), ∀ i j s, s ∈ Ioo (-r) r →
      inner ℝ (p.shiftedField i s) (p.shiftedField j s) =
        inner ℝ (w i) (w j) := by
  obtain ⟨rstate, hrstate, hstate⟩ := exists_pos_radius_of_eventually p.agrees
  let r : ℝ := min rstate p.radius
  have hr : 0 < r := lt_min hrstate p.radius_pos
  refine ⟨r, hr, ?_⟩
  intro i j s hs
  have hsstate : s ∈ Ioo (-rstate) rstate := by
    have hle : r ≤ rstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsgram : s ∈ Ioo (-p.radius) p.radius := by
    have hle : r ≤ p.radius := min_le_right _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hcurve : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s := by
    have hstateAt := hstate s hsstate
    simpa [curve, IntrinsicGeodesic.localState, shift_state] using
      congrArg Bundle.TotalSpace.proj hstateAt
  have hcurve_i : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve (p.toParallelGerm i).localGeodesic s := by
    simpa only [ParallelFamilyGerm.toParallelGerm] using hcurve
  have hcurve_j : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve (p.toParallelGerm j).localGeodesic s := by
    simpa only [ParallelFamilyGerm.toParallelGerm] using hcurve
  change inner ℝ ((p.toParallelGerm i).shiftedField s)
      ((p.toParallelGerm j).shiftedField s) = _
  rw [ParallelGerm.shiftedField_eq_of_curve_eq (p.toParallelGerm i) s hcurve_i,
    ParallelGerm.shiftedField_eq_of_curve_eq (p.toParallelGerm j) s hcurve_j]
  have hresult :=
    (cast_tangent_inner_of_eq (I := I) (M := M) hcurve
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic (p.coordinateSolution i) s)
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic (p.coordinateSolution j) s)).trans
      (p.gram i j s hsgram)
  simpa only [ParallelFamilyGerm.toParallelGerm] using hresult

/-- A finite orthonormal parallel-frame germ remains orthonormal after its
members are reindexed to the actual shifted global geodesic on one common
interval.  Thus the Gram calculation is available in the true tangent fibres,
not merely on a selected local chart curve. -/
theorem ParallelFamilyGerm.exists_interval_shiftedField_orthonormal
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w)
    (hw : Orthonormal ℝ w) :
    ∃ r > (0 : ℝ), ∀ s ∈ Ioo (-r) r,
      Orthonormal ℝ (fun i ↦ p.shiftedField i s) := by
  classical
  obtain ⟨rstate, hrstate, hstate⟩ :=
    exists_pos_radius_of_eventually p.agrees
  let r : ℝ := min rstate p.radius
  have hr : 0 < r := lt_min hrstate p.radius_pos
  refine ⟨r, hr, ?_⟩
  intro s hs
  have hsstate : s ∈ Ioo (-rstate) rstate := by
    have hle : r ≤ rstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsgram : s ∈ Ioo (-p.radius) p.radius := by
    have hle : r ≤ p.radius := min_le_right _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hcurve : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic s := by
    have hstateAt := hstate s hsstate
    simpa [curve, IntrinsicGeodesic.localState, shift_state] using
      congrArg Bundle.TotalSpace.proj hstateAt
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  change inner ℝ ((p.toParallelGerm i).shiftedField s)
      ((p.toParallelGerm j).shiftedField s) = _
  have hcurve_i : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve (p.toParallelGerm i).localGeodesic s := by
    simpa only [ParallelFamilyGerm.toParallelGerm] using hcurve
  have hcurve_j : curve (shift γ t₀) s =
      IntrinsicGeodesic.LocalGeodesic.curve (p.toParallelGerm j).localGeodesic s := by
    simpa only [ParallelFamilyGerm.toParallelGerm] using hcurve
  rw [ParallelGerm.shiftedField_eq_of_curve_eq (p.toParallelGerm i) s hcurve_i,
    ParallelGerm.shiftedField_eq_of_curve_eq (p.toParallelGerm j) s hcurve_j]
  have hresult :=
    (cast_tangent_inner_of_eq (I := I) (M := M) hcurve
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic (p.coordinateSolution i) s)
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) p.localGeodesic (p.coordinateSolution j) s)).trans
      ((p.gram i j s hsgram).trans (hw i j))
  simpa only [ParallelFamilyGerm.toParallelGerm] using hresult

/-- An orthonormal parallel-frame germ whose distinguished initial vector is
the geodesic velocity yields, on one common interval of the actual shifted
global geodesic, a covariantly constant orthonormal transverse frame.  This
is the fully intrinsic local frame datum needed by second variation: every
field is in the true tangent fibre of the global curve. -/
theorem ParallelFamilyGerm.exists_interval_shiftedField_adapted
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w)
    (hw : Orthonormal ℝ w) (i₀ : ι)
    (hinit : w i₀ = velocity γ t₀) :
    ∃ r > (0 : ℝ), ∀ s ∈ Ioo (-r) r,
      (∀ i, IsCovariantAccelerationAt cov (curve (shift γ t₀))
        (p.shiftedField i) s (velocity (shift γ t₀) s) 0) ∧
      Orthonormal ℝ (fun i ↦ p.shiftedField i s) ∧
      p.shiftedField i₀ s = velocity (shift γ t₀) s ∧
      ∀ i ∈ Finset.univ.erase i₀,
        inner ℝ (p.shiftedField i s) (velocity (shift γ t₀) s) = 0 := by
  obtain ⟨rparallel, hrparallel, hparallel⟩ :=
    p.exists_interval_shiftedField_isCovariantAccelerationAt_zero
  obtain ⟨rorth, hrorth, horth⟩ :=
    p.exists_interval_shiftedField_orthonormal hw
  have hfirstGerm :=
    (p.toParallelGerm i₀).shiftedField_eventuallyEq_velocity_of_initial hinit
  obtain ⟨rfirst, hrfirst, hfirst⟩ :=
    exists_pos_radius_of_eventually hfirstGerm
  let r : ℝ := min rparallel (min rorth rfirst)
  have hr : 0 < r := lt_min hrparallel (lt_min hrorth hrfirst)
  refine ⟨r, hr, ?_⟩
  intro s hs
  have hsparallel : s ∈ Ioo (-rparallel) rparallel := by
    have hle : r ≤ rparallel := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsorth : s ∈ Ioo (-rorth) rorth := by
    have hle : r ≤ rorth := le_trans (min_le_right _ _) (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsfirst : s ∈ Ioo (-rfirst) rfirst := by
    have hle : r ≤ rfirst := le_trans (min_le_right _ _) (min_le_right _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hfirst' : p.shiftedField i₀ s = velocity (shift γ t₀) s := by
    change (p.toParallelGerm i₀).shiftedField s = _
    exact hfirst s hsfirst
  have horth' := horth s hsorth
  refine ⟨?_, horth', hfirst', ?_⟩
  · intro i
    exact hparallel i s hsparallel
  · intro i hi
    have hine : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    rw [← hfirst']
    rw [orthonormal_iff_ite] at horth'
    rw [horth' i i₀]
    simp [hine]

/-- The local parallel frame defines a linear isometry from the initial
tangent fibre to the tangent fibre of the actual shifted global geodesic.
This is a concrete local parallel-transport map: it sends each chosen initial
orthonormal basis vector to its reindexed parallel field. -/
noncomputable def ParallelFamilyGerm.shiftedTransport
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i))
    (s : ℝ) (horth : Orthonormal ℝ (fun i ↦ p.shiftedField i s)) :
    TM (curve γ t₀) →ₗᵢ[ℝ] TM (curve (shift γ t₀) s) := by
  classical
  let f : TM (curve γ t₀) →ₗ[ℝ] TM (curve (shift γ t₀) s) :=
    b.toBasis.constr ℝ (fun i ↦ p.shiftedField i s)
  apply f.isometryOfOrthonormal (v := b.toBasis)
  · simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  ·
    have hf : (f : TM (curve γ t₀) → TM (curve (shift γ t₀) s)) ∘ b.toBasis =
        fun i ↦ p.shiftedField i s := by
      funext i
      exact b.toBasis.constr_basis ℝ (fun i ↦ p.shiftedField i s) i
    rw [hf]
    exact horth

/-- The local transport isometry has the intended value on every initial
frame vector. -/
theorem ParallelFamilyGerm.shiftedTransport_apply_basis
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i))
    (s : ℝ) (horth : Orthonormal ℝ (fun i ↦ p.shiftedField i s))
    (i : ι) :
    p.shiftedTransport s horth (b i) = p.shiftedField i s := by
  change (b.toBasis.constr ℝ (fun i ↦ p.shiftedField i s)) (b i) =
    p.shiftedField i s
  exact b.toBasis.constr_basis ℝ (fun i ↦ p.shiftedField i s) i

/-- The local transport isometry has the correct identity value at its
restart time.  This is stated in the total tangent bundle so the unavoidable
dependent-fibre identification at `s = 0` is explicit rather than hidden by
a coercion. -/
theorem ParallelFamilyGerm.shiftedTransport_initial_totalState_apply_basis
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i))
    (horth : Orthonormal ℝ (fun i ↦ p.shiftedField i 0)) (i : ι) :
    (⟨curve (shift γ t₀) 0, p.shiftedTransport 0 horth (b i)⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ t₀, b i⟩ := by
  rw [p.shiftedTransport_apply_basis 0 horth i]
  exact (p.toParallelGerm i).shiftedField_initial_totalState

/-- Once two local parallel-frame constructions have the same values on an
orthonormal basis at a given time, the induced transport isometries coincide.
This isolates the linear-algebra part of transport gluing from the separate
geometric proof that independently chosen local fields agree. -/
theorem ParallelFamilyGerm.shiftedTransport_eq_of_shiftedField_eq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p q : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i))
    (s : ℝ) (hp : Orthonormal ℝ (fun i ↦ p.shiftedField i s))
    (hq : Orthonormal ℝ (fun i ↦ q.shiftedField i s))
    (hfield : ∀ i, p.shiftedField i s = q.shiftedField i s) :
    p.shiftedTransport s hp = q.shiftedTransport s hq := by
  apply LinearIsometry.toLinearMap_injective
  apply b.toBasis.ext
  intro i
  change p.shiftedTransport s hp (b i) = q.shiftedTransport s hq (b i)
  rw [p.shiftedTransport_apply_basis s hp i,
    q.shiftedTransport_apply_basis s hq i]
  exact hfield i

/-- The local transport map is independent, as a germ, of the arbitrary
choice of canonical parallel-frame solutions at a fixed global-geodesic
restart.  The quantification over the orthonormality certificates makes this
an equality of the actual induced linear isometries, not merely equality of
their displayed basis vectors. -/
theorem ParallelFamilyGerm.eventually_forall_shiftedTransport_eq_of_same_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p q : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ hp : Orthonormal ℝ (fun i ↦ p.shiftedField i s),
        ∀ hq : Orthonormal ℝ (fun i ↦ q.shiftedField i s),
          p.shiftedTransport s hp = q.shiftedTransport s hq := by
  have hmember : ∀ i, ∀ᶠ s in 𝓝 (0 : ℝ),
      p.shiftedField i s = q.shiftedField i s := by
    intro i
    change (p.toParallelGerm i).shiftedField =ᶠ[𝓝 (0 : ℝ)]
      (q.toParallelGerm i).shiftedField
    exact (p.toParallelGerm i).shiftedField_eventuallyEq_of_same_initial
      (q.toParallelGerm i)
  have hfields : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ i ∈ (Finset.univ : Finset ι),
        p.shiftedField i s = q.shiftedField i s :=
    (Finset.eventually_all Finset.univ).2 fun i _ ↦ hmember i
  filter_upwards [hfields] with s hs
  intro hp hq
  apply p.shiftedTransport_eq_of_shiftedField_eq q s hp hq
  intro i
  exact hs i (Finset.mem_univ i)

/-- Since tangent fibres have the same finite dimension, the local transport
isometry is surjective as well.  It is therefore a genuine linear isometric
equivalence between the initial fibre and the fibre of the shifted global
geodesic at the specified time. -/
noncomputable def ParallelFamilyGerm.shiftedTransportEquiv
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i))
    (s : ℝ) (horth : Orthonormal ℝ (fun i ↦ p.shiftedField i s)) :
    TM (curve γ t₀) ≃ₗᵢ[ℝ] TM (curve (shift γ t₀) s) := by
  let T := p.shiftedTransport s horth
  have hdim : Module.finrank ℝ (TM (curve γ t₀)) =
      Module.finrank ℝ (TM (curve (shift γ t₀) s)) :=
    tangent_finrank_eq (I := I) (M := M) (curve γ t₀)
      (curve (shift γ t₀) s)
  let e : TM (curve γ t₀) ≃ₗ[ℝ] TM (curve (shift γ t₀) s) :=
    T.toLinearMap.linearEquivOfInjective T.injective hdim
  apply e.isometryOfOrthonormal (v := b.toBasis)
  · simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  ·
    have he : (e : TM (curve γ t₀) → TM (curve (shift γ t₀) s)) ∘ b.toBasis =
        fun i ↦ p.shiftedField i s := by
      funext i
      change e (b i) = p.shiftedField i s
      rw [show e (b i) = T.toLinearMap (b i) by
        exact LinearMap.linearEquivOfInjective_apply T.injective hdim (b i)]
      exact p.shiftedTransport_apply_basis s horth i
    rw [he]
    exact horth

/-- The local transport equivalence sends each initial frame vector to its
parallel continuation on the actual global curve. -/
theorem ParallelFamilyGerm.shiftedTransportEquiv_apply_basis
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i))
    (s : ℝ) (horth : Orthonormal ℝ (fun i ↦ p.shiftedField i s))
    (i : ι) :
    p.shiftedTransportEquiv s horth (b i) = p.shiftedField i s := by
  change p.shiftedTransport s horth (b i) = p.shiftedField i s
  exact p.shiftedTransport_apply_basis s horth i

/-- A unit-speed global geodesic has an adapted local parallel frame at every
time.  The first field is the actual local geodesic velocity, while all other
fields are orthogonal to it on one common nonempty interval.  This packages
the precise transverse-frame datum required by the index-form construction;
the fields remain on their certified local geodesic until the separate global
gluing theorem is proved. -/
theorem exists_adapted_parallelFamilyGerm
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (hmetric : cov.IsMetricCompatibleTangent)
    (hunit : ‖velocity γ t₀‖ = 1)
    (hn : 1 ≤ Module.finrank ℝ (TM (curve γ t₀))) :
    letI : Nonempty (Fin (Module.finrank ℝ (TM (curve γ t₀)))) :=
      ⟨⟨0, by omega⟩⟩
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
          (TM (curve γ t₀)),
      b ⟨0, by omega⟩ = velocity γ t₀ ∧
      ∃ p : ParallelFamilyGerm (I := I) (M := M) γ t₀ (fun i ↦ b i),
        ∃ r > (0 : ℝ), ∀ s ∈ Ioo (-r) r,
          IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
            (I := I) (M := M) p.localGeodesic
            (p.coordinateSolution ⟨0, by omega⟩) s =
            IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic s ∧
          Orthonormal ℝ (fun i ↦
            IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) p.localGeodesic (p.coordinateSolution i) s) ∧
          ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
            Fin (Module.finrank ℝ (TM (curve γ t₀)))),
            inner ℝ
              (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
                (I := I) (M := M) p.localGeodesic (p.coordinateSolution i) s)
              (IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic s) = 0 := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_first hunit hn
  let i0 : Fin (Module.finrank ℝ (TM (curve γ t₀))) := ⟨0, by omega⟩
  letI : Nonempty (Fin (Module.finrank ℝ (TM (curve γ t₀)))) := ⟨i0⟩
  obtain ⟨p⟩ := exists_parallelFamilyGerm (I := I) (M := M)
    γ t₀ (fun i ↦ b i) hmetric
  refine ⟨b, hb, p, ?_⟩
  have hstate0 : γ.state t₀ = IntrinsicGeodesic.localState p.localGeodesic 0 := by
    simpa using p.agrees.self_of_nhds
  have hvelocity0 : velocity γ t₀ =
      IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic 0 := by
    change (γ.state t₀).snd = (IntrinsicGeodesic.localState p.localGeodesic 0).snd
    rw [hstate0]
  have hinit : IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
      (I := I) (M := M) p.localGeodesic (p.coordinateSolution i0) 0 =
      IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic 0 := by
    have hfield := p.initial i0
    have hbi0 : b i0 = velocity γ t₀ := by
      simpa [i0] using hb
    exact hfield.trans (hbi0.trans hvelocity0)
  have hfirst :=
    IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel_eventuallyEq_velocity_of_initial
      (I := I) (M := M) p.localGeodesic (p.coordinateSolution i0) hinit
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hfirst
  have horth := ParallelFamilyGerm.orthonormal_near_zero p b.orthonormal
  let r : ℝ := min p.radius (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min p.radius_pos (by linarith)
  refine ⟨r, hr, ?_⟩
  intro s hs
  have hrp : r ≤ p.radius := min_le_left _ _
  have hsp : s ∈ Ioo (-p.radius) p.radius := by
    exact ⟨lt_of_le_of_lt (neg_le_neg hrp) hs.1,
      lt_of_lt_of_le hs.2 hrp⟩
  have hrδ : r ≤ δ / 2 := min_le_right _ _
  have habs : |s| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2, hrδ]
  have hsfirst : IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
      (I := I) (M := M) p.localGeodesic (p.coordinateSolution i0) s =
      IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic s := by
    apply hδsub
    rw [Metric.mem_ball]
    simpa [dist_zero_right] using habs
  have hsorth := horth s hsp
  refine ⟨?_, hsorth, ?_⟩
  · simpa [i0] using hsfirst
  · intro i hi
    have hine : i ≠ i0 := by
      have hne0 := (Finset.mem_erase.mp hi).1
      simpa [i0] using hne0
    rw [← hsfirst]
    rw [orthonormal_iff_ite] at hsorth
    rw [hsorth i i0]
    simp [hine]

end GlobalGeodesic
end IntrinsicGeodesic

end BonnetMyersEntry
