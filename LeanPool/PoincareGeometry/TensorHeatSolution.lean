/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasSymmetricWellPosedness

/-!
# Short-time heat well-posedness for symmetric covariant two-tensors

The statement exposes the geometric equation independently of the proof
development.  The rough Laplacian is the orthonormal trace of the second
covariant derivative, expanded using Mathlib's manifold derivative and the
given tangent connection.  The conclusion constructs finite-atlas coefficient
spaces and their geometric readouts.  For every represented symmetric spatial
datum and symmetric parabolic source, there is a unique coefficient witness
whose readout has the asserted initial trace, is fiberwise symmetric, solves
the actual tensor heat equation, and satisfies a global finite-atlas Schauder
estimate.

This is deliberately a theorem for the constructed finite-atlas Holder data
class.  It does not assert that every bare intrinsic section has such a
coefficient representation, and uniqueness is of the atlas coefficient
witness in the constructed classical class.
-/

@[expose] public section

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology BigOperators

namespace SymmetricTensorHeatEntry

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance challengeTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
@[reducible] local instance challengeTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance challengeTwoTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) (fun x => TM x →L[ℝ] ℝ)
local instance challengeTwoFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) (fun x => TM x →L[ℝ] ℝ)
local instance challengeTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) (fun x => TM x →L[ℝ] ℝ)
@[reducible] local instance challengeThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
@[reducible] local instance challengeThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance
local instance challengeThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance challengeThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance challengeThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- A connection on covariant two-tensors is the one induced by `cov` when it
obeys the actual three-slot Leibniz formula on differentiable sections. -/
def IsInducedTwoTensorConnection
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂) : Prop :=
  ∀ (h : ∀ x : M, T₂ x) (U V : ∀ x : M, TM x) (x : M),
    MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x →
      MDiffAt (T% U) x → MDiffAt (T% V) x →
      ∀ X : TM x,
        cov₂ h x X (U x) (V x) =
          mvfderiv (I := I) (fun y => h y (U y) (V y)) x X
            - h x (cov U x X) (V x) - h x (U x) (cov V x X)

/-- A connection on covariant three-tensors is the one induced by `cov` when
it obeys the actual four-slot Leibniz formula on differentiable sections. -/
def IsInducedThreeTensorConnection
    (cov : CovariantDerivative I E TM)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) : Prop :=
  ∀ (K : ∀ x : M, T₃ x) (U V W : ∀ x : M, TM x) (x : M),
    MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y (K y)) x →
      MDiffAt (T% U) x → MDiffAt (T% V) x →
      MDiffAt (T% W) x → ∀ X : TM x,
        cov₃ K x X (U x) (V x) (W x) =
          mvfderiv (I := I) (fun y => K y (U y) (V y) (W y)) x X
            - K x (cov U x X) (V x) (W x)
            - K x (U x) (cov V x X) (W x)
            - K x (U x) (V x) (cov W x X)

/-- The actual rough Laplacian `tr_g(∇²h)` evaluated on two tangent
vectors, with the positive-coordinate sign convention.  The two tensor
connections are constrained by `IsInducedTwoTensorConnection` and
`IsInducedThreeTensorConnection` in the selected theorem. -/
def connectionLaplacianApply
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (cov₃ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (h : ∀ x : M, T₂ x)
    (x : M) (u v : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  ∑ i : Fin (Module.finrank ℝ (TM x)),
    cov₃ (cov₂ h) x (b i) (b i) u v

/-- Fiberwise symmetry of a covariant two-tensor section. -/
def IsSymmetricSection (h : ∀ x : M, T₂ x) : Prop :=
  ∀ x : M, ∀ u v : TM x, h x u v = h x v u

/-- Pointwise initial trace from the finite forward interval. -/
def HasInitialTrace (t₀ S : ℝ) (u : ℝ → ∀ x : M, T₂ x)
    (u₀ : ∀ x : M, T₂ x) : Prop :=
  ∀ x : M, Tendsto (fun t : ℝ => u t x)
    (nhdsWithin t₀ (Ioc t₀ S)) (nhds (u₀ x))

/-- Temporal differentiability after evaluation on arbitrary fiber vectors. -/
def HasTimeDerivative (t₀ S : ℝ)
    (u du : ℝ → ∀ x : M, T₂ x) : Prop :=
  ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M, ∀ a b : TM x,
    HasDerivAt (fun s : ℝ => u s x a b) (du t x a b) t

/-- The componentwise tensor heat equation with the explicitly expanded
connection Laplacian above. -/
def SolvesTensorHeat
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (cov₃ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (t₀ S : ℝ)
    (u du f : ℝ → ∀ x : M, T₂ x) : Prop :=
  ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M, ∀ a b : TM x,
    du t x a b - connectionLaplacianApply cov₂ cov₃ (u t) x a b = f t x a b

/-- Metric compatibility written as the genuine manifold Leibniz rule. -/
def IsMetricCompatibleTangent (cov : CovariantDerivative I E TM) : Prop :=
  ∀ {x : M} {U V : ∀ y : M, TM y},
    MDiffAt (T% U) x → MDiffAt (T% V) x → ∀ w : TM x,
      mvfderiv (I := I) (fun y => inner ℝ (U y) (V y)) x w =
        inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)

/-- The torsion-free, metric-compatible Levi--Civita conditions. -/
def IsLeviCivita (cov : CovariantDerivative I E TM) : Prop :=
  cov.torsion = 0 ∧ IsMetricCompatibleTangent cov

/-- The parabolic metric used by the finite-atlas Hölder norms: time has
weight two and space has weight one. -/
def parabolicDistance {X : Type u} [PseudoMetricSpace X]
    (p q : ℝ × X) : ℝ :=
  max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2)

/-- An explicit, single-radius parabolic `C⁰ᵃ` certificate.  The displayed
radius simultaneously dominates a sup bound and a Hölder seminorm bound. -/
def HasParabolicC0AlphaNormLe {X : Type u} {V : Type v} [PseudoMetricSpace X]
    [NormedAddCommGroup V] (t₀ S α N : ℝ) (f : ℝ × X → V) : Prop :=
  ∃ B ≥ 0, ∃ H ≥ 0, B + H ≤ N ∧
    (∀ z, z.1 ∈ Ioc t₀ S → ‖f z‖ ≤ B) ∧
    ∀ p, p.1 ∈ Ioc t₀ S → ∀ q, q.1 ∈ Ioc t₀ S →
      ‖f p - f q‖ ≤ H * parabolicDistance p q ^ α

/-- A concrete bounded spatial `C²ᵃ` jet with its genuine first and second
Fréchet derivatives and one displayed norm radius. -/
def HasSpatialC2AlphaNormLe {X : Type u} {V : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (α N : ℝ) (f : X → V) (df : X → X →L[ℝ] V)
    (d2f : X → X →L[ℝ] X →L[ℝ] V) : Prop :=
  0 ≤ N ∧
    (∀ x, ‖f x‖ ≤ N) ∧ (∀ x, ‖df x‖ ≤ N) ∧
    (∀ x, ‖d2f x‖ ≤ N) ∧
    (∀ x y, ‖f x - f y‖ ≤ N * dist x y ^ α) ∧
    (∀ x y, ‖df x - df y‖ ≤ N * dist x y ^ α) ∧
    (∀ x y, ‖d2f x - d2f y‖ ≤ N * dist x y ^ α) ∧
    (∀ x, HasFDerivAt f (df x) x) ∧
    ∀ x, HasFDerivAt df (d2f x) x

/-- A concrete finite-cylinder `C²⁺ᵃ,¹⁺ᵃ/²` jet.  All four
components have genuine parabolic Hölder bounds controlled by the displayed
Schauder norm, and the derivative fields are the actual derivatives. -/
def HasParabolicC2AlphaNormLe {X : Type u} {V : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t₀ S α N : ℝ) (f : ℝ × X → V)
    (df : ℝ × X → X →L[ℝ] V)
    (d2f : ℝ × X → X →L[ℝ] X →L[ℝ] V)
    (dtf : ℝ × X → V) : Prop :=
  HasParabolicC0AlphaNormLe t₀ S α N f ∧
    HasParabolicC0AlphaNormLe t₀ S α N df ∧
    HasParabolicC0AlphaNormLe t₀ S α N d2f ∧
    HasParabolicC0AlphaNormLe t₀ S α N dtf ∧
    (∀ t, t ∈ Ioc t₀ S → ∀ x, HasFDerivAt (fun y => f (t, y)) (df (t, x)) x) ∧
    (∀ t, t ∈ Ioc t₀ S → ∀ x,
      HasFDerivAt (fun y => df (t, y)) (d2f (t, x)) x) ∧
    ∀ t, t ∈ Ioo t₀ S → ∀ x,
      HasDerivAt (fun s => f (s, x)) (dtf (t, x)) t

/-- The complete Mathlib-facing statement.  The existential types are the
finite-atlas initial, source, and higher-coefficient spaces constructed by the
proof.  Their readout maps expose every geometric conclusion, while
`coordinateClass` records the precise unique atlas solution class rather than
claiming uniqueness among unrepresented bare fields. -/
def completeStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [Nontrivial E]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [CompactSpace M] [SigmaCompactSpace M]
    [I.Boundaryless] [Nonempty M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1]
    (cov₂ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    [cov₂.ContMDiffCovariantDerivative 1]
    [cov₂.ContMDiffCovariantDerivative 2]
    [cov₃.ContMDiffCovariantDerivative 1]
    (t₀ α : ℝ),
    let inducedTwo : Prop :=
      ∀ (h : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ)
        (U V : ∀ x : M, TangentSpace I x) (x : M),
        MDiffAt (fun y => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M => TangentSpace I z →L[ℝ]
            TangentSpace I z →L[ℝ] ℝ) y (h y)) x →
        MDiffAt (T% U) x → MDiffAt (T% V) x →
        ∀ X : TangentSpace I x,
          cov₂ h x X (U x) (V x) =
            mvfderiv (I := I) (fun y => h y (U y) (V y)) x X
              - h x (cov U x X) (V x) - h x (U x) (cov V x X)
    let inducedThree : Prop :=
      ∀ (K : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (U V W : ∀ x : M, TangentSpace I x) (x : M),
        MDiffAt (fun y => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M => TangentSpace I z →L[ℝ]
            TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y (K y)) x →
        MDiffAt (T% U) x → MDiffAt (T% V) x → MDiffAt (T% W) x →
        ∀ X : TangentSpace I x,
          cov₃ K x X (U x) (V x) (W x) =
            mvfderiv (I := I) (fun y => K y (U y) (V y) (W y)) x X
              - K x (cov U x X) (V x) (W x)
              - K x (U x) (cov V x X) (W x)
              - K x (U x) (V x) (cov W x X)
    let roughLaplacian := fun
        (h : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ)
        (x : M) (u v : TangentSpace I x) =>
      letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
      let b := stdOrthonormalBasis ℝ (TangentSpace I x)
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        cov₃ (cov₂ h) x (b i) (b i) u v
    let symmetric := fun
        (h : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ x : M, ∀ u v : TangentSpace I x, h x u v = h x v u
    let initialTrace := fun (S : ℝ)
        (u : ℝ → ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ)
        (u₀ : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ x : M, Tendsto (fun t : ℝ => u t x)
        (nhdsWithin t₀ (Ioc t₀ S)) (nhds (u₀ x))
    let timeDerivative := fun (S : ℝ)
        (u du : ℝ → ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M,
        ∀ a b : TangentSpace I x,
          HasDerivAt (fun s : ℝ => u s x a b) (du t x a b) t
    let solves := fun (S : ℝ)
        (u du f : ℝ → ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M,
        ∀ a b : TangentSpace I x,
          du t x a b - roughLaplacian (u t) x a b = f t x a b
    let metricCompatible : Prop :=
      ∀ {x : M} {U V : ∀ y : M, TangentSpace I y},
        MDiffAt (T% U) x → MDiffAt (T% V) x →
        ∀ w : TangentSpace I x,
          mvfderiv (I := I) (fun y => inner ℝ (U y) (V y)) x w =
            inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)
    let leviCivita : Prop := cov.torsion = 0 ∧ metricCompatible
    leviCivita → inducedTwo → inducedThree →
    0 < α → α < 1 →
    ∃ (S : ℝ), t₀ < S ∧
      ∃ (Tcoord : ℝ), t₀ < Tcoord ∧
      ∃ (Index Initial Source Solution : Type u)
        (_indexFinite : Finite Index) (_indexNonempty : Nonempty Index)
        (initialTensor : Initial →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (sourceTensor : Source → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionTensor : Solution → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionTimeDerivative : Solution → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (initialLocalTensor : Initial → Index →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (sourceLocalTensor : Source → Index → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionLocalTensor : Solution → Index → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionLocalTimeDerivative : Solution → Index → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (atlasCoordinate : Index → M → E)
        (atlasFrame : Index → Fin (Module.finrank ℝ E) →
          ∀ x : M, TangentSpace I x)
        (atlasWeight : Index → M → ℝ)
        (normalizedTimeCoordinate : Index → ℝ → ℝ)
        (sourceRescale : Index → ℝ)
        (initialValue : Initial → Index → E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialSpaceDeriv : Initial → Index → E →
          E →L[ℝ] (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialSpaceSecondDeriv : Initial → Index → E →
          E →L[ℝ] E →L[ℝ]
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialHolderConstant : Initial → Index → ℝ)
        (sourceValue : Source → Index → ℝ × E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionValue : Solution → Index → ℝ × E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionSpaceDeriv : Solution → Index → ℝ × E →
          E →L[ℝ] (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionSpaceSecondDeriv : Solution → Index → ℝ × E →
          E →L[ℝ] E →L[ℝ]
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionTimeDerivCoordinate : Solution → Index → ℝ × E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialSize : Initial → ℝ) (sourceNorm : Source → ℝ)
        (solutionNorm : Solution → ℝ)
        (coordinateClass : Initial → Source → Solution → Prop)
        (C : ℝ),
        Nonempty Initial ∧ Nonempty Source ∧ Nonempty Solution ∧ 0 ≤ C ∧
        (∀ x, ∑ᶠ i, atlasWeight i x = 1) ∧
        (∀ i x, 0 ≤ atlasWeight i x) ∧
        (∀ i, 0 < sourceRescale i) ∧
        (∀ i t, t ∈ Ioo t₀ S →
          normalizedTimeCoordinate i t ∈ Ioc t₀ Tcoord) ∧
        (∀ i x, atlasWeight i x ≠ 0 → ∀ v,
          ∃ a : Fin (Module.finrank ℝ E) → ℝ,
          v = ∑ p, a p • atlasFrame i p x) ∧
        (∀ D x, initialTensor D x = ∑ᶠ i, initialLocalTensor D i x) ∧
        (∀ f t x, sourceTensor f t x = ∑ᶠ i, sourceLocalTensor f i t x) ∧
        (∀ q t, t ∈ Ioc t₀ S → ∀ x a b,
          solutionTensor q t x a b =
            ((∑ᶠ i, solutionLocalTensor q i t x a b) +
              ∑ᶠ i, solutionLocalTensor q i t x b a) / 2) ∧
        (∀ q t, t ∈ Ioo t₀ S → ∀ x a b,
          solutionTimeDerivative q t x a b =
            ((∑ᶠ i, solutionLocalTimeDerivative q i t x a b) +
              ∑ᶠ i, solutionLocalTimeDerivative q i t x b a) / 2) ∧
        (∀ D i x, atlasWeight i x = 0 → initialLocalTensor D i x = 0) ∧
        (∀ f i t x, atlasWeight i x = 0 → sourceLocalTensor f i t x = 0) ∧
        (∀ q i t x, atlasWeight i x = 0 → solutionLocalTensor q i t x = 0) ∧
        (∀ q i t x, atlasWeight i x = 0 →
          solutionLocalTimeDerivative q i t x = 0) ∧
        (∀ D i x p k,
          initialLocalTensor D i x (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x * initialValue D i (atlasCoordinate i x) (k, p)) ∧
        (∀ f i t x p k,
          sourceLocalTensor f i t x (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x * (sourceRescale i *
              sourceValue f i (normalizedTimeCoordinate i t,
                atlasCoordinate i x) (k, p))) ∧
        (∀ q i t, t ∈ Ioc t₀ S → ∀ x p k,
          solutionLocalTensor q i t x (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x *
              solutionValue q i (normalizedTimeCoordinate i t,
                atlasCoordinate i x) (k, p)) ∧
        (∀ q i t, t ∈ Ioo t₀ S → ∀ x p k,
          solutionLocalTimeDerivative q i t x
              (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x * (sourceRescale i *
              solutionTimeDerivCoordinate q i (normalizedTimeCoordinate i t,
                atlasCoordinate i x) (k, p))) ∧
        Function.Injective (fun D =>
          (initialValue D, initialSpaceDeriv D,
            initialSpaceSecondDeriv D, initialHolderConstant D)) ∧
        Function.Injective sourceValue ∧
        Function.Injective (fun q =>
          (solutionValue q, solutionSpaceDeriv q,
            solutionSpaceSecondDeriv q, solutionTimeDerivCoordinate q)) ∧
        (∀ c : Index →
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ),
          ∃ D, ∀ i x, initialValue D i x = c i) ∧
        (∀ c : Index →
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ),
          ∃ f, ∀ i z, z.1 ∈ Ioc t₀ Tcoord → sourceValue f i z = c i) ∧
        (∀ c : Index →
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ),
          ∃ q, ∀ i z, z.1 ∈ Ioc t₀ Tcoord → solutionValue q i z = c i) ∧
        (∀ D i, HasSpatialC2AlphaNormLe (X := E)
          (V := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ)
          α (initialSize D)
          (initialValue D i) (initialSpaceDeriv D i)
          (initialSpaceSecondDeriv D i)) ∧
        (∀ f i, HasParabolicC0AlphaNormLe (X := E)
          (V := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ)
          t₀ Tcoord α (sourceNorm f)
          (sourceValue f i)) ∧
        (∀ D, 0 ≤ initialSize D) ∧ (∀ f, 0 ≤ sourceNorm f) ∧
        (∀ D f,
          symmetric (initialTensor D) →
          (∀ t, t ∈ Ioo t₀ S → symmetric (sourceTensor f t)) →
          ∃! q : Solution,
            coordinateClass D f q ∧
            timeDerivative S (solutionTensor q) (solutionTimeDerivative q) ∧
            initialTrace S (solutionTensor q) (initialTensor D) ∧
            (∀ t, t ∈ Ioc t₀ S →
              symmetric (solutionTensor q t)) ∧
            solves S (solutionTensor q) (solutionTimeDerivative q) (sourceTensor f)) ∧
        (∀ D f q, coordinateClass D f q →
          (∀ i, HasParabolicC2AlphaNormLe (X := E)
            (V := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ)
            t₀ Tcoord α (solutionNorm q)
            (solutionValue q i) (solutionSpaceDeriv q i)
            (solutionSpaceSecondDeriv q i) (solutionTimeDerivCoordinate q i)) ∧
          solutionNorm q ≤ C * (initialSize D + sourceNorm f))

private theorem canonicalTwo_apply_eq
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (hcov₂ : IsInducedTwoTensorConnection cov cov₂)
    (h : ∀ x : M, T₂ x) (x : M)
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x) :
    _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov h x =
      cov₂ h x := by
  ext X u v
  let U := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x u
  let V := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x v
  have hU : MDiffAt (T% U) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x u).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hV : MDiffAt (T% V) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x v).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  rw [_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
    cov hh X u v]
  have H := hcov₂ h U V x hh hU hV X
  simpa [U, V, _root_.CovariantDerivative.smoothExtend_apply] using H.symm

private theorem canonicalThree_apply_eq
    (cov : CovariantDerivative I E TM)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (hcov₃ : IsInducedThreeTensorConnection cov cov₃)
    (K : ∀ x : M, T₃ x) (x : M)
    (hK : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y (K y)) x) :
    _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov K x =
      cov₃ K x := by
  ext X u v w
  let U := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x u
  let V := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x v
  let W := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x w
  have hU : MDiffAt (T% U) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x u).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hV : MDiffAt (T% V) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x v).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hW : MDiffAt (T% W) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x w).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hKU : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (K y (U y))) x :=
    hK.clm_bundle_apply hU
  unfold _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative
  simp only [_root_.CovariantDerivative.inducedHomCovariantDerivative, dif_pos hK]
  rw [_root_.CovariantDerivative.inducedHomAtOfMDiff_apply]
  change
    (_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov
        (fun y => K y (U y)) x X) v w -
      K x (cov (_root_.CovariantDerivative.smoothExtend
          (I := I) (F := E) (V := TM) x u) x X) v w = _
  rw [_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
    cov hKU X v w]
  have H := hcov₃ K U V W x hK hU hV hW X
  simp only [U, V, W, _root_.CovariantDerivative.smoothExtend_apply] at H ⊢
  linear_combination H.symm

private theorem canonicalTwoRegularity
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (k : ℕ∞ω) [cov₂.ContMDiffCovariantDerivative k]
    (hcov₂ : IsInducedTwoTensorConnection cov cov₂)
    (hk : (1 : ℕ∞ω) ≤ k + 1) :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov) k where
  contMDiff := ⟨by
    intro h hh
    have heq :
        _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov h =
          cov₂ h := by
      funext x
      apply canonicalTwo_apply_eq cov cov₂ hcov₂ h x
      exact ((hh.contMDiffAt (isOpen_univ.mem_nhds (mem_univ x))).of_le hk).mdifferentiableAt
        one_ne_zero
    rw [heq]
    exact (inferInstance : cov₂.ContMDiffCovariantDerivative k).contMDiff.contMDiff hh⟩

private theorem canonicalThreeRegularity
    (cov : CovariantDerivative I E TM)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (k : ℕ∞ω) [cov₃.ContMDiffCovariantDerivative k]
    (hcov₃ : IsInducedThreeTensorConnection cov cov₃)
    (hk : (1 : ℕ∞ω) ≤ k + 1) :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (_root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov) k where
  contMDiff := ⟨by
    intro K hK
    have heq :
        _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov K =
          cov₃ K := by
      funext x
      apply canonicalThree_apply_eq cov cov₃ hcov₃ K x
      exact ((hK.contMDiffAt (isOpen_univ.mem_nhds (mem_univ x))).of_le hk).mdifferentiableAt
        one_ne_zero
    rw [heq]
    exact (inferInstance : cov₃.ContMDiffCovariantDerivative k).contMDiff.contMDiff hK⟩

private theorem connectionLaplacianApply_eq_canonical
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (hcov₂ : IsInducedTwoTensorConnection cov cov₂)
    (hcov₃ : IsInducedThreeTensorConnection cov cov₃)
    (h : _root_.CovariantDerivative.ConnectionLaplacianDomain
      (E := E) (I := I) (M := M) cov)
    (x : M) (u v : TM x) :
    connectionLaplacianApply cov₂ cov₃ h.1 x u v =
      _root_.CovariantDerivative.connectionLaplacian cov h.1 x u v := by
  let canonical₂ :=
    _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov
  have h₂ : canonical₂ h.1 = cov₂ h.1 := by
    funext y
    exact canonicalTwo_apply_eq cov cov₂ hcov₂ h.1 y (h.2.1 y)
  have hcov₃eq :
      _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov
          (cov₂ h.1) x = cov₃ (cov₂ h.1) x := by
    apply canonicalThree_apply_eq cov cov₃ hcov₃ (cov₂ h.1) x
    rw [← h₂]
    exact h.2.2 x
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [_root_.CovariantDerivative.connectionLaplacian_eq_sum_orthonormalBasis
    cov h.1 x b]
  unfold connectionLaplacianApply
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← hcov₃eq, ← h₂]
  rfl

private theorem strongAtlasSchauderConstant_nonneg
    {t₀ T α : ℝ} {d : ℕ}
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.StrongCommutatorLift
      cov A) :
    0 ≤ RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.strongAtlasSchauderConstant
      cov Hlift := by
  have hpos : 0 < 1 - ‖Hlift.sourceLift.toContinuousLinearMap‖ :=
    sub_pos.mpr Hlift.sourceLift.norm_lt_one
  unfold RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.strongAtlasSchauderConstant
  positivity

private theorem hasParabolicC0AlphaNormLe_of_banach
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {t₀ S T α N : ℝ} (hST : S ≤ T)
    (q : RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach X V α
      (RicciFlow.AnalyticPDE.parabolicFiniteCylinder X t₀ T))
    (hq : ‖q‖ ≤ N) :
    HasParabolicC0AlphaNormLe t₀ S α N
      (RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative q) := by
  let out := RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.outL q
  have hfull := RicciFlow.AnalyticPDE.parabolicC0AlphaNormLe_norm
    (RicciFlow.AnalyticPDE.ParabolicC0AlphaSpace.toSubmodule out).2
  have hnorm : RicciFlow.AnalyticPDE.parabolicC0AlphaNorm α
      (↑(RicciFlow.AnalyticPDE.ParabolicC0AlphaSpace.toSubmodule out) : ℝ × X → V)
      (RicciFlow.AnalyticPDE.parabolicFiniteCylinder X t₀ T) = ‖q‖ := by
    exact (RicciFlow.AnalyticPDE.ParabolicC0AlphaSpace.norm_def out).symm.trans
      (RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.norm_outL q)
  rw [hnorm] at hfull
  change RicciFlow.AnalyticPDE.ParabolicC0AlphaNormLe ‖q‖ α
    (RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative q)
    (RicciFlow.AnalyticPDE.parabolicFiniteCylinder X t₀ T) at hfull
  have hsmall := (hfull.mono_const hq).mono_set
    (RicciFlow.AnalyticPDE.parabolicFiniteCylinder_mono hST)
  rcases hsmall with ⟨B, hB, H, hH, hsum, hbounded, hholder⟩
  exact ⟨B, hB, H, hH, hsum,
    (by intro z hz; exact hbounded (by simpa [RicciFlow.AnalyticPDE.parabolicFiniteCylinder] using hz)),
    (by
      intro p hp q hq'
      simpa [parabolicDistance, RicciFlow.AnalyticPDE.parabolicDistance] using
        hholder (by simpa [RicciFlow.AnalyticPDE.parabolicFiniteCylinder] using hp)
          (by simpa [RicciFlow.AnalyticPDE.parabolicFiniteCylinder] using hq'))⟩

private def constSpatialData {d : ℕ} {α : ℝ}
    (c : Fin d × Fin d → ℝ) :
    RicciFlow.AnalyticPDE.BoundedSpatialC2AlphaData E
      (Fin d × Fin d → ℝ) α where
  value := BoundedContinuousFunction.const E c
  spaceDeriv := BoundedContinuousFunction.const E 0
  spaceSecondDeriv := BoundedContinuousFunction.const E 0
  holderConstant := 0
  holderConstant_nonneg := le_rfl
  value_holder := by
    intro x y
    change ‖c - c‖ ≤ 0 * dist x y ^ α
    simp
  spaceDeriv_holder := by
    intro x y
    change ‖(0 : E →L[ℝ] (Fin d × Fin d → ℝ)) - 0‖ ≤ 0 * dist x y ^ α
    simp
  spaceSecondDeriv_holder := by
    intro x y
    rw [BoundedContinuousFunction.const_apply]
    simp only [zero_mul, sub_self]
    exact le_of_eq
      (@norm_zero (E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) inferInstance)
  hasFDerivAt_value := by
    intro x
    change HasFDerivAt (fun _ : E => c)
      (0 : E →L[ℝ] (Fin d × Fin d → ℝ)) x
    exact hasFDerivAt_const (x := x) (c := c)
  hasFDerivAt_spaceDeriv := by
    intro x
    change HasFDerivAt
      (fun _ : E => (0 : E →L[ℝ] (Fin d × Fin d → ℝ)))
      (0 : E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) x
    exact hasFDerivAt_const (x := x)
      (c := (0 : E →L[ℝ] (Fin d × Fin d → ℝ)))

private def zeroSpatialData {d : ℕ} {α : ℝ} :
    RicciFlow.AnalyticPDE.BoundedSpatialC2AlphaData E
      (Fin d × Fin d → ℝ) α :=
  constSpatialData 0

private theorem boundedSpatialC2AlphaData_ext
    {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {α : ℝ}
    (a b : RicciFlow.AnalyticPDE.BoundedSpatialC2AlphaData X W α)
    (hv : a.value = b.value) (hd : a.spaceDeriv = b.spaceDeriv)
    (hdd : a.spaceSecondDeriv = b.spaceSecondDeriv)
    (hH : a.holderConstant = b.holderConstant) : a = b := by
  cases a
  cases b
  congr

private theorem partition_eq_zero_of_notMem_trivialization
    {d : ℕ} {t₀ T α : ℝ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {b : Module.Basis (Fin d) ℝ E}
    (A : RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) {x : M}
    (hx : x ∉ (trivializationAt E
      (TangentSpace I : M → Type _) (i : M)).baseSet) :
    A.cover.partition i x = 0 := by
  by_contra hne
  have hsupp : x ∈ Function.support (A.cover.partition i) :=
    Function.mem_support.mpr hne
  have hpiece : x ∈ (A.cover.pieces i : Set M) := subset_closure hsupp
  exact hx (A.patch_subset_trivialization (i : M)
    (A.cover.pieces_subset_domain i hpiece))

theorem symmetricTensorHeatShortTimeWellPosed : completeStatement := by
  dsimp only [completeStatement]
  intro E instNorm instSpace instFD instComplete instNontrivial H instTopH I M
    instTopM instCharted instT2 instManifold instCompact instSigma instBoundary
    instNonempty instRiem instRiemSmooth instVB cov instCov cov₂ cov₃
    instCov₂One instCov₂Two instCov₃One
    t₀ α hLevi hcov₂ hcov₃ hα hα1
  letI canonicalTwoOne := canonicalTwoRegularity cov cov₂ 1 hcov₂ (by norm_num)
  letI canonicalTwoTwo := canonicalTwoRegularity cov cov₂ 2 hcov₂ (by norm_num)
  letI canonicalThreeOne := canonicalThreeRegularity cov cov₃ 1 hcov₃ (by norm_num)
  have hLevi' : _root_.CovariantDerivative.IsLeviCivita cov := by
    refine ⟨hLevi.1, ?_⟩
    intro x U V hU hV w
    exact hLevi.2 hU hV w
  let b := Module.finBasis ℝ E
  let Traw := t₀ + 1
  have hTraw : t₀ < Traw := by dsimp [Traw]; linarith
  obtain ⟨Sraw, hSraw, hSrawT, A, Hlift, hunique, hwell⟩ :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.exists_short_symmetric_tensorHeat_wellPosed
      cov hLevi' b hTraw hα hα1
  let S := A.commonTerminalTime
  have hS : t₀ < S := A.lt_commonTerminalTime cov
  refine ⟨S, hS, ?_⟩
  refine ⟨Sraw, hSraw, ?_⟩
  let Index := A.cover.Index
  let Initial :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.AtlasSpatialInitialData cov A
  let Source :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.SourceSpace cov A
  let Solution :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.HigherCoefficientSpace cov A
  let initialTensor : Initial → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun D => RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.spatialInitialTensor
      cov A D
  let sourceTensor : Source → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun f t => A.physicalAtlasSourceSlice cov f t
  let solutionTensor : Solution → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun q => (A.symmetrizedAtlasField cov q).toFun
  let solutionTimeDerivative : Solution → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun q => (A.symmetrizedAtlasField cov q).timeDerivative
  let initialLocalTensor : Initial → Index → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun D i => RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix (I := I)
      (trivializationAt E (TangentSpace I : M → Type _) (i : M)) b
      (A.cover.partition i)
      (fun y => RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.tensorCoordinateReconstructionEquiv
        (Module.finrank ℝ E)
        ((D i).value (RicciFlow.AnalyticPDE.normalizedTensorHeatCoordinate
          (I := I) (i : M) (A.radius (i : M)) y)))
  let sourceLocalTensor : Source → Index → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun f i t => A.physicalLocalSourceSlice cov i (f i) t
  let solutionLocalTensor : Solution → Index → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun q i => (A.localFieldOfHigher cov i (q i)).toFun
  let solutionLocalTimeDerivative : Solution → Index → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun q i => (A.localFieldOfHigher cov i (q i)).timeDerivative
  let atlasCoordinate : Index → M → E :=
    fun i x => RicciFlow.AnalyticPDE.normalizedTensorHeatCoordinate
      (I := I) (i : M) (A.radius (i : M)) x
  let atlasFrame : Index → Fin (Module.finrank ℝ E) →
      ∀ x : M, TangentSpace I x :=
    fun i p x => (trivializationAt E
      (TangentSpace I : M → Type _) (i : M)).localFrame b p x
  let atlasWeight : Index → M → ℝ := fun i => A.cover.partition i
  let normalizedTimeCoordinate : Index → ℝ → ℝ :=
    fun i t => CovariantDerivative.FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (i : M)) t
  let sourceRescale : Index → ℝ := fun i => (A.radius (i : M))⁻¹ ^ 2
  let initialValue : Initial → Index → E →
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun D i x => (D i).value x
  let initialSpaceDeriv : Initial → Index → E →
      E →L[ℝ] (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun D i x => (D i).spaceDeriv x
  let initialSpaceSecondDeriv : Initial → Index → E →
      E →L[ℝ] E →L[ℝ]
        (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun D i x => (D i).spaceSecondDeriv x
  let initialHolderConstant : Initial → Index → ℝ :=
    fun D i => (D i).holderConstant
  let sourceValue : Source → Index → ℝ × E →
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun f i => RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative (f i)
  let solutionValue : Solution → Index → ℝ × E →
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun q i => RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.value (q i)
  let solutionSpaceDeriv : Solution → Index → ℝ × E →
      E →L[ℝ] (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun q i => RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.spaceDeriv (q i)
  let solutionSpaceSecondDeriv : Solution → Index → ℝ × E →
      E →L[ℝ] E →L[ℝ]
        (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun q i => RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.spaceSecondDeriv (q i)
  let solutionTimeDerivCoordinate : Solution → Index → ℝ × E →
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    fun q i => RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.timeDeriv (q i)
  let initialSize : Initial → ℝ :=
    fun D => A.spatialInitialSize cov D
  let sourceNorm : Source → ℝ := fun f => ‖f‖
  let solutionNorm : Solution → ℝ := fun q => ‖q‖
  let coordinateClass : Initial → Source → Solution → Prop :=
    fun D f q => A.SymmetricAtlasSpatialClassicalSolution cov Hlift D f q
  let C := A.strongAtlasSchauderConstant cov Hlift
  refine ⟨Index, Initial, Source, Solution, inferInstance, A.index_nonempty,
    initialTensor, sourceTensor, solutionTensor, solutionTimeDerivative,
    initialLocalTensor, sourceLocalTensor, solutionLocalTensor,
    solutionLocalTimeDerivative, atlasCoordinate, atlasFrame,
    atlasWeight, normalizedTimeCoordinate, sourceRescale,
    initialValue, initialSpaceDeriv, initialSpaceSecondDeriv,
    initialHolderConstant, sourceValue,
    solutionValue, solutionSpaceDeriv, solutionSpaceSecondDeriv,
    solutionTimeDerivCoordinate, initialSize, sourceNorm,
    solutionNorm, coordinateClass, C, ?_⟩
  refine ⟨⟨fun _ => zeroSpatialData⟩, ⟨0⟩, ⟨0⟩,
    strongAtlasSchauderConstant_nonneg cov Hlift, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The displayed weights are a genuine finite partition of unity.
    intro x
    dsimp [atlasWeight]
    exact A.cover.partition.sum_eq_one (Set.mem_univ x)
  · intro i x
    exact A.cover.partition.nonneg i x
  · -- Physical source scaling is strictly positive in every chart.
    intro i
    dsimp [sourceRescale]
    exact pow_pos (inv_pos.mpr (A.radius_pos (i : M))) 2
  · -- Physical solution time maps into the normalized coefficient cylinder.
    intro i t ht
    exact A.normalizedTime_mem_Ioc_of_mem_commonInterval cov i ht
  · -- Wherever a weight is active, the displayed local frame spans the fiber.
    intro i x hweight v
    have hsupp : x ∈ Function.support (A.cover.partition i) := by
      apply Function.mem_support.mpr
      simpa [atlasWeight] using hweight
    have hpiece : x ∈ (A.cover.pieces i : Set M) := subset_closure hsupp
    have hx : x ∈ (trivializationAt E
        (TangentSpace I : M → Type _) (i : M)).baseSet :=
      A.patch_subset_trivialization (i : M)
        (A.cover.pieces_subset_domain i hpiece)
    let e := trivializationAt E (TangentSpace I : M → Type _) (i : M)
    let bx := e.basisAt b hx
    refine ⟨fun p => bx.repr v p, ?_⟩
    change v = ∑ p, bx.repr v p • e.localFrame b p x
    simp_rw [e.localFrame_apply_of_mem_baseSet b hx]
    exact (bx.sum_repr v).symm
  · -- The global initial tensor is exactly the sum of its chart tensors.
    intro D x
    dsimp [initialTensor, initialLocalTensor]
    unfold RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.spatialInitialTensor
    rw [finsum_eq_sum_of_fintype]
  · -- The global source tensor is exactly the sum of its chart tensors.
    intro f t x
    dsimp [sourceTensor, sourceLocalTensor]
    unfold RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.physicalAtlasSourceSlice
    rw [finsum_eq_sum_of_fintype]
  · -- The geometric solution is the symmetrized sum of its local jets.
    intro q t ht x a b'
    change (A.symmetrizedAtlasField cov q).toFun t x a b' = _
    rw [A.symmetrizedAtlasField_toFun cov q t]
    simp only [Pi.smul_apply, Pi.add_apply, _root_.smul_apply, add_apply,
      smul_eq_mul]
    rw [A.atlasFieldOfHigher_transpose_toFun cov q t ht x a b']
    rw [A.atlasFieldOfHigher_toFun cov q t x]
    dsimp [solutionLocalTensor]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp only [_root_.sum_apply]
    rw [Finset.attach_eq_univ]
    ring
  · -- Its displayed time derivative is reconstructed from the same local jets.
    intro q t ht x a b'
    change (A.symmetrizedAtlasField cov q).timeDerivative t x a b' = _
    rw [A.symmetrizedAtlasField_timeDerivative cov q t]
    simp only [Pi.smul_apply, Pi.add_apply, _root_.smul_apply, add_apply,
      smul_eq_mul]
    rw [A.atlasFieldOfHigher_transpose_timeDerivative cov q t ht x a b']
    unfold RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.atlasFieldOfHigher
    simp only [CovariantDerivative.FiniteClassicalTensorHeatField.finsetSum_timeDerivative,
      _root_.sum_apply]
    dsimp [solutionLocalTimeDerivative]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    rw [Finset.attach_eq_univ]
    ring
  · -- A zero chart weight removes the corresponding initial tensor summand.
    intro D i x hweight
    dsimp [initialLocalTensor, atlasWeight] at hweight ⊢
    simp [RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix, hweight]
  · -- A zero chart weight removes the corresponding source tensor summand.
    intro f i t x hweight
    dsimp [sourceLocalTensor, atlasWeight] at hweight ⊢
    simp [RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.physicalLocalSourceSlice,
      RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix, hweight]
  · -- The same support law holds for every local solution value.
    intro q i t x hweight
    dsimp [atlasWeight] at hweight
    change RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix (I := I)
        (trivializationAt E (TangentSpace I : M → Type _) (i : M)) b
        (A.cover.partition i)
        (RicciFlow.AnalyticPDE.normalizedTensorHeatCoefficientSlice
          (I := I) (i : M) (A.radius (i : M))
          (RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
            (q i))
          (CovariantDerivative.FiniteClassicalTensorHeatField.normalizedTime
            t₀ (A.radius (i : M)) t)) x = 0
    simp [RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix, hweight]
  · -- The same support law holds for local physical time derivatives.
    intro q i t x hweight
    dsimp [atlasWeight] at hweight
    change (A.radius (i : M))⁻¹ ^ 2 •
        RicciFlow.AnalyticPDE.normalizedTensorHeatTimeDerivative (I := I)
          (i : M) (A.radius (i : M)) b (A.cover.partition i)
          (RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
            (q i))
          (CovariantDerivative.FiniteClassicalTensorHeatField.normalizedTime
            t₀ (A.radius (i : M)) t) x = 0
    simp [RicciFlow.AnalyticPDE.normalizedTensorHeatTimeDerivative,
      RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix, hweight]
  · -- Initial matrix readouts are the actual local-frame coefficients.
    intro D i x p k
    let e := trivializationAt E (TangentSpace I : M → Type _) (i : M)
    by_cases hx : x ∈ e.baseSet
    · change RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix (I := I) e b
          (A.cover.partition i)
          (fun y => RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.tensorCoordinateReconstructionEquiv
            (Module.finrank ℝ E)
            ((D i).value (RicciFlow.AnalyticPDE.normalizedTensorHeatCoordinate
              (I := I) (i : M) (A.radius (i : M)) y))) x
          (e.localFrame b p x) (e.localFrame b k x) = _
      rw [RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix_localFrame
        (I := I) e b _ _ hx]
      simp [atlasWeight, initialValue, atlasCoordinate,
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.tensorCoordinateReconstructionEquiv_apply]
    · have hweight : A.cover.partition i x = 0 :=
        partition_eq_zero_of_notMem_trivialization cov A i hx
      simp [initialLocalTensor, atlasFrame, atlasWeight, atlasCoordinate,
        hweight, RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix]
  · -- Source matrix readouts are the actual rescaled local-frame coefficients.
    intro f i t x p k
    let e := trivializationAt E (TangentSpace I : M → Type _) (i : M)
    by_cases hx : x ∈ e.baseSet
    · change A.physicalLocalSourceSlice cov i (f i) t x
          (e.localFrame b p x) (e.localFrame b k x) = _
      rw [A.physicalLocalSourceSlice_localFrame cov i (f i) t hx p k]
    · have hweight : A.cover.partition i x = 0 :=
        partition_eq_zero_of_notMem_trivialization cov A i hx
      simp [sourceLocalTensor, atlasFrame, atlasWeight, atlasCoordinate,
        normalizedTimeCoordinate, sourceRescale, hweight,
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.physicalLocalSourceSlice,
        RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix]
  · -- Solution values are the coefficients of the reconstructed local tensors.
    intro q i t ht x p k
    let e := trivializationAt E (TangentSpace I : M → Type _) (i : M)
    let s := CovariantDerivative.FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (i : M)) t
    let ξ := RicciFlow.AnalyticPDE.normalizedTensorHeatCoordinate
      (I := I) (i : M) (A.radius (i : M)) x
    have hs : s ∈ Ioc t₀ Sraw := by
      apply CovariantDerivative.FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc
        (ne_of_gt (A.radius_pos (i : M)))
      exact ⟨ht.1, ht.2.trans (A.commonTerminalTime_le cov i)⟩
    have hz : (s, ξ) ∈ RicciFlow.AnalyticPDE.parabolicFiniteCylinder
        E t₀ Sraw := by
      simpa [RicciFlow.AnalyticPDE.parabolicFiniteCylinder] using hs
    by_cases hx : x ∈ e.baseSet
    · change RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix (I := I) e b
          (A.cover.partition i)
          (RicciFlow.AnalyticPDE.normalizedTensorHeatCoefficientSlice
            (I := I) (i : M) (A.radius (i : M))
            (RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
              (q i)) s) x
          (e.localFrame b p x) (e.localFrame b k x) =
        A.cover.partition i x *
          RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.value
            (q i) (s, ξ) (k, p)
      rw [RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix_localFrame
        (I := I) e b _ _ hx]
      unfold RicciFlow.AnalyticPDE.normalizedTensorHeatCoefficientSlice
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
      rw [RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.value_fiberPostcompL
        _ _ _ hz]
      simp [ξ,
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.tensorCoordinateReconstructionEquiv_apply]
    · have hweight : A.cover.partition i x = 0 :=
        partition_eq_zero_of_notMem_trivialization cov A i hx
      have hzero : (A.localFieldOfHigher cov i (q i)).toFun t x = 0 := by
        change RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix (I := I) e b
          (A.cover.partition i)
          (RicciFlow.AnalyticPDE.normalizedTensorHeatCoefficientSlice
            (I := I) (i : M) (A.radius (i : M))
            (RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
              (q i)) s) x = 0
        simp [RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix, hweight]
      change (A.localFieldOfHigher cov i (q i)).toFun t x
          (e.localFrame b p x) (e.localFrame b k x) =
        A.cover.partition i x * _
      rw [hweight, hzero, zero_mul]
      simp only [zero_apply]
  · -- Coordinate time derivatives reconstruct the physical local derivative.
    intro q i t ht x p k
    let e := trivializationAt E (TangentSpace I : M → Type _) (i : M)
    let s := CovariantDerivative.FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (i : M)) t
    let ξ := RicciFlow.AnalyticPDE.normalizedTensorHeatCoordinate
      (I := I) (i : M) (A.radius (i : M)) x
    have hs : s ∈ Ioc t₀ Sraw :=
      A.normalizedTime_mem_Ioc_of_mem_commonInterval cov i ht
    have hz : (s, ξ) ∈ RicciFlow.AnalyticPDE.parabolicFiniteCylinder
        E t₀ Sraw := by
      simpa [RicciFlow.AnalyticPDE.parabolicFiniteCylinder] using hs
    by_cases hx : x ∈ e.baseSet
    · change ((A.radius (i : M))⁻¹ ^ 2 •
          RicciFlow.AnalyticPDE.normalizedTensorHeatTimeDerivative (I := I)
            (i : M) (A.radius (i : M)) b (A.cover.partition i)
            (RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
              (q i)) s x)
          (e.localFrame b p x) (e.localFrame b k x) =
        A.cover.partition i x * ((A.radius (i : M))⁻¹ ^ 2 *
          RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.timeDeriv
            (q i) (s, ξ) (k, p))
      simp only [_root_.smul_apply, smul_eq_mul]
      rw [RicciFlow.AnalyticPDE.normalizedTensorHeatTimeDerivative,
        RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix_localFrame
          (I := I) e b _ _ hx]
      have hz' : (s, RicciFlow.AnalyticPDE.normalizedTensorHeatCoordinate
          (I := I) (i : M) (A.radius (i : M)) x) ∈
          RicciFlow.AnalyticPDE.parabolicFiniteCylinder E t₀ Sraw := by
        simpa [ξ] using hz
      unfold RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
      rw [RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL
        _ _ _ hz']
      dsimp [ξ]
      ring
    · have hweight : A.cover.partition i x = 0 :=
        partition_eq_zero_of_notMem_trivialization cov A i hx
      have hzero : (A.localFieldOfHigher cov i (q i)).timeDerivative t x = 0 := by
        change (A.radius (i : M))⁻¹ ^ 2 •
          RicciFlow.AnalyticPDE.normalizedTensorHeatTimeDerivative (I := I)
            (i : M) (A.radius (i : M)) b (A.cover.partition i)
            (RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.normalizedHigherSolution
              (q i)) s x = 0
        simp [RicciFlow.AnalyticPDE.normalizedTensorHeatTimeDerivative,
          RicciFlow.AnalyticPDE.cutoffLocalTensorOfMatrix, hweight]
      change (A.localFieldOfHigher cov i (q i)).timeDerivative t x
          (e.localFrame b p x) (e.localFrame b k x) =
        A.cover.partition i x * _
      rw [hweight, hzero, zero_mul]
      simp only [zero_apply]
  · -- Initial coefficient jets are a faithful representation.
    intro D D' h
    dsimp [initialValue, initialSpaceDeriv, initialSpaceSecondDeriv,
      initialHolderConstant] at h
    funext i
    have hv : (D i).value = (D' i).value := by
      apply DFunLike.coe_injective
      exact congrFun (congrArg Prod.fst h) i
    have hd : (D i).spaceDeriv = (D' i).spaceDeriv := by
      apply DFunLike.coe_injective
      exact congrFun (congrArg (fun p => p.2.1) h) i
    have hdd : (D i).spaceSecondDeriv = (D' i).spaceSecondDeriv := by
      apply DFunLike.coe_injective
      exact congrFun (congrArg (fun p => p.2.2.1) h) i
    have hH : (D i).holderConstant = (D' i).holderConstant :=
      congrFun (congrArg (fun p => p.2.2.2) h) i
    exact boundedSpatialC2AlphaData_ext (D i) (D' i) hv hd hdd hH
  · -- Canonical Hölder representatives faithfully encode source classes.
    intro f g h
    funext i
    apply RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.outL_injective
    apply Subtype.ext
    exact congrFun h i
  · -- The four canonical jet representatives faithfully encode solutions.
    intro q r h
    have hv := congrArg (fun p => p.1) h
    funext i
    apply RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.ext_value hα A.time_lt
    intro z _hz
    exact congrFun (congrFun hv i) z
  · -- Every atlas-wide family of constant spatial matrices is represented.
    intro c
    refine ⟨fun i => constSpatialData (c i), ?_⟩
    intro i x
    simp [initialValue, constSpatialData]
  · -- Every atlas-wide family of constant parabolic matrices is represented.
    intro c
    let g : Index → RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach E
        (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) α
        (RicciFlow.AnalyticPDE.parabolicFiniteCylinder E t₀ Sraw) :=
      fun i => RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.mk
        (RicciFlow.AnalyticPDE.ParabolicC0AlphaSpace.ofSubmodule
          ⟨fun _ => c i, RicciFlow.AnalyticPDE.ParabolicC0AlphaOn.const (c i)⟩)
    refine ⟨g, ?_⟩
    intro i z hz
    dsimp [sourceValue, g]
    exact RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative_mk_eq _ z
      (by simpa [RicciFlow.AnalyticPDE.parabolicFiniteCylinder] using hz)
  · -- The solution carrier itself contains every constant atlas jet family.
    intro c
    refine ⟨fun i => (constSpatialData (c i)).timeIndependentExtension hα, ?_⟩
    intro i z hz
    dsimp [solutionValue]
    exact RicciFlow.AnalyticPDE.BoundedSpatialC2AlphaData.value_timeIndependentExtension
      (constSpatialData (c i)) hα
      (by simpa [RicciFlow.AnalyticPDE.parabolicFiniteCylinder] using hz)
  · -- The initial-data size controls genuine bounded spatial C²ᵃ jets.
    intro D i
    letI : NormedAddCommGroup
        (E →L[ℝ] E →L[ℝ]
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ
        (E →L[ℝ] E →L[ℝ]
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ)) :=
      ContinuousLinearMap.toNormedSpace
    let Di := D i
    have hRi : Di.normRadius ≤ A.spatialInitialSize cov D := by
      exact Finset.single_le_sum
        (fun j _hj => (D j).normRadius_nonneg) (Finset.mem_univ i)
    have hvR : ‖Di.value‖ ≤ Di.normRadius := by
      exact (le_add_of_nonneg_right Di.holderConstant_nonneg).trans
        (le_max_left _ _)
    have hdR : ‖Di.spaceDeriv‖ ≤ Di.normRadius := by
      exact (le_add_of_nonneg_right Di.holderConstant_nonneg).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    have hddR : ‖Di.spaceSecondDeriv‖ ≤ Di.normRadius := by
      exact (le_add_of_nonneg_right Di.holderConstant_nonneg).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    have hHR : Di.holderConstant ≤ Di.normRadius := by
      exact (le_add_of_nonneg_left (norm_nonneg Di.value)).trans
        (le_max_left _ _)
    unfold HasSpatialC2AlphaNormLe
    refine ⟨A.spatialInitialSize_nonneg cov D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      exact (Di.value.norm_coe_le_norm x).trans (hvR.trans hRi)
    · intro x
      exact (Di.spaceDeriv.norm_coe_le_norm x).trans (hdR.trans hRi)
    · intro x
      exact (Di.spaceSecondDeriv.norm_coe_le_norm x).trans (hddR.trans hRi)
    · intro x y
      exact (Di.value_holder x y).trans
        (mul_le_mul_of_nonneg_right (hHR.trans hRi) (Real.rpow_nonneg dist_nonneg _))
    · intro x y
      exact (Di.spaceDeriv_holder x y).trans
        (mul_le_mul_of_nonneg_right (hHR.trans hRi) (Real.rpow_nonneg dist_nonneg _))
    · intro x y
      exact (Di.spaceSecondDeriv_holder x y).trans
        (mul_le_mul_of_nonneg_right (hHR.trans hRi) (Real.rpow_nonneg dist_nonneg _))
    · exact Di.hasFDerivAt_value
    · exact Di.hasFDerivAt_spaceDeriv
  · -- The source norm controls genuine parabolic C⁰ᵃ representatives.
    intro f i
    apply hasParabolicC0AlphaNormLe_of_banach le_rfl (f i)
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mp le_rfl i
  · intro D
    exact A.spatialInitialSize_nonneg cov D
  · intro f
    exact norm_nonneg f
  · intro D f hD hf
    have hD' :
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.AtlasSpatialInitialData.IsSymmetric
          cov D := by
      exact hD
    have hf' :
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.SourceSpace.IsSymmetric
          cov f := by
      exact hf
    obtain ⟨q, hq, huniq⟩ := (hwell D f hD' hf').1
    refine ⟨q, ⟨hq, ?_, hq.2.1, hq.2.2.1, ?_⟩, ?_⟩
    · exact (A.symmetrizedAtlasField cov q).hasTimeDerivative
    · intro t ht x a c
      have hP := hq.2.2.2 t ht x
      have hPeval := congrArg
        (fun k : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ => k a c) hP
      have hlap := connectionLaplacianApply_eq_canonical cov cov₂ cov₃
        hcov₂ hcov₃
        ((A.symmetrizedAtlasField cov q).slice cov t ⟨ht.1, ht.2.le⟩) x a c
      have hlap' : connectionLaplacianApply cov₂ cov₃
          ((A.symmetrizedAtlasField cov q).toFun t) x a c =
          _root_.CovariantDerivative.connectionLaplacian cov
            ((A.symmetrizedAtlasField cov q).toFun t) x a c := hlap
      change
        (A.symmetrizedAtlasField cov q).timeDerivative t x a c -
          connectionLaplacianApply cov₂ cov₃
            ((A.symmetrizedAtlasField cov q).toFun t) x a c =
          A.physicalAtlasSourceSlice cov f t x a c
      rw [hlap']
      exact hPeval
    · intro q' hq'
      exact huniq q' hq'.1
  · intro D f q hq
    refine ⟨?_, A.norm_le_strongAtlasSchauderConstant_mul_symmetricData
      cov hunique Hlift D f q hq⟩
    intro i
    let qi := q i
    have hqi : ‖qi‖ ≤ ‖q‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mp le_rfl i
    have hv : ‖qi.1.1‖ ≤ ‖qi‖ := by
      change ‖qi.1.1‖ ≤ ‖qi.1‖
      rw [Prod.norm_def]
      exact le_max_left _ _
    have hd : ‖qi.1.2.1‖ ≤ ‖qi‖ := by
      change ‖qi.1.2.1‖ ≤ ‖qi.1‖
      rw [Prod.norm_def, Prod.norm_def]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hdd : ‖qi.1.2.2.1‖ ≤ ‖qi‖ := by
      change ‖qi.1.2.2.1‖ ≤ ‖qi.1‖
      rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
      exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have ht : ‖qi.1.2.2.2‖ ≤ ‖qi‖ := by
      change ‖qi.1.2.2.2‖ ≤ ‖qi.1‖
      rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
      exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    unfold HasParabolicC2AlphaNormLe
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.value qi)
      change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative qi.1.1)
      exact hasParabolicC0AlphaNormLe_of_banach le_rfl qi.1.1 (hv.trans hqi)
    · change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.spaceDeriv qi)
      change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative qi.1.2.1)
      exact hasParabolicC0AlphaNormLe_of_banach le_rfl qi.1.2.1 (hd.trans hqi)
    · change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.spaceSecondDeriv qi)
      change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative qi.1.2.2.1)
      exact hasParabolicC0AlphaNormLe_of_banach le_rfl qi.1.2.2.1 (hdd.trans hqi)
    · change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.timeDeriv qi)
      change HasParabolicC0AlphaNormLe t₀ Sraw α ‖q‖
        (RicciFlow.AnalyticPDE.ParabolicC0AlphaBanach.representative qi.1.2.2.2)
      exact hasParabolicC0AlphaNormLe_of_banach le_rfl qi.1.2.2.2 (ht.trans hqi)
    · intro t ht' x
      exact RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.hasFDerivAt_space qi ht' x
    · intro t ht' x
      exact RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.hasFDerivAt_spaceDeriv qi ht' x
    · intro t ht' x
      exact RicciFlow.AnalyticPDE.FiniteParabolicC2AlphaBanach.hasDerivAt_time qi ht' x

end SymmetricTensorHeatEntry
