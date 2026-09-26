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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyParabolic
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyConnectionVariation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyKoszulVariation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.MetricInverseVariation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ThreeDimensionalRicciNorm
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLinear
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TraceLaplacian

/-!
# Intrinsic time variation for the Hamilton--Ivey support

The parabolic Hamilton--Ivey layer is phrased using an arbitrary smooth
Levi--Civita representative `cov`, because that is the connection family used
by the curvature spectrum.  The metric-variation layer, on the other hand,
packages the Ricci time derivative intrinsically as a bilinear tensor.  This
file is the transport bridge between the two APIs: it derives the scalar and
contact Ricci derivatives for the chosen representative from one genuine
intrinsic Ricci derivative.

No coordinate matrix or symmetrized readout is introduced here.  The only
auxiliary object is the canonical smooth Levi--Civita family used by the
intrinsic API, and all occurrences of it are eliminated by the proved
Levi--Civita invariance lemmas.
-/

@[expose] public section

noncomputable section

open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

/-- The contact speed written directly from a genuine intrinsic Ricci-tensor
time derivative.  The scalar velocity is the metric-variation trace
`2 |Ric|² + tr_g(Ric')`, while the second velocity is the same tensor
derivative evaluated on the contact field. -/
def hamiltonIveyIntrinsicSupportSpeed
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M)
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ) : ℝ :=
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x (ricciVelocity x)
  let v : TM x := g.curvatureNuContactVectorField
    cov hcov hLevi hdim t x x
  scalarVelocity / (-g.curvatureNu cov hcov hLevi hdim t x) +
    (g.scalarCurvature cov hcov t x -
        g.curvatureNu cov hcov hLevi hdim t x) /
      (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 *
      (scalarVelocity - 2 * ricciVelocity x v v -
      (g.curvatureLambda cov hcov hLevi hdim t x +
          g.curvatureMu cov hcov hLevi hdim t x) ^ 2) -
    K / (1 + K * t)

/-- The genuine connection-Laplacian readout of the shifted curvature tensor
at a Hamilton--Ivey contact.  The local instances are part of this
definition, so a downstream contact certificate can refer to an ordinary
real-valued quantity without manufacturing a coordinate coefficient array. -/
def hamiltonIveyContactCurvatureLaplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  letI : ∀ x : M, NormedAddCommGroup (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ x : M, NormedAddCommGroup (T₂ x) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
  exact connectionLaplacian (cov t₀)
    (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀) x₀
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)

@[simp] theorem hamiltonIveyContactCurvatureLaplacian_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t₀ x₀ =
      (letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
       letI : ∀ x : M, NormedAddCommGroup (TM x →L[ℝ] ℝ) := fun _ =>
         ContinuousLinearMap.toNormedAddCommGroup
       letI : ∀ x : M, NormedSpace ℝ (TM x →L[ℝ] ℝ) := fun _ =>
         ContinuousLinearMap.toNormedSpace
       letI : ∀ x : M, NormedAddCommGroup (T₂ x) := fun _ =>
         ContinuousLinearMap.toNormedAddCommGroup
       letI : ∀ x : M, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
       connectionLaplacian (cov t₀)
         (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀) x₀
         (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
         (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)) := by
  rfl

/-! The canonical smooth Levi--Civita family is kept local in the proofs
below.  These abbreviations make the transport equalities readable while
remaining definitionally tied to the repository's intrinsic API. -/

section IntrinsicTransport

variable [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
/-- Ricci-flow specialization of the metric-to-connection variation formula.
The metric velocity is obtained from the actual Ricci-flow equation and the
intrinsic Ricci tensor is identified with the chosen Levi-Civita representative.
The three mixed time/space derivative hypotheses remain explicit: they are
the regularity needed to differentiate the spatial metric derivatives. -/
theorem metricVelocityCovariantDerivative_connectionVariation_formula_intrinsicRicci
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    (A : ∀ x : M, TM x → TM x → TM x)
    (hvariation : TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
      (I := I) (M := M) cov A t)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hRicciYZ : MDiffAt
      (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (Y y) (Z y)) x)
    (hRicciXZ : MDiffAt
      (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (X y) (Z y)) x)
    (hRicciXY : MDiffAt
      (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (X y) (Y y)) x)
    (hmixedXYZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I)
        (fun y ↦ ((-2 : ℝ) • RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y) (Y y) (Z y)) x (X x)) t)
    (hmixedYXZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I)
        (fun y ↦ ((-2 : ℝ) • RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y) (X y) (Z y)) x (Y x)) t)
    (hmixedZXY : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I)
        (fun y ↦ ((-2 : ℝ) • RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y) (X y) (Y y)) x (Z x)) t) :
    2 * (g t).inner x (A x (X x) (Y x)) (Z x) =
      -2 * (metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov
          (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
          t X Y Z x +
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov
          (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
          t Y X Z x -
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov
          (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
          t Z X Y x) := by
  let ricci : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t
  let hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    fun y => (-2 : ℝ) • ricci y
  have hRicciTensor : RicciFlow.intrinsicRicciTensor (I := I) (M := M) g =
      RicciFlow.ricciTensor (I := I) (M := M) g cov hcov :=
    RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
      (I := I) (M := M) g hcov hLevi
  have hricciEq (y : M) (u v : TM y) :
      ricci y u v = g.ricciCurvature cov hcov t y u v := by
    have hpoint := congrArg (fun q => q t y u v) hRicciTensor
    simpa [ricci, RicciFlow.intrinsicRicciBilinearAt_apply,
      RicciFlow.ricciTensor] using hpoint
  have hmetric : ∀ (y : M) (u v : TM y),
      HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (hdot y u v) t := by
    intro y u v
    have hmetric₀ := hflow.2.1 ht y u v
    have hmetricEq := hflow.2.2 ht y u v
    change HasDerivAt (fun τ => (g τ).inner y u v) (gdot t y u v) t at hmetric₀
    rw [hmetricEq] at hmetric₀
    have hmetricRicci : HasDerivAt (fun τ => (g τ).inner y u v)
        ((-2 : ℝ) * g.ricciCurvature cov hcov t y u v) t := by
      simpa [RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor] using hmetric₀
    simpa [hdot, ricci, hricciEq y u v, smul_eq_mul] using hmetricRicci
  have hformula := metricVelocityCovariantDerivative_connectionVariation_formula_smul
    (I := I) (M := M) g cov hcov hLevi A ricci (-2) (t := t)
    hvariation hmetric hX hY hZ hRicciYZ hRicciXZ hRicciXY
    hmixedXYZ hmixedYXZ hmixedZXY
  simpa [ricci] using hformula

theorem hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) {x : M}
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x)
      (2 * g.ricciNormSq cov hcov t x +
        RicciFlow.metricTraceAt (I := I) (M := M) g t x (ricciVelocity x)) t := by
  let cov₀ : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) :=
    TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov₀ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov₀ t) 1 := by
    intro τ
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g τ
  let hLevi₀ : g.IsLeviCivita cov₀ := by
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) g
  have hIntrinsic : RicciFlow.IsIntrinsicRicciFlowOn
      (I := I) (M := M) g gdot s :=
    (RicciFlow.isIntrinsicRicciFlowOn_iff_of_isLeviCivita
      (I := I) (M := M) g hcov gdot s hLevi).2 hflow
  have hcanonical :=
    hIntrinsic.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
      ht (x := x) ricciVelocity hRicci
  have hscalarEq :
      (fun τ : ℝ => g.scalarCurvature cov hcov τ x) =
        (fun τ : ℝ => g.scalarCurvature cov₀ hcov₀ τ x) := by
    funext τ
    exact g.scalarCurvature_eq_of_isLeviCivita
      hcov hcov₀ hLevi hLevi₀ τ x
  have hnormEq :
      g.ricciNormSq cov₀ hcov₀ t x = g.ricciNormSq cov hcov t x := by
    exact g.ricciNormSq_eq_of_isLeviCivita
      hcov₀ hcov hLevi₀ hLevi t x
  rw [hscalarEq]
  rw [← hnormEq]
  exact hcanonical

theorem hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    {t : ℝ} (x : M) (u v : TM x)
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    HasDerivAt
      (fun τ => g.ricciCurvature cov hcov τ x u v)
      (ricciVelocity x u v) t := by
  let cov₀ : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) :=
    TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov₀ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov₀ t) 1 := by
    intro τ
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g τ
  let hLevi₀ : g.IsLeviCivita cov₀ := by
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) g
  have hricciEq :
      (fun τ : ℝ => g.ricciCurvature cov hcov τ x u v) =
        (fun τ : ℝ => RicciFlow.intrinsicRicciTensor
          (I := I) (M := M) g τ x u v) := by
    funext τ
    have hchosen := g.ricciCurvature_eq_of_isLeviCivita
      hcov hcov₀ hLevi hLevi₀ τ x u v
    simpa [RicciFlow.intrinsicRicciTensor, RicciFlow.ricciTensor,
      cov₀, hcov₀] using hchosen
  rw [hricciEq]
  exact hRicci x u v

/-! The intrinsic Ricci tensor is symmetric on every time slice.  Therefore
its genuine time derivative is symmetric as well; this is the direct
time-variation statement used by the lowered curvature-operator layer. -/

theorem intrinsicRicciTimeDerivative_symm_of_isLeviCivita
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    {t : ℝ}
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    ∀ (y : M) (u v : TM y),
      ricciVelocity y u v = ricciVelocity y v u := by
  intro y u v
  have hleft := hRicci y u v
  have hright := hRicci y v u
  have hfun :
      (fun τ : ℝ => RicciFlow.intrinsicRicciTensor
        (I := I) (M := M) g τ y u v) =
        (fun τ : ℝ => RicciFlow.intrinsicRicciTensor
          (I := I) (M := M) g τ y v u) := by
    funext τ
    exact RicciFlow.intrinsicRicciTensor_symm
      (I := I) (M := M) g τ y u v
  rw [hfun] at hleft
  exact hleft.unique hright

/-! A curvature-tensor derivative induces the Ricci-tensor derivative by the
same genuine trace contraction used in the definition of Ricci curvature.  We
keep this bridge separate from the Ricci-flow evolution formula: it isolates
the temporal curvature-variation obligation without replacing it by a
coordinate coefficient hypothesis. -/

def curvatureTensorVelocityEndomorphism
    (curvatureVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y)
    (y : M) (u w : TM y) : TM y →ₗ[ℝ] TM y :=
  { toFun := fun v => curvatureVelocity y v u w
    map_add' := by
      intro v v'
      simp
    map_smul' := by
      intro c v
      simp }

def curvatureTensorVelocityRicci
    (curvatureVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y)
    (y : M) : TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
  { toFun := fun u =>
      { toFun := fun w =>
          LinearMap.trace ℝ (TM y)
            (curvatureTensorVelocityEndomorphism curvatureVelocity y u w)
        map_add' := by
          intro w w'
          have hE :
              curvatureTensorVelocityEndomorphism curvatureVelocity y u (w + w') =
                curvatureTensorVelocityEndomorphism curvatureVelocity y u w +
                  curvatureTensorVelocityEndomorphism curvatureVelocity y u w' := by
            ext v
            simp [curvatureTensorVelocityEndomorphism]
          rw [hE, (LinearMap.trace ℝ (TM y)).map_add]
        map_smul' := by
          intro c w
          have hE :
              curvatureTensorVelocityEndomorphism curvatureVelocity y u (c • w) =
                c • curvatureTensorVelocityEndomorphism curvatureVelocity y u w := by
            ext v
            simp [curvatureTensorVelocityEndomorphism]
          rw [hE, (LinearMap.trace ℝ (TM y)).map_smul]
          rfl }
    map_add' := by
      intro u u'
      ext w
      have hE :
          curvatureTensorVelocityEndomorphism curvatureVelocity y (u + u') w =
            curvatureTensorVelocityEndomorphism curvatureVelocity y u w +
              curvatureTensorVelocityEndomorphism curvatureVelocity y u' w := by
        ext v
        simp [curvatureTensorVelocityEndomorphism]
      change LinearMap.trace ℝ (TM y)
          (curvatureTensorVelocityEndomorphism curvatureVelocity y (u + u') w) =
        LinearMap.trace ℝ (TM y)
            (curvatureTensorVelocityEndomorphism curvatureVelocity y u w) +
          LinearMap.trace ℝ (TM y)
            (curvatureTensorVelocityEndomorphism curvatureVelocity y u' w)
      rw [hE, (LinearMap.trace ℝ (TM y)).map_add]
    map_smul' := by
      intro c u
      ext w
      have hE :
          curvatureTensorVelocityEndomorphism curvatureVelocity y (c • u) w =
            c • curvatureTensorVelocityEndomorphism curvatureVelocity y u w := by
        ext v
        simp [curvatureTensorVelocityEndomorphism]
      change LinearMap.trace ℝ (TM y)
          (curvatureTensorVelocityEndomorphism curvatureVelocity y (c • u) w) =
        c * LinearMap.trace ℝ (TM y)
          (curvatureTensorVelocityEndomorphism curvatureVelocity y u w)
      rw [hE, (LinearMap.trace ℝ (TM y)).map_smul]
      rfl }

/-! A curvature-type four-tensor variation has a symmetric Ricci trace for the
same algebraic reason as an ordinary Riemann tensor.  The skew, Bianchi, and
pair-symmetry premises are stated on the actual vector-valued variation; no
symmetrization of the traced bilinear form is performed. -/

theorem curvatureTensorVelocityRicci_symm_of_curvatureIdentities
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (t : ℝ)
    (curvatureVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y)
    (hself : ∀ (y : M) (a c : TM y), curvatureVelocity y a a c = 0)
    (hswap : ∀ (y : M) (a b c : TM y),
      curvatureVelocity y a b c = -curvatureVelocity y b a c)
    (hBianchi : ∀ (y : M) (a b c : TM y),
      curvatureVelocity y a b c + curvatureVelocity y b c a +
          curvatureVelocity y c a b = 0)
    (hpair : ∀ (y : M) (a b c d : TM y),
      (g t).inner y (curvatureVelocity y a b c) d =
        (g t).inner y (curvatureVelocity y c d a) b)
    (y : M) (u w : TM y) :
    curvatureTensorVelocityRicci curvatureVelocity y u w =
      curvatureTensorVelocityRicci curvatureVelocity y w u := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TM y))) ℝ (TM y) :=
    stdOrthonormalBasis ℝ (TM y)
  change LinearMap.trace ℝ (TM y)
      (curvatureTensorVelocityEndomorphism curvatureVelocity y u w) =
    LinearMap.trace ℝ (TM y)
      (curvatureTensorVelocityEndomorphism curvatureVelocity y w u)
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl ?_
  intro i _
  let e : TM y := b i
  have hInner := congrArg (fun z : TM y => Inner.inner ℝ z e)
    (hBianchi y e u w)
  have hInner' :
      Inner.inner ℝ (curvatureVelocity y e u w) e +
          Inner.inner ℝ (curvatureVelocity y u w e) e +
        Inner.inner ℝ (curvatureVelocity y w e u) e = 0 := by
    simpa only [inner_add_left, inner_zero_left] using hInner
  have hmiddle :
      Inner.inner ℝ (curvatureVelocity y u w e) e = 0 := by
    change (g t).inner y (curvatureVelocity y u w e) e = 0
    rw [hpair y u w e e, hself y e u]
    simp
  have hthird :
      Inner.inner ℝ (curvatureVelocity y w e u) e =
        -Inner.inner ℝ (curvatureVelocity y e w u) e := by
    change (g t).inner y (curvatureVelocity y w e u) e =
      -(g t).inner y (curvatureVelocity y e w u) e
    rw [hswap y w e u]
    simp
  have hterm :
      Inner.inner ℝ (curvatureVelocity y e u w) e =
        Inner.inner ℝ (curvatureVelocity y e w u) e := by
    rw [hmiddle, hthird] at hInner'
    linarith
  change Inner.inner ℝ (b i) (curvatureVelocity y (b i) u w) =
    Inner.inner ℝ (b i) (curvatureVelocity y (b i) w u)
  simpa [e, real_inner_comm] using hterm

theorem hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    {t : ℝ}
    (curvatureVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y)
    (hCurvature : ∀ (y : M) (u v w : TM y),
      HasDerivAt
        (fun τ => TimeDependentCovariantDerivative.curvatureTensor
          (I := I) (M := M) cov hcov τ y u v w)
        (curvatureVelocity y u v w) t) :
    RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g (curvatureTensorVelocityRicci curvatureVelocity) t := by
  intro y u w
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TM y))) ℝ (TM y) :=
    stdOrthonormalBasis ℝ (TM y)
  have htrace : ∀ τ : ℝ,
      g.ricciCurvature cov hcov τ y u w =
        ∑ i,
          (g t).inner y (b i)
            (TimeDependentCovariantDerivative.curvatureTensor
              (I := I) (M := M) cov hcov τ y (b i) u w) := by
    intro τ
    letI : ContMDiffCovariantDerivative (cov τ) 1 := hcov τ
    change CovariantDerivative.ricciCurvature (cov := cov τ) y u w = _
    have hinner (v w : TM y) :
        (g t).inner y v w = Inner.inner ℝ v w := by
      rfl
    simpa only [TimeDependentCovariantDerivative.curvatureTensor_apply, hinner] using
      (CovariantDerivative.ricciCurvature_eq_sum_curvature_orthonormalBasis
        (I := I) (M := M) (cov := cov τ) y b u w)
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i (_hi : i ∈ Finset.univ) => by
    have hi := (hasDerivAt_const (x := t)
      ((g t).inner y (b i)) :
      HasDerivAt (fun _ : ℝ => (g t).inner y (b i)) 0 t).clm_apply
      (hCurvature y (b i) u w)
    simpa only [zero_smul, zero_add] using hi)
  have hsumFun :
      (∑ i, fun τ : ℝ =>
        (g t).inner y (b i)
          (TimeDependentCovariantDerivative.curvatureTensor
            (I := I) (M := M) cov hcov τ y (b i) u w)) =
      (fun τ : ℝ => ∑ i,
        (g t).inner y (b i)
          (TimeDependentCovariantDerivative.curvatureTensor
            (I := I) (M := M) cov hcov τ y (b i) u w)) := by
    funext τ
    simp
  rw [hsumFun] at hsum
  have hderiv : HasDerivAt
      (fun τ : ℝ => g.ricciCurvature cov hcov τ y u w)
      (((curvatureTensorVelocityRicci curvatureVelocity y) u) w) t := by
    rw [show (fun τ : ℝ => g.ricciCurvature cov hcov τ y u w) =
      (fun τ : ℝ => ∑ i,
        (g t).inner y (b i)
          (TimeDependentCovariantDerivative.curvatureTensor
            (I := I) (M := M) cov hcov τ y (b i) u w)) by
        funext τ; exact htrace τ]
    have htraceVel :
        (∑ i, (g t).inner y (b i) (curvatureVelocity y (b i) u w)) =
      LinearMap.trace ℝ (TM y)
          (curvatureTensorVelocityEndomorphism curvatureVelocity y u w) := by
      rw [LinearMap.trace_eq_sum_inner _ b]
      rfl
    exact hsum.congr_deriv (by
      simpa [curvatureTensorVelocityRicci] using htraceVel)
  have hricciEq :
      (fun τ : ℝ => RicciFlow.intrinsicRicciTensor
        (I := I) (M := M) g τ y u w) =
        (fun τ : ℝ => g.ricciCurvature cov hcov τ y u w) := by
    funext τ
    have hEq := congrArg (fun F => F τ y u w)
      (RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
        (I := I) (M := M) g hcov hLevi)
    simpa [RicciFlow.ricciTensor,
      TimeDependentRiemannianMetric.ricciCurvature] using hEq
  rw [hricciEq]
  exact hderiv

/-! The preceding trace bridge can be fed directly into the metric-variation
formula.  This version is convenient for a future curvature-variation proof:
its only temporal input is the actual curvature-tensor derivative, while the
remaining scalar trace term is displayed by the intrinsic metric contraction. -/

theorem hasDerivAt_scalarCurvature_of_curvatureTensorTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) {x : M}
    (curvatureVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y)
    (hCurvature : ∀ (y : M) (u v w : TM y),
      HasDerivAt
        (fun τ => TimeDependentCovariantDerivative.curvatureTensor
          (I := I) (M := M) cov hcov τ y u v w)
        (curvatureVelocity y u v w) t) :
    HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x)
      (2 * g.ricciNormSq cov hcov t x +
        RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (curvatureTensorVelocityRicci curvatureVelocity x)) t := by
  exact g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := x)
      (curvatureTensorVelocityRicci curvatureVelocity)
      (hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
        g cov hcov hLevi curvatureVelocity hCurvature)

/-! The previous two transport lemmas combine with the metric variation to
give the time derivative of the actual lowered curvature operator.  This is
the tensorial quantity that enters the curvature evolution equation; no
coordinate matrix or symmetrized projection is used. -/

def curvatureOperatorTwoTensorVelocity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (y : M) (u v : TM y) : ℝ :=
  (2 * g.ricciNormSq cov hcov t y +
      RicciFlow.metricTraceAt (I := I) (M := M) g t y (ricciVelocity y)) *
      (g t).inner y u v -
    2 * g.scalarCurvature cov hcov t y *
      g.ricciCurvature cov hcov t y u v -
    2 * ricciVelocity y u v

/-! The lowered curvature velocity inherits symmetry from the genuine Ricci
velocity.  This is an algebraic preservation statement for the actual tensor;
it does not define a symmetrized readout or discard any antisymmetric data. -/

theorem curvatureOperatorTwoTensorVelocity_symm
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (y : M)
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hsymm : ∀ (z : M) (u v : TM z), ricciVelocity z u v = ricciVelocity z v u)
    (u v : TM y) :
    curvatureOperatorTwoTensorVelocity g cov hcov t ricciVelocity y u v =
      curvatureOperatorTwoTensorVelocity g cov hcov t ricciVelocity y v u := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hinner : (g t).inner y u v = (g t).inner y v u := by
    change Inner.inner ℝ u v = Inner.inner ℝ v u
    exact (real_inner_comm u v).symm
  have hricci := g.ricciCurvature_symm_of_isLeviCivita
    cov hcov hLevi t y u v
  unfold curvatureOperatorTwoTensorVelocity
  rw [hinner, hricci, hsymm]

/-! Variant of the preceding symmetry lemma with the intrinsic derivative as
the sole Ricci-velocity hypothesis.  The symmetry is inherited from the
actual time-slice Ricci tensor, rather than supplied by a projected
coefficient presentation. -/

theorem curvatureOperatorTwoTensorVelocity_symm_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    {t : ℝ} (y : M)
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (u v : TM y) :
    curvatureOperatorTwoTensorVelocity g cov hcov t ricciVelocity y u v =
      curvatureOperatorTwoTensorVelocity g cov hcov t ricciVelocity y v u := by
  exact g.curvatureOperatorTwoTensorVelocity_symm cov hcov hLevi t y
    ricciVelocity
    (g.intrinsicRicciTimeDerivative_symm_of_isLeviCivita ricciVelocity hRicci)
    u v

theorem hasDerivAt_curvatureOperatorTwoTensor_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (y : M) (u v : TM y)
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    HasDerivAt
      (fun τ => g.curvatureOperatorTwoTensor cov hcov τ y u v)
      (curvatureOperatorTwoTensorVelocity g cov hcov t ricciVelocity y u v) t := by
  have hscalar := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := y) ricciVelocity hRicci
  have hmetric := hflow.2.1 ht y u v
  have hmetricEq := hflow.2.2 ht y u v
  change HasDerivAt (fun τ => (g τ).inner y u v) (gdot t y u v) t at hmetric
  rw [hmetricEq] at hmetric
  have hmetric' : HasDerivAt (fun τ => (g τ).inner y u v)
      (-2 * g.ricciCurvature cov hcov t y u v) t := by
    simpa [RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor] using hmetric
  have hricci := g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi y u v ricciVelocity hRicci
  have htotal := (hscalar.mul hmetric').sub (hricci.const_mul 2)
  change HasDerivAt
    (fun τ => g.scalarCurvature cov hcov τ y * (g τ).inner y u v -
      2 * g.ricciCurvature cov hcov τ y u v)
    _ t at htotal
  convert htotal using 1
  · rfl
  · simp [curvatureOperatorTwoTensorVelocity]
    ring

/-! The same curvature-tensor derivative also supplies the time derivative of
the lowered curvature operator.  This is the precise transport statement used
when a later curvature-evolution calculation is expressed in terms of the
actual four-tensor rather than an independently postulated Ricci velocity. -/

theorem hasDerivAt_curvatureOperatorTwoTensor_of_curvatureTensorTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (y : M) (u v : TM y)
    (curvatureVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hCurvature : ∀ (z : M) (a b c : TM z),
      HasDerivAt
        (fun τ => TimeDependentCovariantDerivative.curvatureTensor
          (I := I) (M := M) cov hcov τ z a b c)
        (curvatureVelocity z a b c) t) :
    HasDerivAt
      (fun τ => g.curvatureOperatorTwoTensor cov hcov τ y u v)
      (curvatureOperatorTwoTensorVelocity g cov hcov t
        (curvatureTensorVelocityRicci curvatureVelocity) y u v) t := by
  exact g.hasDerivAt_curvatureOperatorTwoTensor_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht y u v
      (curvatureTensorVelocityRicci curvatureVelocity)
      (hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
        g cov hcov hLevi curvatureVelocity hCurvature)

/-! The three-dimensional curvature reaction is recorded intrinsically as a
polynomial in the curvature endomorphism.  If `A` is that endomorphism and
`R` is scalar curvature, the algebraic part is

`Q(A) = 2 A^2 - R A + (lambda*mu + lambda*nu + mu*nu) I`.

The final term is the metric-variation contribution to a lowered curvature
component.  Thus this is an actual tensorial bilinear expression, rather
than an independently supplied scalar coefficient. -/

def curvatureOperatorReaction
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (u v : TM y) : ℝ :=
  let A := fun z : TM y =>
    g.curvatureEndomorphismApply cov hcov t y z
  let R := g.scalarCurvature cov hcov t y
  let e₂ :=
    g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureMu cov hcov hLevi hdim t y +
      g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y +
      g.curvatureMu cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y
  (g t).inner y u
      ((2 : ℝ) • A (A v) - R • A v + e₂ • v) -
    2 * g.ricciCurvature cov hcov t y u (A v)

/-! The polynomial part of the curvature reaction is bundled as the actual
continuous endomorphism

`Q(A) = 2 A ∘ A - R A + (λ μ + λ ν + μ ν) Id`.

Keeping this object as a fibrewise linear map makes the tensorial reaction
available to downstream maximum-principle code without introducing a matrix
or a chosen eigenbasis. -/

def curvatureOperatorReactionEndomorphism
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) : TM y →L[ℝ] TM y := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let A : TM y →L[ℝ] TM y :=
    CovariantDerivative.ricciComplementEndomorphism (cov t) y
  let e₂ : ℝ :=
    g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureMu cov hcov hLevi hdim t y +
      g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y +
      g.curvatureMu cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y
  exact (2 : ℝ) • (A.comp A) -
      g.scalarCurvature cov hcov t y • A +
      e₂ • ContinuousLinearMap.id ℝ (TM y)

@[simp] theorem curvatureOperatorReactionEndomorphism_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (v : TM y) :
    curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v =
      (2 : ℝ) • g.curvatureEndomorphismApply cov hcov t y
          (g.curvatureEndomorphismApply cov hcov t y v) -
        g.scalarCurvature cov hcov t y •
          g.curvatureEndomorphismApply cov hcov t y v +
        (g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureMu cov hcov hLevi hdim t y +
          g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y +
          g.curvatureMu cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y) • v := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  simp [curvatureOperatorReactionEndomorphism, curvatureEndomorphismApply]

theorem curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (u v : TM y) :
    curvatureOperatorReaction g cov hcov hLevi hdim t y u v =
      (g t).inner y u
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) -
        2 * g.ricciCurvature cov hcov t y u
          (g.curvatureEndomorphismApply cov hcov t y v) := by
  simp [curvatureOperatorReaction, curvatureOperatorReactionEndomorphism,
    curvatureEndomorphismApply]

theorem curvatureOperatorReactionEndomorphism_isSymmetric
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) :
    ∀ u v : TM y,
      (g t).inner y
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y u) v =
        (g t).inner y u
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let A : TM y →L[ℝ] TM y :=
    CovariantDerivative.ricciComplementEndomorphism (cov t) y
  have hA : A.toLinearMap.IsSymmetric := by
    simpa [A] using
      (CovariantDerivative.ricciComplementEndomorphism_isSymmetric
        (cov t) (hLevi t).1 (hLevi t).2 y)
  have hAcomp : ∀ u v : TM y,
      Inner.inner ℝ ((A.comp A) u) v = Inner.inner ℝ u ((A.comp A) v) := by
    intro u v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact (hA (A u) v).trans (hA u (A v))
  have hAuv : ∀ u v : TM y,
      Inner.inner ℝ (A u) v = Inner.inner ℝ u (A v) := by
    intro u v
    exact hA u v
  let e₂ : ℝ :=
    g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureMu cov hcov hLevi hdim t y +
      g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y +
      g.curvatureMu cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y
  intro u v
  change Inner.inner ℝ
      ((2 : ℝ) • (A.comp A) u -
        g.scalarCurvature cov hcov t y • A u + e₂ • u) v =
    Inner.inner ℝ u
      ((2 : ℝ) • (A.comp A) v -
        g.scalarCurvature cov hcov t y • A v + e₂ • v)
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hAcomp u v, hAuv u v]

/-! The lowered reaction is itself a symmetric bilinear form.  The polynomial
part is self-adjoint, while the remaining Ricci contraction is symmetric
because the curvature endomorphism is the Ricci-complement
`R Id - 2 Ric♯`. -/

theorem curvatureOperatorReaction_symm
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (u v : TM y) :
    curvatureOperatorReaction g cov hcov hLevi hdim t y u v =
      curvatureOperatorReaction g cov hcov hLevi hdim t y v u := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hRicci :=
    CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
      (cov := cov t) (hLevi t) y u v
  have hcomp :
      g.ricciCurvature cov hcov t y u
          (g.curvatureEndomorphismApply cov hcov t y v) =
        g.ricciCurvature cov hcov t y v
          (g.curvatureEndomorphismApply cov hcov t y u) := by
    change CovariantDerivative.ricciCurvature (cov := cov t) y u
        (CovariantDerivative.ricciComplementEndomorphism (cov t) y v) =
      CovariantDerivative.ricciCurvature (cov := cov t) y v
        (CovariantDerivative.ricciComplementEndomorphism (cov t) y u)
    rw [CovariantDerivative.ricciComplementEndomorphism_apply,
      CovariantDerivative.ricciComplementEndomorphism_apply]
    simp only [map_sub, map_smul]
    rw [hRicci]
    have hinner :
        Inner.inner ℝ
            (CovariantDerivative.raisedRicciEndomorphism (cov t) y u)
            (CovariantDerivative.raisedRicciEndomorphism (cov t) y v) =
          Inner.inner ℝ
            (CovariantDerivative.raisedRicciEndomorphism (cov t) y v)
            (CovariantDerivative.raisedRicciEndomorphism (cov t) y u) := by
      exact real_inner_comm _ _
    rw [← CovariantDerivative.inner_raisedRicciEndomorphism (cov t) y u
          (CovariantDerivative.raisedRicciEndomorphism (cov t) y v),
      ← CovariantDerivative.inner_raisedRicciEndomorphism (cov t) y v
          (CovariantDerivative.raisedRicciEndomorphism (cov t) y u)]
    rw [hinner]
  rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci,
    curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci]
  have hQ' :
      (g t).inner y u
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) =
        (g t).inner y v
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y u) := by
    calc
      (g t).inner y u
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) =
          (g t).inner y
            (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) u :=
        by
          change Inner.inner ℝ u
              (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) =
            Inner.inner ℝ
              (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) u
          exact (real_inner_comm _ _).symm
      _ = (g t).inner y v
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y u) := by
        exact curvatureOperatorReactionEndomorphism_isSymmetric
          g cov hcov hLevi hdim t y v u
  rw [hQ', hcomp]

/-! On the selected least-curvature eigendirection the polynomial reaction
operator has the diagonal ODE eigenreaction `ν² + λ μ`.  This is the
endomorphism-level form of the reaction calculation used by the support
maximum principle. -/

theorem curvatureOperatorReactionEndomorphism_apply_curvatureNuEigenvector
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) :
    curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y
        (g.curvatureNuEigenvector cov hcov hLevi hdim t y) =
      (g.curvatureNu cov hcov hLevi hdim t y) ^ 2 •
          g.curvatureNuEigenvector cov hcov hLevi hdim t y +
        (g.curvatureLambda cov hcov hLevi hdim t y *
          g.curvatureMu cov hcov hLevi hdim t y) •
          g.curvatureNuEigenvector cov hcov hLevi hdim t y := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let V : TM y := g.curvatureNuEigenvector cov hcov hLevi hdim t y
  have hA : g.curvatureEndomorphismApply cov hcov t y V =
      (g.curvatureNu cov hcov hLevi hdim t y) • V :=
    g.curvatureEndomorphismApply_curvatureNuEigenvector
      cov hcov hLevi hdim t y
  have hA' : CovariantDerivative.ricciComplementEndomorphism (cov t) y V =
      (g.curvatureNu cov hcov hLevi hdim t y) • V := by
    simpa [curvatureEndomorphismApply] using hA
  have hAA : g.curvatureEndomorphismApply cov hcov t y
      (g.curvatureEndomorphismApply cov hcov t y V) =
      (g.curvatureNu cov hcov hLevi hdim t y) ^ 2 • V := by
    rw [hA]
    unfold curvatureEndomorphismApply
    rw [map_smul, hA']
    rw [smul_smul]
    congr 1
    ring
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t y
  rw [curvatureOperatorReactionEndomorphism_apply
    g cov hcov hLevi hdim t y V, hAA, hA]
  rw [← hsum]
  simp only [V, smul_smul]
  rw [sub_eq_add_neg, ← neg_smul]
  rw [← add_smul]
  rw [← add_smul]
  congr 1
  ring_nf
  rw [add_smul]

/-! The same polynomial reaction is diagonal on every member of the genuine
curvature eigenbasis.  The least-direction calculation above is therefore a
special case of a fibrewise statement about the full self-adjoint operator. -/

theorem curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (i : Fin 3) :
    curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y i) =
      ((2 : ℝ) *
          (g.curvatureEigenvalues cov hcov hLevi hdim t y i) ^ 2 -
        g.scalarCurvature cov hcov t y *
          g.curvatureEigenvalues cov hcov hLevi hdim t y i +
        (g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureMu cov hcov hLevi hdim t y +
          g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y +
          g.curvatureMu cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y)) •
        g.curvatureEigenbasisVector cov hcov hLevi hdim t y i := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  change curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y
      (CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i) = _
  change curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y
      (CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i) =
    _ • (CovariantDerivative.ricciComplementEigenbasis
      (I := I) (M := M) (E := E)
      (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i)
  have hAraw := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i
  have hA : g.curvatureEndomorphismApply cov hcov t y
      (CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i) =
      g.curvatureEigenvalues cov hcov hLevi hdim t y i •
        (CovariantDerivative.ricciComplementEigenbasis
          (I := I) (M := M) (E := E)
          (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i) := by
    simpa [curvatureEndomorphismApply, curvatureEigenvalues] using hAraw
  rw [curvatureOperatorReactionEndomorphism_apply]
  rw [hA]
  unfold curvatureEndomorphismApply
  rw [map_smul, hAraw]
  simp only [smul_smul]
  simp only [curvatureEigenvalues]
  rw [sub_eq_add_neg, ← neg_smul]
  rw [← add_smul]
  rw [← add_smul]
  congr 1
  ring_nf

/-! The Ricci quadratic form on each genuine curvature eigenvector is the
corresponding complement of the curvature eigenvalue.  This is the
coordinate-free identity `2 Ric(eᵢ,eᵢ) = R - κᵢ` used to reduce the lowered
reaction to its scalar polynomial. -/

theorem two_mul_ricci_curvatureEigenbasis_eq_scalar_sub_eigenvalue
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (i : Fin 3) :
    2 * g.ricciCurvature cov hcov t y
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y i)
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y i) =
      g.scalarCurvature cov hcov t y -
        g.curvatureEigenvalues cov hcov hLevi hdim t y i := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 y (hdim y)
  let k := CovariantDerivative.ricciComplementEigenvalues
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i
  have hA := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i
  have hinner : Inner.inner ℝ (b i) (b i) = 1 := by
    simpa [b] using
      (CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 y (hdim y)).orthonormal
        (i := i) (j := i)
  have hnorm : ‖b i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hinner
  have hAinner := congrArg (fun z : TM y => Inner.inner ℝ z (b i)) hA
  have hAinner' :
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) y (b i))
          (b i) = k := by
    calc
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) y (b i))
          (b i) = Inner.inner ℝ (k • b i) (b i) := by
            simpa [k] using hAinner
      _ = k := by
        rw [real_inner_smul_left, hinner, mul_one]
  have hquad := CovariantDerivative.inner_ricciComplementEndomorphism
    (cov t) y (b i)
  have hquad' :
      Inner.inner ℝ
          (CovariantDerivative.ricciComplementEndomorphism (cov t) y (b i))
          (b i) =
        CovariantDerivative.scalarCurvature (cov := cov t) y -
          2 * CovariantDerivative.ricciCurvature (cov := cov t) y (b i) (b i) := by
    simpa [hnorm] using hquad
  have hresult :
      2 * CovariantDerivative.ricciCurvature (cov := cov t) y (b i) (b i) =
        CovariantDerivative.scalarCurvature (cov := cov t) y - k := by
    linarith [hAinner', hquad']
  change 2 * CovariantDerivative.ricciCurvature (cov := cov t) y (b i) (b i) =
    CovariantDerivative.scalarCurvature (cov := cov t) y - k
  exact hresult

/-! The lowered curvature reaction is diagonal on the genuine curvature
eigenbasis.  The formula below retains the actual scalar and Ricci terms so
that its relation to the tensor evolution equation remains explicit. -/

theorem curvatureOperatorReaction_apply_curvatureEigenbasis
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (i : Fin 3) :
    curvatureOperatorReaction g cov hcov hLevi hdim t y
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y i)
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y i) =
      3 * (g.curvatureEigenvalues cov hcov hLevi hdim t y i) ^ 2 -
        2 * g.scalarCurvature cov hcov t y *
          g.curvatureEigenvalues cov hcov hLevi hdim t y i +
        (g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureMu cov hcov hLevi hdim t y +
          g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y +
          g.curvatureMu cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let b : TM y := g.curvatureEigenbasisVector cov hcov hLevi hdim t y i
  let k : ℝ := g.curvatureEigenvalues cov hcov hLevi hdim t y i
  let R : ℝ := g.scalarCurvature cov hcov t y
  have hinner : (g t).inner y b b = 1 := by
    change Inner.inner ℝ b b = 1
    dsimp [b, curvatureEigenbasisVector]
    simpa using
      (CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 y (hdim y)).orthonormal
        (i := i) (j := i)
  have hinner' : Inner.inner ℝ b b = 1 := by
    change (g t).inner y b b = 1
    exact hinner
  have hA : g.curvatureEndomorphismApply cov hcov t y b = k • b := by
    change g.curvatureEndomorphismApply cov hcov t y
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y i) = _
    change CovariantDerivative.ricciComplementEndomorphism (cov t) y
        (CovariantDerivative.ricciComplementEigenbasis
          (I := I) (M := M) (E := E)
          (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i) = _
    simpa [b, k, curvatureEigenvalues, curvatureEigenbasisVector,
      curvatureEndomorphismApply] using
      (CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
        (I := I) (M := M) (E := E)
        (cov t) (hLevi t).1 (hLevi t).2 y (hdim y) i)
  have hQ := curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    g cov hcov hLevi hdim t y i
  have hQ' :
      curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y b =
        (2 * k ^ 2 - R * k +
          (g.curvatureLambda cov hcov hLevi hdim t y *
              g.curvatureMu cov hcov hLevi hdim t y +
            g.curvatureLambda cov hcov hLevi hdim t y *
              g.curvatureNu cov hcov hLevi hdim t y +
            g.curvatureMu cov hcov hLevi hdim t y *
              g.curvatureNu cov hcov hLevi hdim t y)) • b := by
    simpa [b, k, R] using hQ
  have hRic := g.two_mul_ricci_curvatureEigenbasis_eq_scalar_sub_eigenvalue
    cov hcov hLevi hdim t y i
  have hRicScale :
      g.ricciCurvature cov hcov t y b (k • b) =
        k * g.ricciCurvature cov hcov t y b b := by
    change CovariantDerivative.ricciCurvature (cov := cov t) y b (k • b) = _
    rw [map_smul]
    rfl
  change curvatureOperatorReaction g cov hcov hLevi hdim t y b b = _
  rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
    g cov hcov hLevi hdim t y b b, hQ', hA, hRicScale]
  change Inner.inner ℝ b _ - _ = _
  simp only [real_inner_smul_right, hinner', mul_one]
  have hhalf : g.ricciCurvature cov hcov t y b b =
      (g.scalarCurvature cov hcov t y - k) / 2 := by
    linarith [hRic]
  rw [hhalf]
  dsimp [k, R]
  ring

/-! The polynomial reaction endomorphism has the diagonal ODE reactions from
Hamilton--Ivey's three-dimensional curvature system.  These are the three
ordered eigendirections of the genuine Ricci-complement operator, so the
identification is independent of any coordinate coefficient presentation. -/

theorem curvatureOperatorReactionEndomorphism_apply_curvatureLambdaEigenbasis
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) :
    curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y 0) =
      (g.curvatureLambda cov hcov hLevi hdim t y) ^ 2 •
          g.curvatureEigenbasisVector cov hcov hLevi hdim t y 0 +
        (g.curvatureMu cov hcov hLevi hdim t y *
          g.curvatureNu cov hcov hLevi hdim t y) •
          g.curvatureEigenbasisVector cov hcov hLevi hdim t y 0 := by
  have hQ := curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    g cov hcov hLevi hdim t y (0 : Fin 3)
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t y
  rw [curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    g cov hcov hLevi hdim t y (0 : Fin 3)]
  rw [← hsum]
  simp only [curvatureLambda, curvatureMu, curvatureNu, curvatureEigenvalues,
    curvatureEigenbasisVector]
  rw [← add_smul]
  congr 1
  ring

theorem curvatureOperatorReactionEndomorphism_apply_curvatureMuEigenbasis
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) :
    curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y 1) =
      (g.curvatureMu cov hcov hLevi hdim t y) ^ 2 •
          g.curvatureEigenbasisVector cov hcov hLevi hdim t y 1 +
        (g.curvatureLambda cov hcov hLevi hdim t y *
          g.curvatureNu cov hcov hLevi hdim t y) •
          g.curvatureEigenbasisVector cov hcov hLevi hdim t y 1 := by
  have hQ := curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    g cov hcov hLevi hdim t y (1 : Fin 3)
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t y
  rw [curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    g cov hcov hLevi hdim t y (1 : Fin 3)]
  rw [← hsum]
  simp only [curvatureLambda, curvatureMu, curvatureNu, curvatureEigenvalues,
    curvatureEigenbasisVector]
  rw [← add_smul]
  congr 1
  ring

theorem curvatureOperatorReactionEndomorphism_apply_curvatureNuEigenbasis
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) :
    curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y
        (g.curvatureEigenbasisVector cov hcov hLevi hdim t y 2) =
      (g.curvatureNu cov hcov hLevi hdim t y) ^ 2 •
          g.curvatureEigenbasisVector cov hcov hLevi hdim t y 2 +
        (g.curvatureLambda cov hcov hLevi hdim t y *
          g.curvatureMu cov hcov hLevi hdim t y) •
          g.curvatureEigenbasisVector cov hcov hLevi hdim t y 2 := by
  have hQ := curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    g cov hcov hLevi hdim t y (2 : Fin 3)
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t y
  rw [curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
    g cov hcov hLevi hdim t y (2 : Fin 3)]
  rw [← hsum]
  simp only [curvatureLambda, curvatureMu, curvatureNu, curvatureEigenvalues,
    curvatureEigenbasisVector]
  rw [← add_smul]
  congr 1
  ring

/-! Taking the fibrewise trace of this genuine reaction endomorphism recovers
the scalar component of the three-dimensional curvature-reaction ODE. -/

theorem curvatureOperatorReactionEndomorphism_trace_eq_scalarReaction
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) :
    LinearMap.trace ℝ (TM y)
        (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y).toLinearMap =
      HamiltonIveyReaction.scalarReaction
        (g.curvatureLambda cov hcov hLevi hdim t y)
        (g.curvatureMu cov hcov hLevi hdim t y)
        (g.curvatureNu cov hcov hLevi hdim t y) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 y (hdim y)
  have htrace := LinearMap.trace_eq_sum_inner
    (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y).toLinearMap b
  rw [htrace, Fin.sum_univ_three]
  have h0 := g.curvatureOperatorReactionEndomorphism_apply_curvatureLambdaEigenbasis
    cov hcov hLevi hdim t y
  have h1 := g.curvatureOperatorReactionEndomorphism_apply_curvatureMuEigenbasis
    cov hcov hLevi hdim t y
  have h2 := g.curvatureOperatorReactionEndomorphism_apply_curvatureNuEigenbasis
    cov hcov hLevi hdim t y
  change Inner.inner ℝ (b 0)
        (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y (b 0)) +
      Inner.inner ℝ (b 1)
        (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y (b 1)) +
      Inner.inner ℝ (b 2)
        (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y (b 2)) = _
  have h0' :
      curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y (b 0) =
        (g.curvatureLambda cov hcov hLevi hdim t y) ^ 2 • b 0 +
          (g.curvatureMu cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y) • b 0 := by
    simpa [b, curvatureEigenbasisVector] using h0
  have h1' :
      curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y (b 1) =
        (g.curvatureMu cov hcov hLevi hdim t y) ^ 2 • b 1 +
          (g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y) • b 1 := by
    simpa [b, curvatureEigenbasisVector] using h1
  have h2' :
      curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y (b 2) =
        (g.curvatureNu cov hcov hLevi hdim t y) ^ 2 • b 2 +
          (g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureMu cov hcov hLevi hdim t y) • b 2 := by
    simpa [b, curvatureEigenbasisVector] using h2
  rw [h0', h1', h2']
  simp only [inner_add_right, real_inner_smul_right]
  have hb0 : Inner.inner ℝ (b 0) (b 0) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1]
    norm_num
  have hb1 : Inner.inner ℝ (b 1) (b 1) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1]
    norm_num
  have hb2 : Inner.inner ℝ (b 2) (b 2) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1]
    norm_num
  rw [hb0, hb1, hb2]
  simp only [mul_one]
  dsimp [HamiltonIveyReaction.scalarReaction]

/-! The trace of the actual lowered curvature reaction is the scalar reaction
that appears in the Ricci-flow scalar equation, with the metric-variation
correction kept visible. This is the algebraic part of recovering the scalar
trace evolution from a full tensor evolution identity. -/
theorem curvatureOperatorReaction_trace_eq_sixRicciNormSq_sub_twoScalarSq
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    let b := CovariantDerivative.ricciComplementEigenbasis
      (I := I) (M := M) (E := E) (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
    (∑ i : Fin 3,
      curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b i)) =
      6 * g.ricciNormSq cov hcov t x -
        2 * (g.scalarCurvature cov hcov t x) ^ 2 := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
  let eig : Fin 3 → ℝ := fun i =>
    g.curvatureEigenvalues cov hcov hLevi hdim t x i
  let lam : ℝ := g.curvatureLambda cov hcov hLevi hdim t x
  let mu : ℝ := g.curvatureMu cov hcov hLevi hdim t x
  let nu : ℝ := g.curvatureNu cov hcov hLevi hdim t x
  let R : ℝ := g.scalarCurvature cov hcov t x
  let e₂ : ℝ :=
    lam * mu + lam * nu + mu * nu
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x
  have hnorm (i : Fin 3) : Inner.inner ℝ (b i) (b i) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1]
    norm_num
  have hnormSq (i : Fin 3) : ‖b i‖ ^ 2 = 1 := by
    rw [b.orthonormal.1]
    norm_num
  have hA (i : Fin 3) :
      g.curvatureEndomorphismApply cov hcov t x (b i) = eig i • b i := by
    have h := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
      (I := I) (M := M) (E := E) (cov t)
      (hLevi t).1 (hLevi t).2 x (hdim x) i
    simpa [curvatureEndomorphismApply, eig, b, curvatureEigenvalues] using h
  have hQ (i : Fin 3) :
      curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t x (b i) =
        (2 * eig i ^ 2 - R * eig i + e₂) • b i := by
    have h := g.curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
      cov hcov hLevi hdim t x i
    simpa [b, eig, R, e₂, lam, mu, nu, curvatureEigenbasisVector] using h
  have hinnerQ (i : Fin 3) :
      (g t).inner x (b i)
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t x (b i)) =
        2 * eig i ^ 2 - R * eig i + e₂ := by
    rw [hQ i]
    change Inner.inner ℝ (b i)
        ((2 * eig i ^ 2 - R * eig i + e₂) • b i) = _
    simp [real_inner_smul_right, hnorm i]
  have hRicciDiag (i : Fin 3) :
      g.ricciCurvature cov hcov t x (b i) (b i) = (R - eig i) / 2 := by
    have hinner :
        Inner.inner ℝ
          (g.curvatureEndomorphismApply cov hcov t x (b i)) (b i) = eig i := by
      rw [hA i, real_inner_smul_left, hnorm i]
      ring
    have hquadratic :=
      CovariantDerivative.inner_ricciComplementEndomorphism (cov t) x (b i)
    have hidentity : eig i = R -
        2 * g.ricciCurvature cov hcov t x (b i) (b i) := by
      calc
        eig i = Inner.inner ℝ
            (g.curvatureEndomorphismApply cov hcov t x (b i)) (b i) := hinner.symm
        _ = R * ‖b i‖ ^ 2 -
            2 * g.ricciCurvature cov hcov t x (b i) (b i) := by
          simpa [curvatureEndomorphismApply, R, hnormSq i] using hquadratic
        _ = R - 2 * g.ricciCurvature cov hcov t x (b i) (b i) := by
          rw [hnormSq i]
          ring
    nlinarith [hidentity]
  have hRicciA (i : Fin 3) :
      g.ricciCurvature cov hcov t x (b i)
          (g.curvatureEndomorphismApply cov hcov t x (b i)) =
        eig i * g.ricciCurvature cov hcov t x (b i) (b i) := by
    rw [hA i]
    simp
  have hterm (i : Fin 3) :
      curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b i) =
        (2 * eig i ^ 2 - R * eig i + e₂) -
          2 * ((R - eig i) / 2) * eig i := by
    rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci,
      hinnerQ i, hRicciA i, hRicciDiag i]
    ring
  have hterm0 := hterm 0
  have hterm1 := hterm 1
  have hterm2 := hterm 2
  have heig0 : eig 0 = lam := by
    rfl
  have heig1 : eig 1 = mu := by
    rfl
  have heig2 : eig 2 = nu := by
    rfl
  have hsumLambda : lam + mu + nu = R := by
    simpa [lam, mu, nu, R] using hsum
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hnormReaction' :=
    CovariantDerivative.two_mul_ricciNormSq_eq_threeDimensionalCurvatureReaction
      (I := I) (M := M) (E := E) (cov t)
      (hLevi t).1 (hLevi t).2 x (hdim x)
  have hnormReaction :
      2 * g.ricciNormSq cov hcov t x =
        HamiltonIveyReaction.scalarReaction
          (g.curvatureLambda cov hcov hLevi hdim t x)
          (g.curvatureMu cov hcov hLevi hdim t x)
          (g.curvatureNu cov hcov hLevi hdim t x) := by
    dsimp [HamiltonIveyReaction.scalarReaction]
    convert hnormReaction' using 1
    · rfl
    · simp [CovariantDerivative.TimeDependentRiemannianMetric.ricciNormSq,
        curvatureLambda, curvatureMu, curvatureNu, curvatureEigenvalues,
        CovariantDerivative.threeDimensionalCurvatureLambda,
        CovariantDerivative.threeDimensionalCurvatureMu,
        CovariantDerivative.threeDimensionalCurvatureNu]
      ring
  dsimp only
  rw [Fin.sum_univ_three, hterm0, hterm1, hterm2,
    heig0, heig1, heig2, ← hsumLambda]
  rw [← hsum]
  dsimp [R, e₂, HamiltonIveyReaction.scalarReaction] at hnormReaction ⊢
  nlinarith [hnormReaction]

theorem curvatureOperatorReaction_apply_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    curvatureOperatorReaction g cov hcov hLevi hdim t x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hV : V = g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
    simp [V, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hA : g.curvatureEndomorphismApply cov hcov t x V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    rw [hV]
    exact g.curvatureEndomorphismApply_curvatureNuEigenvector
      cov hcov hLevi hdim t x
  have hA' : (CovariantDerivative.ricciComplementEndomorphism (cov t) x) V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    simpa [curvatureEndomorphismApply] using hA
  have hA_smul :
      g.curvatureEndomorphismApply cov hcov t x
          ((g.curvatureNu cov hcov hLevi hdim t x) • V) =
        (g.curvatureNu cov hcov hLevi hdim t x) •
          ((g.curvatureNu cov hcov hLevi hdim t x) • V) := by
    unfold curvatureEndomorphismApply
    rw [map_smul, hA']
  have hRic_smul :
      g.ricciCurvature cov hcov t x V
          ((g.curvatureNu cov hcov hLevi hdim t x) • V) =
        (g.curvatureNu cov hcov hLevi hdim t x) *
          g.ricciCurvature cov hcov t x V V := by
    change CovariantDerivative.ricciCurvature (cov := cov t) x V
        ((g.curvatureNu cov hcov hLevi hdim t x) • V) = _
    rw [map_smul]
    rfl
  have hinner : (g t).inner x V V = 1 := by
    rw [hV]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hinner' : Inner.inner ℝ V V = 1 := by
    change (g t).inner x V V = 1
    exact hinner
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x
  change curvatureOperatorReaction g cov hcov hLevi hdim t x V V = _
  change _ = (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x V V
  simp only [curvatureOperatorReaction] at ⊢
  rw [hA, hA_smul]
  rw [hRic_smul]
  change Inner.inner ℝ V _ - _ = _
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right,
    hinner']
  rw [← hsum]
  ring_nf

/-! The reaction at the least curvature direction is the product of the two
spectral gaps.  The Ricci contraction used here is recovered from the
eigenvector equation for the genuine Ricci-complement endomorphism; it is not
an independently supplied coefficient identity. -/

theorem curvatureOperatorReaction_apply_contact_eq_gap_product
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    curvatureOperatorReaction g cov hcov hLevi hdim t x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      (g.curvatureLambda cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) *
        (g.curvatureMu cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hV : V = g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
    simp [V, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hA : g.curvatureEndomorphismApply cov hcov t x V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    rw [hV]
    exact g.curvatureEndomorphismApply_curvatureNuEigenvector
      cov hcov hLevi hdim t x
  have hA' : (CovariantDerivative.ricciComplementEndomorphism (cov t) x) V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    simpa [curvatureEndomorphismApply] using hA
  have hinner : (g t).inner x V V = 1 := by
    rw [hV]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hinner' : Inner.inner ℝ V V = 1 := by
    change (g t).inner x V V = 1
    exact hinner
  have hnorm : ‖V‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hinner'
  have hquad := CovariantDerivative.inner_ricciComplementEndomorphism
    (cov t) x V
  have hRic : 2 * g.ricciCurvature cov hcov t x V V =
      g.curvatureLambda cov hcov hLevi hdim t x +
        g.curvatureMu cov hcov hLevi hdim t x := by
    have hAinner := congrArg (fun z : TM x => Inner.inner ℝ z V) hA'
    have hAinner' :
        Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x V) V =
          g.curvatureNu cov hcov hLevi hdim t x := by
      calc
        Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x V) V =
            Inner.inner ℝ
              ((g.curvatureNu cov hcov hLevi hdim t x) • V) V := hAinner
        _ = g.curvatureNu cov hcov hLevi hdim t x * ‖V‖ ^ 2 := by
          rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        _ = g.curvatureNu cov hcov hLevi hdim t x := by rw [hnorm, mul_one]
    have hquad' :
        Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x V) V =
          g.scalarCurvature cov hcov t x -
            2 * g.ricciCurvature cov hcov t x V V := by
      simpa [CovariantDerivative.TimeDependentRiemannianMetric.scalarCurvature,
        CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature,
        curvatureEndomorphismApply, hnorm] using hquad
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    rw [hAinner'] at hquad'
    rw [← hsum] at hquad'
    linarith
  have hreaction :
      curvatureOperatorReaction g cov hcov hLevi hdim t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using g.curvatureOperatorReaction_apply_contact
      cov hcov hLevi hdim t x
  change curvatureOperatorReaction g cov hcov hLevi hdim t x V V = _
  rw [hreaction]
  calc
    (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x *
            (2 * g.ricciCurvature cov hcov t x V V) := by ring
    _ = (g.curvatureLambda cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) *
        (g.curvatureMu cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) := by
      rw [hRic]
      ring

theorem curvatureOperatorReaction_apply_contact_nonneg
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    0 ≤ curvatureOperatorReaction g cov hcov hLevi hdim t x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  rw [curvatureOperatorReaction_apply_contact_eq_gap_product
    g cov hcov hLevi hdim t x]
  have hMuNu := g.curvatureMu_ge_nu cov hcov hLevi hdim t x
  have hLambdaMu := g.curvatureLambda_ge_mu cov hcov hLevi hdim t x
  have hLambdaNu : g.curvatureNu cov hcov hLevi hdim t x ≤
      g.curvatureLambda cov hcov hLevi hdim t x := le_trans hMuNu hLambdaMu
  exact mul_nonneg (sub_nonneg.mpr hLambdaNu) (sub_nonneg.mpr hMuNu)

/-! The scalar Hamilton--Ivey reaction is the genuine curvature-operator
contact reaction with the expected profile weight, together with the two
normalization terms.  This identity is the algebraic tensor-to-scalar bridge
used by the eventual parabolic contact calculation. -/

theorem hamiltonIveyReactionTerm_eq_weighted_curvatureOperatorReaction_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) :
    g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x =
      -2 * g.curvatureNu cov hcov hLevi hdim t x -
          K / (1 + K * t) +
        (g.scalarCurvature cov hcov t x /
            (g.curvatureNu cov hcov hLevi hdim t x) ^ 2) *
          curvatureOperatorReaction g cov hcov hLevi hdim t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  rw [hamiltonIveyReactionTerm, HamiltonIveyReaction.reaction,
    HamiltonIveyReaction.scalar,
    curvatureOperatorReaction_apply_contact_eq_gap_product
      g cov hcov hLevi hdim t x]
  rw [← g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x]
  ring_nf

/-! In dimension three the Ricci norm in the intrinsic metric-variation
formula is exactly Hamilton--Ivey's scalar curvature reaction polynomial.
This is an algebraic identity for the genuine raised Ricci endomorphism, not
an assumption about a coordinate coefficient presentation. -/

theorem two_mul_ricciNormSq_eq_hamiltonIveyScalarReaction
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    2 * g.ricciNormSq cov hcov t x =
      HamiltonIveyReaction.scalarReaction
        (g.curvatureLambda cov hcov hLevi hdim t x)
        (g.curvatureMu cov hcov hLevi hdim t x)
        (g.curvatureNu cov hcov hLevi hdim t x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have h := CovariantDerivative.two_mul_ricciNormSq_eq_threeDimensionalCurvatureReaction
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
  dsimp [HamiltonIveyReaction.scalarReaction]
  convert h using 1
  · rfl
  · simp [CovariantDerivative.TimeDependentRiemannianMetric.ricciNormSq,
      curvatureLambda, curvatureMu, curvatureNu, curvatureEigenvalues,
      CovariantDerivative.threeDimensionalCurvatureLambda,
      CovariantDerivative.threeDimensionalCurvatureMu,
      CovariantDerivative.threeDimensionalCurvatureNu]
    ring

/-! With the intrinsic metric-variation trace identified with the scalar
Laplacian, the scalar-curvature derivative has exactly the Hamilton--Ivey
reaction form.  The trace equality is kept as an explicit hypothesis until
the full contracted-Bianchi/curvature-evolution bridge is proved. -/

theorem hasDerivAt_scalarCurvature_eq_hamiltonIveyReaction_add_laplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) {x : M}
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (htrace : RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (ricciVelocity x) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x) :
    HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x)
      (HamiltonIveyReaction.scalarReaction
          (g.curvatureLambda cov hcov hLevi hdim t x)
          (g.curvatureMu cov hcov hLevi hdim t x)
          (g.curvatureNu cov hcov hLevi hdim t x) +
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x) t := by
  have h := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := x) ricciVelocity hRicci
  convert h using 1
  rw [two_mul_ricciNormSq_eq_hamiltonIveyScalarReaction
    g cov hcov hLevi hdim t x, htrace]

/-! If the actual lowered curvature component satisfies the reaction-form
evolution identity, uniqueness of derivatives identifies its velocity with
the contact reaction.  This is the reusable interface for the curvature
evolution theorem, while leaving that theorem itself as an explicit
geometric obligation. -/

theorem curvatureOperatorTwoTensorVelocity_eq_of_curvatureOperatorReactionEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (hEvolution :
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x))
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)) t) :
    g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hoperator := g.hasDerivAt_curvatureOperatorTwoTensor_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht x V V ricciVelocity hRicci
  have hEvolution' :
      HasDerivAt (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x V V)
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x V V) t := by
    simpa [V] using hEvolution
  have hvel := hoperator.unique hEvolution'
  have hreaction := curvatureOperatorReaction_apply_contact g cov hcov hLevi hdim t x
  have hreactionV :
      curvatureOperatorReaction g cov hcov hLevi hdim t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using hreaction
  have hvel' :
      g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x V V =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    rw [hvel, hreactionV]
    ring
  simpa [V] using hvel'

/-! At a contact eigenvector, the genuine lowered-curvature velocity gives the
time derivative of the Rayleigh support after the quotient correction.  The
assumption below is the exact contact evaluation of the curvature evolution
identity; isolating it here records the remaining geometric bridge without
silently replacing it by a coordinate or symmetrized coefficient statement. -/

theorem hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (hcurv :
      g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t x (τ, x))
      (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x) t := by
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (ricciVelocity x)
  let contactRicciVelocity : ℝ := ricciVelocity x V V
  have hscalar := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := x) ricciVelocity hRicci
  have hricci := g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi x V V ricciVelocity hRicci
  have hq := g.hasDerivAt_curvatureNuSpacetimeSupport_time_eigenvalue_form
    cov hcov hLevi hdim gdot s hflow ht x scalarVelocity contactRicciVelocity
    hscalar hricci
  have hRic := g.two_mul_ricci_curvatureNuEigenvector_eq_lambda_add_mu
    cov hcov hLevi hdim t x
  have hV : V = g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
    simp [V, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hinner : (g t).inner x V V = 1 := by
    rw [hV]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x
  have hrel :
      scalarVelocity - 2 * contactRicciVelocity -
          (g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x) ^ 2 =
        g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x V V +
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    have hRic' : 2 * g.ricciCurvature cov hcov t x V V =
        g.curvatureLambda cov hcov hLevi hdim t x +
          g.curvatureMu cov hcov hLevi hdim t x := by
      simpa [V, curvatureNuContactVectorField,
        firstOrderParallelSmoothExtend_apply_center] using hRic
    have hRminus :
        g.scalarCurvature cov hcov t x -
            g.curvatureNu cov hcov hLevi hdim t x =
          g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x := by
      linarith [hsum]
    have hprod :
        2 * (g.scalarCurvature cov hcov t x -
            g.curvatureNu cov hcov hLevi hdim t x) *
            g.ricciCurvature cov hcov t x V V =
          (g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x) ^ 2 := by
      calc
        2 * (g.scalarCurvature cov hcov t x -
            g.curvatureNu cov hcov hLevi hdim t x) *
              g.ricciCurvature cov hcov t x V V =
            (g.scalarCurvature cov hcov t x -
              g.curvatureNu cov hcov hLevi hdim t x) *
              (2 * g.ricciCurvature cov hcov t x V V) := by ring
        _ = (g.curvatureLambda cov hcov hLevi hdim t x +
              g.curvatureMu cov hcov hLevi hdim t x) ^ 2 := by
          rw [hRic', hRminus]
          ring
    simp only [scalarVelocity, contactRicciVelocity,
      curvatureOperatorTwoTensorVelocity]
    rw [hinner]
    ring_nf
    linarith [hprod]
  have hcurvV :
      g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x V V =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using hcurv
  apply hq.congr_deriv
  rw [hrel, hcurvV]
  ring

/-! The preceding contact-support derivative can now consume the reaction-form
curvature evolution directly.  The only input not proved in this file is the
actual time derivative of the curvature component; its right-hand side is
required to be the intrinsic connection Laplacian plus the displayed
curvature polynomial. -/

theorem hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorReactionEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (hEvolution :
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x))
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)) t) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t x (τ, x))
      (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x) t := by
  have hcurv :=
    g.curvatureOperatorTwoTensorVelocity_eq_of_curvatureOperatorReactionEvolution
      cov hcov hLevi hdim gdot s hflow ht x ricciVelocity hRicci hEvolution
  exact g.hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorEvolution
    cov hcov hLevi hdim gdot s hflow ht x ricciVelocity hRicci hcurv

/-! The same support-speed calculation can be driven by the actual curvature
four-tensor derivative.  The contact evolution hypothesis is still stated for
the lowered curvature component, but its derivative is now independently
identified with the velocity obtained by tracing the genuine four-tensor
variation. -/

theorem hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureTensorReactionEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (curvatureVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hCurvature : ∀ (z : M) (a b c : TM z),
      HasDerivAt
        (fun τ => TimeDependentCovariantDerivative.curvatureTensor
          (I := I) (M := M) cov hcov τ z a b c)
        (curvatureVelocity z a b c) t)
    (hEvolution :
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x))
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)) t) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t x (τ, x))
      (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x) t := by
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hRicci :=
    hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi curvatureVelocity hCurvature
  have hoperator :=
    g.hasDerivAt_curvatureOperatorTwoTensor_of_curvatureTensorTimeDerivative
      cov hcov hLevi hdim gdot s hflow ht x V V curvatureVelocity hCurvature
  have hEvolution' :
      HasDerivAt (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x V V)
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x V V) t := by
    simpa [V] using hEvolution
  have hvel := hoperator.unique hEvolution'
  have hreaction := curvatureOperatorReaction_apply_contact g cov hcov hLevi hdim t x
  have hreactionV :
      curvatureOperatorReaction g cov hcov hLevi hdim t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using hreaction
  have hcurv :
      g.curvatureOperatorTwoTensorVelocity cov hcov t
          (curvatureTensorVelocityRicci curvatureVelocity) x V V =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    rw [hvel, hreactionV]
    ring
  exact g.hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorEvolution
    cov hcov hLevi hdim gdot s hflow ht x
      (curvatureTensorVelocityRicci curvatureVelocity) hRicci (by
        simpa [V] using hcurv)

/-! A genuine curvature-evolution theorem is naturally stated for every
tangent pair, not only for the selected contact vector.  This specialization
keeps that stronger interface intact: once the lowered curvature component has
the connection-Laplacian plus reaction derivative for all `u,v`, the support
derivative follows by evaluating it at the contact field. -/

theorem hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureTensorConnectionLaplacianEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (curvatureVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hCurvature : ∀ (z : M) (a b c : TM z),
      HasDerivAt
        (fun τ => TimeDependentCovariantDerivative.curvatureTensor
          (I := I) (M := M) cov hcov τ z a b c)
        (curvatureVelocity z a b c) t)
    (hEvolution :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedSpace
      letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
        inferInstance
      ∀ u v : TM x,
        HasDerivAt
          (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x u v)
          (connectionLaplacian (cov t)
              (g.curvatureNuShiftedContactTwoTensor
                cov hcov hLevi hdim t x) x u v +
            curvatureOperatorReaction g cov hcov hLevi hdim t x u v) t) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t x (τ, x))
      (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x) t := by
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hRicci :=
    hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi curvatureVelocity hCurvature
  have hEvolutionContact :
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x V V)
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x V V) t := by
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedSpace
    letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
      inferInstance
    simpa [V, hamiltonIveyContactCurvatureLaplacian] using
      (hEvolution V V)
  have hoperator :=
    g.hasDerivAt_curvatureOperatorTwoTensor_of_curvatureTensorTimeDerivative
      cov hcov hLevi hdim gdot s hflow ht x V V curvatureVelocity hCurvature
  have hvel := hoperator.unique hEvolutionContact
  have hreaction := curvatureOperatorReaction_apply_contact g cov hcov hLevi hdim t x
  have hreactionV :
      curvatureOperatorReaction g cov hcov hLevi hdim t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using hreaction
  have hcurv :
      g.curvatureOperatorTwoTensorVelocity cov hcov t
          (curvatureTensorVelocityRicci curvatureVelocity) x V V =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    rw [hvel, hreactionV]
    ring
  exact g.hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorEvolution
    cov hcov hLevi hdim gdot s hflow ht x
      (curvatureTensorVelocityRicci curvatureVelocity) hRicci (by
        simpa [V] using hcurv)

/-! The preceding theorem has the exact geometric input needed by the
support calculation, but its long dependent hypothesis is inconvenient to
thread through a global evolution argument.  Bundle that input without
changing its meaning: the certificate contains the derivative of the actual
time-dependent curvature four-tensor and the connection-Laplacian plus
reaction equation for the actual lowered curvature operator.  No scalar or
coordinate surrogate is introduced. -/

structure HamiltonIveyCurvatureEvolutionCertificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) where
  curvatureVelocity : ∀ z : M,
    TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z
  hCurvature : ∀ (z : M) (a b c : TM z),
    HasDerivAt
      (fun τ => TimeDependentCovariantDerivative.curvatureTensor
        (I := I) (M := M) cov hcov τ z a b c)
      (curvatureVelocity z a b c) t
  hEvolution :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedSpace
    letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
      inferInstance
    ∀ u v : TM x,
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x u v)
        (connectionLaplacian (cov t)
            (g.curvatureNuShiftedContactTwoTensor
              cov hcov hLevi hdim t x) x u v +
          curvatureOperatorReaction g cov hcov hLevi hdim t x u v) t

/-! The connection-variation API computes the derivative of the actual
curvature tensor from its commutator definition.  This constructor records
that computation in the certificate while keeping the connection-Laplacian
evolution equation as an explicit geometric input.  In particular, it does
not turn the curvature PDE into a scalar assumption or a coordinate proxy. -/

/-- Construct the curvature-transport part of a Hamilton--Ivey evolution
certificate from a genuine connection variation.

The supplied `hEvolution` is intentionally still the lowered-curvature
connection-Laplacian-plus-reaction equation.  The theorem only removes the
redundant independent proof of the derivative of the actual curvature tensor:
that proof is obtained from `HasConnectionTimeVariationAt` and the actual
curvature commutator. -/
def HamiltonIveyCurvatureEvolutionCertificate.of_connectionVariation
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {t : ℝ} (x : M)
    (A : ∀ z : M, TM z → TM z → TM z)
    (curvatureVelocity : ∀ z : M,
      TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hvelocity : ∀ (z : M) (a b c : TM z),
      curvatureVelocity z a b c =
        TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
          (I := I) (M := M) cov A t z a b c)
    (hvariation :
      TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
        (I := I) (M := M) cov A t)
    (hA : ∀ (X Y : Π y : M, TM y),
      (∀ y, MDiffAt (T% X) y) → (∀ y, MDiffAt (T% Y) y) →
        ∀ y, MDiffAt (T% (fun z => A z (X z) (Y z))) y)
    (hEvolution :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedSpace
      letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
        inferInstance
      ∀ u v : TM x,
        HasDerivAt
          (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x u v)
          (connectionLaplacian (cov t)
              (g.curvatureNuShiftedContactTwoTensor
                cov hcov hLevi hdim t x) x u v +
            curvatureOperatorReaction g cov hcov hLevi hdim t x u v) t) :
    HamiltonIveyCurvatureEvolutionCertificate g cov hcov hLevi hdim t x := by
  refine
    { curvatureVelocity := curvatureVelocity
      hCurvature := ?_
      hEvolution := hEvolution }
  intro z a b c
  have hcurvature :=
    TimeDependentCovariantDerivative.hasDerivAt_curvatureTensor_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov hcov A (t := t) z hvariation hA a b c
  exact hcurvature.congr_deriv (hvelocity z a b c).symm

/-! The operator regularity needed by the next constructor is packaged with
the dependent bundle instances hidden inside the proposition.  This keeps
the public hypothesis readable while preserving the exact total-space
statements used by the genuine second-order operator. -/

/-- Spatial regularity of the actual lowered curvature operator and of its
induced covariant derivative at the selected point.  This is an honest
regularity package; it contains no curvature evolution equation. -/
def HamiltonIveyCurvatureOperatorRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedAddCommGroup (T₃ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedSpace ℝ (T₃ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    (∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        (g.curvatureOperatorTwoTensor cov hcov t z)) y) ∧
    MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t)
          (fun z => g.curvatureOperatorTwoTensor cov hcov t z) y)) x

/-! A globally C2 curvature-operator hypothesis is a convenient source for
the pointwise package above.  The proposition keeps the dependent bundle
instances local, so callers do not have to expose the total-space plumbing
needed by the induced covariant derivative. -/

/-- Global C2 regularity of the actual lowered curvature operator at a
fixed time.  This is only a regularity hypothesis; it does not include a
curvature evolution equation. -/
def HamiltonIveyCurvatureOperatorC2
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    ContMDiffVectorBundle.continuousLinearMap
  exact ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
    (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y
      (g.curvatureOperatorTwoTensor cov hcov t y))

/-- C1 regularity of the induced covariant derivative on the lowered
curvature-operator bundle at a fixed time.  This is an independent
regularity input; it is not inferred from the C2 curvature-operator
hypothesis. -/
def HamiltonIveyCurvatureOperatorDerivativeRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) (cov t)) 1
/-- Derive the pointwise operator package from genuine global C2 spatial
regularity of the lowered curvature operator. -/
theorem HamiltonIveyCurvatureOperatorRegularity.of_contMDiff_two
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {t : ℝ}
    (hcov₂ : g.HamiltonIveyCurvatureOperatorDerivativeRegularity cov hcov t)
    (x : M)
    (hC2 : g.HamiltonIveyCurvatureOperatorC2 cov hcov hLevi hdim t) :
    g.HamiltonIveyCurvatureOperatorRegularity cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedAddCommGroup (T₃ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedSpace ℝ (T₃ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hC2' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y
        (g.curvatureOperatorTwoTensor cov hcov t y)) := by
    simpa [HamiltonIveyCurvatureOperatorC2] using hC2
  have hoperator : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        (g.curvatureOperatorTwoTensor cov hcov t z)) y := by
    intro y
    have hy := hC2' y
    have hy' := hy.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact hy'.mdifferentiableAt one_ne_zero
  have hC2On : ContMDiffOn I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y
        (g.curvatureOperatorTwoTensor cov hcov t y)) Set.univ := by
    simpa only [contMDiffOn_univ] using hC2'
  have hcov₂' : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) (cov t)) 1 := by
    simpa [HamiltonIveyCurvatureOperatorDerivativeRegularity] using hcov₂
  have hoperatorOn :=
    hcov₂'.contMDiff.contMDiff hC2On
  have hoperatorFirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t)
          (fun z => g.curvatureOperatorTwoTensor cov hcov t z) y)) x := by
    exact (((hoperatorOn x (Set.mem_univ x)).contMDiffAt
      (isOpen_univ.mem_nhds (Set.mem_univ x))).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 1)).mdifferentiableAt
      one_ne_zero
  change (∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        (g.curvatureOperatorTwoTensor cov hcov t z)) y) ∧
    MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t)
          (fun z => g.curvatureOperatorTwoTensor cov hcov t z) y)) x
  exact ⟨hoperator, hoperatorFirst⟩
/-! The contact shift is by a spatially constant multiple of the metric.  The
Levi--Civita connection annihilates that metric, so on the genuine
second-order domain its connection Laplacian is unchanged.  This is the
operator-level simplification needed when a later curvature-evolution proof
is stated with the unshifted curvature operator. -/

/-- The connection Laplacian of the actual contact-shifted curvature tensor
agrees with that of the actual lowered curvature operator, provided the latter
has the spatial regularity required by the genuine second-order operator.

The regularity hypotheses are deliberately stated as differentiability of the
actual curvature-operator section and its induced covariant derivative.  They
do not contain, or imply by fiat, any curvature evolution identity. -/
theorem connectionLaplacian_curvatureNuShiftedContactTwoTensor_eq_curvatureOperatorTwoTensor
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M)
    (hregular : g.HamiltonIveyCurvatureOperatorRegularity
      cov hcov hLevi hdim t x) :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle I 1 E TM :=
        g.slice_isContMDiffRiemannianBundle t
      letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedSpace
      letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
      connectionLaplacian (cov t)
          (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x) x =
        connectionLaplacian (cov t)
          (fun y => g.curvatureOperatorTwoTensor cov hcov t y) x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedAddCommGroup (T₃ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedSpace ℝ (T₃ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
  letI : ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  rcases hregular with ⟨hoperator, hoperatorFirst⟩
  let O : ∀ y : M, T₂ y :=
    fun y => g.curvatureOperatorTwoTensor cov hcov t y
  let G : ∀ y : M, T₂ y :=
    riemannianMetricCovariantTwoTensor (I := I) (M := M)
  let Hshift : ∀ y : M, T₂ y :=
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x
  have hO : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z (O z)) y := by
    intro y
    simpa [O] using hoperator y
  have hOfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t) O y)) x := by
    simpa [O] using hoperatorFirst
  have hG : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z (G z)) y := by
    intro y
    exact riemannianMetricCovariantTwoTensor_mdifferentiableAt
      (I := I) (E := E) (M := M) y
  have hGderiv : covariantTwoTensorCovariantDerivative (cov t) G = 0 := by
    funext y
    ext X u v
    exact covariantTwoTensorCovariantDerivative_riemannianMetric_eq_zero
      (cov t) ((hLevi t).2) y X u v
  have hGfirst : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) z
        (covariantTwoTensorCovariantDerivative (cov t) G z)) y := by
    intro y
    rw [hGderiv]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
      (F := E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃)
        (B := M) (EB := E) (HB := H) (IB := I) (x := y)
  let nu : ℝ := g.curvatureNu cov hcov hLevi hdim t x
  have hnegG : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        ((-nu) • G z)) y := by
    intro y
    have hc : MDiffAt (fun _ : M => -nu) y := mdifferentiableAt_const
    exact hc.smul_section (hG y)
  have hnegGderiv :
      covariantTwoTensorCovariantDerivative (cov t) ((-nu) • G) =
        (-nu) • covariantTwoTensorCovariantDerivative (cov t) G := by
    funext y
    exact covariantTwoTensorCovariantDerivative_smul_const (cov t) (-nu) (hG y)
  have hnegGfirst : MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) z
        (covariantTwoTensorCovariantDerivative (cov t) ((-nu) • G) z)) x := by
    rw [hnegGderiv, hGderiv]
    simp only [smul_zero, Pi.zero_apply]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
      (F := E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃)
        (B := M) (EB := E) (HB := H) (IB := I) (x := x)
  have hfirstAdd :
      covariantTwoTensorCovariantDerivative (cov t) (O + (-nu) • G) =
        covariantTwoTensorCovariantDerivative (cov t) O +
          covariantTwoTensorCovariantDerivative (cov t) ((-nu) • G) := by
    funext y
    exact covariantTwoTensorCovariantDerivative_add (cov t) (hO y) (hnegG y)
  have hLapG : connectionLaplacian (cov t) G x = 0 := by
    letI : FiniteDimensional ℝ (TM x) :=
      VectorBundle.finiteDimensional ℝ E TM x
    rw [connectionLaplacian_eq_sum_orthonormalBasis (cov t) G x
      (stdOrthonormalBasis ℝ (TM x))]
    simp [covariantHessianTwoTensor, hGderiv]
  have hLapNegG := connectionLaplacian_smul_const (cov t) (-nu)
    (hGfirst x) hnegGderiv
  have hLapAdd := connectionLaplacian_add (cov t) hOfirst hnegGfirst hfirstAdd
  have hshift : O + (-nu) • G =
      g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x := by
    funext y
    ext u v
    have hinner : (g t).inner y u v = Inner.inner ℝ u v := rfl
    simp [O, G, nu, curvatureNuShiftedContactTwoTensor,
      riemannianMetricCovariantTwoTensor_apply, sub_eq_add_neg, hinner] <;> ring
  rw [← hshift]
  rw [hLapAdd, hLapNegG, hLapG]
  simpa [O]

/-! The preceding bridge can now be used at the certificate boundary.  An
unshifted actual curvature-operator evolution equation is transported to the
shifted equation expected by the existing Hamilton--Ivey certificate. -/

/-- Construct a Hamilton--Ivey curvature-evolution certificate from a genuine
connection variation and an actual evolution equation for the lowered
curvature operator.

The operator evolution and its spatial regularity remain explicit inputs.
This definition only transports the unshifted connection Laplacian to the
shifted one using the proved metric-compatibility identity. -/
def HamiltonIveyCurvatureEvolutionCertificate.of_connectionVariation_of_operatorEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {t : ℝ} (x : M)
    (A : ∀ z : M, TM z → TM z → TM z)
    (curvatureVelocity : ∀ z : M,
      TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hvelocity : ∀ (z : M) (a b c : TM z),
      curvatureVelocity z a b c =
        TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
          (I := I) (M := M) cov A t z a b c)
    (hvariation :
      TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
        (I := I) (M := M) cov A t)
    (hA : ∀ (X Y : Π y : M, TM y),
      (∀ y, MDiffAt (T% X) y) → (∀ y, MDiffAt (T% Y) y) →
        ∀ y, MDiffAt (T% (fun z => A z (X z) (Y z))) y)
    (hregular : g.HamiltonIveyCurvatureOperatorRegularity
      cov hcov hLevi hdim t x)
    (hEvolutionOperator :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedSpace
      letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
        inferInstance
      ∀ u v : TM x,
        HasDerivAt
          (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x u v)
          (connectionLaplacian (cov t)
              (fun y => g.curvatureOperatorTwoTensor cov hcov t y) x u v +
            curvatureOperatorReaction g cov hcov hLevi hdim t x u v) t) :
    HamiltonIveyCurvatureEvolutionCertificate g cov hcov hLevi hdim t x := by
  apply HamiltonIveyCurvatureEvolutionCertificate.of_connectionVariation
    g cov hcov hLevi hdim x A curvatureVelocity hvelocity hvariation hA
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  have hLap :
      connectionLaplacian (cov t)
          (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x) x =
        connectionLaplacian (cov t)
          (fun y => g.curvatureOperatorTwoTensor cov hcov t y) x := by
    simpa only using
      (connectionLaplacian_curvatureNuShiftedContactTwoTensor_eq_curvatureOperatorTwoTensor
        g cov hcov hLevi hdim t x hregular)
  intro u v
  have hderiv := hEvolutionOperator u v
  apply hderiv.congr_deriv
  have hLapUV := congrArg (fun B => B u v) hLap
  rw [hLapUV]

/-! The full lowered-curvature evolution certificate implies the contact
velocity identity needed by the Hamilton--Ivey reduction.  This is only a
transport step: the certificate still carries the actual connection
Laplacian-plus-reaction evolution for the geometric curvature tensor. -/

theorem HamiltonIveyCurvatureEvolutionCertificate.contactOperatorVelocity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (c : HamiltonIveyCurvatureEvolutionCertificate
      g cov hcov hLevi hdim t x) :
    curvatureOperatorTwoTensorVelocity g cov hcov t
        (curvatureTensorVelocityRicci c.curvatureVelocity) x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hRicci := hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
    g cov hcov hLevi c.curvatureVelocity c.hCurvature
  have hEvolutionContact :
      HasDerivAt (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x V V)
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x V V) t := by
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedSpace
    letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
      inferInstance
    simpa [V, hamiltonIveyContactCurvatureLaplacian] using c.hEvolution V V
  exact g.curvatureOperatorTwoTensorVelocity_eq_of_curvatureOperatorReactionEvolution
    cov hcov hLevi hdim gdot s hflow ht x
    (curvatureTensorVelocityRicci c.curvatureVelocity) hRicci hEvolutionContact

/-! Taking the actual metric trace of the full curvature evolution recovers
the scalar Ricci-variation trace.  The remaining input here is stated
explicitly: trace must commute with the connection Laplacian on the shifted
curvature tensor.  This isolates that differential-geometric lemma from the
finite-dimensional reaction-trace calculation above. -/

/-- The trace/Laplacian commutation identity for the shifted curvature
operator, evaluated in its genuine Ricci-complement orthonormal eigenbasis.
The basis is only an evaluation device; it is the metric trace of the actual
connection Laplacian. -/
def HamiltonIveyTraceLaplacianAt
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E) (cov t)
    (hLevi t).1 (hLevi t).2 x (hdim x)
  exact
    (∑ i : Fin 3,
      connectionLaplacian (cov t)
        (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x)
        x (b i) (b i)) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x
/-- The pointwise regularity data needed to form the shifted-tensor trace
Laplacian identity.  This packages only differentiability statements for the
actual shifted curvature tensor and its covariant derivatives; it does not
contain the target trace identity. -/
def HamiltonIveyShiftedTensorTraceRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedAddCommGroup (T₃ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedSpace ℝ (T₃ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I := by infer_instance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    by infer_instance
  letI : ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I := by infer_instance
  let H : ∀ y : M, T₂ y :=
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x
  exact
    (∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (raisedCovariantTwoTensor (I := I) (E := E) H z)) y) ∧
    MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t) H y)) x ∧
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H) y)) x ∧
    (∀ Y : TM x,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (raisedCovariantTwoTensor (I := I) (E := E)
            (covariantTwoTensorDerivativeAlong (cov t) H
              (smoothExtend (I := I) (F := E) (V := TM) x Y)) z)) x)

/-- The shifted-tensor regularity needed by the trace/Laplacian bridge follows
from regularity of the actual lowered curvature operator.  The contact shift
is a spatially constant multiple of the metric, and metric compatibility
annihilates its covariant derivative; the remaining tensor operations are
proved bundle operations rather than assumptions on coordinate components. -/
theorem HamiltonIveyShiftedTensorTraceRegularity.of_curvatureOperatorRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M)
    (hregular : g.HamiltonIveyCurvatureOperatorRegularity
      cov hcov hLevi hdim t x) :
    g.HamiltonIveyShiftedTensorTraceRegularity
      cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedAddCommGroup (T₃ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedSpace ℝ (T₃ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I := by infer_instance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I := by
    infer_instance
  letI : ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let H : ∀ y : M, T₂ y :=
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x
  let O : ∀ y : M, T₂ y :=
    fun y => g.curvatureOperatorTwoTensor cov hcov t y
  let G : ∀ y : M, T₂ y :=
    riemannianMetricCovariantTwoTensor (I := I) (M := M)
  let nu : ℝ := g.curvatureNu cov hcov hLevi hdim t x
  rcases hregular with ⟨hoperator, hoperatorFirst⟩
  have hO : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        (O z)) y := by
    intro y
    simpa [O] using hoperator y
  have hG : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        (G z)) y := by
    intro y
    exact riemannianMetricCovariantTwoTensor_mdifferentiableAt
      (I := I) (E := E) (M := M) y
  have hGderiv : covariantTwoTensorCovariantDerivative (cov t) G = 0 := by
    funext y
    ext X u v
    exact covariantTwoTensorCovariantDerivative_riemannianMetric_eq_zero
      (cov t) ((hLevi t).2) y X u v
  have hnegG : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        ((-nu) • G z)) y := by
    intro y
    have hc : MDiffAt (fun _ : M => -nu) y := mdifferentiableAt_const
    exact hc.smul_section (hG y)
  have hnegGderiv :
      covariantTwoTensorCovariantDerivative (cov t) ((-nu) • G) =
        (-nu) • covariantTwoTensorCovariantDerivative (cov t) G := by
    funext y
    exact covariantTwoTensorCovariantDerivative_smul_const (cov t) (-nu) (hG y)
  have hfirstAdd :
      covariantTwoTensorCovariantDerivative (cov t) (O + (-nu) • G) =
        covariantTwoTensorCovariantDerivative (cov t) O +
          covariantTwoTensorCovariantDerivative (cov t) ((-nu) • G) := by
    funext y
    exact covariantTwoTensorCovariantDerivative_add (cov t) (hO y) (hnegG y)
  have hshift : O + (-nu) • G = H := by
    funext y
    ext u v
    have hinner : (g t).inner y u v = Inner.inner ℝ u v := rfl
    simp [O, G, H, nu, curvatureNuShiftedContactTwoTensor,
      riemannianMetricCovariantTwoTensor_apply, sub_eq_add_neg, hinner] <;> ring
  have hH : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z
        (H z)) y := by
    rw [← hshift]
    intro y
    exact mdifferentiableAt_add_section (hO y) (hnegG y)
  have hHderiv :
      covariantTwoTensorCovariantDerivative (cov t) H =
        covariantTwoTensorCovariantDerivative (cov t) O := by
    rw [← hshift, hfirstAdd, hnegGderiv, hGderiv]
    simp
  have hHfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t) H y)) x := by
    rw [hHderiv]
    simpa [O] using hoperatorFirst
  have hHraised : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun w : M => TM w →L[ℝ] TM w) z
        (raisedCovariantTwoTensor (I := I) (E := E) H z)) y := by
    intro y
    exact raisedCovariantTwoTensor_mdifferentiableAt
      (I := I) (E := E) (M := M) (h := H) (x₀ := y) (hH y)
  have htraceDifferential :=
    mdifferentiableAt_scalarDifferential_covariantTwoTensorTraceFunction
      (I := I) (E := E) (M := M) (cov t) ((hLevi t).2) H hHraised hHfirst
  have hHsecondRaised : ∀ Y : TM x, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun w : M => TM w →L[ℝ] TM w) z
        (raisedCovariantTwoTensor (I := I) (E := E)
          (covariantTwoTensorDerivativeAlong (cov t) H
            (smoothExtend (I := I) (F := E) (V := TM) x Y)) z)) x := by
    intro Y
    let Yfield : ∀ y : M, TM y :=
      smoothExtend (I := I) (F := E) (V := TM) x Y
    let K : ∀ y : M, T₂ y :=
      covariantTwoTensorDerivativeAlong (cov t) H Yfield
    have hYfield : MDiffAt (T% Yfield) x :=
      ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x Y).of_le
        (by simp) x).mdifferentiableAt one_ne_zero
    have hK : MDiffAt
        (fun y => TotalSpace.mk'
          (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (K y)) x := by
      have hK' := hHfirst.clm_bundle_apply hYfield
      simpa [K, covariantTwoTensorDerivativeAlong, Yfield] using hK'
    have hKraised := raisedCovariantTwoTensor_mdifferentiableAt
      (I := I) (E := E) (M := M) (h := K) (x₀ := x) hK
    simpa [K, Yfield, covariantTwoTensorDerivativeAlong] using hKraised
  exact ⟨hHraised, hHfirst, htraceDifferential, hHsecondRaised⟩

/-- The trace components of the shifted-curvature regularity certificate
already supply first- and second-order spatial regularity of scalar curvature:
the trace of the contact-shifted curvature tensor is `R - 3 nu_contact`, and
the contact eigenvalue is constant in the spatial variable. -/
theorem scalarRegularity_of_shiftedTensorRegularity
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M)
    (hregular : g.HamiltonIveyShiftedTensorTraceRegularity
      cov hcov hLevi hdim t x) :
    MDiffAt (g.scalarCurvature cov hcov t) x ∧
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I)
          (g.scalarCurvature cov hcov t) y)) x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedAddCommGroup (T₃ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedSpace ℝ (T₃ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I := by infer_instance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I := by infer_instance
  letI : ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ∀ y : M, FiniteDimensional ℝ (TM y) := fun y =>
    VectorBundle.finiteDimensional ℝ E TM y
  let H : ∀ y : M, T₂ y :=
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x
  rcases hregular with ⟨hHraised, _hHfirst, htraceDifferential,
    _hHsecondRaised⟩
  have htraceH (y : M) :
      covariantTwoTensorTraceFunction (I := I) (E := E) H y =
        g.scalarCurvature cov hcov t y -
          3 * g.curvatureNu cov hcov hLevi hdim t x := by
    let b' : OrthonormalBasis (Fin 3) ℝ (TM y) :=
      CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E) (cov t)
        (hLevi t).1 (hLevi t).2 y (hdim y)
    have hinner' (i : Fin 3) : (g t).inner y (b' i) (b' i) = 1 := by
      change Inner.inner ℝ (b' i) (b' i) = 1
      rw [real_inner_self_eq_norm_sq, b'.orthonormal.1]
      norm_num
    have hsumRicci' :
        (∑ i : Fin 3, g.ricciCurvature cov hcov t y (b' i) (b' i)) =
          g.scalarCurvature cov hcov t y := by
      have h := CovariantDerivative.scalarCurvature_eq_sum_ricci_orthonormalBasis
        (cov := cov t) y b'
      simpa [TimeDependentRiemannianMetric.scalarCurvature,
        TimeDependentRiemannianMetric.ricciCurvature] using h.symm
    have hterm (i : Fin 3) :
        H y (b' i) (b' i) =
          g.scalarCurvature cov hcov t y -
            2 * g.ricciCurvature cov hcov t y (b' i) (b' i) -
              g.curvatureNu cov hcov hLevi hdim t x := by
      simp [H, hinner' i]
    calc
      _ = ∑ i : Fin 3, H y (b' i) (b' i) := by
        exact covariantTwoTensorTrace_eq_sum_orthonormalBasis
          (covariantTwoTensorLinear (I := I) (M := M) H) y b'
      _ = ∑ i : Fin 3,
          (g.scalarCurvature cov hcov t y -
            2 * g.ricciCurvature cov hcov t y (b' i) (b' i) -
              g.curvatureNu cov hcov hLevi hdim t x) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
      _ = g.scalarCurvature cov hcov t y -
          3 * g.curvatureNu cov hcov hLevi hdim t x := by
        rw [Fin.sum_univ_three]
        have hsumRicci'' := hsumRicci'
        rw [Fin.sum_univ_three] at hsumRicci''
        rw [← hsumRicci'']
        ring
  have htraceMDiff :
      ∀ y : M, MDiffAt (covariantTwoTensorTraceFunction
        (I := I) (E := E) H) y := by
    intro y
    rw [covariantTwoTensorTraceFunction_eq_endomorphismTrace_raised
      (I := I) (E := E) (M := M) H]
    exact mdifferentiableAt_endomorphismTrace
      (F := E) (V := TM) (hHraised y)
  let scalar : M → ℝ := g.scalarCurvature cov hcov t
  let traceOffset : ℝ := 3 * g.curvatureNu cov hcov hLevi hdim t x
  have hscalarAdd :
      scalar = covariantTwoTensorTraceFunction (I := I) (E := E) H +
        (fun _ : M => traceOffset) := by
    funext y
    change g.scalarCurvature cov hcov t y =
      covariantTwoTensorTraceFunction (I := I) (E := E) H y +
        3 * g.curvatureNu cov hcov hLevi hdim t x
    rw [htraceH y]
    ring
  have hoffsetMDiff : ∀ y : M, MDiffAt (fun _ : M => traceOffset) y := by
    intro y
    exact mdifferentiableAt_const
  have hoffsetDifferential :
      scalarDifferential (I := I) (fun _ : M => traceOffset) = 0 := by
    funext y
    have hzero (y : M) :
        scalarDifferential (I := I) (fun _ : M => traceOffset) y = 0 := by
      ext u
      simp only [scalarDifferential_apply]
      rw [mvfderiv_const]
    exact hzero y
  have hscalarDifferentialEq :
      scalarDifferential (I := I) scalar =
        scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H) := by
    calc
      _ = scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H +
            (fun _ : M => traceOffset)) := by rw [hscalarAdd]
      _ = scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H) +
            scalarDifferential (I := I) (fun _ : M => traceOffset) :=
        scalarDifferential_add htraceMDiff hoffsetMDiff
      _ = _ := by rw [hoffsetDifferential]; simp
  have hscalarAt : MDiffAt (g.scalarCurvature cov hcov t) x := by
    change MDiffAt scalar x
    rw [hscalarAdd]
    exact (htraceMDiff x).add mdifferentiableAt_const
  have hscalarDifferentialAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I)
          (g.scalarCurvature cov hcov t) y)) x := by
    have h := htraceDifferential
    rw [← hscalarDifferentialEq] at h
    exact h
  exact ⟨hscalarAt, hscalarDifferentialAt⟩

/-- The scalar-gradient part of the shifted-tensor regularity bridge. -/
theorem scalarDifferential_mdifferentiableAt_of_shiftedTensorRegularity
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M)
    (hregular : g.HamiltonIveyShiftedTensorTraceRegularity
      cov hcov hLevi hdim t x) :
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I)
          (g.scalarCurvature cov hcov t) y)) x := by
  exact (g.scalarRegularity_of_shiftedTensorRegularity
    cov hcov hLevi hdim t x hregular).2

/-- The Hamilton--Ivey trace/Laplacian bridge follows from the proved
second-order metric-trace commutation theorem, provided the actual shifted
 curvature tensor has the differentiability needed to form its genuine
 connection Laplacian.  The regularity package is deliberately explicit: it
 is not implied by the current `C¹` connection input alone. -/
theorem HamiltonIveyTraceLaplacianAt_of_shiftedTensorRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M)
    (hregular : g.HamiltonIveyShiftedTensorTraceRegularity
      cov hcov hLevi hdim t x) :
    g.HamiltonIveyTraceLaplacianAt cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedAddCommGroup (T₃ y) := fun _ => inferInstance
  letI : ∀ y : M, NormedSpace ℝ (T₃ y) := fun _ => inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
  letI : NormedAddCommGroup
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : NormedSpace ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
  letI : FiberBundle (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ := inferInstance
  letI : FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ := inferInstance
  letI : FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ := inferInstance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I := by infer_instance
  letI : ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
    by infer_instance
  letI : ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ∀ y : M, FiniteDimensional ℝ (TM y) := fun y =>
    VectorBundle.finiteDimensional ℝ E TM y
  let H : ∀ y : M, T₂ y :=
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x
  rcases hregular with ⟨hHraised, hHfirst, htraceDifferential, hHsecondRaised⟩
  let b : OrthonormalBasis (Fin 3) ℝ (TM x) :=
    CovariantDerivative.ricciComplementEigenbasis
      (I := I) (M := M) (E := E) (cov t)
      (hLevi t).1 (hLevi t).2 x (hdim x)
  have hinner (i : Fin 3) : (g t).inner x (b i) (b i) = 1 := by
    change Inner.inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1]
    norm_num
  have hsumRicci :
      (∑ i : Fin 3, g.ricciCurvature cov hcov t x (b i) (b i)) =
        g.scalarCurvature cov hcov t x := by
    have h := CovariantDerivative.scalarCurvature_eq_sum_ricci_orthonormalBasis
      (cov := cov t) x b
    simpa [TimeDependentRiemannianMetric.scalarCurvature,
      TimeDependentRiemannianMetric.ricciCurvature] using h.symm
  have htraceH (y : M) :
      covariantTwoTensorTraceFunction (I := I) (E := E) H y =
        g.scalarCurvature cov hcov t y -
          3 * g.curvatureNu cov hcov hLevi hdim t x := by
    let b' : OrthonormalBasis (Fin 3) ℝ (TM y) :=
      CovariantDerivative.ricciComplementEigenbasis
        (I := I) (M := M) (E := E) (cov t)
        (hLevi t).1 (hLevi t).2 y (hdim y)
    have hinner' (i : Fin 3) : (g t).inner y (b' i) (b' i) = 1 := by
      change Inner.inner ℝ (b' i) (b' i) = 1
      rw [real_inner_self_eq_norm_sq, b'.orthonormal.1]
      norm_num
    have hsumRicci' :
        (∑ i : Fin 3, g.ricciCurvature cov hcov t y (b' i) (b' i)) =
          g.scalarCurvature cov hcov t y := by
      have h := CovariantDerivative.scalarCurvature_eq_sum_ricci_orthonormalBasis
        (cov := cov t) y b'
      simpa [TimeDependentRiemannianMetric.scalarCurvature,
        TimeDependentRiemannianMetric.ricciCurvature] using h.symm
    have hterm (i : Fin 3) :
        H y (b' i) (b' i) =
          g.scalarCurvature cov hcov t y -
            2 * g.ricciCurvature cov hcov t y (b' i) (b' i) -
              g.curvatureNu cov hcov hLevi hdim t x := by
      simp [H, hinner' i]
    calc
      _ = ∑ i : Fin 3, H y (b' i) (b' i) := by
        exact covariantTwoTensorTrace_eq_sum_orthonormalBasis
          (covariantTwoTensorLinear (I := I) (M := M) H) y b'
      _ = ∑ i : Fin 3,
          (g.scalarCurvature cov hcov t y -
            2 * g.ricciCurvature cov hcov t y (b' i) (b' i) -
              g.curvatureNu cov hcov hLevi hdim t x) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
      _ = g.scalarCurvature cov hcov t y -
          3 * g.curvatureNu cov hcov hLevi hdim t x := by
        rw [Fin.sum_univ_three]
        have hsumRicci'' := hsumRicci'
        rw [Fin.sum_univ_three] at hsumRicci''
        rw [← hsumRicci'']
        ring
  have htraceMDiff :
      ∀ y : M, MDiffAt (covariantTwoTensorTraceFunction (I := I) (E := E) H) y := by
    intro y
    rw [covariantTwoTensorTraceFunction_eq_endomorphismTrace_raised
      (I := I) (E := E) (M := M) H]
    exact mdifferentiableAt_endomorphismTrace
      (F := E) (V := TM) (hHraised y)
  let scalar : M → ℝ := g.scalarCurvature cov hcov t
  let traceOffset : ℝ := 3 * g.curvatureNu cov hcov hLevi hdim t x
  have hscalarAdd :
      scalar = covariantTwoTensorTraceFunction (I := I) (E := E) H +
        (fun _ : M => traceOffset) := by
    funext y
    change g.scalarCurvature cov hcov t y =
      covariantTwoTensorTraceFunction (I := I) (E := E) H y +
        3 * g.curvatureNu cov hcov hLevi hdim t x
    rw [htraceH y]
    ring
  have hscalarMDiff : ∀ y : M, MDiffAt scalar y := by
    intro y
    rw [hscalarAdd]
    exact (htraceMDiff y).add mdifferentiableAt_const
  have hoffsetMDiff : ∀ y : M, MDiffAt (fun _ : M => traceOffset) y := by
    intro y
    exact mdifferentiableAt_const
  have hoffsetDifferential :
      scalarDifferential (I := I) (fun _ : M => traceOffset) = 0 := by
    funext y
    have hzero (y : M) :
        scalarDifferential (I := I) (fun _ : M => traceOffset) y = 0 := by
      ext u
      simp only [scalarDifferential_apply]
      rw [mvfderiv_const]
    exact hzero y
  have hscalarDifferentialEq :
      scalarDifferential (I := I) scalar =
        scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H) := by
    calc
      _ = scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H +
            (fun _ : M => traceOffset)) := by rw [hscalarAdd]
      _ = scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H) +
            scalarDifferential (I := I) (fun _ : M => traceOffset) :=
          scalarDifferential_add htraceMDiff hoffsetMDiff
      _ = _ := by rw [hoffsetDifferential]; simp
  have hscalarDifferential :
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I) scalar y)) x := by
    have h := htraceDifferential
    rw [← hscalarDifferentialEq] at h
    exact h
  let offsetFunction : M → ℝ := fun _ => -traceOffset
  have hoffsetFunctionMDiff : ∀ y : M, MDiffAt offsetFunction y := by
    intro y
    exact mdifferentiableAt_const
  have hoffsetFunctionDifferential :
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I) offsetFunction y)) x := by
    have hzero :
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I) offsetFunction y)) =
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y 0) := by
      have hconstant (y : M) :
          scalarDifferential (I := I) offsetFunction y = 0 := by
        ext u
        simp only [scalarDifferential_apply]
        rw [mvfderiv_const]
      funext y
      congr 1
      exact hconstant y
    rw [hzero]
    exact mdifferentiableAt_zeroSection
      (𝕜 := ℝ) (F := E →L[ℝ] ℝ) (E := T₁) (x := x)
  have htraceOffsetLap :
      CovariantDerivative.scalarLaplacian (cov t)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H) x =
        CovariantDerivative.scalarLaplacian (cov t) scalar x := by
    have hsum :
      covariantTwoTensorTraceFunction (I := I) (E := E) H =
          scalar + offsetFunction := by
      funext y
      change covariantTwoTensorTraceFunction (I := I) (E := E) H y =
        g.scalarCurvature cov hcov t y -
          3 * g.curvatureNu cov hcov hLevi hdim t x
      exact htraceH y
    calc
      _ = CovariantDerivative.scalarLaplacian (cov t)
          (scalar + offsetFunction) x := by
        rw [hsum]
      _ = CovariantDerivative.scalarLaplacian (cov t) scalar x +
          CovariantDerivative.scalarLaplacian (cov t) offsetFunction x :=
        CovariantDerivative.scalarLaplacian_add (cov t) hscalarMDiff hoffsetFunctionMDiff
          hscalarDifferential hoffsetFunctionDifferential
      _ = CovariantDerivative.scalarLaplacian (cov t) scalar x := by
        rw [CovariantDerivative.scalarLaplacian_const]
        ring
  let HtraceLaplacian :
      CovariantDerivative.scalarLaplacian (cov t)
          (covariantTwoTensorTraceFunction (I := I) (E := E) H) x =
        covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M)
          (fun y => connectionLaplacian (cov t) H y)) x := by
    exact
      scalarLaplacian_covariantTwoTensorTraceFunction_eq_covariantTwoTensorTrace_connectionLaplacian
        (I := I) (E := E) (M := M) (cov t) (hLevi t).2 H hHraised
        hHfirst htraceDifferential hHsecondRaised b
  have htraceBasis :
      covariantTwoTensorTrace (I := I) (E := E) (M := M)
          (covariantTwoTensorLinear (I := I) (M := M)
            (fun y => connectionLaplacian (cov t) H y)) x =
        ∑ i : Fin 3, connectionLaplacian (cov t) H x (b i) (b i) := by
    rw [covariantTwoTensorTrace_eq_sum_orthonormalBasis
      (I := I) (E := E) (M := M)
      (covariantTwoTensorLinear (I := I) (M := M)
        (fun y => connectionLaplacian (cov t) H y)) x b]
    simp [covariantTwoTensorLinear_apply]
  have hscalarTrace :
      CovariantDerivative.scalarLaplacian (cov t) scalar x =
        ∑ i : Fin 3, connectionLaplacian (cov t) H x (b i) (b i) := by
    calc
      _ = covariantTwoTensorTrace (I := I) (E := E) (M := M)
          (covariantTwoTensorLinear (I := I) (M := M)
            (fun y => connectionLaplacian (cov t) H y)) x := by
              rw [← htraceOffsetLap]
              exact HtraceLaplacian
      _ = _ := htraceBasis
  change (∑ i : Fin 3,
      connectionLaplacian (cov t)
        (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x)
        x (b i) (b i)) = CovariantDerivative.scalarLaplacian (cov t) scalar x
  exact hscalarTrace.symm

/-- In dimension three, the genuine metric trace of the lowered
Ricci-complement curvature tensor is scalar curvature.  This is the trace
identity needed to read scalar evolution directly from the lowered-operator
evolution, without first differentiating the Ricci tensor. -/
theorem metricTraceAt_curvatureOperatorTwoTensor_eq_scalarCurvature
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    RicciFlow.metricTraceAt (I := I) (M := M) g t x
      (covariantTwoTensorLinear (I := I) (M := M)
        (fun y => g.curvatureOperatorTwoTensor cov hcov t y) x) =
      g.scalarCurvature cov hcov t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TM x)
  have hinner (i : Fin (Module.finrank ℝ (TM x))) :
      (g t).inner x (b i) (b i) = 1 := by
    change Inner.inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1]
    norm_num
  have hsumRicci :
      (∑ i : Fin (Module.finrank ℝ (TM x)),
        g.ricciCurvature cov hcov t x (b i) (b i)) =
        g.scalarCurvature cov hcov t x := by
    have h := CovariantDerivative.scalarCurvature_eq_sum_ricci_orthonormalBasis
      (cov := cov t) x b
    simpa [TimeDependentRiemannianMetric.scalarCurvature,
      TimeDependentRiemannianMetric.ricciCurvature] using h.symm
  have htrace :
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (covariantTwoTensorLinear (I := I) (M := M)
          (fun y => g.curvatureOperatorTwoTensor cov hcov t y) x) =
      ∑ i : Fin (Module.finrank ℝ (TM x)),
        g.curvatureOperatorTwoTensor cov hcov t x (b i) (b i) := by
    unfold RicciFlow.metricTraceAt
    rw [InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) b, map_sum]
    simp [covariantTwoTensorLinear_apply]
  have hsumScalar :
      (∑ i : Fin (Module.finrank ℝ (TM x)),
        g.scalarCurvature cov hcov t x) =
        (Module.finrank ℝ (TM x) : ℝ) *
          g.scalarCurvature cov hcov t x := by
    simp
  calc
    _ = ∑ i : Fin (Module.finrank ℝ (TM x)),
        (g.scalarCurvature cov hcov t x -
          2 * g.ricciCurvature cov hcov t x (b i) (b i)) := by
      rw [htrace]
      apply Finset.sum_congr rfl
      intro i hi
      rw [g.curvatureOperatorTwoTensor_apply, hinner i]
      ring
    _ = (∑ i : Fin (Module.finrank ℝ (TM x)),
          g.scalarCurvature cov hcov t x) -
        2 * (∑ i : Fin (Module.finrank ℝ (TM x)),
          g.ricciCurvature cov hcov t x (b i) (b i)) := by
      simp [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = g.scalarCurvature cov hcov t x := by
      rw [hsumScalar, hsumRicci, hdim x]
      ring

/-- The scalar-curvature evolution follows from the genuine lowered
curvature-operator evolution by differentiating its metric trace.  This
calculation includes the inverse-metric variation under Ricci flow; it does
not assume or request a separate time derivative of the Ricci tensor. -/
theorem hasDerivAt_scalarCurvature_of_curvatureOperatorEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (hEvolution :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
        ContinuousLinearMap.toNormedSpace
      letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
        ContinuousLinearMap.toNormedAddCommGroup
      letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
        inferInstance
      ∀ u v : TM x,
        HasDerivAt
          (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x u v)
          (connectionLaplacian (cov t)
              (g.curvatureNuShiftedContactTwoTensor
                cov hcov hLevi hdim t x) x u v +
            curvatureOperatorReaction g cov hcov hLevi hdim t x u v) t)
    (hTraceLaplacian :
      g.HamiltonIveyTraceLaplacianAt cov hcov hLevi hdim t x) :
    HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x)
      (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
        2 * g.ricciNormSq cov hcov t x) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ => inferInstance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let b := CovariantDerivative.ricciComplementEigenbasis
    (I := I) (M := M) (E := E) (cov t)
    (hLevi t).1 (hLevi t).2 x (hdim x)
  let e : Trivialization E (π E TM) := trivializationAt E TM x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x
  let bas : Module.Basis (Fin 3) ℝ E :=
    b.toBasis.map (e.linearEquivAt (R := ℝ) x hx)
  have hframe (i : Fin 3) : e.localFrame bas i x = b i := by
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := e) (b := bas) hx]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
    rw [Bundle.Trivialization.linearEquivAt_symm_apply]
    exact e.symm_apply_apply_mk hx (b i)
  let G : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun τ =>
    RicciFlow.localFrameMetricMatrix (I := I) (M := M) g e bas τ x
  let Q : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun τ i j =>
    g.curvatureOperatorTwoTensor cov hcov τ x
      (e.localFrame bas i x) (e.localFrame bas j x)
  let Gdot : Matrix (Fin 3) (Fin 3) ℝ :=
    RicciFlow.localFrameTensorMatrix (I := I) (M := M) gdot e bas t x
  let RicciMat : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    g.ricciCurvature cov hcov t x (b i) (b j)
  let H : ∀ y : M, T₂ y :=
    g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t x
  let Qdot : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    connectionLaplacian (cov t) H x (b i) (b j) +
      curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b j)
  have hG : ∀ i j : Fin 3,
      HasDerivAt (fun τ => G τ i j) (Gdot i j) t := by
    intro i j
    exact (hflow.2.1 ht).hasDerivAt_localFrameMetricMatrix e bas x i j
  have hQ : ∀ i j : Fin 3,
      HasDerivAt (fun τ => Q τ i j) (Qdot i j) t := by
    intro i j
    simpa [Q, Qdot, H, hframe] using hEvolution (b i) (b j)
  have hcontract := PoincareCurvature.hasDerivAt_nonsing_inv_matrixContraction
    (A := G) (S := Q) (Adot := Gdot) (Sdot := Qdot) (t := t)
    hG hQ (fun τ => RicciFlow.localFrameMetricMatrix_det_ne_zero
      (I := I) (M := M) g e bas τ hx)
  have hreadout :
      (fun τ => PoincareCurvature.matrixContraction (G τ)⁻¹ (Q τ)) =
        (fun τ => g.scalarCurvature cov hcov τ x) := by
    funext τ
    have hlocal := RicciFlow.matrixContraction_localFrameTensor_eq_metricTraceAt
      (I := I) (M := M) g τ
      (covariantTwoTensorLinear (I := I) (M := M)
        (fun y => g.curvatureOperatorTwoTensor cov hcov τ y) x) e bas hx
    calc
      PoincareCurvature.matrixContraction (G τ)⁻¹ (Q τ) =
          RicciFlow.metricTraceAt (I := I) (M := M) g τ x
            (covariantTwoTensorLinear (I := I) (M := M)
              (fun y => g.curvatureOperatorTwoTensor cov hcov τ y) x) := by
        simpa [G, Q, covariantTwoTensorLinear_apply, hframe] using hlocal
      _ = g.scalarCurvature cov hcov τ x :=
        metricTraceAt_curvatureOperatorTwoTensor_eq_scalarCurvature
          g cov hcov hdim τ x
  rw [hreadout] at hcontract
  let R : ℝ := g.scalarCurvature cov hcov t x
  let eig : Fin 3 → ℝ := g.curvatureEigenvalues cov hcov hLevi hdim t x
  let lam : ℝ := g.curvatureLambda cov hcov hLevi hdim t x
  let mu : ℝ := g.curvatureMu cov hcov hLevi hdim t x
  let nu : ℝ := g.curvatureNu cov hcov hLevi hdim t x
  have hinner (i j : Fin 3) :
      (g t).inner x (b i) (b j) = if i = j then 1 else 0 := by
    change Inner.inner ℝ (b i) (b j) = if i = j then 1 else 0
    exact orthonormal_iff_ite.mp b.orthonormal i j
  have hGAt : G t = 1 := by
    ext i j
    change (g t).inner x (e.localFrame bas i x) (e.localFrame bas j x) = _
    rw [hframe i, hframe j]
    exact hinner i j
  have hGdot : Gdot = (-2 : ℝ) • RicciMat := by
    ext i j
    change gdot t x (e.localFrame bas i x) (e.localFrame bas j x) =
      ((-2 : ℝ) • RicciMat) i j
    rw [hframe i, hframe j]
    change gdot t x (b i) (b j) = (-2 : ℝ) * RicciMat i j
    have heq := hflow.2.2 ht x (b i) (b j)
    simpa [RicciMat,
      RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor,
      TimeDependentRiemannianMetric.ricciCurvature] using heq
  have hA (i : Fin 3) :
      g.curvatureEndomorphismApply cov hcov t x (b i) = eig i • b i := by
    have h := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
      (I := I) (M := M) (E := E) (cov t)
      (hLevi t).1 (hLevi t).2 x (hdim x) i
    simpa [curvatureEndomorphismApply, eig, b, curvatureEigenvalues] using h
  have hQAt : Q t = fun i j => if i = j then eig i else 0 := by
    ext i j
    change g.curvatureOperatorTwoTensor cov hcov t x
      (e.localFrame bas i x) (e.localFrame bas j x) = _
    rw [hframe i, hframe j,
      g.curvatureOperatorTwoTensor_eq_inner_curvatureEndomorphismApply
        cov hcov hLevi t x (b i) (b j), hA j]
    by_cases hij : i = j
    · subst j
      simp [real_inner_smul_right, hinner]
    · simp [real_inner_smul_right, hinner, hij]
  have hQdiag (i : Fin 3) :
      g.curvatureOperatorTwoTensor cov hcov t x (b i) (b i) = eig i := by
    simpa [Q, hframe] using congrFun (congrFun hQAt i) i
  have hRicciDiag (i : Fin 3) :
      g.ricciCurvature cov hcov t x (b i) (b i) = (R - eig i) / 2 := by
    have hformula := g.curvatureOperatorTwoTensor_apply
      cov hcov t x (b i) (b i)
    rw [show (g t).inner x (b i) (b i) = 1 from by
      simpa using hinner i i] at hformula
    have hformula' : R - 2 * g.ricciCurvature cov hcov t x (b i) (b i) =
        eig i := by
      calc
        R - 2 * g.ricciCurvature cov hcov t x (b i) (b i) =
            g.curvatureOperatorTwoTensor cov hcov t x (b i) (b i) := by
          simpa [R] using hformula.symm
        _ = eig i := hQdiag i
    linarith
  have hsumLambda : lam + mu + nu = R := by
    have h := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    simpa [lam, mu, nu, R] using h
  have heig0 : eig 0 = lam := rfl
  have heig1 : eig 1 = mu := rfl
  have heig2 : eig 2 = nu := rfl
  have hsumEig : (∑ i : Fin 3, eig i) = R := by
    rw [Fin.sum_univ_three, heig0, heig1, heig2]
    exact hsumLambda
  have hCorrection :
    PoincareCurvature.matrixContraction
          (-((G t)⁻¹ * Gdot * (G t)⁻¹)) (Q t) =
        R ^ 2 - ∑ i : Fin 3, eig i ^ 2 := by
    rw [hGAt, hGdot, hQAt]
    simp only [inv_one, one_mul, mul_one, neg_smul, neg_neg]
    have hdiagContract (C : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
        PoincareCurvature.matrixContraction C
            (fun i j => if i = j then a i else 0) =
          ∑ i : Fin 3, C i i * a i := by
      classical
      unfold PoincareCurvature.matrixContraction
      simp [Fin.sum_univ_three]
    calc
      PoincareCurvature.matrixContraction
          ((2 : ℝ) • RicciMat)
          (fun i j => if i = j then eig i else 0) =
        ∑ i : Fin 3, (2 * RicciMat i i) * eig i := by
          rw [hdiagContract]
          simp [Matrix.smul_apply, mul_assoc]
      _ = ∑ i : Fin 3, (R - eig i) * eig i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [RicciMat]
          rw [hRicciDiag i]
          ring
      _ = R ^ 2 - ∑ i : Fin 3, eig i ^ 2 := by
          calc
            _ = ∑ i : Fin 3, (eig i * R - eig i ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (∑ i : Fin 3, eig i) * R -
                ∑ i : Fin 3, eig i ^ 2 := by
              rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
            _ = _ := by rw [hsumEig]; ring
  have hsumLaplacian :
      (∑ i : Fin 3,
        connectionLaplacian (cov t) H x (b i) (b i)) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x := by
    simpa [HamiltonIveyTraceLaplacianAt, H, b] using hTraceLaplacian
  have hsumReaction :
      (∑ i : Fin 3,
        curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b i)) =
        6 * g.ricciNormSq cov hcov t x - 2 * R ^ 2 := by
    simpa [R, b] using
      (curvatureOperatorReaction_trace_eq_sixRicciNormSq_sub_twoScalarSq
        g cov hcov hLevi hdim t x)
  have hsumQdot :
      (∑ i : Fin 3, Qdot i i) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          (6 * g.ricciNormSq cov hcov t x - 2 * R ^ 2) := by
    calc
      _ = (∑ i : Fin 3,
          connectionLaplacian (cov t) H x (b i) (b i)) +
          ∑ i : Fin 3,
            curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b i) := by
        simp [Qdot, Finset.sum_add_distrib]
      _ = _ := by rw [hsumLaplacian, hsumReaction]
  have hsecond :
      PoincareCurvature.matrixContraction (G t)⁻¹ Qdot =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          (6 * g.ricciNormSq cov hcov t x - 2 * R ^ 2) := by
    rw [hGAt]
    simp only [inv_one]
    calc
      PoincareCurvature.matrixContraction (1 : Matrix (Fin 3) (Fin 3) ℝ) Qdot =
          ∑ i : Fin 3, Qdot i i := by
        simp [PoincareCurvature.matrixContraction, Matrix.one_apply]
      _ = _ := hsumQdot
  have hnormReaction :=
    two_mul_ricciNormSq_eq_hamiltonIveyScalarReaction
      g cov hcov hLevi hdim t x
  have hsumEigenSquares :
      R ^ 2 + (∑ i : Fin 3, eig i ^ 2) =
        2 * HamiltonIveyReaction.scalarReaction lam mu nu := by
    rw [Fin.sum_univ_three, heig0, heig1, heig2, ← hsumLambda]
    dsimp [HamiltonIveyReaction.scalarReaction]
    ring
  have hderivativeValue :
      PoincareCurvature.matrixContraction
          (-((G t)⁻¹ * Gdot * (G t)⁻¹)) (Q t) +
        PoincareCurvature.matrixContraction (G t)⁻¹ Qdot =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
        2 * g.ricciNormSq cov hcov t x := by
    rw [hCorrection, hsecond]
    have hreaction := hnormReaction
    dsimp [HamiltonIveyReaction.scalarReaction] at hreaction
    nlinarith [hsumEigenSquares]
  rw [hderivativeValue] at hcontract
  exact hcontract

theorem HamiltonIveyCurvatureEvolutionCertificate.scalarTraceVelocity_of_traceLaplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (c : HamiltonIveyCurvatureEvolutionCertificate
      g cov hcov hLevi hdim t x)
    (hTraceLaplacian :
      g.HamiltonIveyTraceLaplacianAt cov hcov hLevi hdim t x) :
    RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (curvatureTensorVelocityRicci c.curvatureVelocity x) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let ricciVelocity := curvatureTensorVelocityRicci c.curvatureVelocity
  have hRicci := hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
    g cov hcov hLevi c.curvatureVelocity c.hCurvature
  have hscalarFromRicci := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := x) ricciVelocity hRicci
  have hscalarFromOperator := hasDerivAt_scalarCurvature_of_curvatureOperatorEvolution
    g cov hcov hLevi hdim gdot s hflow ht x c.hEvolution hTraceLaplacian
  have hderivativesAgree := hscalarFromRicci.unique hscalarFromOperator
  have hderivativesAgree' :
      2 * g.ricciNormSq cov hcov t x +
          RicciFlow.metricTraceAt (I := I) (M := M) g t x
            (curvatureTensorVelocityRicci c.curvatureVelocity x) =
        (cov t).scalarLaplacian (g.scalarCurvature cov hcov t) x +
          2 * g.ricciNormSq cov hcov t x := by
    simpa [ricciVelocity, TimeDependentRiemannianMetric.scalarLaplacian]
      using hderivativesAgree
  have htrace :
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (curvatureTensorVelocityRicci c.curvatureVelocity x) =
        (cov t).scalarLaplacian (g.scalarCurvature cov hcov t) x := by
    linarith [hderivativesAgree']
  simpa [TimeDependentRiemannianMetric.scalarLaplacian] using htrace

/-! A bundled curvature-evolution certificate feeds the pointwise support
derivative directly.  This is deliberately a reduction theorem: the
certificate still records the genuine curvature-evolution equation that a
Ricci-flow proof must establish. -/

theorem HamiltonIveyCurvatureEvolutionCertificate.support_derivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (c : HamiltonIveyCurvatureEvolutionCertificate
      g cov hcov hLevi hdim t x) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t x (τ, x))
      (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x) t := by
  exact g.hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureTensorConnectionLaplacianEvolution
    cov hcov hLevi hdim gdot s hflow ht x c.curvatureVelocity c.hCurvature
      c.hEvolution

/-! The support speed can therefore be obtained from a single intrinsic
Ricci-tensor derivative.  This theorem is intentionally stated in terms of
the already-proved support-speed calculation, so the logarithmic chain rule
and the Rayleigh support evolution remain in one audited location. -/

theorem hasDerivAt_hamiltonIveySupportedDefect_time_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {K t₀ : ℝ} (hK : 0 < K) {x₀ : M} (ht₀ : t₀ ∈ s)
    (ht₀_nonneg : 0 ≤ t₀)
    (hnu : g.curvatureNu cov hcov hLevi hdim t₀ x₀ < 0)
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t₀) :
    HasDerivAt
      (fun τ => g.hamiltonIveySupportedDefect
        cov hcov hLevi hdim K t₀ x₀ (τ, x₀))
      ((2 * g.ricciNormSq cov hcov t₀ x₀ +
          RicciFlow.metricTraceAt (I := I) (M := M) g t₀ x₀
            (ricciVelocity x₀)) /
          (-g.curvatureNu cov hcov hLevi hdim t₀ x₀) +
        (g.scalarCurvature cov hcov t₀ x₀ -
            g.curvatureNu cov hcov hLevi hdim t₀ x₀) /
          (g.curvatureNu cov hcov hLevi hdim t₀ x₀) ^ 2 *
          ((2 * g.ricciNormSq cov hcov t₀ x₀ +
              RicciFlow.metricTraceAt (I := I) (M := M) g t₀ x₀
                (ricciVelocity x₀)) -
            2 * (ricciVelocity x₀
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)) -
            (g.curvatureLambda cov hcov hLevi hdim t₀ x₀ +
              g.curvatureMu cov hcov hLevi hdim t₀ x₀) ^ 2) -
        K / (1 + K * t₀)) t₀ := by
  let v : TM x₀ := g.curvatureNuContactVectorField
    cov hcov hLevi hdim t₀ x₀ x₀
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t₀ x₀ +
      RicciFlow.metricTraceAt (I := I) (M := M) g t₀ x₀
        (ricciVelocity x₀)
  let contactRicciVelocity : ℝ := ricciVelocity x₀ v v
  have hscalar := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht₀ (x := x₀) ricciVelocity hRicci
  have hricci := g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi x₀ v v ricciVelocity hRicci
  have hs := g.hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
    cov hcov hLevi hdim gdot s hflow hK ht₀ ht₀_nonneg hnu
      scalarVelocity contactRicciVelocity hscalar hricci
  simpa [v, scalarVelocity, contactRicciVelocity] using hs

/-! The contact certificate can now expose one intrinsic Ricci derivative
instead of unrelated scalar and coordinate Ricci speeds.  The remaining
spatial support and PDE clauses are retained verbatim, since those are the
separate curvature-evolution obligations rather than time-variation data. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_support_certificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ,
        RicciFlow.HasIntrinsicRicciTimeDerivativeAt
          (I := I) (M := M) g ricciVelocity t ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          0 < g.scalarCurvature cov hcov p.1 p.2 -
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ y in 𝓝 x,
          MDiffAt
            (fun z : M =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M =>
                g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x ∧
        g.scalarLaplacian cov
            (fun _ y =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
          ricciVelocity) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  apply g.hamiltonIveyPinching_of_ricciFlow_support_certificate
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hscalar hcont
  intro t x ht hdefect
  obtain ⟨ricciVelocity, hRicci, hupper, hneg, hscalarSupport,
    hnear, hdiff, hpde⟩ := hcontact ht hdefect
  let v : TM x := g.curvatureNuContactVectorField
    cov hcov hLevi hdim t x x
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x (ricciVelocity x)
  let contactRicciVelocity : ℝ := ricciVelocity x v v
  have hscalarTime :=
    g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi gdot (Icc 0 T) hflow ht (x := x) ricciVelocity hRicci
  have hricciTime :=
    g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi x v v ricciVelocity hRicci
  refine ⟨scalarVelocity, contactRicciVelocity, hscalarTime, hricciTime,
    hupper, hneg, hscalarSupport, hnear, hdiff, ?_⟩
  simpa [hamiltonIveyIntrinsicSupportSpeed, scalarVelocity,
    contactRicciVelocity, v] using hpde

/-! Finally, the scalar lower barrier can be fed from the same intrinsic
Ricci-time derivative.  The only additional geometric datum is the trace
identity `tr_g(Ric') = ΔR`; this is precisely the contracted-Bianchi/curvature
evolution bridge and is kept explicit rather than replaced by an arbitrary
scalar time derivative. -/

theorem scalarCurvature_hamiltonIvey_lowerBarrier_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 ≤ K)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t)
    (htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x := by
  have hScalarInitial : ∀ x : M,
      -(3 : ℝ) * K ≤ g.scalarCurvature cov hcov 0 x := by
    intro x
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim 0 x
    have hthreeNu :
        3 * g.curvatureNu cov hcov hLevi hdim 0 x ≤
          g.curvatureLambda cov hcov hLevi hdim 0 x +
            g.curvatureMu cov hcov hLevi hdim 0 x +
            g.curvatureNu cov hcov hLevi hdim 0 x := by
      linarith
    rw [hsum] at hthreeNu
    linarith [hnuLower x]
  have hScalarTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t := by
    intro t ht x
    have h := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi gdot (Icc 0 T) hflow ht (x := x)
        (ricciVelocity t) (hRicci ht)
    have htr := htrace t ht x
    convert h using 1
    rw [htr]
    ring
  have hScalarStrong := g.scalarCurvature_lowerBarrier_of_evolution
    cov hcov hdim hK hScalarCont hScalarTime hScalarNear
      hScalarDifferential hScalarInitial
  intro t ht x
  have hden₁ : 0 < 1 + (K : ℝ) * t := by
    nlinarith [mul_nonneg hK ht.1]
  have hden₂ : 0 < 1 + 2 * (K : ℝ) * t := by
    nlinarith [mul_nonneg hK ht.1]
  have hcompare :
      -3 * (K / (1 + K * t)) ≤
        -(3 : ℝ) * K / (1 + 2 * K * t) := by
    calc
      -3 * (K / (1 + K * t)) =
          (-(3 : ℝ) * K) / (1 + K * t) := by ring
      _ ≤ (-(3 : ℝ) * K) / (1 + 2 * K * t) := by
        rw [div_le_div_iff₀ hden₁ hden₂]
        nlinarith [mul_nonneg (sq_nonneg K) ht.1]
  exact hcompare.trans (hScalarStrong t ht x)

/-- The scalar lower-barrier argument needs only the scalar PDE itself.  This
interface is useful when that PDE has been derived directly by tracing the
actual curvature-operator evolution, with no separate Ricci-velocity
certificate. -/
theorem scalarCurvature_hamiltonIvey_lowerBarrier_of_scalarEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 ≤ K)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (hScalarTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x := by
  have hScalarInitial : ∀ x : M,
      -(3 : ℝ) * K ≤ g.scalarCurvature cov hcov 0 x := by
    intro x
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim 0 x
    have hthreeNu :
        3 * g.curvatureNu cov hcov hLevi hdim 0 x ≤
          g.curvatureLambda cov hcov hLevi hdim 0 x +
            g.curvatureMu cov hcov hLevi hdim 0 x +
            g.curvatureNu cov hcov hLevi hdim 0 x := by
      linarith
    rw [hsum] at hthreeNu
    linarith [hnuLower x]
  have hScalarStrong := g.scalarCurvature_lowerBarrier_of_evolution
    cov hcov hdim hK hScalarCont hScalarTime hScalarNear
      hScalarDifferential hScalarInitial
  intro t ht x
  have hden₁ : 0 < 1 + (K : ℝ) * t := by
    nlinarith [mul_nonneg hK ht.1]
  have hden₂ : 0 < 1 + 2 * (K : ℝ) * t := by
    nlinarith [mul_nonneg hK ht.1]
  have hcompare :
      -3 * (K / (1 + K * t)) ≤
        -(3 : ℝ) * K / (1 + 2 * K * t) := by
    calc
      -3 * (K / (1 + K * t)) =
          (-(3 : ℝ) * K) / (1 + K * t) := by ring
      _ ≤ (-(3 : ℝ) * K) / (1 + 2 * K * t) := by
        rw [div_le_div_iff₀ hden₁ hden₂]
        nlinarith [mul_nonneg (sq_nonneg K) ht.1]
  exact hcompare.trans (hScalarStrong t ht x)

/-! A single capstone now combines the intrinsic scalar barrier, the
intrinsic contact derivative, and the support maximum principle. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_trace_certificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t)
    (htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ ricciVelocity' : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ,
        RicciFlow.HasIntrinsicRicciTimeDerivativeAt
          (I := I) (M := M) g ricciVelocity' t ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          0 < g.scalarCurvature cov hcov p.1 p.2 -
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ y in 𝓝 x,
          MDiffAt
            (fun z : M =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M =>
                g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x ∧
        g.scalarLaplacian cov
            (fun _ y =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
          ricciVelocity') :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hscalar := g.scalarCurvature_hamiltonIvey_lowerBarrier_of_intrinsicRicciTimeDerivative
    cov hcov hLevi hdim gdot hK.le hflow hnuLower hScalarCont hScalarNear
      hScalarDifferential ricciVelocity hRicci htrace
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_support_certificate
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hscalar hcont hcontact

/-! This capstone no longer asks for the Ricci time-derivative field or its
scalar trace identity as independent inputs.  They are constructed pointwise
from the full curvature-evolution certificates.  The trace/Laplacian bridge
is now derived from explicit differentiability data for the genuine shifted
curvature tensor, rather than supplied as the target equality. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolutionCertificates
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x)
    (hShiftedTensorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyShiftedTensorTraceRegularity
        cov hcov hLevi hdim t x)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ ricciVelocity' : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ,
        RicciFlow.HasIntrinsicRicciTimeDerivativeAt
          (I := I) (M := M) g ricciVelocity' t ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          0 < g.scalarCurvature cov hcov p.1 p.2 -
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ y in 𝓝 x,
          MDiffAt
            (fun z : M =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M =>
                g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x ∧
        g.scalarLaplacian cov
            (fun _ y =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
          ricciVelocity') :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y := by
    intro t ht x
    exact Filter.Eventually.of_forall (fun y =>
      (g.scalarRegularity_of_shiftedTensorRegularity cov hcov hLevi hdim t y
        (hShiftedTensorRegularity t ht y)).1)
  have hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x := by
    intro t ht x
    exact g.scalarDifferential_mdifferentiableAt_of_shiftedTensorRegularity
      cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
  let ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := fun t x =>
    if ht : t ∈ Icc 0 T then
      curvatureTensorVelocityRicci (evolution t ht x).curvatureVelocity x
    else 0
  have hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t := by
    intro t ht
    change ∀ y : M, ∀ u v : TM y,
      HasDerivAt
        (fun τ => RicciFlow.intrinsicRicciTensor
          (I := I) (M := M) g τ y u v)
        ((ricciVelocity t y) u v) t
    intro y u v
    have h := hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi (evolution t ht y).curvatureVelocity
      (evolution t ht y).hCurvature
    dsimp only [ricciVelocity]
    rw [dif_pos ht]
    exact h y u v
  have htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x := by
    intro t ht x
    have hTraceLaplacian :=
      g.HamiltonIveyTraceLaplacianAt_of_shiftedTensorRegularity
        cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
    have h :=
      HamiltonIveyCurvatureEvolutionCertificate.scalarTraceVelocity_of_traceLaplacian
        g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht x
        (evolution t ht x) hTraceLaplacian
    change RicciFlow.metricTraceAt (I := I) (M := M) g t x
      (if hmem : t ∈ Icc 0 T then
        curvatureTensorVelocityRicci
          (evolution t hmem x).curvatureVelocity x else 0) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x
    rw [dif_pos ht]
    exact h
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_trace_certificate
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hScalarCont
    hScalarNear hScalarDifferential ricciVelocity hRicci htrace hcont hcontact

/-! The next interface exposes the spatial contact inequality through the
actual shifted curvature tensor.  In particular, the certificate no longer
contains a free scalar Laplacian equality: it stores the explicit regularity
data consumed by the proved quotient/connection-Laplacian bridge.  The only
remaining contact inequality is the curvature-evolution estimate itself. -/

/- The regularity structure is defined next to the bridge theorem in
HamiltonIveySupportLaplacian.lean, where its dependent bundle instances are
elaborated in the same context as the bridge. -/
theorem HamiltonIveySupportLaplacianCertificate.eq_connectionLaplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K : ℝ) (t₀ : ℝ) (x₀ : M)
    (c : HamiltonIveySupportLaplacianCertificate
      g cov hcov hLevi hdim t₀ x₀) :
    g.scalarLaplacian cov
        (fun _ y => g.curvatureNuSpacetimeSupport
          cov hcov hLevi hdim t₀ x₀ (t₀, y)) t₀ x₀ =
      g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t₀ x₀ := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  letI : ∀ x : M, NormedAddCommGroup (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ x : M, NormedAddCommGroup (T₂ x) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
  simpa [hamiltonIveyContactCurvatureLaplacian] using
    g.scalarLaplacian_curvatureNuSpacetimeSupport_eq_connectionLaplacian
      cov hcov hLevi hdim t₀ x₀ c.U c.hU c.hx₀ c.hden c.hq c.hd c.ha
      c.hDq c.hDd c.hDa c.hh c.hV c.hfirst c.hdf c.hsecondV

structure HamiltonIveyCurvatureContactCertificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) where
  ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ
  hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
    (I := I) (M := M) g ricciVelocity t
  hupper : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hneg : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0
  hscalarSupport : ∀ᶠ p in 𝓝 (t, x),
    0 < g.scalarCurvature cov hcov p.1 p.2 -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hnear : ∀ᶠ y in 𝓝 x,
    MDiffAt
      (fun z : M =>
        g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y
  hdiff : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (CovariantDerivative.scalarDifferential (I := I)
        (fun z : M =>
          g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x
  hSupport : HamiltonIveySupportLaplacianCertificate
    g cov hcov hLevi hdim t x
  /-- The curvature-evolution contact estimate, expressed through the
  genuine connection Laplacian of the shifted curvature tensor. -/
  hCurvatureEvolution :
    g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
      g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
        ricciVelocity
  /-- The scalar supported-defect inequality consumed by the maximum
  principle.  Its derivation from `hCurvatureEvolution` is the remaining
  chain-rule/evolution bridge, so it is recorded explicitly rather than
  silently identifying two different Laplacians. -/
  hEvolution :
    g.scalarLaplacian cov
        (fun _ y => g.hamiltonIveySupportedDefect
          cov hcov hLevi hdim K t x (t, y)) t x +
        g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
          ricciVelocity

/-! The compact maximum-principle argument only evaluates the supported-defect
PDE at the spatial minimum selected on the first negative time slab.  This
variant records that exact scope while retaining the genuine curvature and
connection-Laplacian data above.  In particular, it does not turn the
minimum-scoped inequality into a pointwise assumption at every bad contact. -/

structure HamiltonIveyCurvatureContactCertificateAtSpatialMinimum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) where
  ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ
  hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
    (I := I) (M := M) g ricciVelocity t
  hupper : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hneg : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0
  hscalarSupport : ∀ᶠ p in 𝓝 (t, x),
    0 < g.scalarCurvature cov hcov p.1 p.2 -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hnear : ∀ᶠ y in 𝓝 x,
    MDiffAt
      (fun z : M =>
        g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y
  hdiff : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (CovariantDerivative.scalarDifferential (I := I)
        (fun z : M =>
          g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x
  hSupport : HamiltonIveySupportLaplacianCertificate
    g cov hcov hLevi hdim t x
  /-- The actual contact evaluation of the curvature-operator evolution
  equation.  Unlike the scalar defect inequality below, this is a geometric
  evolution identity for the genuine raised curvature tensor. -/
  hCurvatureOperatorEvolution :
    curvatureOperatorTwoTensorVelocity g cov hcov t ricciVelocity x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)

/-- Assemble minimum-contact data from an actual full curvature-evolution
certificate and the independent support regularity/bounds.  No scalar
supported-defect inequality is an input; the contact velocity is derived from
the geometric curvature evolution above. -/
def HamiltonIveyCurvatureContactCertificateAtSpatialMinimum.of_curvatureEvolutionCertificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) {K : ℝ} {x : M}
    (hupper : ∀ᶠ p in 𝓝 (t, x),
      g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p)
    (hneg : ∀ᶠ p in 𝓝 (t, x),
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0)
    (hscalarSupport : ∀ᶠ p in 𝓝 (t, x),
      0 < g.scalarCurvature cov hcov p.1 p.2 -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p)
    (hnear : ∀ᶠ y in 𝓝 x,
      MDiffAt
        (fun z : M =>
          g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)
    (hdiff : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I)
          (fun z : M =>
            g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x)
    (hSupport : HamiltonIveySupportLaplacianCertificate
      g cov hcov hLevi hdim t x)
    (evolution : HamiltonIveyCurvatureEvolutionCertificate
      g cov hcov hLevi hdim t x) :
    HamiltonIveyCurvatureContactCertificateAtSpatialMinimum
      g cov hcov hLevi hdim K t x := by
  refine ⟨curvatureTensorVelocityRicci evolution.curvatureVelocity,
    hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi evolution.curvatureVelocity evolution.hCurvature,
    hupper, hneg, hscalarSupport, hnear, hdiff, hSupport, ?_⟩
  exact HamiltonIveyCurvatureEvolutionCertificate.contactOperatorVelocity
    g cov hcov hLevi hdim gdot s hflow ht x evolution

/-- Contact-local analytic data for the smooth Rayleigh support and its
supported defect.  Curvature evolution and the induced Ricci time derivative
are intentionally absent: those are constructed from the full evolution
certificate by the capstone below. -/
structure HamiltonIveySupportContactData
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) where
  hupper : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hneg : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0
  hscalarSupport : ∀ᶠ p in 𝓝 (t, x),
    0 < g.scalarCurvature cov hcov p.1 p.2 -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hnear : ∀ᶠ y in 𝓝 x,
    MDiffAt (fun z : M =>
      g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y
  hdiff : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (CovariantDerivative.scalarDifferential (I := I)
        (fun z : M =>
          g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x
  hSupport : HamiltonIveySupportLaplacianCertificate
    g cov hcov hLevi hdim t x

/-- Build the local support/sign portion of a contact certificate from the
actual Rayleigh quotient and continuity.  The upper support is the least
eigenvalue comparison proved for positive metric square, negativity follows
from contact equality, and scalar-minus-support positivity follows from the
scalar barrier and negative Hamilton--Ivey defect.  Thus none of these three
neighborhood statements is an independent premise of the capstone. -/
def HamiltonIveySupportContactData.of_bad_contact_and_continuity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K t : ℝ} (hK : 0 < K) (ht : 0 ≤ t) (x : M)
    (hnu : g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hdefect : g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0)
    (hscalar : -3 * (K / (1 + K * t)) ≤
      g.scalarCurvature cov hcov t x)
    (hnormContinuous : ContinuousAt
      (fun p : ℝ × M => (g p.1).inner p.2
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x p.2)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x p.2))
      (t, x))
    (hScalarContinuous : ContinuousAt
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2) (t, x))
    (hSupportContinuous : ContinuousAt
      (g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x) (t, x))
    (hScalarNear : ∀ᶠ y in 𝓝 x,
      MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I)
          (g.scalarCurvature cov hcov t) y)) x)
    (hSupport : HamiltonIveySupportLaplacianCertificate
      g cov hcov hLevi hdim t x) :
    HamiltonIveySupportContactData g cov hcov hLevi hdim K t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  let R : M → ℝ := g.scalarCurvature cov hcov t
  let q : M → ℝ := fun y =>
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x (t, y)
  let a : M → ℝ := fun y => 1 / (-q y)
  let b : M → ℝ := fun y => (R y - q y) / q y ^ 2
  let dR : ∀ y : M, T₁ y :=
    fun y => CovariantDerivative.scalarDifferential (I := I) R y
  let dq : ∀ y : M, T₁ y :=
    fun y => CovariantDerivative.scalarDifferential (I := I) q y
  let profile : M → ℝ := fun y => HamiltonIveyReaction.nuProfile (R y) (q y)
  let offset : ℝ := 3 + Real.log (K / (1 + K * t))
  let defectSlice : M → ℝ := fun y =>
    g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)
  have hq : ∀ᶠ y in 𝓝 x, MDiffAt q y := by
    simpa [q] using hSupport.hq
  have hqAt : q x = g.curvatureNu cov hcov hLevi hdim t x := by
    simpa [q] using
      g.curvatureNuSpacetimeSupport_eq_at_contact cov hcov hLevi hdim t x
  have hq0 : q x ≠ 0 := by
    rw [hqAt]
    exact hnu.ne
  have hq0near : ∀ᶠ y in 𝓝 x, q y ≠ 0 :=
    (hq.self_of_nhds).continuousAt.eventually_ne hq0
  have hRnear : ∀ᶠ y in 𝓝 x, MDiffAt R y := by
    simpa [R] using hScalarNear
  have hprofileNear : ∀ᶠ y in 𝓝 x, MDiffAt profile y := by
    filter_upwards [hRnear, hq, hq0near] with y hRy hqy hq0y
    exact mdifferentiableAt_nuProfile hRy hqy hq0y
  have hprofilePlus : defectSlice = profile + (fun _ : M => offset) := by
    funext y
    simp [defectSlice, profile, offset, R, q,
      hamiltonIveySupportedDefect, HamiltonIveyReaction.nuProfile]
    ring
  have hnear : ∀ᶠ y in 𝓝 x, MDiffAt defectSlice y := by
    filter_upwards [hprofileNear] with y hpy
    rw [hprofilePlus]
    exact hpy.add mdifferentiableAt_const
  have hR : MDiffAt R x := hRnear.self_of_nhds
  have ha : MDiffAt a x := by
    dsimp [a]
    exact (mdifferentiableAt_const : MDiffAt (fun _ : M => (1 : ℝ)) x).div
      (hq.self_of_nhds).neg (neg_ne_zero.mpr hq0)
  have hb : MDiffAt b x := by
    dsimp [b]
    exact (hR.sub (hq.self_of_nhds)).div
      ((hq.self_of_nhds).pow 2) (pow_ne_zero 2 hq0)
  have hdR : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (dR y)) x := by
    simpa [dR, R] using hScalarDifferential
  have hdq : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (dq y)) x := by
    simpa [dq, q] using hSupport.hDq
  have hcombo : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (a y • dR y + b y • dq y)) x := by
    exact mdifferentiableAt_add_section
      (ha.smul_section hdR) (hb.smul_section hdq)
  have hdiffFormula : ∀ᶠ y in 𝓝 x,
      CovariantDerivative.scalarDifferential (I := I) defectSlice y =
        a y • dR y + b y • dq y := by
    filter_upwards [hRnear, hq, hq0near] with y hRy hqy hq0y
    have hprof : MDiffAt profile y :=
      mdifferentiableAt_nuProfile hRy hqy hq0y
    have hconst : MDiffAt (fun _ : M => offset) y := mdifferentiableAt_const
    have hconstDifferential :
        CovariantDerivative.scalarDifferential (I := I)
          (fun _ : M => offset) y = 0 := by
      ext u
      simp only [CovariantDerivative.scalarDifferential_apply]
      rw [mvfderiv_const]
    calc
      CovariantDerivative.scalarDifferential (I := I) defectSlice y =
          CovariantDerivative.scalarDifferential (I := I) profile y +
            CovariantDerivative.scalarDifferential (I := I)
              (fun _ : M => offset) y := by
        rw [hprofilePlus]
        ext u
        simp only [CovariantDerivative.scalarDifferential_apply]
        rw [mvfderiv_add hprof hconst]
        simp [mvfderiv_const]
      _ = a y • dR y + b y • dq y := by
        rw [hconstDifferential,
          scalarDifferential_nuProfile hRy hqy hq0y]
        simp [a, b, dR, dq, R, q]
  have hdiffSections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I) defectSlice y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (a y • dR y + b y • dq y)) := by
    filter_upwards [hdiffFormula] with y hy
    rw [hy]
  have hdiff := hcombo.congr_of_eventuallyEq hdiffSections
  have hupper := g.curvatureNu_le_spacetimeSupport_eventually
    cov hcov hLevi hdim t x hnormContinuous
  have hSupportNegAt :
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x (t, x) < 0 := by
    rw [g.curvatureNuSpacetimeSupport_eq_at_contact
      cov hcov hLevi hdim t x]
    exact hnu
  have hneg : ∀ᶠ p in 𝓝 (t, x),
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0 :=
    hSupportContinuous.eventually (isOpen_Iio.mem_nhds hSupportNegAt)
  have hScalarSupportAt :=
    g.scalarCurvature_sub_spacetimeSupport_pos_at_bad_contact
      cov hcov hLevi hdim hK ht x hnu hscalar hdefect
  have hscalarSupport : ∀ᶠ p in 𝓝 (t, x),
      0 < g.scalarCurvature cov hcov p.1 p.2 -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p :=
    (hScalarContinuous.sub hSupportContinuous).eventually
      (isOpen_Ioi.mem_nhds hScalarSupportAt)
  exact ⟨hupper, hneg, hscalarSupport,
    (by
      filter_upwards [hnear] with y hy
      simpa [defectSlice] using hy),
    (by
      simpa [defectSlice] using hdiff), hSupport⟩

/-- The irreducible contact-local regularity input for the Hamilton--Ivey
support argument.  The eigenvalue comparison, sign neighborhoods, supported
defect differentiability, and scalar-minus-support positivity are derived by
`HamiltonIveySupportContactData.of_bad_contact_and_continuity`; only genuine
continuity and the second-order Rayleigh-support certificate remain here. -/
structure HamiltonIveySupportContactRegularityData
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) where
  hnormContinuous : ContinuousAt
    (fun p : ℝ × M => (g p.1).inner p.2
      (g.curvatureNuContactVectorField cov hcov hLevi hdim t x p.2)
      (g.curvatureNuContactVectorField cov hcov hLevi hdim t x p.2)) (t, x)
  hScalarContinuous : ContinuousAt
    (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2) (t, x)
  hSupportContinuous : ContinuousAt
    (g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x) (t, x)
  hSupport : HamiltonIveySupportLaplacianCertificate
    g cov hcov hLevi hdim t x

/-- At a spatial minimum of the supported defect, the scalar-curvature and
Rayleigh-support differentials satisfy the exact Hamilton--Ivey profile
relation.  The support is the genuine smooth Rayleigh quotient from the
certificate; the only extra regularity passed here is that of actual scalar
curvature. -/
theorem HamiltonIveyCurvatureContactCertificateAtSpatialMinimum.scalarGradient_relation
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K t : ℝ} {x : M}
    (c : HamiltonIveyCurvatureContactCertificateAtSpatialMinimum
      g cov hcov hLevi hdim K t x)
    (hScalar : MDiffAt (g.scalarCurvature cov hcov t) x)
    (hmin : IsLocalMin
      (fun y : M => g.hamiltonIveySupportedDefect
        cov hcov hLevi hdim K t x (t, y)) x) :
    CovariantDerivative.scalarDifferential (I := I)
        (g.scalarCurvature cov hcov t) x =
      ((g.scalarCurvature cov hcov t x -
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x (t, x)) /
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x (t, x)) •
        CovariantDerivative.scalarDifferential (I := I)
          (fun y => g.curvatureNuSpacetimeSupport
            cov hcov hLevi hdim t x (t, y)) x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  let R : M → ℝ := g.scalarCurvature cov hcov t
  let q : M → ℝ := fun y => g.curvatureNuSpacetimeSupport
    cov hcov hLevi hdim t x (t, y)
  let C : ℝ := 3 + Real.log (K / (1 + K * t))
  have hq : MDiffAt q x := by
    simpa [q] using (c.hSupport.hq).self_of_nhds
  have hqneg : q x < 0 := by
    simpa [q] using c.hneg.self_of_nhds
  have hminProfile : IsLocalMin
      (fun y => HamiltonIveyReaction.nuProfile (R y) (q y) + C) x := by
    rw [IsLocalMin, IsMinFilter] at hmin ⊢
    filter_upwards [hmin] with y hy
    dsimp [hamiltonIveySupportedDefect, R, q, C] at hy ⊢
    linarith
  have hgradient :=
    scalarDifferential_scalar_eq_of_isLocalMin_nuProfile_add_const
      (R := R) (q := q) hScalar hq hqneg.ne hminProfile
  simpa [R, q] using hgradient

/-- Derive the scalar supported-defect inequality at a spatial minimum from
the actual contact curvature-operator evolution equation.  The profile
Laplacian chain rule and critical-point gradient relation are used explicitly;
the nonpositive gradient correction is not assumed. -/
theorem HamiltonIveyCurvatureContactCertificateAtSpatialMinimum.evolution_at_spatial_minimum_of_curvatureOperatorEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K t : ℝ} {x : M}
    (c : HamiltonIveyCurvatureContactCertificateAtSpatialMinimum
      g cov hcov hLevi hdim K t x)
    (hScalarNear : ∀ᶠ y in 𝓝 x,
      MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential
          (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (htrace : RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (c.ricciVelocity x) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x)
    (hmin : IsLocalMin
      (fun y : M => g.hamiltonIveySupportedDefect
        cov hcov hLevi hdim K t x (t, y)) x) :
    g.scalarLaplacian cov
        (fun _ y => g.hamiltonIveySupportedDefect
          cov hcov hLevi hdim K t x (t, y)) t x +
      g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
    g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
      c.ricciVelocity := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  let R : M → ℝ := g.scalarCurvature cov hcov t
  let q : M → ℝ := fun y =>
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x (t, y)
  let profile : M → ℝ := fun y => HamiltonIveyReaction.nuProfile (R y) (q y)
  let defectSlice : M → ℝ := fun y =>
    g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)
  let C : ℝ := 3 + Real.log (K / (1 + K * t))
  let lam : ℝ := g.curvatureLambda cov hcov hLevi hdim t x
  let mu : ℝ := g.curvatureMu cov hcov hLevi hdim t x
  let nu : ℝ := g.curvatureNu cov hcov hLevi hdim t x
  let v : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  let L : ℝ := g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x (c.ricciVelocity x)
  let contactRicciVelocity : ℝ := c.ricciVelocity x v v
  have hR : MDiffAt R x := hScalarNear.self_of_nhds
  have hq : MDiffAt q x := by
    simpa [q] using (c.hSupport.hq).self_of_nhds
  have hqneg : q x < 0 := by
    simpa [q] using c.hneg.self_of_nhds
  have hq0 : q x ≠ 0 := hqneg.ne
  have hqContact : q x = nu := by
    simpa [q, nu] using
      g.curvatureNuSpacetimeSupport_eq_at_contact
        cov hcov hLevi hdim t x
  have hnu0 : nu ≠ 0 := by
    rw [← hqContact]
    exact hq0
  have hnu0' : g.curvatureNu cov hcov hLevi hdim t x ≠ 0 := by
    simpa [nu] using hnu0
  have hq0near : ∀ᶠ y in 𝓝 x, q y ≠ 0 :=
    hq.continuousAt.eventually_ne hq0
  have hqnear : ∀ᶠ y in 𝓝 x, MDiffAt q y :=
    c.hSupport.hq
  have hprofileNear : ∀ᶠ y in 𝓝 x, MDiffAt (profile) y := by
    filter_upwards [hScalarNear, hqnear, hq0near] with y hRy hqy hq0y
    exact mdifferentiableAt_nuProfile hRy hqy hq0y
  have hprofilePlus : defectSlice = profile + (fun _ : M => C) := by
    funext y
    dsimp [defectSlice, profile, R, q, C, hamiltonIveySupportedDefect]
    ring
  have hminProfile : IsLocalMin profile x := by
    rw [IsLocalMin, IsMinFilter] at hmin ⊢
    filter_upwards [hmin] with y hy
    dsimp [defectSlice, profile, R, q, C,
      hamiltonIveySupportedDefect] at hy ⊢
    linarith
  have hprofileDiffEq : ∀ᶠ y in 𝓝 x,
      CovariantDerivative.scalarDifferential (I := I) defectSlice y =
        CovariantDerivative.scalarDifferential (I := I) profile y := by
    filter_upwards [hprofileNear] with y hpy
    ext u
    change mvfderiv (I := I) defectSlice y u =
      mvfderiv (I := I) profile y u
    rw [hprofilePlus]
    rw [mvfderiv_add (I := I) hpy mdifferentiableAt_const]
    rw [mvfderiv_const]
    simp
  have hprofileSections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I) profile y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I) defectSlice y)) := by
    filter_upwards [hprofileDiffEq] with y hy
    rw [hy.symm]
  have hprofileDiff : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (CovariantDerivative.scalarDifferential (I := I) profile y)) x :=
    c.hdiff.congr_of_eventuallyEq hprofileSections
  have hLapDefect :
      CovariantDerivative.scalarLaplacian (cov t) defectSlice x =
        CovariantDerivative.scalarLaplacian (cov t) profile x := by
    rw [hprofilePlus]
    exact CovariantDerivative.scalarLaplacian_add_const_of_eventually_mdifferentiableAt
      (cov t) C hprofileNear hprofileDiff
  have hprofileLap :=
    scalarLaplacian_nuProfile_eq_of_isLocalMin
      (I := I) (M := M) (cov t) hScalarNear hqnear hScalarDifferential
      c.hSupport.hDq hR hq hq0 hq0near hminProfile
  have hsupportLap :
      CovariantDerivative.scalarLaplacian (cov t) q x = L := by
    simpa [q, L] using
      HamiltonIveySupportLaplacianCertificate.eq_connectionLaplacian
        g cov hcov hLevi hdim K t x c.hSupport
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x
  have hRic := g.two_mul_ricci_curvatureNuEigenvector_eq_lambda_add_mu
    cov hcov hLevi hdim t x
  have hv : v = g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
    simp [v, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hinner : (g t).inner x v v = 1 := by
    rw [hv]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hRic' :
      2 * g.ricciCurvature cov hcov t x v v = lam + mu := by
    simpa [v, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center] using hRic
  have hsum' : lam + mu + nu = R x := by
    simpa [R, lam, mu, nu] using hsum
  have hRminus : R x - nu = lam + mu := by
    linarith [hsum']
  have hprod :
      2 * (R x - nu) * g.ricciCurvature cov hcov t x v v = (lam + mu) ^ 2 := by
    calc
      2 * (R x - nu) * g.ricciCurvature cov hcov t x v v =
          (R x - nu) * (2 * g.ricciCurvature cov hcov t x v v) := by ring
      _ = (lam + mu) ^ 2 := by rw [hRic', hRminus]; ring
  have hrel :
      scalarVelocity - 2 * contactRicciVelocity - (lam + mu) ^ 2 =
        curvatureOperatorTwoTensorVelocity g cov hcov t c.ricciVelocity x v v +
          2 * nu * g.ricciCurvature cov hcov t x v v := by
    simp only [scalarVelocity, contactRicciVelocity,
      curvatureOperatorTwoTensorVelocity]
    rw [hinner]
    ring_nf
    linarith [hprod]
  have hspeed :
      g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
          c.ricciVelocity =
        scalarVelocity / (-nu) + (R x - nu) / nu ^ 2 *
          (L + nu ^ 2 + lam * mu) - K / (1 + K * t) := by
    change scalarVelocity / (-nu) + (R x - nu) / nu ^ 2 *
        (scalarVelocity - 2 * contactRicciVelocity - (lam + mu) ^ 2) -
          K / (1 + K * t) = _
    rw [hrel, c.hCurvatureOperatorEvolution]
    dsimp [L, nu, lam, mu, v]
    ring
  have htrace' : RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (c.ricciVelocity x) =
      CovariantDerivative.scalarLaplacian (cov t) R x := by
    simpa [R] using htrace
  have hscalarVelocity : scalarVelocity =
      2 * g.ricciNormSq cov hcov t x +
        CovariantDerivative.scalarLaplacian (cov t) R x := by
    dsimp [scalarVelocity]
    rw [htrace']
  have hreaction :
      2 * g.ricciNormSq cov hcov t x / (-nu) +
        (R x - nu) / nu ^ 2 * (nu ^ 2 + lam * mu) -
          K / (1 + K * t) =
        g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x := by
    rw [g.two_mul_ricciNormSq_eq_hamiltonIveyScalarReaction
      cov hcov hLevi hdim t x]
    rw [← hsum']
    simp only [hamiltonIveyReactionTerm, HamiltonIveyReaction.reaction,
      HamiltonIveyReaction.scalarReaction, HamiltonIveyReaction.scalar]
    dsimp [lam, mu, nu]
    field_simp [hnu0']
    ring
  let gradSq : ℝ := ∑ i : Fin (Module.finrank ℝ (TM x)),
    (CovariantDerivative.scalarDifferential (I := I) q x
      (stdOrthonormalBasis ℝ (TM x) i)) ^ 2
  have hprofileLap' :
      CovariantDerivative.scalarLaplacian (cov t) profile x =
        (1 / (-q x)) *
            CovariantDerivative.scalarLaplacian (cov t) R x +
          ((R x - q x) / q x ^ 2) *
            CovariantDerivative.scalarLaplacian (cov t) q x -
          (1 / q x ^ 2) * gradSq := by
    simpa [profile, gradSq, R, q] using hprofileLap
  have hprofileSpeed :
      CovariantDerivative.scalarLaplacian (cov t) defectSlice x +
        g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x +
        (1 / nu ^ 2) * gradSq =
      g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
        c.ricciVelocity := by
    rw [hLapDefect, hprofileLap', hsupportLap, hspeed, hscalarVelocity,
      hqContact, ← hreaction]
    field_simp [hnu0]
    ring
  have hgradSq : 0 ≤ gradSq := by
    dsimp [gradSq]
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hcorrection : 0 ≤ (1 / nu ^ 2) * gradSq :=
    mul_nonneg (div_nonneg (by norm_num) (sq_nonneg nu)) hgradSq
  have hineq :
      CovariantDerivative.scalarLaplacian (cov t) defectSlice x +
        g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
      g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
        c.ricciVelocity := by
    linarith [hprofileSpeed, hcorrection]
  simpa [defectSlice] using hineq

/-! The structured certificate is directly consumable by the capstone above.
This is the exact reduction from the geometric connection-Laplacian contact
inequality to the scalar supported-defect inequality required by the compact
maximum principle. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvature_contact_certificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t)
    (htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveyCurvatureContactCertificate
        g cov hcov hLevi hdim K t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  apply g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_trace_certificate
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hScalarCont
    hScalarNear hScalarDifferential ricciVelocity hRicci htrace hcont
  intro t x ht hdefect
  let c := hcontact ht hdefect
  refine ⟨c.ricciVelocity, c.hRicci, c.hupper, c.hneg, c.hscalarSupport,
    c.hnear, c.hdiff, ?_⟩
  exact c.hEvolution

/-! The minimum-scoped contact certificate feeds the corresponding compact
maximum principle without strengthening its PDE hypothesis.  The time
derivative is still constructed from the intrinsic Ricci derivative, while
the spatial inequality is requested only for the local minimum produced by
the slab argument. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvature_contact_certificate_at_spatial_minimum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t)
    (htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveyCurvatureContactCertificateAtSpatialMinimum
        g cov hcov hLevi hdim K t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hscalar := g.scalarCurvature_hamiltonIvey_lowerBarrier_of_intrinsicRicciTimeDerivative
    cov hcov hLevi hdim gdot hK.le hflow hnuLower hScalarCont hScalarNear
      hScalarDifferential ricciVelocity hRicci htrace
  apply g.hamiltonIveyPinching_of_spacetime_support_certificate_at_spatial_minimum
    cov hcov hLevi hdim hK hT hnuNeg hnuLower hscalar hcont
  intro t x ht hdefect
  let c := hcontact ht hdefect
  have hvelocityEq : c.ricciVelocity x = ricciVelocity t x := by
    ext u v
    exact (c.hRicci x u v).unique (hRicci ht x u v)
  have htraceC := htrace t ht x
  rw [← hvelocityEq] at htraceC
  let v : TM x := g.curvatureNuContactVectorField
    cov hcov hLevi hdim t x x
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (c.ricciVelocity x)
  let contactRicciVelocity : ℝ := c.ricciVelocity x v v
  have hscalarTime :=
    g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi gdot (Icc 0 T) hflow ht (x := x)
        c.ricciVelocity c.hRicci
  have hricciTime :=
    g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi x v v c.ricciVelocity c.hRicci
  have hs := g.hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
    cov hcov hLevi hdim gdot (Icc 0 T) hflow hK ht ht.1
      (hnuNeg t ht x) scalarVelocity contactRicciVelocity hscalarTime hricciTime
  refine ⟨fun p => g.hamiltonIveySupportedDefect
      cov hcov hLevi hdim K t x p,
    g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
      c.ricciVelocity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact g.hamiltonIveySupportedDefect_eq_at_contact
      cov hcov hLevi hdim K t x
  · filter_upwards [c.hupper, c.hneg, c.hscalarSupport] with p hpupper hpneg hppos
    exact g.hamiltonIveyDefect_le_supportedDefect
      cov hcov hLevi hdim K t x p hpupper hpneg hppos
  · simpa [hamiltonIveyIntrinsicSupportSpeed, scalarVelocity,
      contactRicciVelocity, v] using hs
  · exact c.hnear
  · exact c.hdiff
  · intro hmin
    exact HamiltonIveyCurvatureContactCertificateAtSpatialMinimum.evolution_at_spatial_minimum_of_curvatureOperatorEvolution
      g cov hcov hLevi hdim c (hScalarNear t ht x)
      (hScalarDifferential t ht x) htraceC hmin

/-! This is the minimum-scoped capstone with the remaining contact inputs
separated cleanly: the full curvature evolution supplies both the Ricci
velocity/trace identity and contact curvature evolution, while the contact
certificate carries only Rayleigh-support regularity and sign data.  Neither
the trace/Laplacian equality nor the scalar supported-defect PDE inequality is
an input to this theorem. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_contactData_at_spatial_minimum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x)
    (hShiftedTensorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyShiftedTensorTraceRegularity
        cov hcov hLevi hdim t x)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveySupportContactRegularityData g cov hcov hLevi hdim t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := fun t x =>
    if ht : t ∈ Icc 0 T then
      curvatureTensorVelocityRicci (evolution t ht x).curvatureVelocity x
    else 0
  have hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t := by
    intro t ht
    change ∀ y : M, ∀ u v : TM y,
      HasDerivAt
        (fun τ => RicciFlow.intrinsicRicciTensor
          (I := I) (M := M) g τ y u v)
        ((ricciVelocity t y) u v) t
    intro y u v
    have h := hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi (evolution t ht y).curvatureVelocity
      (evolution t ht y).hCurvature
    dsimp only [ricciVelocity]
    rw [dif_pos ht]
    exact h y u v
  have htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x := by
    intro t ht x
    have hTraceLaplacian :=
      g.HamiltonIveyTraceLaplacianAt_of_shiftedTensorRegularity
        cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
    have h :=
      HamiltonIveyCurvatureEvolutionCertificate.scalarTraceVelocity_of_traceLaplacian
        g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht x
        (evolution t ht x) hTraceLaplacian
    change RicciFlow.metricTraceAt (I := I) (M := M) g t x
      (if hmem : t ∈ Icc 0 T then
        curvatureTensorVelocityRicci
          (evolution t hmem x).curvatureVelocity x else 0) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x
    rw [dif_pos ht]
    exact h
  have hScalarTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t := by
    intro t ht x
    have hTraceLaplacian :=
      g.HamiltonIveyTraceLaplacianAt_of_shiftedTensorRegularity
        cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
    exact hasDerivAt_scalarCurvature_of_curvatureOperatorEvolution
      g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht x
        (evolution t ht x).hEvolution hTraceLaplacian
  have hscalarLower := g.scalarCurvature_hamiltonIvey_lowerBarrier_of_scalarEvolution
    cov hcov hLevi hdim hK.le hnuLower hScalarCont hScalarNear
      hScalarDifferential hScalarTime
  have hcontactCertificate : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveyCurvatureContactCertificateAtSpatialMinimum
        g cov hcov hLevi hdim K t x := by
    intro t x ht hdefect
    let regularity := hcontact ht hdefect
    let d := HamiltonIveySupportContactData.of_bad_contact_and_continuity
      g cov hcov hLevi hdim hK ht.1 x (hnuNeg t ht x) hdefect
      (hscalarLower t ht x) regularity.hnormContinuous
      regularity.hScalarContinuous regularity.hSupportContinuous
      (hScalarNear t ht x) (hScalarDifferential t ht x) regularity.hSupport
    exact HamiltonIveyCurvatureContactCertificateAtSpatialMinimum.of_curvatureEvolutionCertificate
      g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht
      d.hupper d.hneg d.hscalarSupport d.hnear d.hdiff d.hSupport
      (evolution t ht x)
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvature_contact_certificate_at_spatial_minimum
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hScalarCont
    hScalarNear hScalarDifferential ricciVelocity hRicci htrace hcont
    hcontactCertificate

/-- The capstone pinching theorem with its spatial regularity input stated
directly for the actual lowered curvature operator.  The shifted tensor is
the contact eigenvalue shift of that operator, so its trace/Laplacian
regularity is discharged by the proved metric-compatibility transport.
-/
theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_operatorRegularity_contactData_at_spatial_minimum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x)
    (hOperatorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyCurvatureOperatorRegularity
        cov hcov hLevi hdim t x)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveySupportContactRegularityData g cov hcov hLevi hdim t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hShiftedTensorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyShiftedTensorTraceRegularity
        cov hcov hLevi hdim t x := by
    intro t ht x
    exact HamiltonIveyShiftedTensorTraceRegularity.of_curvatureOperatorRegularity
      g cov hcov hLevi hdim t x (hOperatorRegularity t ht x)
  have hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y := by
    intro t ht x
    exact Filter.Eventually.of_forall (fun y =>
      (g.scalarRegularity_of_shiftedTensorRegularity cov hcov hLevi hdim t y
        (hShiftedTensorRegularity t ht y)).1)
  have hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x := by
    intro t ht x
    exact g.scalarDifferential_mdifferentiableAt_of_shiftedTensorRegularity
      cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_contactData_at_spatial_minimum
    cov hcov hLevi hdim gdot hK hT hflow evolution
    hShiftedTensorRegularity
    hnuNeg hnuLower hScalarCont hScalarNear hScalarDifferential hcont hcontact

/-! The C2 overload keeps the operator regularity source explicit while
delegating the maximum-principle argument to the preceding theorem. -/

/-- Hamilton--Ivey pinching from global C2 regularity of the actual lowered
curvature operator, together with the independent C1 regularity of its
induced covariant derivative.  The geometric curvature-evolution certificate
and Rayleigh-support contact data remain explicit. -/
theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_operatorC2_contactData_at_spatial_minimum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x)
    (hOperatorC2 : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      g.HamiltonIveyCurvatureOperatorC2 cov hcov hLevi hdim t)
    (hOperatorDerivativeRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      g.HamiltonIveyCurvatureOperatorDerivativeRegularity cov hcov t)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveySupportContactRegularityData g cov hcov hLevi hdim t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hOperatorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyCurvatureOperatorRegularity
        cov hcov hLevi hdim t x := by
    intro t ht x
    exact HamiltonIveyCurvatureOperatorRegularity.of_contMDiff_two
      g cov hcov hLevi hdim (t := t)
      (hcov₂ := hOperatorDerivativeRegularity t ht) x
      (hOperatorC2 t ht)
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_operatorRegularity_contactData_at_spatial_minimum
    cov hcov hLevi hdim gdot hK hT hflow evolution
    hOperatorRegularity
    hnuNeg hnuLower hScalarCont hcont hcontact

/-! This version states the pinching estimate only where its logarithmic
profile is geometrically defined (`nu < 0`).  A capped defect is used for
spacetime compactness, so no global negative-curvature-operator hypothesis is
needed.  The contact calculation itself remains on the genuine negative
least-eigenvalue region and uses the same curvature-evolution and support
certificates as the everywhere-negative variant above. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_contactData_on_negative_spectrum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x)
    (hShiftedTensorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyShiftedTensorTraceRegularity
        cov hcov hLevi hdim t x)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hNuCont : ContinuousOn
      (fun p : ℝ × M =>
        g.curvatureNu cov hcov hLevi hdim p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveySupportContactRegularityData g cov hcov hLevi hdim t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
        0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hTruncatedDefectContinuous :=
    g.hamiltonIveyTruncatedDefect_continuousOn_of_scalarCurvature_and_curvatureNu
      cov hcov hLevi hdim hK hT hScalarCont hNuCont
  have hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y := by
    intro t ht x
    exact Filter.Eventually.of_forall (fun y =>
      (g.scalarRegularity_of_shiftedTensorRegularity cov hcov hLevi hdim t y
        (hShiftedTensorRegularity t ht y)).1)
  have hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x := by
    intro t ht x
    exact g.scalarDifferential_mdifferentiableAt_of_shiftedTensorRegularity
      cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
  let ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := fun t x =>
    if ht : t ∈ Icc 0 T then
      curvatureTensorVelocityRicci (evolution t ht x).curvatureVelocity x
    else 0
  have hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t := by
    intro t ht
    change ∀ y : M, ∀ u v : TM y,
      HasDerivAt
        (fun τ => RicciFlow.intrinsicRicciTensor
          (I := I) (M := M) g τ y u v)
        ((ricciVelocity t y) u v) t
    intro y u v
    have h := hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi (evolution t ht y).curvatureVelocity
      (evolution t ht y).hCurvature
    dsimp only [ricciVelocity]
    rw [dif_pos ht]
    exact h y u v
  have htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x := by
    intro t ht x
    have hTraceLaplacian :=
      g.HamiltonIveyTraceLaplacianAt_of_shiftedTensorRegularity
        cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
    have h :=
      HamiltonIveyCurvatureEvolutionCertificate.scalarTraceVelocity_of_traceLaplacian
        g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht x
        (evolution t ht x) hTraceLaplacian
    change RicciFlow.metricTraceAt (I := I) (M := M) g t x
      (if hmem : t ∈ Icc 0 T then
        curvatureTensorVelocityRicci
          (evolution t hmem x).curvatureVelocity x else 0) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x
    rw [dif_pos ht]
    exact h
  have hScalarTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t := by
    intro t ht x
    have hTraceLaplacian :=
      g.HamiltonIveyTraceLaplacianAt_of_shiftedTensorRegularity
        cov hcov hLevi hdim t x (hShiftedTensorRegularity t ht x)
    exact hasDerivAt_scalarCurvature_of_curvatureOperatorEvolution
      g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht x
        (evolution t ht x).hEvolution hTraceLaplacian
  have hscalarLower := g.scalarCurvature_hamiltonIvey_lowerBarrier_of_scalarEvolution
    cov hcov hLevi hdim hK.le hnuLower hScalarCont hScalarNear
      hScalarDifferential hScalarTime
  have hcontactSupport : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ (s : ℝ × M → ℝ) (sdot : ℝ),
        s (t, x) = g.hamiltonIveyDefect cov hcov hLevi hdim K t x ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2 ≤ s p) ∧
        HasDerivAt (fun τ : ℝ => s (τ, x)) sdot t ∧
        (∀ᶠ y in 𝓝 x, MDiffAt (fun z : M => s (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M => s (t, z)) y)) x ∧
        (∀ hmin : IsLocalMin (fun y : M => s (t, y)) x,
          g.scalarLaplacian cov (fun _ y => s (t, y)) t x +
              g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤ sdot) := by
    intro t x ht hnu hdefect
    let regularity := hcontact ht hnu hdefect
    let d := HamiltonIveySupportContactData.of_bad_contact_and_continuity
      g cov hcov hLevi hdim hK ht.1 x hnu hdefect
      (hscalarLower t ht x) regularity.hnormContinuous
      regularity.hScalarContinuous regularity.hSupportContinuous
      (hScalarNear t ht x) (hScalarDifferential t ht x) regularity.hSupport
    let c := HamiltonIveyCurvatureContactCertificateAtSpatialMinimum.of_curvatureEvolutionCertificate
      g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht
      d.hupper d.hneg d.hscalarSupport d.hnear d.hdiff d.hSupport
      (evolution t ht x)
    let s : ℝ × M → ℝ := fun p =>
      g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x p
    have hsTouch : s (t, x) =
        g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
      simpa [s] using
        g.hamiltonIveySupportedDefect_eq_at_contact
          cov hcov hLevi hdim K t x
    have hnuNear : ∀ᶠ p in 𝓝 (t, x),
        g.curvatureNu cov hcov hLevi hdim p.1 p.2 < 0 := by
      filter_upwards [d.hupper, d.hneg] with p hpupper hpneg
      exact hpupper.trans_lt hpneg
    have hsUpper : ∀ᶠ p in 𝓝 (t, x),
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2 ≤ s p := by
      filter_upwards [d.hupper, d.hneg, d.hscalarSupport] with
          p hpupper hpneg hscalarSupport
      simpa [s] using g.hamiltonIveyDefect_le_supportedDefect
        cov hcov hLevi hdim K t x p hpupper hpneg hscalarSupport
    let v : TM x := g.curvatureNuContactVectorField
      cov hcov hLevi hdim t x x
    let scalarVelocity : ℝ :=
      2 * g.ricciNormSq cov hcov t x +
        RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (c.ricciVelocity x)
    let contactRicciVelocity : ℝ := c.ricciVelocity x v v
    let sdot : ℝ :=
      scalarVelocity /
          (-g.curvatureNu cov hcov hLevi hdim t x) +
        (g.scalarCurvature cov hcov t x -
            g.curvatureNu cov hcov hLevi hdim t x) /
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 *
          (scalarVelocity - 2 * contactRicciVelocity -
            (g.curvatureLambda cov hcov hLevi hdim t x +
              g.curvatureMu cov hcov hLevi hdim t x) ^ 2) -
        K / (1 + K * t)
    have hscalarTime :=
      g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
        cov hcov hLevi gdot (Icc 0 T) hflow ht (x := x)
        c.ricciVelocity c.hRicci
    have hricciTime :=
      g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
        cov hcov hLevi x v v c.ricciVelocity c.hRicci
    have hsTime :=
      g.hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
        cov hcov hLevi hdim gdot (Icc 0 T) hflow hK ht ht.1 hnu
        scalarVelocity contactRicciVelocity hscalarTime hricciTime
    have hsTime' : HasDerivAt (fun τ : ℝ => s (τ, x)) sdot t := by
      simpa [s, sdot, scalarVelocity, contactRicciVelocity, v] using hsTime
    have hvelocityEq : c.ricciVelocity x = ricciVelocity t x := by
      ext u v
      exact (c.hRicci x u v).unique (hRicci ht x u v)
    have htraceC := htrace t ht x
    rw [← hvelocityEq] at htraceC
    refine ⟨s, sdot, ?_, hnuNear, hsUpper, hsTime', d.hnear,
      d.hdiff, ?_⟩
    · exact hsTouch
    · intro hmin
      exact HamiltonIveyCurvatureContactCertificateAtSpatialMinimum.evolution_at_spatial_minimum_of_curvatureOperatorEvolution
        g cov hcov hLevi hdim c (hScalarNear t ht x)
        (hScalarDifferential t ht x) htraceC hmin
  exact g.hamiltonIveyPinching_of_truncatedDefect_support_certificate_at_spatial_minimum
    cov hcov hLevi hdim hK hT hnuLower hscalarLower
    hTruncatedDefectContinuous hcontactSupport

/- The negative-spectrum capstone with the same regularity input exposed in
   its actual lowered-curvature-operator form. -/
theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_operatorRegularity_contactData_on_negative_spectrum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x)
    (hOperatorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyCurvatureOperatorRegularity
        cov hcov hLevi hdim t x)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hNuCont : ContinuousOn
      (fun p : ℝ × M =>
        g.curvatureNu cov hcov hLevi hdim p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveySupportContactRegularityData g cov hcov hLevi hdim t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
        0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hShiftedTensorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyShiftedTensorTraceRegularity
        cov hcov hLevi hdim t x := by
    intro t ht x
    exact HamiltonIveyShiftedTensorTraceRegularity.of_curvatureOperatorRegularity
      g cov hcov hLevi hdim t x (hOperatorRegularity t ht x)
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_contactData_on_negative_spectrum
    cov hcov hLevi hdim gdot hK hT hflow evolution
    hShiftedTensorRegularity
    hnuLower hScalarCont hNuCont hcontact

/- A C2 source overload for the negative-spectrum capstone. -/
theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_operatorC2_contactData_on_negative_spectrum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x)
    (hOperatorC2 : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      g.HamiltonIveyCurvatureOperatorC2 cov hcov hLevi hdim t)
    (hOperatorDerivativeRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      g.HamiltonIveyCurvatureOperatorDerivativeRegularity cov hcov t)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hNuCont : ContinuousOn
      (fun p : ℝ × M =>
        g.curvatureNu cov hcov hLevi hdim p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveySupportContactRegularityData g cov hcov hLevi hdim t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
        0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hOperatorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyCurvatureOperatorRegularity
        cov hcov hLevi hdim t x := by
    intro t ht x
    exact HamiltonIveyCurvatureOperatorRegularity.of_contMDiff_two
      g cov hcov hLevi hdim (t := t)
      (hcov₂ := hOperatorDerivativeRegularity t ht) x
      (hOperatorC2 t ht)
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_operatorRegularity_contactData_on_negative_spectrum
    cov hcov hLevi hdim gdot hK hT hflow evolution
    hOperatorRegularity
    hnuLower hScalarCont hNuCont hcontact

end IntrinsicTransport

end CovariantDerivative.TimeDependentRiemannianMetric
