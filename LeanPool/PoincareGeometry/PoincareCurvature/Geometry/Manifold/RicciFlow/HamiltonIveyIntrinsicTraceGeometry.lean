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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyGeometricEvolution
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicConnectionVariation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyDerivedMovingConnectionVariation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.InducedHomCurvature
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHomRegularity
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchiUnconditional

/-!
# Intrinsic static fields for the Hamilton--Ivey trace calculation

This file starts removing the coordinate/contraction certificate from the
geometric evolution interface.  The fields below are the actual curvature,
Ricci, scalar-curvature, and covariant-Hessian fields of a time slice.  The
three-dimensional curvature decomposition, Ricci symmetry, scalar trace, and
last-slot Hessian symmetry are proved from the Levi--Civita connection itself.

The remaining differential contractions are intentionally not hidden here:
they require the corresponding spatial regularity and Bianchi/commutator
bridges, which are the next layer of the intrinsic evolution proof.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] [I.Boundaryless]
  [hContTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)

local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
local notation "T₃" => (fun y : M => TM y →L[ℝ] T₂ y)

local instance intrinsicTraceScalarTopologicalSpace :
    TopologicalSpace (TotalSpace ℝ (Bundle.Trivial M ℝ)) :=
  Bundle.Trivial.topologicalSpace M ℝ
local instance intrinsicTraceScalarFiberBundle :
    FiberBundle ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.fiberBundle M ℝ
local instance intrinsicTraceScalarVectorBundle :
    VectorBundle ℝ ℝ (Bundle.Trivial M ℝ) :=
  Bundle.Trivial.vectorBundle ℝ M ℝ
local instance intrinsicTraceScalarContMDiffVectorBundle :
    ContMDiffVectorBundle 2 ℝ (Bundle.Trivial M ℝ) I :=
  Bundle.Trivial.contMDiffVectorBundle ℝ

local instance intrinsicTraceCovectorNormedAddCommGroup :
    ∀ y : M, NormedAddCommGroup (T₁ y) :=
  fun _ => ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicTraceCovectorNormedSpace :
    ∀ y : M, NormedSpace ℝ (T₁ y) :=
  fun _ => ContinuousLinearMap.toNormedSpace

local instance intrinsicTraceTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance intrinsicTraceTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance intrinsicTraceTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance intrinsicTraceTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance intrinsicTraceTwoFiberTopologicalSpace (y : M) :
    TopologicalSpace (T₂ y) := inferInstance
local instance intrinsicTraceOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance intrinsicTraceOneFiberBundle :
    FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance intrinsicTraceOneVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance intrinsicTraceOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap
local instance intrinsicTraceTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance intrinsicTraceTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance intrinsicTraceTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance intrinsicTraceTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap
local instance intrinsicTraceThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance intrinsicTraceThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance intrinsicTraceThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance intrinsicTraceThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance intrinsicTraceThreeFiberTopologicalSpace (y : M) :
    TopologicalSpace (T₃ y) := inferInstance
local instance intrinsicTraceThreeTopologicalSpace :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance intrinsicTraceThreeFiberBundle :
    FiberBundle
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance intrinsicTraceThreeVectorBundle :
    VectorBundle ℝ
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance intrinsicTraceThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2
      (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- The actual static fields used by the three-dimensional Hamilton--Ivey
trace calculation.  No curvature component or Ricci coefficient is supplied
by the caller: `K`, `Ric`, and `Scal` are evaluations of the genuine slice
curvature and its two contractions, while `H` is the genuine covariant
Hessian of the genuine Ricci two-tensor. -/
theorem intrinsicHamiltonIveyTraceFields
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ y : M, Module.finrank ℝ (TM y) = 3)
    (t : ℝ) (x : M) :
    ∃ (b : Module.Basis (Fin 3) ℝ (TM x))
      (K : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
      (Ric : Fin 3 → Fin 3 → ℝ) (Scal : ℝ)
      (H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
      (S : Fin 3 → Fin 3 → ℝ),
      (∀ a b c d,
        K a b c d =
          Ric a d * (if b = c then 1 else 0) -
            Ric a c * (if b = d then 1 else 0) -
            Ric b d * (if a = c then 1 else 0) +
            Ric b c * (if a = d then 1 else 0) -
            Scal / 2 *
              ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
                (if a = c then 1 else 0) * (if b = d then 1 else 0))) ∧
      (∀ a b, Ric a b = Ric b a) ∧
      (Scal = ∑ i, Ric i i) ∧
      (∀ a b c d, H a b c d = H a b d c) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let e : OrthonormalBasis (Fin 3) ℝ (TM x) :=
    (stdOrthonormalBasis ℝ (TM x)).reindex
      (finCongr (show Module.finrank ℝ (TM x) = 3 from hdim x))
  let b : Module.Basis (Fin 3) ℝ (TM x) := e.toBasis
  let K : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b c d =>
    Inner.inner ℝ
      ((cov t).curvatureTensor x (e a) (e b) (e c)) (e d)
  let Ric : Fin 3 → Fin 3 → ℝ := fun a b =>
    CovariantDerivative.ricciCurvature (cov := cov t) x (e a) (e b)
  let Scal : ℝ :=
    CovariantDerivative.scalarCurvature (cov := cov t) x
  let H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b c d =>
    CovariantDerivative.covariantHessianTwoTensor (cov t)
      (fun y => CovariantDerivative.ricciCovariantTwoTensor (cov t) y)
      x (e a) (e b) (e c) (e d)
  let S : Fin 3 → Fin 3 → ℝ := fun a b =>
    CovariantDerivative.scalarHessian (cov t)
      (fun y => CovariantDerivative.scalarCurvature (cov t) y)
      x (e a) (e b)
  have hK : ∀ a b c d,
      K a b c d =
        Ric a d * (if b = c then 1 else 0) -
          Ric a c * (if b = d then 1 else 0) -
          Ric b d * (if a = c then 1 else 0) +
          Ric b c * (if a = d then 1 else 0) -
          Scal / 2 *
            ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
              (if a = c then 1 else 0) * (if b = d then 1 else 0)) := by
    intro a b c d
    have h :=
      CovariantDerivative.curvature_inner_eq_threeDimensional_curvature
        (cov := cov t) (hLevi := hLevi t) (hdim := hdim x) x
        (e a) (e b) (e c) (e d)
    simpa [K, Ric, Scal, e.inner_eq_ite] using h
  have hRicSymm : ∀ a b, Ric a b = Ric b a := by
    intro a b
    simpa [Ric] using
      (CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
        (cov := cov t) (hLevi t) x (e a) (e b))
  have hScal : Scal = ∑ i, Ric i i := by
    simpa [Scal, Ric] using
      (CovariantDerivative.scalarCurvature_eq_sum_ricci_orthonormalBasis
        (cov t) x e)
  have hRicTensorSymm : ∀ y : M, ∀ u v : TM y,
      CovariantDerivative.ricciCovariantTwoTensor (cov t) y u v =
        CovariantDerivative.ricciCovariantTwoTensor (cov t) y v u := by
    intro y u v
    exact
      CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
        (cov := cov t) (hLevi t) y u v
  have hHlast : ∀ a b c d, H a b c d = H a b d c := by
    intro a b c d
    simpa [H] using
      (CovariantDerivative.covariantHessianTwoTensor_swap
        (cov t) hRicTensorSymm x (e a) (e b) (e c) (e d))
  exact ⟨b, K, Ric, Scal, H, S, hK, hRicSymm, hScal, hHlast⟩

/-! The scalar trace of the genuine Ricci Hessian is the genuine scalar
Hessian.  This is the first differential contraction needed by the
Hamilton--Ivey component calculation; the regularity arguments are stated
explicitly because the current slicewise Ricci-flow predicate does not imply
them. -/

def intrinsicRicciTraceRegularity
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    (∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun w : M => TM w →L[ℝ] TM w) z
        (raisedCovariantTwoTensor (I := I) (E := E)
          (ricciCovariantTwoTensor (cov t)) z)) y) ∧
    MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative (cov t)
          (ricciCovariantTwoTensor (cov t)) y)) x ∧
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E)
            (ricciCovariantTwoTensor (cov t))) y)) x ∧
    (∀ Y : TM x, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun w : M => TM w →L[ℝ] TM w) z
        (raisedCovariantTwoTensor (I := I) (E := E)
          (covariantTwoTensorDerivativeAlong (cov t)
            (ricciCovariantTwoTensor (cov t))
            (smoothExtend (I := I) (F := E) (V := TM) x Y)) z)) x)
theorem intrinsicHamiltonIveyTrace_hTrace
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ y : M, Module.finrank ℝ (TM y) = 3)
    (t : ℝ) (x : M)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin 3) ℝ (TM x)) (a b : Fin 3),
      (∑ i : Fin 3,
        covariantHessianTwoTensor (cov t)
          (ricciCovariantTwoTensor (cov t)) x (e a) (e b) (e i) (e i)) =
        scalarHessian (cov t)
          (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y) x
          (e a) (e b) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  haveI : IsManifold I (minSmoothness ℝ 4) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rcases hregular with
    ⟨hRicciRaised, hRicciFirst, hTraceDifferential, hRicciSecondRaised⟩
  have hRicciLinear :
      covariantTwoTensorLinear (I := I) (M := M)
          (ricciCovariantTwoTensor (cov t)) =
        (fun y : M => CovariantDerivative.ricciCurvature (cov := cov t) y) := by
    funext y
    ext u v
    rfl
  have htraceEq : ∀ y : M,
      covariantTwoTensorTraceFunction (I := I) (E := E)
          (ricciCovariantTwoTensor (cov t)) y =
        CovariantDerivative.scalarCurvature (cov := cov t) y := by
    intro y
    rw [covariantTwoTensorTraceFunction, hRicciLinear]
    exact
      (covariantTwoTensorTrace_ricciCurvature_eq_scalarCurvature
        (I := I) (E := E) (M := M) (cov t) y)
  intro e a b
  have h :=
    scalarHessian_covariantTwoTensorTraceFunction_eq_sum_covariantHessian
      (I := I) (E := E) (M := M) (cov t) ((hLevi t).2)
      (ricciCovariantTwoTensor (cov t)) hRicciRaised hRicciFirst
      hTraceDifferential hRicciSecondRaised (e a) (e b) e
  have hscalar :
      scalarHessian (cov t)
          (covariantTwoTensorTraceFunction (I := I) (E := E)
            (ricciCovariantTwoTensor (cov t))) x (e a) (e b) =
        scalarHessian (cov t)
          (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
          x (e a) (e b) := by
    have hfun :
        covariantTwoTensorTraceFunction (I := I) (E := E)
            (ricciCovariantTwoTensor (cov t)) =
          (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y) := by
      funext y
      exact htraceEq y
    rw [hfun]
  change
    (∑ i : Fin 3,
      covariantHessianTwoTensor (cov t)
        (ricciCovariantTwoTensor (cov t)) x (e a) (e b) (e i) (e i)) =
      scalarHessian (cov t)
        (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
        x (e a) (e b)
  calc
    _ = scalarHessian (cov t)
        (covariantTwoTensorTraceFunction (I := I) (E := E)
          (ricciCovariantTwoTensor (cov t))) x (e a) (e b) := h.symm
    _ = _ := hscalar

/-! The first-slot symmetry of the scalar Hessian is also an intrinsic
commutator statement.  It is not a component assumption: the scalar
second-derivative commutator is supplied by the manifold calculus, and the
remaining connection commutator is exactly the vanishing torsion of the
Levi--Civita slice. -/

theorem scalarHessian_swap_of_contMDiff_two
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative cov 1]
    {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {x : M}
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hT : cov.torsion = 0)
    (u v : TM x) :
    scalarHessian cov f x u v = scalarHessian cov f x v u := by
  let U : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  let V : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x v
  have hU₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% U) := by
    simpa [U] using
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u)
  have hV₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% V) := by
    simpa [V] using
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v)
  have hU₁ := hU₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hV₁ := hV₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hcomm :=
    extDerivFun_lieBracket_commutator (I := I) (f := f) (X := U) (Y := V)
      (x := x) hf hU₁ hV₁
  have htorsion :=
    cov.along_sub_eq_mlieBracket_of_torsion_eq_zero hT hU₁ hV₁
  have htorsionx := congrFun htorsion x
  have hcomm' :
      mvfderiv (I := I) (fun y =>
          scalarDifferential (I := I) f y (V y)) x (U x) -
        mvfderiv (I := I) (fun y =>
          scalarDifferential (I := I) f y (U y)) x (V x) -
        scalarDifferential (I := I) f x
          (VectorField.mlieBracket I U V x) = 0 := by
    simpa only [scalarDifferential_apply] using hcomm
  have htorsion' :
      scalarDifferential (I := I) f x (cov V x (U x)) -
        scalarDifferential (I := I) f x (cov U x (V x)) =
        scalarDifferential (I := I) f x
          (VectorField.mlieBracket I U V x) := by
    simpa [CovariantDerivative.along] using
      congrArg (fun w : TM x => scalarDifferential (I := I) f x w) htorsionx
  rw [scalarHessian_apply_of_mdifferentiableAt cov f hdf u v,
    scalarHessian_apply_of_mdifferentiableAt cov f hdf v u]
  simp only [U, V, smoothExtend_apply]
  simp only [scalarDifferential_apply]
  have hmain :
      mvfderiv (I := I) (fun y =>
          mvfderiv (I := I) f y (V y)) x (U x) -
        mvfderiv (I := I) (fun y =>
          mvfderiv (I := I) f y (U y)) x (V x) =
        mvfderiv (I := I) f x
          (VectorField.mlieBracket I U V x) := by
    linarith [hcomm']
  have hmain' :
      mvfderiv (I := I) (fun y =>
          mvfderiv (I := I) f y
            (smoothExtend (I := I) (F := E) (V := TM) x v y)) x u -
        mvfderiv (I := I) (fun y =>
          mvfderiv (I := I) f y
            (smoothExtend (I := I) (F := E) (V := TM) x u y)) x v =
        mvfderiv (I := I) f x
          (VectorField.mlieBracket I U V x) := by
    simpa [U, V, smoothExtend_apply] using hmain
  have htorsion'' :
      mvfderiv (I := I) f x
          (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x u) -
        mvfderiv (I := I) f x
          (cov (smoothExtend (I := I) (F := E) (V := TM) x u) x v) =
        mvfderiv (I := I) f x
          (VectorField.mlieBracket I U V x) := by
    simpa [U, V, smoothExtend_apply, scalarDifferential_apply] using htorsion'
  linarith [hmain', htorsion'']

/-! The symmetry theorem above, specialized to the actual scalar curvature,
is the scalar-Hessian symmetry field consumed by the Hamilton--Ivey
contraction calculation.  The scalar differential regularity is transferred
from the genuine Ricci trace, rather than postulated for a replacement
scalar. -/
theorem intrinsicHamiltonIveyTrace_hSsymm
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x)
    (hscalar :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle I 1 E TM :=
        g.slice_isContMDiffRiemannianBundle t
      letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
      ContMDiff I 𝓘(ℝ) 2
        (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin 3) ℝ (TM x)) (a b : Fin 3),
      scalarHessian (cov t)
          (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
          x (e a) (e b) =
        scalarHessian (cov t)
          (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
          x (e b) (e a) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  rcases hregular with
    ⟨_, _, hTraceDifferential, _⟩
  have hRicciLinear :
      covariantTwoTensorLinear (I := I) (M := M)
          (ricciCovariantTwoTensor (cov t)) =
        (fun y : M => CovariantDerivative.ricciCurvature (cov := cov t) y) := by
    funext y
    ext u v
    rfl
  have htraceFun :
      covariantTwoTensorTraceFunction (I := I) (E := E)
          (ricciCovariantTwoTensor (cov t)) =
        (fun y : M => CovariantDerivative.scalarCurvature (cov := cov t) y) := by
    funext y
    rw [covariantTwoTensorTraceFunction, hRicciLinear]
    exact
      (covariantTwoTensorTrace_ricciCurvature_eq_scalarCurvature
        (I := I) (E := E) (M := M) (cov t) y)
  have hdf :
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I)
            (fun z => CovariantDerivative.scalarCurvature (cov := cov t) z) y)) x := by
    apply hTraceDifferential.congr_of_eventuallyEq
    filter_upwards [] with y
    apply congrArg (fun α : T₁ y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y α)
    exact congrArg (fun f : M → ℝ => scalarDifferential (I := I) f y) htraceFun.symm
  intro e a b
  exact scalarHessian_swap_of_contMDiff_two
    (cov := cov t) (hf := hscalar) (x := x) (hdf := hdf)
    (hT := (hLevi t).1) (u := e a) (v := e b)

/-! The Laplacian field is the defining orthonormal-basis evaluation of the
genuine connection Laplacian. -/

theorem intrinsicHamiltonIveyTrace_hLaplacian
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (t : ℝ) (x : M) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin 3) ℝ (TM x)) (a b : Fin 3),
      connectionLaplacian (cov t)
          (fun y => ricciCovariantTwoTensor (cov t) y) x (e a) (e b) =
        ∑ k : Fin 3,
          covariantHessianTwoTensor (cov t)
            (ricciCovariantTwoTensor (cov t)) x (e k) (e k) (e a) (e b) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  intro e a b
  exact congrArg (fun q : T₂ x => q (e a) (e b))
    (connectionLaplacian_eq_sum_orthonormalBasis
      (cov t) (fun y => ricciCovariantTwoTensor (cov t) y) x e)

/-! Differentiating contracted Bianchi gives the mixed Ricci-Hessian
contraction.  The trace is commuted through the covariant derivative using
metric compatibility; the moving test vector is retained until its
connection correction cancels against the covector derivative. -/
/-- The contracted Ricci-Hessian trace, with contracted Bianchi derived from
the actual curvature tensor.  The additional C² metric-bundle and connection
regularity are explicit: the IsRicciFlowOn predicate currently supplies only a C¹
connection, so this lemma does not claim to derive that regularity from the
Ricci-flow predicate. -/
theorem intrinsicHamiltonIveyTrace_hDiv
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hcov₂ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 2)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M)
    (hmetric₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 2 E TM)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin 3) ℝ (TM x)) (a b : Fin 3),
      (∑ i : Fin 3,
        covariantHessianTwoTensor (cov t)
          (ricciCovariantTwoTensor (cov t)) x
          (e a) (e i) (e b) (e i)) =
        (1 / 2 : ℝ) *
          scalarHessian (cov t)
            (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
            x (e a) (e b) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : IsContMDiffRiemannianBundle I 2 E TM := hmetric₂
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov t) 2 := hcov₂ t
  rcases hregular with
    ⟨_, hRicciFirst, hTraceDifferential, _⟩
  let ricci : ∀ y : M, T₂ y :=
    CovariantDerivative.ricciCovariantTwoTensor (cov t)
  let C : ∀ y : M, T₃ y :=
    covariantTwoTensorCovariantDerivative (cov t) ricci
  have hRicciSymm : ∀ y : M, ∀ u v : TM y, ricci y u v = ricci y v u := by
    intro y u v
    exact CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
      (cov := cov t) (hLevi t) y u v
  have hCSymm : ∀ y : M, ∀ X u v : TM y, C y X u v = C y X v u := by
    intro y X u v
    exact CovariantDerivative.covariantTwoTensorCovariantDerivative_swap
      (cov t) hRicciSymm y X u v
  have hRicciLinear :
      covariantTwoTensorLinear (I := I) (M := M) ricci =
        (fun y : M => CovariantDerivative.ricciCurvature (cov := cov t) y) := by
    funext y
    ext u v
    rfl
  have htraceFun :
      covariantTwoTensorTraceFunction (I := I) (E := E) ricci =
        (fun y : M => CovariantDerivative.scalarCurvature (cov := cov t) y) := by
    funext y
    rw [covariantTwoTensorTraceFunction, hRicciLinear]
    exact covariantTwoTensorTrace_ricciCurvature_eq_scalarCurvature
      (I := I) (E := E) (M := M) (cov t) y
  have hScalarDifferential :
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I)
            (fun z => CovariantDerivative.scalarCurvature (cov := cov t) z) y)) x := by
    apply hTraceDifferential.congr_of_eventuallyEq
    filter_upwards [] with y
    apply congrArg (fun α : T₁ y =>
      TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y α)
    exact congrArg (fun f : M → ℝ => scalarDifferential (I := I) f y)
      htraceFun.symm
  have hBianchi :
      (fun y : M => ricciDivergence (cov t) y) =
        (fun y : M => (1 / 2 : ℝ) •
          scalarDifferential (I := I)
            (CovariantDerivative.scalarCurvature (cov := cov t)) y) := by
    haveI : IsManifold I (minSmoothness ℝ 4) M := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    haveI : IsManifold I ((3 : ℕ∞) + 1) M :=
      IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
    funext y
    exact CovariantDerivative.ricciDivergence_eq_half_scalarDifferential_of_curvature_unconditional
      (cov := cov t) y (hLevi t).1 (hLevi t).2
  have hDscaled :
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          ((1 / 2 : ℝ) •
            scalarDifferential (I := I)
              (CovariantDerivative.scalarCurvature (cov := cov t)) y)) x :=
    (mdifferentiableAt_const : MDiffAt (fun _ : M => (1 / 2 : ℝ)) x).smul_section
      hScalarDifferential
  have hD :
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (ricciDivergence (cov t) y)) x := by
    apply hDscaled.congr_of_eventuallyEq
    filter_upwards [] with y
    apply congrArg (fun α : T₁ y =>
      TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y α)
    exact congrArg (fun f : ∀ z : M, T₁ z => f y) hBianchi
  intro e a b
  let X : TM x := e a
  let Y₀ : TM x := e b
  let Y : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x Y₀
  have hY₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y) := by
    simpa [Y] using
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x Y₀)
  have hY : MDiffAt (T% Y) x :=
    (hY₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2) x).mdifferentiableAt
      one_ne_zero
  let evalY : ∀ y : M, T₂ y →L[ℝ] T₁ y := fun y =>
    ContinuousLinearMap.apply ℝ (T₁ y) (Y y)
  let k : ∀ y : M, T₂ y := fun y => (evalY y).comp (C y)
  have htraceFunctions :
      covariantTwoTensorTraceFunction (I := I) (E := E) k =
        (fun y => ricciDivergence (cov t) y (Y y)) := by
    funext y
    let ey : OrthonormalBasis (Fin (Module.finrank ℝ (TM y))) ℝ (TM y) :=
      stdOrthonormalBasis ℝ (TM y)
    calc
      covariantTwoTensorTraceFunction (I := I) (E := E) k y =
          ∑ i, k y (ey i) (ey i) := by
            rw [covariantTwoTensorTraceFunction,
              covariantTwoTensorTrace_eq_sum_orthonormalBasis
                (I := I) (E := E) (M := M)
                (covariantTwoTensorLinear (I := I) (M := M) k) y ey]
            simp
      _ = ∑ i, C y (ey i) (Y y) (ey i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [k, evalY, ContinuousLinearMap.comp_apply]
      _ = ∑ i, C y (ey i) (ey i) (Y y) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hCSymm y (ey i) (Y y) (ey i)
      _ = ricciDivergence (cov t) y (Y y) := by
            have hsum := congrArg (fun α : T₁ y => α (Y y))
              (ricciDivergence_eq_sum_orthonormalBasis (cov t) y ey)
            simpa [C] using hsum.symm
  let eFrame : Trivialization E
      (TotalSpace.proj : TotalSpace E TM → M) := trivializationAt E TM x
  let bFrame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E
  have hC : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y (C y)) x := by
    simpa [C, ricci] using hRicciFirst
  have hK : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (k y)) x := by
    refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
      (IB := I) (E₁ := TM) (F₁ := E) (E₂ := T₁)
      (F₂ := E →L[ℝ] ℝ) (s := k) x bFrame ?_
    intro i
    let frame : ∀ y : M, TM y := eFrame.localFrame bFrame i
    have hx : x ∈ eFrame.baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' x
    have hframe : MDiffAt (T% frame) x :=
      (contMDiffAt_localFrame_of_mem (I := I) (e := eFrame)
        (b := bFrame) (n := (1 : ℕ∞) ) (i := i) (hx := hx)).mdifferentiableAt
        one_ne_zero
    have hCframe : MDiffAt
        (fun y => TotalSpace.mk'
          (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (C y (frame y))) x :=
      hC.clm_bundle_apply hframe
    have hKframe : MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (k y (frame y))) x := by
      simpa [k, evalY] using hCframe.clm_bundle_apply hY
    exact hKframe
  have hKraised := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) (h := k) hK
  have hKraised' : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TM z →L[ℝ] TM z) y
        ((rieszMap (I := I) y).comp (k y))) x := by
    simpa only [raisedCovariantTwoTensor] using hKraised
  have htraceDerivative :=
    mvfderiv_covariantTwoTensorTrace_eq_sum_covariantDerivative
      (I := I) (E := E) (M := M) (cov t) (hLevi t).2 k hKraised'
      X e
  have htraceDerivative' :
      mvfderiv (I := I)
        (covariantTwoTensorTraceFunction (I := I) (E := E) k) x X =
        ∑ i, covariantTwoTensorCovariantDerivative (cov t) k x X
          (e i) (e i) := by
    change mvfderiv (I := I)
      (fun y => covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M) k) y) x X = _
    exact htraceDerivative
  have hcovD :
      covectorCovariantDerivative (cov t) (ricciDivergence (cov t)) x X Y₀ =
        mvfderiv (I := I)
          (fun y => ricciDivergence (cov t) y (Y y)) x X -
          ricciDivergence (cov t) x ((cov t) Y x X) := by
    have h := @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM (Bundle.Trivial M ℝ) _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      (cov t) (realLineCovariantDerivative (I := I) (M := M))
      (fun y => ricciDivergence (cov t) y) Y x hD hY X
    simpa [covectorCovariantDerivative, realLineCovariantDerivative,
      trivialCovariantDerivative_apply, Y, smoothExtend_apply] using h
  have hproduct : ∀ i : Fin 3,
      covariantTwoTensorCovariantDerivative (cov t) k x X (e i) (e i) =
        covariantHessianTwoTensor (cov t) ricci x X (e i) Y₀ (e i) +
        C x (e i) ((cov t) Y x X) (e i) := by
    intro i
    let U : ∀ y : M, TM y :=
      smoothExtend (I := I) (F := E) (V := TM) x (e i)
    have hU₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% U) := by
      simpa [U] using
        (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e i))
    have hU : MDiffAt (T% U) x :=
      (hU₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2) x).mdifferentiableAt
        one_ne_zero
    have hmove := realLineCovariantDerivative_trilinear
      (cov := cov t) (A := C) (X := U) (U := Y) (V := U)
      hC hU hY hU X
    have hmove' :
        mvfderiv (I := I)
          (fun y => C y (U y) (Y y) (U y)) x X =
          covariantThreeTensorCovariantDerivative (cov t) C x X
              (e i) Y₀ (e i) +
            C x ((cov t) U x X) Y₀ (e i) +
            C x (e i) ((cov t) Y x X) (e i) +
            C x (e i) Y₀ ((cov t) U x X) := by
      simpa [realLineCovariantDerivative, trivialCovariantDerivative_apply,
        U, Y, smoothExtend_apply] using hmove
    rw [covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
      (cov := cov t) (hh := hK) X (e i) (e i)]
    simp [k, evalY, ContinuousLinearMap.comp_apply, U, Y, smoothExtend_apply]
    change
      mvfderiv (I := I) (fun y => C y (U y) (Y y) (U y)) x X -
        C x ((cov t) U x X) Y₀ (e i) -
        C x (e i) Y₀ ((cov t) U x X) =
      covariantHessianTwoTensor (cov t) ricci x X (e i) Y₀ (e i) +
        C x (e i) ((cov t) Y x X) (e i)
    rw [hmove']
    simp only [covariantHessianTwoTensor]
    ring
  have htraceProduct :
      (∑ i : Fin 3,
        covariantTwoTensorCovariantDerivative (cov t) k x X (e i) (e i)) =
        (∑ i : Fin 3,
          covariantHessianTwoTensor (cov t) ricci x X (e i) Y₀ (e i)) +
          ricciDivergence (cov t) x ((cov t) Y x X) := by
    calc
      _ = ∑ i : Fin 3,
          (covariantHessianTwoTensor (cov t) ricci x X
              (e i) Y₀ (e i) +
            C x (e i) ((cov t) Y x X) (e i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hproduct i
      _ = (∑ i : Fin 3,
            covariantHessianTwoTensor (cov t) ricci x X (e i) Y₀ (e i)) +
            ricciDivergence (cov t) x ((cov t) Y x X) := by
              rw [Finset.sum_add_distrib]
              congr 1
              have hsum := congrArg
                (fun α : T₁ x => α ((cov t) Y x X))
                (ricciDivergence_eq_sum_orthonormalBasis (cov t) x e)
              calc
                (∑ i : Fin 3, C x (e i) ((cov t) Y x X) (e i)) =
                    ∑ i : Fin 3, C x (e i) (e i) ((cov t) Y x X) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      exact hCSymm x (e i) ((cov t) Y x X) (e i)
                _ = ricciDivergence (cov t) x ((cov t) Y x X) := by
                      simpa [C] using hsum.symm
  have hcovDtrace :
      covectorCovariantDerivative (cov t) (ricciDivergence (cov t)) x X Y₀ =
        ∑ i : Fin 3,
          covariantHessianTwoTensor (cov t) ricci x X (e i) Y₀ (e i) := by
    calc
      _ = mvfderiv (I := I)
            (fun y => ricciDivergence (cov t) y (Y y)) x X -
            ricciDivergence (cov t) x ((cov t) Y x X) := hcovD
      _ = mvfderiv (I := I)
            (covariantTwoTensorTraceFunction (I := I) (E := E) k) x X -
            ricciDivergence (cov t) x ((cov t) Y x X) := by
              rw [← htraceFunctions]
      _ = (∑ i : Fin 3,
            covariantTwoTensorCovariantDerivative (cov t) k x X (e i) (e i)) -
            ricciDivergence (cov t) x ((cov t) Y x X) := by
              rw [htraceDerivative']
      _ = ∑ i : Fin 3,
            covariantHessianTwoTensor (cov t) ricci x X (e i) Y₀ (e i) := by
              rw [htraceProduct]
              ring
  have hBianchiDerivative :
      covectorCovariantDerivative (cov t) (ricciDivergence (cov t)) x X Y₀ =
        (1 / 2 : ℝ) *
          scalarHessian (cov t)
            (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
            x X Y₀ := by
    have hsmul :=
      (covectorCovariantDerivative (cov t)).isCovariantDerivativeOn.smul_const
        (1 / 2 : ℝ) hScalarDifferential
    have hBianchiDerivativeArg :
        covectorCovariantDerivative (cov t) (ricciDivergence (cov t)) x X Y₀ =
          covectorCovariantDerivative (cov t)
            ((1 / 2 : ℝ) •
              scalarDifferential (I := I)
                (CovariantDerivative.scalarCurvature (cov := cov t)))
            x X Y₀ := by
      have h := congrArg
        (fun α : ∀ y : M, T₁ y =>
          covectorCovariantDerivative (cov t) α x X)
        hBianchi
      exact congrArg (fun β : T₁ x => β Y₀) h
    calc
      _ = covectorCovariantDerivative (cov t)
            ((1 / 2 : ℝ) •
              scalarDifferential (I := I)
                (CovariantDerivative.scalarCurvature (cov := cov t)))
              x X Y₀ := by
                exact hBianchiDerivativeArg
      _ = ((1 / 2 : ℝ) •
            covectorCovariantDerivative (cov t)
              (scalarDifferential (I := I)
                (CovariantDerivative.scalarCurvature (cov := cov t))) x X) Y₀ := by
                rw [hsmul]
                simp only [smul_apply]
      _ = (1 / 2 : ℝ) *
            scalarHessian (cov t)
              (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
              x X Y₀ := by
                simp [scalarHessian, smul_eq_mul]
  have hfinal := hcovDtrace.symm.trans hBianchiDerivative
  change
    (∑ i : Fin 3,
      covariantHessianTwoTensor (cov t)
        (ricciCovariantTwoTensor (cov t)) x
        (e a) (e i) (e b) (e i)) =
      (1 / 2 : ℝ) *
        scalarHessian (cov t)
          (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
          x (e a) (e b)
  simpa [X, Y₀, ricci] using hfinal

/-! The first two derivative slots of a genuine covariant Hessian have
antisymmetrization equal to curvature acting on the tensor. -/

theorem covariantHessianTwoTensor_firstSlot_commutator
    (cov : CovariantDerivative I E TM)
    {h : ∀ y : M, T₂ y} {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hT : cov.torsion = 0)
    (X₁ X₂ : TM x)
    (hXmd : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x X₁)) x)
    (hYmd : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x X₂)) x)
    (u v : TM x) :
    covariantHessianTwoTensor cov h x X₁ X₂ u v -
        covariantHessianTwoTensor cov h x X₂ X₁ u v =
      (covariantTwoTensorCovariantDerivative cov).curvatureAux
        (smoothExtend (I := I) (F := E) (V := TM) x X₁)
        (smoothExtend (I := I) (F := E) (V := TM) x X₂) h x u v := by
  let X := smoothExtend (I := I) (F := E) (V := TM) x X₁
  let Y := smoothExtend (I := I) (F := E) (V := TM) x X₂
  let D := covariantTwoTensorCovariantDerivative cov
  have hHXY :
      covariantHessianTwoTensor cov h x X₁ X₂ u v =
        D.along X (D.along Y h) x u v - D h x (cov.along X Y x) u v := by
    simp only [covariantHessianTwoTensor,
      covariantThreeTensorCovariantDerivative, inducedHomCovariantDerivative,
      dif_pos hfirst, inducedHomAtOfMDiff_apply, sub_apply]
    unfold CovariantDerivative.along
    simp [D, X, Y, smoothExtend_apply]
  have hHYX :
      covariantHessianTwoTensor cov h x X₂ X₁ u v =
        D.along Y (D.along X h) x u v - D h x (cov.along Y X x) u v := by
    simp only [covariantHessianTwoTensor,
      covariantThreeTensorCovariantDerivative, inducedHomCovariantDerivative,
      dif_pos hfirst, inducedHomAtOfMDiff_apply, sub_apply]
    unfold CovariantDerivative.along
    simp [D, X, Y, smoothExtend_apply]
  have htorsionx :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hT
      (X := X) (Y := Y) (x := x) hXmd hYmd
  rw [hHXY, hHYX]
  simp only [CovariantDerivative.curvatureAux_apply,
    CovariantDerivative.along, sub_apply]
  rw [← htorsionx]
  simp only [map_sub, sub_apply]
  ring

/-! Curvature of the induced connection on covariant two-tensors acts with
the negative curvature action in each covariant slot. -/
theorem covariantTwoTensor_curvatureAux_apply_of_contMDiff
    (cov : CovariantDerivative I E TM)
    [hcov : ContMDiffCovariantDerivative cov 1]
    {h : ∀ y : M, T₂ y}
    (hh : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 2
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)))
    {X Y U V : ∀ y : M, TM y}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E))
      2 (fun y => TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E))
      2 (fun y => TotalSpace.mk' E y (Y y)))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E))
      2 (fun y => TotalSpace.mk' E y (U y)))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E))
      2 (fun y => TotalSpace.mk' E y (V y)))
    (x : M) :
    (covariantTwoTensorCovariantDerivative cov).curvatureAux X Y h x
    (U x) (V x) =
    -h x (cov.curvatureAux X Y U x) (V x) -
      h x (U x) (cov.curvatureAux X Y V x) := by
  -- Match the model-space tangent dictionaries used by the induced Hom
  -- connections in `ConnectionLaplacian`; the Riemannian norm is equivalent,
  -- but has different dependent CLM bundle parameters.
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) :=
    PoincareCurvature.instNormedAddCommGroupTangentSpace I
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) :=
    PoincareCurvature.instNormedSpaceTangentSpace I
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let cov₀ := realLineCovariantDerivative (I := I) (M := M)
  let hcov₀ : ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_realLine (I := I) (M := M)
  letI : ContMDiffCovariantDerivative cov₀ 1 := hcov₀
  let cov₁ := covectorCovariantDerivative (I := I) (M := M) cov
  let hcov₁ : ContMDiffCovariantDerivative cov₁ 1 := by
    dsimp [cov₁, covectorCovariantDerivative, cov₀,
      realLineCovariantDerivative, Bundle.Trivial]
    exact @CovariantDerivative.contMDiffCovariantDerivative_inducedHom
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM (Bundle.Trivial M ℝ) _ _ nTM sTM fTM _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      intrinsicTraceScalarFiberBundle intrinsicTraceScalarVectorBundle
      hContTangent intrinsicTraceScalarContMDiffVectorBundle
      cov cov₀ hcov hcov₀
  letI : ContMDiffCovariantDerivative cov₁ 1 := hcov₁
  let cov₂ := covariantTwoTensorCovariantDerivative cov
  let hcov₂ : ContMDiffCovariantDerivative cov₂ 1 := by
    dsimp [cov₂, covariantTwoTensorCovariantDerivative, cov₁,
      covectorCovariantDerivative, cov₀, realLineCovariantDerivative,
      Bundle.Trivial]
    exact @CovariantDerivative.contMDiffCovariantDerivative_inducedHom
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _ nTM sTM fTM
      intrinsicTraceCovectorNormedAddCommGroup intrinsicTraceCovectorNormedSpace
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      intrinsicTraceOneFiberBundle intrinsicTraceOneVectorBundle
      hContTangent intrinsicTraceOneContMDiffVectorBundle
      cov cov₁ hcov hcov₁
  letI : ContMDiffCovariantDerivative cov₂ 1 := hcov₂
  let ψ : ∀ y : M, T₁ y := fun y => h y (U y)
  let f : M → ℝ := fun y => ψ y (V y)
  have hX₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (X y)) :=
    hX.of_le (by norm_num)
  have hY₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (Y y)) :=
    hY.of_le (by norm_num)
  have hψ₂ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (ψ y)) := by
    simpa [ψ] using hh.clm_bundle_apply hU
  have hfTotal : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (f y)) := by
    simpa [f, ψ] using hψ₂.clm_bundle_apply hV
  have hf : ContMDiff I 𝓘(ℝ) 2 f := by
    intro y
    simpa [Bundle.Trivial.eq_trivialization M ℝ,
      Bundle.Trivial.trivialization_apply] using
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) y).contMDiffAt_section_iff
        (n := (2 : WithTop ℕ∞))
        (FiberBundle.mem_baseSet_trivializationAt' y)).mp (hfTotal y)
  have hhAt : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) z (h z)) y := by
    intro y
    exact (hh y).mdifferentiableAt (by norm_num)
  have hψAt : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) z (ψ z)) y := by
    intro y
    exact (hψ₂ y).mdifferentiableAt (by norm_num)
  have hUAt : ∀ y : M, MDiffAt (T% U) y := by
    intro y
    exact (hU y).mdifferentiableAt (by norm_num)
  have hVAt : ∀ y : M, MDiffAt (T% V) y := by
    intro y
    exact (hV y).mdifferentiableAt (by norm_num)
  have hψAlongX : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along X ψ y)) :=
    cov₁.contMDiff_along (n := 1) hX₁ hψ₂
  have hψAlongY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along Y ψ y)) :=
    cov₁.contMDiff_along (n := 1) hY₁ hψ₂
  have hψAlongXAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along X ψ y)) x :=
    (hψAlongX x).mdifferentiableAt (by norm_num)
  have hψAlongYAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (cov₁.along Y ψ y)) x :=
    (hψAlongY x).mdifferentiableAt (by norm_num)
  have hUAlongX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along X U y)) :=
    cov.contMDiff_along (n := 1) hX₁ hU
  have hUAlongY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along Y U y)) :=
    cov.contMDiff_along (n := 1) hY₁ hU
  have hVAlongX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along X V y)) :=
    cov.contMDiff_along (n := 1) hX₁ hV
  have hVAlongY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y => TotalSpace.mk' E y (cov.along Y V y)) :=
    cov.contMDiff_along (n := 1) hY₁ hV
  have hUAlongXVecAt : MDiffAt (T% (cov.along X U)) x :=
    (hUAlongX x).mdifferentiableAt (by norm_num)
  have hUAlongYVecAt : MDiffAt (T% (cov.along Y U)) x :=
    (hUAlongY x).mdifferentiableAt (by norm_num)
  have hVAlongXAt : MDiffAt (T% (cov.along X V)) x :=
    (hVAlongX x).mdifferentiableAt (by norm_num)
  have hVAlongYAt : MDiffAt (T% (cov.along Y V)) x :=
    (hVAlongY x).mdifferentiableAt (by norm_num)
  have hψVAlongXAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (ψ y (cov.along X V y))) x :=
    (hψAt x).clm_bundle_apply hVAlongXAt
  have hψVAlongYAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (ψ y (cov.along Y V y))) x :=
    (hψAt x).clm_bundle_apply hVAlongYAt
  have hHAlongXSection : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along X h y)) :=
    cov₂.contMDiff_along (n := 1) hX₁ hh
  have hHAlongYSection : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along Y h y)) :=
    cov₂.contMDiff_along (n := 1) hY₁ hh
  have hHAlongXAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along X h y)) x :=
    (hHAlongXSection x).mdifferentiableAt (by norm_num)
  have hHAlongYAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (cov₂.along Y h y)) x :=
    (hHAlongYSection x).mdifferentiableAt (by norm_num)
  have hhAlongXUAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (h y (cov.along X U y))) x :=
    (hhAt x).clm_bundle_apply hUAlongXVecAt
  have hhAlongYUAt : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (h y (cov.along Y U y))) x :=
    (hhAt x).clm_bundle_apply hUAlongYVecAt
  have hfAlongX : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) 1
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along X f y)) :=
    cov₀.contMDiff_along (n := 1) hX₁ hfTotal
  have hfAlongY : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) 1
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along Y f y)) :=
    cov₀.contMDiff_along (n := 1) hY₁ hfTotal
  have hfAlongXAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along X f y)) x :=
    (hfAlongX x).mdifferentiableAt (by norm_num)
  have hfAlongYAt : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (cov₀.along Y f y)) x :=
    (hfAlongY x).mdifferentiableAt (by norm_num)
  have hInner := @curvatureAux_inducedHom_apply_at
    E _ _ H _ I M _ _ _ _ _ _
    E ℝ _ _ _ _ _ _
    TM (Bundle.Trivial M ℝ) _ _ nTM sTM fTM
    (fun _ : M => (inferInstance : NormedAddCommGroup ℝ))
    (fun _ : M => (inferInstance : NormedSpace ℝ ℝ))
    (fun _ : M => (inferInstance : FiniteDimensional ℝ ℝ))
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    intrinsicTraceScalarFiberBundle intrinsicTraceScalarVectorBundle
    hContTangent intrinsicTraceScalarContMDiffVectorBundle
    cov cov₀ (φ := ψ) (σ := V) (X := X) (Y := Y) (x := x)
    hψAt hVAt hψAlongXAt hψAlongYAt
    hVAlongXAt hVAlongYAt hfAlongYAt hfAlongXAt
    hψVAlongXAt hψVAlongYAt
  have hflat : cov₀.curvatureAux X Y (fun y => ψ y (V y)) x = 0 := by
    have hscalar : ContMDiff I 𝓘(ℝ) 2 (fun y => ψ y (V y)) := by
      simpa [f] using hf
    have h := extDerivFun_lieBracket_commutator
      (I := I) (f := fun y => ψ y (V y)) (X := X) (Y := Y) (x := x)
      hscalar hX₁ hY₁
    change
      mvfderiv (I := I)
          (fun y => mvfderiv (I := I) (fun z => ψ z (V z)) y (Y y))
          x (X x) -
        mvfderiv (I := I)
          (fun y => mvfderiv (I := I) (fun z => ψ z (V z)) y (X y))
          x (Y x) -
        mvfderiv (I := I) (fun z => ψ z (V z)) x
          (VectorField.mlieBracket I X Y x) = 0
    exact h
  have hInner' :
      cov₁.curvatureAux X Y ψ x (V x) =
        -ψ x (cov.curvatureAux X Y V x) := by
    have hInner₀ :
        cov₁.curvatureAux X Y ψ x (V x) =
        cov₀.curvatureAux X Y (fun y => ψ y (V y)) x -
            ψ x (cov.curvatureAux X Y V x) := by
      exact hInner
    calc
      cov₁.curvatureAux X Y ψ x (V x) =
          cov₀.curvatureAux X Y (fun y => ψ y (V y)) x -
            ψ x (cov.curvatureAux X Y V x) := hInner₀
      _ = -ψ x (cov.curvatureAux X Y V x) := by
        simpa [hflat]
  have hOuter := @curvatureAux_inducedHom_apply_at
    E _ _ H _ I M _ _ _ _ _ _
    E (E →L[ℝ] ℝ) _ _ _ _ _ _
    TM T₁ _ _ nTM sTM fTM
    intrinsicTraceCovectorNormedAddCommGroup intrinsicTraceCovectorNormedSpace _
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    intrinsicTraceOneFiberBundle intrinsicTraceOneVectorBundle
    hContTangent intrinsicTraceOneContMDiffVectorBundle
    cov cov₁ (φ := h) (σ := U) (X := X) (Y := Y) (x := x)
    hhAt hUAt hHAlongXAt hHAlongYAt
    hUAlongXVecAt hUAlongYVecAt hψAlongYAt hψAlongXAt
    hhAlongXUAt hhAlongYUAt
  have hOuterV := congrArg (fun α : T₁ x => α (V x)) hOuter
  have hOuterAction :
      (covariantTwoTensorCovariantDerivative cov).curvatureAux X Y h x
          (U x) (V x) =
        (cov₁.curvatureAux X Y ψ x -
          h x (cov.curvatureAux X Y U x)) (V x) := by
    exact hOuterV
  calc
    (covariantTwoTensorCovariantDerivative cov).curvatureAux X Y h x
        (U x) (V x) =
      cov₁.curvatureAux X Y ψ x (V x) -
        h x (cov.curvatureAux X Y U x) (V x) := by
          simpa only [ContinuousLinearMap.sub_apply] using hOuterAction
      _ = -h x (cov.curvatureAux X Y U x) (V x) -
        h x (U x) (cov.curvatureAux X Y V x) := by
          rw [hInner']
          simp only [ψ]
          ring

/-! Combining the intrinsic Hessian commutator with the induced-curvature
action yields the component commutator used in the Hamilton--Ivey trace
calculation.  The only extra input is spatial C² regularity of the actual
Ricci two-tensor; the commutator identity itself is derived. -/
theorem intrinsicHamiltonIveyTrace_hHcomm
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x)
    (hRicci₂ : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 2
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)))
    (e : letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      OrthonormalBasis (Fin 3) ℝ (TM x)) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ a b c d,
      covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
          (e a) (e b) (e c) (e d) -
        covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
          (e b) (e a) (e c) (e d) =
        -∑ l,
          (Inner.inner ℝ
              ((cov t).curvatureTensor x (e a) (e b) (e c)) (e l) *
            CovariantDerivative.ricciCurvature (cov := cov t) x (e l) (e d) +
          Inner.inner ℝ
              ((cov t).curvatureTensor x (e a) (e b) (e d)) (e l) *
            CovariantDerivative.ricciCurvature (cov := cov t) x (e c) (e l)) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  rcases hregular with ⟨_, hfirst, _, _⟩
  intro a b c d
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e a)
  let Y : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e b)
  let U : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e c)
  let V : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e d)
  have hX₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X) := by
    simpa [X] using
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e a))
  have hY₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y) := by
    simpa [Y] using
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e b))
  have hU₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% U) := by
    simpa [U] using
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e c))
  have hV₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% V) := by
    simpa [V] using
      (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e d))
  have hXmd : MDiffAt (T% X) x :=
    (hX₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2) x).mdifferentiableAt
      one_ne_zero
  have hYmd : MDiffAt (T% Y) x :=
    (hY₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2) x).mdifferentiableAt
      one_ne_zero
  have hcomm :=
    covariantHessianTwoTensor_firstSlot_commutator
      (cov := cov t) (hfirst := hfirst) (hT := (hLevi t).1)
      (X₁ := e a) (X₂ := e b) hXmd hYmd (e c) (e d)
  have hAction :=
    covariantTwoTensor_curvatureAux_apply_of_contMDiff
      (cov := cov t)
      (h := CovariantDerivative.ricciCovariantTwoTensor (cov t))
      (hh := hRicci₂)
      (X := X) (Y := Y) (U := U) (V := V)
      hX₂ hY₂ hU₂ hV₂ x
  have hAction' :
      (covariantTwoTensorCovariantDerivative (cov t)).curvatureAux
          X Y (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (e c) (e d) =
        -CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            ((cov t).curvatureTensor x (e a) (e b) (e c)) (e d) -
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x (e c)
            ((cov t).curvatureTensor x (e a) (e b) (e d)) := by
    simpa [X, Y, U, V, CovariantDerivative.curvatureTensor_apply,
      smoothExtend_apply] using hAction
  have hcomm' :
      covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
          (e a) (e b) (e c) (e d) -
        covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
          (e b) (e a) (e c) (e d) =
        -CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            ((cov t).curvatureTensor x (e a) (e b) (e c)) (e d) -
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x (e c)
            ((cov t).curvatureTensor x (e a) (e b) (e d)) := by
    calc
      _ = (covariantTwoTensorCovariantDerivative (cov t)).curvatureAux
            X Y (CovariantDerivative.ricciCovariantTwoTensor (cov t))
            x (e c) (e d) := hcomm
      _ = _ := hAction'
  have hExpandLeft (w v : TM x) :
      CovariantDerivative.ricciCovariantTwoTensor (cov t) x w v =
        ∑ l, Inner.inner ℝ w (e l) *
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x (e l) v := by
    calc
      CovariantDerivative.ricciCovariantTwoTensor (cov t) x w v =
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x
          (∑ l, Inner.inner ℝ (e l) w • e l) v := by
        rw [e.sum_repr' w]
      _ = ∑ l, Inner.inner ℝ w (e l) *
            CovariantDerivative.ricciCovariantTwoTensor (cov t) x (e l) v := by
        simp [map_sum, map_smul, ContinuousLinearMap.smul_apply,
          smul_eq_mul, real_inner_comm]
  have hExpandRight (u w : TM x) :
      CovariantDerivative.ricciCovariantTwoTensor (cov t) x u w =
        ∑ l, Inner.inner ℝ w (e l) *
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x u (e l) := by
    calc
      CovariantDerivative.ricciCovariantTwoTensor (cov t) x u w =
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x u
          (∑ l, Inner.inner ℝ (e l) w • e l) := by
        rw [e.sum_repr' w]
      _ = ∑ l, Inner.inner ℝ w (e l) *
            CovariantDerivative.ricciCovariantTwoTensor (cov t) x u (e l) := by
        simp [map_sum, map_smul, ContinuousLinearMap.smul_apply,
          smul_eq_mul, real_inner_comm]
  calc
    _ = -CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            ((cov t).curvatureTensor x (e a) (e b) (e c)) (e d) -
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x (e c)
            ((cov t).curvatureTensor x (e a) (e b) (e d)) := hcomm'
    _ = -∑ l,
          (Inner.inner ℝ
              ((cov t).curvatureTensor x (e a) (e b) (e c)) (e l) *
            CovariantDerivative.ricciCovariantTwoTensor (cov t) x (e l) (e d) +
          Inner.inner ℝ
              ((cov t).curvatureTensor x (e a) (e b) (e d)) (e l) *
            CovariantDerivative.ricciCovariantTwoTensor (cov t) x (e c) (e l)) := by
      rw [hExpandLeft, hExpandRight]
      rw [Finset.sum_add_distrib]
      simp only [mul_comm (Inner.inner ℝ _ _)]
      ring

/-! Pair the actual Ricci connection variation with the metric and
differentiate its cyclic-Ricci formula.  This derives the component formula
for the genuine curvature velocity; the only additional inputs are
differentiability of the actual connection-variation field and the
Hessian regularity already recorded above. -/
theorem intrinsicHamiltonIveyTrace_hRawComponent_of_connectionRegularity
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x)
    (hAregular : ∀ u v : TM x,
      MDiffAt
        (T% (fun y : M =>
          intrinsicRicciConnectionVariation g cov t (hcov t) y
            (smoothExtend (I := I) (F := E) (V := TM) x u y)
            (smoothExtend (I := I) (F := E) (V := TM) x v y))) x)
    (e : letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      OrthonormalBasis (Fin 3) ℝ (TM x))
    (a b c d : Fin 3) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    Inner.inner ℝ
        (TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
          (I := I) (M := M) cov
          (intrinsicRicciConnectionVariation g cov t (hcov t))
          t x (e a) (e b) (e c)) (e d) =
      -covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (e a) (e b) (e c) (e d) -
        covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (e a) (e c) (e b) (e d) +
        covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (e a) (e d) (e b) (e c) +
        covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (e b) (e a) (e c) (e d) +
        covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (e b) (e c) (e a) (e d) -
        covariantHessianTwoTensor (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (e b) (e d) (e a) (e c) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  rcases hregular with ⟨_, hfirst, _, _⟩
  let Ric : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ :=
    fun y => CovariantDerivative.ricciCovariantTwoTensor (cov t) y
  let D : ∀ y : M, TM y →L[ℝ] (TM y →L[ℝ] (TM y →L[ℝ] ℝ)) :=
    fun y => CovariantDerivative.covariantTwoTensorCovariantDerivative
      (cov t) Ric y
  let A : ∀ y : M, TM y → TM y → TM y :=
    fun y => intrinsicRicciConnectionVariation g cov t (hcov t) y
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e a)
  let Y : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e b)
  let Z : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e c)
  let W : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x (e d)
  let qA : M → ℝ := fun y => Inner.inner ℝ (A y (Y y) (Z y)) (W y)
  let qB : M → ℝ := fun y => Inner.inner ℝ (A y (X y) (Z y)) (W y)
  let q1 : M → ℝ := fun y => D y (Y y) (Z y) (W y)
  let q2 : M → ℝ := fun y => D y (Z y) (Y y) (W y)
  let q3 : M → ℝ := fun y => D y (W y) (Y y) (Z y)
  let r1 : M → ℝ := fun y => D y (X y) (Z y) (W y)
  let r2 : M → ℝ := fun y => D y (Z y) (X y) (W y)
  let r3 : M → ℝ := fun y => D y (W y) (X y) (Z y)
  have hX : MDiffAt (T% X) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e a)).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hY : MDiffAt (T% Y) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e b)).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hZ : MDiffAt (T% Z) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e c)).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hW : MDiffAt (T% W) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x (e d)).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hAYZ : MDiffAt (T% (fun y => A y (Y y) (Z y))) x := by
    simpa [A, Y, Z] using hAregular (e b) (e c)
  have hAXZ : MDiffAt (T% (fun y => A y (X y) (Z y))) x := by
    simpa [A, X, Z] using hAregular (e a) (e c)
  have hPair (u v w : TM x) :
      Inner.inner ℝ (A x u v) w =
        -(D x u v w + D x v u w - D x w u v) := by
    simpa [A, D, Ric, intrinsicRicciConnectionVariation] using
      (cyclicCovariantTensorVariationVector_inner
        (cov := cov t)
        (h := fun y => CovariantDerivative.ricciCovariantTwoTensor (cov t) y)
        x u v w)
  have hEval (U V₁ W₁ : ∀ y : M, TM y)
      (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V₁) x)
      (hW₁ : MDiffAt (T% W₁) x) :
      MDiffAt (fun y => D y (U y) (V₁ y) (W₁ y)) x := by
    let q : M → ℝ := fun y => D y (U y) (V₁ y) (W₁ y)
    have hDU := hfirst.clm_bundle_apply hU
    have hDUV := hDU.clm_bundle_apply hV
    have htotal := hDUV.clm_bundle_apply hW₁
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I q (FiberBundle.mem_baseSet_trivializationAt' x)).mp htotal
    simpa [Bundle.Trivial.eq_trivialization M ℝ, q, D] using ht
  have hDderiv (U V₁ W₁ : ∀ y : M, TM y)
      (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V₁) x)
      (hW₁ : MDiffAt (T% W₁) x) (v : TM x) :
      mvfderiv (I := I) (fun y => D y (U y) (V₁ y) (W₁ y)) x v =
        CovariantDerivative.covariantThreeTensorCovariantDerivative
            (cov t) D x v (U x) (V₁ x) (W₁ x) +
          D x ((cov t) U x v) (V₁ x) (W₁ x) +
          D x (U x) ((cov t) V₁ x v) (W₁ x) +
          D x (U x) (V₁ x) ((cov t) W₁ x v) := by
    simpa [D, CovariantDerivative.realLineCovariantDerivative,
      CovariantDerivative.trivialCovariantDerivative_apply] using
      (CovariantDerivative.realLineCovariantDerivative_trilinear
        (cov := cov t) (A := D) (X := U) (U := V₁) (V := W₁)
        hfirst hU hV hW₁ v)
  have hqAfun : qA = q3 - q2 - q1 := by
    funext y
    have hp :=
      cyclicCovariantTensorVariationVector_inner
        (cov := cov t)
        (h := fun z => CovariantDerivative.ricciCovariantTwoTensor (cov t) z)
        y (Y y) (Z y) (W y)
    have hp' : qA y = -(q1 y + q2 y - q3 y) := by
      simpa [qA, q1, q2, q3, A, D, Ric,
        intrinsicRicciConnectionVariation] using hp
    rw [hp']
    change -(q1 y + q2 y - q3 y) = q3 y - q2 y - q1 y
    ring
  have hqBfun : qB = r3 - r2 - r1 := by
    funext y
    have hp :=
      cyclicCovariantTensorVariationVector_inner
        (cov := cov t)
        (h := fun z => CovariantDerivative.ricciCovariantTwoTensor (cov t) z)
        y (X y) (Z y) (W y)
    have hp' : qB y = -(r1 y + r2 y - r3 y) := by
      simpa [qB, r1, r2, r3, A, D, Ric,
        intrinsicRicciConnectionVariation] using hp
    rw [hp']
    change -(r1 y + r2 y - r3 y) = r3 y - r2 y - r1 y
    ring
  have hq1 : MDiffAt q1 x := hEval Y Z W hY hZ hW
  have hq2 : MDiffAt q2 x := hEval Z Y W hZ hY hW
  have hq3 : MDiffAt q3 x := hEval W Y Z hW hY hZ
  have hr1 : MDiffAt r1 x := hEval X Z W hX hZ hW
  have hr2 : MDiffAt r2 x := hEval Z X W hZ hX hW
  have hr3 : MDiffAt r3 x := hEval W X Z hW hX hZ
  have hscalarA :
      mvfderiv (I := I) qA x (e a) =
        mvfderiv (I := I) q3 x (e a) -
          mvfderiv (I := I) q2 x (e a) -
          mvfderiv (I := I) q1 x (e a) := by
    rw [hqAfun, mvfderiv_sub (hq3.sub hq2) hq1,
      mvfderiv_sub hq3 hq2]
    simp only [ContinuousLinearMap.sub_apply]
  have hscalarB :
      mvfderiv (I := I) qB x (e b) =
        mvfderiv (I := I) r3 x (e b) -
          mvfderiv (I := I) r2 x (e b) -
          mvfderiv (I := I) r1 x (e b) := by
    rw [hqBfun, mvfderiv_sub (hr3.sub hr2) hr1,
      mvfderiv_sub hr3 hr2]
    simp only [ContinuousLinearMap.sub_apply]
  have hD1 := hDderiv Y Z W hY hZ hW (e a)
  have hD2 := hDderiv Z Y W hZ hY hW (e a)
  have hD3 := hDderiv W Y Z hW hY hZ (e a)
  have hD4 := hDderiv X Z W hX hZ hW (e b)
  have hD5 := hDderiv Z X W hZ hX hW (e b)
  have hD6 := hDderiv W X Z hW hX hZ (e b)
  have hprodA :
      mvfderiv (I := I) qA x (e a) =
        Inner.inner ℝ
            ((cov t).along X (fun y => A y (Y y) (Z y)) x) (e d) +
          Inner.inner ℝ (A x (e b) (e c))
            ((cov t).along X W x) := by
    simpa [qA, A, X, Y, Z, W, CovariantDerivative.along,
      smoothExtend_apply] using (hLevi t).2 hAYZ hW (e a)
  have hprodB :
      mvfderiv (I := I) qB x (e b) =
        Inner.inner ℝ
            ((cov t).along Y (fun y => A y (X y) (Z y)) x) (e d) +
          Inner.inner ℝ (A x (e a) (e c))
            ((cov t).along Y W x) := by
    simpa [qB, A, X, Y, Z, W, CovariantDerivative.along,
      smoothExtend_apply] using (hLevi t).2 hAXZ hW (e b)
  have hprodA' :
      Inner.inner ℝ
          ((cov t).along X (fun y => A y (Y y) (Z y)) x) (e d) =
        mvfderiv (I := I) qA x (e a) -
          Inner.inner ℝ (A x (e b) (e c))
            ((cov t).along X W x) := by
    linarith [hprodA]
  have hprodB' :
      Inner.inner ℝ
          ((cov t).along Y (fun y => A y (X y) (Z y)) x) (e d) =
        mvfderiv (I := I) qB x (e b) -
          Inner.inner ℝ (A x (e a) (e c))
            ((cov t).along Y W x) := by
    linarith [hprodB]
  have hTorsion :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := cov t)).mp
      (hLevi t).1 (X := X) (Y := Y) (x := x) hX hY
  have hvelocity :
      Inner.inner ℝ
          (TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
            (I := I) (M := M) cov A t x (e a) (e b) (e c)) (e d) =
        Inner.inner ℝ
            ((cov t).along X (fun y => A y (Y y) (Z y)) x) (e d) +
          Inner.inner ℝ (A x (e a) ((cov t).along Y Z x)) (e d) -
          Inner.inner ℝ
            ((cov t).along Y (fun y => A y (X y) (Z y)) x) (e d) -
          Inner.inner ℝ (A x (e b) ((cov t).along X Z x)) (e d) -
          Inner.inner ℝ
            (A x (VectorField.mlieBracket I X Y x) (e c)) (e d) := by
    calc
      _ = Inner.inner ℝ
          (((cov t).along X (fun y => A y (Y y) (Z y)) x +
                A x (e a) ((cov t).along Y Z x)) -
              ((cov t).along Y (fun y => A y (X y) (Z y)) x +
                A x (e b) ((cov t).along X Z x)) -
            A x (VectorField.mlieBracket I X Y x) (e c)) (e d) := by
        simp [TimeDependentCovariantDerivative.curvatureTensorTimeVelocity,
          X, Y, Z, smoothExtend_apply]
      _ = _ := by
        simp only [inner_sub_left, inner_add_left]
        ring
  rw [hvelocity, hprodA', hprodB', hscalarA, hscalarB,
    hD3, hD2, hD1, hD6, hD5, hD4]
  simp only [hPair]
  rw [← hTorsion]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  simp [CovariantDerivative.covariantHessianTwoTensor, D, Ric, X, Y, Z, W,
    smoothExtend_apply, CovariantDerivative.along] <;> ring_nf

end CovariantDerivative.TimeDependentRiemannianMetric
