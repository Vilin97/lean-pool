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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyGeometricEvolution
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyDerivedMovingConnectionVariation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicTraceGeometry

/-!
# Hamilton--Ivey evolution from intrinsic Ricci flow and mixed regularity

This module composes the actual mixed-regularity curvature derivative with
the three-dimensional geometric contraction calculation.  The caller supplies
only regularity data for the metric and nested covariant-derivative sections,
not a connection-variation formula or the curvature evolution equation.

`IsRicciFlowOn` is intentionally kept unchanged: it is slicewise and does not
imply the mixed spacetime regularity below.  The derived evolution theorem is
therefore conditional on that genuine analytic regularity.
-/

@[expose] public section

noncomputable section

open Bundle
open Filter Set Topology
open scoped BigOperators Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual regularity needed by the intrinsic moving-section curvature
derivative.  The fields are spacetime regularity of metric pairings, C²
regularity of each connection slice, and regularity of the two nested
covariant-derivative sections in the curvature commutator.  No derivative or
evolution identity is included. -/
structure HamiltonIveyIntrinsicCurvatureVariationRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov) (t : ℝ) : Prop where
  connectionC2 : ContMDiffCovariantDerivative
    (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 2
  jointMetricTensor : ContMDiff (𝓘(ℝ).prod I)
    (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
    (fun p : ℝ × M => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2))
  nestedYZ : ∀ (x : M) (a b c : TM x),
    IntrinsicRicciMovingSectionRegularity g t x
      (smoothExtend (I := I) (F := E) (V := TM) x a)
      (fun τ : ℝ => (cov τ).along
        (smoothExtend (I := I) (F := E) (V := TM) x b)
        (smoothExtend (I := I) (F := E) (V := TM) x c))
      (fun y : M => intrinsicRicciConnectionVariation g cov t (hcov t) y
        (smoothExtend (I := I) (F := E) (V := TM) x b y)
        (smoothExtend (I := I) (F := E) (V := TM) x c y))
  nestedXZ : ∀ (x : M) (a b c : TM x),
    IntrinsicRicciMovingSectionRegularity g t x
      (smoothExtend (I := I) (F := E) (V := TM) x b)
      (fun τ : ℝ => (cov τ).along
        (smoothExtend (I := I) (F := E) (V := TM) x a)
        (smoothExtend (I := I) (F := E) (V := TM) x c))
      (fun y : M => intrinsicRicciConnectionVariation g cov t (hcov t) y
        (smoothExtend (I := I) (F := E) (V := TM) x a y)
        (smoothExtend (I := I) (F := E) (V := TM) x c y))

/-- Higher *spatial* regularity used by the Ricci-trace contractions at a
fixed flow time.  These fields are kept separate from `IsRicciFlowOn`: that
predicate is slicewise and does not currently derive them.  In particular,
`connectionC2` is required at every slice by the existing contracted-Bianchi
argument, while the remaining fields concern the selected slice `t`. -/
structure HamiltonIveyIntrinsicSliceRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov) (t : ℝ) : Prop where
  connectionC2 : ∀ τ : ℝ, ContMDiffCovariantDerivative
    (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 2
  metricC2 :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    IsContMDiffRiemannianBundle I 2 E TM
  trace : ∀ x : M, intrinsicRicciTraceRegularity g cov hcov hLevi t x
  scalarC2 :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 1 E TM :=
      g.slice_isContMDiffRiemannianBundle t
    letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
    ContMDiff I 𝓘(ℝ) 2
      (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
  ricciC2 :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 2
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := fun z : M => TM z →L[ℝ] (TM z →L[ℝ] ℝ)) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y))

/-! The lowered connection variation is the cyclic covariant derivative of
the actual Ricci tensor.  Differentiating its pairing, using metric
compatibility and torsion-freeness, gives the Hessian contraction in the
Ricci trace of the actual curvature velocity. -/
theorem intrinsicHamiltonIveyTrace_hRawComponent
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x)
    (hvariation : HamiltonIveyIntrinsicCurvatureVariationRegularity
      g cov hcov hLevi t)
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
  have hAregular (u v : TM x) :
      MDiffAt
        (T% (fun y : M =>
          intrinsicRicciConnectionVariation g cov t (hcov t) y
            (smoothExtend (I := I) (F := E) (V := TM) x u y)
            (smoothExtend (I := I) (F := E) (V := TM) x v y))) x := by
    have hspatial :=
      (hvariation.nestedYZ x u u v).spatialVelocity
    have hspatial' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y => TotalSpace.mk' E y
          (intrinsicRicciConnectionVariation g cov t (hcov t) y
            (smoothExtend (I := I) (F := E) (V := TM) x u y)
            (smoothExtend (I := I) (F := E) (V := TM) x v y))) := by
      simpa using hspatial
    exact (hspatial' x).mdifferentiableAt one_ne_zero
  exact intrinsicHamiltonIveyTrace_hRawComponent_of_connectionRegularity
    (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
    (t := t) (x := x) hregular hAregular e a b c d
theorem intrinsicHamiltonIveyTrace_hRaw
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (t : ℝ) (x : M)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x)
    (hvariation : HamiltonIveyIntrinsicCurvatureVariationRegularity
      g cov hcov hLevi t)
    (e : letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      OrthonormalBasis (Fin 3) ℝ (TM x))
    (curvatureVelocity : ∀ z : M,
      TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hvelocity : ∀ (z : M) (a b c : TM z),
      curvatureVelocity z a b c =
        TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
          (I := I) (M := M) cov
          (intrinsicRicciConnectionVariation g cov t (hcov t))
          t z a b c) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ i j,
      curvatureTensorVelocityRicci curvatureVelocity x (e i) (e j) =
        ∑ k,
          (-covariantHessianTwoTensor (cov t)
                (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
                (e k) (e i) (e j) (e k) -
            covariantHessianTwoTensor (cov t)
                (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
                (e k) (e j) (e i) (e k) +
            covariantHessianTwoTensor (cov t)
                (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
                (e k) (e k) (e i) (e j) +
            covariantHessianTwoTensor (cov t)
                (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
                (e i) (e k) (e j) (e k) +
            covariantHessianTwoTensor (cov t)
                (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
                (e i) (e j) (e k) (e k) -
            covariantHessianTwoTensor (cov t)
                (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
                (e i) (e k) (e k) (e j)) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  intro i j
  change LinearMap.trace ℝ (TM x)
      (curvatureTensorVelocityEndomorphism curvatureVelocity x (e i) (e j)) = _
  rw [LinearMap.trace_eq_sum_inner _ e]
  change ∑ k, Inner.inner ℝ (e k)
      (curvatureVelocity x (e k) (e i) (e j)) = _
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [hvelocity]
  simpa [real_inner_comm] using intrinsicHamiltonIveyTrace_hRawComponent
    (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
    (t := t) (x := x) hregular hvariation e k i j k

/-! The elementary fields of the three-dimensional Ricci-trace contraction
package are filled from the actual slice curvature and Ricci Hessian.  The
Hessian commutator and the trace of the differentiated curvature commutator
are derived from actual-Ricci regularity and the moving connection variation.
The constructor chooses the genuine Ricci-complement eigenbasis for its
contractions, and derives the algebraic reaction components there. -/
def HamiltonIveyRicciTraceContractions.of_intrinsicFields
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (curvatureVelocity : ∀ z : M,
      TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (t : ℝ) (x : M)
    (hcov₂ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 2)
    (hmetric₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 2 E TM)
    (hregular : intrinsicRicciTraceRegularity g cov hcov hLevi t x)
    (hscalar :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle I 1 E TM :=
        g.slice_isContMDiffRiemannianBundle t
      letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
      ContMDiff I 𝓘(ℝ) 2
        (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y))
    (hRicci₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      ContMDiff I
        (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) 2
        (fun y => TotalSpace.mk'
          (E →L[ℝ] (E →L[ℝ] ℝ))
          (E := fun z : M => TM z →L[ℝ] (TM z →L[ℝ] ℝ)) y
          (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)))
    (hvariation : HamiltonIveyIntrinsicCurvatureVariationRegularity
      g cov hcov hLevi t)
    (hvelocity : ∀ (z : M) (a b c : TM z),
      curvatureVelocity z a b c =
        TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
          (I := I) (M := M) cov
          (intrinsicRicciConnectionVariation g cov t (hcov t))
          t z a b c) :
    HamiltonIveyRicciTraceContractions
      g cov hcov hLevi hdim curvatureVelocity t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  letI : IsContMDiffRiemannianBundle I 2 E TM := hmetric₂
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let e : OrthonormalBasis (Fin 3) ℝ (TM x) :=
    CovariantDerivative.ricciComplementEigenbasis
      (I := I) (M := M) (E := E) (cov t)
      (hLevi t).1 (hLevi t).2 x (hdim x)
  let b : Module.Basis (Fin 3) ℝ (TM x) := e.toBasis
  let K : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b c d =>
    Inner.inner ℝ ((cov t).curvatureTensor x (e a) (e b) (e c)) (e d)
  let Ric : Fin 3 → Fin 3 → ℝ := fun a b =>
    CovariantDerivative.ricciCurvature (cov := cov t) x (e a) (e b)
  let Scal : ℝ := CovariantDerivative.scalarCurvature (cov := cov t) x
  let H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b c d =>
    covariantHessianTwoTensor (cov t)
      (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x
      (e a) (e b) (e c) (e d)
  let S : Fin 3 → Fin 3 → ℝ := fun a b =>
    CovariantDerivative.scalarHessian (cov t)
      (fun y => CovariantDerivative.scalarCurvature (cov := cov t) y)
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
  have hRicciTensorSymm : ∀ y : M, ∀ u v : TM y,
      CovariantDerivative.ricciCovariantTwoTensor (cov t) y u v =
        CovariantDerivative.ricciCovariantTwoTensor (cov t) y v u := by
    intro y u v
    exact CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
      (cov := cov t) (hLevi t) y u v
  have hHlast : ∀ a b c d, H a b c d = H a b d c := by
    intro a b c d
    simpa [H] using
      (CovariantDerivative.covariantHessianTwoTensor_swap
        (cov t) hRicciTensorSymm x (e a) (e b) (e c) (e d))
  have hTrace : ∀ a b, ∑ i, H a b i i = S a b := by
    intro a b
    simpa [H, S] using
      (intrinsicHamiltonIveyTrace_hTrace
        (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
        (hdim := hdim) (t := t) (x := x) hregular e a b)
  have hSsymm : ∀ a b, S a b = S b a := by
    intro a b
    simpa [S] using
      (intrinsicHamiltonIveyTrace_hSsymm
        (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
        (t := t) (x := x) hregular hscalar e a b)
  have hDiv : ∀ a b, ∑ i, H a i b i = (1 / 2 : ℝ) * S a b := by
    intro a b
    simpa [H, S] using
      (intrinsicHamiltonIveyTrace_hDiv
        (g := g) (cov := cov) (hcov := hcov) (hcov₂ := hcov₂)
        (hLevi := hLevi) (t := t) (x := x) hmetric₂ hregular e a b)
  have hLaplacian : ∀ i j,
      ∑ k, H k k i j =
        connectionLaplacian (cov t)
          (fun y => CovariantDerivative.ricciCovariantTwoTensor (cov t) y)
          x (b i) (b j) := by
    intro i j
    simpa [H, b] using
      (intrinsicHamiltonIveyTrace_hLaplacian
        (g := g) (cov := cov) (hcov := hcov) (t := t) (x := x)
        e i j).symm
  have hRaw := intrinsicHamiltonIveyTrace_hRaw
    (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
    (t := t) (x := x) hregular hvariation e curvatureVelocity hvelocity
  have hHcomm' : ∀ a b c d,
      H a b c d - H b a c d =
        -∑ l, (K a b c l * Ric l d + K a b d l * Ric c l) := by
    intro a b c d
    simpa [H, K, Ric] using
      (intrinsicHamiltonIveyTrace_hHcomm
        (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
        (t := t) (x := x) hregular hRicci₂ e a b c d)
  have hRaw' : ∀ i j,
      curvatureTensorVelocityRicci curvatureVelocity x (b i) (b j) =
        ∑ k, (-H k i j k - H k j i k + H k k i j +
          H i k j k + H i j k k - H i k k j) := by
    intro i j
    simpa [H, b] using hRaw i j
  let eig : Fin 3 → ℝ := fun i =>
    g.curvatureEigenvalues cov hcov hLevi hdim t x i
  let lam : ℝ := g.curvatureLambda cov hcov hLevi hdim t x
  let mu : ℝ := g.curvatureMu cov hcov hLevi hdim t x
  let nu : ℝ := g.curvatureNu cov hcov hLevi hdim t x
  let e2 : ℝ := lam * mu + lam * nu + mu * nu
  have hsumEig : lam + mu + nu = Scal := by
    simpa [lam, mu, nu, Scal] using
      g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
        cov hcov hLevi hdim t x
  have hnormEig :
      2 * g.ricciNormSq cov hcov t x =
        lam ^ 2 + mu ^ 2 + nu ^ 2 + e2 := by
    have h := g.two_mul_ricciNormSq_eq_hamiltonIveyScalarReaction
      cov hcov hLevi hdim t x
    dsimp [HamiltonIveyReaction.scalarReaction, lam, mu, nu, e2] at h ⊢
    nlinarith [h]
  have he2Norm : e2 = Scal ^ 2 - 2 * g.ricciNormSq cov hcov t x := by
    rw [← hsumEig]
    nlinarith [hnormEig]
  have hA : ∀ j : Fin 3,
      CovariantDerivative.ricciComplementEndomorphism (cov t) x (e j) =
        eig j • e j := by
    intro j
    have h := CovariantDerivative.ricciComplementEndomorphism_apply_eigenbasis
      (I := I) (M := M) (E := E) (cov t)
      (hLevi t).1 (hLevi t).2 x (hdim x) j
    simpa [e, eig, curvatureEigenvalues] using h
  have hRaisedRicci : ∀ i j : Fin 3,
      Inner.inner ℝ (e i)
          (CovariantDerivative.raisedRicciEndomorphism (cov t) x (e j)) =
        Ric i j := by
    intro i j
    calc
      Inner.inner ℝ (e i)
          (CovariantDerivative.raisedRicciEndomorphism (cov t) x (e j)) =
        Inner.inner ℝ
          (CovariantDerivative.raisedRicciEndomorphism (cov t) x (e j)) (e i) :=
            real_inner_comm _ _
      _ = CovariantDerivative.ricciCurvature (cov := cov t) x (e j) (e i) :=
        CovariantDerivative.inner_raisedRicciEndomorphism
          (cov t) x (e j) (e i)
      _ = Ric j i := rfl
      _ = Ric i j := hRicSymm j i
  have hAComponent : ∀ i j : Fin 3,
      Inner.inner ℝ (e i)
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (e j)) =
        Scal * (if i = j then 1 else 0) - 2 * Ric i j := by
    intro i j
    rw [CovariantDerivative.ricciComplementEndomorphism_apply]
    simp only [inner_sub_right, real_inner_smul_right]
    rw [hRaisedRicci i j, e.inner_eq_ite]
  have hAComponentEigen : ∀ i j : Fin 3,
      Inner.inner ℝ (e i)
          (CovariantDerivative.ricciComplementEndomorphism (cov t) x (e j)) =
        eig j * (if i = j then 1 else 0) := by
    intro i j
    rw [hA j]
    simp [real_inner_smul_right, e.inner_eq_ite]
  have hRicciComponent : ∀ i j : Fin 3,
      Ric i j = (Scal - eig j) / 2 * (if i = j then 1 else 0) := by
    intro i j
    have h := (hAComponent i j).symm.trans (hAComponentEigen i j)
    nlinarith [h]
  have hInner : ∀ i j : Fin 3,
      (g t).inner x (e i) (e j) = (if i = j then 1 else 0) := by
    intro i j
    change Inner.inner ℝ (e i) (e j) = _
    exact e.inner_eq_ite i j
  have hInnerScale : ∀ i j : Fin 3, ∀ c : ℝ,
      (g t).inner x (e i) (c • e j) =
        c * (if i = j then 1 else 0) := by
    intro i j c
    change Inner.inner ℝ (e i) (c • e j) = _
    simp [real_inner_smul_right, e.inner_eq_ite]
  have hQEndo : ∀ j : Fin 3,
      curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t x (e j) =
        (2 * eig j ^ 2 - Scal * eig j + e2) • e j := by
    intro j
    have h := g.curvatureOperatorReactionEndomorphism_apply_curvatureEigenbasis
      cov hcov hLevi hdim t x j
    simpa [e, eig, Scal, e2, lam, mu, nu, curvatureEigenbasisVector] using h
  have hQComponent : ∀ i j : Fin 3,
      curvatureOperatorReaction g cov hcov hLevi hdim t x (e i) (e j) =
        (if i = j then
          3 * eig i ^ 2 - 2 * Scal * eig i + e2 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst j
      have h := g.curvatureOperatorReaction_apply_curvatureEigenbasis
        cov hcov hLevi hdim t x i
      simpa [e, eig, Scal, e2, lam, mu, nu, curvatureEigenbasisVector] using h
    · rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci,
        hQEndo j]
      unfold curvatureEndomorphismApply
      rw [hA j]
      have hRicciScale :
          g.ricciCurvature cov hcov t x (e i) (eig j • e j) =
            eig j * Ric i j := by
        change CovariantDerivative.ricciCurvature (cov := cov t) x
            (e i) (eig j • e j) =
          eig j * CovariantDerivative.ricciCurvature (cov := cov t) x
            (e i) (e j)
        rw [map_smul]
        rfl
      rw [hInnerScale i j (2 * eig j ^ 2 - Scal * eig j + e2),
        hRicciScale, hRicciComponent i j]
      simp [hij]
  have hRicciProduct : ∀ i j : Fin 3,
      ∑ l, Ric i l * Ric l j =
        (if i = j then ((Scal - eig i) / 2) ^ 2 else 0) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three, hRicciComponent] <;> ring
  have hRicciSquares :
      ∑ p, ∑ q, (Ric p q) ^ 2 =
        ∑ i : Fin 3, ((Scal - eig i) / 2) ^ 2 := by
    simp [Fin.sum_univ_three, hRicciComponent] <;> ring
  have hRicciNormComponents :
      ∑ p, ∑ q, (Ric p q) ^ 2 = g.ricciNormSq cov hcov t x := by
    rw [hRicciSquares, Fin.sum_univ_three]
    have heig0 : eig 0 = lam := rfl
    have heig1 : eig 1 = mu := rfl
    have heig2 : eig 2 = nu := rfl
    rw [heig0, heig1, heig2]
    have hsumSquares :
        ((Scal - lam) / 2) ^ 2 + ((Scal - mu) / 2) ^ 2 +
            ((Scal - nu) / 2) ^ 2 = g.ricciNormSq cov hcov t x := by
      rw [← hsumEig]
      nlinarith [hnormEig]
    exact hsumSquares
  have hReactionE : ∀ i j : Fin 3,
      (2 * (∑ p, ∑ q, (Ric p q) ^ 2) - Scal ^ 2) *
            (if i = j then 1 else 0) +
        3 * Scal * Ric i j - 6 * ∑ l, Ric i l * Ric l j =
      (2 * g.ricciNormSq cov hcov t x * (g t).inner x (e i) (e j) -
        2 * Scal * Ric i j -
        curvatureOperatorReaction g cov hcov hLevi hdim t x (e i) (e j)) / 2 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [hRicciNormComponents, hRicciComponent i i,
        hRicciProduct i i, hQComponent i i, hInner i i]
      simp
      nlinarith [he2Norm]
    · rw [hRicciComponent i j, hRicciProduct i j, hQComponent i j]
      rw [hInner i j]
      simp [hij]
  have hReaction' : ∀ i j,
      (2 * (∑ p, ∑ q, (Ric p q) ^ 2) - Scal ^ 2) *
            (if i = j then 1 else 0) +
        3 * Scal * Ric i j - 6 * ∑ l, Ric i l * Ric l j =
      (2 * g.ricciNormSq cov hcov t x * (g t).inner x (b i) (b j) -
        2 * g.scalarCurvature cov hcov t x *
          g.ricciCurvature cov hcov t x (b i) (b j) -
        curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b j)) / 2 := by
    intro i j
    simpa [Ric, Scal, b] using hReactionE i j
  exact
    { b := b
      K := K
      Ric := Ric
      Scal := Scal
      H := H
      S := S
      hK := hK
      hRicSymm := hRicSymm
      hScal := hScal
      hHlast := hHlast
      hHcomm := hHcomm'
      hDiv := hDiv
      hTrace := hTrace
      hSsymm := hSsymm
      hRaw := hRaw'
      hLaplacian := hLaplacian
      hReaction := hReaction' }

/-! The first fully intrinsic curvature-evolution constructor.  It obtains
the derivative of the genuine curvature tensor from the Ricci-flow equation
and the regularity package above, derives the Ricci trace evolution from the
static geometric contractions, and then proves the lowered curvature-operator
equation. -/
def HamiltonIveyCurvatureEvolutionCertificate.of_intrinsicRicciFlow_and_jointRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (hregularity : HamiltonIveyIntrinsicCurvatureVariationRegularity
      g cov hcov hLevi t)
    (hOperatorRegularity : ∀ y : M,
      g.HamiltonIveyCurvatureOperatorRegularity
        cov hcov hLevi hdim t y)
      (sliceRegularity : HamiltonIveyIntrinsicSliceRegularity
      g cov hcov hLevi t)
    (hShiftedTensorRegularity :
      g.HamiltonIveyShiftedTensorTraceRegularity
        cov hcov hLevi hdim t x) :
  HamiltonIveyCurvatureEvolutionCertificate g cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let hvelocityExists :=
    exists_intrinsicRicciCurvatureTensorVelocity_of_jointRegularity
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
      (hcovTwo := hregularity.connectionC2)
      (hcovTwoAll := sliceRegularity.connectionC2)
      (hjointFixedPairing := fun U V hU hV =>
        jointMetricPairing_contMDiff_of_jointMetricTensor
          (I := I) (M := M) g hregularity.jointMetricTensor hU hV)
      hregularity.nestedYZ hregularity.nestedXZ
  let curvatureVelocity := Classical.choose hvelocityExists
  have hvelocity := (Classical.choose_spec hvelocityExists).1
  have hCurvature := (Classical.choose_spec hvelocityExists).2.1
  have hRicci := (Classical.choose_spec hvelocityExists).2.2
  let contractions :=
    HamiltonIveyRicciTraceContractions.of_intrinsicFields
      g cov hcov hLevi hdim curvatureVelocity t x
      sliceRegularity.connectionC2 sliceRegularity.metricC2
      (sliceRegularity.trace x) sliceRegularity.scalarC2
      sliceRegularity.ricciC2 hregularity hvelocity
  have hRicciEvolution :=
    HamiltonIveyRicciTraceEvolution.of_geometricContractions
      g cov hcov hLevi hdim x curvatureVelocity
      contractions.b contractions.K contractions.Ric contractions.Scal
      contractions.H contractions.S
      contractions.hK contractions.hRicSymm contractions.hScal
      contractions.hHlast contractions.hHcomm contractions.hDiv
      contractions.hTrace contractions.hSsymm contractions.hRaw
      contractions.hLaplacian contractions.hReaction
  have hOperatorLaplacian :=
    hamiltonIveyCurvatureOperatorLaplacian_of_globalRegularity
      g cov hcov hLevi hdim t x hOperatorRegularity
  have hTraceLaplacian :=
    g.HamiltonIveyTraceLaplacianAt_of_shiftedTensorRegularity
      cov hcov hLevi hdim t x hShiftedTensorRegularity
  have hTrace :=
    HamiltonIveyMetricTraceEvolution_of_RicciTraceEvolution
      g cov hcov hLevi hdim curvatureVelocity t x
      hRicciEvolution hOperatorLaplacian hTraceLaplacian
  have hEvolution :=
    hasDerivAt_curvatureOperatorTwoTensor_of_connectionVariation_traceEvolution
      g cov hcov hLevi hdim gdot s hflow ht x curvatureVelocity
      hRicci hRicciEvolution hTrace hOperatorLaplacian
  exact
    { curvatureVelocity := curvatureVelocity
      hCurvature := hCurvature
      hEvolution := hEvolution }

/-! This is the pinching endpoint that consumes the derived evolution
certificate.  The local contact hypothesis is regularity of the genuine
Rayleigh support, not the target differential inequality; the latter is
obtained by the existing curvature-evolution/contact argument. -/
theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_jointGeometricEvolution_contactData_on_negative_spectrum
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
    (hregularity : ∀ {t : ℝ}, t ∈ Icc 0 T →
      HamiltonIveyIntrinsicCurvatureVariationRegularity
        g cov hcov hLevi t)
    (hOperatorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyCurvatureOperatorRegularity
        cov hcov hLevi hdim t x)
    (sliceRegularity : ∀ {t : ℝ}, t ∈ Icc 0 T →
      HamiltonIveyIntrinsicSliceRegularity g cov hcov hLevi t)
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
  let evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x := by
    intro t ht x
    have hShiftedTensorRegularity :=
      HamiltonIveyShiftedTensorTraceRegularity.of_curvatureOperatorRegularity
        g cov hcov hLevi hdim t x (hOperatorRegularity t ht x)
    exact HamiltonIveyCurvatureEvolutionCertificate.of_intrinsicRicciFlow_and_jointRegularity
      g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht x
      (hregularity (t := t) ht) (fun y => hOperatorRegularity t ht y)
      (sliceRegularity (t := t) ht) hShiftedTensorRegularity
  exact hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolution_operatorRegularity_contactData_on_negative_spectrum
    g cov hcov hLevi hdim gdot hK hT hflow evolution
    hOperatorRegularity hnuLower hScalarCont hNuCont hcontact

end CovariantDerivative.TimeDependentRiemannianMetric

end
