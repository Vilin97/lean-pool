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

module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Raw
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
/-!
# Gauge transport primitives for Ricci flow

This internal file starts the missing gauge-transport side of roadmap point 4.
It defines pullback of tangent-bundle bilinear tensor fields along bundled `C^1`
self-maps, upgrades this slicewise to time-dependent tensor families, and
specializes the construction to the metric tensor of an evolving Riemannian
metric family.

These transport lemmas are still preparatory infrastructure only: they do not
complete roadmap point 4 by themselves, but they supply the first proof-bearing
objects needed for a later Ricci-DeTurck-to-Ricci-flow gauge reduction.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The endomorphism traced in the DeTurck one-form, but for an arbitrary pair of
time-dependent connection families. Its argument is the connection-difference slot that is
traced; the fixed vector is the output slot of that difference tensor. -/
def connectionDifferenceTraceEndomorphism
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w : TM x) :
    TM x →L[ℝ] TM x where
  toFun u := (CovariantDerivative.difference (cov t) (cov' t) x u) w
  map_add' u v := by
    exact congrArg
      (fun F : TM x →L[ℝ] TM x => F w)
      ((CovariantDerivative.difference (cov t) (cov' t) x).map_add u v)
  map_smul' c u := by
    exact congrArg
      (fun F : TM x →L[ℝ] TM x => F w)
      ((CovariantDerivative.difference (cov t) (cov' t) x).map_smul c u)

@[simp] lemma connectionDifferenceTraceEndomorphism_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w u : TM x) :
    connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w u =
      (CovariantDerivative.difference (cov t) (cov' t) x u) w := rfl

lemma connectionDifferenceTraceEndomorphism_add
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w₁ w₂ : TM x) :
    connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x (w₁ + w₂) =
      connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w₁ +
        connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w₂ := by
  ext u
  exact ((CovariantDerivative.difference (cov t) (cov' t) x u).map_add w₁ w₂)

lemma connectionDifferenceTraceEndomorphism_smul
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (c : ℝ) (w : TM x) :
    connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x (c • w) =
      c • connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w := by
  ext u
  exact ((CovariantDerivative.difference (cov t) (cov' t) x u).map_smul c w)

/-- On zero-dimensional tangent fibers, every traced connection-difference endomorphism vanishes. -/
theorem connectionDifferenceTraceEndomorphism_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w : TM x) :
    connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w = 0 := by
  ext u
  exact Subsingleton.elim _ _

/-- The traced connection-difference one-form associated to two time-dependent connection families. -/
def connectionDifferenceTraceOneForm
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    TM x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w =>
        LinearMap.trace ℝ (TM x)
          (connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w).toLinearMap
      map_add' := by
        intro w₁ w₂
        calc
          LinearMap.trace ℝ (TM x)
              (connectionDifferenceTraceEndomorphism (I := I) (M := M)
                cov cov' t x (w₁ + w₂)).toLinearMap
            = LinearMap.trace ℝ (TM x)
                ((connectionDifferenceTraceEndomorphism (I := I) (M := M)
                  cov cov' t x w₁ +
                    connectionDifferenceTraceEndomorphism (I := I) (M := M)
                      cov cov' t x w₂).toLinearMap) := by
                rw [connectionDifferenceTraceEndomorphism_add]
          _ = LinearMap.trace ℝ (TM x)
                (connectionDifferenceTraceEndomorphism (I := I) (M := M)
                  cov cov' t x w₁).toLinearMap +
              LinearMap.trace ℝ (TM x)
                (connectionDifferenceTraceEndomorphism (I := I) (M := M)
                  cov cov' t x w₂).toLinearMap := by
                simp [LinearMap.map_add]
      map_smul' := by
        intro c w
        calc
          LinearMap.trace ℝ (TM x)
              (connectionDifferenceTraceEndomorphism (I := I) (M := M)
                cov cov' t x (c • w)).toLinearMap
            = LinearMap.trace ℝ (TM x)
                ((c • connectionDifferenceTraceEndomorphism (I := I) (M := M)
                  cov cov' t x w).toLinearMap) := by
                rw [connectionDifferenceTraceEndomorphism_smul]
          _ = c * LinearMap.trace ℝ (TM x)
                (connectionDifferenceTraceEndomorphism (I := I) (M := M)
                  cov cov' t x w).toLinearMap := by
                simp }

@[simp] lemma connectionDifferenceTraceOneForm_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w : TM x) :
    connectionDifferenceTraceOneForm (I := I) (M := M) cov cov' t x w =
      LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w).toLinearMap := by
  simp [connectionDifferenceTraceOneForm]

/-- On zero-dimensional tangent fibers, every traced connection-difference one-form vanishes. -/
theorem connectionDifferenceTraceOneForm_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (cov cov' : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    connectionDifferenceTraceOneForm (I := I) (M := M) cov cov' t x = 0 := by
  ext w
  rw [connectionDifferenceTraceOneForm_apply]
  have hEnd :
      (connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t x w).toLinearMap = 0 := by
    rw [connectionDifferenceTraceEndomorphism_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) cov cov' t x w]
    rfl
  simpa [hEnd] using (LinearMap.map_zero (LinearMap.trace ℝ (TM x)))

/-- A bundled `C^1` self-map of the manifold. -/
abbrev SmoothSelfMap := C^1⟮I, M; I, M⟯

/-- A time-dependent family of bundled `C^1` self-maps. -/
abbrev SmoothSelfMapFamily :=
  CovariantDerivative.TimeFamily (SmoothSelfMap (I := I) (M := M))

/-- The identity bundled `C^1` self-map. -/
def smoothSelfMapId : SmoothSelfMap (I := I) (M := M) :=
  ⟨id, contMDiff_id⟩

@[simp] lemma smoothSelfMapId_apply (x : M) :
    smoothSelfMapId (I := I) (M := M) x = x := rfl

namespace SmoothSelfMapFamily

variable (Φ : SmoothSelfMapFamily (I := I) (M := M))

/-- Evaluate a time-dependent self-map family at a fixed time. -/
def eval (t : ℝ) : SmoothSelfMap (I := I) (M := M) := Φ t

@[simp] lemma eval_apply (t : ℝ) (x : M) : Φ.eval t x = Φ t x := rfl

/-- The constant time family determined by a single smooth self-map. -/
def const (φ : SmoothSelfMap (I := I) (M := M)) : SmoothSelfMapFamily (I := I) (M := M) :=
  CovariantDerivative.TimeFamily.const φ

@[simp] lemma const_apply
    (φ : SmoothSelfMap (I := I) (M := M)) (t : ℝ) :
    SmoothSelfMapFamily.const (I := I) (M := M) φ t = φ := rfl

/-- The constant identity family. -/
def id : SmoothSelfMapFamily (I := I) (M := M) :=
  const (I := I) (M := M) (smoothSelfMapId (I := I) (M := M))

@[simp] lemma id_apply (t : ℝ) :
    SmoothSelfMapFamily.id (I := I) (M := M) t =
      smoothSelfMapId (I := I) (M := M) := rfl

/-- Pointwise composition of time-dependent smooth self-map families. -/
def comp
    (Φ Ψ : SmoothSelfMapFamily (I := I) (M := M)) :
    SmoothSelfMapFamily (I := I) (M := M) :=
  fun t ↦ (Φ t).comp (Ψ t)

@[simp] lemma comp_apply
    (Φ Ψ : SmoothSelfMapFamily (I := I) (M := M)) (t : ℝ) :
    SmoothSelfMapFamily.comp (I := I) (M := M) Φ Ψ t = (Φ t).comp (Ψ t) := rfl

end SmoothSelfMapFamily

/-- A curve `γ : ℝ → M` is a time-dependent integral curve of `X` on `s` if its derivative at each
time in `s` equals the corresponding time slice `X t` evaluated along `γ`. -/
def IsTimeDependentIntegralCurveOn
    (γ : ℝ → M)
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasMFDerivAt[s] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| X t (γ t))

/-- Local version of `IsTimeDependentIntegralCurveOn`. -/
def IsTimeDependentIntegralCurveAt
    (γ : ℝ → M)
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (t₀ : ℝ) : Prop :=
  ∃ s ∈ 𝓝 t₀, IsTimeDependentIntegralCurveOn (I := I) (M := M) γ X s

lemma IsTimeDependentIntegralCurveOn.mono
    {γ : ℝ → M}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ}
    (hγ : IsTimeDependentIntegralCurveOn (I := I) (M := M) γ X t)
    (hst : s ⊆ t) :
    IsTimeDependentIntegralCurveOn (I := I) (M := M) γ X s := by
  intro u hu
  exact (hγ u (hst hu)).mono hst

lemma IsTimeDependentIntegralCurveOn.hasMFDerivWithinAt
    {γ : ℝ → M}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} (hγ : IsTimeDependentIntegralCurveOn (I := I) (M := M) γ X s)
    {t : ℝ} (ht : t ∈ s) :
    HasMFDerivAt[s] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| X t (γ t)) :=
  hγ t ht

lemma IsTimeDependentIntegralCurveOn.of_hasMFDerivWithinAt
    {γ : ℝ → M}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hγ : ∀ t ∈ s,
      HasMFDerivAt[s] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| X t (γ t))) :
    IsTimeDependentIntegralCurveOn (I := I) (M := M) γ X s :=
  hγ

/-- Reinterpret a Mathlib autonomous manifold integral curve as a time-dependent
integral curve for the constant-in-time vector field. -/
lemma IsMIntegralCurveOn.toTimeDependentIntegralCurveOn_const
    {γ : ℝ → M} {X : Π x : M, TangentSpace I x} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn (I := I) γ X s) :
    IsTimeDependentIntegralCurveOn (I := I) (M := M) γ (fun _ ↦ X) s := by
  intro t ht
  simpa using hγ t ht

/-- Reinterpret a Mathlib autonomous local manifold integral curve as a
time-dependent local integral curve for the constant-in-time vector field. -/
lemma IsMIntegralCurveAt.toTimeDependentIntegralCurveAt_const
    {γ : ℝ → M} {X : Π x : M, TangentSpace I x} {t₀ : ℝ}
    (hγ : IsMIntegralCurveAt (I := I) γ X t₀) :
    IsTimeDependentIntegralCurveAt (I := I) (M := M) γ (fun _ ↦ X) t₀ := by
  rcases isMIntegralCurveAt_iff.mp hγ with ⟨s, hs, hγs⟩
  exact ⟨s, hs,
    IsMIntegralCurveOn.toTimeDependentIntegralCurveOn_const (I := I) (M := M) hγs⟩

lemma IsTimeDependentIntegralCurveAt.hasMFDerivAt
    {γ : ℝ → M}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hγ : IsTimeDependentIntegralCurveAt (I := I) (M := M) γ X t) :
    HasMFDerivAt 𝓘(ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| X t (γ t)) := by
  rcases hγ with ⟨s, hs, hγs⟩
  exact (hγs.hasMFDerivWithinAt (mem_of_mem_nhds hs)).hasMFDerivAt hs

/-- Reinterpret a time-dependent integral curve for an equal vector field along the curve. -/
lemma IsTimeDependentIntegralCurveOn.congr_vectorField
    {γ : ℝ → M}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hγ : IsTimeDependentIntegralCurveOn (I := I) (M := M) γ X s)
    (hXY : ∀ t ∈ s, X t (γ t) = Y t (γ t)) :
    IsTimeDependentIntegralCurveOn (I := I) (M := M) γ Y s := by
  intro t ht
  simpa [hXY t ht] using hγ t ht

/-- Reinterpret a time-dependent integral curve when the vector fields agree
along the curve in the relative time-set filter at each time. -/
lemma IsTimeDependentIntegralCurveOn.congr_vectorField_nhdsWithin
    {γ : ℝ → M}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hγ : IsTimeDependentIntegralCurveOn (I := I) (M := M) γ X s)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, X τ (γ τ) = Y τ (γ τ)) :
    IsTimeDependentIntegralCurveOn (I := I) (M := M) γ Y s := by
  intro t ht
  have hXYt : X t (γ t) = Y t (γ t) :=
    show t ∈ {τ : ℝ | X τ (γ τ) = Y τ (γ τ)} from
      mem_of_mem_nhdsWithin ht (hXY t ht)
  simpa [hXYt] using hγ t ht

/-- Reinterpret a local time-dependent integral curve for a vector field that agrees along the
curve near the base time. -/
lemma IsTimeDependentIntegralCurveAt.congr_vectorField
    {γ : ℝ → M}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t₀ : ℝ}
    (hγ : IsTimeDependentIntegralCurveAt (I := I) (M := M) γ X t₀)
    (hXY : ∀ᶠ t in 𝓝 t₀, X t (γ t) = Y t (γ t)) :
    IsTimeDependentIntegralCurveAt (I := I) (M := M) γ Y t₀ := by
  rcases hγ with ⟨s, hs, hγs⟩
  refine ⟨s ∩ {t | X t (γ t) = Y t (γ t)}, Filter.inter_mem hs hXY, ?_⟩
  exact (hγs.mono Set.inter_subset_left).congr_vectorField (fun t ht ↦ ht.2)

lemma isTimeDependentIntegralCurveOn_const_of_eq_zero
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (x : M)
    (hX : ∀ t ∈ s, X t x = 0) :
    IsTimeDependentIntegralCurveOn (I := I) (M := M) (fun _ : ℝ ↦ x) X s := by
  intro t ht
  have hconst : HasMFDerivAt 𝓘(ℝ) I (fun _ : ℝ ↦ x) t 0 := by
    simpa using (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := I) (x := t) (c := x))
  have htarget :
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t x)) = (0 : ℝ →L[ℝ] TM x) := by
    rw [hX t ht]
    ext r
    simp
  rw [htarget]
  exact hconst.hasMFDerivWithinAt

/-- A time-dependent bundled self-map family solves the gauge-flow equation on `s` if each
pointwise time curve is an integral curve of the time-dependent vector field `X` on `s`. -/
def SatisfiesGaugeFlowOn
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ x : M, IsTimeDependentIntegralCurveOn (I := I) (M := M) (fun t ↦ Φ t x) X s

/-- Local version of `SatisfiesGaugeFlowOn`. -/
def SatisfiesGaugeFlowAt
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (t₀ : ℝ) : Prop :=
  ∀ x : M, IsTimeDependentIntegralCurveAt (I := I) (M := M) (fun t ↦ Φ t x) X t₀

lemma SatisfiesGaugeFlowOn.mono
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ}
    (hΦ : SatisfiesGaugeFlowOn (I := I) (M := M) Φ X t)
    (hst : s ⊆ t) :
    SatisfiesGaugeFlowOn (I := I) (M := M) Φ X s := by
  intro x
  exact (hΦ x).mono hst

lemma SatisfiesGaugeFlowOn.satisfiesAt
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hΦ : SatisfiesGaugeFlowOn (I := I) (M := M) Φ X s)
    (hs : s ∈ 𝓝 t₀) :
    SatisfiesGaugeFlowAt (I := I) (M := M) Φ X t₀ := by
  intro x
  exact ⟨s, hs, hΦ x⟩

lemma SatisfiesGaugeFlowOn.hasMFDerivWithinAt
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} (hΦ : SatisfiesGaugeFlowOn (I := I) (M := M) Φ X s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ Φ τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight <| X t (Φ t x)) :=
  (hΦ x).hasMFDerivWithinAt ht

lemma SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hΦ : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ Φ τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight <| X t (Φ t x))) :
    SatisfiesGaugeFlowOn (I := I) (M := M) Φ X s := by
  intro x
  exact IsTimeDependentIntegralCurveOn.of_hasMFDerivWithinAt
    (I := I) (M := M) (fun t ht ↦ hΦ t ht x)

lemma SatisfiesGaugeFlowAt.hasMFDerivAt
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hΦ : SatisfiesGaugeFlowAt (I := I) (M := M) Φ X t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ Φ τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight <| X t (Φ t x)) :=
  (hΦ x).hasMFDerivAt

/-- A self-map family whose pointwise curves are autonomous Mathlib integral
curves satisfies the gauge-flow equation for the constant-in-time vector field. -/
lemma SatisfiesGaugeFlowOn.of_autonomousIntegralCurves
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : Π x : M, TangentSpace I x} {s : Set ℝ}
    (hΦ : ∀ x : M, IsMIntegralCurveOn (I := I) (fun t : ℝ ↦ Φ t x) X s) :
    SatisfiesGaugeFlowOn (I := I) (M := M) Φ (fun _ ↦ X) s := by
  intro x
  exact IsMIntegralCurveOn.toTimeDependentIntegralCurveOn_const (I := I) (M := M) (hΦ x)

/-- A self-map family whose pointwise curves are autonomous Mathlib local
integral curves satisfies the local gauge-flow equation for the constant-in-time
vector field. -/
lemma SatisfiesGaugeFlowAt.of_autonomousIntegralCurves
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : Π x : M, TangentSpace I x} {t₀ : ℝ}
    (hΦ : ∀ x : M, IsMIntegralCurveAt (I := I) (fun t : ℝ ↦ Φ t x) X t₀) :
    SatisfiesGaugeFlowAt (I := I) (M := M) Φ (fun _ ↦ X) t₀ := by
  intro x
  exact IsMIntegralCurveAt.toTimeDependentIntegralCurveAt_const (I := I) (M := M) (hΦ x)

/-- Pointwise autonomous Mathlib local integral curves at every time in a set
give the constant-in-time gauge-flow equation on that set. -/
lemma SatisfiesGaugeFlowOn.of_autonomousIntegralCurveAt
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X : Π x : M, TangentSpace I x} {s : Set ℝ}
    (hΦ : ∀ t ∈ s, ∀ x : M,
      IsMIntegralCurveAt (I := I) (fun τ : ℝ ↦ Φ τ x) X t) :
    SatisfiesGaugeFlowOn (I := I) (M := M) Φ (fun _ ↦ X) s := by
  intro x
  exact IsMIntegralCurveOn.toTimeDependentIntegralCurveOn_const (I := I) (M := M)
    (IsMIntegralCurveAt.isMIntegralCurveOn (fun t ht => hΦ t ht x))

/-- Reinterpret a gauge-flow family for an equal vector field along the flow image. -/
lemma SatisfiesGaugeFlowOn.congr_vectorField
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hΦ : SatisfiesGaugeFlowOn (I := I) (M := M) Φ X s)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (Φ t x) = Y t (Φ t x)) :
    SatisfiesGaugeFlowOn (I := I) (M := M) Φ Y s := by
  intro x
  exact (hΦ x).congr_vectorField (fun t ht ↦ hXY t ht x)

/-- Reinterpret a gauge-flow family when two vector fields agree along the flow
image in the relative time-set filter at each time. -/
lemma SatisfiesGaugeFlowOn.congr_vectorField_nhdsWithin
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hΦ : SatisfiesGaugeFlowOn (I := I) (M := M) Φ X s)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (Φ τ x) = Y τ (Φ τ x)) :
    SatisfiesGaugeFlowOn (I := I) (M := M) Φ Y s := by
  intro x
  exact (hΦ x).congr_vectorField_nhdsWithin
    (fun t ht ↦ (hXY t ht).mono fun τ hτ ↦ hτ x)

/-- Reinterpret a local gauge-flow family for a vector field that agrees along the family near the
base time. -/
lemma SatisfiesGaugeFlowAt.congr_vectorField
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t₀ : ℝ}
    (hΦ : SatisfiesGaugeFlowAt (I := I) (M := M) Φ X t₀)
    (hXY : ∀ᶠ t in 𝓝 t₀, ∀ x : M, X t (Φ t x) = Y t (Φ t x)) :
    SatisfiesGaugeFlowAt (I := I) (M := M) Φ Y t₀ := by
  intro x
  exact (hΦ x).congr_vectorField (hXY.mono fun t ht ↦ ht x)

lemma SmoothSelfMapFamily.id_satisfiesGaugeFlowOn_of_eq_zero
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      (SmoothSelfMapFamily.id (I := I) (M := M)) X s := by
  intro x
  simpa [SmoothSelfMapFamily.id] using
    isTimeDependentIntegralCurveOn_const_of_eq_zero
      (I := I) (M := M) X s x (fun t ht ↦ hX t ht x)

/-- A gauge-map family is anchored at time `t₀` if it equals the identity map at that time. -/
def AnchoredAt
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (t₀ : ℝ) : Prop :=
  Φ t₀ = smoothSelfMapId (I := I) (M := M)

lemma AnchoredAt.apply
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {t₀ : ℝ}
    (hΦ : AnchoredAt (I := I) (M := M) Φ t₀)
    (x : M) :
    Φ t₀ x = x := by
  simpa [AnchoredAt] using congrArg (fun φ : SmoothSelfMap (I := I) (M := M) => φ x) hΦ

/-- A tensor field is symmetric if it is symmetric in its two tangent slots at every point. -/
def IsSymmetricTensorField (T : Π x : M, TM x → TM x → ℝ) : Prop :=
  ∀ x : M, ∀ u v : TM x, T x u v = T x v u

/-- A time-dependent tensor family is symmetric if each time slice is symmetric. -/
def IsSymmetricTensorFamily (T : MetricTensorFamily (I := I) (M := M)) : Prop :=
  ∀ t : ℝ, IsSymmetricTensorField (I := I) (M := M) (T t)

/-- Pull back a tangent-bundle bilinear tensor field along a bundled `C^1` self-map. -/
def pullbackTensorField
    (φ : SmoothSelfMap (I := I) (M := M))
    (T : Π x : M, TM x → TM x → ℝ) :
    Π x : M, TM x → TM x → ℝ :=
  fun x u v ↦
    T (φ x)
      ((mfderiv I I (φ : M → M) x) u)
      ((mfderiv I I (φ : M → M) x) v)

@[simp] lemma pullbackTensorField_apply
    (φ : SmoothSelfMap (I := I) (M := M))
    (T : Π x : M, TM x → TM x → ℝ)
    (x : M) (u v : TM x) :
    pullbackTensorField (I := I) (M := M) φ T x u v =
      T (φ x)
        ((mfderiv I I (φ : M → M) x) u)
        ((mfderiv I I (φ : M → M) x) v) := rfl

@[simp] theorem pullbackTensorField_id
    (T : Π x : M, TM x → TM x → ℝ) :
    pullbackTensorField (I := I) (M := M) (smoothSelfMapId (I := I) (M := M)) T = T := by
  funext x u v
  change
    T ((_root_.id : M → M) x)
        ((mfderiv I I (_root_.id : M → M) x) u)
        ((mfderiv I I (_root_.id : M → M) x) v) =
      T x u v
  have hu0 :
      (mfderiv I I (_root_.id : M → M) x) u =
        (ContinuousLinearMap.id ℝ (TangentSpace I x)) u := by
    exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I x => f u)
      (mfderiv_id (I := I) (x := x))
  have hv0 :
      (mfderiv I I (_root_.id : M → M) x) v =
        (ContinuousLinearMap.id ℝ (TangentSpace I x)) v := by
    exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I x => f v)
      (mfderiv_id (I := I) (x := x))
  have hu : (mfderiv I I (_root_.id : M → M) x) u = u := hu0.trans rfl
  have hv : (mfderiv I I (_root_.id : M → M) x) v = v := hv0.trans rfl
  rw [hu, hv]
  rfl

theorem pullbackTensorField_comp
    (φ ψ : SmoothSelfMap (I := I) (M := M))
    (T : Π x : M, TM x → TM x → ℝ) :
    pullbackTensorField (I := I) (M := M) (φ.comp ψ) T =
      pullbackTensorField (I := I) (M := M) ψ
        (pullbackTensorField (I := I) (M := M) φ T) := by
  funext x u v
  change
    T (((φ : M → M) ∘ (ψ : M → M)) x)
        ((mfderiv I I ((φ : M → M) ∘ (ψ : M → M)) x) u)
        ((mfderiv I I ((φ : M → M) ∘ (ψ : M → M)) x) v) =
      T (φ (ψ x))
        ((mfderiv I I (φ : M → M) (ψ x)) ((mfderiv I I (ψ : M → M) x) u))
        ((mfderiv I I (φ : M → M) (ψ x)) ((mfderiv I I (ψ : M → M) x) v))
  have hφ : MDifferentiableAt I I (φ : M → M) (ψ x) :=
    φ.contMDiff.mdifferentiableAt (by simp)
  have hψ : MDifferentiableAt I I (ψ : M → M) x :=
    ψ.contMDiff.mdifferentiableAt (by simp)
  have hcomp_u :
      mfderiv I I ((φ : M → M) ∘ (ψ : M → M)) x u =
        (mfderiv I I (φ : M → M) (ψ x)) ((mfderiv I I (ψ : M → M) x) u) :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (f := (ψ : M → M)) (g := (φ : M → M)) (x := x) hφ hψ u
  have hcomp_v :
      mfderiv I I ((φ : M → M) ∘ (ψ : M → M)) x v =
        (mfderiv I I (φ : M → M) (ψ x)) ((mfderiv I I (ψ : M → M) x) v) :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (f := (ψ : M → M)) (g := (φ : M → M)) (x := x) hφ hψ v
  rw [hcomp_u, hcomp_v]
  rfl

theorem IsSymmetricTensorField.pullback
    {T : Π x : M, TM x → TM x → ℝ}
    (hT : IsSymmetricTensorField (I := I) (M := M) T)
    (φ : SmoothSelfMap (I := I) (M := M)) :
    IsSymmetricTensorField (I := I) (M := M)
      (pullbackTensorField (I := I) (M := M) φ T) := by
  intro x u v
  exact hT (φ x) ((mfderiv I I (φ : M → M) x) u) ((mfderiv I I (φ : M → M) x) v)

/-- Pull back a time-dependent tangent-bundle bilinear tensor family along a time-dependent family
of bundled `C^1` self-maps. -/
def pullbackTensorFamily
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (T : MetricTensorFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t ↦ pullbackTensorField (I := I) (M := M) (Φ t) (T t)

@[simp] lemma pullbackTensorFamily_apply
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (T : MetricTensorFamily (I := I) (M := M))
    (t : ℝ) :
    pullbackTensorFamily (I := I) (M := M) Φ T t =
      pullbackTensorField (I := I) (M := M) (Φ t) (T t) := rfl

@[simp] theorem pullbackTensorFamily_id
    (T : MetricTensorFamily (I := I) (M := M)) :
    pullbackTensorFamily (I := I) (M := M)
      (SmoothSelfMapFamily.id (I := I) (M := M)) T = T := by
  funext t
  simpa using pullbackTensorField_id (I := I) (M := M) (T := T t)

theorem pullbackTensorFamily_comp
    (Φ Ψ : SmoothSelfMapFamily (I := I) (M := M))
    (T : MetricTensorFamily (I := I) (M := M)) :
    pullbackTensorFamily (I := I) (M := M)
        (SmoothSelfMapFamily.comp (I := I) (M := M) Φ Ψ) T =
      pullbackTensorFamily (I := I) (M := M) Ψ
        (pullbackTensorFamily (I := I) (M := M) Φ T) := by
  funext t
  simpa [pullbackTensorFamily] using
    pullbackTensorField_comp (I := I) (M := M) (φ := Φ t) (ψ := Ψ t) (T := T t)

theorem pullbackTensorFamily_eq_at_time_of_eq_id
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (T : MetricTensorFamily (I := I) (M := M))
    (t : ℝ)
    (hΦ : Φ t = smoothSelfMapId (I := I) (M := M)) :
    pullbackTensorFamily (I := I) (M := M) Φ T t = T t := by
  rw [pullbackTensorFamily_apply, hΦ, pullbackTensorField_id]

theorem pullbackTensorFamily_eq_at_anchored_time
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (T : MetricTensorFamily (I := I) (M := M))
    (t₀ : ℝ)
    (hΦ : AnchoredAt (I := I) (M := M) Φ t₀) :
    pullbackTensorFamily (I := I) (M := M) Φ T t₀ = T t₀ := by
  exact pullbackTensorFamily_eq_at_time_of_eq_id (I := I) (M := M) Φ T t₀ hΦ

theorem IsSymmetricTensorFamily.pullback
    {T : MetricTensorFamily (I := I) (M := M)}
    (hT : IsSymmetricTensorFamily (I := I) (M := M) T)
    (Φ : SmoothSelfMapFamily (I := I) (M := M)) :
    IsSymmetricTensorFamily (I := I) (M := M)
      (pullbackTensorFamily (I := I) (M := M) Φ T) := by
  intro t
  exact (hT t).pullback (I := I) (M := M) (φ := Φ t)

lemma metricTensor_isSymmetric
    (g : MetricFamily (I := I) (M := M)) :
    IsSymmetricTensorFamily (I := I) (M := M) (metricTensor (I := I) (M := M) g) := by
  intro t x u v
  exact (g t).symm x u v

/-- Pull back the metric tensor family of an evolving smooth Riemannian metric along a
time-dependent family of bundled `C^1` self-maps. -/
def pullbackMetricTensor
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  pullbackTensorFamily (I := I) (M := M) Φ (metricTensor (I := I) (M := M) g)

@[simp] lemma pullbackMetricTensor_apply
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) :
    pullbackMetricTensor (I := I) (M := M) Φ g t =
      pullbackTensorField (I := I) (M := M) (Φ t)
        (metricTensor (I := I) (M := M) g t) := rfl

@[simp] theorem pullbackMetricTensor_id
    (g : MetricFamily (I := I) (M := M)) :
    pullbackMetricTensor (I := I) (M := M)
      (SmoothSelfMapFamily.id (I := I) (M := M)) g =
        metricTensor (I := I) (M := M) g := by
  simpa [pullbackMetricTensor] using
    pullbackTensorFamily_id (I := I) (M := M)
      (T := metricTensor (I := I) (M := M) g)

theorem pullbackMetricTensor_eq_metricTensor_at_time_of_eq_id
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ)
    (hΦ : Φ t = smoothSelfMapId (I := I) (M := M)) :
    pullbackMetricTensor (I := I) (M := M) Φ g t =
      metricTensor (I := I) (M := M) g t := by
  simpa [pullbackMetricTensor] using
    pullbackTensorFamily_eq_at_time_of_eq_id (I := I) (M := M)
      (Φ := Φ) (T := metricTensor (I := I) (M := M) g) t hΦ

theorem pullbackMetricTensor_eq_metricTensor_at_anchored_time
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t₀ : ℝ)
    (hΦ : AnchoredAt (I := I) (M := M) Φ t₀) :
    pullbackMetricTensor (I := I) (M := M) Φ g t₀ =
      metricTensor (I := I) (M := M) g t₀ := by
  exact pullbackMetricTensor_eq_metricTensor_at_time_of_eq_id
    (I := I) (M := M) Φ g t₀ hΦ

theorem pullbackMetricTensor_isSymmetric
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M)) :
    IsSymmetricTensorFamily (I := I) (M := M)
      (pullbackMetricTensor (I := I) (M := M) Φ g) := by
  exact (metricTensor_isSymmetric (I := I) (M := M) g).pullback
    (I := I) (M := M) Φ

/-- On zero-dimensional tangent fibers, every pulled-back metric tensor component vanishes
pointwise, independently of the chosen gauge map family. -/
theorem pullbackMetricTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    pullbackMetricTensor (I := I) (M := M) Φ g t x u v = 0 := by
  rw [pullbackMetricTensor_apply, pullbackTensorField_apply]
  exact metricTensor_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) g t (Φ t x)
    ((mfderiv I I (Φ t : M → M) x) u)
    ((mfderiv I I (Φ t : M → M) x) v)

/-- A bundled `C^1` self-diffeomorphism of the manifold. -/
abbrev SmoothSelfDiffeomorph := M ≃ₘ^1⟮I, I⟯ M

/-- A time-dependent family of bundled `C^1` self-diffeomorphisms. -/
abbrev SmoothSelfDiffeomorphFamily :=
  CovariantDerivative.TimeFamily (SmoothSelfDiffeomorph (I := I) (M := M))

namespace SmoothSelfDiffeomorphFamily

variable (Φ : SmoothSelfDiffeomorphFamily (I := I) (M := M))

/-- Forget the inverse data and regard a diffeomorphism family as a family of bundled `C^1`
self-maps. -/
def toSmoothSelfMapFamily : SmoothSelfMapFamily (I := I) (M := M) :=
  fun t ↦ (Φ t : SmoothSelfMap (I := I) (M := M))

@[simp] lemma toSmoothSelfMapFamily_apply (t : ℝ) :
    Φ.toSmoothSelfMapFamily t = (Φ t : SmoothSelfMap (I := I) (M := M)) := rfl

/-- A diffeomorphism family is anchored at `t₀` if its time slice there is the identity
diffeomorphism. -/
def AnchoredAt (t₀ : ℝ) : Prop :=
  Φ t₀ = Diffeomorph.refl I M (1 : WithTop ℕ∞)

lemma AnchoredAt.toMapAnchoredAt
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    RicciFlow.AnchoredAt (I := I) (M := M) Φ.toSmoothSelfMapFamily t₀ := by
  change ((Φ t₀ : SmoothSelfDiffeomorph (I := I) (M := M)) :
      SmoothSelfMap (I := I) (M := M)) = smoothSelfMapId (I := I) (M := M)
  rw [hΦ]
  rfl

end SmoothSelfDiffeomorphFamily

namespace SmoothSelfDiffeomorph

variable (φ : SmoothSelfDiffeomorph (I := I) (M := M))

/-- The tangent map of a bundled `C^1` self-diffeomorphism is a continuous linear equivalence on
each tangent space. -/
noncomputable abbrev tangentMap (x : M) : TM x ≃L[ℝ] TM (φ x) :=
  φ.mfderivToContinuousLinearEquiv (by simp) x

/-- Forward tangent transport along a self-diffeomorphism. -/
abbrev pushforwardTangent (x : M) : TM x →L[ℝ] TM (φ x) :=
  φ.tangentMap x

/-- Backward tangent transport along a self-diffeomorphism. -/
abbrev pullbackTangent (x : M) : TM (φ x) →L[ℝ] TM x :=
  (φ.tangentMap x).symm

lemma pushforwardTangent_eq_mfderiv (x : M) :
    φ.pushforwardTangent x = mfderiv I I (φ : M → M) x := by
  simpa [SmoothSelfDiffeomorph.pushforwardTangent, SmoothSelfDiffeomorph.tangentMap] using
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (I := I) (J := I) (Φ := φ) (x := x) (hn := by simp))

@[simp] lemma pushforwardTangent_apply (x : M) (u : TM x) :
    φ.pushforwardTangent x u = (mfderiv I I (φ : M → M) x) u := by
  simpa using congrArg (fun f : TM x →L[ℝ] TM (φ x) => f u)
    (φ.pushforwardTangent_eq_mfderiv x)

@[simp] lemma pullbackTangent_pushforwardTangent (x : M) (u : TM x) :
    φ.pullbackTangent x (φ.pushforwardTangent x u) = u := by
  exact (φ.tangentMap x).symm_apply_apply u

@[simp] lemma pushforwardTangent_pullbackTangent (x : M) (u : TM (φ x)) :
    φ.pushforwardTangent x (φ.pullbackTangent x u) = u := by
  exact (φ.tangentMap x).apply_symm_apply u

/-- Push forward a tangent-vector field along a bundled self-diffeomorphism. -/
def pushforwardVectorField
    (X : Π x : M, TM x) :
    Π x : M, TM x :=
  fun y ↦
    cast (congrArg (fun z : M => TM z) (φ.apply_symm_apply y))
      (φ.pushforwardTangent (φ.symm y) (X (φ.symm y)))

/-- Pull back a tangent-vector field along a bundled self-diffeomorphism. -/
def pullbackVectorField
    (X : Π x : M, TM x) :
    Π x : M, TM x :=
  fun x ↦ φ.pullbackTangent x (X (φ x))

@[simp] lemma pushforwardVectorField_apply
    (X : Π x : M, TM x) (y : M) :
    φ.pushforwardVectorField X y =
      cast (congrArg (fun z : M => TM z) (φ.apply_symm_apply y))
        (φ.pushforwardTangent (φ.symm y) (X (φ.symm y))) := rfl

@[simp] lemma pullbackVectorField_apply
    (X : Π x : M, TM x) (x : M) :
    φ.pullbackVectorField X x = φ.pullbackTangent x (X (φ x)) := rfl

@[simp] theorem pullbackVectorField_pushforwardVectorField
    (X : Π x : M, TM x) :
    φ.pullbackVectorField (φ.pushforwardVectorField X) = X := by
  funext x
  have hpush :
      φ.pushforwardVectorField X (φ x) = φ.pushforwardTangent x (X x) := by
    unfold SmoothSelfDiffeomorph.pushforwardVectorField
    simpa using
      (Function.LeftInverse.cast_eq
        (γ := fun z : M => TM z)
        (f := φ) (g := φ.symm) (h := φ.symm_apply_apply)
        (C := fun z : M => φ.pushforwardTangent z (X z)) x)
  rw [SmoothSelfDiffeomorph.pullbackVectorField, hpush]
  exact φ.pullbackTangent_pushforwardTangent x (X x)

@[simp] theorem pushforwardVectorField_pullbackVectorField
    (X : Π x : M, TM x) :
    φ.pushforwardVectorField (φ.pullbackVectorField X) = X := by
  funext y
  have hcore :
      cast (congrArg (fun z : M => TM z) (φ.apply_symm_apply y))
          (φ.pushforwardTangent (φ.symm y)
            (φ.pullbackTangent (φ.symm y) (X (φ (φ.symm y))))) =
        cast (congrArg (fun z : M => TM z) (φ.apply_symm_apply y))
          (X (φ (φ.symm y))) := by
    exact congrArg
      (fun v : TM (φ (φ.symm y)) =>
        cast (congrArg (fun z : M => TM z) (φ.apply_symm_apply y)) v)
      (φ.pushforwardTangent_pullbackTangent (φ.symm y) (X (φ (φ.symm y))))
  have hcast :
      cast (congrArg (fun z : M => TM z) (φ.apply_symm_apply y))
        (X (φ (φ.symm y))) = X y := by
    exact Function.LeftInverse.cast_eq
      (γ := fun z : M => TM z)
      (f := φ.symm) (g := φ) (h := φ.apply_symm_apply) (C := X) y
  unfold SmoothSelfDiffeomorph.pushforwardVectorField SmoothSelfDiffeomorph.pullbackVectorField
  exact hcore.trans hcast

lemma mfderiv_isInvertible (x : M) :
    (mfderiv I I (φ : M → M) x).IsInvertible := by
  rw [← φ.pushforwardTangent_eq_mfderiv x]
  simpa [SmoothSelfDiffeomorph.pushforwardTangent, SmoothSelfDiffeomorph.tangentMap] using
    (isInvertible_equiv : (φ.tangentMap x : TM x →L[ℝ] TM (φ x)).IsInvertible)

lemma pullbackTangent_eq_inverse (x : M) :
    φ.pullbackTangent x = (mfderiv I I (φ : M → M) x).inverse := by
  symm
  apply ContinuousLinearMap.inverse_eq
  · ext u
    rw [← φ.pushforwardTangent_eq_mfderiv x]
    exact φ.pushforwardTangent_pullbackTangent x u
  · ext u
    rw [← φ.pushforwardTangent_eq_mfderiv x]
    exact φ.pullbackTangent_pushforwardTangent x u

theorem pullbackVectorField_eq_mpullback
    (X : Π x : M, TM x) :
    φ.pullbackVectorField X = VectorField.mpullback I I (φ : M → M) X := by
  funext x
  rw [SmoothSelfDiffeomorph.pullbackVectorField, VectorField.mpullback_apply,
    φ.pullbackTangent_eq_inverse x]

/-- Pulling back a continuous tangent-vector field along a `C^1` self-diffeomorphism stays
continuous in the manifold direction. This is the `m = 0`, `n = 1` instance of mathlib's
manifold vector-field pullback regularity theorem, specialized to bundled self-diffeomorphisms. -/
theorem contMDiff_zero_pullbackVectorField
    {X : Π x : M, TM x}
    (hX : ContMDiff I I.tangent 0 (T% X)) :
    ContMDiff I I.tangent 0 (T% (φ.pullbackVectorField X)) := by
  rw [φ.pullbackVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ : M → M)) φ.contMDiff
    (fun x => φ.mfderiv_isInvertible x) (by simp)

end SmoothSelfDiffeomorph

/-- A bundled `C^2` self-diffeomorphism of the manifold. This is the natural regularity level for
transporting `C^1` tangent-vector fields via mathlib's manifold pullback theory. -/
abbrev SmoothSelfDiffeomorph2 := M ≃ₘ^2⟮I, I⟯ M

/-- A time-dependent family of bundled `C^2` self-diffeomorphisms. This is the regularity level
needed to transport `C^1` tangent-vector fields slice-by-slice. -/
abbrev SmoothSelfDiffeomorph2Family :=
  CovariantDerivative.TimeFamily (SmoothSelfDiffeomorph2 (I := I) (M := M))

namespace SmoothSelfDiffeomorph2Family

/-- The constant identity family of bundled `C²` self-diffeomorphisms. -/
def id : SmoothSelfDiffeomorph2Family (I := I) (M := M) :=
  fun _ ↦ Diffeomorph.refl I M (2 : WithTop ℕ∞)

@[simp] lemma id_apply (t : ℝ) :
    SmoothSelfDiffeomorph2Family.id (I := I) (M := M) t =
      Diffeomorph.refl I M (2 : WithTop ℕ∞) := rfl

variable (Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M))

/-- Forget one derivative and regard a `C^2` diffeomorphism family as a `C^1` one. -/
def toSmoothSelfDiffeomorphFamily : SmoothSelfDiffeomorphFamily (I := I) (M := M) :=
  fun t ↦
    { toEquiv := (Φ t).toEquiv
      contMDiff_toFun := (Φ t).contMDiff.of_le (by norm_num)
      contMDiff_invFun := (Φ t).symm.contMDiff.of_le (by norm_num) }

@[simp] lemma toSmoothSelfDiffeomorphFamily_apply (t : ℝ) :
    Φ.toSmoothSelfDiffeomorphFamily t = {
      toEquiv := (Φ t).toEquiv
      contMDiff_toFun := (Φ t).contMDiff.of_le (by norm_num)
      contMDiff_invFun := (Φ t).symm.contMDiff.of_le (by norm_num) } := rfl

/-- Forget the inverse data and regard a `C^2` diffeomorphism family as a family of bundled `C^1`
self-maps. -/
def toSmoothSelfMapFamily : SmoothSelfMapFamily (I := I) (M := M) :=
  Φ.toSmoothSelfDiffeomorphFamily.toSmoothSelfMapFamily

@[simp] lemma toSmoothSelfMapFamily_apply (t : ℝ) :
    Φ.toSmoothSelfMapFamily t = (Φ.toSmoothSelfDiffeomorphFamily t :
      SmoothSelfMap (I := I) (M := M)) := rfl

@[simp] lemma id_toSmoothSelfMapFamily :
    (SmoothSelfDiffeomorph2Family.id (I := I) (M := M)).toSmoothSelfMapFamily =
      SmoothSelfMapFamily.id (I := I) (M := M) := by
  funext t
  rfl

lemma id_satisfiesGaugeFlowOn_of_eq_zero
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      (SmoothSelfDiffeomorph2Family.id (I := I) (M := M)).toSmoothSelfMapFamily X s := by
  simpa using
    SmoothSelfMapFamily.id_satisfiesGaugeFlowOn_of_eq_zero
      (I := I) (M := M) (X := X) (s := s) hX

/-- A `C^2` diffeomorphism family is anchored at `t₀` if its time slice there is the identity
diffeomorphism. -/
def AnchoredAt (t₀ : ℝ) : Prop :=
  Φ t₀ = Diffeomorph.refl I M (2 : WithTop ℕ∞)

@[simp] lemma id_anchoredAt (t₀ : ℝ) :
    (SmoothSelfDiffeomorph2Family.id (I := I) (M := M)).AnchoredAt t₀ := rfl

lemma AnchoredAt.apply
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (x : M) :
    Φ t₀ x = x := by
  rw [SmoothSelfDiffeomorph2Family.AnchoredAt] at hΦ
  rw [hΦ]
  rfl

lemma AnchoredAt.toSmoothSelfDiffeomorphAnchoredAt
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    Φ.toSmoothSelfDiffeomorphFamily.AnchoredAt t₀ := by
  change {
      toEquiv := (Φ t₀).toEquiv
      contMDiff_toFun := (Φ t₀).contMDiff.of_le (by norm_num)
      contMDiff_invFun := (Φ t₀).symm.contMDiff.of_le (by norm_num)
    } = Diffeomorph.refl I M (1 : WithTop ℕ∞)
  rw [hΦ]
  rfl

lemma AnchoredAt.toMapAnchoredAt
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    RicciFlow.AnchoredAt (I := I) (M := M) Φ.toSmoothSelfMapFamily t₀ := by
  exact hΦ.toSmoothSelfDiffeomorphAnchoredAt.toMapAnchoredAt

end SmoothSelfDiffeomorph2Family

namespace SmoothSelfDiffeomorph2

variable (φ : SmoothSelfDiffeomorph2 (I := I) (M := M))

local notation "TStar" => (fun x : M ↦ TM x →L[ℝ] ℝ)
local notation "BilF" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "EndF" => (E →L[ℝ] E)
local notation "OneF" => (E →L[ℝ] ℝ)

/-- Forget one derivative and regard a `C^2` self-diffeomorphism as a `C^1` one. -/
def toSmoothSelfDiffeomorph : SmoothSelfDiffeomorph (I := I) (M := M) :=
  { toEquiv := φ.toEquiv
    contMDiff_toFun := φ.contMDiff.of_le (by norm_num)
    contMDiff_invFun := φ.symm.contMDiff.of_le (by norm_num) }

/-- The tangent map of a bundled `C^2` self-diffeomorphism is a continuous linear equivalence on
each tangent space. -/
noncomputable abbrev tangentMap (x : M) : TM x ≃L[ℝ] TM (φ x) :=
  φ.mfderivToContinuousLinearEquiv (by simp) x

/-- Forward tangent transport along a bundled `C^2` self-diffeomorphism. -/
abbrev pushforwardTangent (x : M) : TM x →L[ℝ] TM (φ x) :=
  φ.tangentMap x

/-- Backward tangent transport along a bundled `C^2` self-diffeomorphism. -/
abbrev pullbackTangent (x : M) : TM (φ x) →L[ℝ] TM x :=
  (φ.tangentMap x).symm

/-- Pull back a bilinear form on `T_(φ x)M` along the tangent equivalence induced by `φ`. -/
noncomputable def pullbackBilinearForm (x : M) :
    (TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ) →L[ℝ] (TM x →L[ℝ] TM x →L[ℝ] ℝ) :=
  ((((φ.tangentMap x).symm).arrowCongr
      (((φ.tangentMap x).symm).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).toContinuousLinearMap)

@[simp] lemma pullbackBilinearForm_apply
    (x : M)
    (B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ)
    (u : TM x) :
    φ.pullbackBilinearForm x B u =
      (((φ.tangentMap x).symm).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
        (B (φ.pushforwardTangent x u)) := by
  simpa [SmoothSelfDiffeomorph2.pullbackBilinearForm, SmoothSelfDiffeomorph2.pushforwardTangent]
    using
      (ContinuousLinearEquiv.arrowCongr_apply
        ((φ.tangentMap x).symm)
        (((φ.tangentMap x).symm).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) B u)

@[simp] lemma pullbackBilinearForm_apply_apply
    (x : M)
    (B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ)
    (u v : TM x) :
    φ.pullbackBilinearForm x B u v =
      B (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
  rw [φ.pullbackBilinearForm_apply]
  simpa [SmoothSelfDiffeomorph2.pushforwardTangent] using
    (ContinuousLinearEquiv.arrowCongr_apply ((φ.tangentMap x).symm)
      (ContinuousLinearEquiv.refl ℝ ℝ) (B (φ.pushforwardTangent x u)) v)

lemma pullbackBilinearForm_symm
    (x : M)
    {B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ}
    (hB : ∀ u v : TM (φ x), B u v = B v u) :
    ∀ u v : TM x, φ.pullbackBilinearForm x B u v = φ.pullbackBilinearForm x B v u := by
  intro u v
  rw [φ.pullbackBilinearForm_apply_apply, φ.pullbackBilinearForm_apply_apply, hB]

lemma pullbackBilinearForm_pos
    (x : M)
    {B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ}
    (hB : ∀ u : TM (φ x), u ≠ 0 → 0 < B u u) :
    ∀ u : TM x, u ≠ 0 → 0 < φ.pullbackBilinearForm x B u u := by
  intro u hu
  have hpush : φ.pushforwardTangent x u ≠ 0 := by
    intro hzero
    apply hu
    have := congrArg (φ.pullbackTangent x) hzero
    simpa using this
  simpa [φ.pullbackBilinearForm_apply_apply] using hB (φ.pushforwardTangent x u) hpush

lemma pullbackBilinearForm_lt_one_eq_image
    (x : M)
    (B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ) :
    {u : TM x | φ.pullbackBilinearForm x B u u < 1} =
      φ.pullbackTangent x '' {v : TM (φ x) | B v v < 1} := by
  ext u
  constructor
  · intro hu
    refine ⟨φ.pushforwardTangent x u, ?_, ?_⟩
    · simpa [φ.pullbackBilinearForm_apply_apply] using hu
    · simpa using (φ.pullbackTangent_pushforwardTangent x u).symm
  · rintro ⟨v, hv, rfl⟩
    simpa [φ.pullbackBilinearForm_apply_apply] using hv

lemma isVonNBounded_pullbackBilinearForm
    (x : M)
    {B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ}
    (hB : Bornology.IsVonNBounded ℝ {v : TM (φ x) | B v v < 1}) :
    Bornology.IsVonNBounded ℝ {u : TM x | φ.pullbackBilinearForm x B u u < 1} := by
  rw [φ.pullbackBilinearForm_lt_one_eq_image (x := x) (B := B)]
  exact Bornology.IsVonNBounded.image hB (φ.pullbackTangent x)

/-- The tangent-map coordinates coming from `inTangentCoordinates` agree with the standard
continuous-linear-map bundle coordinates. -/
lemma tangentCoord_eq_inCoordinates (x0 x : M)
    (hx : x ∈ (trivializationAt E TM x0).baseSet)
    (hφx : φ x ∈ (trivializationAt E TM (φ x0)).baseSet) :
    inTangentCoordinates I I (_root_.id : M → M) (φ : M → M)
      (fun y ↦ mfderiv I I (φ : M → M) y) x0 x =
      ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
        (φ.pushforwardTangent x) := by
  rw [inTangentCoordinates_eq (I := I) (I' := I) (f := (_root_.id : M → M))
    (g := (φ : M → M)) (ϕ := fun y ↦ mfderiv I I (φ : M → M) y) (x₀ := x0) (x := x) hx hφx]
  rw [ContinuousLinearMap.inCoordinates_eq (x₀ := x0) (x := x) (y₀ := φ x0) (y := φ x)
    (ϕ := φ.pushforwardTangent x) hx hφx]
  rw [Trivialization.coe_continuousLinearEquivAt_eq' _ hφx,
    Trivialization.symm_continuousLinearEquivAt_eq' _ hx,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (b₀ := φ x0) (b := φ x)
      hφx,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := x0) (b := x) hx]
  rw [show φ.pushforwardTangent x = mfderiv I I (φ : M → M) x by
      simpa [SmoothSelfDiffeomorph2.pushforwardTangent, SmoothSelfDiffeomorph2.tangentMap] using
        (Diffeomorph.mfderivToContinuousLinearEquiv_coe
          (I := I) (J := I) (Φ := φ) (x := x) (hn := by simp))]
  rfl

/-- In preferred local coordinates, the pulled-back bilinear form is obtained by composing the
target bilinear form with the coordinate representation of the tangent map in both slots. -/
lemma coord_pullbackBilinearForm_eq (x0 x : M)
    (hx : x ∈ (trivializationAt E TM x0).baseSet)
    (hφx : φ x ∈ (trivializationAt E TM (φ x0)).baseSet)
    (B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates E TM OneF TStar x0 x x0 x
        (φ.pullbackBilinearForm x B) =
      let A : EndF :=
        ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
          (φ.pushforwardTangent x)
      let Bc : BilF :=
        ContinuousLinearMap.inCoordinates E TM OneF TStar (φ x0) (φ x) (φ x0) (φ x) B
      (A.precomp ℝ).comp (Bc.comp A) := by
  let A : EndF :=
    ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
      (φ.pushforwardTangent x)
  let Bc : BilF :=
    ContinuousLinearMap.inCoordinates E TM OneF TStar (φ x0) (φ x) (φ x0) (φ x) B
  ext u v
  have hAeq :
      A u =
        ((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx)
          (φ.pushforwardTangent x
            (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm u)) := by
    change ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
        (φ.pushforwardTangent x) u =
      ((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx)
        (φ.pushforwardTangent x
          (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm u))
    rw [ContinuousLinearMap.inCoordinates_eq (x₀ := x0) (x := x) (y₀ := φ x0) (y := φ x)
      (ϕ := φ.pushforwardTangent x) hx hφx]
    rfl
  have hBceq :
      Bc (A u) (A v) =
        B (((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx).symm (A u))
          (((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx).symm (A v)) := by
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := φ x0) (x := φ x) hφx B (A u) (A v)]
  have hAu :
      ((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx).symm (A u) =
        φ.pushforwardTangent x
          (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm u) := by
    rw [hAeq]
    simpa using
      (((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx).symm_apply_apply
        (φ.pushforwardTangent x
          (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm u)))
  have hAv :
      ((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx).symm (A v) =
        φ.pushforwardTangent x
          (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm v) := by
    have hAeqv :
        A v =
          ((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx)
            (φ.pushforwardTangent x
              (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm v)) := by
      change ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
          (φ.pushforwardTangent x) v =
        ((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx)
          (φ.pushforwardTangent x
            (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm v))
      rw [ContinuousLinearMap.inCoordinates_eq (x₀ := x0) (x := x) (y₀ := φ x0) (y := φ x)
        (ϕ := φ.pushforwardTangent x) hx hφx]
      rfl
    rw [hAeqv]
    simpa using
      (((trivializationAt E TM (φ x0)).continuousLinearEquivAt ℝ (φ x) hφx).symm_apply_apply
        (φ.pushforwardTangent x
          (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm v)))
  calc
    ContinuousLinearMap.inCoordinates E TM OneF TStar x0 x x0 x
        (φ.pullbackBilinearForm x B) u v
      = φ.pullbackBilinearForm x B
          (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm u)
          (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm v) := by
            erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
              (x0 := x0) (x := x) hx (φ.pullbackBilinearForm x B) u v]
    _ = B
          (φ.pushforwardTangent x
            (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm u))
          (φ.pushforwardTangent x
            (((trivializationAt E TM x0).continuousLinearEquivAt ℝ x hx).symm v)) := by
            rw [φ.pullbackBilinearForm_apply_apply]
    _ = Bc (A u) (A v) := by
          rw [hBceq, hAu, hAv]
    _ = ((A.precomp ℝ).comp (Bc.comp A)) u v := by
          simp [ContinuousLinearMap.precomp_apply]

/-- The coordinate representation of the pulled-back metric is `C^1`, as expected from pulling a
`C^2` metric back along a `C^2` diffeomorphism. -/
lemma contMDiffAt_coord_pullbackBilinearForm
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) (x0 : M) :
    ContMDiffAt I 𝓘(ℝ, BilF) 1
      (fun x ↦ ContinuousLinearMap.inCoordinates E TM OneF TStar x0 x x0 x
        (φ.pullbackBilinearForm x (g.inner (φ x)))) x0 := by
  let Acoord : M → EndF := fun x ↦
    inTangentCoordinates I I (_root_.id : M → M) (φ : M → M)
      (fun y ↦ mfderiv I I (φ : M → M) y) x0 x
  let Bbase : M → BilF := fun y ↦
    ContinuousLinearMap.inCoordinates E TM OneF TStar (φ x0) y (φ x0) y (g.inner y)
  let Bcoord : M → BilF := fun x ↦ Bbase (φ x)
  let expr : M → BilF := fun x ↦
    (((Acoord x).precomp ℝ : OneF →L[ℝ] OneF)).comp ((Bcoord x).comp (Acoord x))
  have hA : ContMDiffAt I 𝓘(ℝ, EndF) 1 Acoord x0 := by
    simpa [Acoord] using
      (ContMDiffAt.mfderiv_const (I := I) (I' := I) (n := 2) (m := 1)
        (hf := φ.contMDiffAt) (by norm_num))
  have hBbase : ContMDiffAt I 𝓘(ℝ, BilF) 2 Bbase (φ x0) := by
    let f : M → TotalSpace BilF (fun y : M ↦ TM y →L[ℝ] TStar y) :=
      fun y ↦ TotalSpace.mk' BilF y (g.inner y)
    exact ((contMDiffAt_hom_bundle (f := f) (x₀ := φ x0)).mp (g.contMDiff (φ x0))).2
  have hBcoord : ContMDiffAt I 𝓘(ℝ, BilF) 1 Bcoord x0 := by
    exact (hBbase.of_le (by norm_num)).comp x0 (φ.contMDiffAt.of_le (by norm_num))
  have hExpr : ContMDiffAt I 𝓘(ℝ, BilF) 1 expr x0 := by
    have hMid : ContMDiffAt I 𝓘(ℝ, BilF) 1 (fun x ↦ (Bcoord x).comp (Acoord x)) x0 := by
      exact hBcoord.clm_comp hA
    have hPost : ContMDiffAt I 𝓘(ℝ, OneF →L[ℝ] OneF) 1
        (fun x ↦ ((Acoord x).precomp ℝ : OneF →L[ℝ] OneF)) x0 := by
      simpa using
        (ContMDiffAt.clm_precomp (I := I) (n := 1) (F₁ := E) (F₂ := E) (F₃ := ℝ)
          (f := Acoord) (x := x0) hA)
    exact hPost.clm_comp hMid
  have hEq : expr =ᶠ[𝓝 x0] (fun x ↦ ContinuousLinearMap.inCoordinates E TM OneF TStar x0 x x0 x
      (φ.pullbackBilinearForm x (g.inner (φ x)))) := by
    have hx :
        {x : M | x ∈ (trivializationAt E TM x0).baseSet} ∈ 𝓝 x0 :=
      (trivializationAt E TM x0).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x0)
    have hφ :
        {x : M | φ x ∈ (trivializationAt E TM (φ x0)).baseSet} ∈ 𝓝 x0 := by
      exact (φ.continuous.continuousAt).preimage_mem_nhds <|
        (trivializationAt E TM (φ x0)).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (φ x0))
    filter_upwards [hx, hφ] with x hx' hφx'
    have hAraw :
        Acoord x =
          ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
            (φ.pushforwardTangent x) := by
      simpa [Acoord] using φ.tangentCoord_eq_inCoordinates (x0 := x0) (x := x) hx' hφx'
    rw [show expr x =
        (((Acoord x).precomp ℝ : OneF →L[ℝ] OneF)).comp ((Bcoord x).comp (Acoord x)) by rfl]
    rw [φ.coord_pullbackBilinearForm_eq (x0 := x0) (x := x) hx' hφx' (g.inner (φ x))]
    simp [hAraw, Bcoord, Bbase]
  exact hExpr.congr_of_eventuallyEq hEq.symm

/-- Pulling a `C^2` metric back along a bundled `C^2` self-diffeomorphism produces the expected
`C^1` Riemannian metric on the source manifold. -/
def pullbackRiemannianMetric
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    Bundle.ContMDiffRiemannianMetric I 1 E TM where
  inner x := φ.pullbackBilinearForm x (g.inner (φ x))
  symm x u v := φ.pullbackBilinearForm_symm x (fun u v => g.symm (φ x) u v) u v
  pos x u hu := φ.pullbackBilinearForm_pos x (fun u hu => g.pos (φ x) u hu) u hu
  isVonNBounded x := φ.isVonNBounded_pullbackBilinearForm x (g.isVonNBounded (φ x))
  contMDiff := by
    intro x0
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    change ContMDiffAt I 𝓘(ℝ, BilF) 1
      (fun x ↦ ContinuousLinearMap.inCoordinates E TM OneF TStar x0 x x0 x
        (φ.pullbackBilinearForm x (g.inner (φ x)))) x0
    exact φ.contMDiffAt_coord_pullbackBilinearForm g x0

@[simp] lemma pullbackRiemannianMetric_inner
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (x : M) (u v : TM x) :
    (φ.pullbackRiemannianMetric g).inner x u v =
      g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
  rfl

/-- On zero-dimensional tangent fibers, every component of a `C^2` diffeomorphism-pulled metric
vanishes. -/
lemma pullbackRiemannianMetric_inner_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (x : M) (u v : TM x) :
    (φ.pullbackRiemannianMetric g).inner x u v = 0 := by
  rw [pullbackRiemannianMetric_inner]
  have hu : φ.pushforwardTangent x u = 0 := Subsingleton.elim _ _
  rw [hu]
  simp

lemma pushforwardTangent_rieszMap_of_pullback_inner
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E TM}
    (hinner : ∀ x : M, ∀ u v : TM x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    {x : M}
    (omegaSrc : TM x →L[ℝ] ℝ) (omegaTgt : TM (φ x) →L[ℝ] ℝ)
    (hω : ∀ u : TM x, omegaSrc u = omegaTgt (φ.pushforwardTangent x u)) :
    φ.pushforwardTangent x
        (letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩
         CovariantDerivative.rieszMap (I := I) x omegaSrc) =
      (letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
       CovariantDerivative.rieszMap (I := I) (φ x) omegaTgt) := by
  let Rsrc : TM x := by
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩
    exact CovariantDerivative.rieszMap (I := I) x omegaSrc
  let Rtgt : TM (φ x) := by
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    exact CovariantDerivative.rieszMap (I := I) (φ x) omegaTgt
  change φ.pushforwardTangent x Rsrc = Rtgt
  letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro z
  have htransport :
      g.inner (φ x) (φ.pushforwardTangent x Rsrc) z =
        g'.inner x Rsrc (φ.pullbackTangent x z) := by
    have h := hinner x Rsrc (φ.pullbackTangent x z)
    simpa using h.symm
  have hsrc :
      g'.inner x Rsrc (φ.pullbackTangent x z) =
        omegaSrc (φ.pullbackTangent x z) := by
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩
    change inner ℝ Rsrc (φ.pullbackTangent x z) = omegaSrc (φ.pullbackTangent x z)
    exact
      (CovariantDerivative.rieszMap_apply_inner
        (I := I) x omegaSrc (φ.pullbackTangent x z))
  have htgt :
      g.inner (φ x) Rtgt z = omegaTgt z := by
    change inner ℝ Rtgt z = omegaTgt z
    exact
      (CovariantDerivative.rieszMap_apply_inner (I := I) (φ x) omegaTgt z)
  have hpb : φ.pushforwardTangent x (φ.pullbackTangent x z) = z :=
    (φ.tangentMap x).apply_symm_apply z
  change
    g.inner (φ x) (φ.pushforwardTangent x Rsrc) z =
      g.inner (φ x) Rtgt z
  calc
    g.inner (φ x) (φ.pushforwardTangent x Rsrc) z =
        g'.inner x Rsrc (φ.pullbackTangent x z) := htransport
    _ = omegaSrc (φ.pullbackTangent x z) := hsrc
    _ = omegaTgt (φ.pushforwardTangent x (φ.pullbackTangent x z)) :=
      hω (φ.pullbackTangent x z)
    _ = omegaTgt z := by rw [hpb]
    _ = g.inner (φ x) Rtgt z := htgt.symm

lemma pullbackRiemannianMetric_eq_of_eq_id
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (hφ : φ = Diffeomorph.refl I M (2 : WithTop ℕ∞)) :
    φ.pullbackRiemannianMetric g =
      ({ g with contMDiff := g.contMDiff.of_le (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) := by
  ext x u v
  subst hφ
  let φid : SmoothSelfDiffeomorph2 (I := I) (M := M) := Diffeomorph.refl I M (2 : WithTop ℕ∞)
  change
    g.inner ((_root_.id : M → M) x)
        (φid.pushforwardTangent x u)
        (φid.pushforwardTangent x v) =
      g.inner x u v
  have hu1 :
      φid.pushforwardTangent x u =
        (mfderiv I I (φid : M → M) x) u := by
    simpa [SmoothSelfDiffeomorph2.pushforwardTangent, SmoothSelfDiffeomorph2.tangentMap] using
      congrArg (fun f : TM x →L[ℝ] TM (φid x) => f u)
        (Diffeomorph.mfderivToContinuousLinearEquiv_coe
          (I := I) (J := I) (Φ := φid)
          (x := x) (hn := by simp))
  have hv1 :
      φid.pushforwardTangent x v =
        (mfderiv I I (φid : M → M) x) v := by
    simpa [SmoothSelfDiffeomorph2.pushforwardTangent, SmoothSelfDiffeomorph2.tangentMap] using
      congrArg (fun f : TM x →L[ℝ] TM (φid x) => f v)
        (Diffeomorph.mfderivToContinuousLinearEquiv_coe
          (I := I) (J := I) (Φ := φid)
          (x := x) (hn := by simp))
  have hu0 :
      (mfderiv I I (φid : M → M) x) u =
        (ContinuousLinearMap.id ℝ (TM x)) u := by
    change (mfderiv I I (_root_.id : M → M) x) u =
      (ContinuousLinearMap.id ℝ (TM x)) u
    exact congrArg (fun f : TM x →L[ℝ] TM x => f u) (mfderiv_id (I := I) (x := x))
  have hv0 :
      (mfderiv I I (φid : M → M) x) v =
        (ContinuousLinearMap.id ℝ (TM x)) v := by
    change (mfderiv I I (_root_.id : M → M) x) v =
      (ContinuousLinearMap.id ℝ (TM x)) v
    exact congrArg (fun f : TM x →L[ℝ] TM x => f v) (mfderiv_id (I := I) (x := x))
  have hu : φid.pushforwardTangent x u = u := by
    simpa using hu1.trans hu0
  have hv : φid.pushforwardTangent x v = v := by
    simpa using hv1.trans hv0
  rw [hu, hv]
  rfl

/-- The tangent transport agrees with the manifold derivative. -/
lemma pushforwardTangent_eq_mfderiv (x : M) :
    φ.pushforwardTangent x = mfderiv I I (φ : M → M) x := by
  simpa [SmoothSelfDiffeomorph2.pushforwardTangent, SmoothSelfDiffeomorph2.tangentMap] using
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (I := I) (J := I) (Φ := φ) (x := x) (hn := by simp))

@[simp] lemma pushforwardTangent_apply (x : M) (u : TM x) :
    φ.pushforwardTangent x u = (mfderiv I I (φ : M → M) x) u := by
  simpa using congrArg (fun f : TM x →L[ℝ] TM (φ x) => f u)
    (φ.pushforwardTangent_eq_mfderiv x)

@[simp] lemma pullbackTangent_pushforwardTangent (x : M) (u : TM x) :
    φ.pullbackTangent x (φ.pushforwardTangent x u) = u := by
  exact (φ.tangentMap x).symm_apply_apply u

@[simp] lemma pushforwardTangent_pullbackTangent (x : M) (u : TM (φ x)) :
    φ.pushforwardTangent x (φ.pullbackTangent x u) = u := by
  exact (φ.tangentMap x).apply_symm_apply u

/-- Pull back a tangent-vector field along a bundled `C^2` self-diffeomorphism. -/
def pullbackVectorField
    (X : Π x : M, TM x) :
    Π x : M, TM x :=
  fun x ↦ φ.pullbackTangent x (X (φ x))

/-- Push forward a tangent-vector field along a bundled `C^2` self-diffeomorphism. Defining this as
pullback along the inverse makes the `C^1` regularity theorem immediate from the pullback theory. -/
def pushforwardVectorField
    (X : Π x : M, TM x) :
    Π x : M, TM x :=
  SmoothSelfDiffeomorph2.pullbackVectorField
    (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) X

@[simp] lemma pullbackVectorField_apply
    (X : Π x : M, TM x) (x : M) :
    φ.pullbackVectorField X x = φ.pullbackTangent x (X (φ x)) := rfl

@[simp] lemma pushforwardVectorField_apply
    (X : Π x : M, TM x) (x : M) :
    φ.pushforwardVectorField X x =
      SmoothSelfDiffeomorph2.pullbackTangent
        (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) x
        (X (φ.symm x)) := rfl

@[simp] theorem pullbackVectorField_add
    (X Y : Π x : M, TM x) :
    φ.pullbackVectorField (X + Y) = φ.pullbackVectorField X + φ.pullbackVectorField Y := by
  funext x
  simp [SmoothSelfDiffeomorph2.pullbackVectorField]

@[simp] theorem pushforwardVectorField_add
    (X Y : Π x : M, TM x) :
    φ.pushforwardVectorField (X + Y) = φ.pushforwardVectorField X + φ.pushforwardVectorField Y := by
  funext x
  simp [SmoothSelfDiffeomorph2.pushforwardVectorField]

theorem pullbackVectorField_smul
    (g : M → ℝ) (X : Π x : M, TM x) :
    φ.pullbackVectorField (g • X) = (g ∘ φ) • φ.pullbackVectorField X := by
  funext x
  simp [SmoothSelfDiffeomorph2.pullbackVectorField]

theorem pushforwardVectorField_smul
    (g : M → ℝ) (X : Π x : M, TM x) :
    φ.pushforwardVectorField (g • X) = (g ∘ φ.symm) • φ.pushforwardVectorField X := by
  funext x
  simp [SmoothSelfDiffeomorph2.pushforwardVectorField]

lemma mfderiv_isInvertible (x : M) :
    (mfderiv I I (φ : M → M) x).IsInvertible := by
  let e : TM x ≃L[ℝ] TM (φ x) := φ.mfderivToContinuousLinearEquiv (by simp) x
  have he :
      (e : TM x →L[ℝ] TM (φ x)) = mfderiv I I (φ : M → M) x := by
    simpa [e] using
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (I := I) (J := I) (Φ := φ) (x := x) (hn := by simp))
  rw [← he]
  exact ContinuousLinearMap.isInvertible_equiv

lemma pullbackVectorField_value_eq_inverse
    (X : Π x : M, TM x) (x : M) :
    (φ.mfderivToContinuousLinearEquiv (by simp) x).symm (X (φ x)) =
      (mfderiv I I (φ : M → M) x).inverse (X (φ x)) := by
  let e : TM x ≃L[ℝ] TM (φ x) := φ.mfderivToContinuousLinearEquiv (by simp) x
  have he :
      (e : TM x →L[ℝ] TM (φ x)) = mfderiv I I (φ : M → M) x := by
    simpa [e] using
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (I := I) (J := I) (Φ := φ) (x := x) (hn := by simp))
  have hinv :
      (mfderiv I I (φ : M → M) x).inverse =
        (e : TM x ≃L[ℝ] TM (φ x)).symm := by
    apply ContinuousLinearMap.inverse_eq
    · ext u
      rw [← he]
      simp
    · ext u
      rw [← he]
      simp
  change e.symm (X (φ x)) = (mfderiv I I (φ : M → M) x).inverse (X (φ x))
  simpa [hinv]

lemma pullbackVectorField_eq_mpullback
    (X : Π x : M, TM x) :
    φ.pullbackVectorField X = VectorField.mpullback I I (φ : M → M) X := by
  funext x
  rw [SmoothSelfDiffeomorph2.pullbackVectorField, VectorField.mpullback_apply]
  symm
  exact (φ.pullbackVectorField_value_eq_inverse X x).symm

lemma pushforwardVectorField_eq_mpullback
    (X : Π x : M, TM x) :
    φ.pushforwardVectorField X = VectorField.mpullback I I (φ.symm : M → M) X := by
  simpa [SmoothSelfDiffeomorph2.pushforwardVectorField] using
    (SmoothSelfDiffeomorph2.pullbackVectorField_eq_mpullback
      (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) (X := X))

/-- Pulling back a `C^1` tangent-vector field along a `C^2` self-diffeomorphism stays `C^1`. This
is the exact regularity upgrade needed before defining a pulled-back affine connection. -/
theorem contMDiff_one_pullbackVectorField
    {X : Π x : M, TM x}
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    ContMDiff I I.tangent 1 (T% (φ.pullbackVectorField X)) := by
  rw [φ.pullbackVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ : M → M)) φ.contMDiff
    (fun x => φ.mfderiv_isInvertible x) (by norm_num)

/-- Pushing forward a `C^1` tangent-vector field along a `C^2` self-diffeomorphism stays `C^1`.
This gives the forward half of the regularity package needed to transport affine-connection data. -/
theorem contMDiff_one_pushforwardVectorField
    {X : Π x : M, TM x}
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    ContMDiff I I.tangent 1 (T% (φ.pushforwardVectorField X)) := by
  rw [φ.pushforwardVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ.symm : M → M)) φ.symm.contMDiff
    (fun x =>
      SmoothSelfDiffeomorph2.mfderiv_isInvertible
        (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) x)
    (by norm_num)

/-- Pointwise differentiability of vector fields is preserved under `C^2` pullback. -/
theorem mdifferentiableAt_pullbackVectorField
    {X : Π x : M, TM x} {x : M}
    (hX : MDiffAt (T% X) (φ x)) :
    MDiffAt (T% (φ.pullbackVectorField X)) x := by
  rw [φ.pullbackVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ : M → M)) φ.contMDiffAt
    (φ.mfderiv_isInvertible x) (by norm_num)

/-- Differentiable vector fields stay differentiable after `C^2` pullback. -/
theorem mdifferentiable_pullbackVectorField
    {X : Π x : M, TM x}
    (hX : MDiff (T% X)) :
    MDiff (T% (φ.pullbackVectorField X)) := by
  rw [φ.pullbackVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ : M → M)) φ.contMDiff
    (fun x => φ.mfderiv_isInvertible x) (by norm_num)

/-- Pointwise differentiability of vector fields is preserved under `C^2` pushforward. -/
theorem mdifferentiableAt_pushforwardVectorField
    {X : Π x : M, TM x} {x : M}
    (hX : MDiffAt (T% X) (φ.symm x)) :
    MDiffAt (T% (φ.pushforwardVectorField X)) x := by
  rw [φ.pushforwardVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ.symm : M → M)) φ.symm.contMDiffAt
    (SmoothSelfDiffeomorph2.mfderiv_isInvertible
      (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) x)
    (by norm_num)

/-- Differentiable vector fields stay differentiable after `C^2` pushforward. -/
theorem mdifferentiable_pushforwardVectorField
    {X : Π x : M, TM x}
    (hX : MDiff (T% X)) :
    MDiff (T% (φ.pushforwardVectorField X)) := by
  rw [φ.pushforwardVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ.symm : M → M)) φ.symm.contMDiff
    (fun x =>
      SmoothSelfDiffeomorph2.mfderiv_isInvertible
        (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) x)
    (by norm_num)

/-- Pullback along a bundled `C^2` self-diffeomorphism commutes with the manifold Lie bracket. -/
theorem pullbackVectorField_mlieBracket
    {X Y : Π x : M, TM x} {x : M}
    (hX : MDiffAt (T% X) (φ x)) (hY : MDiffAt (T% Y) (φ x)) :
    φ.pullbackVectorField (VectorField.mlieBracket I X Y) x =
      VectorField.mlieBracket I (φ.pullbackVectorField X) (φ.pullbackVectorField Y) x := by
  haveI : ENat.LEInfty (minSmoothness ℝ 2) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact inferInstance
  haveI : IsManifold I (minSmoothness ℝ 2) M := inferInstance
  rw [φ.pullbackVectorField_eq_mpullback (VectorField.mlieBracket I X Y),
    φ.pullbackVectorField_eq_mpullback X, φ.pullbackVectorField_eq_mpullback Y]
  exact VectorField.mpullback_mlieBracket (I := I) (I' := I) (f := (φ : M → M))
    (x₀ := x) hX hY φ.contMDiffAt (by simp)

/-- Pullback along a bundled `C^2` self-diffeomorphism commutes with the manifold Lie bracket,
globally. -/
theorem pullbackVectorField_mlieBracket_eq
    {X Y : Π x : M, TM x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    φ.pullbackVectorField (VectorField.mlieBracket I X Y) =
      VectorField.mlieBracket I (φ.pullbackVectorField X) (φ.pullbackVectorField Y) := by
  funext x
  exact φ.pullbackVectorField_mlieBracket (x := x) (hX (φ x)) (hY (φ x))

/-- Pushforward along a bundled `C^2` self-diffeomorphism commutes with the manifold Lie bracket,
globally. -/
theorem pushforwardVectorField_mlieBracket_eq
    {X Y : Π x : M, TM x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    φ.pushforwardVectorField (VectorField.mlieBracket I X Y) =
      VectorField.mlieBracket I (φ.pushforwardVectorField X) (φ.pushforwardVectorField Y) := by
  simpa [SmoothSelfDiffeomorph2.pushforwardVectorField] using
    (SmoothSelfDiffeomorph2.pullbackVectorField_mlieBracket_eq
      (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M)))
      (X := X) (Y := Y) hX hY)

@[simp] lemma mfderiv_symm_apply_pushforwardTangent (x : M) (u : TM x) :
    (mfderiv I I (φ.symm : M → M) (φ x)) (φ.pushforwardTangent x u) = u := by
  have hφ : MDifferentiableAt I I (φ : M → M) x :=
    φ.contMDiff.mdifferentiableAt (by simp)
  have hφsymm : MDifferentiableAt I I (φ.symm : M → M) (φ x) :=
    φ.symm.contMDiff.mdifferentiableAt (by simp)
  have hcomp :
      mfderiv I I ((φ.symm : M → M) ∘ (φ : M → M)) x u =
        (mfderiv I I (φ.symm : M → M) (φ x)) ((mfderiv I I (φ : M → M) x) u) :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (f := (φ : M → M)) (g := (φ.symm : M → M)) (x := x) hφsymm hφ u
  have hfun : ((φ.symm : M → M) ∘ (φ : M → M)) = (_root_.id : M → M) := by
    ext y
    simp [Function.comp]
  rw [mfderiv_congr (I := I) (I' := I) (x := x) hfun] at hcomp
  rw [φ.pushforwardTangent_eq_mfderiv]
  exact hcomp.symm.trans <|
    (congrArg (fun f : TM x →L[ℝ] TM x => f u) (mfderiv_id (I := I) (x := x))).trans
      (by rfl)

@[simp] lemma pushforwardTangent_mfderiv_symm_apply (x : M) (u : TM (φ x)) :
    φ.pushforwardTangent x ((mfderiv I I (φ.symm : M → M) (φ x)) u) = u := by
  have hφ : MDifferentiableAt I I (φ : M → M) (φ.symm (φ x)) :=
    φ.contMDiff.mdifferentiableAt (by simp)
  have hφsymm : MDifferentiableAt I I (φ.symm : M → M) (φ x) :=
    φ.symm.contMDiff.mdifferentiableAt (by simp)
  have hcomp :
      mfderiv I I ((φ : M → M) ∘ (φ.symm : M → M)) (φ x) u =
        (mfderiv I I (φ : M → M) (φ.symm (φ x)))
          ((mfderiv I I (φ.symm : M → M) (φ x)) u) :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (f := (φ.symm : M → M)) (g := (φ : M → M)) (x := φ x) hφ hφsymm u
  have hfun : ((φ : M → M) ∘ (φ.symm : M → M)) = (_root_.id : M → M) := by
    ext y
    simp [Function.comp]
  rw [mfderiv_congr (I := I) (I' := I) (x := φ x) hfun] at hcomp
  rw [mfderiv_congr_point (I := I) (I' := I) (f := (φ : M → M))
    (x := φ.symm (φ x)) (x' := x) (by simp)] at hcomp
  rw [φ.pushforwardTangent_eq_mfderiv]
  exact hcomp.symm.trans <|
    (congrArg (fun f : TM (φ x) →L[ℝ] TM (φ x) => f u)
      (mfderiv_id (I := I) (x := φ x))).trans (by rfl)
@[simp] lemma pushforwardVectorField_apply_image
    (X : Π x : M, TM x) (x : M) :
    φ.pushforwardVectorField X (φ x) = φ.pushforwardTangent x (X x) := by
  rw [φ.pushforwardVectorField_eq_mpullback X, VectorField.mpullback_apply]
  have hinv :
      (mfderiv I I (φ.symm : M → M) (φ x)).inverse = φ.pushforwardTangent x := by
    apply ContinuousLinearMap.inverse_eq
    · ext u
      change (mfderiv I I (φ.symm : M → M) (φ x))
          (φ.pushforwardTangent x u) = u
      exact φ.mfderiv_symm_apply_pushforwardTangent x u
    · ext u
      change φ.pushforwardTangent x ((mfderiv I I (φ.symm : M → M) (φ x)) u) = u
      exact φ.pushforwardTangent_mfderiv_symm_apply x u
  calc
    (mfderiv I I (φ.symm : M → M) (φ x)).inverse (X (φ.symm (φ x)))
      = φ.pushforwardTangent x (X (φ.symm (φ x))) := by
          rw [hinv]
          rfl
    _ = φ.pushforwardTangent x (X x) := by
          rw [φ.symm_apply_apply x]

@[simp] lemma pullbackTangent_pushforwardVectorField_apply_image
    (X : Π x : M, TM x) (x : M) :
    φ.pullbackTangent x (φ.pushforwardVectorField X (φ x)) = X x := by
  rw [φ.pushforwardVectorField_apply_image]
  simpa using φ.pullbackTangent_pushforwardTangent x (X x)

lemma extDerivFun_comp_symm_apply_pushforwardTangent
    {g : M → ℝ} {x : M} (hg : MDiffAt g x) (u : TM x) :
    mvfderiv (I := I) (g ∘ (φ.symm : M → M)) (φ x) (φ.pushforwardTangent x u) =
      mvfderiv (I := I) g x u := by
  have hg' : MDiffAt g (φ.symm (φ x)) := by simpa using hg
  have hφsymm : MDifferentiableAt I I (φ.symm : M → M) (φ x) :=
    φ.symm.contMDiff.mdifferentiableAt (by simp)
  have hcomp :
      mfderiv I 𝓘(ℝ, ℝ) (g ∘ (φ.symm : M → M)) (φ x) (φ.pushforwardTangent x u) =
        (mfderiv I 𝓘(ℝ, ℝ) g (φ.symm (φ x)))
          ((mfderiv I I (φ.symm : M → M) (φ x)) (φ.pushforwardTangent x u)) :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓘(ℝ, ℝ))
      (f := (φ.symm : M → M)) (g := g) (x := φ x) hg' hφsymm (φ.pushforwardTangent x u)
  rw [mvfderiv, mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hcomp, φ.mfderiv_symm_apply_pushforwardTangent]
  rw [mfderiv_congr_point (I := I) (I' := 𝓘(ℝ, ℝ)) (f := g)
    (x := φ.symm (φ x)) (x' := x) (by simp)]
  rw [show (g ∘ (φ.symm : M → M)) (φ x) = g x by simp [Function.comp]]
  rfl

lemma extDerivFun_comp_apply_pushforwardTangent
    {g : M → ℝ} {x : M} (hg : MDiffAt g (φ x)) (u : TM x) :
    mvfderiv (I := I) (g ∘ (φ : M → M)) x u =
      mvfderiv (I := I) g (φ x) (φ.pushforwardTangent x u) := by
  have hφ : MDifferentiableAt I I (φ : M → M) x :=
    φ.contMDiff.mdifferentiableAt (by simp)
  have hcomp :
      mfderiv I 𝓘(ℝ, ℝ) (g ∘ (φ : M → M)) x u =
        (mfderiv I 𝓘(ℝ, ℝ) g (φ x))
          ((mfderiv I I (φ : M → M) x) u) :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓘(ℝ, ℝ))
      (f := (φ : M → M)) (g := g) (x := x) hg hφ u
  rw [mvfderiv, mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hcomp, φ.pushforwardTangent_apply]
  rfl

lemma mdifferentiableAt_pushforwardVectorField_image
    {X : Π x : M, TM x} {x : M}
    (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (φ.pushforwardVectorField X)) (φ x) := by
  simpa using
    (SmoothSelfDiffeomorph2.mdifferentiableAt_pushforwardVectorField
      (φ := φ) (x := φ x) (X := X) (by simpa using hX))

/-- Pull back a tangent-bundle covariant derivative along a bundled `C^2` self-diffeomorphism. -/
noncomputable def pullbackCovariantDerivative
    (cov : CovariantDerivative I E TM) :
    CovariantDerivative I E TM where
  toFun := fun X x ↦
    (φ.pullbackTangent x).comp <|
      (cov (φ.pushforwardVectorField X) (φ x)).comp (φ.pushforwardTangent x)
  isCovariantDerivativeOnUniv := by
    refine
      { add := ?_
        leibniz := ?_ }
    · intro σ τ x hσ hτ hx
      have hσpush : MDiffAt (T% (φ.pushforwardVectorField σ)) (φ x) :=
        φ.mdifferentiableAt_pushforwardVectorField_image hσ
      have hτpush : MDiffAt (T% (φ.pushforwardVectorField τ)) (φ x) :=
        φ.mdifferentiableAt_pushforwardVectorField_image hτ
      have hadd :
          cov (φ.pushforwardVectorField (σ + τ)) (φ x) =
            cov (φ.pushforwardVectorField σ) (φ x) +
              cov (φ.pushforwardVectorField τ) (φ x) := by
        simpa [φ.pushforwardVectorField_add] using
          (cov.isCovariantDerivativeOn.add (x := φ x) hσpush hτpush)
      ext u
      simpa [ContinuousLinearMap.comp_apply]
        using congrArg
          (fun A : TM (φ x) →L[ℝ] TM (φ x) =>
            φ.pullbackTangent x (A (φ.pushforwardTangent x u)))
          hadd
    · intro σ g x hσ hg hx
      have hσpush : MDiffAt (T% (φ.pushforwardVectorField σ)) (φ x) :=
        φ.mdifferentiableAt_pushforwardVectorField_image hσ
      have hφsymm : MDiffAt (φ.symm : M → M) (φ x) :=
        φ.symm.contMDiff.mdifferentiableAt (by simp)
      have hgcomp : MDiffAt (g ∘ (φ.symm : M → M)) (φ x) := by
        simpa [Function.comp] using
          (MDifferentiableAt.comp_of_eq
            (I := I) (I' := I) (I'' := 𝓘(ℝ, ℝ))
            (g := g) (f := (φ.symm : M → M)) (x := φ x) (y := x) hg hφsymm (by simp))
      have hleib :
          cov (φ.pushforwardVectorField (g • σ)) (φ x) =
            (g ∘ (φ.symm : M → M)) (φ x) • cov (φ.pushforwardVectorField σ) (φ x) +
              (mvfderiv (I := I) (g ∘ (φ.symm : M → M)) (φ x)).smulRight
                ((φ.pushforwardVectorField σ) (φ x)) := by
        simpa [φ.pushforwardVectorField_smul, Function.comp] using
          (cov.isCovariantDerivativeOn.leibniz
            (σ := φ.pushforwardVectorField σ) (g := g ∘ (φ.symm : M → M))
            (x := φ x) hσpush hgcomp)
      ext u
      have hleib_u :
          cov (φ.pushforwardVectorField (g • σ)) (φ x) (φ.pushforwardTangent x u) =
            ((g ∘ (φ.symm : M → M)) (φ x) • cov (φ.pushforwardVectorField σ) (φ x) +
              (mvfderiv (I := I) (g ∘ (φ.symm : M → M)) (φ x)).smulRight
                ((φ.pushforwardVectorField σ) (φ x))) (φ.pushforwardTangent x u) := by
        exact congrArg
          (fun A : TM (φ x) →L[ℝ] TM (φ x) => A (φ.pushforwardTangent x u))
          hleib
      calc
        φ.pullbackTangent x (cov (φ.pushforwardVectorField (g • σ)) (φ x) (φ.pushforwardTangent x u))
          = φ.pullbackTangent x
              (((g ∘ (φ.symm : M → M)) (φ x) • cov (φ.pushforwardVectorField σ) (φ x) +
                (mvfderiv (I := I) (g ∘ (φ.symm : M → M)) (φ x)).smulRight
                  ((φ.pushforwardVectorField σ) (φ x))) (φ.pushforwardTangent x u)) := by
                rw [hleib_u]
        _ = g x • φ.pullbackTangent x
              (cov (φ.pushforwardVectorField σ) (φ x) (φ.pushforwardTangent x u)) +
              mvfderiv (I := I) (g ∘ (φ.symm : M → M)) (φ x)
                (φ.pushforwardTangent x u) •
                φ.pullbackTangent x (φ.pushforwardVectorField σ (φ x)) := by
                  simp [ContinuousLinearMap.smulRight_apply, Function.comp]
        _ = g x • φ.pullbackTangent x
              (cov (φ.pushforwardVectorField σ) (φ x) (φ.pushforwardTangent x u)) +
              mvfderiv (I := I) g x u • σ x := by
                  rw [φ.extDerivFun_comp_symm_apply_pushforwardTangent hg u,
                    φ.pullbackTangent_pushforwardVectorField_apply_image σ x]

@[simp] lemma pullbackCovariantDerivative_apply
    (cov : CovariantDerivative I E TM)
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    φ.pullbackCovariantDerivative cov X x u =
      φ.pullbackTangent x (cov (φ.pushforwardVectorField X) (φ x) (φ.pushforwardTangent x u)) := by
  rfl

lemma pullbackCovariantDerivative_eq_of_eq_id_apply
    (cov : CovariantDerivative I E TM)
    (hφ : φ = Diffeomorph.refl I M (2 : WithTop ℕ∞))
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    φ.pullbackCovariantDerivative cov X x u = cov X x u := by
  subst hφ
  let φid : SmoothSelfDiffeomorph2 (I := I) (M := M) := Diffeomorph.refl I M (2 : WithTop ℕ∞)
  rw [SmoothSelfDiffeomorph2.pullbackCovariantDerivative_apply]
  change φid.pullbackTangent x (cov (φid.pushforwardVectorField X) (φid x)
    (φid.pushforwardTangent x u)) = cov X x u
  have hx : φid x = x := by
    simp [φid, Diffeomorph.coe_refl]
  rw [hx]
  have hpush : ∀ {y : M} (v : TM y), φid.pushforwardTangent y v = v := by
    intro y v
    rw [SmoothSelfDiffeomorph2.pushforwardTangent_apply]
    have hid :
        mfderiv I I (_root_.id : M → M) y v = v := by
      rw [mfderiv_id]
      rfl
    change (mfderiv I I (_root_.id : M → M) y) v = v
    exact hid
  have hpull : ∀ {y : M} (v : TM y), φid.pullbackTangent y v = v := by
    intro y v
    calc
      φid.pullbackTangent y v = φid.pullbackTangent y (φid.pushforwardTangent y v) := by
        rw [hpush v]
      _ = v := φid.pullbackTangent_pushforwardTangent y v
  have hX :
      φid.pushforwardVectorField X = X := by
    funext y
    rw [SmoothSelfDiffeomorph2.pushforwardVectorField_apply]
    change φid.pullbackTangent y (X y) = X y
    exact hpull (y := y) (X y)
  rw [hX]
  calc
    φid.pullbackTangent x (cov X x (φid.pushforwardTangent x u)) =
        cov X x (φid.pushforwardTangent x u) :=
      hpull (y := x) (cov X x (φid.pushforwardTangent x u))
    _ = cov X x u := by
      rw [hpush u]

lemma pullbackCovariantDerivative_eq_of_eq_id
    (cov : CovariantDerivative I E TM)
    (hφ : φ = Diffeomorph.refl I M (2 : WithTop ℕ∞)) :
    φ.pullbackCovariantDerivative cov = cov := by
  ext X x u
  exact φ.pullbackCovariantDerivative_eq_of_eq_id_apply cov hφ X x u

@[simp] theorem pullbackVectorField_pushforwardVectorField
    (X : Π x : M, TM x) :
    φ.pullbackVectorField (φ.pushforwardVectorField X) = X := by
  funext x
  simpa using φ.pullbackTangent_pushforwardVectorField_apply_image X x

@[simp] theorem pushforwardVectorField_pullbackVectorField
    (X : Π x : M, TM x) :
    φ.pushforwardVectorField (φ.pullbackVectorField X) = X := by
  have hsymm :
      ((φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M)).symm) = φ := by
    apply Diffeomorph.ext
    intro y
    rfl
  simpa [SmoothSelfDiffeomorph2.pushforwardVectorField, hsymm] using
    (SmoothSelfDiffeomorph2.pullbackVectorField_pushforwardVectorField
      (φ := (φ.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) (X := X))

lemma along_pullbackCovariantDerivative
    (cov : CovariantDerivative I E TM)
    (X Y : Π x : M, TM x) :
    (φ.pullbackCovariantDerivative cov).along X Y =
      φ.pullbackVectorField (cov.along (φ.pushforwardVectorField X) (φ.pushforwardVectorField Y)) := by
  funext x
  change ((φ.pullbackCovariantDerivative cov) Y x) (X x) =
    φ.pullbackTangent x (cov.along (φ.pushforwardVectorField X) (φ.pushforwardVectorField Y) (φ x))
  rw [φ.pullbackCovariantDerivative_apply, CovariantDerivative.along_apply]
  exact congrArg (φ.pullbackTangent x) <|
    congrArg (cov (φ.pushforwardVectorField Y) (φ x))
      (φ.pushforwardVectorField_apply_image X x).symm

lemma curvatureAux_pullbackCovariantDerivative
    (cov : CovariantDerivative I E TM)
    {X Y σ : Π x : M, TM x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (φ.pullbackCovariantDerivative cov).curvatureAux X Y σ =
      φ.pullbackVectorField
        (cov.curvatureAux
          (φ.pushforwardVectorField X)
          (φ.pushforwardVectorField Y)
          (φ.pushforwardVectorField σ)) := by
  have hXY :
      (φ.pullbackCovariantDerivative cov).along X
          ((φ.pullbackCovariantDerivative cov).along Y σ) =
        φ.pullbackVectorField
          (cov.along
            (φ.pushforwardVectorField X)
            (cov.along
              (φ.pushforwardVectorField Y)
              (φ.pushforwardVectorField σ))) := by
    rw [φ.along_pullbackCovariantDerivative]
    simp [φ.along_pullbackCovariantDerivative]
  have hYX :
      (φ.pullbackCovariantDerivative cov).along Y
          ((φ.pullbackCovariantDerivative cov).along X σ) =
        φ.pullbackVectorField
          (cov.along
            (φ.pushforwardVectorField Y)
            (cov.along
              (φ.pushforwardVectorField X)
              (φ.pushforwardVectorField σ))) := by
    rw [φ.along_pullbackCovariantDerivative]
    simp [φ.along_pullbackCovariantDerivative]
  have hbracket :
      φ.pushforwardVectorField (VectorField.mlieBracket I X Y) =
        VectorField.mlieBracket I
          (φ.pushforwardVectorField X) (φ.pushforwardVectorField Y) := by
    exact φ.pushforwardVectorField_mlieBracket_eq (X := X) (Y := Y) hX hY
  have hBracketTerm :
      (φ.pullbackCovariantDerivative cov).along (VectorField.mlieBracket I X Y) σ =
        φ.pullbackVectorField
          (cov.along
            (VectorField.mlieBracket I
              (φ.pushforwardVectorField X) (φ.pushforwardVectorField Y))
            (φ.pushforwardVectorField σ)) := by
    rw [φ.along_pullbackCovariantDerivative]
    simpa [hbracket]
  funext x
  rw [CovariantDerivative.curvatureAux_apply, hXY, hYX, hBracketTerm]
  simp [CovariantDerivative.curvatureAux, SmoothSelfDiffeomorph2.pullbackVectorField]

@[simp] lemma curvatureAux_pullbackCovariantDerivative_apply
    (cov : CovariantDerivative I E TM)
    {X Y σ : Π x : M, TM x} {x : M}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (φ.pullbackCovariantDerivative cov).curvatureAux X Y σ x =
      φ.pullbackTangent x
        (cov.curvatureAux
          (φ.pushforwardVectorField X)
          (φ.pushforwardVectorField Y)
          (φ.pushforwardVectorField σ) (φ x)) := by
  simpa [SmoothSelfDiffeomorph2.pullbackVectorField] using
    congrArg (fun s => s x) <|
      φ.curvatureAux_pullbackCovariantDerivative (cov := cov) (X := X) (Y := Y) (σ := σ) hX hY

@[simp] lemma pushforwardTangent_curvatureAux_pullbackCovariantDerivative
    (cov : CovariantDerivative I E TM)
    {X Y σ : Π x : M, TM x} {x : M}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    φ.pushforwardTangent x
      ((φ.pullbackCovariantDerivative cov).curvatureAux X Y σ x) =
        cov.curvatureAux
          (φ.pushforwardVectorField X)
          (φ.pushforwardVectorField Y)
          (φ.pushforwardVectorField σ) (φ x) := by
  rw [φ.curvatureAux_pullbackCovariantDerivative_apply (cov := cov) (X := X) (Y := Y) (σ := σ) hX hY]
  simpa using
    φ.pushforwardTangent_pullbackTangent x
      (cov.curvatureAux
        (φ.pushforwardVectorField X)
        (φ.pushforwardVectorField Y)
        (φ.pushforwardVectorField σ) (φ x))

@[simp] lemma curvatureTensor_pullbackCovariantDerivative_apply
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [CovariantDerivative.ContMDiffCovariantDerivative (φ.pullbackCovariantDerivative cov) 1]
    {x : M} (u v w : TM x) :
    (φ.pullbackCovariantDerivative cov).curvatureTensor x u v w =
      φ.pullbackTangent x
        (cov.curvatureAux
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          (φ x)) := by
  let X : Π y : M, TM y := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u
  let Y : Π y : M, TM y := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v
  let σ : Π y : M, TM y := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w
  have hX₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)) := by
    simpa [X] using
      CovariantDerivative.smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u
  have hY₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)) := by
    simpa [Y] using
      CovariantDerivative.smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v
  have hX : MDiff (T% X) := fun y ↦ by
    exact (hX₁ y).mdifferentiableAt one_ne_zero
  have hY : MDiff (T% Y) := fun y ↦ by
    exact (hY₁ y).mdifferentiableAt one_ne_zero
  rw [CovariantDerivative.curvatureTensor_apply]
  simpa [X, Y, σ] using
    (φ.curvatureAux_pullbackCovariantDerivative_apply
      (cov := cov) (X := X) (Y := Y) (σ := σ) (x := x) hX hY)

@[simp] lemma pushforwardTangent_curvatureTensor_pullbackCovariantDerivative
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [CovariantDerivative.ContMDiffCovariantDerivative (φ.pullbackCovariantDerivative cov) 1]
    {x : M} (u v w : TM x) :
    φ.pushforwardTangent x
      ((φ.pullbackCovariantDerivative cov).curvatureTensor x u v w) =
        cov.curvatureAux
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          (φ x) := by
  rw [φ.curvatureTensor_pullbackCovariantDerivative_apply (cov := cov) (u := u) (v := v) (w := w)]
  simpa using
    φ.pushforwardTangent_pullbackTangent x
      (cov.curvatureAux
        (φ.pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
        (φ.pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
        (φ.pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
        (φ x))

@[simp] lemma pushforwardTangent_ricciEndomorphism_pullbackCovariantDerivative
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [CovariantDerivative.ContMDiffCovariantDerivative (φ.pullbackCovariantDerivative cov) 1]
    {x : M} (u w v : TM x) :
    φ.pushforwardTangent x
      ((φ.pullbackCovariantDerivative cov).ricciEndomorphism x u w v) =
        cov.curvatureAux
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          (φ x) := by
  rw [CovariantDerivative.ricciEndomorphism_apply]
  simpa using
    (φ.pushforwardTangent_curvatureTensor_pullbackCovariantDerivative
      (cov := cov) (x := x) (u := v) (v := u) (w := w))

@[simp] lemma tangentMap_conj_ricciEndomorphism_pullbackCovariantDerivative_apply
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [CovariantDerivative.ContMDiffCovariantDerivative (φ.pullbackCovariantDerivative cov) 1]
    {x : M} (u w : TM x) (z : TM (φ x)) :
    (((φ.tangentMap x).toLinearEquiv).conj
      ((φ.pullbackCovariantDerivative cov).ricciEndomorphism x u w)) z =
        cov.curvatureAux
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x
              (φ.pullbackTangent x z)))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          (φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          (φ x) := by
  rw [LinearEquiv.conj_apply]
  change φ.pushforwardTangent x
      (((φ.pullbackCovariantDerivative cov).ricciEndomorphism x u w) (φ.pullbackTangent x z)) = _
  simpa using
    (φ.pushforwardTangent_ricciEndomorphism_pullbackCovariantDerivative
      (cov := cov) (x := x) (u := u) (w := w) (v := φ.pullbackTangent x z))

lemma ricciCurvature_pullbackCovariantDerivative_eq_trace_tangentMap_conj_ricciEndomorphism
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [CovariantDerivative.ContMDiffCovariantDerivative (φ.pullbackCovariantDerivative cov) 1]
    {x : M} (u w : TM x) :
    (φ.pullbackCovariantDerivative cov).ricciCurvature x u w =
      LinearMap.trace ℝ (TM (φ x))
        (((φ.tangentMap x).toLinearEquiv).conj
          ((φ.pullbackCovariantDerivative cov).ricciEndomorphism x u w)) := by
  rw [CovariantDerivative.ricciCurvature_apply]
  simpa using
    (LinearMap.trace_conj'
      (R := ℝ)
      (f := (φ.pullbackCovariantDerivative cov).ricciEndomorphism x u w)
      (e := (φ.tangentMap x).toLinearEquiv)).symm

lemma torsion_pullbackCovariantDerivative
    (cov : CovariantDerivative I E TM)
    {X Y : Π x : M, TM x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    (φ.pullbackCovariantDerivative cov).torsion x (X x) (Y x) =
      φ.pullbackTangent x (cov.torsion (φ x)
        (φ.pushforwardTangent x (X x)) (φ.pushforwardTangent x (Y x))) := by
  have hXpush : MDiffAt (T% (φ.pushforwardVectorField X)) (φ x) :=
    φ.mdifferentiableAt_pushforwardVectorField_image hX
  have hYpush : MDiffAt (T% (φ.pushforwardVectorField Y)) (φ x) :=
    φ.mdifferentiableAt_pushforwardVectorField_image hY
  have hbracket :
      VectorField.mlieBracket I X Y x =
        φ.pullbackTangent x
          (VectorField.mlieBracket I (φ.pushforwardVectorField X) (φ.pushforwardVectorField Y) (φ x)) := by
    simpa using
      (φ.pullbackVectorField_mlieBracket (X := φ.pushforwardVectorField X)
        (Y := φ.pushforwardVectorField Y) (x := x) hXpush hYpush).symm
  have htor :
      cov.torsion (φ x) (φ.pushforwardTangent x (X x)) (φ.pushforwardTangent x (Y x)) =
        cov (φ.pushforwardVectorField Y) (φ x) (φ.pushforwardTangent x (X x)) -
          cov (φ.pushforwardVectorField X) (φ x) (φ.pushforwardTangent x (Y x)) -
            VectorField.mlieBracket I (φ.pushforwardVectorField X) (φ.pushforwardVectorField Y) (φ x) := by
    have htor0 := cov.torsion_apply (x := φ x) hXpush hYpush
    rw [φ.pushforwardVectorField_apply_image X x, φ.pushforwardVectorField_apply_image Y x] at htor0
    exact htor0
  rw [(φ.pullbackCovariantDerivative cov).torsion_apply (x := x) hX hY, htor]
  simp [φ.pullbackCovariantDerivative_apply, hbracket]

lemma difference_pullbackCovariantDerivative
    (cov cov' : CovariantDerivative I E TM)
    {X : Π x : M, TM x} {x : M}
    (hX : MDiffAt (T% X) x) :
    CovariantDerivative.difference (φ.pullbackCovariantDerivative cov)
      (φ.pullbackCovariantDerivative cov') x (X x) =
        (φ.pullbackTangent x).comp
          (((CovariantDerivative.difference cov cov') (φ x)
            (φ.pushforwardVectorField X (φ x))).comp (φ.pushforwardTangent x)) := by
  have hXpush : MDiffAt (T% (φ.pushforwardVectorField X)) (φ x) :=
    φ.mdifferentiableAt_pushforwardVectorField_image hX
  have hdiff_pull :
      CovariantDerivative.difference (φ.pullbackCovariantDerivative cov)
        (φ.pullbackCovariantDerivative cov') x (X x) =
          (φ.pullbackCovariantDerivative cov X x : TM x →L[ℝ] TM x) -
            (φ.pullbackCovariantDerivative cov' X x : TM x →L[ℝ] TM x) := by
    simpa [CovariantDerivative.difference] using
      (IsCovariantDerivativeOn.difference_apply
        (hcov := CovariantDerivative.isCovariantDerivativeOn (φ.pullbackCovariantDerivative cov))
        (hcov' := CovariantDerivative.isCovariantDerivativeOn (φ.pullbackCovariantDerivative cov'))
        (x := x) (s := Set.univ) (hx := by trivial) (σ := X) (hσ := hX))
  have hdiff :
      CovariantDerivative.difference cov cov' (φ x) (φ.pushforwardVectorField X (φ x)) =
        (cov (φ.pushforwardVectorField X) (φ x) : TM (φ x) →L[ℝ] TM (φ x)) -
          (cov' (φ.pushforwardVectorField X) (φ x) : TM (φ x) →L[ℝ] TM (φ x)) := by
    simpa [CovariantDerivative.difference] using
      (IsCovariantDerivativeOn.difference_apply
        (hcov := CovariantDerivative.isCovariantDerivativeOn cov)
        (hcov' := CovariantDerivative.isCovariantDerivativeOn cov')
        (x := φ x) (s := Set.univ) (hx := by trivial) (σ := φ.pushforwardVectorField X)
        (hσ := hXpush))
  ext u
  rw [hdiff_pull, hdiff]
  calc
    (((φ.pullbackCovariantDerivative cov X x : TM x →L[ℝ] TM x) -
          (φ.pullbackCovariantDerivative cov' X x : TM x →L[ℝ] TM x)) u)
        = φ.pullbackTangent x
            (cov (φ.pushforwardVectorField X) (φ x) (φ.pushforwardTangent x u)) -
          φ.pullbackTangent x
            (cov' (φ.pushforwardVectorField X) (φ x) (φ.pushforwardTangent x u)) := by
              simp [φ.pullbackCovariantDerivative_apply]
    _ = φ.pullbackTangent x
          (((cov (φ.pushforwardVectorField X) (φ x) : TM (φ x) →L[ℝ] TM (φ x)) -
              (cov' (φ.pushforwardVectorField X) (φ x) : TM (φ x) →L[ℝ] TM (φ x)))
            (φ.pushforwardTangent x u)) := by
          simp
    _ = ((φ.pullbackTangent x).comp
          (((cov (φ.pushforwardVectorField X) (φ x) : TM (φ x) →L[ℝ] TM (φ x)) -
              (cov' (φ.pushforwardVectorField X) (φ x) : TM (φ x) →L[ℝ] TM (φ x))).comp
            (φ.pushforwardTangent x))) u := by
          rfl

@[simp] lemma difference_pullbackCovariantDerivative_apply
    (cov cov' : CovariantDerivative I E TM)
    {X : Π x : M, TM x} {x : M} (hX : MDiffAt (T% X) x) (u : TM x) :
    CovariantDerivative.difference (φ.pullbackCovariantDerivative cov)
      (φ.pullbackCovariantDerivative cov') x (X x) u =
        φ.pullbackTangent x
          ((CovariantDerivative.difference cov cov') (φ x)
            (φ.pushforwardVectorField X (φ x)) (φ.pushforwardTangent x u)) := by
  rw [φ.difference_pullbackCovariantDerivative (cov := cov) (cov' := cov') hX]
  rfl

lemma isMetricCompatibleTangent_pullbackCovariantDerivative_c1
    {g g' : Bundle.ContMDiffRiemannianMetric I 1 E TM}
    (hinner : ∀ x : M, ∀ u v : TM x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent) :
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsMetricCompatibleTangent := by
  letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩
  intro x σ τ hσ hτ u
  change
    mvfderiv (I := I) (fun y ↦ g'.inner y (σ y) (τ y)) x u =
      g'.inner x ((φ.pullbackCovariantDerivative cov) σ x u) (τ x) +
        g'.inner x (σ x) ((φ.pullbackCovariantDerivative cov) τ x u)
  set σp : Π y : M, TM y := φ.pushforwardVectorField σ with hσpdef
  set τp : Π y : M, TM y := φ.pushforwardVectorField τ with hτpdef
  let f : M → ℝ := fun y ↦ g.inner y (σp y) (τp y)
  have hσpush : MDiffAt (T% σp) (φ x) := by
    simpa [σp] using φ.mdifferentiableAt_pushforwardVectorField_image (X := σ) (x := x) hσ
  have hτpush : MDiffAt (T% τp) (φ x) := by
    simpa [τp] using φ.mdifferentiableAt_pushforwardVectorField_image (X := τ) (x := x) hτ
  have hf : MDiffAt f (φ x) := by
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    change MDiffAt (fun y ↦ inner ℝ (σp y) (τp y)) (φ x)
    exact CovariantDerivative.mdiffAt_inner_sections
      (I := I) (E := E) (M := M) (x := φ x) (σ := σp) (τ := τp) hσpush hτpush
  have hcompat :
      mvfderiv (I := I) f (φ x) (φ.pushforwardTangent x u) =
        g.inner (φ x) (cov σp (φ x) (φ.pushforwardTangent x u)) (τp (φ x)) +
          g.inner (φ x) (σp (φ x)) (cov τp (φ x) (φ.pushforwardTangent x u)) := by
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    change mvfderiv (I := I) (fun y ↦ inner ℝ (σp y) (τp y)) (φ x)
        (φ.pushforwardTangent x u) =
      inner ℝ (cov σp (φ x) (φ.pushforwardTangent x u)) (τp (φ x)) +
        inner ℝ (σp (φ x)) (cov τp (φ x) (φ.pushforwardTangent x u))
    exact hcov (σ := σp) (τ := τp) hσpush hτpush (φ.pushforwardTangent x u)
  have hfun : (fun y ↦ g'.inner y (σ y) (τ y)) = f ∘ (φ : M → M) := by
    funext y
    rw [hinner y]
    rw [← φ.pushforwardVectorField_apply_image σ y, ← φ.pushforwardVectorField_apply_image τ y]
    rfl
  have hσimage : φ.pushforwardTangent x (σ x) = σp (φ x) := by
    simpa [σp] using (φ.pushforwardVectorField_apply_image σ x).symm
  have hτimage : φ.pushforwardTangent x (τ x) = τp (φ x) := by
    simpa [τp] using (φ.pushforwardVectorField_apply_image τ x).symm
  have htransportσ :
      φ.pushforwardTangent x ((φ.pullbackCovariantDerivative cov) σ x u) =
        cov σp (φ x) (φ.pushforwardTangent x u) := by
    rw [φ.pullbackCovariantDerivative_apply]
    simpa [σp, φ.pushforwardTangent_apply] using
      (φ.pushforwardTangent_pullbackTangent x
        (cov σp (φ x) (φ.pushforwardTangent x u)))
  have htransportτ :
      φ.pushforwardTangent x ((φ.pullbackCovariantDerivative cov) τ x u) =
        cov τp (φ x) (φ.pushforwardTangent x u) := by
    rw [φ.pullbackCovariantDerivative_apply]
    simpa [τp, φ.pushforwardTangent_apply] using
      (φ.pushforwardTangent_pullbackTangent x
        (cov τp (φ x) (φ.pushforwardTangent x u)))
  calc
    mvfderiv (I := I) (fun y ↦ g'.inner y (σ y) (τ y)) x u
      = mvfderiv (I := I) (f ∘ (φ : M → M)) x u := by rw [hfun]
    _ = mvfderiv (I := I) f (φ x) (φ.pushforwardTangent x u) := by
          exact φ.extDerivFun_comp_apply_pushforwardTangent (hg := hf) u
    _ = g.inner (φ x) (cov σp (φ x) (φ.pushforwardTangent x u)) (τp (φ x)) +
          g.inner (φ x) (σp (φ x)) (cov τp (φ x) (φ.pushforwardTangent x u)) := hcompat
    _ = g'.inner x ((φ.pullbackCovariantDerivative cov) σ x u) (τ x) +
          g'.inner x (σ x) ((φ.pullbackCovariantDerivative cov) τ x u) := by
          rw [hinner x ((φ.pullbackCovariantDerivative cov) σ x u) (τ x),
            hinner x (σ x) ((φ.pullbackCovariantDerivative cov) τ x u)]
          rw [htransportσ, htransportτ, hσimage, hτimage]

lemma isMetricCompatibleTangent_pullbackCovariantDerivative
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E TM}
    (hinner : ∀ x : M, ∀ u v : TM x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent) :
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsMetricCompatibleTangent := by
  let g1 : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    { g with contMDiff := g.contMDiff.of_le (by norm_num) }
  let g1' : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    { g' with contMDiff := g'.contMDiff.of_le (by norm_num) }
  have hcov1 : letI : Bundle.RiemannianBundle TM := ⟨g1.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent := by
    change letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent
    exact hcov
  have hinner1 : ∀ x : M, ∀ u v : TM x,
      g1'.inner x u v =
        g1.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := hinner
  change letI : Bundle.RiemannianBundle TM := ⟨g1'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsMetricCompatibleTangent
  intro x σ τ hσ hτ u
  simpa [CovariantDerivative.IsMetricCompatibleTangent] using
    φ.isMetricCompatibleTangent_pullbackCovariantDerivative_c1
      (g := g1) (g' := g1') (hinner := hinner1) (cov := cov) (hcov := hcov1) hσ hτ u

lemma isMetricCompatibleTangent_pullbackCovariantDerivative_pullbackRiemannianMetric
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent) :
    letI : Bundle.RiemannianBundle TM := ⟨(φ.pullbackRiemannianMetric g).toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsMetricCompatibleTangent := by
  let g1 : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    { g with contMDiff := g.contMDiff.of_le (by norm_num) }
  have hcov1 : letI : Bundle.RiemannianBundle TM := ⟨g1.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent := by
    change letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent
    exact hcov
  have hinner :
      ∀ x : M, ∀ u v : TM x,
        (φ.pullbackRiemannianMetric g).inner x u v =
          g1.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
    intro x u v
    rw [φ.pullbackRiemannianMetric_inner]
  intro x σ τ hσ hτ u
  simpa [CovariantDerivative.IsMetricCompatibleTangent] using
    φ.isMetricCompatibleTangent_pullbackCovariantDerivative_c1
      (g := g1) (g' := φ.pullbackRiemannianMetric g) (hinner := hinner) (cov := cov)
      (hcov := hcov1) hσ hτ u

lemma isTorsionFree_pullbackCovariantDerivative
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM)
    (hcov : cov.IsTorsionFree) :
    (φ.pullbackCovariantDerivative cov).IsTorsionFree := by
  unfold CovariantDerivative.IsTorsionFree at hcov ⊢
  ext x u v
  have htransport :=
    φ.torsion_pullbackCovariantDerivative (cov := cov) (x := x)
      (X := FiberBundle.extend E u) (Y := FiberBundle.extend E v)
      (FiberBundle.mdifferentiableAt_extend (I := I) (F := E) u)
      (FiberBundle.mdifferentiableAt_extend (I := I) (F := E) v)
  have htransport' :
      ((φ.pullbackCovariantDerivative cov).torsion x u) v =
        φ.pullbackTangent x
          (((cov.torsion (φ x)) (φ.pushforwardTangent x u)) (φ.pushforwardTangent x v)) := by
    simpa using htransport
  have hzero := congrArg
    (fun T : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x =>
      T (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)) hcov
  have hzero' :
      φ.pullbackTangent x
        (((cov.torsion (φ x)) (φ.pushforwardTangent x u)) (φ.pushforwardTangent x v)) = 0 := by
    simpa using congrArg (φ.pullbackTangent x) hzero
  exact htransport'.trans hzero'
lemma isLeviCivita_pullbackCovariantDerivative_c1
    {g g' : Bundle.ContMDiffRiemannianMetric I 1 E TM}
    (hinner : ∀ x : M, ∀ u v : TM x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsLeviCivita) :
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsLeviCivita := by
  have htorsion : cov.torsion = 0 := by
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    exact hcov.1
  have hcompat :
      letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent := by
    exact hcov.2
  letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  constructor
  · exact φ.isTorsionFree_pullbackCovariantDerivative (cov := cov)
      (by simpa [CovariantDerivative.IsTorsionFree] using htorsion)
  · exact φ.isMetricCompatibleTangent_pullbackCovariantDerivative_c1
      (g := g) (g' := g') (hinner := hinner) (cov := cov) (hcov := hcompat)
lemma isLeviCivita_pullbackCovariantDerivative
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E TM}
    (hinner : ∀ x : M, ∀ u v : TM x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsLeviCivita) :
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsLeviCivita := by
  let g1 : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    { g with contMDiff := g.contMDiff.of_le (by norm_num) }
  let g1' : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    { g' with contMDiff := g'.contMDiff.of_le (by norm_num) }
  have hcov1 :
      letI : Bundle.RiemannianBundle TM := ⟨g1.toRiemannianMetric⟩;
      cov.IsLeviCivita := by
    change letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsLeviCivita
    exact hcov
  have hinner1 : ∀ x : M, ∀ u v : TM x,
      g1'.inner x u v =
        g1.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := hinner
  change letI : Bundle.RiemannianBundle TM := ⟨g1'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsLeviCivita
  exact φ.isLeviCivita_pullbackCovariantDerivative_c1
    (g := g1) (g' := g1') (hinner := hinner1) (cov := cov) (hcov := hcov1)
lemma isLeviCivita_pullbackCovariantDerivative_pullbackRiemannianMetric
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsLeviCivita) :
    letI : Bundle.RiemannianBundle TM := ⟨(φ.pullbackRiemannianMetric g).toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsLeviCivita := by
  let g1 : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    { g with contMDiff := g.contMDiff.of_le (by norm_num) }
  have hcov1 :
      letI : Bundle.RiemannianBundle TM := ⟨g1.toRiemannianMetric⟩;
      cov.IsLeviCivita := by
    change letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsLeviCivita
    exact hcov
  have hinner : ∀ x : M, ∀ u v : TM x,
      (φ.pullbackRiemannianMetric g).inner x u v =
        g1.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
    intro x u v
    rw [φ.pullbackRiemannianMetric_inner]
  exact φ.isLeviCivita_pullbackCovariantDerivative_c1
    (g := g1) (g' := φ.pullbackRiemannianMetric g) hinner (cov := cov) hcov1

end SmoothSelfDiffeomorph2

/-- A bundled `C^3` self-diffeomorphism of the manifold. This is the natural regularity level for
pulling back a `C^2` metric while retaining a `C^2` metric family. -/
abbrev SmoothSelfDiffeomorph3 := M ≃ₘ^3⟮I, I⟯ M

namespace SmoothSelfDiffeomorph3

/-- Bundle mutually inverse `C^3` self-maps as a `C^3` self-diffeomorphism. -/
noncomputable def ofInverse
    (f g : M → M)
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f)
    (hf : ContMDiff I I 3 f) (hg : ContMDiff I I 3 g) :
    SmoothSelfDiffeomorph3 (I := I) (M := M) where
  toEquiv :=
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright }
  contMDiff_toFun := hf
  contMDiff_invFun := hg

@[simp] theorem ofInverse_apply
    (f g : M → M)
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f)
    (hf : ContMDiff I I 3 f) (hg : ContMDiff I I 3 g)
    (x : M) :
    ofInverse (I := I) (M := M) f g hleft hright hf hg x = f x := rfl

@[simp] theorem ofInverse_symm_apply
    (f g : M → M)
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f)
    (hf : ContMDiff I I 3 f) (hg : ContMDiff I I 3 g)
    (x : M) :
    (ofInverse (I := I) (M := M) f g hleft hright hf hg).symm x = g x := rfl

variable (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))

local notation "TStar" => (fun x : M ↦ TM x →L[ℝ] ℝ)
local notation "BilF" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "EndF" => (E →L[ℝ] E)
local notation "OneF" => (E →L[ℝ] ℝ)

/-- Forget one derivative and regard a `C^3` self-diffeomorphism as a `C^2` one. -/
def toSmoothSelfDiffeomorph2 : SmoothSelfDiffeomorph2 (I := I) (M := M) :=
  { toEquiv := φ.toEquiv
    contMDiff_toFun := φ.contMDiff.of_le (by norm_num)
    contMDiff_invFun := φ.symm.contMDiff.of_le (by norm_num) }

@[simp] lemma toSmoothSelfDiffeomorph2_apply (x : M) :
    φ.toSmoothSelfDiffeomorph2 x = φ x := rfl

@[simp] lemma toSmoothSelfDiffeomorph2_symm_apply (x : M) :
    φ.toSmoothSelfDiffeomorph2.symm x = φ.symm x := rfl

lemma toSmoothSelfDiffeomorph2_of_symm_eq_symm :
    SmoothSelfDiffeomorph3.toSmoothSelfDiffeomorph2
        (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M))) =
      φ.toSmoothSelfDiffeomorph2.symm := by
  apply Diffeomorph.ext
  intro x
  rfl

/-- The tangent map of a bundled `C^3` self-diffeomorphism. -/
noncomputable abbrev tangentMap (x : M) : TM x ≃L[ℝ] TM (φ x) :=
  (φ.toSmoothSelfDiffeomorph2).tangentMap x

/-- Forward tangent transport along a bundled `C^3` self-diffeomorphism. -/
abbrev pushforwardTangent (x : M) : TM x →L[ℝ] TM (φ x) :=
  φ.tangentMap x

/-- Backward tangent transport along a bundled `C^3` self-diffeomorphism. -/
abbrev pullbackTangent (x : M) : TM (φ x) →L[ℝ] TM x :=
  (φ.tangentMap x).symm

@[simp] lemma pullbackTangent_pushforwardTangent (x : M) (u : TM x) :
    φ.pullbackTangent x (φ.pushforwardTangent x u) = u := by
  exact (φ.tangentMap x).symm_apply_apply u

@[simp] lemma pushforwardTangent_pullbackTangent (x : M) (u : TM (φ x)) :
    φ.pushforwardTangent x (φ.pullbackTangent x u) = u := by
  exact (φ.tangentMap x).apply_symm_apply u

lemma pushforwardTangent_eq_mfderiv (x : M) :
    φ.pushforwardTangent x = mfderiv I I (φ : M → M) x := by
  change φ.toSmoothSelfDiffeomorph2.pushforwardTangent x =
    mfderiv I I (φ : M → M) x
  have h := SmoothSelfDiffeomorph2.pushforwardTangent_eq_mfderiv
    (φ := φ.toSmoothSelfDiffeomorph2) x
  rw [show (φ.toSmoothSelfDiffeomorph2 : M → M) = (φ : M → M) by rfl] at h
  exact h

@[simp] lemma pushforwardTangent_apply (x : M) (u : TM x) :
    φ.pushforwardTangent x u = (mfderiv I I (φ : M → M) x) u := by
  simpa using congrArg (fun f : TM x →L[ℝ] TM (φ x) => f u)
    (φ.pushforwardTangent_eq_mfderiv x)

@[simp] lemma toSmoothSelfDiffeomorph2_pushforwardTangent_apply
    (x : M) (u : TM x) :
    φ.toSmoothSelfDiffeomorph2.pushforwardTangent x u =
      φ.pushforwardTangent x u := by
  rw [SmoothSelfDiffeomorph2.pushforwardTangent_apply,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply]
  change (mfderiv I I (φ : M → M) x) u = (mfderiv I I (φ : M → M) x) u
  rfl
@[simp] lemma symm_pushforwardTangent_pushforwardTangent (x : M) (u : TM x) :
    SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
        (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x)
        (φ.pushforwardTangent x u) = u := by
  have hfun : (φ.toSmoothSelfDiffeomorph2 : M → M) = (φ : M → M) := by rfl
  have hinvfun :
      (φ.toSmoothSelfDiffeomorph2.symm : M → M) = (φ.symm : M → M) := by rfl
  have h := SmoothSelfDiffeomorph2.mfderiv_symm_apply_pushforwardTangent
    (I := I) (M := M) (φ := φ.toSmoothSelfDiffeomorph2) x u
  rw [SmoothSelfDiffeomorph2.pushforwardTangent_eq_mfderiv] at h
  rw [show φ.toSmoothSelfDiffeomorph2 x = φ x by rfl] at h
  rw [mfderiv_congr (I := I) (I' := I)
    (f := (φ.toSmoothSelfDiffeomorph2 : M → M)) (f' := (φ : M → M))
    (x := x) hfun] at h
  rw [mfderiv_congr (I := I) (I' := I)
    (f := (φ.toSmoothSelfDiffeomorph2.symm : M → M)) (f' := (φ.symm : M → M))
    (x := φ x) hinvfun] at h
  rw [SmoothSelfDiffeomorph3.pushforwardTangent_apply,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply]
  convert h using 1 <;> rfl
@[simp] lemma pushforwardTangent_symm_pushforwardTangent (x : M) (u : TM (φ x)) :
    φ.pushforwardTangent x
        (SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x) u) =
      u := by
  have hfun : (φ.toSmoothSelfDiffeomorph2 : M → M) = (φ : M → M) := by rfl
  have hinvfun :
      (φ.toSmoothSelfDiffeomorph2.symm : M → M) = (φ.symm : M → M) := by rfl
  have h := SmoothSelfDiffeomorph2.pushforwardTangent_mfderiv_symm_apply
    (I := I) (M := M) (φ := φ.toSmoothSelfDiffeomorph2) x u
  rw [SmoothSelfDiffeomorph2.pushforwardTangent_eq_mfderiv] at h
  rw [show φ.toSmoothSelfDiffeomorph2 x = φ x by rfl] at h
  rw [mfderiv_congr (I := I) (I' := I)
    (f := (φ.toSmoothSelfDiffeomorph2 : M → M)) (f' := (φ : M → M))
    (x := x) hfun] at h
  rw [mfderiv_congr (I := I) (I' := I)
    (f := (φ.toSmoothSelfDiffeomorph2.symm : M → M)) (f' := (φ.symm : M → M))
    (x := φ x) hinvfun] at h
  rw [SmoothSelfDiffeomorph3.pushforwardTangent_apply]
  change φ.pushforwardTangent x ((tangentSpaceCast I (φ.symm (φ x)) x)
    ((mfderiv I I (φ.symm : M → M) (φ x)) u)) = u
  rw [SmoothSelfDiffeomorph3.pushforwardTangent_apply]
  convert h using 1 <;> rfl

@[simp] lemma toSmoothSelfDiffeomorph2_pushforwardTangent
    (x : M) :
    φ.toSmoothSelfDiffeomorph2.pushforwardTangent x =
      φ.pushforwardTangent x := by
  ext u
  exact φ.toSmoothSelfDiffeomorph2_pushforwardTangent_apply x u

@[simp] lemma toSmoothSelfDiffeomorph2_pullbackTangent_apply
    (x : M) (u : TM (φ x)) :
    φ.toSmoothSelfDiffeomorph2.pullbackTangent x u =
      φ.pullbackTangent x u := by
  rfl

@[simp] lemma toSmoothSelfDiffeomorph2_pullbackTangent
    (x : M) :
    φ.toSmoothSelfDiffeomorph2.pullbackTangent x =
      φ.pullbackTangent x := by
  rfl

/-- Pull back a tangent-vector field along a bundled `C^3` self-diffeomorphism. -/
def pullbackVectorField
    (X : Π x : M, TM x) : Π x : M, TM x :=
  φ.toSmoothSelfDiffeomorph2.pullbackVectorField X

/-- Push forward a tangent-vector field along a bundled `C^3` self-diffeomorphism. -/
def pushforwardVectorField
    (X : Π x : M, TM x) : Π x : M, TM x :=
  φ.toSmoothSelfDiffeomorph2.pushforwardVectorField X

@[simp] lemma pullbackVectorField_apply
    (X : Π x : M, TM x) (x : M) :
    φ.pullbackVectorField X x = φ.pullbackTangent x (X (φ x)) := by
  rfl

theorem pullbackVectorField_eq_mpullback
    (X : Π x : M, TM x) :
    φ.pullbackVectorField X = VectorField.mpullback I I (φ : M → M) X := by
  rw [SmoothSelfDiffeomorph3.pullbackVectorField]
  exact SmoothSelfDiffeomorph2.pullbackVectorField_eq_mpullback
    (φ := φ.toSmoothSelfDiffeomorph2) X

theorem pushforwardVectorField_eq_mpullback
    (X : Π x : M, TM x) :
    φ.pushforwardVectorField X = VectorField.mpullback I I (φ.symm : M → M) X := by
  rw [SmoothSelfDiffeomorph3.pushforwardVectorField]
  exact SmoothSelfDiffeomorph2.pushforwardVectorField_eq_mpullback
    (φ := φ.toSmoothSelfDiffeomorph2) X

theorem contMDiff_two_pullbackVectorField
    {X : Π x : M, TM x}
    (hX : ContMDiff I I.tangent 2 (T% X)) :
    ContMDiff I I.tangent 2 (T% (φ.pullbackVectorField X)) := by
  rw [φ.pullbackVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ : M → M)) φ.contMDiff
    (fun x => φ.toSmoothSelfDiffeomorph2.mfderiv_isInvertible x) (by norm_num)

theorem contMDiff_two_pushforwardVectorField
    {X : Π x : M, TM x}
    (hX : ContMDiff I I.tangent 2 (T% X)) :
    ContMDiff I I.tangent 2 (T% (φ.pushforwardVectorField X)) := by
  rw [φ.pushforwardVectorField_eq_mpullback X]
  exact hX.mpullback_vectorField
    (I := I) (I' := I) (f := (φ.symm : M → M)) φ.symm.contMDiff
    (fun x =>
      SmoothSelfDiffeomorph2.mfderiv_isInvertible
        (φ := (φ.toSmoothSelfDiffeomorph2.symm : SmoothSelfDiffeomorph2 (I := I) (M := M))) x)
    (by norm_num)

theorem contMDiff_two_pullback_smoothExtend (x : M) (u : TM x) :
    ContMDiff I I.tangent 2
      (T% (φ.pullbackVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) (φ x)
          (φ.pushforwardTangent x u)))) :=
  φ.contMDiff_two_pullbackVectorField
    (CovariantDerivative.smoothExtend_contMDiff_two (I := I) (F := E) (V := TM)
      (φ x) (φ.pushforwardTangent x u))

theorem contMDiff_two_pushforward_smoothExtend (x : M) (u : TM x) :
    ContMDiff I I.tangent 2
      (T% (φ.pushforwardVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))) :=
  φ.contMDiff_two_pushforwardVectorField
    (CovariantDerivative.smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u)

theorem contMDiff_two_localFrameCoeff_pushforward_smoothExtend_of_tsupport_subset
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {x : M} (u : TM x)
    (hsupp : ∀ ⦃z : M⦄,
      z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
        φ z ∈ (trivializationAt E TM (φ x)).baseSet)
    (i : ι) :
    ContMDiff I 𝓘(ℝ) 2
      (fun y ↦
        (trivializationAt E TM (φ x)).localFrameCoeff I b i y
          ((φ.pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)) y)) := by
  letI := b.finiteDimensional_of_finite
  let e := trivializationAt E TM (φ x)
  let ψ : SmoothBumpFunction I x :=
    CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x
  let Z : Π y : M, TM y :=
    φ.pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
  let outsideSupport : Set M := (φ.symm : M → M) ⁻¹' (tsupport ψ)ᶜ
  have hZ₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)) := by
    simpa [Z] using φ.contMDiff_two_pushforward_smoothExtend x u
  have hbase :
      ContMDiffOn I 𝓘(ℝ) 2
        (fun y ↦ e.localFrameCoeff I b i y (Z y)) e.baseSet := by
    exact
      contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
        (t := e.baseSet) (k := (2 : WithTop ℕ∞))
        e.open_baseSet (subset_refl _) hZ₂.contMDiffOn i
  have houtside :
      ContMDiffOn I 𝓘(ℝ) 2
        (fun y ↦ e.localFrameCoeff I b i y (Z y)) outsideSupport := by
    have hzero : ContMDiffOn I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) outsideSupport :=
      contMDiff_const.contMDiffOn
    refine hzero.congr ?_
    intro y hy
    have hψy : (ψ : M → ℝ) (φ.symm y) = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [Z, SmoothSelfDiffeomorph3.pushforwardVectorField,
      SmoothSelfDiffeomorph2.pushforwardVectorField, CovariantDerivative.smoothExtend, ψ, hψy]
    have hlinzero :
        (SmoothSelfDiffeomorph2.pullbackTangent
          (Diffeomorph.symm φ.toSmoothSelfDiffeomorph2) y)
            (0 : TangentSpace I ((Diffeomorph.symm φ) y)) = 0 := by
      exact ContinuousLinearMap.map_zero _
    exact (congrArg (fun v ↦ e.localFrameCoeff I b i y v) hlinzero).trans
      ((e.localFrameCoeff I b i y).map_zero)
  have hcover : e.baseSet ∪ outsideSupport = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    by_cases hybase : y ∈ e.baseSet
    · exact Or.inl hybase
    · refine Or.inr ?_
      intro hysupp
      have himage : φ (φ.symm y) ∈ e.baseSet := hsupp hysupp
      exact hybase (by simpa [e] using himage)
  have hopenOutside : IsOpen outsideSupport := by
    exact (isOpen_compl_iff.mpr (isClosed_tsupport ψ)).preimage φ.symm.continuous
  have hglobal :=
    contMDiff_of_contMDiffOn_union_of_isOpen hbase houtside hcover e.open_baseSet hopenOutside
  simpa [e, Z] using hglobal

theorem contMDiff_two_localFrameCoeff_pushforward_smoothExtendWithBump_of_tsupport_subset
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {x : M} (η : SmoothBumpFunction I x) (u : TM x)
    (hηsource :
      tsupport η ⊆ (trivializationAt E TM x).baseSet)
    (hηtarget : ∀ ⦃z : M⦄, z ∈ tsupport η →
        φ z ∈ (trivializationAt E TM (φ x)).baseSet)
    (i : ι) :
    ContMDiff I 𝓘(ℝ) 2
      (fun y ↦
        (trivializationAt E TM (φ x)).localFrameCoeff I b i y
          ((φ.pushforwardVectorField
            (CovariantDerivative.smoothExtendWithBump
              (I := I) (F := E) (V := TM) x η u)) y)) := by
  letI := b.finiteDimensional_of_finite
  let e := trivializationAt E TM (φ x)
  let Z : Π y : M, TM y :=
    φ.pushforwardVectorField
      (CovariantDerivative.smoothExtendWithBump (I := I) (F := E) (V := TM) x η u)
  let outsideSupport : Set M := (φ.symm : M → M) ⁻¹' (tsupport η)ᶜ
  have hZ₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)) := by
    have hηsmooth :
        ContMDiff I (I.prod 𝓘(ℝ, E)) 2
          (fun y ↦ TotalSpace.mk' E y
            (CovariantDerivative.smoothExtendWithBump (I := I) (F := E) (V := TM) x η u y)) :=
      CovariantDerivative.smoothExtendWithBump_contMDiff_two_of_tsupport_subset
        (I := I) (F := E) (V := TM) x η u hηsource
    simpa [Z] using φ.contMDiff_two_pushforwardVectorField hηsmooth
  have hbase :
      ContMDiffOn I 𝓘(ℝ) 2
        (fun y ↦ e.localFrameCoeff I b i y (Z y)) e.baseSet := by
    exact
      contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
        (t := e.baseSet) (k := (2 : WithTop ℕ∞))
        e.open_baseSet (subset_refl _) hZ₂.contMDiffOn i
  have houtside :
      ContMDiffOn I 𝓘(ℝ) 2
        (fun y ↦ e.localFrameCoeff I b i y (Z y)) outsideSupport := by
    have hzero : ContMDiffOn I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) outsideSupport :=
      contMDiff_const.contMDiffOn
    refine hzero.congr ?_
    intro y hy
    have hηy : (η : M → ℝ) (φ.symm y) = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [Z, SmoothSelfDiffeomorph3.pushforwardVectorField,
      SmoothSelfDiffeomorph2.pushforwardVectorField,
      CovariantDerivative.smoothExtendWithBump, hηy]
    have hlinzero :
        (SmoothSelfDiffeomorph2.pullbackTangent
          (Diffeomorph.symm φ.toSmoothSelfDiffeomorph2) y)
            (0 : TangentSpace I ((Diffeomorph.symm φ) y)) = 0 := by
      exact ContinuousLinearMap.map_zero _
    exact (congrArg (fun v ↦ e.localFrameCoeff I b i y v) hlinzero).trans
      ((e.localFrameCoeff I b i y).map_zero)
  have hcover : e.baseSet ∪ outsideSupport = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    by_cases hybase : y ∈ e.baseSet
    · exact Or.inl hybase
    · refine Or.inr ?_
      intro hysupp
      have himage : φ (φ.symm y) ∈ e.baseSet := hηtarget hysupp
      exact hybase (by simpa [e] using himage)
  have hopenOutside : IsOpen outsideSupport := by
    exact (isOpen_compl_iff.mpr (isClosed_tsupport η)).preimage φ.symm.continuous
  have hglobal :=
    contMDiff_of_contMDiffOn_union_of_isOpen hbase houtside hcover e.open_baseSet hopenOutside
  simpa [e, Z] using hglobal

@[simp] lemma pushforwardVectorField_apply_image
    (X : Π x : M, TM x) (x : M) :
    φ.pushforwardVectorField X (φ x) = φ.pushforwardTangent x (X x) := by
  change φ.toSmoothSelfDiffeomorph2.pushforwardVectorField X (φ x) =
    φ.pushforwardTangent x (X x)
  rw [← SmoothSelfDiffeomorph3.toSmoothSelfDiffeomorph2_pushforwardTangent_apply
    (φ := φ) (x := x) (u := X x)]
  exact SmoothSelfDiffeomorph2.pushforwardVectorField_apply_image
    (φ := φ.toSmoothSelfDiffeomorph2) X x

@[simp] lemma pullbackTangent_pushforwardVectorField_apply_image
    (X : Π x : M, TM x) (x : M) :
    φ.pullbackTangent x (φ.pushforwardVectorField X (φ x)) = X x := by
  rw [φ.pushforwardVectorField_apply_image]
  simpa using φ.pullbackTangent_pushforwardTangent x (X x)

/-- Pull back a bilinear form along the tangent equivalence induced by a `C^3` diffeomorphism. -/
noncomputable abbrev pullbackBilinearForm (x : M) :
    (TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ) →L[ℝ] (TM x →L[ℝ] TM x →L[ℝ] ℝ) :=
  (φ.toSmoothSelfDiffeomorph2).pullbackBilinearForm x

@[simp] lemma pullbackBilinearForm_apply_apply
    (x : M)
    (B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ)
    (u v : TM x) :
    φ.pullbackBilinearForm x B u v =
      B (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
  exact SmoothSelfDiffeomorph2.pullbackBilinearForm_apply_apply
    (φ := φ.toSmoothSelfDiffeomorph2) x B u v

lemma pullbackBilinearForm_symm
    (x : M)
    {B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ}
    (hB : ∀ u v : TM (φ x), B u v = B v u) :
    ∀ u v : TM x, φ.pullbackBilinearForm x B u v = φ.pullbackBilinearForm x B v u := by
  exact SmoothSelfDiffeomorph2.pullbackBilinearForm_symm
    (φ := φ.toSmoothSelfDiffeomorph2) x hB

lemma pullbackBilinearForm_pos
    (x : M)
    {B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ}
    (hB : ∀ u : TM (φ x), u ≠ 0 → 0 < B u u) :
    ∀ u : TM x, u ≠ 0 → 0 < φ.pullbackBilinearForm x B u u := by
  exact SmoothSelfDiffeomorph2.pullbackBilinearForm_pos
    (φ := φ.toSmoothSelfDiffeomorph2) x hB

lemma isVonNBounded_pullbackBilinearForm
    (x : M)
    {B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ}
    (hB : Bornology.IsVonNBounded ℝ {v : TM (φ x) | B v v < 1}) :
    Bornology.IsVonNBounded ℝ {u : TM x | φ.pullbackBilinearForm x B u u < 1} := by
  exact SmoothSelfDiffeomorph2.isVonNBounded_pullbackBilinearForm
    (φ := φ.toSmoothSelfDiffeomorph2) x hB

lemma coord_pullbackBilinearForm_eq (x0 x : M)
    (hx : x ∈ (trivializationAt E TM x0).baseSet)
    (hφx : φ x ∈ (trivializationAt E TM (φ x0)).baseSet)
    (B : TM (φ x) →L[ℝ] TM (φ x) →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates E TM OneF TStar x0 x x0 x
        (φ.pullbackBilinearForm x B) =
      let A : EndF :=
        ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
          (φ.pushforwardTangent x)
      let Bc : BilF :=
        ContinuousLinearMap.inCoordinates E TM OneF TStar
          (φ x0) (φ x) (φ x0) (φ x) B
      (A.precomp ℝ).comp (Bc.comp A) := by
  exact SmoothSelfDiffeomorph2.coord_pullbackBilinearForm_eq
    (φ := φ.toSmoothSelfDiffeomorph2) x0 x hx hφx B

/-- The coordinate representation of a pulled-back `C^2` metric is `C^2` when the
diffeomorphism is `C^3`. -/
lemma contMDiffAt_coord_pullbackBilinearForm
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) (x0 : M) :
    ContMDiffAt I 𝓘(ℝ, BilF) 2
      (fun x ↦ ContinuousLinearMap.inCoordinates E TM OneF TStar
        x0 x x0 x (φ.pullbackBilinearForm x (g.inner (φ x)))) x0 := by
  let Acoord : M → EndF := fun x ↦
    inTangentCoordinates I I (_root_.id : M → M) (φ : M → M)
      (fun y ↦ mfderiv I I (φ : M → M) y) x0 x
  let Bbase : M → BilF := fun y ↦
    ContinuousLinearMap.inCoordinates E TM OneF TStar
      (φ x0) y (φ x0) y (g.inner y)
  let Bcoord : M → BilF := fun x ↦ Bbase (φ x)
  let expr : M → BilF := fun x ↦
    (((Acoord x).precomp ℝ : OneF →L[ℝ] OneF)).comp
      ((Bcoord x).comp (Acoord x))
  have hA : ContMDiffAt I 𝓘(ℝ, EndF) 2 Acoord x0 := by
    simpa [Acoord] using
      (ContMDiffAt.mfderiv_const (I := I) (I' := I) (n := 3) (m := 2)
        (hf := φ.contMDiffAt) (by norm_num))
  have hBbase : ContMDiffAt I 𝓘(ℝ, BilF) 2 Bbase (φ x0) := by
    let f : M → TotalSpace BilF (fun y : M ↦ TM y →L[ℝ] TStar y) :=
      fun y ↦ TotalSpace.mk' BilF y (g.inner y)
    exact ((contMDiffAt_hom_bundle (f := f) (x₀ := φ x0)).mp (g.contMDiff (φ x0))).2
  have hBcoord : ContMDiffAt I 𝓘(ℝ, BilF) 2 Bcoord x0 := by
    exact hBbase.comp x0 (φ.contMDiffAt.of_le (by norm_num))
  have hExpr : ContMDiffAt I 𝓘(ℝ, BilF) 2 expr x0 := by
    have hMid : ContMDiffAt I 𝓘(ℝ, BilF) 2
        (fun x ↦ (Bcoord x).comp (Acoord x)) x0 := by
      exact hBcoord.clm_comp hA
    have hPost : ContMDiffAt I 𝓘(ℝ, OneF →L[ℝ] OneF) 2
        (fun x ↦ ((Acoord x).precomp ℝ : OneF →L[ℝ] OneF)) x0 := by
      simpa using
        (ContMDiffAt.clm_precomp (I := I) (n := 2) (F₁ := E) (F₂ := E) (F₃ := ℝ)
          (f := Acoord) (x := x0) hA)
    exact hPost.clm_comp hMid
  have hEq : expr =ᶠ[𝓝 x0] (fun x ↦
      ContinuousLinearMap.inCoordinates E TM OneF TStar
        x0 x x0 x (φ.pullbackBilinearForm x (g.inner (φ x)))) := by
    have hx :
        {x : M | x ∈ (trivializationAt E TM x0).baseSet} ∈ 𝓝 x0 :=
      (trivializationAt E TM x0).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x0)
    have hφ :
        {x : M | φ x ∈ (trivializationAt E TM (φ x0)).baseSet} ∈ 𝓝 x0 := by
      exact (φ.continuous.continuousAt).preimage_mem_nhds <|
        (trivializationAt E TM (φ x0)).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (φ x0))
    filter_upwards [hx, hφ] with x hx' hφx'
    have hAraw :
        Acoord x =
          ContinuousLinearMap.inCoordinates E TM E TM x0 x (φ x0) (φ x)
            (φ.pushforwardTangent x) := by
      have h := φ.toSmoothSelfDiffeomorph2.tangentCoord_eq_inCoordinates
        (x0 := x0) (x := x) hx' hφx'
      rw [show (φ.toSmoothSelfDiffeomorph2 : M → M) = (φ : M → M) by rfl] at h
      rw [SmoothSelfDiffeomorph3.toSmoothSelfDiffeomorph2_pushforwardTangent
        (φ := φ) x] at h
      simpa [Acoord] using h
    rw [show expr x =
        (((Acoord x).precomp ℝ : OneF →L[ℝ] OneF)).comp
          ((Bcoord x).comp (Acoord x)) by rfl]
    rw [φ.coord_pullbackBilinearForm_eq (x0 := x0) (x := x) hx' hφx' (g.inner (φ x))]
    simp [hAraw, Bcoord, Bbase]
  exact hExpr.congr_of_eventuallyEq hEq.symm

/-- Pulling a `C^2` metric back along a bundled `C^3` self-diffeomorphism produces a `C^2`
Riemannian metric. -/
def pullbackRiemannianMetric
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    Bundle.ContMDiffRiemannianMetric I 2 E TM where
  inner x := φ.pullbackBilinearForm x (g.inner (φ x))
  symm x u v := φ.pullbackBilinearForm_symm x (fun u v => g.symm (φ x) u v) u v
  pos x u hu := φ.pullbackBilinearForm_pos x (fun u hu => g.pos (φ x) u hu) u hu
  isVonNBounded x := φ.isVonNBounded_pullbackBilinearForm x (g.isVonNBounded (φ x))
  contMDiff := by
    intro x0
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    change ContMDiffAt I 𝓘(ℝ, BilF) 2
      (fun x ↦ ContinuousLinearMap.inCoordinates E TM OneF TStar
        x0 x x0 x (φ.pullbackBilinearForm x (g.inner (φ x)))) x0
    exact φ.contMDiffAt_coord_pullbackBilinearForm g x0

@[simp] lemma pullbackRiemannianMetric_inner
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (x : M) (u v : TM x) :
    (φ.pullbackRiemannianMetric g).inner x u v =
      g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
  rfl

/-- On zero-dimensional tangent fibers, every component of a `C^3` diffeomorphism-pulled metric
vanishes. -/
lemma pullbackRiemannianMetric_inner_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (x : M) (u v : TM x) :
    (φ.pullbackRiemannianMetric g).inner x u v = 0 := by
  rw [pullbackRiemannianMetric_inner]
  have hu : φ.pushforwardTangent x u = 0 := Subsingleton.elim _ _
  rw [hu]
  simp
lemma pullbackRiemannianMetric_eq_of_eq_id
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (hφ : φ = Diffeomorph.refl I M (3 : WithTop ℕ∞)) :
    φ.pullbackRiemannianMetric g = g := by
  ext x u v
  subst hφ
  let φid : SmoothSelfDiffeomorph3 (I := I) (M := M) :=
    Diffeomorph.refl I M (3 : WithTop ℕ∞)
  change
    g.inner ((_root_.id : M → M) x)
        (φid.pushforwardTangent x u)
        (φid.pushforwardTangent x v) =
      g.inner x u v
  have hu1 :
      φid.pushforwardTangent x u =
        (mfderiv I I (_root_.id : M → M) x) u := by
    have h := φid.pushforwardTangent_eq_mfderiv x
    rw [show (φid : M → M) = (_root_.id : M → M) by rfl] at h
    exact congrArg (fun f : TM x →L[ℝ] TM x => f u) h
  have hv1 :
      φid.pushforwardTangent x v =
        (mfderiv I I (_root_.id : M → M) x) v := by
    have h := φid.pushforwardTangent_eq_mfderiv x
    rw [show (φid : M → M) = (_root_.id : M → M) by rfl] at h
    exact congrArg (fun f : TM x →L[ℝ] TM x => f v) h
  have hu0 :
      (mfderiv I I (_root_.id : M → M) x) u =
        (ContinuousLinearMap.id ℝ (TM x)) u := by
    exact congrArg (fun f : TM x →L[ℝ] TM x => f u) (mfderiv_id (I := I) (x := x))
  have hv0 :
      (mfderiv I I (_root_.id : M → M) x) v =
        (ContinuousLinearMap.id ℝ (TM x)) v := by
    exact congrArg (fun f : TM x →L[ℝ] TM x => f v) (mfderiv_id (I := I) (x := x))
  have hu : φid.pushforwardTangent x u = u := by
    simpa using hu1.trans hu0
  have hv : φid.pushforwardTangent x v = v := by
    simpa using hv1.trans hv0
  rw [hu, hv]
  rfl

lemma pullbackRiemannianMetric_symm_pullbackRiemannianMetric
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    φ.pullbackRiemannianMetric
        (SmoothSelfDiffeomorph3.pullbackRiemannianMetric (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) g) = g := by
  ext x u v
  change
    (SmoothSelfDiffeomorph3.pullbackRiemannianMetric (I := I) (M := M)
        (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) g).inner (φ x)
      (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) =
        g.inner x u v
  rw [SmoothSelfDiffeomorph3.pullbackRiemannianMetric_inner]
  have hbase : (φ.symm : M → M) (φ x) = x := by
    simpa using φ.symm_apply_apply x
  have hu :
      SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x)
          (φ.pushforwardTangent x u) = u := by
    simpa using
      φ.symm_pushforwardTangent_pushforwardTangent x u
  have hv :
      SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x)
          (φ.pushforwardTangent x v) = v := by
    simpa using
      φ.symm_pushforwardTangent_pushforwardTangent x v
  rw [hu, hv]
  exact congrArg (fun y : M ↦ g.inner y u v) hbase

@[simp] lemma symm_pullbackRiemannianMetric_pullbackRiemannianMetric
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    SmoothSelfDiffeomorph3.pullbackRiemannianMetric (I := I) (M := M)
        (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M))
        (φ.pullbackRiemannianMetric g) = g := by
  have hsymm :
      (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)).symm = φ := by
    apply Diffeomorph.ext
    intro y
    rfl
  simpa only [hsymm] using
    (SmoothSelfDiffeomorph3.pullbackRiemannianMetric_symm_pullbackRiemannianMetric
      (I := I) (M := M)
      (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M))) g)

end SmoothSelfDiffeomorph3

/-- A time-dependent family of bundled `C^3` self-diffeomorphisms. -/
abbrev SmoothSelfDiffeomorph3Family :=
  CovariantDerivative.TimeFamily (SmoothSelfDiffeomorph3 (I := I) (M := M))

namespace SmoothSelfDiffeomorph3Family

/-- The constant identity family of bundled `C^3` self-diffeomorphisms. -/
def id : SmoothSelfDiffeomorph3Family (I := I) (M := M) :=
  fun _ ↦ Diffeomorph.refl I M (3 : WithTop ℕ∞)

/-- The constant family determined by a bundled `C^3` self-diffeomorphism. -/
def const (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    SmoothSelfDiffeomorph3Family (I := I) (M := M) :=
  fun _ ↦ φ

/-- Build a `C^3` self-diffeomorphism family from mutually inverse `C^3`
time-slice maps. -/
noncomputable def ofInverse
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t)) :
    SmoothSelfDiffeomorph3Family (I := I) (M := M) :=
  fun t ↦ SmoothSelfDiffeomorph3.ofInverse (I := I) (M := M)
    (F t) (G t) (hleft t) (hright t) (hF t) (hG t)

@[simp] lemma id_apply (t : ℝ) :
    SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t =
      Diffeomorph.refl I M (3 : WithTop ℕ∞) := rfl

@[simp] lemma const_apply (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) (t : ℝ) :
    SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ t = φ := rfl

@[simp] theorem ofInverse_apply_apply
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    (t : ℝ) (x : M) :
    (ofInverse (I := I) (M := M) F G hleft hright hF hG t) x = F t x := rfl

@[simp] theorem ofInverse_symm_apply
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    (t : ℝ) (x : M) :
    (ofInverse (I := I) (M := M) F G hleft hright hF hG t).symm x = G t x := rfl

variable (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))

/-- Forget one derivative in every time slice of a `C^3` diffeomorphism family. -/
def toSmoothSelfDiffeomorph2Family : SmoothSelfDiffeomorph2Family (I := I) (M := M) :=
  fun t ↦ (Φ t).toSmoothSelfDiffeomorph2

@[simp] lemma toSmoothSelfDiffeomorph2Family_apply (t : ℝ) :
    Φ.toSmoothSelfDiffeomorph2Family t = (Φ t).toSmoothSelfDiffeomorph2 := rfl

@[simp] lemma id_toSmoothSelfDiffeomorph2Family :
    (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).toSmoothSelfDiffeomorph2Family =
      SmoothSelfDiffeomorph2Family.id (I := I) (M := M) := by
  funext t
  rfl

@[simp] lemma id_toSmoothSelfMapFamily :
    (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily =
      SmoothSelfMapFamily.id (I := I) (M := M) := by
  rw [id_toSmoothSelfDiffeomorph2Family, SmoothSelfDiffeomorph2Family.id_toSmoothSelfMapFamily]

lemma id_satisfiesGaugeFlowOn_of_eq_zero
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      X s := by
  simpa using
    SmoothSelfDiffeomorph2Family.id_satisfiesGaugeFlowOn_of_eq_zero
      (I := I) (M := M) (X := X) (s := s) hX

lemma id_hasMFDerivWithinAt_of_eq_zero
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ}
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s]
        (fun τ : ℝ ↦ (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (X t ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x))) := by
  intro t ht x
  have hconst : HasMFDerivAt 𝓘(ℝ) I (fun _ : ℝ ↦ x) t
      (0 : TangentSpace 𝓘(ℝ) t →L[ℝ] TM x) := by
    simpa using (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := I) (x := t) (c := x))
  have hzero :
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (X t ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x))) =
        (0 : ℝ →L[ℝ] TM x) := by
    rw [show (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x = x by rfl,
      hX t ht x]
    ext r
    simp
  rw [hzero]
  change HasMFDerivAt[s] (fun _ : ℝ ↦ x) t
    (0 : TangentSpace 𝓘(ℝ) t →L[ℝ] TM x)
  exact hconst.hasMFDerivWithinAt

/-- A `C^3` diffeomorphism family is anchored at `t₀` if its time slice there is the identity
diffeomorphism. -/
def AnchoredAt (t₀ : ℝ) : Prop :=
  Φ t₀ = Diffeomorph.refl I M (3 : WithTop ℕ∞)

@[simp] lemma id_anchoredAt (t₀ : ℝ) :
    (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).AnchoredAt t₀ := rfl

theorem ofInverse_anchoredAt
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    {t₀ : ℝ}
    (hFid : ∀ x : M, F t₀ x = x) :
    (ofInverse (I := I) (M := M) F G hleft hright hF hG).AnchoredAt t₀ := by
  apply DFunLike.ext
  intro x
  exact hFid x

lemma AnchoredAt.apply
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (x : M) :
    Φ t₀ x = x := by
  rw [SmoothSelfDiffeomorph3Family.AnchoredAt] at hΦ
  rw [hΦ]
  rfl

lemma AnchoredAt.toSmoothSelfDiffeomorph2AnchoredAt
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    Φ.toSmoothSelfDiffeomorph2Family.AnchoredAt t₀ := by
  change (Φ t₀).toSmoothSelfDiffeomorph2 =
    Diffeomorph.refl I M (2 : WithTop ℕ∞)
  rw [hΦ]
  rfl

/-- Slice-wise `C^2` regularity is preserved by pullback through a `C^3` diffeomorphism family. -/
theorem contMDiff_two_pullbackVectorField
    {X : Π x : M, TM x}
    (hX : ContMDiff I I.tangent 2 (T% X))
    (t : ℝ) :
    ContMDiff I I.tangent 2 (T% ((Φ t).pullbackVectorField X)) :=
  (Φ t).contMDiff_two_pullbackVectorField hX

/-- Slice-wise `C^2` regularity is preserved by pushforward through a `C^3` diffeomorphism family. -/
theorem contMDiff_two_pushforwardVectorField
    {X : Π x : M, TM x}
    (hX : ContMDiff I I.tangent 2 (T% X))
    (t : ℝ) :
    ContMDiff I I.tangent 2 (T% ((Φ t).pushforwardVectorField X)) :=
  (Φ t).contMDiff_two_pushforwardVectorField hX

theorem contMDiff_two_pullback_smoothExtend
    (t : ℝ) (x : M) (u : TM x) :
    ContMDiff I I.tangent 2
      (T% ((Φ t).pullbackVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) ((Φ t) x)
          ((Φ t).pushforwardTangent x u)))) :=
  (Φ t).contMDiff_two_pullback_smoothExtend x u

theorem contMDiff_two_pushforward_smoothExtend
    (t : ℝ) (x : M) (u : TM x) :
    ContMDiff I I.tangent 2
      (T% ((Φ t).pushforwardVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))) :=
  (Φ t).contMDiff_two_pushforward_smoothExtend x u

/-- Pull back a `C^2` metric family along a `C^3` diffeomorphism family. -/
def pullbackMetricFamily (g : MetricFamily (I := I) (M := M)) :
    MetricFamily (I := I) (M := M) :=
  fun t ↦ (Φ t).pullbackRiemannianMetric (g t)

@[simp] lemma pullbackMetricFamily_inner
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    (Φ.pullbackMetricFamily g t).inner x u v =
      (g t).inner ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v) := by
  rfl

/-- On zero-dimensional tangent fibers, every component of a `C^3` family-pulled metric family
vanishes. -/
lemma pullbackMetricFamily_inner_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    (Φ.pullbackMetricFamily g t).inner x u v = 0 := by
  rw [pullbackMetricFamily_inner]
  have hu : (Φ t).pushforwardTangent x u = 0 := Subsingleton.elim _ _
  rw [hu]
  simp

/-- Unfold the time-derivative obligation for a `C³` gauge-pulled metric to the scalar
inner-product derivative at fixed tangent vectors. -/
theorem pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TM x,
      HasDerivAt
        (fun τ ↦
          (g τ).inner ((Φ τ) x)
            ((Φ τ).pushforwardTangent x u)
            ((Φ τ).pushforwardTangent x v))
        (gdot t x u v) t) :
    HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s := by
  intro t ht x u v
  simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
    hderiv ht x u v

/-- Single-time version of
`pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt`. -/
theorem pullbackMetricFamily_hasTimeDerivativeAt_of_inner_hasDerivAt
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {t : ℝ}
    (hderiv : ∀ x : M, ∀ u v : TM x,
      HasDerivAt
        (fun τ ↦
          (g τ).inner ((Φ τ) x)
            ((Φ τ).pushforwardTangent x u)
            ((Φ τ).pushforwardTangent x v))
        (gdot t x u v) t) :
    HasTimeDerivativeAt (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot t := by
  intro x u v
  simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
    hderiv x u v

/-- Extract the scalar inner-product derivative from a time-derivative statement for a `C³`
gauge-pulled metric family. -/
theorem pullbackMetricFamily_inner_hasDerivAt_of_hasTimeDerivativeOn
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M) (u v : TM x) :
    HasDerivAt
      (fun τ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v))
      (gdot t x u v) t := by
  simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
    hderiv ht x u v

/-- Single-time version of
`pullbackMetricFamily_inner_hasDerivAt_of_hasTimeDerivativeOn`. -/
theorem pullbackMetricFamily_inner_hasDerivAt_of_hasTimeDerivativeAt
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {t : ℝ}
    (hderiv : HasTimeDerivativeAt (I := I) (M := M)
      (Φ.pullbackMetricFamily g) gdot t)
    (x : M) (u v : TM x) :
    HasDerivAt
      (fun τ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v))
      (gdot t x u v) t := by
  simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
    hderiv x u v

/-- Time derivatives commute with pullback by a time-independent `C³` diffeomorphism.  This is the
static-gauge part of the non-identity gauge time-regularity problem. -/
theorem const_pullbackMetricFamily_hasTimeDerivativeOn
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g gdot s) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily g)
      (fun t x u v ↦
        gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)) s := by
  intro t ht x u v
  change HasDerivAt
    (fun s ↦ (g s).inner (φ x)
      (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)) t
  rw [SmoothSelfDiffeomorph3.pushforwardTangent_apply (φ := φ) x u,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply (φ := φ) x v]
  exact hderiv ht (φ x)
    ((mfderiv I I (φ : M → M) x) u)
    ((mfderiv I I (φ : M → M) x) v)

lemma pullbackMetricFamily_eq_at_time_of_eq_id
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ)
    (hΦ : Φ t = Diffeomorph.refl I M (3 : WithTop ℕ∞)) :
    Φ.pullbackMetricFamily g t = g t := by
  exact SmoothSelfDiffeomorph3.pullbackRiemannianMetric_eq_of_eq_id
    (φ := Φ t) (g := g t) hΦ

lemma pullbackMetricFamily_eq_at_anchored_time
    (g : MetricFamily (I := I) (M := M))
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    Φ.pullbackMetricFamily g t₀ = g t₀ := by
  exact Φ.pullbackMetricFamily_eq_at_time_of_eq_id g t₀ hΦ

@[simp] lemma id_pullbackMetricFamily
    (g : MetricFamily (I := I) (M := M)) :
    (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily g = g := by
  funext t
  exact SmoothSelfDiffeomorph3Family.pullbackMetricFamily_eq_at_anchored_time
    (I := I) (M := M)
    (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) g
    (SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t)

end SmoothSelfDiffeomorph3Family

namespace SmoothSelfDiffeomorph2Family

variable (Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M))
lemma AnchoredAt.pushforwardTangent
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (x : M) (u : TM x) :
    (Φ t₀).pushforwardTangent x u = u := by
  rw [SmoothSelfDiffeomorph2Family.AnchoredAt] at hΦ
  rw [hΦ]
  have h := SmoothSelfDiffeomorph2.pushforwardTangent_eq_mfderiv
    (φ := Diffeomorph.refl I M (2 : WithTop ℕ∞)) x
  rw [show (Diffeomorph.refl I M (2 : WithTop ℕ∞) : M → M) =
      (_root_.id : M → M) by rfl] at h
  have hid : (mfderiv I I (_root_.id : M → M) x) u = u := by
    simpa using congrArg (fun f : TM x →L[ℝ] TM x => f u)
      (mfderiv_id (I := I) (x := x))
  exact (congrArg (fun f : TM x →L[ℝ] TM x => f u) h).trans hid

lemma AnchoredAt.pushforwardVectorField
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (X : Π x : M, TM x) :
    (Φ t₀).pushforwardVectorField X = X := by
  funext x
  have hpoint : Φ t₀ x = x :=
    SmoothSelfDiffeomorph2Family.AnchoredAt.apply (Φ := Φ) hΦ x
  have htan : (Φ t₀).pushforwardTangent x (X x) = X x :=
    SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent (Φ := Φ) hΦ x (X x)
  have himage := SmoothSelfDiffeomorph2.pushforwardVectorField_apply_image
    (φ := Φ t₀) X x
  rw [hpoint] at himage
  exact himage.trans htan

/-- Pull back a time-dependent tangent-bundle affine-connection family slice by slice along a
time-dependent family of bundled `C^2` self-diffeomorphisms. -/
noncomputable def pullbackConnectionFamily
    (cov : ConnectionFamily (I := I) (M := M)) :
    ConnectionFamily (I := I) (M := M) :=
  fun t ↦ (Φ t).pullbackCovariantDerivative (cov t)

@[simp] lemma pullbackConnectionFamily_apply
    (cov : ConnectionFamily (I := I) (M := M)) (t : ℝ) :
    Φ.pullbackConnectionFamily cov t = (Φ t).pullbackCovariantDerivative (cov t) := rfl

lemma pullbackConnectionFamily_eq_at_time_of_eq_id_apply
    (cov : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hΦ : Φ t = Diffeomorph.refl I M (2 : WithTop ℕ∞))
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    Φ.pullbackConnectionFamily cov t X x u = cov t X x u := by
  simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using
    (SmoothSelfDiffeomorph2.pullbackCovariantDerivative_eq_of_eq_id_apply
      (φ := Φ t) (cov := cov t) hΦ X x u)

lemma pullbackConnectionFamily_eq_at_time_of_eq_id
    (cov : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hΦ : Φ t = Diffeomorph.refl I M (2 : WithTop ℕ∞)) :
    Φ.pullbackConnectionFamily cov t = cov t := by
  ext X x u
  exact Φ.pullbackConnectionFamily_eq_at_time_of_eq_id_apply cov t hΦ X x u

lemma pullbackConnectionFamily_eq_at_anchored_time_apply
    (cov : ConnectionFamily (I := I) (M := M))
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    Φ.pullbackConnectionFamily cov t₀ X x u = cov t₀ X x u := by
  exact Φ.pullbackConnectionFamily_eq_at_time_of_eq_id_apply cov t₀ hΦ X x u

lemma pullbackConnectionFamily_eq_at_anchored_time
    (cov : ConnectionFamily (I := I) (M := M))
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    Φ.pullbackConnectionFamily cov t₀ = cov t₀ := by
  exact Φ.pullbackConnectionFamily_eq_at_time_of_eq_id cov t₀ hΦ

@[simp] lemma id_pullbackConnectionFamily
    (cov : ConnectionFamily (I := I) (M := M)) :
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      (SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) cov = cov := by
  funext t
  exact SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time
    (I := I) (M := M) (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
    cov (SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t)

lemma difference_pullbackConnectionFamily
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {X : Π x : M, TM x} {t : ℝ} {x : M}
    (hX : MDiffAt (T% X) x) :
    CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
        (Φ.pullbackConnectionFamily cov' t) x (X x) =
      ((Φ t).pullbackTangent x).comp
        (((CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
          ((Φ t).pushforwardVectorField X ((Φ t) x))).comp
            ((Φ t).pushforwardTangent x)) := by
  simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using
    (SmoothSelfDiffeomorph2.difference_pullbackCovariantDerivative
      (φ := Φ t) (cov := cov t) (cov' := cov' t) (X := X) (x := x) hX)

@[simp] lemma difference_pullbackConnectionFamily_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {X : Π x : M, TM x} {t : ℝ} {x : M}
    (hX : MDiffAt (T% X) x) (u : TM x) :
    CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
        (Φ.pullbackConnectionFamily cov' t) x (X x) u =
      (Φ t).pullbackTangent x
        ((CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
          ((Φ t).pushforwardVectorField X ((Φ t) x))
          ((Φ t).pushforwardTangent x u)) := by
  rw [Φ.difference_pullbackConnectionFamily (cov := cov) (cov' := cov') (X := X) hX]
  rfl

@[simp] lemma difference_pullbackConnectionFamily_smoothExtend_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w u : TM x) :
    CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
        (Φ.pullbackConnectionFamily cov' t) x w u =
      (Φ t).pullbackTangent x
        ((CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
          ((Φ t).pushforwardTangent x w)
          ((Φ t).pushforwardTangent x u)) := by
  let X : Π y : M, TM y :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w
  have hX₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)) := by
    simpa [X] using
      CovariantDerivative.smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x w
  have hX : MDiffAt (T% X) x := by
    exact (hX₁ x).mdifferentiableAt one_ne_zero
  have hx : X x = w := by
    simpa [X] using
      CovariantDerivative.smoothExtend_apply (I := I) (F := E) (V := TM) x w
  calc
    CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
        (Φ.pullbackConnectionFamily cov' t) x w u =
      CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
        (Φ.pullbackConnectionFamily cov' t) x (X x) u := by
          rw [hx]
    _ = (Φ t).pullbackTangent x
        ((CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
          ((Φ t).pushforwardVectorField X ((Φ t) x))
          ((Φ t).pushforwardTangent x u)) := by
          exact Φ.difference_pullbackConnectionFamily_apply
            (cov := cov) (cov' := cov') (X := X) hX u
    _ = (Φ t).pullbackTangent x
        ((CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
          ((Φ t).pushforwardTangent x w)
          ((Φ t).pushforwardTangent x u)) := by
          rw [SmoothSelfDiffeomorph2.pushforwardVectorField_apply_image, hx]

@[simp] lemma pushforwardTangent_difference_pullbackConnectionFamily_smoothExtend_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w u : TM x) :
    (Φ t).pushforwardTangent x
        (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
          (Φ.pullbackConnectionFamily cov' t) x w u) =
      (CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
        ((Φ t).pushforwardTangent x w)
        ((Φ t).pushforwardTangent x u) := by
  rw [Φ.difference_pullbackConnectionFamily_smoothExtend_apply
    (cov := cov) (cov' := cov') (t := t) (x := x) w u]
  simpa using
    (Φ t).pushforwardTangent_pullbackTangent x
      ((CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
        ((Φ t).pushforwardTangent x w)
        ((Φ t).pushforwardTangent x u))

@[simp] lemma tangentMap_conj_difference_pullbackConnectionFamily_smoothExtend_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) (z : TM ((Φ t) x)) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
        (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
          (Φ.pullbackConnectionFamily cov' t) x w).toLinearMap) z =
      (CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
        ((Φ t).pushforwardTangent x w) z := by
  rw [LinearEquiv.conj_apply]
  change
    (Φ t).pushforwardTangent x
        (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
          (Φ.pullbackConnectionFamily cov' t) x w ((Φ t).pullbackTangent x z)) =
      (CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x)
        ((Φ t).pushforwardTangent x w) z
  rw [Φ.pushforwardTangent_difference_pullbackConnectionFamily_smoothExtend_apply
    (cov := cov) (cov' := cov') (t := t) (x := x) w ((Φ t).pullbackTangent x z)]
  rw [(Φ t).pushforwardTangent_pullbackTangent x z]

lemma trace_difference_pullbackConnectionFamily_smoothExtend
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    LinearMap.trace ℝ (TM x)
        (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
          (Φ.pullbackConnectionFamily cov' t) x w).toLinearMap =
      LinearMap.trace ℝ (TM ((Φ t) x))
        (CovariantDerivative.difference (cov t) (cov' t) ((Φ t) x)
          ((Φ t).pushforwardTangent x w)).toLinearMap := by
  have hconj :
      (((((Φ t).tangentMap x).toLinearEquiv).conj
        (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
          (Φ.pullbackConnectionFamily cov' t) x w).toLinearMap) :
          TM ((Φ t) x) →ₗ[ℝ] TM ((Φ t) x)) =
        (CovariantDerivative.difference (cov t) (cov' t) ((Φ t) x)
          ((Φ t).pushforwardTangent x w)).toLinearMap := by
    ext z
    exact Φ.tangentMap_conj_difference_pullbackConnectionFamily_smoothExtend_apply
      (cov := cov) (cov' := cov') (t := t) (x := x) w z
  calc
    LinearMap.trace ℝ (TM x)
        (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
          (Φ.pullbackConnectionFamily cov' t) x w).toLinearMap =
      LinearMap.trace ℝ (TM ((Φ t) x))
        (((((Φ t).tangentMap x).toLinearEquiv).conj
          (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
            (Φ.pullbackConnectionFamily cov' t) x w).toLinearMap) :
            TM ((Φ t) x) →ₗ[ℝ] TM ((Φ t) x)) := by
          simpa using
            (LinearMap.trace_conj'
              (R := ℝ)
              (f := (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
                (Φ.pullbackConnectionFamily cov' t) x w).toLinearMap)
              (e := ((Φ t).tangentMap x).toLinearEquiv)).symm
    _ = LinearMap.trace ℝ (TM ((Φ t) x))
        (CovariantDerivative.difference (cov t) (cov' t) ((Φ t) x)
          ((Φ t).pushforwardTangent x w)).toLinearMap := by
          rw [hconj]

@[simp] lemma tangentMap_conj_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) (z : TM ((Φ t) x)) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w).toLinearMap) z =
      connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) z := by
  rw [LinearEquiv.conj_apply]
  change
    (Φ t).pushforwardTangent x
        (CovariantDerivative.difference (Φ.pullbackConnectionFamily cov t)
          (Φ.pullbackConnectionFamily cov' t) x ((Φ t).pullbackTangent x z) w) =
      (CovariantDerivative.difference (cov t) (cov' t)) ((Φ t) x) z
        ((Φ t).pushforwardTangent x w)
  rw [Φ.pushforwardTangent_difference_pullbackConnectionFamily_smoothExtend_apply
    (cov := cov) (cov' := cov') (t := t) (x := x)
    ((Φ t).pullbackTangent x z) w]
  rw [(Φ t).pushforwardTangent_pullbackTangent x z]

lemma trace_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w).toLinearMap =
      LinearMap.trace ℝ (TM ((Φ t) x))
        (connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t
          ((Φ t) x) ((Φ t).pushforwardTangent x w)).toLinearMap := by
  have hconj :
      (((((Φ t).tangentMap x).toLinearEquiv).conj
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w).toLinearMap) :
          TM ((Φ t) x) →ₗ[ℝ] TM ((Φ t) x)) =
        (connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t
          ((Φ t) x) ((Φ t).pushforwardTangent x w)).toLinearMap := by
    ext z
    exact Φ.tangentMap_conj_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily_apply
      (cov := cov) (cov' := cov') (t := t) (x := x) w z
  calc
    LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w).toLinearMap =
      LinearMap.trace ℝ (TM ((Φ t) x))
        (((((Φ t).tangentMap x).toLinearEquiv).conj
          (connectionDifferenceTraceEndomorphism (I := I) (M := M)
            (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w).toLinearMap) :
            TM ((Φ t) x) →ₗ[ℝ] TM ((Φ t) x)) := by
          simpa using
            (LinearMap.trace_conj'
              (R := ℝ)
              (f := (connectionDifferenceTraceEndomorphism (I := I) (M := M)
                (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w).toLinearMap)
              (e := ((Φ t).tangentMap x).toLinearEquiv)).symm
    _ = LinearMap.trace ℝ (TM ((Φ t) x))
        (connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t
          ((Φ t) x) ((Φ t).pushforwardTangent x w)).toLinearMap := by
          rw [hconj]

@[simp] lemma connectionDifferenceTraceOneForm_pullbackConnectionFamily_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w =
      connectionDifferenceTraceOneForm (I := I) (M := M)
        cov cov' t ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
  rw [connectionDifferenceTraceOneForm_apply, connectionDifferenceTraceOneForm_apply]
  exact Φ.trace_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily
    (cov := cov) (cov' := cov') (t := t) (x := x) w

lemma connectionDifferenceTraceOneForm_pullbackConnectionFamily
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x =
      (connectionDifferenceTraceOneForm (I := I) (M := M)
        cov cov' t ((Φ t) x)).comp ((Φ t).pushforwardTangent x) := by
  ext w
  exact Φ.connectionDifferenceTraceOneForm_pullbackConnectionFamily_apply
    (cov := cov) (cov' := cov') (t := t) (x := x) w

lemma curvatureAux_pullbackConnectionFamily
    (cov : ConnectionFamily (I := I) (M := M))
    {X Y σ : Π x : M, TM x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    ∀ t : ℝ,
      (Φ.pullbackConnectionFamily cov t).curvatureAux X Y σ =
        (Φ t).pullbackVectorField
          ((cov t).curvatureAux
            ((Φ t).pushforwardVectorField X)
            ((Φ t).pushforwardVectorField Y)
            ((Φ t).pushforwardVectorField σ)) := by
  intro t
  exact SmoothSelfDiffeomorph2.curvatureAux_pullbackCovariantDerivative
    (φ := Φ t) (cov := cov t) hX hY

@[simp] lemma curvatureAux_pullbackConnectionFamily_apply
    (cov : ConnectionFamily (I := I) (M := M))
    {X Y σ : Π x : M, TM x} {t : ℝ} {x : M}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (Φ.pullbackConnectionFamily cov t).curvatureAux X Y σ x =
      (Φ t).pullbackTangent x
        ((cov t).curvatureAux
          ((Φ t).pushforwardVectorField X)
          ((Φ t).pushforwardVectorField Y)
          ((Φ t).pushforwardVectorField σ) ((Φ t) x)) := by
  simpa [SmoothSelfDiffeomorph2.pullbackVectorField] using
    (SmoothSelfDiffeomorph2.curvatureAux_pullbackCovariantDerivative_apply
      (φ := Φ t) (cov := cov t) (X := X) (Y := Y) (σ := σ) (x := x) hX hY)

@[simp] lemma curvatureTensor_pullbackConnectionFamily_apply
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x) :
    (Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w =
      (Φ t).pullbackTangent x
        ((cov t).curvatureAux
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          ((Φ t) x)) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        ((Φ t).pullbackCovariantDerivative (cov t)) 1 := by
    simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using hpull t
  simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using
    (SmoothSelfDiffeomorph2.curvatureTensor_pullbackCovariantDerivative_apply
      (φ := Φ t) (cov := cov t) (x := x) (u := u) (v := v) (w := w))

@[simp] lemma pushforwardTangent_ricciEndomorphism_pullbackConnectionFamily
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w v : TM x) :
    (Φ t).pushforwardTangent x
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w v) =
        (cov t).curvatureAux
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          ((Φ t) x) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        ((Φ t).pullbackCovariantDerivative (cov t)) 1 := by
    simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using hpull t
  simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using
    (SmoothSelfDiffeomorph2.pushforwardTangent_ricciEndomorphism_pullbackCovariantDerivative
      (φ := Φ t) (cov := cov t) (x := x) (u := u) (w := w) (v := v))

@[simp] lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_apply
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x) (z : TM ((Φ t) x)) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) z =
        (cov t).curvatureAux
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x
              ((Φ t).pullbackTangent x z)))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          ((Φ t) x) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        ((Φ t).pullbackCovariantDerivative (cov t)) 1 := by
    simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using hpull t
  simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using
    (SmoothSelfDiffeomorph2.tangentMap_conj_ricciEndomorphism_pullbackCovariantDerivative_apply
      (φ := Φ t) (cov := cov t) (x := x) (u := u) (w := w) (z := z))

lemma ricciCurvature_pullbackConnectionFamily_eq_trace_tangentMap_conj_ricciEndomorphism
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      LinearMap.trace ℝ (TM ((Φ t) x))
        ((((Φ t).tangentMap x).toLinearEquiv).conj
          ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        ((Φ t).pullbackCovariantDerivative (cov t)) 1 := by
    simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using hpull t
  simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using
    (SmoothSelfDiffeomorph2.ricciCurvature_pullbackCovariantDerivative_eq_trace_tangentMap_conj_ricciEndomorphism
      (φ := Φ t) (cov := cov t) (x := x) (u := u) (w := w))

lemma isTorsionFree_pullbackConnectionFamily
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, (cov t).IsTorsionFree) :
    ∀ t : ℝ, (Φ.pullbackConnectionFamily cov t).IsTorsionFree := by
  intro t
  exact SmoothSelfDiffeomorph2.isTorsionFree_pullbackCovariantDerivative
    (φ := Φ t) (cov := cov t) (hcov t)

lemma isMetricCompatible_pullbackConnectionFamily
    {g g' : MetricFamily (I := I) (M := M)}
    (cov : ConnectionFamily (I := I) (M := M))
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (g t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsMetricCompatible
      (I := I) (M := M) g cov) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsMetricCompatible
      (I := I) (M := M) g' (Φ.pullbackConnectionFamily cov) := by
  intro t
  exact SmoothSelfDiffeomorph2.isMetricCompatibleTangent_pullbackCovariantDerivative
    (φ := Φ t) (g := g t) (g' := g' t) (cov := cov t) (hinner := hinner t) (hcov := hcov t)
lemma isLeviCivita_pullbackConnectionFamily
    {g g' : MetricFamily (I := I) (M := M)}
    (cov : ConnectionFamily (I := I) (M := M))
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (g t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g' (Φ.pullbackConnectionFamily cov) := by
  intro t
  exact SmoothSelfDiffeomorph2.isLeviCivita_pullbackCovariantDerivative
    (φ := Φ t) (g := g t) (g' := g' t) (cov := cov t)
    (hinner := hinner t) (hcov := hcov t)

lemma isMetricCompatible_pullbackConnectionFamily_pullbackRiemannianMetric
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsMetricCompatible
      (I := I) (M := M) g cov) :
    ∀ t : ℝ,
      letI : Bundle.RiemannianBundle TM :=
        ⟨((Φ t).pullbackRiemannianMetric (g t)).toRiemannianMetric⟩
      (Φ.pullbackConnectionFamily cov t).IsMetricCompatibleTangent := by
  intro t
  exact SmoothSelfDiffeomorph2.isMetricCompatibleTangent_pullbackCovariantDerivative_pullbackRiemannianMetric
    (φ := Φ t) (g := g t) (cov := cov t) (hcov := hcov t)
lemma isLeviCivita_pullbackConnectionFamily_pullbackRiemannianMetric
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov) :
    ∀ t : ℝ,
      letI : Bundle.RiemannianBundle TM :=
        ⟨((Φ t).pullbackRiemannianMetric (g t)).toRiemannianMetric⟩
      (Φ.pullbackConnectionFamily cov t).IsLeviCivita := by
  intro t
  exact SmoothSelfDiffeomorph2.isLeviCivita_pullbackCovariantDerivative_pullbackRiemannianMetric
    (φ := Φ t) (g := g t) (cov := cov t) (hcov := hcov t)

lemma pullbackRiemannianMetric_eq_at_time_of_eq_id
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ)
    (hΦ : Φ t = Diffeomorph.refl I M (2 : WithTop ℕ∞)) :
    (Φ t).pullbackRiemannianMetric (g t) =
      ({ g t with contMDiff := (g t).contMDiff.of_le (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) := by
  exact SmoothSelfDiffeomorph2.pullbackRiemannianMetric_eq_of_eq_id
    (φ := Φ t) (g := g t) hΦ

lemma pullbackRiemannianMetric_eq_at_anchored_time
    (g : MetricFamily (I := I) (M := M))
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    (Φ t₀).pullbackRiemannianMetric (g t₀) =
      ({ g t₀ with contMDiff := (g t₀).contMDiff.of_le (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) := by
  exact SmoothSelfDiffeomorph2Family.pullbackRiemannianMetric_eq_at_time_of_eq_id
    (Φ := Φ) g t₀ hΦ

@[simp] lemma id_pullbackRiemannianMetric
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) :
    ((SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) t).pullbackRiemannianMetric
        (g t) =
      ({ g t with contMDiff := (g t).contMDiff.of_le (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) := by
  exact SmoothSelfDiffeomorph2Family.pullbackRiemannianMetric_eq_at_anchored_time
    (I := I) (M := M) (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
    g (SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t)

end SmoothSelfDiffeomorph2Family

namespace SmoothSelfDiffeomorph3Family

variable (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
lemma AnchoredAt.pushforwardTangent
    {t₀ : ℝ}
  (hΦ : Φ.AnchoredAt t₀)
    (x : M) (u : TM x) :
    (Φ t₀).pushforwardTangent x u = u := by
  rw [SmoothSelfDiffeomorph3Family.AnchoredAt] at hΦ
  rw [hΦ]
  have h := SmoothSelfDiffeomorph3.pushforwardTangent_eq_mfderiv
    (φ := Diffeomorph.refl I M (3 : WithTop ℕ∞)) x
  rw [show (Diffeomorph.refl I M (3 : WithTop ℕ∞) : M → M) =
      (_root_.id : M → M) by rfl] at h
  have hid : (mfderiv I I (_root_.id : M → M) x) u = u := by
    simpa using congrArg (fun f : TM x →L[ℝ] TM x => f u)
      (mfderiv_id (I := I) (x := x))
  exact (congrArg (fun f : TM x →L[ℝ] TM x => f u) h).trans hid

lemma AnchoredAt.pushforwardVectorField
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (X : Π x : M, TM x) :
    (Φ t₀).pushforwardVectorField X = X := by
  simpa [SmoothSelfDiffeomorph3.pushforwardVectorField] using
    SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardVectorField
      (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      hΦ.toSmoothSelfDiffeomorph2AnchoredAt X

lemma AnchoredAt.pushforward_smoothExtend
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (x : M) (w : TM x) :
    (Φ t₀).pushforwardVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
      CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
        ((Φ t₀) x) ((Φ t₀).pushforwardTangent x w) := by
  calc
    (Φ t₀).pushforwardVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
      CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w := by
        exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardVectorField (Φ := Φ) hΦ
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)
    _ =
      CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
        ((Φ t₀) x) ((Φ t₀).pushforwardTangent x w) := by
        have hpoint : (Φ t₀) x = x :=
          SmoothSelfDiffeomorph3Family.AnchoredAt.apply (Φ := Φ) hΦ x
        have htan :
            (Φ t₀).pushforwardTangent x w = w :=
          SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent (Φ := Φ) hΦ x w
        rw [hpoint]
        rw [hpoint] at htan
        rw [htan]

/-- Pull back a connection family along a `C^3` diffeomorphism family, by forgetting one derivative
for the connection transport. -/
noncomputable def pullbackConnectionFamily
    (cov : ConnectionFamily (I := I) (M := M)) :
    ConnectionFamily (I := I) (M := M) :=
  Φ.toSmoothSelfDiffeomorph2Family.pullbackConnectionFamily cov

@[simp] lemma pullbackConnectionFamily_apply
    (cov : ConnectionFamily (I := I) (M := M)) (t : ℝ) :
    Φ.pullbackConnectionFamily cov t =
      ((Φ t).toSmoothSelfDiffeomorph2).pullbackCovariantDerivative (cov t) := rfl

lemma pullbackConnectionFamily_eq_at_anchored_time_apply
    (cov : ConnectionFamily (I := I) (M := M))
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    Φ.pullbackConnectionFamily cov t₀ X x u = cov t₀ X x u := by
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily] using
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time_apply
      (I := I) (M := M) (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      cov hΦ.toSmoothSelfDiffeomorph2AnchoredAt X x u

lemma pullbackConnectionFamily_eq_at_anchored_time
    (cov : ConnectionFamily (I := I) (M := M))
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀) :
    Φ.pullbackConnectionFamily cov t₀ = cov t₀ := by
  ext X x u
  exact Φ.pullbackConnectionFamily_eq_at_anchored_time_apply cov hΦ X x u

@[simp] lemma id_pullbackConnectionFamily
    (cov : ConnectionFamily (I := I) (M := M)) :
    SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) cov = cov := by
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily] using
    SmoothSelfDiffeomorph2Family.id_pullbackConnectionFamily (I := I) (M := M) cov

lemma trace_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w).toLinearMap =
      LinearMap.trace ℝ (TM ((Φ t) x))
        (connectionDifferenceTraceEndomorphism (I := I) (M := M) cov cov' t
          ((Φ t) x) ((Φ t).pushforwardTangent x w)).toLinearMap := by
  have h :=
    SmoothSelfDiffeomorph2Family.trace_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily
      (I := I) (M := M) (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      (cov := cov) (cov' := cov') (t := t) (x := x) w
  have htan :
      (Φ.toSmoothSelfDiffeomorph2Family t).pushforwardTangent x w =
        (Φ t).pushforwardTangent x w := by
    exact (Φ t).toSmoothSelfDiffeomorph2_pushforwardTangent_apply x w
  rw [htan] at h
  exact h

@[simp] lemma connectionDifferenceTraceOneForm_pullbackConnectionFamily_apply
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x w =
      connectionDifferenceTraceOneForm (I := I) (M := M)
        cov cov' t ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
  rw [connectionDifferenceTraceOneForm_apply, connectionDifferenceTraceOneForm_apply]
  have h :=
    SmoothSelfDiffeomorph2Family.trace_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily
      (I := I) (M := M) (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      (cov := cov) (cov' := cov') (t := t) (x := x) w
  have htan :
      (Φ.toSmoothSelfDiffeomorph2Family t).pushforwardTangent x w =
        (Φ t).pushforwardTangent x w := by
    exact (Φ t).toSmoothSelfDiffeomorph2_pushforwardTangent_apply x w
  rw [htan] at h
  exact h

lemma connectionDifferenceTraceOneForm_pullbackConnectionFamily
    (cov cov' : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (Φ.pullbackConnectionFamily cov) (Φ.pullbackConnectionFamily cov') t x =
      (connectionDifferenceTraceOneForm (I := I) (M := M)
        cov cov' t ((Φ t) x)).comp ((Φ t).pushforwardTangent x) := by
  ext w
  exact Φ.connectionDifferenceTraceOneForm_pullbackConnectionFamily_apply
    (cov := cov) (cov' := cov') (t := t) (x := x) w

lemma curvatureAux_pullbackConnectionFamily
    (cov : ConnectionFamily (I := I) (M := M))
    {X Y σ : Π x : M, TM x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    ∀ t : ℝ,
      (Φ.pullbackConnectionFamily cov t).curvatureAux X Y σ =
        (Φ t).pullbackVectorField
          ((cov t).curvatureAux
            ((Φ t).pushforwardVectorField X)
            ((Φ t).pushforwardVectorField Y)
            ((Φ t).pushforwardVectorField σ)) := by
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
    SmoothSelfDiffeomorph3Family.toSmoothSelfDiffeomorph2Family,
    SmoothSelfDiffeomorph3.pullbackVectorField, SmoothSelfDiffeomorph3.pushforwardVectorField] using
    SmoothSelfDiffeomorph2Family.curvatureAux_pullbackConnectionFamily
      (I := I) (M := M) (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      (cov := cov) (X := X) (Y := Y) (σ := σ) hX hY

@[simp] lemma curvatureAux_pullbackConnectionFamily_apply
    (cov : ConnectionFamily (I := I) (M := M))
    {X Y σ : Π x : M, TM x} {t : ℝ} {x : M}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (Φ.pullbackConnectionFamily cov t).curvatureAux X Y σ x =
      (Φ t).pullbackTangent x
        ((cov t).curvatureAux
          ((Φ t).pushforwardVectorField X)
          ((Φ t).pushforwardVectorField Y)
          ((Φ t).pushforwardVectorField σ) ((Φ t) x)) := by
  change (Φ.pullbackConnectionFamily cov t).curvatureAux X Y σ x =
      ((Φ t).pullbackVectorField
        ((cov t).curvatureAux
          ((Φ t).pushforwardVectorField X)
          ((Φ t).pushforwardVectorField Y)
          ((Φ t).pushforwardVectorField σ))) x
  exact congrArg (fun Z : Π x : M, TM x => Z x)
    (Φ.curvatureAux_pullbackConnectionFamily
      (cov := cov) (X := X) (Y := Y) (σ := σ) hX hY t)

@[simp] lemma curvatureTensor_pullbackConnectionFamily_apply
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x) :
    (Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w =
      (Φ t).pullbackTangent x
        ((cov t).curvatureAux
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          ((Φ t) x)) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  let X : Π y : M, TM y := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u
  let Y : Π y : M, TM y := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v
  let σ : Π y : M, TM y := CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w
  have hX₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)) := by
    simpa [X] using
      CovariantDerivative.smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u
  have hY₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)) := by
    simpa [Y] using
      CovariantDerivative.smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v
  have hX : MDiff (T% X) := fun y ↦
    (hX₁ y).mdifferentiableAt one_ne_zero
  have hY : MDiff (T% Y) := fun y ↦
    (hY₁ y).mdifferentiableAt one_ne_zero
  rw [CovariantDerivative.curvatureTensor_apply]
  simpa [X, Y, σ] using
    Φ.curvatureAux_pullbackConnectionFamily_apply
      (cov := cov) (X := X) (Y := Y) (σ := σ) (t := t) (x := x) hX hY

lemma pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x)
    (hRightEq :
      ∀ᶠ y' in nhds ((Φ t) x),
        (Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) y' =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((Φ t) x) ((Φ t).pushforwardTangent x w) y') :
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w) =
      (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  let y : M := (Φ t) x
  let Xpush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
  let Ypush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v)
  let Zpush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)
  have hXpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Xpush y)) := by
    simpa [Xpush] using (Φ t).contMDiff_two_pushforward_smoothExtend x u
  have hYpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Ypush y)) := by
    simpa [Ypush] using (Φ t).contMDiff_two_pushforward_smoothExtend x v
  have hZpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Zpush y)) := by
    simpa [Zpush] using (Φ t).contMDiff_two_pushforward_smoothExtend x w
  have hXeq : Xpush y = (Φ t).pushforwardTangent x u := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x u
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply]
  have hYeq : Ypush y = (Φ t).pushforwardTangent x v := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x v
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply]
  have hZeq :
      ∀ᶠ y' in nhds y, Zpush y' =
        CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) y
          ((Φ t).pushforwardTangent x w) y' := by
    filter_upwards [hRightEq] with y' hy'
    simpa [Zpush, y] using hy'
  calc
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w)
        = (cov t).curvatureAux Xpush Ypush Zpush y := by
          rw [Φ.curvatureTensor_pullbackConnectionFamily_apply
            (cov := cov) hcov hpull (t := t) (x := x) u v w]
          rw [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent]
    _ = (cov t).curvatureTensor y
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
          exact (cov t).curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_right
            (x := y) (X := Xpush) (Y := Ypush) (σ := Zpush)
            (hXpush₂.of_le (by norm_num)) (hYpush₂.of_le (by norm_num)) hZpush₂
            hXeq hYeq hZeq
    _ = (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
          rfl

lemma pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_section_eq
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x)
    (hRight :
      (Φ t).pushforwardVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((Φ t) x) ((Φ t).pushforwardTangent x w)) :
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w) =
      (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
  have hRightEq :
      ∀ᶠ y' in nhds ((Φ t) x),
        (Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) y' =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((Φ t) x) ((Φ t).pushforwardTangent x w) y' := by
    filter_upwards [] with y'
    simpa using congrFun hRight y'
  exact
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
      (cov := cov) hcov hpull (t := t) (x := x) u v w hRightEq

lemma pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_localFrameCoeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x)
    (hZpushCoeff : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y' ↦
            (trivializationAt E TM ((Φ t) x)).localFrameCoeff I b i y'
              (((Φ t).pushforwardVectorField
              (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)) y'))) :
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w) =
      (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  let y : M := (Φ t) x
  let Xpush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
  let Ypush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v)
  let Zpush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)
  have hXpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Xpush y)) := by
    simpa [Xpush] using (Φ t).contMDiff_two_pushforward_smoothExtend x u
  have hYpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Ypush y)) := by
    simpa [Ypush] using (Φ t).contMDiff_two_pushforward_smoothExtend x v
  have hZpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Zpush y)) := by
    simpa [Zpush] using (Φ t).contMDiff_two_pushforward_smoothExtend x w
  have hXeq : Xpush y = (Φ t).pushforwardTangent x u := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x u
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply]
  have hYeq : Ypush y = (Φ t).pushforwardTangent x v := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x v
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply]
  have hZpush_at : Zpush y = (Φ t).pushforwardTangent x w := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x w
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply]
  have hZpushCoeff' : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y' ↦ (trivializationAt E TM y).localFrameCoeff I b i y' (Zpush y')) := by
    intro i
    simpa [Zpush, y] using hZpushCoeff i
  have hcoeff_eq : ∀ i : ι,
      (trivializationAt E TM y).localFrameCoeff I b i y (Zpush y) =
        (trivializationAt E TM y).localFrameCoeff I b i y
          ((Φ t).pushforwardTangent x w) := by
    intro i
    rw [hZpush_at]
  calc
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w)
        = (cov t).curvatureAux Xpush Ypush Zpush y := by
          rw [Φ.curvatureTensor_pullbackConnectionFamily_apply
            (cov := cov) hcov hpull (t := t) (x := x) u v w]
          rw [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent]
    _ = (cov t).curvatureTensor y
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
          exact
            (cov t).curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right
              (b := b) (x := y) (X := Xpush) (Y := Ypush) (σ := Zpush)
              (hXpush₂.of_le (by norm_num)) (hYpush₂.of_le (by norm_num)) hZpush₂
              hXeq hYeq hZpushCoeff' hcoeff_eq
     _ = (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
          rfl

lemma pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x)
    (hZsupport : ∀ ⦃z : M⦄,
      z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
        (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet) :
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w) =
      (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) :=
  Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_localFrameCoeff
    (b := b) (cov := cov) hcov hpull (t := t) (x := x) u v w
    (fun i ↦
      (Φ t).contMDiff_two_localFrameCoeff_pushforward_smoothExtend_of_tsupport_subset
        (I := I) (b := b) w hZsupport i)

lemma pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset_finBasis
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x)
    (hZsupport : ∀ ⦃z : M⦄,
      z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
        (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet) :
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w) =
      (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
  classical
  exact
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
      (b := Module.finBasis ℝ E) (cov := cov) hcov hpull (t := t) (x := x) u v w
      hZsupport

lemma pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_bump_tsupport_subset
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x)
    (η : SmoothBumpFunction I x)
    (hηsource : tsupport η ⊆ (trivializationAt E TM x).baseSet)
    (hηtarget : ∀ ⦃z : M⦄, z ∈ tsupport η →
      (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet) :
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w) =
      (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
  classical
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  let y : M := (Φ t) x
  let Xcanon : Π y : M, TM y :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u
  let Ycanon : Π y : M, TM y :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v
  let Zbump : Π y : M, TM y :=
    CovariantDerivative.smoothExtendWithBump (I := I) (F := E) (V := TM) x η w
  let Xpush : Π y : M, TM y := (Φ t).pushforwardVectorField Xcanon
  let Ypush : Π y : M, TM y := (Φ t).pushforwardVectorField Ycanon
  let Zpush : Π y : M, TM y := (Φ t).pushforwardVectorField Zbump
  have hXcanon₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Xcanon y)) := by
    simpa [Xcanon] using CovariantDerivative.smoothExtend_contMDiff_one
      (I := I) (F := E) (V := TM) x u
  have hYcanon₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Ycanon y)) := by
    simpa [Ycanon] using CovariantDerivative.smoothExtend_contMDiff_one
      (I := I) (F := E) (V := TM) x v
  have hZbump₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Zbump y)) := by
    simpa [Zbump] using
      CovariantDerivative.smoothExtendWithBump_contMDiff_two_of_tsupport_subset
        (I := I) (F := E) (V := TM) x η w hηsource
  have hXpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Xpush y)) := by
    simpa [Xpush, Xcanon] using (Φ t).contMDiff_two_pushforward_smoothExtend x u
  have hYpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Ypush y)) := by
    simpa [Ypush, Ycanon] using (Φ t).contMDiff_two_pushforward_smoothExtend x v
  have hZpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Zpush y)) := by
    simpa [Zpush] using (Φ t).contMDiff_two_pushforwardVectorField hZbump₂
  have hXeq : Xpush y = (Φ t).pushforwardTangent x u := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x u
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply]
  have hYeq : Ypush y = (Φ t).pushforwardTangent x v := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x v
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply]
  have hZpush_at : Zpush y = (Φ t).pushforwardTangent x w := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtendWithBump (I := I) (F := E) (V := TM) x η w)
          ((Φ t) x) =
        (Φ t).pushforwardTangent x w
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtendWithBump_apply]
  have hZpushCoeff : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ) 2
        (fun y' ↦ (trivializationAt E TM y).localFrameCoeff I
          (Module.finBasis ℝ E) i y' (Zpush y')) := by
    intro i
    simpa [Zpush, y] using
      (Φ t).contMDiff_two_localFrameCoeff_pushforward_smoothExtendWithBump_of_tsupport_subset
        (I := I) (b := Module.finBasis ℝ E) η w hηsource hηtarget i
  have hcoeff_eq : ∀ i : Fin (Module.finrank ℝ E),
      (trivializationAt E TM y).localFrameCoeff I (Module.finBasis ℝ E) i y (Zpush y) =
        (trivializationAt E TM y).localFrameCoeff I (Module.finBasis ℝ E) i y
          ((Φ t).pushforwardTangent x w) := by
    intro i
    rw [hZpush_at]
  have hcurv_bump :
      (Φ.pullbackConnectionFamily cov t).curvatureAux Xcanon Ycanon Zbump x =
        (Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w := by
    have hXu : Xcanon x = u := by
      simpa [Xcanon] using CovariantDerivative.smoothExtend_apply
        (I := I) (F := E) (V := TM) x u
    have hYv : Ycanon x = v := by
      simpa [Ycanon] using CovariantDerivative.smoothExtend_apply
        (I := I) (F := E) (V := TM) x v
    simpa [Zbump] using
      (Φ.pullbackConnectionFamily cov t).curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_smoothExtendWithBump_right
        (φ := η) hηsource hXcanon₁ hYcanon₁ hXu hYv
  have hXmdiff : MDiff (T% Xcanon) := fun y ↦
    (hXcanon₁ y).mdifferentiableAt one_ne_zero
  have hYmdiff : MDiff (T% Ycanon) := fun y ↦
    (hYcanon₁ y).mdifferentiableAt one_ne_zero
  calc
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w)
        = (Φ t).pushforwardTangent x
            ((Φ.pullbackConnectionFamily cov t).curvatureAux Xcanon Ycanon Zbump x) := by
          rw [hcurv_bump]
    _ = (cov t).curvatureAux Xpush Ypush Zpush y := by
          rw [Φ.curvatureAux_pullbackConnectionFamily_apply
            (cov := cov) (X := Xcanon) (Y := Ycanon) (σ := Zbump)
            (t := t) (x := x) hXmdiff hYmdiff]
          rw [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent]
    _ = (cov t).curvatureTensor y
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
          exact
            (cov t).curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right
              (b := Module.finBasis ℝ E) (x := y) (X := Xpush) (Y := Ypush) (σ := Zpush)
              (hXpush₂.of_le (by norm_num)) (hYpush₂.of_le (by norm_num)) hZpush₂
              hXeq hYeq hZpushCoeff hcoeff_eq
    _ = (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
          rfl

lemma pushforwardTangent_curvatureTensor_pullbackConnectionFamily
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u v w : TM x) :
    (Φ t).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t).curvatureTensor x u v w) =
      (cov t).curvatureTensor ((Φ t) x)
        ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x v)
        ((Φ t).pushforwardTangent x w) := by
  classical
  let sourceSet : Set M := (trivializationAt E TM x).baseSet
  let targetSet : Set M := (trivializationAt E TM ((Φ t) x)).baseSet
  let supportSet : Set M := sourceSet ∩ (Φ t : M → M) ⁻¹' targetSet
  have hsource_mem : sourceSet ∈ nhds x := by
    exact (trivializationAt E TM x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E TM x)
  have htarget_mem : (Φ t : M → M) ⁻¹' targetSet ∈ nhds x := by
    exact ((Φ t).continuous.continuousAt).preimage_mem_nhds <|
      (trivializationAt E TM ((Φ t) x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt E TM ((Φ t) x))
  have hsupport_mem : supportSet ∈ nhds x :=
    Filter.inter_mem (f := nhds x) hsource_mem htarget_mem
  have hη :
      ∃ η : SmoothBumpFunction I x, True ∧ tsupport η ⊆ supportSet :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp hsupport_mem
  let η : SmoothBumpFunction I x := Classical.choose hη
  have hηsubset : tsupport η ⊆ supportSet := (Classical.choose_spec hη).2
  have hηsource : tsupport η ⊆ (trivializationAt E TM x).baseSet := by
    intro z hz
    exact (hηsubset hz).1
  have hηtarget : ∀ ⦃z : M⦄, z ∈ tsupport η →
      (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet := by
    intro z hz
    exact (hηsubset hz).2
  exact
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_bump_tsupport_subset
      (cov := cov) hcov hpull (t := t) (x := x) u v w η hηsource hηtarget

lemma AnchoredAt.pushforwardTangent_curvatureTensor_pullbackConnectionFamily
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {x : M} (u v w : TM x) :
    (Φ t₀).pushforwardTangent x
        ((Φ.pullbackConnectionFamily cov t₀).curvatureTensor x u v w) =
      (cov t₀).curvatureTensor x u v w := by
  have hRight :
      (Φ t₀).pushforwardVectorField
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((Φ t₀) x) ((Φ t₀).pushforwardTangent x w) :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.pushforward_smoothExtend (Φ := Φ) hΦ x w
  have htransport :=
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_section_eq
      (cov := cov) hcov hpull (t := t₀) (x := x) u v w hRight
  have hx : (Φ t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply (Φ := Φ) hΦ x
  have hu : (Φ t₀).pushforwardTangent x u = u :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent (Φ := Φ) hΦ x u
  have hv : (Φ t₀).pushforwardTangent x v = v :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent (Φ := Φ) hΦ x v
  have hw : (Φ t₀).pushforwardTangent x w = w :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent (Φ := Φ) hΦ x w
  exact htransport.trans (by
    rw [hx]
    congr)

@[simp] lemma pushforwardTangent_ricciEndomorphism_pullbackConnectionFamily
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w v : TM x) :
    (Φ t).pushforwardTangent x
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w v) =
        (cov t).curvatureAux
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          ((Φ t) x) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  rw [CovariantDerivative.ricciEndomorphism_apply]
  have h :=
    congrArg (fun q : TM x => (Φ t).pushforwardTangent x q)
      (Φ.curvatureTensor_pullbackConnectionFamily_apply
        (cov := cov) hcov hpull (t := t) (x := x) (u := v) (v := u) (w := w))
  simpa only [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent,
    CovariantDerivative.smoothExtend_apply] using h

@[simp] lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_apply
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x) (z : TM ((Φ t) x)) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) z =
        (cov t).curvatureAux
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x
              ((Φ t).pullbackTangent x z)))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u))
          ((Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
          ((Φ t) x) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  rw [LinearEquiv.conj_apply]
  change (Φ t).pushforwardTangent x
      (((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)
        ((Φ t).pullbackTangent x z)) = _
  simpa using
    Φ.pushforwardTangent_ricciEndomorphism_pullbackConnectionFamily
      (cov := cov) hcov hpull (t := t) (x := x)
      (u := u) (w := w) (v := (Φ t).pullbackTangent x z)

lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hRight : ∀ z : TM ((Φ t) x),
      (cov t).curvatureAux
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) z)
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x u))
        ((Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
        ((Φ t) x) =
      (cov t).curvatureAux
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) z)
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x u))
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x w))
        ((Φ t) x)) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
        (cov t).ricciEndomorphism ((Φ t) x)
          ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  ext z
  let y : M := (Φ t) x
  let Xpush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x
        ((Φ t).pullbackTangent x z))
  let Ypush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
  let Zpush : Π y : M, TM y :=
    (Φ t).pushforwardVectorField
      (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)
  let Xcanon : Π y' : M, TM y' :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) y z
  let Ycanon : Π y' : M, TM y' :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) y
      ((Φ t).pushforwardTangent x u)
  let Zcanon : Π y' : M, TM y' :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) y
      ((Φ t).pushforwardTangent x w)
  have hXpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Xpush y)) := by
    simpa [Xpush] using
      (Φ t).contMDiff_two_pushforward_smoothExtend x ((Φ t).pullbackTangent x z)
  have hYpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Ypush y)) := by
    simpa [Ypush] using (Φ t).contMDiff_two_pushforward_smoothExtend x u
  have hZpush₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Zpush y)) := by
    simpa [Zpush] using (Φ t).contMDiff_two_pushforward_smoothExtend x w
  have hXcanon₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y' ↦ TotalSpace.mk' E y' (Xcanon y')) := by
    simpa [Xcanon] using
      CovariantDerivative.smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) y z
  have hYcanon₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y' ↦ TotalSpace.mk' E y' (Ycanon y')) := by
    simpa [Ycanon] using
      CovariantDerivative.smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) y
        ((Φ t).pushforwardTangent x u)
  have hZcanon₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y' ↦ TotalSpace.mk' E y' (Zcanon y')) := by
    simpa [Zcanon] using
      CovariantDerivative.smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) y
        ((Φ t).pushforwardTangent x w)
  have hYpush₁ :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Ypush y)) :=
    hYpush₂.of_le (by norm_num)
  have hZpush₂' :
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Zpush y)) := hZpush₂
  have hXpush_at : MDiffAt (T% Xpush) y :=
    (hXpush₂.of_le (by norm_num) y).mdifferentiableAt one_ne_zero
  have hXcanon_at : MDiffAt (T% Xcanon) y :=
    (hXcanon₁ y).mdifferentiableAt one_ne_zero
  have hYpush_at : MDiffAt (T% Ypush) y :=
    (hYpush₁ y).mdifferentiableAt one_ne_zero
  have hYcanon_at : MDiffAt (T% Ycanon) y :=
    (hYcanon₁ y).mdifferentiableAt one_ne_zero
  have hXeq : Xpush y = Xcanon y := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x
            ((Φ t).pullbackTangent x z)) ((Φ t) x) =
        CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) z ((Φ t) x)
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply, CovariantDerivative.smoothExtend_apply]
    exact (Φ t).pushforwardTangent_pullbackTangent x z
  have hYeq : Ypush y = Ycanon y := by
    change
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x u)
          ((Φ t) x) =
        CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x u) ((Φ t) x)
    rw [SmoothSelfDiffeomorph3.pushforwardVectorField_apply_image]
    rw [CovariantDerivative.smoothExtend_apply, CovariantDerivative.smoothExtend_apply]
  calc
    ((((Φ t).tangentMap x).toLinearEquiv).conj
        ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) z =
        (cov t).curvatureAux Xpush Ypush Zpush y := by
      simpa [Xpush, Ypush, Zpush, y] using
        Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_apply
          (cov := cov) hcov hpull (t := t) (x := x) (u := u) (w := w) z
    _ = (cov t).curvatureAux Xcanon Ypush Zpush y := by
      exact (cov t).curvatureAux_eq_of_eq_left_apply
        (x := y) (X := Xpush) (X' := Xcanon) (Y := Ypush) (σ := Zpush)
        hYpush₁ hZpush₂' hXpush_at hXcanon_at hXeq
    _ = (cov t).curvatureAux Xcanon Ycanon Zpush y := by
      exact (cov t).curvatureAux_eq_of_eq_middle_apply
        (x := y) (X := Xcanon) (Y := Ypush) (Y' := Ycanon) (σ := Zpush)
        hXcanon₁ hZpush₂' hYpush_at hYcanon_at hYeq
    _ = (cov t).curvatureAux Xcanon Ycanon Zcanon y := by
      simpa [Xcanon, Ycanon, Zpush, Zcanon, y] using hRight z
    _ = (cov t).ricciEndomorphism y ((Φ t).pushforwardTangent x u)
        ((Φ t).pushforwardTangent x w) z := by
      simp [CovariantDerivative.ricciEndomorphism_apply,
        CovariantDerivative.curvatureTensor_apply, Xcanon, Ycanon, Zcanon, y]

lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hRightEq :
      ∀ᶠ y' in nhds ((Φ t) x),
        (Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) y' =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((Φ t) x) ((Φ t).pushforwardTangent x w) y') :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
        (cov t).ricciEndomorphism ((Φ t) x)
          ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  ext z
  rw [LinearEquiv.conj_apply]
  change
    (Φ t).pushforwardTangent x
        (((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)
          ((Φ t).pullbackTangent x z)) =
      ((cov t).ricciEndomorphism ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w)) z
  rw [CovariantDerivative.ricciEndomorphism_apply]
  have hcurv :=
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
      (cov := cov) hcov hpull (t := t) (x := x)
      ((Φ t).pullbackTangent x z) u w hRightEq
  exact hcurv.trans (by
    rw [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent]
    rw [CovariantDerivative.ricciEndomorphism_apply])

lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot_localFrameCoeff
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hZpushCoeff : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y' ↦
            (trivializationAt E TM ((Φ t) x)).localFrameCoeff I b i y'
              (((Φ t).pushforwardVectorField
              (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)) y'))) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
        (cov t).ricciEndomorphism ((Φ t) x)
          ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  ext z
  rw [LinearEquiv.conj_apply]
  change
    (Φ t).pushforwardTangent x
        (((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)
          ((Φ t).pullbackTangent x z)) =
      ((cov t).ricciEndomorphism ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w)) z
  rw [CovariantDerivative.ricciEndomorphism_apply]
  have hcurv :=
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_localFrameCoeff
      (b := b) (cov := cov) hcov hpull (t := t) (x := x)
      ((Φ t).pullbackTangent x z) u w hZpushCoeff
  exact hcurv.trans (by
    rw [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent]
    rw [CovariantDerivative.ricciEndomorphism_apply])

lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hZsupport : ∀ ⦃z : M⦄,
      z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
        (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
        (cov t).ricciEndomorphism ((Φ t) x)
          ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  ext z
  rw [LinearEquiv.conj_apply]
  change
    (Φ t).pushforwardTangent x
        (((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)
          ((Φ t).pullbackTangent x z)) =
      ((cov t).ricciEndomorphism ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w)) z
  rw [CovariantDerivative.ricciEndomorphism_apply]
  have hcurv :=
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
      (b := b) (cov := cov) hcov hpull (t := t) (x := x)
      ((Φ t).pullbackTangent x z) u w hZsupport
  exact hcurv.trans (by
    rw [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent]
    rw [CovariantDerivative.ricciEndomorphism_apply])

lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset_finBasis
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hZsupport : ∀ ⦃z : M⦄,
      z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
        (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
        (cov t).ricciEndomorphism ((Φ t) x)
          ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  classical
  exact
    Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
      (b := Module.finBasis ℝ E) (cov := cov) hcov hpull (t := t) (x := x) u w hZsupport

lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
        (cov t).ricciEndomorphism ((Φ t) x)
          ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  ext z
  rw [LinearEquiv.conj_apply]
  change
    (Φ t).pushforwardTangent x
        (((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)
          ((Φ t).pullbackTangent x z)) =
      ((cov t).ricciEndomorphism ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w)) z
  rw [CovariantDerivative.ricciEndomorphism_apply]
  have hcurv :=
    Φ.pushforwardTangent_curvatureTensor_pullbackConnectionFamily
      (cov := cov) hcov hpull (t := t) (x := x)
      ((Φ t).pullbackTangent x z) u w
  exact hcurv.trans (by
    rw [SmoothSelfDiffeomorph3.pushforwardTangent_pullbackTangent]
    rw [CovariantDerivative.ricciEndomorphism_apply])

lemma tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot_section_eq
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hRightEq :
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
        CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x w)) :
    ((((Φ t).tangentMap x).toLinearEquiv).conj
      ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
        (cov t).ricciEndomorphism ((Φ t) x)
          ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
    (cov := cov) hcov hpull (t := t) (x := x) u w (by
      filter_upwards [] with y'
      simpa using congrFun hRightEq y')

lemma ricciCurvature_pullbackConnectionFamily_eq_trace_tangentMap_conj_ricciEndomorphism
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      LinearMap.trace ℝ (TM ((Φ t) x))
        ((((Φ t).tangentMap x).toLinearEquiv).conj
          ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) := by
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
    SmoothSelfDiffeomorph3Family.toSmoothSelfDiffeomorph2Family,
    SmoothSelfDiffeomorph3.tangentMap] using
    SmoothSelfDiffeomorph2Family.ricciCurvature_pullbackConnectionFamily_eq_trace_tangentMap_conj_ricciEndomorphism
      (I := I) (M := M) (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      cov hcov (by
        intro t
        simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily] using hpull t)
      (t := t) (x := x) u w

lemma ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hconj :
      ((((Φ t).tangentMap x).toLinearEquiv).conj
        ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) =
          (cov t).ricciEndomorphism ((Φ t) x)
            ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w)) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 := hpull t
  rw [Φ.ricciCurvature_pullbackConnectionFamily_eq_trace_tangentMap_conj_ricciEndomorphism
    (cov := cov) hcov hpull (t := t) (x := x) u w]
  rw [CovariantDerivative.ricciCurvature_apply]
  rw [hconj]

lemma ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism_apply
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hconj : ∀ z : TM ((Φ t) x),
      ((((Φ t).tangentMap x).toLinearEquiv).conj
        ((Φ.pullbackConnectionFamily cov t).ricciEndomorphism x u w)) z =
          (cov t).ricciEndomorphism ((Φ t) x)
            ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) z) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism
    (cov := cov) hcov hpull (t := t) (x := x) u w (LinearMap.ext hconj)

lemma ricciCurvature_pullbackConnectionFamily_eq_of_right_slot
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hRight : ∀ z : TM ((Φ t) x),
      (cov t).curvatureAux
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) z)
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x u))
        ((Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w))
        ((Φ t) x) =
      (cov t).curvatureAux
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) z)
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x u))
        (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x w))
        ((Φ t) x)) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism
    (cov := cov) hcov hpull (t := t) (x := x) u w
    (Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot
      (cov := cov) hcov hpull (t := t) (x := x) u w hRight)

lemma ricciCurvature_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hRightEq :
      ∀ᶠ y' in nhds ((Φ t) x),
        (Φ t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) y' =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((Φ t) x) ((Φ t).pushforwardTangent x w) y') :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism
    (cov := cov) hcov hpull (t := t) (x := x) u w
    (Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
      (cov := cov) hcov hpull (t := t) (x := x) u w hRightEq)

lemma ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_localFrameCoeff
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hZpushCoeff : ∀ i : ι,
      ContMDiff I 𝓘(ℝ) 2
        (fun y' ↦
            (trivializationAt E TM ((Φ t) x)).localFrameCoeff I b i y'
              (((Φ t).pushforwardVectorField
              (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)) y'))) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism
    (cov := cov) hcov hpull (t := t) (x := x) u w
    (Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot_localFrameCoeff
      (b := b) (cov := cov) hcov hpull (t := t) (x := x) u w
      hZpushCoeff)

lemma ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hZsupport : ∀ ⦃z : M⦄,
      z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
        (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism
    (cov := cov) hcov hpull (t := t) (x := x) u w
    (Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
      (b := b) (cov := cov) hcov hpull (t := t) (x := x) u w
      hZsupport)

lemma ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset_finBasis
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hZsupport : ∀ ⦃z : M⦄,
      z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
        (Φ t) z ∈ (trivializationAt E TM ((Φ t) x)).baseSet) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) := by
  classical
  exact
    Φ.ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
      (b := Module.finBasis ℝ E) (cov := cov) hcov hpull (t := t) (x := x) u w hZsupport

lemma ricciCurvature_pullbackConnectionFamily
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.ricciCurvature_pullbackConnectionFamily_eq_of_tangentMap_conj_ricciEndomorphism
    (cov := cov) hcov hpull (t := t) (x := x) u w
    (Φ.tangentMap_conj_ricciEndomorphism_pullbackConnectionFamily
      (cov := cov) hcov hpull (t := t) (x := x) u w)

lemma ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_section_eq
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t : ℝ} {x : M} (u w : TM x)
    (hRightEq :
      (Φ t).pushforwardVectorField
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
        CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
          ((Φ t) x) ((Φ t).pushforwardTangent x w)) :
    (Φ.pullbackConnectionFamily cov t).ricciCurvature x u w =
      (cov t).ricciCurvature ((Φ t) x)
        ((Φ t).pushforwardTangent x u) ((Φ t).pushforwardTangent x w) :=
  Φ.ricciCurvature_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
    (cov := cov) hcov hpull (t := t) (x := x) u w
    (by
      filter_upwards [] with y'
      simpa using congrFun hRightEq y')

lemma ricciCurvature_pullbackConnectionFamily_eq_at_anchored_time
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1)
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    {x : M} (u w : TM x) :
    (Φ.pullbackConnectionFamily cov t₀).ricciCurvature x u w =
      (cov t₀).ricciCurvature ((Φ t₀) x)
        ((Φ t₀).pushforwardTangent x u) ((Φ t₀).pushforwardTangent x w) := by
  refine
    Φ.ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_section_eq
      (cov := cov) hcov hpull (t := t₀) (x := x) u w ?_
  exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforward_smoothExtend (Φ := Φ) hΦ x w

lemma ricciCurvature_pullbackConnectionFamily_eq_self_at_anchored_time
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (cov : ConnectionFamily (I := I) (M := M))
    {t₀ : ℝ}
    (hΦ : Φ.AnchoredAt t₀)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative (cov t₀) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t₀) 1]
    (x : M) (u w : TM x) :
    (Φ.pullbackConnectionFamily cov t₀).ricciCurvature x u w =
      (cov t₀).ricciCurvature x u w := by
  have hconn : Φ.pullbackConnectionFamily cov t₀ = cov t₀ :=
    Φ.pullbackConnectionFamily_eq_at_anchored_time cov hΦ
  revert hpull
  rw [hconn]
  intro hpull
  letI := hpull
  rfl

lemma isMetricCompatible_pullbackConnectionFamily_pullbackMetricFamily
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsMetricCompatible
      (I := I) (M := M) g cov) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsMetricCompatible
      (I := I) (M := M) (Φ.pullbackMetricFamily g) (Φ.pullbackConnectionFamily cov) := by
  have hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      ((Φ.pullbackMetricFamily g) t).inner x u v =
        (g t).inner ((Φ.toSmoothSelfDiffeomorph2Family t) x)
          (((Φ.toSmoothSelfDiffeomorph2Family t).pushforwardTangent x) u)
          (((Φ.toSmoothSelfDiffeomorph2Family t).pushforwardTangent x) v) := by
    intro t x u v
    rfl
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily] using
    SmoothSelfDiffeomorph2Family.isMetricCompatible_pullbackConnectionFamily
      (I := I) (M := M) (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      (g := g) (g' := Φ.pullbackMetricFamily g) (cov := cov) hinner hcov
lemma isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) (Φ.pullbackMetricFamily g) (Φ.pullbackConnectionFamily cov) := by
  have hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      ((Φ.pullbackMetricFamily g) t).inner x u v =
        (g t).inner ((Φ.toSmoothSelfDiffeomorph2Family t) x)
          (((Φ.toSmoothSelfDiffeomorph2Family t).pushforwardTangent x) u)
          (((Φ.toSmoothSelfDiffeomorph2Family t).pushforwardTangent x) v) := by
    intro t x u v
    rfl
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily] using
    SmoothSelfDiffeomorph2Family.isLeviCivita_pullbackConnectionFamily
      (I := I) (M := M) (Φ := Φ.toSmoothSelfDiffeomorph2Family)
      (g := g) (g' := Φ.pullbackMetricFamily g) (cov := cov) hinner hcov

/-- The Ricci-flow equation is invariant under pullback by a fixed `C³` diffeomorphism. -/
theorem const_pullbackMetricFamily_satisfiesEquationAt
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {cov : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackConnectionFamily
            cov t) 1)
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {t : ℝ}
    (hEq : SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t) :
    SatisfiesEquationAt (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily g)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackConnectionFamily cov)
      hpull
      (fun τ x u v ↦ gdot τ (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      t := by
  intro x u v
  let Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ
  letI : Bundle.RiemannianBundle TM := ⟨((Φ.pullbackMetricFamily g) t).toRiemannianMetric⟩
  have hRicci :
      ((Φ.pullbackConnectionFamily cov) t).ricciCurvature x u v =
        (cov t).ricciCurvature (φ x)
          (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
    exact SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily
      (I := I) (M := M) (Φ := Φ) (cov := cov) hcov
      (by
        intro τ
        simpa [Φ] using hpull τ)
      (t := t) (x := x) u v
  calc
    gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
        = ricciFlowRHS (I := I) (M := M) g cov hcov t (φ x)
            (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
          exact hEq (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
    _ = (-2 : ℝ) *
          (cov t).ricciCurvature (φ x)
            (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) := by
          rfl
    _ = (-2 : ℝ) * ((Φ.pullbackConnectionFamily cov) t).ricciCurvature x u v := by
          rw [hRicci]
    _ = ricciFlowRHS (I := I) (M := M)
          ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily g)
          ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackConnectionFamily cov)
          hpull t x u v := by
          rfl

/-- Ricci flow is invariant under pullback by a fixed `C³` diffeomorphism. -/
theorem const_pullbackMetricFamily_isRicciFlowOn
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {cov : ConnectionFamily (I := I) (M := M)}
    {hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hFlow : IsRicciFlowOn (I := I) (M := M) g cov hcov gdot s)
    (hpull :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackConnectionFamily
            cov t) 1) :
    IsRicciFlowOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily g)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackConnectionFamily cov)
      hpull
      (fun t x u v ↦ gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      s := by
  let Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ
  refine ⟨?_, ?_, ?_⟩
  · simpa [Φ] using
      (Φ.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily g cov hFlow.1)
  · simpa [Φ] using
      SmoothSelfDiffeomorph3Family.const_pullbackMetricFamily_hasTimeDerivativeOn
        (I := I) (M := M) φ hFlow.2.1
  · intro t ht
    exact
      SmoothSelfDiffeomorph3Family.const_pullbackMetricFamily_satisfiesEquationAt
        (I := I) (M := M) φ hcov hpull (hFlow.2.2 ht)

/-- Ricci flow is invariant under pullback by a fixed `C³` diffeomorphism; the pulled-back
connection regularity is derived from Levi-Civita uniqueness. -/
theorem const_pullbackMetricFamily_isRicciFlowOn_of_isRicciFlowOn
    [SigmaCompactSpace M]
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {cov : ConnectionFamily (I := I) (M := M)}
    {hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hFlow : IsRicciFlowOn (I := I) (M := M) g cov hcov gdot s) :
    let Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ
    let hpull : ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (Φ.pullbackConnectionFamily cov t) 1 :=
      CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
        (I := I) (M := M) (g := Φ.pullbackMetricFamily g)
        (Φ.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily g cov hFlow.1)
    IsRicciFlowOn (I := I) (M := M)
      (Φ.pullbackMetricFamily g) (Φ.pullbackConnectionFamily cov) hpull
      (fun t x u v ↦ gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      s := by
  let Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ
  let hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 :=
    CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
      (I := I) (M := M) (g := Φ.pullbackMetricFamily g)
      (Φ.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily g cov hFlow.1)
  exact
    SmoothSelfDiffeomorph3Family.const_pullbackMetricFamily_isRicciFlowOn
      (I := I) (M := M) φ hFlow hpull

/-- The pointwise intrinsic Ricci-flow equation is invariant under pullback by a fixed `C³`
diffeomorphism. -/
theorem const_pullbackMetricFamily_satisfiesIntrinsicEquationAt
    [SigmaCompactSpace M]
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {t : ℝ}
    (hEq : SatisfiesIntrinsicEquationAt (I := I) (M := M) g gdot t) :
    SatisfiesIntrinsicEquationAt (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily g)
      (fun τ x u v ↦ gdot τ (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      t := by
  let Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ
  let cov : ConnectionFamily (I := I) (M := M) :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov : ∀ τ : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov τ) 1 :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g
  let hpull : ∀ τ : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov τ) 1 :=
    CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
      (I := I) (M := M) (g := Φ.pullbackMetricFamily g)
      (Φ.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily g cov
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
          (I := I) (M := M) g))
  have hOrd : SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t :=
    (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
      (I := I) (M := M) g hcov gdot t
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (M := M) g)).1 hEq
  have hPullOrd : SatisfiesEquationAt (I := I) (M := M)
      (Φ.pullbackMetricFamily g) (Φ.pullbackConnectionFamily cov) hpull
      (fun τ x u v ↦ gdot τ (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      t := by
    simpa [Φ, cov, hcov, hpull] using
      SmoothSelfDiffeomorph3Family.const_pullbackMetricFamily_satisfiesEquationAt
        (I := I) (M := M) φ hcov hpull hOrd
  exact
    (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
      (I := I) (M := M) (Φ.pullbackMetricFamily g) hpull
      (fun τ x u v ↦ gdot τ (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      t
      (Φ.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily g cov
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
          (I := I) (M := M) g))).2 hPullOrd

/-- Intrinsic Ricci flow is invariant under pullback by a fixed `C³` diffeomorphism. -/
theorem const_pullbackMetricFamily_isIntrinsicRicciFlowOn
    [SigmaCompactSpace M]
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hFlow : IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s) :
    IsIntrinsicRicciFlowOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily g)
      (fun t x u v ↦ gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      s := by
  let Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ
  let cov : ConnectionFamily (I := I) (M := M) :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g
  let hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily cov t) 1 :=
    CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
      (I := I) (M := M) (g := Φ.pullbackMetricFamily g)
      (Φ.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily g cov
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
          (I := I) (M := M) g))
  have hOrd : IsRicciFlowOn (I := I) (M := M) g cov hcov gdot s :=
    (isIntrinsicRicciFlowOn_iff_of_isLeviCivita
      (I := I) (M := M) g hcov gdot s
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (M := M) g)).1 hFlow
  have hPullOrd : IsRicciFlowOn (I := I) (M := M)
      (Φ.pullbackMetricFamily g) (Φ.pullbackConnectionFamily cov) hpull
      (fun t x u v ↦ gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      s := by
    simpa [Φ, cov, hcov, hpull] using
      SmoothSelfDiffeomorph3Family.const_pullbackMetricFamily_isRicciFlowOn
        (I := I) (M := M) φ hOrd hpull
  exact
    (isIntrinsicRicciFlowOn_iff_of_isLeviCivita
      (I := I) (M := M) (Φ.pullbackMetricFamily g) hpull
      (fun t x u v ↦ gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
      s hPullOrd.1).2 hPullOrd

end SmoothSelfDiffeomorph3Family

namespace InitialValueProblem

/-- Pull an initial-value problem back by a fixed `C³` diffeomorphism. -/
def pullbackByDiffeomorph3
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    InitialValueProblem (E := E) (H := H) (I := I) (M := M) where
  initialTime := ivp.initialTime
  initialMetric := φ.pullbackRiemannianMetric ivp.initialMetric

@[simp] lemma pullbackByDiffeomorph3_initialTime
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (ivp.pullbackByDiffeomorph3 φ).initialTime = ivp.initialTime := rfl

@[simp] lemma pullbackByDiffeomorph3_initialMetric
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (ivp.pullbackByDiffeomorph3 φ).initialMetric =
      φ.pullbackRiemannianMetric ivp.initialMetric := rfl

@[simp] theorem pullbackByDiffeomorph3_symm_pullbackByDiffeomorph3
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (ivp.pullbackByDiffeomorph3 φ).pullbackByDiffeomorph3
        (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) = ivp := by
  cases ivp
  simp [InitialValueProblem.pullbackByDiffeomorph3]

@[simp] theorem pullbackByDiffeomorph3_pullbackByDiffeomorph3_symm
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    ((ivp.pullbackByDiffeomorph3
        (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M))).pullbackByDiffeomorph3 φ) =
      ivp := by
  cases ivp
  simp [InitialValueProblem.pullbackByDiffeomorph3,
    SmoothSelfDiffeomorph3.pullbackRiemannianMetric_symm_pullbackRiemannianMetric]

end InitialValueProblem

namespace Solution

/-- Pull an ordinary Ricci-flow solution back by a fixed `C³` diffeomorphism.  The pulled-back
connection regularity is derived from the transported Levi-Civita property, so no extra
regularity assumption is needed on the transported connection family. -/
noncomputable def pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    Solution (E := E) (H := H) (I := I) (M := M) :=
  let Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ
  let hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (Φ.pullbackConnectionFamily sol.connection t) 1 :=
    CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
      (I := I) (M := M) (g := Φ.pullbackMetricFamily sol.metric)
      (Φ.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily
        sol.metric sol.connection sol.isRicciFlow.1)
  { timeSet := sol.timeSet
    metric := Φ.pullbackMetricFamily sol.metric
    connection := Φ.pullbackConnectionFamily sol.connection
    hconnection := hpull
    metricVelocity :=
      fun t x u v ↦
        sol.metricVelocity t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
    isRicciFlow :=
      SmoothSelfDiffeomorph3Family.const_pullbackMetricFamily_isRicciFlowOn
        (I := I) (M := M) φ sol.isRicciFlow hpull }

@[simp] lemma pullbackByDiffeomorph3_timeSet
    [SigmaCompactSpace M]
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).timeSet = sol.timeSet := rfl

@[simp] lemma pullbackByDiffeomorph3_metric
    [SigmaCompactSpace M]
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).metric =
      (SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily
        sol.metric := rfl

@[simp] lemma pullbackByDiffeomorph3_connection
    [SigmaCompactSpace M]
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).connection =
      (SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackConnectionFamily
        sol.connection := rfl

@[simp] lemma pullbackByDiffeomorph3_metricVelocity
    [SigmaCompactSpace M]
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).metricVelocity =
      fun t x u v ↦
        sol.metricVelocity t (φ x) (φ.pushforwardTangent x u)
          (φ.pushforwardTangent x v) := rfl

/-- Fixed diffeomorphism pullback preserves identically-zero metric velocity. -/
theorem pullbackByDiffeomorph3_zero_velocity
    [SigmaCompactSpace M]
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (hzero : ∀ t ∈ sol.timeSet, ∀ x : M, ∀ u v : TM x,
      sol.metricVelocity t x u v = 0) :
    ∀ t ∈ (sol.pullbackByDiffeomorph3 φ).timeSet, ∀ x : M, ∀ u v : TM x,
      (sol.pullbackByDiffeomorph3 φ).metricVelocity t x u v = 0 := by
  intro t ht x u v
  simpa using hzero t ht (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)

end Solution

namespace IntrinsicSolution

/-- Pull an intrinsic Ricci-flow solution back by a fixed `C³` diffeomorphism. -/
noncomputable def pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    IntrinsicSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := sol.timeSet
  metric :=
    (SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily
      sol.metric
  metricVelocity :=
    fun t x u v ↦
      sol.metricVelocity t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
  isRicciFlow :=
    SmoothSelfDiffeomorph3Family.const_pullbackMetricFamily_isIntrinsicRicciFlowOn
      (I := I) (M := M) φ sol.isRicciFlow

@[simp] lemma pullbackByDiffeomorph3_timeSet
    [SigmaCompactSpace M]
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).timeSet = sol.timeSet := rfl

@[simp] lemma pullbackByDiffeomorph3_metric
    [SigmaCompactSpace M]
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).metric =
      (SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily
        sol.metric := rfl

@[simp] lemma pullbackByDiffeomorph3_metricVelocity
    [SigmaCompactSpace M]
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).metricVelocity =
      fun t x u v ↦
        sol.metricVelocity t (φ x) (φ.pushforwardTangent x u)
          (φ.pushforwardTangent x v) := rfl

/-- Fixed diffeomorphism pullback preserves identically-zero intrinsic metric velocity. -/
theorem pullbackByDiffeomorph3_zero_velocity
    [SigmaCompactSpace M]
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (hzero : ∀ t ∈ sol.timeSet, ∀ x : M, ∀ u v : TM x,
      sol.metricVelocity t x u v = 0) :
    ∀ t ∈ (sol.pullbackByDiffeomorph3 φ).timeSet, ∀ x : M, ∀ u v : TM x,
      (sol.pullbackByDiffeomorph3 φ).metricVelocity t x u v = 0 := by
  intro t ht x u v
  simpa using hzero t ht (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)

end IntrinsicSolution

namespace LocalSolution

/-- Pull an ordinary local Ricci-flow solution back by a fixed `C³` diffeomorphism. -/
noncomputable def pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    LocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ) where
  terminalTime := sol.terminalTime
  initial_lt_terminal := by
    simpa [InitialValueProblem.pullbackByDiffeomorph3] using sol.initial_lt_terminal
  toSolution := sol.toSolution.pullbackByDiffeomorph3 φ
  interval_subset := by
    simpa [InitialValueProblem.pullbackByDiffeomorph3, Solution.pullbackByDiffeomorph3]
      using sol.interval_subset
  matchesInitialMetric := by
    intro x u v
    have hsrc := localSolution_metric_eq_initial
      (I := I) (M := M) sol (φ x)
      (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
    have hφu : φ.pushforwardTangent x u =
        (mfderiv I I (φ : M → M) x) u := φ.pushforwardTangent_apply x u
    have hφv : φ.pushforwardTangent x v =
        (mfderiv I I (φ : M → M) x) v := φ.pushforwardTangent_apply x v
    change
      (sol.toSolution.metric ivp.initialTime).inner (φ x)
          (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) =
        ivp.initialMetric.inner (φ x)
          (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
    rw [hφu, hφv]
    simpa [metricTensor] using hsrc

@[simp] lemma pullbackByDiffeomorph3_terminalTime
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).terminalTime = sol.terminalTime := rfl

@[simp] lemma pullbackByDiffeomorph3_toSolution
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).toSolution =
      sol.toSolution.pullbackByDiffeomorph3 φ := rfl

/-- Fixed diffeomorphism pullback preserves zero velocity on a local-solution interval. -/
theorem pullbackByDiffeomorph3_zero_velocity
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0) :
    ∀ t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
        (sol.pullbackByDiffeomorph3 φ).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (sol.pullbackByDiffeomorph3 φ).toSolution.metricVelocity t x u v = 0 := by
  intro t ht x u v
  have ht' : t ∈ Set.Icc ivp.initialTime sol.terminalTime := by
    simpa [InitialValueProblem.pullbackByDiffeomorph3, LocalSolution.pullbackByDiffeomorph3]
      using ht
  simpa [LocalSolution.pullbackByDiffeomorph3, Solution.pullbackByDiffeomorph3] using
    hzero t ht' (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)

/-- Reindex an ordinary local solution along an equality of the initial data. -/
def reindexInitialValueProblem
    {ivp ivp' : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hTime : ivp'.initialTime = ivp.initialTime)
    (hMetric : ∀ x : M, ∀ u v : TM x,
      ivp'.initialMetric.inner x u v = ivp.initialMetric.inner x u v) :
    LocalSolution (E := E) (H := H) (I := I) (M := M) ivp' where
  terminalTime := sol.terminalTime
  initial_lt_terminal := by
    simpa [hTime] using sol.initial_lt_terminal
  toSolution := sol.toSolution
  interval_subset := by
    intro t ht
    exact sol.interval_subset (by simpa [hTime] using ht)
  matchesInitialMetric := by
    intro x u v
    calc
      metricTensor (I := I) (M := M) sol.toSolution.metric ivp'.initialTime x u v
          = metricTensor (I := I) (M := M) sol.toSolution.metric ivp.initialTime x u v := by
            rw [hTime]
      _ = ivp.initialMetric.inner x u v := sol.matchesInitialMetric x u v
      _ = ivp'.initialMetric.inner x u v := (hMetric x u v).symm

@[simp] lemma reindexInitialValueProblem_terminalTime
    {ivp ivp' : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hTime : ivp'.initialTime = ivp.initialTime)
    (hMetric : ∀ x : M, ∀ u v : TM x,
      ivp'.initialMetric.inner x u v = ivp.initialMetric.inner x u v) :
    (sol.reindexInitialValueProblem hTime hMetric).terminalTime = sol.terminalTime := rfl

@[simp] lemma reindexInitialValueProblem_toSolution
    {ivp ivp' : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hTime : ivp'.initialTime = ivp.initialTime)
    (hMetric : ∀ x : M, ∀ u v : TM x,
      ivp'.initialMetric.inner x u v = ivp.initialMetric.inner x u v) :
    (sol.reindexInitialValueProblem hTime hMetric).toSolution = sol.toSolution := rfl

end LocalSolution

namespace IntrinsicLocalSolution

/-- Pull an intrinsic local Ricci-flow solution back by a fixed `C³` diffeomorphism. -/
noncomputable def pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ) where
  terminalTime := sol.terminalTime
  initial_lt_terminal := by
    simpa [InitialValueProblem.pullbackByDiffeomorph3] using sol.initial_lt_terminal
  toIntrinsicSolution :=
    sol.toIntrinsicSolution.pullbackByDiffeomorph3 φ
  interval_subset := by
    simpa [InitialValueProblem.pullbackByDiffeomorph3] using sol.interval_subset
  matchesInitialMetric := by
    intro x u v
    have hsrc := intrinsicLocalSolution_metric_eq_initial
      (I := I) (M := M) sol (φ x)
      (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
    have hφu : φ.pushforwardTangent x u =
        (mfderiv I I (φ : M → M) x) u := φ.pushforwardTangent_apply x u
    have hφv : φ.pushforwardTangent x v =
        (mfderiv I I (φ : M → M) x) v := φ.pushforwardTangent_apply x v
    change
      (sol.toIntrinsicSolution.metric ivp.initialTime).inner (φ x)
          (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) =
        ivp.initialMetric.inner (φ x)
          (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
    rw [hφu, hφv]
    simpa [metricTensor] using hsrc

@[simp] lemma pullbackByDiffeomorph3_terminalTime
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).terminalTime = sol.terminalTime := rfl

@[simp] lemma pullbackByDiffeomorph3_metric
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).toIntrinsicSolution.metric =
      (SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily
        sol.toIntrinsicSolution.metric := rfl

@[simp] lemma pullbackByDiffeomorph3_toIntrinsicSolution
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    (sol.pullbackByDiffeomorph3 φ).toIntrinsicSolution =
      sol.toIntrinsicSolution.pullbackByDiffeomorph3 φ := rfl

/-- Fixed diffeomorphism pullback preserves zero intrinsic velocity on a local-solution interval. -/
theorem pullbackByDiffeomorph3_zero_velocity
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicSolution.metricVelocity t x u v = 0) :
    ∀ t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
        (sol.pullbackByDiffeomorph3 φ).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (sol.pullbackByDiffeomorph3 φ).toIntrinsicSolution.metricVelocity t x u v = 0 := by
  intro t ht x u v
  have ht' : t ∈ Set.Icc ivp.initialTime sol.terminalTime := by
    simpa [InitialValueProblem.pullbackByDiffeomorph3, IntrinsicLocalSolution.pullbackByDiffeomorph3]
      using ht
  simpa [IntrinsicLocalSolution.pullbackByDiffeomorph3, IntrinsicSolution.pullbackByDiffeomorph3]
    using hzero t ht' (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)

/-- Reindex an intrinsic local solution along an equality of the initial data. -/
def reindexInitialValueProblem
    [SigmaCompactSpace M]
    {ivp ivp' : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hTime : ivp'.initialTime = ivp.initialTime)
    (hMetric : ∀ x : M, ∀ u v : TM x,
      ivp'.initialMetric.inner x u v = ivp.initialMetric.inner x u v) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp' where
  terminalTime := sol.terminalTime
  initial_lt_terminal := by
    simpa [hTime] using sol.initial_lt_terminal
  toIntrinsicSolution := sol.toIntrinsicSolution
  interval_subset := by
    intro t ht
    exact sol.interval_subset (by simpa [hTime] using ht)
  matchesInitialMetric := by
    intro x u v
    change metricTensor (I := I) (M := M) sol.toIntrinsicSolution.toSolution.metric
        ivp'.initialTime x u v = ivp'.initialMetric.inner x u v
    calc
      metricTensor (I := I) (M := M) sol.toIntrinsicSolution.toSolution.metric
          ivp'.initialTime x u v
          = metricTensor (I := I) (M := M) sol.toIntrinsicSolution.toSolution.metric
              ivp.initialTime x u v := by
            rw [hTime]
      _ = ivp.initialMetric.inner x u v := sol.matchesInitialMetric x u v
      _ = ivp'.initialMetric.inner x u v := (hMetric x u v).symm

@[simp] lemma reindexInitialValueProblem_terminalTime
    [SigmaCompactSpace M]
    {ivp ivp' : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hTime : ivp'.initialTime = ivp.initialTime)
    (hMetric : ∀ x : M, ∀ u v : TM x,
      ivp'.initialMetric.inner x u v = ivp.initialMetric.inner x u v) :
    (sol.reindexInitialValueProblem hTime hMetric).terminalTime = sol.terminalTime := rfl

@[simp] lemma reindexInitialValueProblem_toIntrinsicSolution
    [SigmaCompactSpace M]
    {ivp ivp' : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hTime : ivp'.initialTime = ivp.initialTime)
    (hMetric : ∀ x : M, ∀ u v : TM x,
      ivp'.initialMetric.inner x u v = ivp.initialMetric.inner x u v) :
    (sol.reindexInitialValueProblem hTime hMetric).toIntrinsicSolution =
      sol.toIntrinsicSolution := rfl

end IntrinsicLocalSolution

namespace InitialValueProblem

/-- Ordinary local Ricci-flow existence is preserved by pullback of the initial data along a fixed
`C³` diffeomorphism. -/
theorem nonempty_localSolution_pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) →
      Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M)
        (ivp.pullbackByDiffeomorph3 φ)) := by
  rintro ⟨sol⟩
  exact ⟨sol.pullbackByDiffeomorph3 φ⟩

/-- Intrinsic local Ricci-flow existence is preserved by pullback of the initial data along a fixed
`C³` diffeomorphism. -/
theorem nonempty_intrinsicLocalSolution_pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) →
      Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M)
        (ivp.pullbackByDiffeomorph3 φ)) := by
  rintro ⟨sol⟩
  exact ⟨sol.pullbackByDiffeomorph3 φ⟩

/-- Ricci-flat stationary local existence also transports to fixed `C³` pullbacks of the initial
metric.  This records that the current explicit stationary examples are stable under the static
gauge action already proved for general local solutions. -/
theorem nonempty_localSolution_pullbackByDiffeomorph3_of_isRicciFlat
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ)) := by
  exact nonempty_localSolution_pullbackByDiffeomorph3
    (I := I) (M := M) (ivp := ivp) φ
    (localSolution_nonempty_of_isRicciFlat (I := I) (M := M) ivp hRicciFlat)

end InitialValueProblem

namespace LocalExistenceUniqueness

/-- The existence half of an ordinary local-existence/uniqueness package transports through fixed
`C³` pullback of the initial data. -/
theorem nonempty_pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ)) :=
  InitialValueProblem.nonempty_localSolution_pullbackByDiffeomorph3
    (I := I) (M := M) (ivp := ivp) φ pkg.exists_solution

/-- Metric uniqueness in an ordinary local-existence/uniqueness package transports to the fixed
`C³` pullbacks of any two source local solutions. -/
theorem pullbackByDiffeomorph3_unique_metric
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) (sol₁.pullbackByDiffeomorph3 φ).toSolution.metric t x u v =
      metricTensor (I := I) (M := M) (sol₂.pullbackByDiffeomorph3 φ).toSolution.metric
        t x u v := by
  have hφu : φ.pushforwardTangent x u =
      (mfderiv I I (φ : M → M) x) u := φ.pushforwardTangent_apply x u
  have hφv : φ.pushforwardTangent x v =
      (mfderiv I I (φ : M → M) x) v := φ.pushforwardTangent_apply x v
  change
    (sol₁.toSolution.metric t).inner (φ x)
        (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) =
      (sol₂.toSolution.metric t).inner (φ x)
        (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
  rw [hφu, hφv]
  simpa [metricTensor] using
    pkg.unique_metric sol₁ sol₂ t ht (φ x)
      ((mfderiv I I (φ : M → M) x) u) ((mfderiv I I (φ : M → M) x) v)

/-- Connection uniqueness in an ordinary local-existence/uniqueness package transports to the fixed
`C³` pullbacks of any two source local solutions. -/
theorem pullbackByDiffeomorph3_unique_connection
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (sol₁.pullbackByDiffeomorph3 φ).toSolution.connection t σ x =
      (sol₂.pullbackByDiffeomorph3 φ).toSolution.connection t σ x := by
  let sol₁' := sol₁.pullbackByDiffeomorph3 φ
  let sol₂' := sol₂.pullbackByDiffeomorph3 φ
  have ht' :
      t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
        (min sol₁'.terminalTime sol₂'.terminalTime) := by
    simpa [sol₁', sol₂', InitialValueProblem.pullbackByDiffeomorph3,
      LocalSolution.pullbackByDiffeomorph3] using ht
  have ht₁ : t ∈ sol₁'.toSolution.timeSet :=
    sol₁'.interval_subset ⟨ht'.1, le_trans ht'.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂'.toSolution.timeSet :=
    sol₂'.interval_subset ⟨ht'.1, le_trans ht'.2 (min_le_right _ _)⟩
  exact
    localSolution_connection_eq_of_metric_eq
      (I := I) (M := M) sol₁' sol₂' ht₁ ht₂
      (fun y u v ↦
        LocalExistenceUniqueness.pullbackByDiffeomorph3_unique_metric
          (I := I) (M := M) pkg φ sol₁ sol₂ ht y u v)
      hσ

/-- Metric uniqueness transports to arbitrary ordinary local solutions of the pulled-back
initial-value problem. -/
theorem pullbackByDiffeomorph3_unique_metric_of_target
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ))
    {t : ℝ}
    (ht : t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
      (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v := by
  let ψ : SmoothSelfDiffeomorph3 (I := I) (M := M) := φ.symm
  let back₁Raw := sol₁.pullbackByDiffeomorph3 ψ
  let back₂Raw := sol₂.pullbackByDiffeomorph3 ψ
  have hTime :
      ivp.initialTime = ((ivp.pullbackByDiffeomorph3 φ).pullbackByDiffeomorph3 ψ).initialTime := by
    simp [ψ, InitialValueProblem.pullbackByDiffeomorph3]
  have hMetric : ∀ x : M, ∀ u v : TM x,
      ivp.initialMetric.inner x u v =
        ((ivp.pullbackByDiffeomorph3 φ).pullbackByDiffeomorph3 ψ).initialMetric.inner x u v := by
    intro y u' v'
    simp [ψ, InitialValueProblem.pullbackByDiffeomorph3]
  let back₁ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    back₁Raw.reindexInitialValueProblem hTime hMetric
  let back₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    back₂Raw.reindexInitialValueProblem hTime hMetric
  have htBack :
      t ∈ Set.Icc ivp.initialTime (min back₁.terminalTime back₂.terminalTime) := by
    change t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime)
    exact ht
  have huniq :=
    pkg.unique_metric back₁ back₂ t htBack (φ x)
      (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
  have hφu : φ.pushforwardTangent x u =
      (mfderiv I I (φ : M → M) x) u := φ.pushforwardTangent_apply x u
  have hφv : φ.pushforwardTangent x v =
      (mfderiv I I (φ : M → M) x) v := φ.pushforwardTangent_apply x v
  have hbase : (φ.symm : M → M) (φ x) = x := by
    simpa using φ.symm_apply_apply x
  have hu :
      SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x)
          ((mfderiv I I (φ : M → M) x) u) = u := by
    simpa [SmoothSelfDiffeomorph3.pushforwardTangent_apply] using
      φ.symm_pushforwardTangent_pushforwardTangent x u
  have hv :
      SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x)
          ((mfderiv I I (φ : M → M) x) v) = v := by
    simpa [SmoothSelfDiffeomorph3.pushforwardTangent_apply] using
      φ.symm_pushforwardTangent_pushforwardTangent x v
  have huniq' :
      (sol₁.toSolution.metric t).inner ((φ.symm : M → M) (φ x))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) u))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) v)) =
        (sol₂.toSolution.metric t).inner ((φ.symm : M → M) (φ x))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) u))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) v)) := by
    convert huniq using 1 <;>
      simp only [back₁, back₂, back₁Raw, back₂Raw, ψ, metricTensor,
      LocalSolution.reindexInitialValueProblem,
      LocalSolution.pullbackByDiffeomorph3, Solution.pullbackByDiffeomorph3,
      SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner,
      SmoothSelfDiffeomorph3Family.const, SmoothSelfDiffeomorph3Family.const_apply,
      hφu, hφv] <;> rfl
  rw [hu, hv] at huniq'
  rw [← hbase]
  simpa [metricTensor] using huniq'

/-- Connection uniqueness transports to arbitrary ordinary local solutions of the pulled-back
initial-value problem. -/
theorem pullbackByDiffeomorph3_unique_connection_of_target
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ))
    {t : ℝ}
    (ht : t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
      (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x := by
  have ht₁ : t ∈ sol₁.toSolution.timeSet :=
    sol₁.interval_subset ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂.toSolution.timeSet :=
    sol₂.interval_subset ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  exact
    localSolution_connection_eq_of_metric_eq
      (I := I) (M := M) sol₁ sol₂ ht₁ ht₂
      (fun y u v ↦
        LocalExistenceUniqueness.pullbackByDiffeomorph3_unique_metric_of_target
          (I := I) (M := M) pkg φ sol₁ sol₂ ht y u v)
      hσ

/-- Fixed `C³` pullback transports an ordinary local-existence/uniqueness package to the
pulled-back initial-value problem. -/
noncomputable def pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ) where
  exists_solution :=
    LocalExistenceUniqueness.nonempty_pullbackByDiffeomorph3
      (I := I) (M := M) pkg φ
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    exact
      LocalExistenceUniqueness.pullbackByDiffeomorph3_unique_metric_of_target
        (I := I) (M := M) pkg φ sol₁ sol₂ ht x u v

end LocalExistenceUniqueness

namespace IntrinsicLocalExistenceUniqueness

/-- The existence half of an intrinsic local-existence/uniqueness package transports through fixed
`C³` pullback of the initial data. -/
theorem nonempty_pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ)) :=
  InitialValueProblem.nonempty_intrinsicLocalSolution_pullbackByDiffeomorph3
    (I := I) (M := M) (ivp := ivp) φ pkg.exists_solution

/-- Metric uniqueness in an intrinsic local-existence/uniqueness package transports to the fixed
`C³` pullbacks of any two source intrinsic local solutions. -/
theorem pullbackByDiffeomorph3_unique_metric
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
        (sol₁.pullbackByDiffeomorph3 φ).toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M)
        (sol₂.pullbackByDiffeomorph3 φ).toIntrinsicSolution.metric t x u v := by
  have hφu : φ.pushforwardTangent x u =
      (mfderiv I I (φ : M → M) x) u := φ.pushforwardTangent_apply x u
  have hφv : φ.pushforwardTangent x v =
      (mfderiv I I (φ : M → M) x) v := φ.pushforwardTangent_apply x v
  change
    (sol₁.toIntrinsicSolution.metric t).inner (φ x)
        (φ.pushforwardTangent x u) (φ.pushforwardTangent x v) =
      (sol₂.toIntrinsicSolution.metric t).inner (φ x)
        (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
  rw [hφu, hφv]
  simpa [metricTensor] using
    pkg.unique_metric sol₁ sol₂ t ht (φ x)
      ((mfderiv I I (φ : M → M) x) u) ((mfderiv I I (φ : M → M) x) v)

/-- Connection uniqueness in an intrinsic local-existence/uniqueness package transports to the fixed
`C³` pullbacks of any two source intrinsic local solutions. -/
theorem pullbackByDiffeomorph3_unique_connection
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (sol₁.pullbackByDiffeomorph3 φ).toIntrinsicSolution.toSolution.connection t σ x =
      (sol₂.pullbackByDiffeomorph3 φ).toIntrinsicSolution.toSolution.connection t σ x := by
  let sol₁' := sol₁.pullbackByDiffeomorph3 φ
  let sol₂' := sol₂.pullbackByDiffeomorph3 φ
  have ht' :
      t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
        (min sol₁'.terminalTime sol₂'.terminalTime) := by
    simpa [sol₁', sol₂', InitialValueProblem.pullbackByDiffeomorph3,
      IntrinsicLocalSolution.pullbackByDiffeomorph3] using ht
  have ht₁ : t ∈ sol₁'.toIntrinsicSolution.timeSet :=
    sol₁'.interval_subset ⟨ht'.1, le_trans ht'.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂'.toIntrinsicSolution.timeSet :=
    sol₂'.interval_subset ⟨ht'.1, le_trans ht'.2 (min_le_right _ _)⟩
  exact
    intrinsicLocalSolution_connection_eq_of_metric_eq
      (I := I) (M := M) sol₁' sol₂' ht₁ ht₂
      (fun y u v ↦
        IntrinsicLocalExistenceUniqueness.pullbackByDiffeomorph3_unique_metric
          (I := I) (M := M) pkg φ sol₁ sol₂ ht y u v)
      hσ

/-- Metric uniqueness transports to arbitrary intrinsic local solutions of the pulled-back
initial-value problem. -/
theorem pullbackByDiffeomorph3_unique_metric_of_target
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ))
    {t : ℝ}
    (ht : t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
      (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v := by
  let ψ : SmoothSelfDiffeomorph3 (I := I) (M := M) := φ.symm
  let back₁Raw := sol₁.pullbackByDiffeomorph3 ψ
  let back₂Raw := sol₂.pullbackByDiffeomorph3 ψ
  have hTime :
      ivp.initialTime = ((ivp.pullbackByDiffeomorph3 φ).pullbackByDiffeomorph3 ψ).initialTime := by
    simp [ψ, InitialValueProblem.pullbackByDiffeomorph3]
  have hMetric : ∀ x : M, ∀ u v : TM x,
      ivp.initialMetric.inner x u v =
        ((ivp.pullbackByDiffeomorph3 φ).pullbackByDiffeomorph3 ψ).initialMetric.inner x u v := by
    intro y u' v'
    simp [ψ, InitialValueProblem.pullbackByDiffeomorph3]
  let back₁ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    back₁Raw.reindexInitialValueProblem hTime hMetric
  let back₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    back₂Raw.reindexInitialValueProblem hTime hMetric
  have htBack :
      t ∈ Set.Icc ivp.initialTime (min back₁.terminalTime back₂.terminalTime) := by
    change t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime)
    exact ht
  have huniq :=
    pkg.unique_metric back₁ back₂ t htBack (φ x)
      (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)
  have hφu : φ.pushforwardTangent x u =
      (mfderiv I I (φ : M → M) x) u := φ.pushforwardTangent_apply x u
  have hφv : φ.pushforwardTangent x v =
      (mfderiv I I (φ : M → M) x) v := φ.pushforwardTangent_apply x v
  have hbase : (φ.symm : M → M) (φ x) = x := by
    simpa using φ.symm_apply_apply x
  have hu :
      SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x)
          ((mfderiv I I (φ : M → M) x) u) = u := by
    simpa [SmoothSelfDiffeomorph3.pushforwardTangent_apply] using
      φ.symm_pushforwardTangent_pushforwardTangent x u
  have hv :
      SmoothSelfDiffeomorph3.pushforwardTangent (I := I) (M := M)
          (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)) (φ x)
          ((mfderiv I I (φ : M → M) x) v) = v := by
    simpa [SmoothSelfDiffeomorph3.pushforwardTangent_apply] using
      φ.symm_pushforwardTangent_pushforwardTangent x v
  have huniq' :
      (sol₁.toIntrinsicSolution.metric t).inner ((φ.symm : M → M) (φ x))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) u))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) v)) =
        (sol₂.toIntrinsicSolution.metric t).inner ((φ.symm : M → M) (φ x))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) u))
          (SmoothSelfDiffeomorph3.pushforwardTangent
            (φ := (φ.symm : SmoothSelfDiffeomorph3 (I := I) (M := M)))
            (φ x) ((mfderiv I I (φ : M → M) x) v)) := by
    convert huniq using 1 <;>
      simp only [back₁, back₂, back₁Raw, back₂Raw, ψ, metricTensor,
      IntrinsicLocalSolution.reindexInitialValueProblem,
      IntrinsicLocalSolution.pullbackByDiffeomorph3, IntrinsicSolution.pullbackByDiffeomorph3,
      SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner,
      SmoothSelfDiffeomorph3Family.const, SmoothSelfDiffeomorph3Family.const_apply,
      hφu, hφv] <;> rfl
  rw [hu, hv] at huniq'
  rw [← hbase]
  simpa [metricTensor] using huniq'

/-- Connection uniqueness transports to arbitrary intrinsic local solutions of the pulled-back
initial-value problem. -/
theorem pullbackByDiffeomorph3_unique_connection_of_target
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ))
    {t : ℝ}
    (ht : t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
      (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x := by
  have ht₁ : t ∈ sol₁.toIntrinsicSolution.timeSet :=
    sol₁.interval_subset ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂.toIntrinsicSolution.timeSet :=
    sol₂.interval_subset ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  exact
    intrinsicLocalSolution_connection_eq_of_metric_eq
      (I := I) (M := M) sol₁ sol₂ ht₁ ht₂
      (fun y u v ↦
        IntrinsicLocalExistenceUniqueness.pullbackByDiffeomorph3_unique_metric_of_target
          (I := I) (M := M) pkg φ sol₁ sol₂ ht y u v)
      hσ

/-- Fixed `C³` pullback transports an intrinsic local-existence/uniqueness package to the
pulled-back initial-value problem. -/
noncomputable def pullbackByDiffeomorph3
    [SigmaCompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ) where
  exists_solution :=
    IntrinsicLocalExistenceUniqueness.nonempty_pullbackByDiffeomorph3
      (I := I) (M := M) pkg φ
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    exact
      IntrinsicLocalExistenceUniqueness.pullbackByDiffeomorph3_unique_metric_of_target
        (I := I) (M := M) pkg φ sol₁ sol₂ ht x u v

end IntrinsicLocalExistenceUniqueness

end RicciFlow
