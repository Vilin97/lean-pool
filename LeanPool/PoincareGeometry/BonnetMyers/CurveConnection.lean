/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.IntrinsicAcceleration
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Covariant acceleration along a curve

The covariant-derivative API is formulated for sections over the manifold,
whereas a geodesic has a tangent vector in a changing fibre.  This file gives
an intrinsic characterization of an acceleration along a curve: it is the
unique tangent vector whose scalar products against differentiable test
sections obey the metric-compatible product rule.

The characterization makes no chart choice.  The frame computation below
then proves the transformation law for every local coordinate description.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace CurveConnection

/-- The derivative map of a real-time curve whose velocity is `v`.  Writing
the model-space identification explicitly avoids treating a tangent fibre of
the time manifold as definitionally equal to `ℝ`. -/
def timeTangentMap {x : M} (t : ℝ) (v : TM x) :
    TangentSpace (𝓘(ℝ, ℝ)) t →L[ℝ] TM x :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t).toContinuousLinearMap

theorem timeTangentMap_eq_toSpanSingleton {x : M} (t : ℝ) (v : TM x) :
    timeTangentMap (I := I) t v = ContinuousLinearMap.toSpanSingleton ℝ v := by
  apply ContinuousLinearMap.ext
  intro s
  simp only [timeTangentMap, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  rfl

/-- The time-tangent encoding retains the tangent vector it represents. -/
theorem timeTangentMap_injective {x : M} (t : ℝ) :
    Function.Injective (timeTangentMap (I := I) (x := x) t) := by
  intro v w hvw
  have hunit := congrArg (fun L ↦
      L (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) hvw
  rw [timeTangentMap] at hunit
  change (ContinuousLinearMap.toSpanSingleton ℝ v)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t)
        (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) =
    (ContinuousLinearMap.toSpanSingleton ℝ w)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t)
        (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) at hunit
  rw [ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.toSpanSingleton_apply] at hunit
  change (1 : ℝ) • v = (1 : ℝ) • w at hunit
  simpa using hunit

/-- The manifold derivative of a scalar-valued function of real time,
evaluated on the canonical unit time tangent. -/
def curveScalarDeriv (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (mvfderiv (I := 𝓘(ℝ, ℝ)) f t) 1

/-- On the real line, the manifold notation used for scalar derivatives is
the ordinary derivative.  Keeping this conversion explicit lets local
connection identities be transported across affine changes of the time
parameter without introducing a separate coordinate convention. -/
theorem curveScalarDeriv_eq_deriv (f : ℝ → ℝ) (t : ℝ) :
    curveScalarDeriv f t = deriv f t := by
  unfold curveScalarDeriv mvfderiv
  rw [mfderiv_eq_fderiv]
  rfl

/-- Translation of the time parameter preserves the scalar derivative. -/
theorem curveScalarDeriv_comp_const_add (f : ℝ → ℝ) (t : ℝ) :
    curveScalarDeriv (fun s ↦ f (t + s)) 0 = curveScalarDeriv f t := by
  rw [curveScalarDeriv_eq_deriv, curveScalarDeriv_eq_deriv,
    deriv_comp_const_add]
  simp

theorem curveScalarDeriv_eq_of_hasDerivAt
    {f : ℝ → ℝ} {t a : ℝ} (h : HasDerivAt f a t) :
    curveScalarDeriv f t = a := by
  have hMF := h.hasFDerivAt.hasMFDerivAt
  unfold curveScalarDeriv mvfderiv
  rw [hMF.mfderiv]
  change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) (f t))
      ((ContinuousLinearMap.toSpanSingleton ℝ a) 1) = a
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rfl

theorem curveScalarDeriv_comp
    {γ : ℝ → M} {g : M → ℝ} {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hg : MDiffAt g (γ t)) :
    curveScalarDeriv (g ∘ γ) t = (mvfderiv (I := I) g (γ t)) v := by
  have hvel : (mfderiv (𝓘(ℝ, ℝ)) I γ t)
      (1 : TangentSpace (𝓘(ℝ, ℝ)) t) = v := by
    rw [hγ.mfderiv]
    change (ContinuousLinearMap.toSpanSingleton ℝ v)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t)
        (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) = v
    rw [ContinuousLinearMap.toSpanSingleton_apply]
    change (1 : ℝ) • v = v
    exact one_smul ℝ v
  unfold curveScalarDeriv
  rw [mvfderiv_comp_apply t hg hγ.mdifferentiableAt 1, hvel]

theorem curveScalarDeriv_mul
    {f g : ℝ → ℝ} {t : ℝ}
    (hf : MDiffAt f t) (hg : MDiffAt g t) :
    curveScalarDeriv (f * g) t =
      f t * curveScalarDeriv g t + g t * curveScalarDeriv f t := by
  unfold curveScalarDeriv
  have h := congrArg (fun L ↦ L (1 : TangentSpace (𝓘(ℝ, ℝ)) t))
    (mvfderiv_mul (I := 𝓘(ℝ, ℝ)) hf hg)
  simpa [smul_eq_mul] using h

theorem curveScalarDeriv_add
    {f g : ℝ → ℝ} {t : ℝ}
    (hf : MDiffAt f t) (hg : MDiffAt g t) :
    curveScalarDeriv (f + g) t = curveScalarDeriv f t + curveScalarDeriv g t := by
  unfold curveScalarDeriv
  have h := congrArg (fun L ↦ L (1 : TangentSpace (𝓘(ℝ, ℝ)) t))
    (mvfderiv_add (I := 𝓘(ℝ, ℝ)) hf hg)
  simpa using h

theorem curveScalarDeriv_sum
    {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ) {t : ℝ}
    (hf : ∀ i ∈ s, MDiffAt (f i) t) :
    curveScalarDeriv (fun τ ↦ ∑ i ∈ s, f i τ) t =
      ∑ i ∈ s, curveScalarDeriv (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold curveScalarDeriv
      change (mvfderiv (I := 𝓘(ℝ, ℝ)) (fun _ : ℝ ↦ (0 : ℝ)) t) 1 = 0
      rw [mvfderiv_const]
      rfl
  | insert i s hi ih =>
      have hfi : MDiffAt (f i) t := hf i (Finset.mem_insert_self i s)
      have hfs : MDiffAt (fun τ ↦ ∑ j ∈ s, f j τ) t := by
        have hfs' : MDiffAt (∑ j ∈ s, f j) t := by
          apply MDifferentiableAt.sum (I := 𝓘(ℝ, ℝ))
          intro j hj
          exact hf j (Finset.mem_insert_of_mem hj)
        have heq : (fun τ ↦ ∑ j ∈ s, f j τ) = ∑ j ∈ s, f j := by
          funext τ
          simp
        rw [heq]
        exact hfs'
      have hfun : (fun τ ↦ ∑ j ∈ insert i s, f j τ) =
          fun τ ↦ f i τ + ∑ j ∈ s, f j τ := by
        funext τ
        rw [Finset.sum_insert hi]
      have hadd : (fun τ ↦ f i τ + ∑ j ∈ s, f j τ) =
          f i + (fun τ ↦ ∑ j ∈ s, f j τ) := by
        rfl
      rw [hfun, hadd, curveScalarDeriv_add hfi hfs, Finset.sum_insert hi]
      rw [ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

theorem curveScalarDeriv_congr_of_eventuallyEq
    {f g : ℝ → ℝ} {t : ℝ} (hfg : f =ᶠ[𝓝 t] g) :
    curveScalarDeriv f t = curveScalarDeriv g t := by
  unfold curveScalarDeriv mvfderiv
  rw [hfg.mfderiv_eq]
  exact congrArg (fun z ↦
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) z)
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) g t) 1))
    (Filter.Eventually.self_of_nhds (p := fun s ↦ f s = g s) hfg)

/-- A local equality after translating the parameter transports the scalar
derivative back to the original time.  This formulation works directly with
the germ certificates carried by global geodesics. -/
theorem curveScalarDeriv_eq_of_eventuallyEq_const_add
    {f g : ℝ → ℝ} {t : ℝ}
    (hfg : (fun s ↦ f (t + s)) =ᶠ[𝓝 (0 : ℝ)] g) :
    curveScalarDeriv f t = curveScalarDeriv g 0 := by
  rw [← curveScalarDeriv_comp_const_add f t]
  exact curveScalarDeriv_congr_of_eventuallyEq hfg

variable [FiniteDimensional ℝ E] [CompleteSpace E]
  [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- `A` is the covariant acceleration of a tangent-vector family `V` along
`γ` at time `t` when the metric-compatible product rule holds against every
differentiable test section. -/
def IsCovariantAccelerationAt
    (cov : CovariantDerivative I E TM) (γ : ℝ → M)
    (V : (s : ℝ) → TM (γ s)) (t : ℝ) (v A : TM (γ t)) : Prop :=
  ∀ W : (x : M) → TM x, MDiffAt (T% W) (γ t) →
    curveScalarDeriv (fun s ↦ inner ℝ (V s) (W (γ s))) t =
      inner ℝ A (W (γ t)) + inner ℝ (V t) (cov W (γ t) v)

theorem IsCovariantAccelerationAt.unique
    {cov : CovariantDerivative I E TM} {γ : ℝ → M}
    {V : (s : ℝ) → TM (γ s)} {t : ℝ} {v A B : TM (γ t)}
    (hA : IsCovariantAccelerationAt cov γ V t v A)
    (hB : IsCovariantAccelerationAt cov γ V t v B) : A = B := by
  apply ext_inner_right ℝ
  intro z
  have hA' := hA (FiberBundle.extend E z) (FiberBundle.mdifferentiableAt_extend ..)
  have hB' := hB (FiberBundle.extend E z) (FiberBundle.mdifferentiableAt_extend ..)
  simp only [FiberBundle.extend_apply_self] at hA' hB'
  linarith

/-- The scalar characterization depends only on the germ of the tangent
vector family along the curve at the time under consideration. -/
theorem IsCovariantAccelerationAt.congr_of_eventuallyEq
    {cov : CovariantDerivative I E TM} {γ : ℝ → M}
    {V U : (s : ℝ) → TM (γ s)} {t : ℝ} {v A : TM (γ t)}
    (hA : IsCovariantAccelerationAt cov γ V t v A)
    (hVU : V =ᶠ[𝓝 t] U) :
    IsCovariantAccelerationAt cov γ U t v A := by
  intro W hW
  have hscalar : (fun s ↦ inner ℝ (V s) (W (γ s))) =ᶠ[𝓝 t]
      (fun s ↦ inner ℝ (U s) (W (γ s))) := by
    filter_upwards [hVU] with s hs
    rw [hs]
  have hvalue : V t = U t :=
    Filter.Eventually.self_of_nhds (p := fun s ↦ V s = U s) hVU
  calc
    curveScalarDeriv (fun s ↦ inner ℝ (U s) (W (γ s))) t =
        curveScalarDeriv (fun s ↦ inner ℝ (V s) (W (γ s))) t :=
      curveScalarDeriv_congr_of_eventuallyEq hscalar.symm
    _ = inner ℝ A (W (γ t)) + inner ℝ (V t) (cov W (γ t) v) := hA W hW
    _ = inner ℝ A (W (γ t)) + inner ℝ (U t) (cov W (γ t) v) := by rw [hvalue]

/-- Multiplying a tangent-vector family by a differentiable scalar gives the
expected intrinsic product rule.  The separate scalar-pairing differentiability
hypothesis is essential: the abstract acceleration predicate itself records a
derivative value, but does not imply that the scalar pairing is differentiable. -/
theorem IsCovariantAccelerationAt.smul
    {cov : CovariantDerivative I E TM} {γ : ℝ → M}
    {V : (s : ℝ) → TM (γ s)} {t : ℝ} {v A : TM (γ t)}
    {f : ℝ → ℝ}
    (hA : IsCovariantAccelerationAt cov γ V t v A)
    (hf : MDiffAt f t)
    (hscalar : ∀ W : (x : M) → TM x, MDiffAt (T% W) (γ t) →
      MDiffAt (fun s ↦ inner ℝ (V s) (W (γ s))) t) :
    IsCovariantAccelerationAt cov γ (fun s ↦ f s • V s) t v
      (curveScalarDeriv f t • V t + f t • A) := by
  intro W hW
  have hpair := hscalar W hW
  have hrewrite : (fun s ↦ inner ℝ (f s • V s) (W (γ s))) =
      f * (fun s ↦ inner ℝ (V s) (W (γ s))) := by
    funext s
    change inner ℝ (f s • V s) (W (γ s)) =
      f s * inner ℝ (V s) (W (γ s))
    rw [real_inner_smul_left]
  rw [hrewrite, curveScalarDeriv_mul hf hpair, hA W hW]
  simp only [inner_add_left, real_inner_smul_left]
  ring

/-- A curve family has a covariant acceleration at `t` if the scalar test
identity has a tangent-fibre witness. -/
def HasCovariantAccelerationAt
    (cov : CovariantDerivative I E TM) (γ : ℝ → M)
    (V : (s : ℝ) → TM (γ s)) (t : ℝ) (v : TM (γ t)) : Prop :=
  ∃ A : TM (γ t), IsCovariantAccelerationAt cov γ V t v A

/-- The intrinsically defined acceleration.  It is parameterized by its
existence proof because the general library does not yet provide derivatives
of arbitrary bundle-valued curve families.  The uniqueness theorem below
makes the value independent of that proof. -/
noncomputable def covariantAcceleration
    {cov : CovariantDerivative I E TM} {γ : ℝ → M}
    {V : (s : ℝ) → TM (γ s)} {t : ℝ} {v : TM (γ t)}
    (h : HasCovariantAccelerationAt cov γ V t v) : TM (γ t) :=
  Classical.choose h

theorem covariantAcceleration_spec
    {cov : CovariantDerivative I E TM} {γ : ℝ → M}
    {V : (s : ℝ) → TM (γ s)} {t : ℝ} {v : TM (γ t)}
    (h : HasCovariantAccelerationAt cov γ V t v) :
    IsCovariantAccelerationAt cov γ V t v (covariantAcceleration h) :=
  Classical.choose_spec h

theorem covariantAcceleration_eq
    {cov : CovariantDerivative I E TM} {γ : ℝ → M}
    {V : (s : ℝ) → TM (γ s)} {t : ℝ} {v A : TM (γ t)}
    (h : HasCovariantAccelerationAt cov γ V t v)
    (hA : IsCovariantAccelerationAt cov γ V t v A) :
    covariantAcceleration h = A :=
  IsCovariantAccelerationAt.unique (covariantAcceleration_spec h) hA

/-- Coordinate transformation law for a time-dependent frame.  If the
coefficient derivative is `a t` and `v` is the curve velocity, differentiating
the scalar pairing with any test section yields the intrinsic connection
formula. -/
theorem curveScalarDeriv_inner_timeFrameField
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u a : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu : ∀ i, HasDerivAt (fun s ↦ b.repr (u s) i) (b.repr (a t) i) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent)
    (W : (x : M) → TM x) (hW : MDiffAt (T% W) (γ t)) :
    curveScalarDeriv (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (W (γ s))) t =
      inner ℝ
        (IntrinsicAcceleration.frameField (I := I) (M := M) b S (a t) (γ t) +
          cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t))
            (γ t) v)
        (W (γ t)) +
      inner ℝ (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t) (γ t))
        (cov W (γ t) v) := by
  classical
  have hc : ∀ i, MDiffAt (fun s ↦ b.repr (u s) i) t := by
    intro i
    exact (hu i).differentiableAt.mdifferentiableAt
  have hg : ∀ i, MDiffAt (fun y ↦ inner ℝ (S i y) (W y)) (γ t) := by
    intro i
    exact CovariantDerivative.mdiffAt_inner_sections (hS i) hW
  have hq : ∀ i, MDiffAt (fun s ↦ inner ℝ (S i (γ s)) (W (γ s))) t := by
    intro i
    exact (hg i).comp t hγ.mdifferentiableAt
  have hscalar : (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (W (γ s))) =
      fun s ↦ ∑ i, (b.repr (u s) i) * inner ℝ (S i (γ s)) (W (γ s)) := by
    funext s
    unfold IntrinsicAcceleration.timeFrameField
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left]
  rw [hscalar]
  let f : IntrinsicAcceleration.FrameIndex E → ℝ → ℝ := fun i s ↦
    (b.repr (u s) i) * inner ℝ (S i (γ s)) (W (γ s))
  have hf : ∀ i, MDiffAt (f i) t := by
    intro i
    exact (hc i).mul (hq i)
  have hcoeff : ∀ i, curveScalarDeriv (fun s ↦ b.repr (u s) i) t =
      b.repr (a t) i := by
    intro i
    exact curveScalarDeriv_eq_of_hasDerivAt (hu i)
  have hinter : ∀ i, curveScalarDeriv
      (fun s ↦ inner ℝ (S i (γ s)) (W (γ s))) t =
      (mvfderiv (I := I) (fun y ↦ inner ℝ (S i y) (W y)) (γ t)) v := by
    intro i
    exact curveScalarDeriv_comp hγ (hg i)
  have hmetric' : ∀ i,
      (mvfderiv (I := I) (fun y ↦ inner ℝ (S i y) (W y)) (γ t)) v =
        inner ℝ (cov (S i) (γ t) v) (W (γ t)) +
          inner ℝ (S i (γ t)) (cov W (γ t) v) := by
    intro i
    exact hmetric (hS i) hW v
  change curveScalarDeriv (fun s ↦ ∑ i, f i s) t = _
  rw [curveScalarDeriv_sum Finset.univ f (fun i _ ↦ hf i)]
  have hsum : ∑ i, curveScalarDeriv (f i) t =
      ∑ i, ((b.repr (u t) i) *
        (inner ℝ (cov (S i) (γ t) v) (W (γ t)) +
          inner ℝ (S i (γ t)) (cov W (γ t) v)) +
        inner ℝ (S i (γ t)) (W (γ t)) * (b.repr (a t) i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f]
    change curveScalarDeriv
      ((fun s ↦ b.repr (u s) i) *
        fun s ↦ inner ℝ (S i (γ s)) (W (γ s))) t = _
    rw [curveScalarDeriv_mul (hc i) (hq i), hcoeff i, hinter i, hmetric' i]
  rw [hsum]
  rw [inner_add_left]
  rw [IntrinsicAcceleration.cov_frameField_eq_sum (I := I) (M := M)
    cov b S (u t) hS]
  simp only [IntrinsicAcceleration.frameField, sum_apply, smul_apply, sum_inner,
    real_inner_smul_left]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- A time-frame field has differentiable scalar pairings with every
differentiable section.  This is the regularity input required by the
intrinsic scalar-multiple rule, kept separate from any assertion about its
covariant acceleration. -/
theorem mdiffAt_inner_timeFrameField_section
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu : ∀ i, DifferentiableAt ℝ (fun s ↦ b.repr (u s) i) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (W : (x : M) → TM x) (hW : MDiffAt (T% W) (γ t)) :
    MDiffAt (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (W (γ s))) t := by
  classical
  have hcoeff : ∀ i, MDiffAt (fun s ↦ b.repr (u s) i) t := by
    intro i
    exact (hu i).mdifferentiableAt
  have hinner : ∀ i, MDiffAt (fun y ↦ inner ℝ (S i y) (W y)) (γ t) := by
    intro i
    exact CovariantDerivative.mdiffAt_inner_sections (hS i) hW
  have hcurve : ∀ i, MDiffAt
      (fun s ↦ inner ℝ (S i (γ s)) (W (γ s))) t := by
    intro i
    exact (hinner i).comp t hγ.mdifferentiableAt
  have hrewrite : (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (W (γ s))) =
      fun s ↦ ∑ i, (b.repr (u s) i) * inner ℝ (S i (γ s)) (W (γ s)) := by
    funext s
    unfold IntrinsicAcceleration.timeFrameField
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left]
  rw [hrewrite]
  have hsum : MDiffAt
      (∑ i ∈ (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E)),
        fun s ↦ (b.repr (u s) i) * inner ℝ (S i (γ s)) (W (γ s))) t := by
    apply MDifferentiableAt.sum
    intro i hi
    exact (hcoeff i).mul (hcurve i)
  convert hsum using 1
  funext s
  simp

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- The scalar inner product of two time-dependent frame fields is
differentiable whenever their coefficient functions and the underlying curve
are differentiable.  This analytic prerequisite is kept separate from the
product-rule computation below so that a vanishing covariant derivative can
later be promoted to constancy on an interval. -/
theorem mdiffAt_inner_two_timeFrameField
    (b c : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u w : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu : ∀ i, DifferentiableAt ℝ (fun s ↦ b.repr (u s) i) t)
    (hw : ∀ j, DifferentiableAt ℝ (fun s ↦ c.repr (w s) j) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (hT : ∀ j, MDiffAt (T% (T j)) (γ t)) :
    MDiffAt (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w s (γ s))) t := by
  let P : (s : ℝ) → TM (γ s) := fun s ↦
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s)
  let Q : (s : ℝ) → TM (γ s) := fun s ↦
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w s (γ s)
  have hcoeffU : ∀ i, MDiffAt (fun s ↦ b.repr (u s) i) t := by
    intro i
    exact (hu i).mdifferentiableAt
  have hinnerST : ∀ i j, MDiffAt
      (fun s ↦ inner ℝ (S i (γ s)) (T j (γ s))) t := by
    intro i j
    exact (CovariantDerivative.mdiffAt_inner_sections (hS i) (hT j)).comp t
      hγ.mdifferentiableAt
  have hPexpand : ∀ j,
      (fun s ↦ inner ℝ (P s) (T j (γ s))) =
        fun s ↦ ∑ i, (b.repr (u s) i) *
          inner ℝ (S i (γ s)) (T j (γ s)) := by
    intro j
    funext s
    dsimp [P]
    unfold IntrinsicAcceleration.timeFrameField
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left]
  have hPdiff : ∀ j, MDiffAt (fun s ↦ inner ℝ (P s) (T j (γ s))) t := by
    intro j
    rw [hPexpand j]
    have hsum' : MDiffAt
        (∑ i ∈ (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E)),
          fun s ↦ (b.repr (u s) i) *
            inner ℝ (S i (γ s)) (T j (γ s))) t := by
      apply MDifferentiableAt.sum
      intro i hi
      exact (hcoeffU i).mul (hinnerST i j)
    convert hsum' using 1
    funext s
    simp
  have hcoeffW : ∀ j, MDiffAt (fun s ↦ c.repr (w s) j) t := by
    intro j
    exact (hw j).mdifferentiableAt
  have hscalar :
      (fun s ↦ inner ℝ (P s) (Q s)) =
        fun s ↦ ∑ j, (c.repr (w s) j) *
          inner ℝ (P s) (T j (γ s)) := by
    funext s
    dsimp [Q]
    unfold IntrinsicAcceleration.timeFrameField
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_smul_right]
  change MDiffAt (fun s ↦ inner ℝ (P s) (Q s)) t
  rw [hscalar]
  have hsum' : MDiffAt
      (∑ j ∈ (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E)),
        fun s ↦ (c.repr (w s) j) * inner ℝ (P s) (T j (γ s))) t := by
    apply MDifferentiableAt.sum
    intro j hj
    exact (hcoeffW j).mul (hPdiff j)
  convert hsum' using 1
  funext s
  simp

/-- Product rule for the inner product of two independently moving frame
fields.  Unlike `curveScalarDeriv_inner_timeFrameField`, the two fields may
use different smooth frame extensions.  This is the local analytic identity
needed to compare parallel fields that are restarted in overlapping charts. -/
theorem curveScalarDeriv_inner_two_timeFrameField
    (cov : CovariantDerivative I E TM)
    (b c : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u a w d : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu : ∀ i, HasDerivAt (fun s ↦ b.repr (u s) i) (b.repr (a t) i) t)
    (hw : ∀ j, HasDerivAt (fun s ↦ c.repr (w s) j) (c.repr (d t) j) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (hT : ∀ j, MDiffAt (T% (T j)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent) :
    curveScalarDeriv (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w s (γ s))) t =
      inner ℝ
        (IntrinsicAcceleration.frameField (I := I) (M := M) b S (a t) (γ t) +
          cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t))
            (γ t) v)
        (IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t (γ t)) +
      inner ℝ
        (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t (γ t))
        (IntrinsicAcceleration.frameField (I := I) (M := M) c T (d t) (γ t) +
          cov (IntrinsicAcceleration.frameField (I := I) (M := M) c T (w t))
            (γ t) v) := by
  let P : (s : ℝ) → TM (γ s) := fun s ↦
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s)
  let Q : (s : ℝ) → TM (γ s) := fun s ↦
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w s (γ s)
  let A : TM (γ t) :=
    IntrinsicAcceleration.frameField (I := I) (M := M) b S (a t) (γ t) +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t))
        (γ t) v
  have hcoeffU : ∀ i, MDiffAt (fun s ↦ b.repr (u s) i) t := by
    intro i
    exact (hu i).differentiableAt.mdifferentiableAt
  have hinnerST : ∀ i j, MDiffAt
      (fun s ↦ inner ℝ (S i (γ s)) (T j (γ s))) t := by
    intro i j
    exact (CovariantDerivative.mdiffAt_inner_sections (hS i) (hT j)).comp t
      hγ.mdifferentiableAt
  have hPexpand : ∀ j,
      (fun s ↦ inner ℝ (P s) (T j (γ s))) =
        fun s ↦ ∑ i, (b.repr (u s) i) *
          inner ℝ (S i (γ s)) (T j (γ s)) := by
    intro j
    funext s
    dsimp [P]
    unfold IntrinsicAcceleration.timeFrameField
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left]
  have hPdiff : ∀ j, MDiffAt (fun s ↦ inner ℝ (P s) (T j (γ s))) t := by
    intro j
    rw [hPexpand j]
    have hsum' : MDiffAt
        (∑ i ∈ (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E)),
          fun s ↦ (b.repr (u s) i) *
            inner ℝ (S i (γ s)) (T j (γ s))) t := by
      apply MDifferentiableAt.sum
      intro i hi
      exact (hcoeffU i).mul (hinnerST i j)
    convert hsum' using 1
    funext s
    simp
  have hcoeffW : ∀ j, MDiffAt (fun s ↦ c.repr (w s) j) t := by
    intro j
    exact (hw j).differentiableAt.mdifferentiableAt
  have hPderiv : ∀ j,
      curveScalarDeriv (fun s ↦ inner ℝ (P s) (T j (γ s))) t =
        inner ℝ A (T j (γ t)) +
          inner ℝ (P t) (cov (T j) (γ t) v) := by
    intro j
    simpa [P, A, IntrinsicAcceleration.timeFrameField,
      IntrinsicAcceleration.frameField] using
      curveScalarDeriv_inner_timeFrameField (I := I) (M := M)
        cov b S u a γ hγ hu hS hmetric (T j) (hT j)
  have hscalar :
      (fun s ↦ inner ℝ (P s) (Q s)) =
        fun s ↦ ∑ j, (c.repr (w s) j) *
          inner ℝ (P s) (T j (γ s)) := by
    funext s
    dsimp [Q]
    unfold IntrinsicAcceleration.timeFrameField
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_smul_right]
  have hsum :
      curveScalarDeriv (fun s ↦ ∑ j, (c.repr (w s) j) *
          inner ℝ (P s) (T j (γ s))) t =
        ∑ j, ((c.repr (w t) j) *
          (inner ℝ A (T j (γ t)) +
            inner ℝ (P t) (cov (T j) (γ t) v)) +
          inner ℝ (P t) (T j (γ t)) * (c.repr (d t) j)) := by
    rw [curveScalarDeriv_sum (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E))
      (fun j s ↦ (c.repr (w s) j) * inner ℝ (P s) (T j (γ s)))
      (fun j _ ↦ (hcoeffW j).mul (hPdiff j))]
    apply Finset.sum_congr rfl
    intro j hj
    change curveScalarDeriv
      ((fun s ↦ c.repr (w s) j) *
        fun s ↦ inner ℝ (P s) (T j (γ s))) t = _
    rw [curveScalarDeriv_mul (hcoeffW j) (hPdiff j),
      curveScalarDeriv_eq_of_hasDerivAt (hw j), hPderiv j]
  have hQ :
      inner ℝ A (Q t) =
        ∑ j, (c.repr (w t) j) * inner ℝ A (T j (γ t)) := by
    dsimp [Q]
    unfold IntrinsicAcceleration.timeFrameField
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_smul_right]
  have hframeD :
      inner ℝ (P t)
          (IntrinsicAcceleration.frameField (I := I) (M := M) c T (d t) (γ t)) =
        ∑ j, inner ℝ (P t) (T j (γ t)) * (c.repr (d t) j) := by
    unfold IntrinsicAcceleration.frameField
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_smul_right]
    ring
  have hcovD :
      inner ℝ (P t)
          (cov (IntrinsicAcceleration.frameField (I := I) (M := M) c T (w t))
            (γ t) v) =
        ∑ j, (c.repr (w t) j) * inner ℝ (P t) (cov (T j) (γ t) v) := by
    rw [IntrinsicAcceleration.cov_frameField_eq_sum (I := I) (M := M)
      cov c T (w t) hT]
    rw [sum_apply]
    simp only [smul_apply]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_smul_right]
  have hsumexpand :
      (∑ j, ((c.repr (w t) j) *
          (inner ℝ A (T j (γ t)) +
            inner ℝ (P t) (cov (T j) (γ t) v)) +
          inner ℝ (P t) (T j (γ t)) * (c.repr (d t) j))) =
        (∑ j, (c.repr (w t) j) * inner ℝ A (T j (γ t))) +
          (∑ j, inner ℝ (P t) (T j (γ t)) * (c.repr (d t) j)) +
          (∑ j, (c.repr (w t) j) * inner ℝ (P t) (cov (T j) (γ t) v)) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ac_rfl
  change curveScalarDeriv (fun s ↦ inner ℝ (P s) (Q s)) t =
    inner ℝ A (Q t) +
      inner ℝ (P t)
        (IntrinsicAcceleration.frameField (I := I) (M := M) c T (d t) (γ t) +
          cov (IntrinsicAcceleration.frameField (I := I) (M := M) c T (w t))
            (γ t) v)
  rw [hscalar, hsum, hsumexpand, hQ, inner_add_right, hframeD, hcovD]
  ring

/-- If two moving frame fields have zero direct covariant acceleration at a
time, their scalar inner product has zero derivative at that time.  The two
frames may be unrelated, which is the point needed for overlap comparisons. -/
theorem curveScalarDeriv_inner_two_timeFrameField_eq_zero
    (cov : CovariantDerivative I E TM)
    (b c : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u a w d : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu : ∀ i, HasDerivAt (fun s ↦ b.repr (u s) i) (b.repr (a t) i) t)
    (hw : ∀ j, HasDerivAt (fun s ↦ c.repr (w s) j) (c.repr (d t) j) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (hT : ∀ j, MDiffAt (T% (T j)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzeroS : IntrinsicAcceleration.frameField (I := I) (M := M) b S
        (a t) (γ t) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t))
          (γ t) v = 0)
    (hzeroT : IntrinsicAcceleration.frameField (I := I) (M := M) c T
        (d t) (γ t) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) c T (w t))
          (γ t) v = 0) :
    curveScalarDeriv (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w s (γ s))) t = 0 := by
  rw [curveScalarDeriv_inner_two_timeFrameField (I := I) (M := M)
    cov b c S T u a w d γ hγ hu hw hS hT hmetric]
  rw [hzeroS, hzeroT]
  simp

/-- Two frame fields with vanishing covariant acceleration preserve their
mutual inner product on a connected time interval.  The frame extensions may
be different; this is the interval-level comparison principle needed before
parallel data constructed in overlapping charts can be glued. -/
theorem inner_two_timeFrameField_eq_initial_on_Ioo
    (cov : CovariantDerivative I E TM)
    (b c : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u a w d : ℝ → E) (γ : ℝ → M)
    (v : (t : ℝ) → TM (γ t)) {l r t₀ s : ℝ}
    (ht₀ : t₀ ∈ Ioo l r) (hs : s ∈ Ioo l r)
    (hγ : ∀ t ∈ Ioo l r, HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t
      (timeTangentMap (I := I) t (v t)))
    (hu : ∀ t ∈ Ioo l r, ∀ i,
      HasDerivAt (fun z ↦ b.repr (u z) i) (b.repr (a t) i) t)
    (hw : ∀ t ∈ Ioo l r, ∀ j,
      HasDerivAt (fun z ↦ c.repr (w z) j) (c.repr (d t) j) t)
    (hS : ∀ t ∈ Ioo l r, ∀ i, MDiffAt (T% (S i)) (γ t))
    (hT : ∀ t ∈ Ioo l r, ∀ j, MDiffAt (T% (T j)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzeroS : ∀ t ∈ Ioo l r,
      IntrinsicAcceleration.frameField (I := I) (M := M) b S (a t) (γ t) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t))
          (γ t) (v t) = 0)
    (hzeroT : ∀ t ∈ Ioo l r,
      IntrinsicAcceleration.frameField (I := I) (M := M) c T (d t) (γ t) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) c T (w t))
          (γ t) (v t) = 0) :
    inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s))
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w s (γ s)) =
    inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t₀ (γ t₀))
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t₀ (γ t₀)) := by
  let f : ℝ → ℝ := fun t ↦ inner ℝ
    (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t (γ t))
    (IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t (γ t))
  have hf : DifferentiableOn ℝ f (Ioo l r) := by
    intro t ht
    exact (mdiffAt_inner_two_timeFrameField (I := I) (M := M) b c S T u w γ
      (hγ t ht)
      (fun i ↦ (hu t ht i).differentiableAt)
      (fun j ↦ (hw t ht j).differentiableAt)
      (fun i ↦ hS t ht i) (fun j ↦ hT t ht j)).differentiableAt.differentiableWithinAt
  have hfderiv : (Ioo l r).EqOn (deriv f) (fun _ ↦ (0 : ℝ)) := by
    intro t ht
    rw [← curveScalarDeriv_eq_deriv]
    exact curveScalarDeriv_inner_two_timeFrameField_eq_zero (I := I) (M := M)
      cov b c S T u a w d γ (hγ t ht)
      (fun i ↦ hu t ht i) (fun j ↦ hw t ht j)
      (fun i ↦ hS t ht i) (fun j ↦ hT t ht j) hmetric
      (hzeroS t ht) (hzeroT t ht)
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero
    isPreconnected_Ioo hf hfderiv hs ht₀
  simpa [f] using hconst

/-- A zero-acceleration time-frame field is uniquely determined on an interval
by its value at one time, even when the two descriptions use different smooth
frame extensions.  This is the chart-independent local uniqueness theorem
needed to continue parallel fields through a restart. -/
theorem timeFrameField_eq_of_zeroAcceleration_on_Ioo
    (cov : CovariantDerivative I E TM)
    (b c : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u a w d : ℝ → E) (γ : ℝ → M)
    (v : (t : ℝ) → TM (γ t)) {l r t₀ s : ℝ}
    (ht₀ : t₀ ∈ Ioo l r) (hs : s ∈ Ioo l r)
    (hγ : ∀ t ∈ Ioo l r, HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t
      (timeTangentMap (I := I) t (v t)))
    (hu : ∀ t ∈ Ioo l r, ∀ i,
      HasDerivAt (fun z ↦ b.repr (u z) i) (b.repr (a t) i) t)
    (hw : ∀ t ∈ Ioo l r, ∀ j,
      HasDerivAt (fun z ↦ c.repr (w z) j) (c.repr (d t) j) t)
    (hS : ∀ t ∈ Ioo l r, ∀ i, MDiffAt (T% (S i)) (γ t))
    (hT : ∀ t ∈ Ioo l r, ∀ j, MDiffAt (T% (T j)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent)
    (hzeroS : ∀ t ∈ Ioo l r,
      IntrinsicAcceleration.frameField (I := I) (M := M) b S (a t) (γ t) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t))
          (γ t) (v t) = 0)
    (hzeroT : ∀ t ∈ Ioo l r,
      IntrinsicAcceleration.frameField (I := I) (M := M) c T (d t) (γ t) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) c T (w t))
          (γ t) (v t) = 0)
    (hinit : IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t₀ (γ t₀) =
      IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t₀ (γ t₀)) :
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u s (γ s) =
      IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w s (γ s) := by
  let P : (t : ℝ) → TM (γ t) := fun t ↦
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t (γ t)
  let Q : (t : ℝ) → TM (γ t) := fun t ↦
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) c T w t (γ t)
  have hPP : inner ℝ (P s) (P s) = inner ℝ (P t₀) (P t₀) := by
    simpa [P] using inner_two_timeFrameField_eq_initial_on_Ioo
      (I := I) (M := M) cov b b S S u a u a γ v ht₀ hs hγ hu hu hS hS
      hmetric hzeroS hzeroS
  have hPQ : inner ℝ (P s) (Q s) = inner ℝ (P t₀) (Q t₀) := by
    simpa [P, Q] using inner_two_timeFrameField_eq_initial_on_Ioo
      (I := I) (M := M) cov b c S T u a w d γ v ht₀ hs hγ hu hw hS hT
      hmetric hzeroS hzeroT
  have hQQ : inner ℝ (Q s) (Q s) = inner ℝ (Q t₀) (Q t₀) := by
    simpa [Q] using inner_two_timeFrameField_eq_initial_on_Ioo
      (I := I) (M := M) cov c c T T w d w d γ v ht₀ hs hγ hw hw hT hT
      hmetric hzeroT hzeroT
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ (P s - Q s) (P s - Q s) =
        inner ℝ (P s) (P s) - 2 * inner ℝ (P s) (Q s) +
          inner ℝ (Q s) (Q s) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_comm (Q s) (P s)]
      ring
    _ = inner ℝ (P t₀) (P t₀) - 2 * inner ℝ (P t₀) (Q t₀) +
          inner ℝ (Q t₀) (Q t₀) := by rw [hPP, hPQ, hQQ]
    _ = 0 := by
      have hinit' : P t₀ = Q t₀ := by simpa [P, Q] using hinit
      rw [hinit']
      ring

/-- The preceding coordinate formula produces the intrinsic acceleration of
the moving frame field once that field agrees with the curve velocity. -/
theorem isCovariantAccelerationAt_timeFrameField
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u a : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu : ∀ i, HasDerivAt (fun s ↦ b.repr (u s) i) (b.repr (a t) i) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent)
    (hv : v = IntrinsicAcceleration.frameField (I := I) (M := M)
      b S (u t) (γ t)) :
    IsCovariantAccelerationAt cov γ
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M)
        b S u s (γ s)) t v
      (IntrinsicAcceleration.directFrameCovariantAcceleration (I := I) (M := M)
        cov b S (u t) (a t) (γ t)) := by
  intro W hW
  rw [curveScalarDeriv_inner_timeFrameField cov b S u a γ hγ hu hS hmetric W hW]
  rw [IntrinsicAcceleration.directFrameCovariantAcceleration,
    ← IntrinsicAcceleration.cov_frameField_apply_eq_directFrameConnectionTerm
      (I := I) (M := M) cov b S (u t) hS]
  rw [hv]
  rfl

/-- Coordinate transformation law.  Two local frame descriptions of the
same velocity germ produce the same tangent-fibre acceleration.  This is the
chart-independent bridge used when a curve is reexpressed on an overlap. -/
theorem directFrameCovariantAcceleration_eq_of_eventuallyEq
    (cov : CovariantDerivative I E TM)
    (b₁ b₂ : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S T : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u₁ a₁ u₂ a₂ : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu₁ : ∀ i, HasDerivAt (fun s ↦ b₁.repr (u₁ s) i) (b₁.repr (a₁ t) i) t)
    (hu₂ : ∀ i, HasDerivAt (fun s ↦ b₂.repr (u₂ s) i) (b₂.repr (a₂ t) i) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (hT : ∀ i, MDiffAt (T% (T i)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent)
    (hv₁ : v = IntrinsicAcceleration.frameField (I := I) (M := M)
      b₁ S (u₁ t) (γ t))
    (hv₂ : v = IntrinsicAcceleration.frameField (I := I) (M := M)
      b₂ T (u₂ t) (γ t))
    (hV : (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M)
        b₁ S u₁ s (γ s)) =ᶠ[𝓝 t]
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M)
        b₂ T u₂ s (γ s))) :
    IntrinsicAcceleration.directFrameCovariantAcceleration (I := I) (M := M)
        cov b₁ S (u₁ t) (a₁ t) (γ t) =
      IntrinsicAcceleration.directFrameCovariantAcceleration (I := I) (M := M)
        cov b₂ T (u₂ t) (a₂ t) (γ t) := by
  apply IsCovariantAccelerationAt.unique
  · exact (isCovariantAccelerationAt_timeFrameField (I := I) (M := M)
      cov b₁ S u₁ a₁ γ hγ hu₁ hS hmetric hv₁).congr_of_eventuallyEq hV
  · exact isCovariantAccelerationAt_timeFrameField (I := I) (M := M)
      cov b₂ T u₂ a₂ γ hγ hu₂ hT hmetric hv₂

/-- The coordinate-frame map is injective at every point in its chart
source.  This is the fibrewise step that lets a vanishing tangent-valued
acceleration be read back as the ordinary `E`-valued coordinate equation. -/
theorem coordinateFrameLinear_injective_of_mem_source
    (x₀ : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    {y : M} (hy : y ∈ (extChartAt I x₀).source) :
    Function.Injective
      (IntrinsicAcceleration.coordinateFrameLinear (I := I) (M := M) x₀ b y) := by
  intro u v huv
  let e := trivializationAt E TM x₀
  have hybase : y ∈ e.baseSet := by
    change y ∈ (trivializationAt E TM x₀).baseSet
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) x₀]
    rw [← extChartAt_source (I := I) x₀]
    exact hy
  have hmap := congrArg (fun q : TM y => e.continuousLinearMapAt ℝ y q) huv
  have hmap_apply (q : E) :
      e.continuousLinearMapAt ℝ y
        (IntrinsicAcceleration.coordinateFrameLinear (I := I) (M := M) x₀ b y q) = q := by
    change e.continuousLinearMapAt ℝ y
      (∑ i, (b.repr q i) • e.localFrame b i y) = q
    rw [map_sum]
    have hframe : ∀ i, e.continuousLinearMapAt ℝ y (e.localFrame b i y) = b i := by
      intro i
      rw [e.localFrame_apply_of_mem_baseSet b hybase]
      change e.continuousLinearMapAt ℝ y
        ((e.linearEquivAt ℝ y hybase).symm (b i)) = b i
      rw [e.continuousLinearMapAt_apply_of_mem ℝ hybase]
      exact (e.linearEquivAt ℝ y hybase).apply_symm_apply (b i)
    simp only [map_smul, hframe]
    exact b.sum_repr q
  rw [hmap_apply u, hmap_apply v] at hmap
  exact hmap

/-- Intrinsic zero covariant acceleration implies the coordinate geodesic
equation in any overlapping extended chart.  The hypotheses record the
actual chart-frame description of the curve velocity, so this theorem is the
coordinate transformation bridge used for gluing, not a claim tied to the
chart used to construct the curve. -/
theorem coordinateCovariantAcceleration_eq_zero_of_intrinsic_zero
    (cov : CovariantDerivative I E TM)
    (x₀ : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (u a : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t
      (timeTangentMap (I := I) t v))
    (hu : ∀ i, HasDerivAt (fun s ↦ b.repr (u s) i) (b.repr (a t) i) t)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hmem : γ t ∈ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) x₀ b)
    (hv : v = IntrinsicAcceleration.frameField (I := I) (M := M) b
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
      (u t) (γ t))
    (hzero : IsCovariantAccelerationAt cov γ
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        u s (γ s)) t v 0) :
    LocalGeodesicData.coordinateCovariantAcceleration (I := I) (M := M)
      cov x₀ b (extChartAt I x₀ (γ t)) (u t) (a t) = 0 := by
  have hS : ∀ i, MDiffAt (T% (LocalGeodesicData.smoothFrame
      (I := I) (M := M) (E := E) x₀ b i)) (γ t) := by
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M) x₀ b i _
  have hdirect := isCovariantAccelerationAt_timeFrameField
    (I := I) (M := M) cov b
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
    u a γ hγ hu hS hmetric hv
  have hdirectzero :
      IntrinsicAcceleration.directFrameCovariantAcceleration (I := I) (M := M)
        cov b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        (u t) (a t) (γ t) = 0 :=
    IsCovariantAccelerationAt.unique hdirect hzero
  have hvector :
      IntrinsicAcceleration.coordinateCovariantAccelerationVector (I := I) (M := M)
        cov x₀ b (extChartAt I x₀ (γ t)) (u t) (a t) = 0 := by
    rw [IntrinsicAcceleration.coordinateCovariantAccelerationVector_eq_directFrameCovariantAcceleration_of_mem_agreement
      (I := I) (M := M) cov x₀ b hmem]
    exact hdirectzero
  change IntrinsicAcceleration.coordinateFrameLinear (I := I) (M := M) x₀ b
      ((extChartAt I x₀).symm (extChartAt I x₀ (γ t)))
      (LocalGeodesicData.coordinateCovariantAcceleration (I := I) (M := M)
        cov x₀ b (extChartAt I x₀ (γ t)) (u t) (a t)) = 0 at hvector
  rw [(extChartAt I x₀).left_inv hmem.1] at hvector
  apply coordinateFrameLinear_injective_of_mem_source (I := I) (M := M) x₀ b hmem.1
  simpa [IntrinsicAcceleration.coordinateFrameVector,
    LocalGeodesicData.coordinateFrameCombination] using hvector

/-- On the neighbourhood where the canonical smooth frame agrees with the
coordinate frame, frame coefficients represent the same tangent vector as the
coordinate construction. -/
theorem frameField_eq_coordinateFrameCombination_of_mem_agreement
    (x₀ : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (u : E) {y : M}
    (hy : y ∈ IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) x₀ b) :
    IntrinsicAcceleration.frameField (I := I) (M := M) b
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
      u y =
    LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y := by
  unfold IntrinsicAcceleration.frameField LocalGeodesicData.coordinateFrameCombination
  apply Finset.sum_congr rfl
  intro i hi
  change (b.repr u i) •
      LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i y = _
  rw [hy.2 i]

/-- The curve constructed from the coordinate geodesic equation has zero
intrinsic covariant acceleration on a neighbourhood of its initial time.
This turns the coordinate ODE certificate into the actual equation
`∇_{γ̇} γ̇ = 0`, expressed through the chart-free scalar characterization. -/
theorem local_solution_eventually_isCovariantAccelerationAt_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E) {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := x₀) (b := b) sol)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve sol)
        (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) b
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
          sol.velocity s (LocalChartSecondOrderSolution.curve sol s))
        t
        (IntrinsicAcceleration.frameField (I := I) (M := M) b
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
          (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
        0 := by
  have hinterval : Ioo (-sol.radius) sol.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [sol.radius_pos])
      (by linarith [sol.radius_pos])
  filter_upwards [hinterval,
    IntrinsicAcceleration.local_solution_eventually_mem_smoothFrameAgreementSet
      (I := I) (M := M) (E := E) (H := H) x₀ b sol,
    IntrinsicAcceleration.local_solution_eventually_directFrameCovariantAcceleration_eq_zero
      (I := I) (M := M) cov x₀ b sol hsol] with t ht hmem hzero
  have hfield :
      IntrinsicAcceleration.frameField (I := I) (M := M) b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t) :=
    frameField_eq_coordinateFrameCombination_of_mem_agreement
      (I := I) (M := M) x₀ b (sol.velocity t) hmem
  have hraw := LocalGeodesicData.curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol ht
  have hcurve : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve sol) t
      (timeTangentMap (I := I) t
        (IntrinsicAcceleration.frameField (I := I) (M := M) b
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
          (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))) := by
    rw [timeTangentMap_eq_toSpanSingleton, hfield]
    exact hraw
  have hvelocity : HasDerivAt sol.velocity (deriv sol.velocity t) t := by
    rw [(sol.velocity_hasDeriv t ht).deriv]
    exact sol.velocity_hasDeriv t ht
  have hcoeff : ∀ i, HasDerivAt (fun s ↦ b.repr (sol.velocity s) i)
      (b.repr (deriv sol.velocity t) i) t := by
    intro i
    have hc : HasDerivAt (fun _ : ℝ ↦ (b.coord i).toContinuousLinearMap) 0 t :=
      hasDerivAt_const t (b.coord i).toContinuousLinearMap
    simpa using hc.clm_apply hvelocity
  have hS : ∀ i, MDiffAt (T% (LocalGeodesicData.smoothFrame
      (I := I) (M := M) (E := E) x₀ b i))
      (LocalChartSecondOrderSolution.curve sol t) := by
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M) x₀ b i _
  have hacc := isCovariantAccelerationAt_timeFrameField
    (I := I) (M := M) cov b
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
    sol.velocity (fun s ↦ deriv sol.velocity s)
    (LocalChartSecondOrderSolution.curve sol) hcurve hcoeff hS hmetric rfl
  rw [hzero] at hacc
  exact hacc

/-- The canonical smooth-frame representative of the velocity of a packaged
local geodesic.  It is a genuine tangent-vector family along the manifold
curve and agrees pointwise with the coordinate velocity on the local frame
agreement neighbourhood. -/
def canonicalFrameVelocity
    {cov : CovariantDerivative I E TM} {x₀ : M} {v₀ : TM x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) : TM (IntrinsicGeodesic.LocalGeodesic.curve γ t) :=
  IntrinsicAcceleration.timeFrameField (I := I) (M := M)
    (IntrinsicGeodesic.canonicalBasis (E := E))
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
      (IntrinsicGeodesic.canonicalBasis (E := E)) i)
    γ.solution.velocity t (IntrinsicGeodesic.LocalGeodesic.curve γ t)

/-- The local geodesic produced by the coordinate existence theorem satisfies
the intrinsic zero-acceleration equation. -/
theorem localGeodesic_eventually_isCovariantAccelerationAt_zero
    {cov : CovariantDerivative I E TM} {x₀ : M} {v₀ : TM x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IsCovariantAccelerationAt cov (IntrinsicGeodesic.LocalGeodesic.curve γ)
        (canonicalFrameVelocity γ) t
        (IntrinsicAcceleration.frameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
            (IntrinsicGeodesic.canonicalBasis (E := E)) i)
          (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t)) 0 := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hraw := local_solution_eventually_isCovariantAccelerationAt_zero
    (I := I) (M := M) cov x₀ b γ.solution γ.isGeodesic hmetric
  change ∀ᶠ t in 𝓝 (0 : ℝ),
    IsCovariantAccelerationAt cov (LocalChartSecondOrderSolution.curve γ.solution)
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
          (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        γ.solution.velocity s (LocalChartSecondOrderSolution.curve γ.solution s))
      t
      (IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
          (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t)) 0
  exact hraw

/-- On a neighborhood of the initial time, the smooth-frame velocity is the
velocity carried by the local-geodesic wrapper. -/
theorem localGeodesic_eventually_canonicalFrameVelocity_eq_velocity
    {cov : CovariantDerivative I E TM} {x₀ : M} {v₀ : TM x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      canonicalFrameVelocity γ t = IntrinsicGeodesic.LocalGeodesic.velocity γ t := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hinterval : Ioo (-γ.solution.radius) γ.solution.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
      (by linarith [γ.solution.radius_pos])
  filter_upwards [hinterval,
    IntrinsicAcceleration.local_solution_eventually_mem_smoothFrameAgreementSet
      (I := I) (M := M) (E := E) (H := H) x₀ b γ.solution] with t ht hmem
  have hfield :
      IntrinsicAcceleration.frameField (I := I) (M := M) b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t) :=
    frameField_eq_coordinateFrameCombination_of_mem_agreement
      (I := I) (M := M) x₀ b (γ.solution.velocity t) hmem
  change IntrinsicAcceleration.frameField (I := I) (M := M) b
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
    (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t) = _
  rw [IntrinsicGeodesic.LocalGeodesic.velocity,
    LocalGeodesicData.tangentField_eq_coordinateFrameCombination
      (I := I) (M := M) (E := E) (H := H) cov x₀ b γ.solution
      γ.solution.velocity ht]
  exact hfield

/-- The smooth-frame family is the actual derivative of the packaged local
geodesic curve throughout a neighborhood of its initial time. -/
theorem localGeodesic_eventually_hasMFDerivAt_curve_canonicalFrameVelocity
    {cov : CovariantDerivative I E TM} {x₀ : M} {v₀ : TM x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasMFDerivAt (𝓘(ℝ, ℝ)) I (IntrinsicGeodesic.LocalGeodesic.curve γ) t
        (timeTangentMap (I := I) t (canonicalFrameVelocity γ t)) := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hinterval : Ioo (-γ.solution.radius) γ.solution.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
      (by linarith [γ.solution.radius_pos])
  filter_upwards [hinterval,
    IntrinsicAcceleration.local_solution_eventually_mem_smoothFrameAgreementSet
      (I := I) (M := M) (E := E) (H := H) x₀ b γ.solution] with t ht hmem
  have hfield :
      IntrinsicAcceleration.frameField (I := I) (M := M) b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t) :=
    frameField_eq_coordinateFrameCombination_of_mem_agreement
      (I := I) (M := M) x₀ b (γ.solution.velocity t) hmem
  have hraw := LocalGeodesicData.curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov x₀ b γ.solution ht
  change HasMFDerivAt (𝓘(ℝ, ℝ)) I (LocalChartSecondOrderSolution.curve γ.solution) t
    (timeTangentMap (I := I) t
      (IntrinsicAcceleration.frameField (I := I) (M := M) b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t)))
  rw [timeTangentMap_eq_toSpanSingleton, hfield]
  exact hraw

end CurveConnection

end BonnetMyersEntry
