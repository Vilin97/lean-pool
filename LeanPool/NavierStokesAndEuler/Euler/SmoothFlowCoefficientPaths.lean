/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowGevrey
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathTimeJets
import Mathlib.Analysis.Calculus.MeanValue
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJacobian
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.Euler.SeparatingTimeDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The actual flow displacement and material velocity, with every spatial
jet in the uniform continuous-time bounded-field space. -/

section

/-! Genuine joint time-space regularity of the constructed flow and its
inverse. Interior C² uses only the actual first time derivative of the
velocity coefficient, together with its existing smooth spatial jets. -/

section

/-! Joint time-space differentiability of a genuine smooth family of
continuous paths, and the actual mixed derivative of its spatial Jacobian. -/

@[expose] public section

noncomputable section

open scoped ContDiff Topology

namespace EulerSmoothPathJoint

open Set Filter EulerVolterraConvolution EulerSmoothPathTimeJets

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T, V))

/-- Time slice, given by `extendPath T hT (f x) t`. -/
def timeSlice (t : ℝ) (x : E) : V := extendPath T hT (f x) t

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem timeSlice_joint_continuous (hf : Continuous f) :
    Continuous (Function.uncurry (timeSlice T hT f)) := by
  unfold timeSlice extendPath
  fun_prop

/-- Spatial derivative as an element of `C(Icc (0 : ℝ) T,E →L[ℝ] V)`. -/
def spatialDerivative (x : E) : C(Icc (0 : ℝ) T,E →L[ℝ] V) :=
  ((continuousMultilinearCurryFin1 ℝ E
      V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
    ℝ (Icc (0 : ℝ) T)) (jetFamily T f 1 x)

theorem spatialDerivative_contDiff (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spatialDerivative T f) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,E [×1]→L[ℝ] V)) (F := C(Icc (0 : ℝ) T,E →L[ℝ] V))
    ((continuousMultilinearCurryFin1 ℝ E
        V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
      ℝ (Icc (0 : ℝ) T))).comp (jetFamily_contDiff T f hf 1)

theorem spatialDerivative_apply (hf : ContDiff ℝ ∞ f) (x : E) (t : Icc (0 : ℝ) T) :
    spatialDerivative T f x t = fderiv ℝ (fun y => f y t) x := by
  change continuousMultilinearCurryFin1 ℝ E V (jetFamily T f 1 x t) = _
  rw [jetFamily_apply T f hf]
  apply ContinuousLinearMap.ext
  intro v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp

theorem timeSlice_hasFDerivAt (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    HasFDerivAt (timeSlice T hT f t) (spatialDerivative T f x (projIcc 0 T hT t)) x := by
  rw [spatialDerivative_apply T f hf]
  exact (((ContinuousMap.evalCLM ℝ (projIcc 0 T hT t)).contDiff.comp hf).differentiable
    (by simp) x).hasFDerivAt

/-- Joint derivative, given by `(ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q t
x)).coprod (timeSlice T hT (spatialDerivative T f) t x)`. -/
def jointDerivative (t : ℝ) (x : E) : (ℝ × E) →L[ℝ] V :=
  (ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q t x)).coprod
    (timeSlice T hT (spatialDerivative T f) t x)

theorem jointDerivative_continuous (hf : ContDiff ℝ ∞ f) (hq : Continuous q) :
    Continuous (Function.uncurry (jointDerivative T hT f q)) := by
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
    (timeSlice_joint_continuous T hT q hq)).continuousLinearMapCoprod
      (timeSlice_joint_continuous T hT (spatialDerivative T f)
        (spatialDerivative_contDiff T f hf).continuous)

variable (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)

include hf hq hd in
theorem joint_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (Function.uncurry (timeSlice T hT f)) (jointDerivative T hT f q t x) (t,x) := by
  have hloc : ∀ᶠ p : ℝ × E in 𝓝 (t,x), p.1 ∈ Ioo 0 T :=
    (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := timeSlice T hT f) (u := (t,x))
    (f₁ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q s y))
    (f₂ := timeSlice T hT (spatialDerivative T f))
  · filter_upwards [hloc] with p hp
    change HasFDerivAt (fun s => timeSlice T hT f s p.2)
      (ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q p.1 p.2)) p.1
    have hh := (hd p.2 ⟨p.1,hp.1.le,hp.2.le⟩).hasDerivAt (Icc_mem_nhds hp.1 hp.2)
    have he : timeSlice T hT q p.1 p.2 = q p.2 ⟨p.1,hp.1.le,hp.2.le⟩ := by
      simp only [timeSlice, extendPath, projIcc_of_mem hT ⟨hp.1.le,hp.2.le⟩]
    rw [he]
    exact hh.hasFDerivAt
  · apply Eventually.of_forall
    intro p
    exact timeSlice_hasFDerivAt T hT f hf p.1 p.2
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
      (timeSlice_joint_continuous T hT q hq.continuous)).continuousAt
  · exact (timeSlice_joint_continuous T hT (spatialDerivative T f)
      (spatialDerivative_contDiff T f hf).continuous).continuousAt

include hf hq hd in
theorem joint_contDiffAt_one (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (timeSlice T hT f)) (t,x) := by
  rw [contDiffAt_one_iff]
  refine ⟨Function.uncurry (jointDerivative T hT f q), {p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_,
    (jointDerivative_continuous T hT f q hf hq.continuous).continuousOn, ?_⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact joint_hasFDerivAt T hT f q hf hq hd p.1 hp p.2

include hf hq hd in
theorem spatialDerivative_time (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (spatialDerivative T f x))
      (spatialDerivative T q x t) (Icc (0 : ℝ) T) t := by
  have h := (continuousMultilinearCurryFin1 ℝ E
      V).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) (jetFamily_hasDerivWithinAt T hT f q hf hq hd 1 x t)
  exact h

end EulerSmoothPathJoint

end
end

end

section

/-! The actual acceleration of the constructed nonlinear flow is the
material derivative of its velocity, including the one-sided endpoint
identities. All coefficient time derivatives are literal hypotheses. -/

@[expose] public section

noncomputable section

open scoped ContDiff Topology

namespace EulerSmoothBanachFlow

open Set Filter EulerVolterraConvolution EulerContinuousTimeIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)

/-- Acceleration family, given by `A₁.superposition (pathFamily T hT A x) + multiplier
(A.derivative.superposition (pathFamily T hT A x)) (velocityFamily T hT A x)`. -/
def accelerationFamily (x : E) : C(Icc (0 : ℝ) T,E) :=
  A₁.superposition (pathFamily T hT A x) +
    multiplier (A.derivative.superposition (pathFamily T hT A x)) (velocityFamily T hT A x)

theorem accelerationFamily_apply (x : E) (t : Icc (0 : ℝ) T) :
    accelerationFamily T hT A A₁ x t =
      A₁.field t ((flowData T hT A).forward t x) +
        fderiv ℝ (A.field t : E → E) ((flowData T hT A).forward t x)
          (A.field t ((flowData T hT A).forward t x)) := by
  change A₁.field t ((flowData T hT A).forward t x) +
    A.derivativeField t ((flowData T hT A).forward t x)
      (A.field t ((flowData T hT A).forward t x)) = _
  rw [A.derivativeField_eq]

theorem pathFamily_time_derivative (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (pathFamily T hT A x))
      (velocityFamily T hT A x t) (Icc (0 : ℝ) T) t := by
  apply (pathFamily_hasDerivWithinAt T hT A x t).congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs, pathFamily_apply]

theorem velocityFamily_time_derivative_interior
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT (velocityFamily T hT A x))
      (accelerationFamily T hT A A₁ x ⟨t,ht.1.le,ht.2.le⟩) t := by
  have hf := (pathFamily_time_derivative T hT A x ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  have hd := SmoothTimeField.realField_hasFDerivAt T hT A A₁ htime t ht
    (extendPath T hT (pathFamily T hT A x) t)
  have h := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hf)
  convert h using 1
  · rfl
  · simp only [SmoothTimeField.jointDerivative, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    simp only [SmoothTimeField.realField, extendPath,
      projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩]
    rfl

theorem velocityFamily_time_derivative
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (velocityFamily T hT A x))
      (accelerationFamily T hT A A₁ x t) (Icc (0 : ℝ) T) t := by
  apply EulerSeparatingTimeDerivative.hasDerivWithinAt T hT
    (velocityFamily T hT A x) (accelerationFamily T hT A A₁ x)
    (fun _ : Unit => ContinuousLinearMap.id ℝ E)
  · intro u v h
    exact congrFun h ()
  · intro _ s hs
    exact velocityFamily_time_derivative_interior T hT A A₁ htime x s hs

theorem forward_second_time_derivative
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => deriv (fun r => (flowData T hT A).forward r x) s)
      (accelerationFamily T hT A A₁ x t) (Icc (0 : ℝ) T) t := by
  apply (velocityFamily_time_derivative T hT A A₁ htime x t).congr_of_mem _ t.property
  intro s hs
  rw [((flowData T hT A).forward_hasDerivAt s x).deriv]
  change (flowData T hT A).velocity s ((flowData T hT A).forward s x) =
    velocityFamily T hT A x (projIcc 0 T hT s)
  rw [projIcc_of_mem hT hs]
  exact EulerBoundedLipschitzFlow.ofTimeInterval_velocity T hT A.field
    ‖A.derivative.field‖₊ (velocity_lipschitz T A) ⟨s,hs⟩ _

end EulerSmoothBanachFlow

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff Topology

namespace EulerSmoothBanachFlow

open Set Filter EulerVolterraConvolution EulerContinuousTimeIntegral
  EulerSmoothPathJoint EulerContinuousPathCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)

theorem accelerationFamily_contDiff : ContDiff ℝ ∞ (accelerationFamily T hT A A₁) := by
  have hp := pathFamily_contDiff T hT A
  exact (A₁.superposition_contDiff.comp hp).add
    (contDiff_apply _ _ (A.derivative.superposition_contDiff.comp hp)
      (velocityFamily_contDiff T hT A))

theorem forward_joint_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (Function.uncurry (flowData T hT A).forward)
      (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x) (t,x) := by
  have h := joint_hasFDerivAt T hT (pathFamily T hT A) (velocityFamily T hT A)
    (pathFamily_contDiff T hT A) (velocityFamily_contDiff T hT A)
    (pathFamily_time_derivative T hT A) t ht x
  apply h.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)] with p hp
  change (flowData T hT A).forward p.1 p.2 =
    extendPath T hT (pathFamily T hT A p.2) p.1
  simp only [extendPath, projIcc_of_mem hT ⟨hp.1.le,hp.2.le⟩, pathFamily_apply]

theorem forward_joint_contDiffAt_one (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (flowData T hT A).forward) (t,x) := by
  rw [contDiffAt_one_iff]
  refine ⟨Function.uncurry (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A)),
    {p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_,
    (jointDerivative_continuous T hT _ _ (pathFamily_contDiff T hT A)
      (velocityFamily_contDiff T hT A).continuous).continuousOn, ?_⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact forward_joint_hasFDerivAt T hT A p.1 hp p.2

theorem forward_jointDerivative_contDiffAt_one
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1
      (Function.uncurry (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A))) (t,x)
          := by
  have hq := joint_contDiffAt_one T hT (velocityFamily T hT A) (accelerationFamily T hT A A₁)
    (velocityFamily_contDiff T hT A) (accelerationFamily_contDiff T hT A A₁)
    (velocityFamily_time_derivative T hT A A₁ htime) t ht x
  have hJ := joint_contDiffAt_one T hT (spatialDerivative T (pathFamily T hT A))
    (spatialDerivative T (velocityFamily T hT A))
    (spatialDerivative_contDiff T _ (pathFamily_contDiff T hT A))
    (spatialDerivative_contDiff T _ (velocityFamily_contDiff T hT A))
    (spatialDerivative_time T hT _ _ (pathFamily_contDiff T hT A)
      (velocityFamily_contDiff T hT A) (pathFamily_time_derivative T hT A)) t ht x
  have hs := (ContinuousLinearMap.toSpanSingletonLIE ℝ
      E).toContinuousLinearEquiv.contDiff.contDiffAt.comp
    (t,x) hq
  let L : ((ℝ →L[ℝ] E) × (E →L[ℝ] E)) →L[ℝ] ((ℝ × E) →L[ℝ] E) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := E) (G := E) ℝ).toContinuousLinearMap
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
    (E := (ℝ →L[ℝ] E) × (E →L[ℝ] E)) (F := (ℝ × E) →L[ℝ] E) L).contDiffAt.comp
    (t,x) (hs.prodMk hJ)

theorem forward_joint_contDiffAt_two
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (Function.uncurry (flowData T hT A).forward) (t,x) := by
  rw [show (2 : ℕ∞ω) = ((1 : ℕ) + 1) from rfl, contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨Function.uncurry (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A)),
    ⟨{p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_, ?_⟩,
    forward_jointDerivative_contDiffAt_one T hT A A₁ htime t ht x⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact forward_joint_hasFDerivAt T hT A p.1 hp p.2

omit [FiniteDimensional ℝ E] in
/-- Time lift equiv, constructed using `ContinuousLinearEquiv.equivOfInverse`. -/
def timeLiftEquiv (J : E ≃L[ℝ] E) (v : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ ℝ E).prod
      (((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ E)) +
        J.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ E)))
    ((ContinuousLinearMap.fst ℝ ℝ E).prod
      (J.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.snd ℝ ℝ E) -
          (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ E))))
    (by intro p; ext <;> simp)
    (by intro p; ext <;> simp)

/-- Lift forward, given by `(p.1, (flowData T hT A).forward p.1 p.2)`. -/
def liftForward (p : ℝ × E) : ℝ × E := (p.1, (flowData T hT A).forward p.1 p.2)
/-- Lift backward, given by `(p.1, (flowData T hT A).backward p.1 p.2)`. -/
def liftBackward (p : ℝ × E) : ℝ × E := (p.1, (flowData T hT A).backward p.1 p.2)

theorem liftForward_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (liftForward T hT A)
      (timeLiftEquiv (jacobianEquiv T hT A ⟨t,ht.1.le,ht.2.le⟩ x)
        (velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩)).toContinuousLinearMap (t,x) := by
  have h : HasFDerivAt (liftForward T hT A)
      ((ContinuousLinearMap.fst ℝ ℝ E).prod
        (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x)) (t,x) :=
    hasFDerivAt_fst.prodMk (forward_joint_hasFDerivAt T hT A t ht x)
  have he : (timeLiftEquiv (jacobianEquiv T hT A ⟨t,ht.1.le,ht.2.le⟩ x)
      (velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩)).toContinuousLinearMap =
      (ContinuousLinearMap.fst ℝ ℝ E).prod
        (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x) := by
    apply ContinuousLinearMap.ext
    intro p
    ext
    · rfl
    · change p.1 • velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩ +
        (jacobianEvolution T hT A x).forward ⟨t,ht.1.le,ht.2.le⟩ p.2 =
        (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x) p
      simp only [jointDerivative, timeSlice, extendPath,
        projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩, ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      rw [spatialDerivative_apply T _ (pathFamily_contDiff T hT A)]
      change _ = p.1 • velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩ +
        fderiv ℝ (fun y => (flowData T hT A).forward t y) x p.2
      rw [forward_fderiv T hT A ⟨t,ht.1.le,ht.2.le⟩ x]
  rw [he]
  exact h

theorem liftBackward_contDiffAt_two
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (liftBackward T hT A) (t,x) := by
  let y := (flowData T hT A).backward t x
  have hg : ContDiffAt ℝ 2 (liftForward T hT A) (t,y) :=
    contDiffAt_fst.prodMk (forward_joint_contDiffAt_two T hT A A₁ htime t ht y)
  apply EulerSmoothImplicitLift.contDiffAt_of_identity
    (liftBackward T hT A) (liftForward T hT A) id (t,x) 2 (by norm_num)
    ((continuous_fst.prodMk (flowData T hT A).backward_joint_continuous).continuousAt)
    hg contDiff_id.contDiffAt
    (timeLiftEquiv (jacobianEquiv T hT A ⟨t,ht.1.le,ht.2.le⟩ y)
      (velocityFamily T hT A y ⟨t,ht.1.le,ht.2.le⟩))
  · exact liftForward_hasFDerivAt T hT A t ht y
  · intro p
    ext
    · rfl
    · exact (flowData T hT A).forward_backward p.1 p.2

theorem backward_joint_contDiffAt_two
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (Function.uncurry (flowData T hT A).backward) (t,x) :=
  (liftBackward_contDiffAt_two T hT A A₁ htime t ht x).snd

end EulerSmoothBanachFlow

end
end

end

section

/-! Constructing literal bounded smooth coefficient paths from an actual
smooth path family and uniform bounds on its differentiated evolution. -/

section

/-! Uniform bounds on a genuine time derivative turn a continuous family
of paths into a continuous path of bounded fields. -/

@[expose] public section

noncomputable section

open scoped BoundedContinuousFunction

namespace EulerBoundedPathFamily

open Set EulerVolterraConvolution

variable {X V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : X → C(Icc (0 : ℝ) T, V))
  (hf : Continuous f) (C D : ℝ)
  (hC : ∀ t x, ‖f x t‖ ≤ C)
  (hD : 0 ≤ D) (hq : ∀ t x, ‖q x t‖ ≤ D)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)

/-- Bounded slice, given by `BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x t)
((ContinuousMap.evalCLM ℝ t).continuous.comp hf) C (hC t)`. -/
def boundedSlice (t : Icc (0 : ℝ) T) : X →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x t)
    ((ContinuousMap.evalCLM ℝ t).continuous.comp hf) C (hC t)

include hq hd in
theorem boundedSlice_lipschitz :
    LipschitzWith ⟨D,hD⟩ (boundedSlice T f hf C hC) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hD dist_nonneg)).2
  intro x
  change ‖f x s - f x t‖ ≤ D * dist s t
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := extendPath T hT (f x)) (f' := extendPath T hT (q x)) (C := D)
    (fun r hr => by simpa only [extendPath, projIcc_of_mem hT hr] using hd x ⟨r,hr⟩)
    (fun r hr => by simpa only [extendPath, projIcc_of_mem hT hr] using hq ⟨r,hr⟩ x)
    (convex_Icc (0 : ℝ) T) t.property s.property
  simpa only [extendPath,
    projIcc_of_mem hT t.property, projIcc_of_mem hT s.property,
    dist_eq_norm, Subtype.dist_eq] using h

/-- Bounded path, bundling `toFun`, `continuous_toFun`. -/
def boundedPath : C(Icc (0 : ℝ) T,X →ᵇ V) where
  toFun := boundedSlice T f hf C hC
  continuous_toFun := (boundedSlice_lipschitz T hT f q hf C D hC hD hq hd).continuous

@[simp] theorem boundedPath_apply (t : Icc (0 : ℝ) T) (x : X) :
    boundedPath T hT f q hf C D hC hD hq hd t x = f x t := rfl

theorem boundedPath_norm (hCnonneg : 0 ≤ C) :
    ‖boundedPath T hT f q hf C D hC hD hq hd‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hCnonneg).2
  intro t
  exact (BoundedContinuousFunction.norm_le hCnonneg).2 (hC t)

end EulerBoundedPathFamily

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace SmoothTimeField

open Set EulerSmoothPathTimeJets EulerBoundedPathFamily EulerVolterraConvolution

variable {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T, V))
  (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)
  (C D : ℕ → ℝ)
  (hC : ∀ n t x, ‖iteratedFDeriv ℝ n (fun y => f y t) x‖ ≤ C n)
  (hD : ∀ n t x, ‖iteratedFDeriv ℝ n (fun y => q y t) x‖ ≤ D n)

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldFromPaths1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldFromPaths2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldFromPaths3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldFromPaths4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
include hC in
theorem value_bound (t : Icc (0 : ℝ) T) (x : E) : ‖f x t‖ ≤ C 0 := by
  simpa only [norm_iteratedFDeriv_zero] using hC 0 t x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
include hT hD in
theorem derivativeBound_nonneg (n : ℕ) : 0 ≤ D n :=
  (norm_nonneg _).trans (hD n ⟨0,le_rfl,hT⟩ 0)

/-- Of path family, bundling `field`, `smooth`, `change`, `jet` and the required compatibility
proofs. -/
def ofPathFamily : SmoothTimeField (Icc (0 : ℝ) T) E V where
  field := boundedPath T hT f q hf.continuous (C 0) (D 0)
    (value_bound T f C hC) (derivativeBound_nonneg T hT q D hD 0)
    (value_bound T q D hD) hd
  smooth t := by
    change ContDiff ℝ ∞ (fun x => f x t)
    exact (ContinuousMap.evalCLM ℝ t).contDiff.comp hf
  jet n := boundedPath T hT (jetFamily T f n) (jetFamily T q n)
    (jetFamily_contDiff T f hf n).continuous (C n) (D n)
    (fun t x => by rw [jetFamily_apply T f hf]; exact hC n t x)
    (derivativeBound_nonneg T hT q D hD n)
    (fun t x => by rw [jetFamily_apply T q hq]; exact hD n t x)
    (jetFamily_hasDerivWithinAt T hT f q hf hq hd n)
  jet_eq n t x := jetFamily_apply T f hf n x t

@[simp] theorem ofPathFamily_apply (t : Icc (0 : ℝ) T) (x : E) :
    (ofPathFamily T hT f q hf hq hd C D hC hD).field t x = f x t := rfl

@[simp] theorem ofPathFamily_jet_apply (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    (ofPathFamily T hT f q hf hq hd C D hC hD).jet n t x =
      iteratedFDeriv ℝ n (fun y => f y t) x :=
  jetFamily_apply T f hf n x t

theorem ofPathFamily_jet_norm (n : ℕ) :
    ‖(ofPathFamily T hT f q hf hq hd C D hC hD).jet n‖ ≤ C n := by
  have hnonneg : 0 ≤ C n := (norm_nonneg _).trans (hC n ⟨0,le_rfl,hT⟩ 0)
  apply (ContinuousMap.norm_le _ hnonneg).2
  intro t
  apply (BoundedContinuousFunction.norm_le hnonneg).2
  intro x
  rw [ofPathFamily_jet_apply]
  exact hC n t x

theorem ofPathFamily_field_norm :
    ‖(ofPathFamily T hT f q hf hq hd C D hC hD).field‖ ≤ C 0 := by
  have hnonneg : 0 ≤ C 0 := (norm_nonneg _).trans (hC 0 ⟨0,le_rfl,hT⟩ 0)
  apply (ContinuousMap.norm_le _ hnonneg).2
  intro t
  apply (BoundedContinuousFunction.norm_le hnonneg).2
  intro x
  exact value_bound T f C hC t x

end SmoothTimeField

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerSmoothBanachFlow

open Set EulerVolterraConvolution EulerContinuousTimeIntegral EulerSmoothFlowGevrey

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (B R : ℝ)

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowCoefficientPaths2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance

variable (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
  (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)

theorem displacementFamily_time_derivative (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (displacementFamily T hT A x))
      (velocityFamily T hT A x t) (Icc (0 : ℝ) T) t := by
  rw [displacementFamily_integral]
  exact integral_hasDerivWithinAt T hT _ t

include hB hR hsmall hb in
theorem displacementFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => displacementFamily T hT A y t) x‖ ≤
      B*T*(4*R)^n*(n.factorial : ℝ)^2 := by
  have he : (fun y => displacementFamily T hT A y t) = displacement T hT A t := by
    funext y
    simp only [displacement, extendPath, projIcc_of_mem hT t.property]
  rw [he]
  apply (displacement_bound T hT A B R hB hR hsmall hb n t t.property x).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t.property.2 hB)
      (pow_nonneg (by positivity) n)) (sq_nonneg _)

include hB hR hsmall hb in
theorem velocityFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => velocityFamily T hT A y t) x‖ ≤
      B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2 :=
  materialVelocity_bound T hT A B R hB hR hsmall hb n t x

/-- Displacement coefficient, constructed using `SmoothTimeField.ofPathFamily`. -/
def displacementCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  SmoothTimeField.ofPathFamily T hT
    (displacementFamily T hT A) (velocityFamily T hT A)
    (displacementFamily_contDiff T hT A) (velocityFamily_contDiff T hT A)
    (displacementFamily_time_derivative T hT A)
    (fun n => B*T*(4*R)^n*(n.factorial : ℝ)^2)
    (fun n => B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2)
    (displacementFamily_jet_bound T hT A B R hB hR hsmall hb)
    (velocityFamily_jet_bound T hT A B R hB hR hsmall hb)

@[simp] theorem displacementCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (displacementCoefficient T hT A B R hB hR hsmall hb).field t x =
      (flowData T hT A).forward t x-x := rfl

theorem displacementCoefficient_jet_norm (n : ℕ) :
    ‖(displacementCoefficient T hT A B R hB hR hsmall hb).jet n‖ ≤
      B*T*(4*R)^n*(n.factorial : ℝ)^2 := by
  apply SmoothTimeField.ofPathFamily_jet_norm

variable (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (htime : SmoothTimeField.TimeDerivative T hT A A₁)
  (B₁ R₁ : ℝ) (hB₁ : 0 ≤ B₁) (hR₁ : 0 ≤ R₁)
  (hb₁ : ∀ n, ‖A₁.jet n‖ ≤ B₁ * R₁ ^ n * (n.factorial : ℝ) ^ 2)

include hB hR hsmall hb hB₁ hR₁ hb₁ in
theorem accelerationFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => accelerationFamily T hT A A₁ y t) x‖ ≤
      (B₁+3*B^2*R)*(flowRadius B R T (4*R+R₁))^n*(n.factorial : ℝ)^2 := by
  have he : (fun y => accelerationFamily T hT A A₁ y t) =
      materialAcceleration T hT A A₁ t := funext (fun y => accelerationFamily_apply T hT A A₁ y t)
  rw [he]
  exact materialAcceleration_bound T hT A A₁ B R B₁ R₁ hB hR hB₁ hR₁ hsmall hb hb₁ n t x

/-- Velocity coefficient, constructed using `SmoothTimeField.ofPathFamily`. -/
def velocityCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  SmoothTimeField.ofPathFamily T hT
    (velocityFamily T hT A) (accelerationFamily T hT A A₁)
    (velocityFamily_contDiff T hT A) (accelerationFamily_contDiff T hT A A₁)
    (velocityFamily_time_derivative T hT A A₁ htime)
    (fun n => B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2)
    (fun n => (B₁+3*B^2*R)*(flowRadius B R T (4*R+R₁))^n*(n.factorial : ℝ)^2)
    (velocityFamily_jet_bound T hT A B R hB hR hsmall hb)
    (accelerationFamily_jet_bound T hT A B R hB hR hsmall hb A₁ B₁ R₁ hB₁ hR₁ hb₁)

@[simp] theorem velocityCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).field t x =
      A.field t ((flowData T hT A).forward t x) := rfl

theorem velocityCoefficient_jet_norm (n : ℕ) :
    ‖(velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).jet n‖ ≤
      B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2 := by
  apply SmoothTimeField.ofPathFamily_jet_norm

end EulerSmoothBanachFlow
