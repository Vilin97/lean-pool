/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJacobian
public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathJoint

@[expose] public section

/-! Genuine joint time-space regularity of the constructed flow and its
inverse. Interior C² uses only the actual first time derivative of the
velocity coefficient, together with its existing smooth spatial jets. -/

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

def liftForward (p : ℝ × E) : ℝ × E := (p.1, (flowData T hT A).forward p.1 p.2)
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
