/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelFrozenGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevGevreyAt

@[expose] public section

/-!
# The forward estimate in actual fixed-Sobolev external-word blocks

The normalized Duhamel solution satisfies the constructed frozen equation.
Its inverse at the base point is literally Id. Applying the finite base-order
inverse estimate and then the external-word recurrence gives one factorial
shift at the same input/output radius. Every constant is a fixed polynomial
in the coefficient, data, propagator and time-length constants when q is fixed.
-/

noncomputable section

namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousTimeWeight
  EulerGevrey EulerParameterWordGevrey
open scoped ContDiff

/-- The once-enlarged coefficient amplitude for the frozen equation at fixed base order. -/
def forwardSobolevAmplitude (ι : Type*) [Fintype ι] (q : ℕ) (T C CB Rc : ℝ) : ℝ :=
  sobolevCoefficientAmplitude ι q Rc (frozenAmplitude T C CB)

/-- A fixed polynomial cost for the source's forward Hq external-word estimate. -/
def forwardSobolevCost (ι : Type*) [Fintype ι] (q : ℕ) (T C A D CB Rc : ℝ) : ℝ :=
  1+sobolevInverseCost 1 (forwardSobolevAmplitude ι q T C CB Rc) q *
    (forwardSobolevAmplitude ι q T C CB Rc+C*A+C*T*D)

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T,E →L[ℝ] E))
  (U : ∀ x, Evolution T hT (B x))
  (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
  (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E)

private local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)) :=
  inferInstance
private local instance : NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)) :=
  inferInstance

include hd in
/-- The actual fixed-Hq block of the forward solution gains just one shift,
with an unchanged radius and with H3 used only at the base parameter. -/
theorem weightedSolution_block_gevrey_at
    (hB : ContDiff ℝ ∞ B) (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀)
    (hg₀ : g ⟨0,le_rfl,hT⟩ = 1)
    (C A D CB Rc R : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hCB : 0 ≤ CB)
    (hRc : 0 ≤ Rc)
    (hR : 2*forwardSobolevCost ι q T C A D CB Rc*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hBb : ∀ n y, ‖iteratedFDeriv ℝ n B y‖ ≤ CB*majorant Rc 0 n)
    (x : P) (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖(U x).propagator t s‖ ≤ C*g t/g s)
    (d : ℕ) (hforce : ∀ n, block directions q f n x ≤ D*majorant R d n)
    (hinitial : ∀ n, block directions q a₀ n x ≤ A*majorant R d n)
    (n : ℕ) :
    block directions q (fun y => (U y).weightedSolution g hg (f y) (a₀ y)) n x ≤
      majorant R (d+1) n := by
  let Aₓ := frozenOperator T hT B U g hg x
  let Fₓ := frozenForcing T hT B U g hg f a₀ x
  let u := fun y => (U y).weightedSolution g hg (f y) (a₀ y)
  let CF := forwardSobolevAmplitude ι q T C CB Rc
  let DF := C*A+C*T*D
  let M := forwardSobolevCost ι q T C A D CB Rc
  have hfrozen : 0 ≤ frozenAmplitude T C CB := by unfold frozenAmplitude; positivity
  have hCF : 0 ≤ CF := sobolevCoefficientAmplitude_nonneg q Rc (frozenAmplitude T C CB) hRc hfrozen
  have hDF : 0 ≤ DF := by dsimp [DF]; positivity
  have hcost : 0 ≤ sobolevInverseCost 1 CF q := sobolevInverseCost_nonneg 1 CF zero_le_one hCF q
  have hMeq : M = 1+sobolevInverseCost 1 CF q*(CF+DF) := by
    dsimp only [M, forwardSobolevCost, CF, DF]
    ring
  have hM : 1 ≤ M := by
    rw [hMeq]
    exact le_add_of_nonneg_right (mul_nonneg hcost (add_nonneg hCF hDF))
  have hMC : sobolevInverseCost 1 CF q*CF ≤ M := by
    rw [hMeq]
    nlinarith [mul_nonneg hcost hDF]
  have hMD : sobolevInverseCost 1 CF q*DF ≤ M := by
    rw [hMeq]
    nlinarith [mul_nonneg hcost hCF]
  have hAₓ : ContDiff ℝ ∞ Aₓ := frozenOperator_contDiff T hT B U g hg hB x
  have hFₓ : ContDiff ℝ ∞ Fₓ := frozenForcing_contDiff T hT B U g hg f a₀ hf ha₀ x
  have hu : ContDiff ℝ ∞ u := weightedSolution_contDiff T hT B U g hg f a₀ hB hf ha₀
  have hAb : ∀ j y, ‖iteratedFDeriv ℝ j Aₓ y‖ ≤ frozenAmplitude T C CB*majorant Rc 0 j :=
    frozenOperator_bound T hT B U g hg hB hg₀ C CB Rc hC hCB hRc hBb x hU
  have hbase : baseSize directions q Aₓ x ≤ CF :=
    baseSize_of_tensor_bound directions hd q Aₓ hAₓ Rc (frozenAmplitude T C CB) hRc hfrozen hAb x
  have hcoeff (j : ℕ) : coefficientBlock directions q Aₓ (j+1) x ≤
      CF*(sobolevCoefficientRadius ι Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    simpa only [majorant, Nat.add_zero, CF, forwardSobolevAmplitude] using
      coefficientBlock_of_tensor_bound directions hd q Aₓ hAₓ
      Rc (frozenAmplitude T C CB) hRc hfrozen hAb (j+1) x
  have hFb : ∀ j, block directions q Fₓ j x ≤ DF*majorant R d j :=
    frozenForcing_block_bound T hT B U g hg directions q f a₀ hf ha₀ hg₀ C A D R hC x hU d hforce
      hinitial
  exact block_inverse_gevrey_at directions q Aₓ u Fₓ hAₓ hu hFₓ
    (frozenOperator_equation T hT B U g hg f a₀ x) x
    (ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) T,E))
    (fun v => by change Aₓ x v = v; rw [show Aₓ x = ContinuousLinearMap.id ℝ _ from
      frozenOperator_self T hT B U g hg x]; rfl)
    1 CF CF DF M (sobolevCoefficientRadius ι Rc) R hCF hDF hM hMC hMD
    (sobolevCoefficientRadius_nonneg Rc hRc) hR norm_id_le hbase hcoeff d hFb n

end EulerLinearDuhamel
