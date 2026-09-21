/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.Domain
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra

/-! # Mean Zero -/

namespace Homogenization

noncomputable def integralAverage {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, u x ∂MeasureTheory.volume

namespace H1Function

theorem integrableOn {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) :
    MeasureTheory.IntegrableOn u U := by
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
    u.memL2.integrable (by norm_num : (1 : ENNReal) ≤ 2)

noncomputable def const {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (c : ℝ) : H1Function U :=
  { toFun := fun _ => c
    grad := fun _ => 0
    memL2 := by
      simpa using
        (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := c))
    gradMemL2 := by
      intro i
      exact
        (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal))
          (c := (0 : ℝ)))
    hasWeakGradient := by
      simpa using!
        (HasWeakGradientOn.of_contDiff
          (U := U)
          (f := fun _ : Vec d => c)
          (hf := contDiff_const)) }

@[simp] theorem const_apply {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (c : ℝ) (x : Vec d) :
    (H1Function.const (U := U) c) x = c :=
  rfl

@[simp] theorem grad_const {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (c : ℝ) (x : Vec d) :
    (H1Function.const (U := U) c).grad x = 0 :=
  rfl

noncomputable def addConst {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (c : ℝ) : H1Function U :=
  u + H1Function.const (U := U) c

@[simp] theorem addConst_apply {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (c : ℝ) (x : Vec d) :
    u.addConst c x = u x + c :=
  rfl

@[simp] theorem grad_addConst {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (c : ℝ) (x : Vec d) :
    (u.addConst c).grad x = u.grad x := by
  ext i
  change (u.grad x + 0) i = u.grad x i
  simp

noncomputable def subAverage {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1Function U) : H1Function U :=
  u.addConst (-integralAverage U u)

@[simp] theorem subAverage_apply {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (x : Vec d) :
    u.subAverage x = u x - integralAverage U u := by
  simp [H1Function.subAverage, sub_eq_add_neg]

@[simp] theorem grad_subAverage {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (x : Vec d) :
    (u.subAverage).grad x = u.grad x := by
  simp [H1Function.subAverage]

theorem meanZeroOn_subAverage {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1Function U) :
    MeanZeroOn U u.subAverage := by
  unfold MeanZeroOn H1Function.subAverage H1Function.addConst integralAverage
  have huInt : MeasureTheory.IntegrableOn u U := u.integrableOn
  have hconstInt :
      MeasureTheory.IntegrableOn
        (fun _ : Vec d => -((MeasureTheory.volume U).toReal⁻¹ *
          ∫ x in U, u x ∂MeasureTheory.volume)) U := by
    simpa [MeasureTheory.IntegrableOn] using
      (MeasureTheory.integrable_const
        (-((MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, u x ∂MeasureTheory.volume)) :
        MeasureTheory.Integrable
          (fun _ : Vec d => -((MeasureTheory.volume U).toReal⁻¹ *
            ∫ x in U, u x ∂MeasureTheory.volume))
          (volumeMeasureOn U))
  have hμ :
      (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
    exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
  have hμ' : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
  by_cases hvol : (MeasureTheory.volume U).toReal = 0
  · have hfinite : MeasureTheory.volume U < ⊤ := by
      simpa [volumeMeasureOn] using (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ)
    have hzeroMeasure : MeasureTheory.volume U = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (MeasureTheory.volume U)).mp hvol with hzero | htop
      · exact hzero
      · exact (hfinite.ne htop).elim
    simpa using!
      (MeasureTheory.setIntegral_measure_zero
        (f := fun x =>
          (u + const (-((MeasureTheory.volume U).toReal⁻¹ *
            ∫ y in U, u y ∂MeasureTheory.volume))).toFun x)
        hzeroMeasure)
  · let I : ℝ := ∫ x in U, u x ∂MeasureTheory.volume
    have hconst :
        ∫ x in U, (-((MeasureTheory.volume U).toReal⁻¹ * I)) ∂MeasureTheory.volume =
          (MeasureTheory.volume U).toReal * (-((MeasureTheory.volume U).toReal⁻¹ * I)) := by
      rw [MeasureTheory.integral_const, smul_eq_mul, hμ, hμ']
    have hcancel :
        (MeasureTheory.volume U).toReal * ((MeasureTheory.volume U).toReal⁻¹ * I) = I := by
      field_simp [hvol]
    have hfun :
        (fun x => (u + const (-((MeasureTheory.volume U).toReal⁻¹ * I))).toFun x) =
          (fun x => u x + -((MeasureTheory.volume U).toReal⁻¹ * I)) := by
      rfl
    simpa [I] using!
      (calc
        ∫ x in U, (u + const (-((MeasureTheory.volume U).toReal⁻¹ * I))).toFun x
            ∂MeasureTheory.volume
          = ∫ x in U, u x ∂MeasureTheory.volume +
              ∫ x in U, (-((MeasureTheory.volume U).toReal⁻¹ * I)) ∂MeasureTheory.volume := by
                rw [hfun]
                rw [MeasureTheory.integral_add huInt.integrable hconstInt.integrable]
        _ = I + (MeasureTheory.volume U).toReal * (-((MeasureTheory.volume U).toReal⁻¹ * I)) := by
              rw [hconst]
        _ = 0 := by
              rw [show (MeasureTheory.volume U).toReal * (-((MeasureTheory.volume U).toReal⁻¹ * I)) =
                -((MeasureTheory.volume U).toReal * ((MeasureTheory.volume U).toReal⁻¹ * I)) by ring]
              rw [hcancel]
              ring)

noncomputable def coordOnIsBoundedDomain {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hBounded : IsBoundedDomain U) (i : Fin d) :
    H1Function U := by
  classical
  let R : ℝ := Classical.choose hBounded
  have hRpos : 0 < R := (Classical.choose_spec hBounded).1
  have hR : ∀ x ∈ U, ∀ j, |x j| ≤ R := (Classical.choose_spec hBounded).2
  refine
    { toFun := fun x => x i
      grad := fun _ => basisVec i
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · refine MeasureTheory.MemLp.of_bound
      (μ := volumeMeasureOn U)
      (continuous_apply i).aestronglyMeasurable
      R ?_
    rw [MeasureTheory.ae_restrict_iff' hU]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact by simpa [Real.norm_eq_abs] using hR x hx i
  · intro j
    simpa using
      (MeasureTheory.memLp_const
        (μ := volumeMeasureOn U)
        (p := (2 : ENNReal))
        (c := basisVec i j))
  · intro j
    convert
      (HasWeakPartialDerivOn.of_contDiff
        (U := U)
        (i := j)
        (f := fun x : Vec d => x i)
        (hf := contDiff_apply (𝕜 := ℝ) (n := (1 : ℕ∞)) (E := ℝ) i)) using 2
    rename_i x
    let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have hproj :
        HasFDerivAt (fun y : Vec d => y i) π x := by
      simpa [π] using! π.hasFDerivAt (x := x)
    have hlin : fderiv ℝ (fun y : Vec d => y i) x = π := hproj.fderiv
    simpa [π, basisVec_apply, eq_comm] using
      (congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec j)) hlin).symm

@[simp] theorem coordOnIsBoundedDomain_apply {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hBounded : IsBoundedDomain U) (i : Fin d) (x : Vec d) :
    (H1Function.coordOnIsBoundedDomain hU hBounded i) x = x i :=
  by
    simp [H1Function.coordOnIsBoundedDomain]

@[simp] theorem coordOnIsBoundedDomain_grad {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hBounded : IsBoundedDomain U) (i : Fin d) (x : Vec d) :
    (H1Function.coordOnIsBoundedDomain hU hBounded i).grad x = basisVec i :=
  by
    simp [H1Function.coordOnIsBoundedDomain]

noncomputable def coordOnIsSobolevRegularDomain {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (i : Fin d) :
    H1Function U :=
  H1Function.coordOnIsBoundedDomain hU.measurableSet hU.isBoundedDomain i

@[simp] theorem coordOnIsSobolevRegularDomain_apply {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (i : Fin d) (x : Vec d) :
    (H1Function.coordOnIsSobolevRegularDomain hU i) x = x i := by
  simp [H1Function.coordOnIsSobolevRegularDomain]

@[simp] theorem coordOnIsSobolevRegularDomain_grad {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (i : Fin d) (x : Vec d) :
    (H1Function.coordOnIsSobolevRegularDomain hU i).grad x = basisVec i := by
  simp [H1Function.coordOnIsSobolevRegularDomain]

/-- The componentwise average gradient of an `H¹` function on a finite-measure
domain. -/
noncomputable def averageGradient {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1Function U) : Vec d :=
  fun i => integralAverage U (fun x => u.grad x i)

/-- If each gradient coordinate of an `H¹` function has zero integral, then its
componentwise average gradient vanishes. -/
theorem averageGradient_eq_zero_of_integral_eq_zero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U)
    (hzero : (fun i => ∫ x in U, u.grad x i ∂MeasureTheory.volume) = 0) :
    u.averageGradient = 0 := by
  ext i
  change integralAverage U (fun x => u.grad x i) = 0
  unfold integralAverage
  rw [show ∫ x in U, u.grad x i ∂MeasureTheory.volume = 0 by
    simpa using congrFun hzero i]
  simp

/-- The affine `H¹` function on a Sobolev-regular domain with constant gradient
`p`. -/
noncomputable def affineOnIsSobolevRegularDomain {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (p : Vec d) : H1Function U := by
  classical
  let R : ℝ := Classical.choose hU.isBoundedDomain
  have hR : ∀ x ∈ U, ∀ i, |x i| ≤ R := (Classical.choose_spec hU.isBoundedDomain).2
  let π : Vec d →L[ℝ] ℝ := ∑ i : Fin d, p i • ContinuousLinearMap.proj i
  refine
    { toFun := fun x => π x
      grad := fun _ => p
      memL2 := by
        let C : ℝ := ∑ i : Fin d, ‖p i‖ * R
        refine MeasureTheory.MemLp.of_bound
          (μ := volumeMeasureOn U) π.continuous.aestronglyMeasurable C ?_
        rw [MeasureTheory.ae_restrict_iff' hU.measurableSet]
        refine Filter.Eventually.of_forall ?_
        intro x hx
        calc
          ‖π x‖ = ‖∑ i : Fin d, p i * x i‖ := by
            simp [π, ContinuousLinearMap.proj_apply]
          _ ≤ ∑ i : Fin d, ‖p i * x i‖ := norm_sum_le _ _
          _ = ∑ i : Fin d, ‖p i‖ * ‖x i‖ := by
              simp [norm_mul]
          _ ≤ ∑ i : Fin d, ‖p i‖ * R := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hxi : ‖x i‖ ≤ R := by
                simpa [Real.norm_eq_abs] using hR x hx i
              exact mul_le_mul_of_nonneg_left hxi (norm_nonneg _)
          _ = C := rfl
      gradMemL2 := by
        intro i
        simpa using
          (MeasureTheory.memLp_const
            (μ := volumeMeasureOn U)
            (p := (2 : ENNReal))
            (c := p i))
      hasWeakGradient := by
        intro i
        have hpart :
            HasWeakPartialDerivOn U i (fun x : Vec d => π x)
              (fun x => (fderiv ℝ (fun y : Vec d => π y) x) (basisVec i)) :=
          HasWeakPartialDerivOn.of_contDiff
            (i := i)
            (f := fun x : Vec d => π x)
            (hf := π.contDiff)
        have hbasis : π (basisVec i) = p i := by
          simp [π, basisVec_apply, ContinuousLinearMap.proj_apply, eq_comm]
        intro φ hφ_smooth hφ_compact hφ_sub
        simpa [hbasis] using hpart φ hφ_smooth hφ_compact hφ_sub }

@[simp] theorem affineOnIsSobolevRegularDomain_apply {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (p : Vec d) (x : Vec d) :
    (H1Function.affineOnIsSobolevRegularDomain hU p) x = ∑ i : Fin d, p i * x i := by
  simp [H1Function.affineOnIsSobolevRegularDomain]

@[simp] theorem affineOnIsSobolevRegularDomain_grad {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (p : Vec d) (x : Vec d) :
    (H1Function.affineOnIsSobolevRegularDomain hU p).grad x = p := by
  simp [H1Function.affineOnIsSobolevRegularDomain]

/-- The affine `H¹` function with gradient equal to `u.averageGradient`. -/
noncomputable def averageGradientAffineOnIsSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (u : H1Function U) : H1Function U :=
  H1Function.affineOnIsSobolevRegularDomain hU u.averageGradient

@[simp] theorem averageGradientAffineOnIsSobolevRegularDomain_grad
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (u : H1Function U) (x : Vec d) :
    (u.averageGradientAffineOnIsSobolevRegularDomain hU).grad x = u.averageGradient := by
  simp [H1Function.averageGradientAffineOnIsSobolevRegularDomain]

@[simp] theorem sub_averageGradientAffineOnIsSobolevRegularDomain_grad
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (u : H1Function U) (x : Vec d) :
    (u - u.averageGradientAffineOnIsSobolevRegularDomain hU).grad x =
      u.grad x - u.averageGradient := by
  ext i
  calc
    (u - u.averageGradientAffineOnIsSobolevRegularDomain hU).grad x i
        = (u.grad x + (-1 : ℝ) •
            (u.averageGradientAffineOnIsSobolevRegularDomain hU).grad x) i := by
            rfl
    _ = u.grad x i + (-1 : ℝ) * (u.averageGradientAffineOnIsSobolevRegularDomain hU).grad x i := by
          simp
    _ = u.grad x i + -u.averageGradient i := by
          simp [H1Function.averageGradientAffineOnIsSobolevRegularDomain]
    _ = u.grad x i - u.averageGradient i := by
          ring
    _ = (u.grad x - u.averageGradient) i := by
          rfl

/-- Honest `H¹` affine decomposition: subtracting the affine function with
gradient `averageGradient` leaves an `H¹` function whose gradient has zero
average. -/
theorem exists_h1_sub_averageGradient_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    ∃ w : H1Function U,
      w.grad = fun x => u.grad x - u.averageGradient := by
  refine ⟨u - u.averageGradientAffineOnIsSobolevRegularDomain hU, ?_⟩
  funext x
  exact u.sub_averageGradientAffineOnIsSobolevRegularDomain_grad hU x

/-- If the average gradient vanishes and the domain has nonzero volume, then
the componentwise gradient integrals vanish. -/
theorem integral_eq_zero_of_averageGradient_eq_zero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1Function U) (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (havg : u.averageGradient = 0) :
    (fun i => ∫ x in U, u.grad x i ∂MeasureTheory.volume) = 0 := by
  ext i
  have havi : integralAverage U (fun x => u.grad x i) = 0 := by
    simpa [H1Function.averageGradient] using congrFun havg i
  unfold integralAverage at havi
  have hm := congrArg (fun t : ℝ => (MeasureTheory.volume U).toReal * t) havi
  field_simp [hvol] at hm
  simpa using hm

end H1Function

end Homogenization
