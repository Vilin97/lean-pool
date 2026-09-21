/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries

/-! # Graph -/

namespace Homogenization

open scoped RealInnerProductSpace

section Graph

variable {d : ℕ} {U : Set (Vec d)}

/-- The weak-gradient constraint attached to a coordinate `i` and a smooth
compactly supported test function `φ`. Its kernel consists of pairs
`(u, Du) ∈ L²(U) × L²(U; HilbertVec d)` satisfying the corresponding
integration-by-parts identity. -/
noncomputable def h1WeakConstraintCLM (i : Fin d) (φ : H1WeakTestFunction U) :
    (ScalarL2 U × HilbertVectorL2 U) →L[ℝ] ℝ :=
  ((InnerProductSpace.toDual ℝ (ScalarL2 U) (φ.derivToScalarL2 i)).comp
      (ContinuousLinearMap.fst ℝ (ScalarL2 U) (HilbertVectorL2 U))) +
    (((InnerProductSpace.toDual ℝ (ScalarL2 U) φ.toScalarL2).comp
        (hilbertVectorCoordToScalarL2 (U := U) i)).comp
      (ContinuousLinearMap.snd ℝ (ScalarL2 U) (HilbertVectorL2 U)))

@[simp] theorem h1WeakConstraintCLM_apply (i : Fin d) (φ : H1WeakTestFunction U)
    (z : ScalarL2 U × HilbertVectorL2 U) :
    h1WeakConstraintCLM (U := U) i φ z =
      inner ℝ z.1 (φ.derivToScalarL2 i) +
        inner ℝ (hilbertVectorCoordToScalarL2 (U := U) i z.2) φ.toScalarL2 := by
  simp [h1WeakConstraintCLM, InnerProductSpace.toDual_apply_apply, real_inner_comm]

theorem h1WeakConstraintCLM_apply_eq_integral (i : Fin d) (φ : H1WeakTestFunction U)
    (z : ScalarL2 U × HilbertVectorL2 U) :
    h1WeakConstraintCLM (U := U) i φ z =
      ∫ x in U, z.1 x * φ.deriv i x ∂MeasureTheory.volume +
        ∫ x in U, z.2 x i * φ x ∂MeasureTheory.volume := by
  rw [h1WeakConstraintCLM_apply, scalarInner_eq_integral, coordInner_eq_integral]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [φ.coeFn_derivToScalarL2 i] with x hφ
  rw [hφ]

/-- The closed ambient subspace cut out by the weak-gradient constraints. -/
noncomputable def h1GraphClosedSubmodule :
    ClosedSubmodule ℝ (ScalarL2 U × HilbertVectorL2 U) :=
  ⨅ i : Fin d, ⨅ φ : H1WeakTestFunction U,
    (⊥ : ClosedSubmodule ℝ ℝ).comap (h1WeakConstraintCLM (U := U) i φ)

theorem mem_h1GraphClosedSubmodule_iff
    (z : ScalarL2 U × HilbertVectorL2 U) :
    z ∈ h1GraphClosedSubmodule (U := U) ↔
      ∀ i : Fin d, ∀ φ : H1WeakTestFunction U,
        h1WeakConstraintCLM (U := U) i φ z = 0 := by
  simp [h1GraphClosedSubmodule]

theorem h1_pair_mem_h1GraphClosedSubmodule (u : H1Function U) :
    (u.toScalarL2, u.gradToHilbertVectorL2) ∈ h1GraphClosedSubmodule (U := U) := by
  rw [mem_h1GraphClosedSubmodule_iff]
  intro i φ
  have hweak :=
    u.hasWeakGradient i φ φ.smooth φ.compactSupport φ.support_subset
  have hcoord :
      ∫ x in U, u.gradToHilbertVectorL2 x i * φ x ∂MeasureTheory.volume =
        ∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [u.coeFn_gradToHilbertVectorL2] with x hgrad
    rw [hgrad]
    simp [hilbertifyVecField]
  calc
    h1WeakConstraintCLM (U := U) i φ (u.toScalarL2, u.gradToHilbertVectorL2)
        = ∫ x in U, u.toScalarL2 x * φ.deriv i x ∂MeasureTheory.volume +
            ∫ x in U, u.gradToHilbertVectorL2 x i * φ x ∂MeasureTheory.volume := by
              exact h1WeakConstraintCLM_apply_eq_integral (U := U) i φ
                (u.toScalarL2, u.gradToHilbertVectorL2)
    _ = ∫ x in U, u x * φ.deriv i x ∂MeasureTheory.volume +
          ∫ x in U, u.gradToHilbertVectorL2 x i * φ x ∂MeasureTheory.volume := by
            congr 1
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [u.coeFn_toScalarL2] with x hu
            rw [hu]
    _ = ∫ x in U, u x * φ.deriv i x ∂MeasureTheory.volume +
          ∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume := by
            rw [hcoord]
    _ = 0 := by
          have hweak' :
              ∫ x in U, u x * φ.deriv i x ∂MeasureTheory.volume =
                -∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume := by
            simpa [H1WeakTestFunction.deriv] using hweak
          rw [hweak']
          ring

/-- Recover an `H¹` witness from a point of the closed weak-gradient graph. -/
noncomputable def toH1FunctionOfMemH1Graph
    (z : ScalarL2 U × HilbertVectorL2 U)
    (hz : z ∈ h1GraphClosedSubmodule (U := U)) :
    H1Function U where
  toFun := z.1
  grad := hilbertVectorL2ToVectorL2 (U := U) z.2
  memL2 := MeasureTheory.Lp.memLp z.1
  gradMemL2 := by
    intro i
    have hgradMem : MemVectorL2 U (hilbertVectorL2ToVectorL2 (U := U) z.2) :=
      MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) z.2)
    simpa [MemL2On, MemVectorL2, volumeMeasureOn] using
      (show MemL2On U (fun x => (hilbertVectorL2ToVectorL2 (U := U) z.2 x) i) by
        let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
        simpa [MemL2On, MemVectorL2, volumeMeasureOn] using! π.comp_memLp' hgradMem)
  hasWeakGradient := by
    intro i ψ hψ_smooth hψ_compact hψ_sub
    let φ : H1WeakTestFunction U :=
      ⟨ψ, hψ_smooth, hψ_compact, hψ_sub⟩
    have hconstraint :
        h1WeakConstraintCLM (U := U) i φ z = 0 := by
      exact (mem_h1GraphClosedSubmodule_iff (U := U) z).mp hz i φ
    have hcoord :
        ∫ x in U, z.2 x i * φ x ∂MeasureTheory.volume =
          ∫ x in U, (hilbertVectorL2ToVectorL2 (U := U) z.2 x i) * φ x
            ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (U := U) (f := z.2)] with x hg
      rw [hg]
    have hsum :
        ∫ x in U, z.1 x * φ.deriv i x ∂MeasureTheory.volume +
            ∫ x in U, (hilbertVectorL2ToVectorL2 (U := U) z.2 x i) * φ x
              ∂MeasureTheory.volume = 0 := by
      rw [← hcoord, ← h1WeakConstraintCLM_apply_eq_integral (U := U) i φ]
      exact hconstraint
    have hneg :
        ∫ x in U, z.1 x * φ.deriv i x ∂MeasureTheory.volume =
          -∫ x in U, (hilbertVectorL2ToVectorL2 (U := U) z.2 x i) * φ x
            ∂MeasureTheory.volume := by
      exact eq_neg_of_add_eq_zero_left hsum
    simpa [H1WeakTestFunction.deriv] using hneg

theorem mem_h1GraphClosedSubmodule_iff_exists_h1Function
    (z : ScalarL2 U × HilbertVectorL2 U) :
    z ∈ h1GraphClosedSubmodule (U := U) ↔
      ∃ u : H1Function U, u.toScalarL2 = z.1 ∧ u.gradToHilbertVectorL2 = z.2 := by
  constructor
  · intro hz
    refine ⟨toH1FunctionOfMemH1Graph (U := U) z hz, ?_, ?_⟩
    show (MeasureTheory.Lp.memLp z.1).toLp z.1 = z.1
    exact MeasureTheory.Lp.toLp_coeFn z.1 (MeasureTheory.Lp.memLp z.1)
    have hvec :
        (toH1FunctionOfMemH1Graph (U := U) z hz).gradToVectorL2 =
          hilbertVectorL2ToVectorL2 (U := U) z.2 := by
      show (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) z.2)).toLp
          (hilbertVectorL2ToVectorL2 (U := U) z.2) =
        hilbertVectorL2ToVectorL2 (U := U) z.2
      exact MeasureTheory.Lp.toLp_coeFn
        (hilbertVectorL2ToVectorL2 (U := U) z.2)
        (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) z.2))
    calc
      (toH1FunctionOfMemH1Graph (U := U) z hz).gradToHilbertVectorL2
          = vectorL2ToHilbertVectorL2 (U := U)
              ((toH1FunctionOfMemH1Graph (U := U) z hz).gradToVectorL2) := by
                symm
                simpa [H1Function.gradToVectorL2, H1Function.gradToHilbertVectorL2] using
                  vectorL2ToHilbertVectorL2_toVectorL2
                    (U := U)
                    (f := (toH1FunctionOfMemH1Graph (U := U) z hz).grad)
                    (toH1FunctionOfMemH1Graph (U := U) z hz).grad_memVectorL2
      _ = vectorL2ToHilbertVectorL2 (U := U) (hilbertVectorL2ToVectorL2 (U := U) z.2) := by
            rw [hvec]
      _ = z.2 := by
            exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) z.2
  · rintro ⟨u, hval, hgrad⟩
    have hz :
        z = (u.toScalarL2, u.gradToHilbertVectorL2) := by
      cases z
      simp_all
    rw [hz]
    exact h1_pair_mem_h1GraphClosedSubmodule (U := U) u

/-- Exact representative form of `toH1FunctionOfMemH1Graph`.

If explicit scalar/vector representatives define a point of the closed `H¹`
graph, then they themselves can be used as the `toFun` and `grad` fields of an
`H1Function`.  This avoids losing pointwise control to arbitrary `Lp`
representatives. -/
theorem exists_h1Function_of_toScalarL2_toHilbertVectorL2OfVecField_mem_h1GraphClosedSubmodule
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemScalarL2 U u) (hG : MemVectorL2 U G)
    (hz : (toScalarL2 hu, toHilbertVectorL2OfVecField hG) ∈
      h1GraphClosedSubmodule (U := U)) :
    ∃ w : H1Function U, w.toFun = u ∧ w.grad = G := by
  refine ⟨?_, ?_⟩
  refine
    { toFun := u
      grad := G
      memL2 := hu
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · intro i
    let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
    simpa [MemL2On, MemVectorL2, volumeMeasureOn] using! π.comp_memLp' hG
  · intro i φ hφ_smooth hφ_compact hφ_sub
    let ψ : H1WeakTestFunction U :=
      ⟨φ, hφ_smooth, hφ_compact, hφ_sub⟩
    have hconstraint :
        h1WeakConstraintCLM (U := U) i ψ
            (toScalarL2 hu, toHilbertVectorL2OfVecField hG) = 0 := by
      exact (mem_h1GraphClosedSubmodule_iff (U := U)
        (toScalarL2 hu, toHilbertVectorL2OfVecField hG)).mp hz i ψ
    have hval :
        ∫ x in U, (toScalarL2 hu) x * ψ.deriv i x ∂MeasureTheory.volume =
          ∫ x in U, u x * ψ.deriv i x ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [coeFn_toScalarL2 hu] with x hx
      rw [hx]
    have hgrad :
        ∫ x in U, (toHilbertVectorL2OfVecField hG) x i * ψ x
            ∂MeasureTheory.volume =
          ∫ x in U, G x i * ψ x ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [coeFn_toHilbertVectorL2OfVecField hG] with x hx
      rw [hx]
      simp [hilbertifyVecField]
    have hsum :
        ∫ x in U, u x * ψ.deriv i x ∂MeasureTheory.volume +
            ∫ x in U, G x i * ψ x ∂MeasureTheory.volume = 0 := by
      calc
        ∫ x in U, u x * ψ.deriv i x ∂MeasureTheory.volume +
            ∫ x in U, G x i * ψ x ∂MeasureTheory.volume =
          ∫ x in U, (toScalarL2 hu) x * ψ.deriv i x ∂MeasureTheory.volume +
              ∫ x in U, (toHilbertVectorL2OfVecField hG) x i * ψ x
                ∂MeasureTheory.volume := by
                rw [hval, hgrad]
        _ = h1WeakConstraintCLM (U := U) i ψ
              (toScalarL2 hu, toHilbertVectorL2OfVecField hG) := by
              rw [h1WeakConstraintCLM_apply_eq_integral]
        _ = 0 := hconstraint
    have hneg :
        ∫ x in U, u x * ψ.deriv i x ∂MeasureTheory.volume =
          -∫ x in U, G x i * ψ x ∂MeasureTheory.volume :=
      eq_neg_of_add_eq_zero_left hsum
    simpa [ψ, H1WeakTestFunction.deriv] using hneg
  · constructor <;> rfl

/-- Closedness of the `H¹` graph, stated as a sequential/filter handoff for
honest `H1Function` approximants. -/
theorem mem_h1GraphClosedSubmodule_of_tendsto_h1Function
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (w : ι → H1Function U) {z : ScalarL2 U × HilbertVectorL2 U}
    (hval :
      Filter.Tendsto (fun n => (w n).toScalarL2) l (nhds z.1))
    (hgrad :
      Filter.Tendsto (fun n => (w n).gradToHilbertVectorL2) l (nhds z.2)) :
    z ∈ h1GraphClosedSubmodule (U := U) := by
  have hpair :
      Filter.Tendsto
        (fun n => ((w n).toScalarL2, (w n).gradToHilbertVectorL2))
        l (nhds z) := by
    cases z
    exact hval.prodMk_nhds hgrad
  exact
    (h1GraphClosedSubmodule (U := U)).isClosed.mem_of_tendsto hpair
      (Filter.Eventually.of_forall fun n =>
        h1_pair_mem_h1GraphClosedSubmodule (U := U) (w n))

@[simp] theorem toH1FunctionOfMemH1Graph_toScalarL2
    (z : ScalarL2 U × HilbertVectorL2 U)
    (hz : z ∈ h1GraphClosedSubmodule (U := U)) :
    (toH1FunctionOfMemH1Graph (U := U) z hz).toScalarL2 = z.1 := by
  show (MeasureTheory.Lp.memLp z.1).toLp z.1 = z.1
  exact MeasureTheory.Lp.toLp_coeFn z.1 (MeasureTheory.Lp.memLp z.1)

@[simp] theorem toH1FunctionOfMemH1Graph_gradToHilbertVectorL2
    (z : ScalarL2 U × HilbertVectorL2 U)
    (hz : z ∈ h1GraphClosedSubmodule (U := U)) :
    (toH1FunctionOfMemH1Graph (U := U) z hz).gradToHilbertVectorL2 = z.2 := by
  have hvec :
      (toH1FunctionOfMemH1Graph (U := U) z hz).gradToVectorL2 =
        hilbertVectorL2ToVectorL2 (U := U) z.2 := by
    show (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) z.2)).toLp
        (hilbertVectorL2ToVectorL2 (U := U) z.2) =
      hilbertVectorL2ToVectorL2 (U := U) z.2
    exact MeasureTheory.Lp.toLp_coeFn
      (hilbertVectorL2ToVectorL2 (U := U) z.2)
      (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) z.2))
  calc
    (toH1FunctionOfMemH1Graph (U := U) z hz).gradToHilbertVectorL2
        = vectorL2ToHilbertVectorL2 (U := U)
            ((toH1FunctionOfMemH1Graph (U := U) z hz).gradToVectorL2) := by
              symm
              simpa [H1Function.gradToVectorL2, H1Function.gradToHilbertVectorL2] using
                vectorL2ToHilbertVectorL2_toVectorL2
                  (U := U)
                  (f := (toH1FunctionOfMemH1Graph (U := U) z hz).grad)
                  (toH1FunctionOfMemH1Graph (U := U) z hz).grad_memVectorL2
    _ = vectorL2ToHilbertVectorL2 (U := U) (hilbertVectorL2ToVectorL2 (U := U) z.2) := by
          rw [hvec]
    _ = z.2 := by
          exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) z.2

end Graph

section MeanZero

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The constant-one class in scalar `L²(U)`. -/
noncomputable def oneScalarL2 : ScalarL2 U :=
  Homogenization.toScalarL2
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := (1 : ℝ)))

@[simp] theorem coeFn_oneScalarL2 :
    oneScalarL2 (U := U) =ᵐ[volumeMeasureOn U] fun _ : Vec d => (1 : ℝ) :=
  Homogenization.coeFn_toScalarL2
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := (1 : ℝ)))

/-- The scalar integral on `L²(U)` for finite-measure domains. -/
noncomputable def scalarIntegralCLM : ScalarL2 U →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ (ScalarL2 U) (oneScalarL2 (U := U))

@[simp] theorem scalarIntegralCLM_apply (s : ScalarL2 U) :
    scalarIntegralCLM (U := U) s = ∫ x in U, s x ∂MeasureTheory.volume := by
  rw [scalarIntegralCLM, InnerProductSpace.toDual_apply_apply, real_inner_comm, scalarInner_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [coeFn_oneScalarL2 (U := U)] with x h1
  rw [h1]
  ring

/-- The constant-value embedding `ℝ → L²(U)` attached to the constant-one
class. -/
noncomputable def constScalarL2CLM : ℝ →L[ℝ] ScalarL2 U :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (oneScalarL2 (U := U))

@[simp] theorem constScalarL2CLM_apply (c : ℝ) :
    constScalarL2CLM (U := U) c = c • oneScalarL2 (U := U) := by
  simp [constScalarL2CLM]

/-- The average functional on scalar `L²(U)`. -/
noncomputable def integralAverageCLM : ScalarL2 U →L[ℝ] ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ • scalarIntegralCLM (U := U)

@[simp] theorem integralAverageCLM_apply (s : ScalarL2 U) :
    integralAverageCLM (U := U) s =
      (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, s x ∂MeasureTheory.volume := by
  simp [integralAverageCLM, scalarIntegralCLM_apply, smul_eq_mul]

/-- The scalar-value operator that subtracts the average. -/
noncomputable def subAverageValueCLM : ScalarL2 U →L[ℝ] ScalarL2 U :=
  ContinuousLinearMap.id ℝ (ScalarL2 U) -
    (integralAverageCLM (U := U)).smulRight (oneScalarL2 (U := U))

@[simp] theorem subAverageValueCLM_apply (s : ScalarL2 U) :
    subAverageValueCLM (U := U) s =
      s - (integralAverageCLM (U := U) s) • oneScalarL2 (U := U) := by
  simp [subAverageValueCLM, sub_eq_add_neg]

namespace H1Function

@[simp] theorem toScalarL2_const (c : ℝ) :
    (H1Function.const (U := U) c).toScalarL2 = c • oneScalarL2 (U := U) := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [H1Function.coeFn_toScalarL2 (H1Function.const (U := U) c),
        MeasureTheory.Lp.coeFn_smul c (oneScalarL2 (U := U)),
        coeFn_oneScalarL2 (U := U)]
    with x hc hsmul h1
  calc
    (H1Function.const (U := U) c).toScalarL2 x = (H1Function.const (U := U) c).toFun x := hc
    _ = c := by simp [H1Function.const]
    _ = c * 1 := by ring
    _ = c * oneScalarL2 (U := U) x := by rw [show oneScalarL2 (U := U) x = 1 by simpa using h1]
    _ = (c • oneScalarL2 (U := U)) x := by
          rw [hsmul]
          simp [smul_eq_mul]

theorem integralAverage_eq_integralAverageCLM_toScalarL2
    (u : H1Function U) :
    integralAverage U u = integralAverageCLM (U := U) u.toScalarL2 := by
  calc
    integralAverage U u
        = (MeasureTheory.volume U).toReal⁻¹ *
            ∫ x in U, u x ∂MeasureTheory.volume := by
              rfl
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ∫ x in U, u.toScalarL2 x ∂MeasureTheory.volume := by
            congr 1
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [u.coeFn_toScalarL2] with x hx
            rw [hx]
    _ = integralAverageCLM (U := U) u.toScalarL2 := by
          rw [integralAverageCLM_apply]

theorem toScalarL2_subAverage_eq_subAverageValueCLM
    (u : H1Function U) :
    u.subAverage.toScalarL2 = subAverageValueCLM (U := U) u.toScalarL2 := by
  calc
    u.subAverage.toScalarL2
        = (u + H1Function.const (U := U) (-integralAverage U u)).toScalarL2 := by
            rfl
    _ = u.toScalarL2 +
          (H1Function.const (U := U) (-integralAverage U u)).toScalarL2 := by
            rw [H1Function.toScalarL2_add]
    _ = u.toScalarL2 + (-integralAverage U u) • oneScalarL2 (U := U) := by
          rw [H1Function.toScalarL2_const]
    _ = u.toScalarL2 - (integralAverage U u) • oneScalarL2 (U := U) := by
          simp [sub_eq_add_neg]
    _ = u.toScalarL2 - (integralAverageCLM (U := U) u.toScalarL2) • oneScalarL2 (U := U) := by
          rw [integralAverage_eq_integralAverageCLM_toScalarL2]
    _ = subAverageValueCLM (U := U) u.toScalarL2 := by
          rw [subAverageValueCLM_apply]

theorem tendsto_integralAverage_of_tendsto_toScalarL2
    {α : Type*} {l : Filter α} {f : α → H1Function U} {u : H1Function U}
    (h : Filter.Tendsto (fun a => (f a).toScalarL2) l (nhds u.toScalarL2)) :
    Filter.Tendsto (fun a => integralAverage U (f a)) l (nhds (integralAverage U u)) := by
  have hCLM :
      Filter.Tendsto (fun a => integralAverageCLM (U := U) ((f a).toScalarL2)) l
        (nhds (integralAverageCLM (U := U) u.toScalarL2)) := by
    simpa only [Function.comp_apply] using!
      ((integralAverageCLM (U := U)).continuous.tendsto u.toScalarL2).comp h
  simpa [integralAverage_eq_integralAverageCLM_toScalarL2] using hCLM

theorem tendsto_toScalarL2_subAverage_of_tendsto_toScalarL2
    {α : Type*} {l : Filter α} {f : α → H1Function U} {u : H1Function U}
    (h : Filter.Tendsto (fun a => (f a).toScalarL2) l (nhds u.toScalarL2)) :
    Filter.Tendsto (fun a => ((f a).subAverage).toScalarL2) l
      (nhds (u.subAverage.toScalarL2)) := by
  have hCLM :
      Filter.Tendsto (fun a => subAverageValueCLM (U := U) ((f a).toScalarL2)) l
        (nhds (subAverageValueCLM (U := U) u.toScalarL2)) := by
    simpa only [Function.comp_apply] using!
      ((subAverageValueCLM (U := U)).continuous.tendsto u.toScalarL2).comp h
  simpa [toScalarL2_subAverage_eq_subAverageValueCLM] using hCLM

@[simp] theorem gradCoordToScalarL2_subAverage_eq
    (u : H1Function U) (i : Fin d) :
    u.subAverage.gradCoordToScalarL2 i = u.gradCoordToScalarL2 i := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [H1Function.coeFn_gradCoordToScalarL2 u.subAverage i,
        H1Function.coeFn_gradCoordToScalarL2 u i]
    with x hsub hu
  rw [hsub, hu]
  exact congrArg (fun g : Vec d => g i) (u.grad_subAverage x)

@[simp] theorem gradientCoordL2NormSum_subAverage_eq
    (u : H1Function U) :
    u.subAverage.gradientCoordL2NormSum = u.gradientCoordL2NormSum := by
  simp [H1Function.gradientCoordL2NormSum]

theorem tendsto_gradientCoordL2NormSum_subAverage_of_tendsto_gradCoordToScalarL2
    {α : Type*} {l : Filter α} {f : α → H1Function U} {u : H1Function U}
    (hgrad :
      ∀ i : Fin d,
        Filter.Tendsto (fun a => (f a).gradCoordToScalarL2 i) l
          (nhds (u.gradCoordToScalarL2 i))) :
    Filter.Tendsto (fun a => (f a).subAverage.gradientCoordL2NormSum) l
      (nhds u.subAverage.gradientCoordL2NormSum) := by
  simpa [H1Function.gradientCoordL2NormSum, H1Function.gradCoordToScalarL2_subAverage_eq] using
    (tendsto_finsetSum Finset.univ
      (fun i _ =>
        (continuous_norm.tendsto _).comp
          (hgrad i)))

end H1Function

/-- The closed mean-zero weak-gradient graph in
`L²(U) × L²(U; HilbertVec d)`. -/
noncomputable def h1MeanZeroGraphClosedSubmodule :
    ClosedSubmodule ℝ (ScalarL2 U × HilbertVectorL2 U) :=
  h1GraphClosedSubmodule (U := U) ⊓
    (⊥ : ClosedSubmodule ℝ ℝ).comap
      ((scalarIntegralCLM (U := U)).comp
        (ContinuousLinearMap.fst ℝ (ScalarL2 U) (HilbertVectorL2 U)))

theorem mem_h1MeanZeroGraphClosedSubmodule_iff
    (z : ScalarL2 U × HilbertVectorL2 U) :
    z ∈ h1MeanZeroGraphClosedSubmodule (U := U) ↔
      z ∈ h1GraphClosedSubmodule (U := U) ∧
        scalarIntegralCLM (U := U) z.1 = 0 := by
  simp [h1MeanZeroGraphClosedSubmodule]

theorem h1MeanZero_pair_mem_h1MeanZeroGraphClosedSubmodule
    (u : H1MeanZeroFunction U) :
    (u.toScalarL2, u.gradToHilbertVectorL2) ∈ h1MeanZeroGraphClosedSubmodule (U := U) := by
  rw [mem_h1MeanZeroGraphClosedSubmodule_iff]
  refine ⟨h1_pair_mem_h1GraphClosedSubmodule (U := U) u.toH1Function, ?_⟩
  calc
    scalarIntegralCLM (U := U) u.toScalarL2 = ∫ x in U, u.toScalarL2 x ∂MeasureTheory.volume := by
      exact scalarIntegralCLM_apply (U := U) u.toScalarL2
    _ = ∫ x in U, u x ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [u.toH1Function.coeFn_toScalarL2] with x hu
          simpa [H1MeanZeroFunction.toScalarL2] using hu
    _ = 0 := u.meanZero

theorem mem_h1MeanZeroGraphClosedSubmodule_iff_exists_h1MeanZeroFunction
    (z : ScalarL2 U × HilbertVectorL2 U) :
    z ∈ h1MeanZeroGraphClosedSubmodule (U := U) ↔
      ∃ u : H1MeanZeroFunction U, u.toScalarL2 = z.1 ∧ u.gradToHilbertVectorL2 = z.2 := by
  constructor
  · intro hz
    have hz' := (mem_h1MeanZeroGraphClosedSubmodule_iff (U := U) z).mp hz
    rcases (mem_h1GraphClosedSubmodule_iff_exists_h1Function (U := U) z).mp hz'.1 with
      ⟨u, hval, hgrad⟩
    have hmean :
        MeanZeroOn U u.toFun := by
      have hInt :
          scalarIntegralCLM (U := U) u.toScalarL2 = ∫ x in U, u x ∂MeasureTheory.volume := by
        calc
          scalarIntegralCLM (U := U) u.toScalarL2 = ∫ x in U, u.toScalarL2 x ∂MeasureTheory.volume := by
            exact scalarIntegralCLM_apply (U := U) u.toScalarL2
          _ = ∫ x in U, u x ∂MeasureTheory.volume := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards [u.coeFn_toScalarL2] with x hu
                rw [hu]
      calc
        ∫ x in U, u x ∂MeasureTheory.volume = scalarIntegralCLM (U := U) u.toScalarL2 := by
              simpa using hInt.symm
        _ = scalarIntegralCLM (U := U) z.1 := by rw [hval]
        _ = 0 := hz'.2
    exact ⟨⟨u, hmean⟩, hval, hgrad⟩
  · rintro ⟨u, hval, hgrad⟩
    have hz :
        z = (u.toScalarL2, u.gradToHilbertVectorL2) := by
      cases z
      simp_all
    rw [hz]
    exact h1MeanZero_pair_mem_h1MeanZeroGraphClosedSubmodule (U := U) u

end MeanZero

end Homogenization
