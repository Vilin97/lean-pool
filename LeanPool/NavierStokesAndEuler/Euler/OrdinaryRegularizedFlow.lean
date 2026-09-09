/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizedEquation
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryStrongTime
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

@[expose] public section

/-! The regularized L² flow has genuine smooth spatial representatives,
continuous jets of every order, and its true time derivative. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution EulerContinuousTimeIntegral Finset
open scoped ContDiff Topology

namespace SmoothingOperator

variable (S : SmoothingOperator)

def rhs (u : L2) : SmoothL2Field Space :=
  fieldNeg (S.field (advectionField (S.field u) (S.field u)).toLp)

theorem rhs_toLp (u : L2) : (S.rhs u).toLp=S.quadratic u u := by
  simp only [rhs,toLp_fieldNeg,field_toLp,quadratic_apply]

theorem rhs_continuous {K : Type*} [TopologicalSpace K] (u : K → L2)
    (hu : Continuous u) (n : ℕ) : Continuous (fun t => (S.rhs (u t)).jetLp n) := by
  apply continuous_jetLp_mapField
  apply S.field_jet_continuous
  exact (S.advection.continuous.comp hu).clm_apply hu

end SmoothingOperator

structure RegularizedEvolution (S : SmoothingOperator) (T : ℝ) (hT : 0 ≤ T) where
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => (velocity (projIcc 0 T hT r)).toLp)
      (S.quadratic (velocity ⟨t,ht.1.le,ht.2.le⟩).toLp (velocity ⟨t,ht.1.le,ht.2.le⟩).toLp) t

namespace RegularizedEvolution

variable {S : SmoothingOperator} {T : ℝ} {hT : 0 ≤ T} (U : RegularizedEvolution S T hT)

def derivative (t : Icc (0 : ℝ) T) : SmoothL2Field Space := S.rhs (U.velocity t).toLp

theorem derivative_continuous (n : ℕ) : Continuous (fun t => (U.derivative t).jetLp n) :=
  S.rhs_continuous _ (fieldPath U.velocity U.velocity_continuous).continuous n

theorem pointwise_time (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun r => (U.velocity (projIcc 0 T hT r)).field x)
      ((U.derivative t).field x) (Icc (0 : ℝ) T) t := by
  apply pointwise_derivative_of_l2 T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous _ t x
  intro r hr
  simpa only [derivative,SmoothingOperator.rhs_toLp] using U.time_law r hr

theorem l2_time (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (U.velocity (projIcc 0 T hT r)).toLp)
      (U.derivative t).toLp (Icc (0 : ℝ) T) t := by
  have h := ordinaryWord_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
    (fun r hr x => (U.pointwise_time ⟨r,hr.1.le,hr.2.le⟩ x).hasDerivAt (Icc_mem_nhds hr.1 hr.2))
    (n := 0) Fin.elim0 t
  simpa only [wordField_zero] using h

end RegularizedEvolution

namespace SmoothingOperator

variable (S : SmoothingOperator) (T : ℝ) (hT : 0 ≤ T)

theorem exists_smooth (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∃ U : RegularizedEvolution S T hT, U.velocity ⟨0,le_rfl,hT⟩=A := by
  obtain ⟨u,hu0,hu,_huNorm⟩ := S.exists_global A.toLp
  have huc : Continuous u := (show Differentiable ℝ u from fun t => (hu
    t).differentiableAt).continuous
  let a : C(Icc (0 : ℝ) T,L2) :=
    ⟨fun t => S.advection (u t) (u t),
      (S.advection.continuous.comp (huc.comp continuous_subtype_val)).clm_apply
        (huc.comp continuous_subtype_val)⟩
  let z : C(Icc (0 : ℝ) T,L2) := -integral T hT a
  let v : Icc (0 : ℝ) T → SmoothL2Field Space := fun t => addField A (S.field (z t))
  have hv : ∀ t, (v t).toLp=u t := by
    intro t
    have he := eq_initial_add_integral T hT
      ((-S.op).compLeftContinuous ℝ (Icc (0 : ℝ) T) a) u
      (fun s => by
        change HasDerivWithinAt u (-S.op (S.advection (u s) (u s))) _ _
        exact (hu (s : ℝ)).hasDerivWithinAt) t
    have hi : integral T hT ((-S.op).compLeftContinuous ℝ (Icc (0 : ℝ) T) a) t=
        S.op (z t) := by
      change (∫ r in (0 : ℝ)..(t : ℝ), (-S.op) (extendPath T hT a r))=S.op (z t)
      rw [(-S.op).intervalIntegral_comp_comm
        ((extendPath_continuous T hT a).intervalIntegrable 0 t)]
      change -S.op (realIntegral T hT a t)=S.op (-realIntegral T hT a t)
      rw [map_neg]
    rw [hu0,hi] at he
    simpa only [v,toLp_addField,field_toLp] using he.symm
  have hvcont : ∀ n, Continuous (fun t => (v t).jetLp n) :=
    fun n => continuous_jetLp_addField _ _ (fun _ => continuous_const)
      (S.field_jet_continuous z z.continuous) n
  have hv0 : v ⟨0,le_rfl,hT⟩=A := by
    apply smoothField_eq_of_toLp_eq
    rw [hv,hu0]
  refine ⟨{ velocity := v
            velocity_continuous := hvcont
            solenoidal := fun t => ?_
            time_law := fun t ht => ?_ },hv0⟩
  · simpa only [v,toLp_addField,field_toLp] using solenoidalSpace.add_mem hA (S.solenoidal (z t))
  · simp only [hv]
    have he : (fun r => u (projIcc 0 T hT r : ℝ)) =ᶠ[𝓝 t] u := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      simp only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1.le,hr.2.le⟩)]
    exact (hu t).congr_of_eventuallyEq he

end SmoothingOperator
end EulerOrdinarySobolev
