/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFieldSobolevTime
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientContinuity

@[expose] public section

/-! The classical Euler equation supplies strong evolution in every
Sobolev norm once the actual velocity and pressure-gradient L² jets are
continuous. The advection field and its regularity are constructed here. -/

noncomputable section

namespace EulerSmoothEulerEvolution

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerLpSmoothCoefficientProduct
  EulerMeanSobolevBoundedField EulerSmoothFieldSobolevTime EulerVolterraConvolution
open scoped ContDiff Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def advection (U : K → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n)) (t : K) : SmoothL2Field Space :=
  product (coefficientPath (fun s => (U s).derivative) (continuous_jetLp_derivative U hU)) t (U t)

theorem advection_field (U : K → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n)) (t : K) (x : Space) :
    (advection U hU t).field x = fderiv ℝ (U t).field x ((U t).field x) := by
  rw [advection,product_field,coefficientPath_apply]
  rfl

theorem advection_jet_continuous (U : K → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (advection U hU t).jetLp n) :=
  continuous_product_jet _ U hU n

def rhs (U : K → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
    (G : K → SmoothL2Field Space) (t : K) : SmoothL2Field Space :=
  mapField (-(ContinuousLinearMap.id ℝ Space)) (addField (advection U hU t) (G t))

theorem rhs_field (U : K → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
    (G : K → SmoothL2Field Space) (t : K) (x : Space) :
    (rhs U hU G t).field x = -fderiv ℝ (U t).field x ((U t).field x)-(G t).field x := by
  rw [rhs,mapField_field,addField_field,advection_field,
    neg_apply,ContinuousLinearMap.id_apply]
  abel

theorem rhs_jet_continuous (U : K → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
    (G : K → SmoothL2Field Space) (hG : ∀ n, Continuous (fun t => (G t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (rhs U hU G t).jetLp n) :=
  continuous_jetLp_mapField _ _
    (continuous_jetLp_addField _ _ (advection_jet_continuous U hU) hG) n

variable (T : ℝ) (hT : 0 ≤ T)
  (U G : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
  (hG : ∀ n, Continuous (fun t => (G t).jetLp n))

theorem sobolev_evolution
    (hd : ∀ t (ht : t ∈ Ioo 0 T) x,
      HasDerivAt (fun r => (U (projIcc 0 T hT r)).field x)
        (-fderiv ℝ (U ⟨t,ht.1.le,ht.2.le⟩).field x ((U ⟨t,ht.1.le,ht.2.le⟩).field x)-
          (G ⟨t,ht.1.le,ht.2.le⟩).field x) t)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath U hU q))
      (sobolevPath (rhs U hU G) (rhs_jet_continuous U hU G hG) q t)
      (Icc (0 : ℝ) T) t := by
  apply sobolevPath_hasDerivWithinAt T hT U (rhs U hU G) hU (rhs_jet_continuous U hU G hG)
  intro r hr x
  rw [rhs_field]
  exact hd r hr x

theorem pointwise_time_derivative_of_classical
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (hmatch : ∀ (t : Icc (0 : ℝ) T) x, u (t,x)=(U t).field x)
    (hgradient : ∀ (t : Icc (0 : ℝ) T) x, gradient (fun y => p (t,y)) x=(G t).field x)
    (hdiff : ∀ t ∈ Ioo 0 T, ∀ x, DifferentiableAt ℝ u (t,x))
    (heuler : ∀ t ∈ Ioo 0 T, ∀ x, EulerLagrangian.momentumResidual u p (t,x)=0)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    HasDerivAt (fun r => (U (projIcc 0 T hT r)).field x)
      (-fderiv ℝ (U ⟨t,ht.1.le,ht.2.le⟩).field x ((U ⟨t,ht.1.le,ht.2.le⟩).field x)-
        (G ⟨t,ht.1.le,ht.2.le⟩).field x) t := by
  let s : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
  have hu := (hdiff t ht x).hasFDerivAt
  have hv := hu.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hs : (fun y => u (t,y))=(U s).field := funext (hmatch s)
  have hx : fderiv ℝ u (t,x) (0,(U s).field x) =
      fderiv ℝ (U s).field x ((U s).field x) := by
    have h := (hu.comp x (hasFDerivAt_prodMk_right t x)).fderiv
    simp only [Function.comp_def] at h
    rw [hs] at h
    exact (congrArg (fun A : Space →L[ℝ] Space => A ((U s).field x)) h).symm
  have he := heuler t ht x
  change fderiv ℝ u (t,x) (1,u (t,x))+gradient (fun y => p (t,y)) x=0 at he
  have hp : ((1 : ℝ),u (t,x)) = (1,0)+(0,u (t,x)) := by simp
  rw [hp,map_add,hmatch s x,hx,hgradient s x] at he
  have htval : fderiv ℝ u (t,x) (1,0) =
      -fderiv ℝ (U s).field x ((U s).field x)-(G s).field x := by
    have h := eq_neg_of_add_eq_zero_left (show fderiv ℝ u (t,x) (1,0)+
        (fderiv ℝ (U s).field x ((U s).field x)+(G s).field x)=0 from by
      simpa only [add_assoc] using he)
    rw [h]
    abel
  have hv' : HasDerivAt (fun r => u (r,x))
      (-fderiv ℝ (U s).field x ((U s).field x)-(G s).field x) t := by
    simpa only [Function.comp_def,id_eq,htval] using hv
  apply hv'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
  exact (hmatch ⟨r,hr.1.le,hr.2.le⟩ x).symm

theorem sobolev_evolution_of_classical
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (hmatch : ∀ (t : Icc (0 : ℝ) T) x, u (t,x)=(U t).field x)
    (hgradient : ∀ (t : Icc (0 : ℝ) T) x, gradient (fun y => p (t,y)) x=(G t).field x)
    (hdiff : ∀ t ∈ Ioo 0 T, ∀ x, DifferentiableAt ℝ u (t,x))
    (heuler : ∀ t ∈ Ioo 0 T, ∀ x, EulerLagrangian.momentumResidual u p (t,x)=0)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath U hU q))
      (sobolevPath (rhs U hU G) (rhs_jet_continuous U hU G hG) q t)
      (Icc (0 : ℝ) T) t :=
  sobolev_evolution T hT U G hU hG
    (pointwise_time_derivative_of_classical T hT U G u p hmatch hgradient hdiff heuler) q t

end EulerSmoothEulerEvolution
