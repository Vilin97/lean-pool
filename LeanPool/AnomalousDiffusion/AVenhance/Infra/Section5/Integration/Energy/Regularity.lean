/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.TimeDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.AdvDiffOp

/-! # Joint regularity of the spatial derivatives of a jointly `C²` function

For `v` jointly `C²` on `[0,∞) × ℝ²` the forcing `advDiffOp b κ v` is jointly continuous on
`(0,∞) × ℝ²` (whenever the drift `b` is), and the spatial gradient of a jointly `C¹` function is
jointly continuous up to `t = 0`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.Energy

open AVenhance

/-- The slice derivative of a jointly `C¹` function is the within-derivative in the spatial
direction. -/
theorem fderiv_slice_eq_fderivWithin_one {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ 1 (Function.uncurry T) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (x v : Vec 2) :
    fderiv ℝ (T t) x v =
      fderivWithin ℝ (Function.uncurry T) (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x) (0, v) := by
  have hp : (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := ⟨ht, mem_univ _⟩
  have hdiff : DifferentiableWithinAt ℝ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x) :=
    (hT.differentiableOn (by simp)) _ hp
  have hmaps : MapsTo (fun y : Vec 2 => (t, y)) Set.univ (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    fun y _ => ⟨ht, mem_univ _⟩
  have hcomp := hdiff.hasFDerivWithinAt.comp x (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt
    hmaps
  have hat : HasFDerivAt (T t)
      ((fderivWithin ℝ (Function.uncurry T) (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) x :=
    hcomp.hasFDerivAt Filter.univ_mem
  rw [hat.fderiv]
  simp

/-- The joint spatial gradient of a jointly `C¹` function is continuous up to `t = 0`. -/
theorem spaceGrad_continuousOn_one {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ 1 (Function.uncurry T) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hs : UniqueDiffOn ℝ (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ
  have hc := hT.continuousOn_fderivWithin hs le_rfl
  refine continuousOn_pi.mpr fun i => ?_
  have hi := hc.clm_apply (continuousOn_const (c := ((0 : ℝ), basisVec i)))
  refine hi.congr ?_
  intro p hp
  exact fderiv_slice_eq_fderivWithin_one hT hp.1 p.2 (basisVec i)

/-- Fréchet derivative of a spatial slice of a function differentiable at `(s,x)`. -/
theorem fderiv_slice_apply {A : ℝ × Vec 2 → ℝ} {s : ℝ} {x : Vec 2}
    (hA : DifferentiableAt ℝ A (s, x)) (w : Vec 2) :
    fderiv ℝ (fun y => A (s, y)) x w = fderiv ℝ A (s, x) (0, w) := by
  have h : HasFDerivAt (fun y => A (s, y))
      ((fderiv ℝ A (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) x :=
    hA.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  rw [h.fderiv]
  simp

/-- The forcing `advDiffOp b κ v` is jointly continuous on `(0,∞) × ℝ²` when `v` is jointly `C²`
and the drift is continuous. -/
theorem continuousOn_advDiffOp {b : ℝ → Vec 2 → Vec 2}
    (hb : Continuous (Function.uncurry b)) (κ : ℝ) {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ 2 (Function.uncurry v) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => advDiffOp b κ v p.1 p.2) classicalPositiveTimeDomain := by
  have hU := isOpen_positiveTimeDomain
  have hV : ContDiffOn ℝ 2 (Function.uncurry v) classicalPositiveTimeDomain :=
    hv.mono (by
      intro p hp
      simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
      exact ⟨le_of_lt hp.1, trivial⟩)
  have hV1 : ContDiffOn ℝ 1 (Function.uncurry v) classicalPositiveTimeDomain :=
    hV.of_le (by norm_num)
  have hdV : ContDiffOn ℝ 1 (fun p => fderiv ℝ (Function.uncurry v) p)
      classicalPositiveTimeDomain := hV.fderiv_of_isOpen hU (by norm_num)
  let A : Fin 2 → ℝ × Vec 2 → ℝ := fun i p =>
    fderiv ℝ (Function.uncurry v) p ((0 : ℝ), basisVec i)
  have hA : ∀ i, ContDiffOn ℝ 1 (A i) classicalPositiveTimeDomain := fun i =>
    hdV.clm_apply contDiffOn_const
  have hAc : ∀ i, ContinuousOn (A i) classicalPositiveTimeDomain := fun i =>
    (hA i).continuousOn
  have hdA : ∀ i, ContinuousOn (fun p => fderiv ℝ (A i) p ((0 : ℝ), basisVec i))
      classicalPositiveTimeDomain := fun i =>
    ((hA i).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hcont : ContinuousOn (fun p : ℝ × Vec 2 =>
      fderiv ℝ (Function.uncurry v) p ((1 : ℝ), (0 : Vec 2)) -
        κ * ∑ i : Fin 2, fderiv ℝ (A i) p ((0 : ℝ), basisVec i) +
        ∑ j : Fin 2, b p.1 p.2 j * A j p) classicalPositiveTimeDomain := by
    refine (continuousOn_timePartial_one hV1).sub (continuousOn_const.mul ?_) |>.add ?_
    · exact continuousOn_finsetSum _ fun i _ => hdA i
    · refine continuousOn_finsetSum _ fun j _ => ?_
      have : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2 j) :=
        (continuous_apply j).comp hb
      exact this.continuousOn.mul (hAc j)
  refine hcont.congr ?_
  intro p hp
  obtain ⟨s, x⟩ := p
  have hs : 0 < s := hp.1
  have hdiffAt : DifferentiableAt ℝ (Function.uncurry v) (s, x) :=
    ((hV1.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  have hgrad : ∀ y i, spaceGrad (v s) y i = A i (s, y) := by
    intro y i
    have hyp : (s, y) ∈ classicalPositiveTimeDomain := by simp [classicalPositiveTimeDomain, hs]
    have hd : DifferentiableAt ℝ (Function.uncurry v) (s, y) :=
      ((hV1.contDiffAt (hU.mem_nhds hyp)).differentiableAt (by simp))
    exact fderiv_slice_apply (A := Function.uncurry v) hd (basisVec i)
  have hlap : spaceLap (v s) x = ∑ i : Fin 2, fderiv ℝ (A i) (s, x) ((0 : ℝ), basisVec i) := by
    unfold spaceLap
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfun : (fun y => spaceGrad (v s) y i) = fun y => A i (s, y) := by
      funext y
      exact hgrad y i
    change fderiv ℝ (fun y => spaceGrad (v s) y i) x (basisVec i) = _
    rw [hfun]
    exact fderiv_slice_apply (A := A i)
      (((hA i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) (basisVec i)
  simp only [advDiffOp, hlap, vecDot, hgrad]
  rw [deriv_timeSection_eq hV1 hs x]

end AVenhance.Infra.Section5.Integration.Energy

end
