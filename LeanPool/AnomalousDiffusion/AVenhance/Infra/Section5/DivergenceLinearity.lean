/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Differentiability-based linearity of the classical divergence. -/

@[expose] public section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

theorem DivergenceLinearity.vecDiv_eq_fderivAt
    {V : Vec 2 → Vec 2} {x : Vec 2} {L : Vec 2 →L[ℝ] Vec 2}
    (hV : HasFDerivAt V L x) :
    vecDiv V x = ∑ i : Fin 2, (L (basisVec i)) i := by
  unfold vecDiv
  apply Finset.sum_congr rfl
  intro i hi
  have hcoord : HasFDerivAt (fun y => V y i)
      ((ContinuousLinearMap.proj i).comp L) x := by
    exact (ContinuousLinearMap.proj i).hasFDerivAt.comp x hV
  rw [spaceGrad, hcoord.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- Divergence is additive under explicit local derivative hypotheses. -/
theorem vecDiv_add_of_hasFDerivAt
    {V W : Vec 2 → Vec 2} {x : Vec 2}
    {LV LW : Vec 2 →L[ℝ] Vec 2}
    (hV : HasFDerivAt V LV x) (hW : HasFDerivAt W LW x) :
    vecDiv (fun y => V y + W y) x = vecDiv V x + vecDiv W x := by
  change vecDiv (V + W) x = _
  rw [DivergenceLinearity.vecDiv_eq_fderivAt (hV.add hW), DivergenceLinearity.vecDiv_eq_fderivAt hV,
    DivergenceLinearity.vecDiv_eq_fderivAt hW]
  simp [Finset.sum_add_distrib]

/-- A finite weighted sum may be passed through the divergence when each
summand has the displayed derivative at the point. -/
theorem vecDiv_finite_weighted_sum
    {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (F : ι → Vec 2 → Vec 2) (x : Vec 2)
    {LF : ι → Vec 2 →L[ℝ] Vec 2}
    (hF : ∀ i ∈ S, HasFDerivAt (F i) (LF i) x) :
    vecDiv (fun y => ∑ i ∈ S, c i • F i y) x =
      ∑ i ∈ S, c i * vecDiv (F i) x := by
  classical
  let V : Vec 2 → Vec 2 := fun y => ∑ i ∈ S, c i • F i y
  let LV : Vec 2 →L[ℝ] Vec 2 := ∑ i ∈ S, c i • LF i
  have hV : HasFDerivAt V LV x := by
    dsimp [V, LV]
    have hfun : (fun y => ∑ i ∈ S, c i • F i y) =
        ∑ i ∈ S, (fun y => c i • F i y) := by
      funext y
      simp
    rw [hfun]
    apply HasFDerivAt.sum
    intro i hi
    exact (hF i hi).const_smul (c i)
  rw [DivergenceLinearity.vecDiv_eq_fderivAt hV]
  have hformula :
      (∑ j : Fin 2, (LV (basisVec j)) j) =
        ∑ i ∈ S, c i * vecDiv (F i) x := by
    have hdiv (i : ι) (hi : i ∈ S) :
        vecDiv (F i) x = ∑ j : Fin 2, (LF i (basisVec j)) j :=
      DivergenceLinearity.vecDiv_eq_fderivAt (hF i hi)
    change (∑ j ∈ (Finset.univ : Finset (Fin 2)),
        (∑ i ∈ S, c i • LF i) (basisVec j) j) = _
    simp only [sum_apply, Finset.sum_apply, smul_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Fin.sum_univ_two]
    have hdiv' (i : ι) (hi : i ∈ S) :
        vecDiv (F i) x = (LF i (basisVec 0)) 0 + (LF i (basisVec 1)) 1 := by
      simpa only [Fin.sum_univ_two] using hdiv i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiv' i hi]
    ring
  exact hformula

end AVenhance.Infra.Section5
