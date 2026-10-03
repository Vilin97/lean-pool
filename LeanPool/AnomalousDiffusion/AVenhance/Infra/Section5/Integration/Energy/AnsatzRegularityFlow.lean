/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite

/-! # Regularity of the ansatz `θTilde_m`: flow ingredients

Joint `C^∞` regularity of the flow slices `X_{m-1,l}`, `X⁻¹_{m-1,l}`, the partial
derivatives of the flow, and the chain rule for the transported gradient
`(t,x) ↦ ∇(T(t)∘X_{m-1,l}(t,·))(X⁻¹_{m-1,l}(t,x))` written as
`∑_j ∂_i X^j(t, X⁻¹(t,x)) ∂_j T(t,x)`, jointly `C^∞` on `Ici 0 ×ˢ univ`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem AnsatzRegularityFlow.ansFlowSmooth (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    Infra.Flow.SmoothPeriodicField (streamVel (Φ (m - 1))) :=
  Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)

theorem AnsatzRegularityFlow.ansFlowIsFlow (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    IsFlow (streamVel (Φ (m - 1)))
      (flow (streamVel (Φ (m - 1)))
        (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz) :=
  flow_isFlow _ _ _

/-- The forward flow slice is jointly `C^∞` in target time and position. -/
theorem xFlow_joint_contDiff_infty (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => I.xFlow hΦ m l p.1 p.2) := by
  have hmain := Infra.Flow.flow_joint_contDiff_infty (AnsatzRegularityFlow.ansFlowSmooth I hΦ m)
      (AnsatzRegularityFlow.ansFlowIsFlow I hΦ m)
  have hembed : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, p.2, (l : ℝ) * tauPP β I.Λ m)) := by
    fun_prop
  exact hmain.comp hembed

/-- The inverse flow slice is jointly `C^∞` in target time and position. -/
theorem xFlowInv_joint_contDiff_infty (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => I.xFlowInv hΦ m l p.1 p.2) := by
  have hmain := Infra.Flow.flow_inverse_joint_contDiff_infty (AnsatzRegularityFlow.ansFlowSmooth I
      hΦ m)
    (AnsatzRegularityFlow.ansFlowIsFlow I hΦ m)
  have hembed : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, p.2, (l : ℝ) * tauPP β I.Λ m)) := by
    fun_prop
  exact hmain.comp hembed

/-! ### Partial derivatives of a jointly smooth vector field -/

/-- Entry `(i,j)` of the spatial Jacobian of a slice `y ↦ F(t,y)`, as a partial derivative of the
joint map. -/
theorem gradMatrix_slice_eq {F : ℝ × Vec 2 → Vec 2} (hF : ContDiff ℝ ∞ F) (t : ℝ) (y : Vec 2)
    (i j : Fin 2) :
    gradMatrix (fun z => F (t, z)) y i j =
      fderiv ℝ (fun p => F p j) (t, y) (0, basisVec i) := by
  have hFj : ContDiff ℝ ∞ (fun p => F p j) := (contDiff_apply ℝ ℝ j).comp hF
  have hd : HasFDerivAt (fun p => F p j) (fderiv ℝ (fun p => F p j) (t, y)) (t, y) :=
    (hFj.differentiable (by simp) (t, y)).hasFDerivAt
  have hc := hd.comp y (hasFDerivAt_prodMk_right t y)
  have hfun : (fun z => F (t, z) j) = (fun p => F p j) ∘ (fun z => (t, z)) := rfl
  simp only [gradMatrix, Matrix.of_apply, spaceGrad]
  rw [hfun, hc.fderiv]
  rfl

/-- Every partial derivative of a `C^∞` real function on `ℝ × Vec 2` is `C^∞`. -/
theorem contDiff_partial {G : ℝ × Vec 2 → ℝ} (hG : ContDiff ℝ ∞ G) (v : ℝ × Vec 2) :
    ContDiff ℝ ∞ (fun q => fderiv ℝ G q v) :=
  (hG.fderiv_right (by simp)).clm_apply contDiff_const

/-- The spatial gradient of a slice of a function that is `C¹` on a set `s` containing the whole
slice is the partial derivative of the joint map within `s`. -/
theorem spaceGrad_slice_eq {F : ℝ × Vec 2 → ℝ} {s : Set (ℝ × Vec 2)} (t : ℝ) (x : Vec 2)
    (hs : ∀ y, (t, y) ∈ s) (hF : DifferentiableWithinAt ℝ F s (t, x)) (j : Fin 2) :
    spaceGrad (fun y => F (t, y)) x j = fderivWithin ℝ F s (t, x) (0, basisVec j) := by
  have hd : HasFDerivWithinAt F (fderivWithin ℝ F s (t, x)) s (t, x) := hF.hasFDerivWithinAt
  have hc := hd.comp x (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt (s := Set.univ)
    (fun y _ => hs y)
  rw [hasFDerivWithinAt_univ] at hc
  simp only [spaceGrad]
  rw [show (fun y => F (t, y)) = F ∘ (fun y => (t, y)) from rfl, hc.fderiv]
  rfl

/-! ### The transported gradient -/

/-- A function that is `C^∞` on `Ici 0 ×ˢ univ` is `C^∞` on each slice at a nonnegative time. -/
theorem slice_contDiff_of_contDiffOn {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (T t) := by
  have h : ContDiffOn ℝ ∞ ((fun p : ℝ × Vec 2 => T p.1 p.2) ∘ (fun y : Vec 2 => (t, y)))
      Set.univ :=
    hT.comp (contDiff_prodMk_right t).contDiffOn (fun y _ => ⟨ht, trivial⟩)
  exact contDiffOn_univ.mp h

/-- `∇(T(t)∘X_{m-1,l}(t,·))(X⁻¹_{m-1,l}(t,x))` is, jointly in `(t,x)`, a `C^∞` function on
`Ici 0 ×ˢ univ`, whenever `T` is. -/
theorem transportedGrad_contDiffOn (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 =>
      spaceGrad (fun y => T p.1 (I.xFlow hΦ m l p.1 y)) (I.xFlowInv hΦ m l p.1 p.2) i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  set s : Set (ℝ × Vec 2) := Set.Ici (0 : ℝ) ×ˢ Set.univ with hs
  have hsu : UniqueDiffOn ℝ s := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ
  have hXF := xFlow_joint_contDiff_infty I hΦ m l
  have hXI := xFlowInv_joint_contDiff_infty I hΦ m l
  have hpair : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, I.xFlowInv hΦ m l p.1 p.2)) :=
    contDiff_fst.prodMk hXI
  set E : ℝ × Vec 2 → ℝ := fun p => ∑ j : Fin 2,
    fderiv ℝ (fun q : ℝ × Vec 2 => I.xFlow hΦ m l q.1 q.2 j) (p.1, I.xFlowInv hΦ m l p.1 p.2)
        (0, basisVec i) *
      fderivWithin ℝ (fun p : ℝ × Vec 2 => T p.1 p.2) s p (0, basisVec j) with hE
  have hEsm : ContDiffOn ℝ ∞ E s := by
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ ?_
    · have hXj : ContDiff ℝ ∞ (fun q : ℝ × Vec 2 => I.xFlow hΦ m l q.1 q.2 j) :=
        (contDiff_apply ℝ ℝ j).comp hXF
      exact ((contDiff_partial hXj (0, basisVec i)).comp hpair).contDiffOn
    · exact ((hT.fderivWithin hsu (by simp)).clm_apply contDiffOn_const)
  refine hEsm.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  have ht' : 0 ≤ t := ht
  have hslice := slice_contDiff_of_contDiffOn hT ht'
  have hXslice : ContDiff ℝ ∞ (I.xFlow hΦ m l t) := hXF.comp (contDiff_prodMk_right t)
  have hxx : I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x :=
    (LeftToShow.xFlowDiffeo I hΦ m l t).right_inv x
  have hfT : HasFDerivAt (T t) (fderiv ℝ (T t) (I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x)))
      (I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x)) :=
    (hslice.differentiable (by simp) _).hasFDerivAt
  have hfX : HasFDerivAt (I.xFlow hΦ m l t)
      (fderiv ℝ (I.xFlow hΦ m l t) (I.xFlowInv hΦ m l t x)) (I.xFlowInv hΦ m l t x) :=
    (hXslice.differentiable (by simp) _).hasFDerivAt
  have hchain := spaceGrad_comp_eq_gradMatrix_mul hfT hfX i
  simp only [hE]
  rw [hchain]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hxx]
  congr 1
  · exact gradMatrix_slice_eq hXF t _ i j
  · have := spaceGrad_slice_eq (F := fun p : ℝ × Vec 2 => T p.1 p.2) (s := s) t x
      (fun y => ⟨ht', trivial⟩) (hT.differentiableOn (by simp) (t, x) ⟨ht', trivial⟩) j
    exact this

end AVenhance.Infra.Section5.Integration
