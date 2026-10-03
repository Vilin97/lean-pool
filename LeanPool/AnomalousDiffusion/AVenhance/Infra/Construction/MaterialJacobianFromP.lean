/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialGoalAllOrders
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialFlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowMixedEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowJacobianC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixTransport

/-! The material Jacobian field follows from the all-order velocity-gradient
jets and the spatial flow displays. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

open AVenhance.Infra.Section4

/-- Translate the time coordinate while fixing the spatial coordinate. -/
def MaterialJacobianFromP.materialTimeShift (s : ℝ) (z : AmnrSpace) : AmnrSpace :=
  ((s, (0 : Vec 2)) : AmnrSpace) + z

theorem MaterialJacobianFromP.amnrOp_timeShift {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (s : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : Option (Fin 2)) (z : AmnrSpace) :
    amnrOp (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) d
      (fun y => f (MaterialJacobianFromP.materialTimeShift s y)) z =
        amnrOp b d f (MaterialJacobianFromP.materialTimeShift s z) := by
  let T := MaterialJacobianFromP.materialTimeShift s
  have hT : HasFDerivAt T (ContinuousLinearMap.id ℝ AmnrSpace) z := by
    have hid : HasFDerivAt (fun y : AmnrSpace => y)
        (ContinuousLinearMap.id ℝ AmnrSpace) z := hasFDerivAt_id z
    have h := hid.const_add ((s, (0 : Vec 2)) : AmnrSpace)
    have hfun : T = fun y : AmnrSpace => ((s, (0 : Vec 2)) : AmnrSpace) + y := by
      funext y
      simp [T, MaterialJacobianFromP.materialTimeShift]
    rw [hfun]
    exact h
  have hcomp := (hf.differentiable (by simp) (T z)).hasFDerivAt.comp z hT
  have hderiv : fderiv ℝ (f ∘ T) z = fderiv ℝ f (T z) := by
    simpa [Function.comp_def] using hcomp.fderiv
  have hdir : amnrDirection (fun y => b (T y)) d z =
      amnrDirection b d (T z) := by
    cases d <;> simp [amnrDirection, T]
  unfold amnrOp
  rw [show (fun y => f (T y)) = f ∘ T by rfl, hderiv, hdir]

theorem MaterialJacobianFromP.amnrWord_timeShift {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (s : ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Option (Fin 2))) :
    amnrWord (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) w
      (fun y => f (MaterialJacobianFromP.materialTimeShift s y)) =
        fun z => amnrWord b w f (MaterialJacobianFromP.materialTimeShift s z) := by
  induction w with
  | nil => rfl
  | cons d w ih =>
      have htail : ContDiff ℝ (⊤ : ℕ∞) (amnrWord b w f) :=
        contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ
          hb.contDiffOn hf.contDiffOn w)
      funext z
      change amnrOp (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) d
        (amnrWord (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) w
          (fun y => f (MaterialJacobianFromP.materialTimeShift s y))) z = _
      rw [ih]
      exact MaterialJacobianFromP.amnrOp_timeShift s htail d z

theorem MaterialJacobianFromP.materialJacobianEntry_transport
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s : ℝ) (i j : Fin 2) :
    ∀ z : AmnrSpace,
      amnrOp (fun y => streamVel (Φ m) (s + y.1) y.2) none
        (fun y => constructionComposedFlowJacobian hseq m s y.1 y.2
          (basisVec j) i) z =
        ∑ q : Fin 2,
          constructionComposedFlowJacobian hseq m s z.1 z.2
            (basisVec j) q *
          amnrVelocityGradient
            (fun y => streamVel (Φ m) (s + y.1) y.2) i q z := by
  intro z
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let bshift : ℝ → Vec 2 → Vec 2 := fun r x => b (s + r) x
  let x₀ : Vec 2 := constructionFlowInv hseq m (s + z.1) z.2 s
  let X : ℝ → Vec 2 := fun r => constructionFlow hseq m (s + r) x₀ s
  let G : ℝ → Vec 2 → ℝ := fun r y =>
    constructionComposedFlowJacobian hseq m s r y (basisVec j) i
  let g : AmnrSpace → ℝ := fun y => G y.1 y.2
  have hφ : IsAdmissibleStream (Φ m) := streamSeq_isAdmissible hseq m
  have hfield : Infra.Flow.SmoothPeriodicField b := smoothPeriodic_streamVel hφ
  have hXflow : IsFlow b (constructionFlow hseq m) := by
    dsimp [b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hXderiv (r : ℝ) : HasDerivAt X (bshift r (X r)) r := by
    have hode := hXflow.2 x₀ s (r + s)
    have htime := hode.comp_add_const r s
    simpa [X, bshift, b, add_comm, add_left_comm, add_assoc] using htime
  have hXz : X z.1 = z.2 := by
    change constructionFlow hseq m (s + z.1)
      (constructionFlowInv hseq m (s + z.1) z.2 s) s = z.2
    exact flowInv_rightInverse b hφ.vel_continuous hφ.vel_lipschitz
      (s + z.1) s z.2
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar G) := by
    have h := constructionComposedFlowJacobian_joint_contDiff (hseq := hseq) m s
    have hcol := h.clm_apply
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : AmnrSpace => basisVec j))
    exact (contDiff_pi.1 hcol) i
  have hbshift : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector bshift) := by
    have hb : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b) := hfield.smooth
    have hb' : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ × Vec 2 => b y.1 y.2) := by
      convert hb using 1
      funext y
      rfl
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ × Vec 2 => b (s + y.1) y.2)
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ × Vec 2 => (s + y.1, y.2)) := by fun_prop
    exact hb'.comp hmap
  have hGslice : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar G) := hGsmooth
  have hmat := constructionMaterialDerivative_eq_deriv_pullback
    (b := bshift) (F := G) hGslice z.1 (hXderiv z.1)
  have hmaterial : constructionMaterialDerivative bshift G z.1 z.2 =
      amnrOp (constructionJointVector bshift) none (constructionJointScalar G) z := by
    rw [constructionMaterialDerivative_eq_joint_fderiv hGslice]
    rfl
  have hpullEq (r : ℝ) : G r (X r) =
      constructionFlowJacobian hseq m r s x₀ (basisVec j) i := by
    have hflowId : constructionFlowInv hseq m (s + r)
        (constructionFlow hseq m (s + r) x₀ s) s = x₀ := by
      calc
        _ = constructionFlow hseq m s
            (constructionFlow hseq m (s + r) x₀ s) (s + r) := rfl
        _ = constructionFlow hseq m s x₀ s := by
          exact Infra.Flow.flow_group_law b hφ.vel_lipschitz hXflow x₀ s (s + r) s
        _ = x₀ := hXflow.1 x₀ s
    simp [G, X, constructionComposedFlowJacobian, hflowId]
  have htimepull := constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
    (hseq := hseq) m s x₀ i j 1 z.1
  have htimeDerivative : iteratedTimeDerivative 1
      (fun r => constructionFlowJacobian hseq m r s x₀ (basisVec j) i) z.1 =
      Infra.Flow.jointSpatialFDeriv b (s + z.1) z.2
        (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i := by
    have hvar := amnrFlowJacobianEntry_hasDerivAt_time hfield hXflow s
      (s + z.1) x₀ j i
    have hvar' : HasDerivAt
        (fun r => amnrFlowJacobianEntry (constructionFlow hseq m) s j i (r, x₀))
        ((Infra.Flow.jointSpatialFDeriv b (s + z.1)
          (constructionFlow hseq m (s + z.1) x₀ s)
          (fderiv ℝ (fun y => constructionFlow hseq m (s + z.1) y s)
            x₀ (basisVec j))) i) (z.1 + s) := by
      convert hvar using 1; ring
    have hshifted := hvar'.comp_add_const z.1 s
    have hentry : (fun q : ℝ =>
        amnrFlowJacobianEntry (constructionFlow hseq m) s j i (q + s, x₀)) =
        fun q => constructionFlowJacobian hseq m q s x₀ (basisVec j) i := by
      funext q
      simp [amnrFlowJacobianEntry, constructionFlowJacobian, constructionFlow,
        add_comm]
    have hshifted' := hshifted.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => (congrFun hentry q).symm)
    have hpoint := hshifted'.deriv
    have hflowpt : constructionFlow hseq m (s + z.1) x₀ s = z.2 := by
      simpa [X] using hXz
    rw [hflowpt] at hpoint
    simpa [iteratedTimeDerivative, b, constructionFlowJacobian,
      Infra.Flow.jointSpatialFDeriv, add_comm, add_left_comm] using hpoint
  have hderivpoint :
      constructionMaterialDerivative bshift G z.1 z.2 =
      Infra.Flow.jointSpatialFDeriv b (s + z.1) z.2
          (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i := by
    calc
      constructionMaterialDerivative bshift G z.1 z.2 =
          constructionMaterialIterate bshift 1 G z.1 z.2 := rfl
      _ = iteratedTimeDerivative 1
          (fun r => constructionFlowJacobian hseq m r s x₀ (basisVec j) i) z.1 := by
        simpa [bshift, X, hXz] using htimepull
      _ = Infra.Flow.jointSpatialFDeriv b (s + z.1) z.2
          (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i := htimeDerivative
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (b (s + z.1)) := by
    have hb : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b) := hfield.smooth
    have hb' : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ × Vec 2 => b y.1 y.2) := by
      convert hb using 1
      funext y
      rfl
    have hm : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (s + z.1, y)) := by fun_prop
    exact hb'.comp hm
  have hcomponent := AVenhance.Infra.Section5.fderiv_vector_component_eq_sum_gradMatrix
    (F := fun y => b (s + z.1) y) (x := z.2)
    (v := constructionFlowJacobian hseq m z.1 s x₀ (basisVec j))
    (hslice.differentiable (by simp) z.2) i
  have hspatial := Infra.Flow.jointSpatialFDeriv_eq_slice hfield (s + z.1) z.2
  have hcolumn (q : Fin 2) :
      constructionFlowJacobian hseq m z.1 s x₀ (basisVec j) q =
        constructionComposedFlowJacobian hseq m s z.1 z.2 (basisVec j) q := by
    rfl
  change amnrOp (constructionJointVector bshift) none
    (constructionJointScalar G) z = _
  rw [← hmaterial, hderivpoint, hspatial]
  change fderiv ℝ (fun y => b (s + z.1) y) z.2
      (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i = _
  rw [hcomponent]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hcolumn q]
  rfl

theorem MaterialJacobianFromP.materialPureWord_eq_iterate
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) (ell : ℕ) :
    amnrWord (constructionJointVector b) (List.replicate ell none)
      (constructionJointScalar F) =
        constructionJointScalar (constructionMaterialIterate b ell F) := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      change amnrOp (constructionJointVector b) none
          (amnrWord (constructionJointVector b) (List.replicate ell none)
            (constructionJointScalar F)) =
        constructionJointScalar (constructionMaterialIterate b (ell + 1) F)
      rw [ih]
      funext p
      have hiterate := constructionMaterialIterate_joint_contDiff hb hF ell
      have hstep := constructionMaterialDerivative_eq_joint_fderiv
        (b := b) (F := constructionMaterialIterate b ell F) hiterate p.1 p.2
      change fderiv ℝ (constructionJointScalar
        (constructionMaterialIterate b ell F)) p
          (1, b p.1 p.2) = _
      simpa [constructionJointScalar, constructionJointVector,
        constructionMaterialIterate] using hstep.symm

theorem MaterialJacobianFromP.amnrVelocityGradient_timeShift
    {b : AmnrSpace → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (s : ℝ) (i p : Fin 2) (z : AmnrSpace) :
    amnrVelocityGradient (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) i p z =
      amnrVelocityGradient b i p (MaterialJacobianFromP.materialTimeShift s z) := by
  let f : AmnrSpace → ℝ := fun y => b y i
  let bs : AmnrSpace → Vec 2 := fun y => b (MaterialJacobianFromP.materialTimeShift s y)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_apply ℝ ℝ i).comp hb
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (MaterialJacobianFromP.materialTimeShift s) := by
    fun_prop [MaterialJacobianFromP.materialTimeShift]
  have hbs : ContDiff ℝ (⊤ : ℕ∞) bs := hb.comp hmap
  have hshift := MaterialJacobianFromP.amnrOp_timeShift (b := b) s hf (some p) z
  have hdleft : DifferentiableAt ℝ (fun y => bs y i) z := by
    have hdvec : DifferentiableAt ℝ bs z := hbs.differentiable (by simp) z
    simpa only [Function.comp_def] using
      (differentiable_apply i).differentiableAt.comp z hdvec
  have hdright : DifferentiableAt ℝ f (MaterialJacobianFromP.materialTimeShift s z) := by
    have hdvec : DifferentiableAt ℝ b (MaterialJacobianFromP.materialTimeShift s z) :=
      hb.differentiable (by simp) (MaterialJacobianFromP.materialTimeShift s z)
    simpa only [Function.comp_def] using
      (differentiable_apply i).differentiableAt.comp (MaterialJacobianFromP.materialTimeShift s z)
          hdvec
  calc
    amnrVelocityGradient bs i p z = amnrOp bs (some p) (fun y => bs y i) z := by
      symm
      simpa [bs, amnrVelocityGradient] using amnrOp_space hdleft p
    _ = amnrOp b (some p) f (MaterialJacobianFromP.materialTimeShift s z) := hshift
    _ = amnrVelocityGradient b i p (MaterialJacobianFromP.materialTimeShift s z) := by
      simpa [f, amnrVelocityGradient] using amnrOp_space hdright p

/-- Constant controlling the material derivatives of the Section 2 Jacobian. -/
def section2MaterialJacobianConstant (β K : ℝ) : ℝ :=
  (2 : ℝ) ^ (Nstar β + 1) *
    section2MaterialSpatialConstant (2 * Nstar β + 1) *
      (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β

theorem section2MaterialJacobianConstant_ge_one {β K : ℝ} (hK : 1 ≤ K) :
    1 ≤ section2MaterialJacobianConstant β K := by
  have hpow2 : 1 ≤ (2 : ℝ) ^ (Nstar β + 1) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hspatial : 1 ≤ section2MaterialSpatialConstant (2 * Nstar β + 1) := by
    unfold section2MaterialSpatialConstant
    have hs : 0 ≤ ∑ q ∈ Finset.range (2 * Nstar β + 2),
        ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q)) := by positivity
    linarith
  have hcoef : 1 ≤ 1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K := by
    have hp : 0 ≤ (2 : ℝ) ^ (2 * Nstar β + 2) * K := by positivity
    linarith
  have hpow : 1 ≤
      (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := one_le_pow₀ hcoef
  calc
    1 = (1 : ℝ) * 1 * 1 := by ring
    _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
        section2MaterialSpatialConstant (2 * Nstar β + 1) *
          (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by gcongr
    _ = section2MaterialJacobianConstant β K := rfl

private theorem section2_material_jacobian_of_material_levels_CmatGeOne1 :
  ∀ {β K : ℝ},
    1 ≤ K →
      let N := Nstar β;
      let W := 2 * N + 1;
      let R := 1 + (2 : ℝ) ^ (W + 1) * K;
      let Cmat := section2MaterialJacobianConstant β K;
      1 ≤ section2MaterialSpatialConstant W → 1 ≤ R → 1 ≤ Cmat
    := by
  intro β K hK N W R Cmat hCflow hR
  have hpow2 : 1 ≤ (2 : ℝ) ^ (Nstar β + 1) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hpowR : 1 ≤
      (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by
    apply one_le_pow₀
    have hcoef : 0 ≤ (2 : ℝ) ^ (2 * Nstar β + 2) * K := by positivity
    linarith
  have hcf : 1 ≤ section2MaterialSpatialConstant (2 * Nstar β + 1) := by
    unfold section2MaterialSpatialConstant
    have hs : 0 ≤ ∑ q ∈ Finset.range (2 * Nstar β + 2),
        ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q)) := by positivity
    linarith
  have hprod : (1 : ℝ) * 1 * 1 ≤
      (2 : ℝ) ^ (Nstar β + 1) *
        section2MaterialSpatialConstant (2 * Nstar β + 1) *
          (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by
    calc
      _ ≤ (2 : ℝ) ^ (Nstar β + 1) * 1 * 1 := by gcongr
      _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
            section2MaterialSpatialConstant (2 * Nstar β + 1) * 1 := by gcongr
      _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
            section2MaterialSpatialConstant (2 * Nstar β + 1) *
              (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by gcongr
  simpa [Cmat, section2MaterialJacobianConstant] using hprod

private theorem section2_material_jacobian_of_material_levels_Bb1 :
  ∀ {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {K : ℝ},
    MaterialAuxJetLevels I Φ (2 * Nstar β + 1) K (Nstar β) →
      ∀ {m : ℕ} (s t : ℝ) (_ _ : ℕ) (x : Vec 2),
        let N := Nstar β;
        let W := 2 * N + 1;
        let S := (epsilon β I.Λ m)⁻¹;
        let H := a β I.Λ m;
        (ContDiff ℝ ∞ fun (z : AmnrSpace) => streamVel (Φ m) z.1 z.2) →
          let b0 : AmnrSpace → Vec 2 := fun z => streamVel (Φ m) z.1 z.2;
          let bAmnr : AmnrSpace → Vec 2 := fun z => b0 (MaterialJacobianFromP.materialTimeShift s
              z);
          (∀ (p q : Fin 2), ContDiff ℝ ∞ (amnrVelocityGradient b0 p q)) →
            (∀ (p q : Fin 2),
                amnrVelocityGradient bAmnr p q = fun (z : AmnrSpace) =>
                  amnrVelocityGradient b0 p q (MaterialJacobianFromP.materialTimeShift s z)) →
              ∀ (p q : Fin 2) (w : List (Option (Fin 2))),
                IsAmnrMixedWord w →
                  amnrBudget w + 2 ≤ W →
                    |amnrWord bAmnr w (amnrVelocityGradient bAmnr p q) (t, x)| ≤ K * H *
                        amnrWeight S H w
    := by
  intro β I Φ K hlevels m s t n ell x N W S H hb0 b0 bAmnr hgradSmooth hgradShift p q w hw hbudget
  obtain ⟨α, r, rfl⟩ := hw.normalForm
  have hbudget' : α.length + 2 * r + 2 ≤ W := by
    rw [amnrMixedWord_budget] at hbudget
    omega
  have hr : r ≤ N := by omega
  have hWordShift := MaterialJacobianFromP.amnrWord_timeShift (b := b0) s hb0 (hgradSmooth p q)
    (amnrMixedWord α r)
  have hlevel := hlevels.gradient m α r hr hbudget' p q
    (MaterialJacobianFromP.materialTimeShift s (t, x))
  have hwordEq : amnrWord bAmnr (amnrMixedWord α r)
      (amnrVelocityGradient bAmnr p q) (t, x) =
      amnrWord b0 (amnrMixedWord α r)
        (amnrVelocityGradient b0 p q) (MaterialJacobianFromP.materialTimeShift s (t, x)) := by
    rw [hgradShift]
    simpa [bAmnr, b0, MaterialJacobianFromP.materialTimeShift] using congrFun hWordShift (t, x)
  rw [hwordEq]
  have hweight : amnrWeight S H (amnrMixedWord α r) = S ^ α.length * H ^ r := by
    simp [amnrWeight, amnrMixedWord, S, H, Function.comp_def,
      List.map_append, List.map_replicate, List.prod_append,
      List.prod_replicate, inv_pow]
  rw [hweight]
  simpa [S, H, inv_pow, mul_assoc, mul_left_comm, mul_comm] using hlevel

/-- The material-Jacobian display follows from the all-order weighted
material gradient jets and the source spatial flow displays. -/
theorem section2_material_jacobian_of_material_levels
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {K : ℝ}
    (hK : 1 ≤ K)
    (hlevels : MaterialAuxJetLevels I Φ (2 * Nstar β + 1) K (Nstar β))
    {m : ℕ} (hflow : Section2SpatialFlowData I Φ hseq m) :
    ∀ s t : ℝ,
      |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
          ‖iteratedFDeriv ℝ n
            (fun y => constructionMaterialIterate
              (fun r z => streamVel (Φ m) (s + r) z) ell
              (fun r z => constructionComposedFlowJacobian hseq m s r z
                (basisVec j) i) t y)
            x (fun k => basisVec (J k))‖ ≤
              section2MaterialJacobianConstant β K *
                (epsilon β I.Λ m)⁻¹ ^ n *
                (epsilon β I.Λ m ^ (β - 2)) ^ ell := by
  intro s t ht n ell hnell i j x J
  let N := Nstar β
  let W := 2 * N + 1
  let S := (epsilon β I.Λ m)⁻¹
  let H := a β I.Λ m
  let Cflow := section2MaterialSpatialConstant W
  let R := 1 + (2 : ℝ) ^ (W + 1) * K
  let Cmat := section2MaterialJacobianConstant β K
  have hE : 0 < epsilon β I.Λ m :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    exact (Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hN : 1 ≤ N := by
    dsimp [N]
    have h := Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hnN : n ≤ N := by dsimp [N]; omega
  have hellN : ell ≤ N := by dsimp [N]; omega
  have hWbudget : n + 2 * ell ≤ W := by dsimp [W, N]; omega
  have ⟨hCflow, hspatial⟩ :=
    section2_material_jacobian_spatial_slice_of_flow_bounds
      (N := W) hflow
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hR : 1 ≤ R := by
    dsimp [R]
    have hprod : 0 ≤ (2 : ℝ) ^ (W + 1) * K := by positivity
    linarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRpow : ∀ r : ℕ, r ≤ N → R ^ r ≤ R ^ N := by
    intro r hr
    exact pow_le_pow_right₀ hR hr
  have hCmatGeOne : 1 ≤ Cmat := by
    apply section2_material_jacobian_of_material_levels_CmatGeOne1
    all_goals assumption
  have hb0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ m) z.1 z.2) :=
    (smoothPeriodic_streamVel (streamSeq_isAdmissible hseq m)).smooth
  let b0 : AmnrSpace → Vec 2 := fun z => streamVel (Φ m) z.1 z.2
  let bshift : ℝ → Vec 2 → Vec 2 := fun r y => streamVel (Φ m) (s + r) y
  let bAmnr : AmnrSpace → Vec 2 := fun z => b0 (MaterialJacobianFromP.materialTimeShift s z)
  have hbAmnr : ContDiff ℝ (⊤ : ℕ∞) bAmnr := by
    dsimp [bAmnr, b0]
    exact hb0.comp (by fun_prop [MaterialJacobianFromP.materialTimeShift])
  have hbshiftEq : bAmnr = constructionJointVector bshift := by
    funext z
    simp [bAmnr, b0, constructionJointVector, bshift,
      MaterialJacobianFromP.materialTimeShift, add_comm]
  have hbAmnrEq : bAmnr = fun y => streamVel (Φ m) (s + y.1) y.2 := by
    funext z
    simp [bAmnr, b0, MaterialJacobianFromP.materialTimeShift]
  let G : Fin 2 → AmnrSpace → ℝ := fun p z =>
    constructionComposedFlowJacobian hseq m s z.1 z.2 (basisVec j) p
  have hG : ∀ p : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (G p) := by
    intro p
    have hmatrix := constructionComposedFlowJacobian_joint_contDiff
      (hseq := hseq) m s
    have hcolumn := hmatrix.clm_apply
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : AmnrSpace => basisVec j))
    have hentry := (contDiff_pi.1 hcolumn) p
    simpa [G] using hentry
  have htransport : ∀ p z, amnrOp bAmnr none (G p) z =
      ∑ q : Fin 2, G q z * amnrVelocityGradient bAmnr p q z := by
    intro p z
    have hh := MaterialJacobianFromP.materialJacobianEntry_transport (hseq := hseq) m s p j z
    rw [hbAmnrEq]
    simpa [G, constructionJointVector, bshift, add_comm] using hh
  have hgradSmooth : ∀ p q : Fin 2,
      ContDiff ℝ (⊤ : ℕ∞) (amnrVelocityGradient b0 p q) := by
    intro p q
    exact contDiffOn_univ.mp
      (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb0.contDiffOn p q)
  have hgradShift (p q : Fin 2) :
      amnrVelocityGradient bAmnr p q =
        fun z => amnrVelocityGradient b0 p q (MaterialJacobianFromP.materialTimeShift s z) := by
    funext z
    exact MaterialJacobianFromP.amnrVelocityGradient_timeShift hb0 s p q z
  have hBb : ∀ p q w, IsAmnrMixedWord w → amnrBudget w + 2 ≤ W →
      |amnrWord bAmnr w (amnrVelocityGradient bAmnr p q) (t, x)| ≤
        K * H * amnrWeight S H w := by
    apply section2_material_jacobian_of_material_levels_Bb1
    all_goals assumption
  have hGb : ∀ p (η : List (Fin 2)), η.length ≤ W →
      |amnrWord bAmnr (η.map some) (G p) (t, x)| ≤ Cflow * S ^ η.length := by
    intro p η hη
    let f : Vec 2 → ℝ := fun y => G p (t, y)
    have hf : ContDiff ℝ (⊤ : ℕ∞) f := (hG p).comp (by fun_prop)
    rw [amnrWord_spatial_slice (hG p) bAmnr η]
    change |amnrSpaceWord η f x| ≤ Cflow * S ^ η.length
    rw [amnrSpaceWord_eq_iteratedFDeriv hf η, amnrSpatialDirections_eq]
    have hpoint := hspatial s t ht η.length hη p j x
      (fun k => amnrSpatialIndices η k)
    simpa [f, S, Real.norm_eq_abs] using hpoint
  have hGjoint : ∀ p : Fin 2, ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar (fun r y => G p (r, y))) := by
    intro p
    change ContDiff ℝ (⊤ : ℕ∞) (G p)
    exact hG p
  have hbshift : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector bshift) := by
    rw [← hbshiftEq]
    exact hbAmnr
  have hIterSmooth (p : Fin 2) (r : ℕ) :
      ContDiff ℝ (⊤ : ℕ∞)
        (constructionJointScalar
          (constructionMaterialIterate bshift r (fun q y => G p (q, y)))) :=
    constructionMaterialIterate_joint_contDiff hbshift (hGjoint p) r
  have htargetWord (p : Fin 2) (α : List (Fin 2)) :
      amnrWord bAmnr (amnrMixedWord α ell) (G p) (t, x) =
        amnrSpaceWord α
          (fun y => constructionMaterialIterate bshift ell
            (fun q z => G p (q, z)) t y) x := by
    rw [hbshiftEq]
    simp only [amnrMixedWord]
    have hpure := MaterialJacobianFromP.materialPureWord_eq_iterate hbshift (hGjoint p) ell
    have hGpeq : G p = constructionJointScalar (fun q y => G p (q, y)) := by
      funext z
      rfl
    have hpure' : amnrWord (constructionJointVector bshift)
        (List.replicate ell none) (G p) =
        constructionJointScalar
          (constructionMaterialIterate bshift ell (fun q y => G p (q, y))) := by
      rw [← hGpeq] at hpure
      exact hpure
    rw [amnrWord_append, hpure']
    have hslice := amnrWord_spatial_slice (hIterSmooth p ell)
      (constructionJointVector bshift) α
    simpa [constructionJointScalar] using congrFun hslice (t, x)
  have hWbound := amnr_flow_mixed_abs_le_of_primitive_jets
    hbAmnr G hG htransport hS hH (le_trans (by norm_num) hCflow) hK0
    (t, x) hGb hBb
    (List.ofFn J) ell (by simpa [N, W] using hWbudget) i
  have hconst :
      (2 : ℝ) ^ ((List.ofFn J).length + 1) * Cflow * R ^ ell ≤ Cmat := by
    have hpow2 : (2 : ℝ) ^ ((List.ofFn J).length + 1) ≤ (2 : ℝ) ^ (N + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      simp only [List.length_ofFn]
      exact Nat.add_le_add_right hnN 1
    have hpowR' := hRpow ell hellN
    calc
      _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
          section2MaterialSpatialConstant (2 * Nstar β + 1) *
            (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ ell := by
        calc
          _ ≤ (2 : ℝ) ^ (N + 1) * Cflow * R ^ ell := by
            gcongr
          _ = (2 : ℝ) ^ (Nstar β + 1) *
              section2MaterialSpatialConstant (2 * Nstar β + 1) *
                (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ ell := by
            simp [N, Cflow, W, R]
      _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
          section2MaterialSpatialConstant (2 * Nstar β + 1) *
            (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by
        exact mul_le_mul_of_nonneg_left hpowR' (by positivity)
      _ = Cmat := by simp [Cmat, section2MaterialJacobianConstant]
  have htargetBound :
      |amnrWord bAmnr (amnrMixedWord (List.ofFn J) ell) (G i) (t, x)| ≤
        Cmat * S ^ n * H ^ ell := by
    calc
      _ ≤ (2 : ℝ) ^ ((List.ofFn J).length + 1) * Cflow * R ^ ell *
          S ^ (List.ofFn J).length * H ^ ell := by
        simpa [R, S, H, W] using hWbound
      _ = ((2 : ℝ) ^ ((List.ofFn J).length + 1) * Cflow * R ^ ell) *
          (S ^ (List.ofFn J).length * H ^ ell) := by ring
      _ ≤ Cmat * (S ^ (List.ofFn J).length * H ^ ell) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = Cmat * S ^ n * H ^ ell := by simp [List.length_ofFn]; ring
  have htarget := htargetWord i (List.ofFn J)
  have hslice : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => constructionMaterialIterate bshift ell
        (fun q z => G i (q, z)) t y) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
    exact (hIterSmooth i ell).comp hmap
  have hderivWord := amnrSpaceWord_ofFn_eq_iteratedFDeriv hslice n J
  rw [htarget, hderivWord] at htargetBound
  have hHdef : H = epsilon β I.Λ m ^ (β - 2) := by rfl
  simpa [Real.norm_eq_abs, S, H, hHdef, Cmat,
    section2MaterialJacobianConstant] using htargetBound

end AVenhance.Infra.Construction

end
