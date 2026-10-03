/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC3Forward
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC2All
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSpatialDerivativeAll

/-! Global joint C³ regularity by reference-time factorization. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Spatial Jacobian used in the joint C³ bootstrap. -/
def JointC3All.flowSpatialJacobianJointC2
    (X : ℝ → Vec 2 → ℝ → Vec 2) (p : ℝ × Vec 2 × ℝ) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1

/-- The spatial Jacobian is jointly C² in target time, initial point, and
start time. Reference-time factorization reduces the claim locally to a
forward strip, where the variational equation gives C² regularity. -/
theorem flow_spatialFDeriv_contDiff_two_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 2 (JointC3All.flowSpatialJacobianJointC2 X) := by
  rw [contDiff_iff_contDiffAt]
  intro p₀
  rcases p₀ with ⟨t₀, x₀, s₀⟩
  let r : ℝ := min t₀ s₀ - 1
  let T : ℝ := max t₀ s₀ + 1
  have hrt : r < t₀ := by dsimp [r]; linarith [min_le_left t₀ s₀]
  have hrs : r < s₀ := by dsimp [r]; linarith [min_le_right t₀ s₀]
  have htT : t₀ < T := by dsimp [T]; linarith [le_max_left t₀ s₀]
  have hsT : s₀ < T := by dsimp [T]; linarith [le_max_right t₀ s₀]
  have hrT : r < T := lt_trans hrt htT
  let baseRegion := Ioo r T ×ˢ (univ : Set (Vec 2))
  let region := Ioo r T ×ˢ ((univ : Set (Vec 2)) ×ˢ Ioo r T)
  have hbaseOpen : IsOpen baseRegion := isOpen_Ioo.prod isOpen_univ
  have hregionOpen : IsOpen region := isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)
  have hmem : (t₀, x₀, s₀) ∈ region :=
    ⟨⟨hrt, htT⟩, mem_univ _, ⟨hrs, hsT⟩⟩
  let J₀ : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun q =>
    fderiv ℝ (fun y => X q.1 y r) q.2
  have hJ₀ : ContDiffOn ℝ 2 J₀ baseRegion := by
    exact flow_spatialFDeriv_contDiffOn_two_of_le hb hX r T hrT
  have hXall : ContDiff ℝ 2
      (fun q : ℝ × Vec 2 × ℝ => X q.1 q.2.1 q.2.2) :=
    flow_joint_contDiff_two_all hb hX
  let Z : ℝ × Vec 2 × ℝ → Vec 2 := fun q => X r q.2.1 q.2.2
  have hZ : ContDiff ℝ 2 Z := by
    have hmap : ContDiff ℝ 2 (fun q : ℝ × Vec 2 × ℝ => (r, q.2.1, q.2.2)) := by
      fun_prop
    exact hXall.comp hmap
  let targetMap : ℝ × Vec 2 × ℝ → ℝ × Vec 2 := fun q => (q.1, Z q)
  let startMap : ℝ × Vec 2 × ℝ → ℝ × Vec 2 := fun q => (q.2.2, Z q)
  have htargetMap : ContDiffOn ℝ 2 targetMap region := by
    exact (contDiff_fst.prodMk hZ).contDiffOn
  have hstartMap : ContDiffOn ℝ 2 startMap region := by
    have hfst : ContDiff ℝ 2 (fun q : ℝ × Vec 2 × ℝ => q.2.2) := by fun_prop
    exact (hfst.prodMk hZ).contDiffOn
  have htargetMaps : MapsTo targetMap region baseRegion := by
    intro q hq
    exact ⟨hq.1, mem_univ _⟩
  have hstartMaps : MapsTo startMap region baseRegion := by
    intro q hq
    exact ⟨hq.2.2, mem_univ _⟩
  let A : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun q => J₀ (targetMap q)
  let B : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun q => J₀ (startMap q)
  have hA : ContDiffOn ℝ 2 A region := hJ₀.comp htargetMap htargetMaps
  have hB : ContDiffOn ℝ 2 B region := hJ₀.comp hstartMap hstartMaps
  have hAAt : ContDiffAt ℝ 2 A (t₀, x₀, s₀) :=
    hA.contDiffAt (hregionOpen.mem_nhds hmem)
  have hBAt : ContDiffAt ℝ 2 B (t₀, x₀, s₀) :=
    hB.contDiffAt (hregionOpen.mem_nhds hmem)
  have hBInv : (B (t₀, x₀, s₀)).IsInvertible := by
    obtain ⟨hInv, _⟩ :=
      flow_reference_derivative_inverse hb hX r x₀ s₀ (X r x₀ s₀) rfl
    simpa [B, startMap, J₀, Z] using hInv
  have hBInvAt : ContDiffAt ℝ 2 ContinuousLinearMap.inverse
      (B (t₀, x₀, s₀)) := hBInv.contDiffAt_map_inverse (n := 2)
  have hInvAt : ContDiffAt ℝ 2 (fun q => (B q).inverse) (t₀, x₀, s₀) :=
    ContDiffAt.comp (t₀, x₀, s₀) hBInvAt hBAt
  have hFactoredAt : ContDiffAt ℝ 2
      (fun q => (A q).comp (B q).inverse) (t₀, x₀, s₀) :=
    hAAt.clm_comp hInvAt
  have hFactor (q : ℝ × Vec 2 × ℝ) :
      JointC3All.flowSpatialJacobianJointC2 X q = (A q).comp (B q).inverse := by
    dsimp [JointC3All.flowSpatialJacobianJointC2, A, B, targetMap, startMap, J₀, Z]
    exact flow_spatialFDeriv_reference_factor hb hX r q.2.1 q.2.2 q.1
  apply hFactoredAt.congr_of_eventuallyEq
  filter_upwards [hregionOpen.mem_nhds hmem] with q hq
  exact hFactor q

/-- Observation-time velocity used in the joint C³ bootstrap. -/
def JointC3All.flowTimeVelocityC2
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  b p.1 (X p.1 p.2.1 p.2.2)

/-- Starting-time velocity used in the joint C³ bootstrap. -/
def JointC3All.flowStartVelocityC2
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  -(JointC3All.flowSpatialJacobianJointC2 X p (b p.2.2 p.2.1))

/-- Continuous linear starting-time differential used in the joint C³ bootstrap. -/
def JointC3All.flowStartCLMC2
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : ℝ →L[ℝ] Vec 2 :=
  ContinuousLinearMap.toSpanSingleton ℝ (JointC3All.flowStartVelocityC2 b X p)

/-- Position and starting-time differential used in the joint C³ bootstrap. -/
def JointC3All.flowParameterDerivativeC2
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (JointC3All.flowSpatialJacobianJointC2 X p).coprod (JointC3All.flowStartCLMC2 b X p)

/-- Full joint differential used in the joint C³ bootstrap. -/
def JointC3All.flowJointDerivativeC2
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (ℝ × Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ (JointC3All.flowTimeVelocityC2 b X p)).coprod
    (JointC3All.flowParameterDerivativeC2 b X p)

/-- Joint C³ regularity of a smooth periodic flow in target time, initial
position, and start time. -/
theorem flow_joint_contDiff_three_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 3 (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) := by
  have hflow : ContDiff ℝ 2
      (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) :=
    flow_joint_contDiff_two_all hb hX
  have hJ : ContDiff ℝ 2 (JointC3All.flowSpatialJacobianJointC2 X) :=
    flow_spatialFDeriv_contDiff_two_all hb hX
  have htime : ContDiff ℝ 2 (JointC3All.flowTimeVelocityC2 b X) := by
    have hpair : ContDiff ℝ 2
        (fun p : ℝ × Vec 2 × ℝ => (p.1, X p.1 p.2.1 p.2.2)) :=
      contDiff_fst.prodMk hflow
    change ContDiff ℝ 2
      (Function.uncurry b ∘ fun p : ℝ × Vec 2 × ℝ => (p.1, X p.1 p.2.1 p.2.2))
    exact (hb.smooth.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)).comp hpair
  have hfield : ContDiff ℝ 2
      (fun p : ℝ × Vec 2 × ℝ => b p.2.2 p.2.1) := by
    have hmap : ContDiff ℝ 2 (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1)) := by
      fun_prop
    exact (hb.smooth.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)).comp hmap
  have hstartVelocity : ContDiff ℝ 2 (JointC3All.flowStartVelocityC2 b X) := by
    have happly : ContDiff ℝ 2
        (fun p : ℝ × Vec 2 × ℝ => JointC3All.flowSpatialJacobianJointC2 X p
          (b p.2.2 p.2.1)) := hJ.clm_apply hfield
    change ContDiff ℝ 2
      (fun p => -(JointC3All.flowSpatialJacobianJointC2 X p (b p.2.2 p.2.1)))
    exact happly.neg
  have hstartCLM : ContDiff ℝ 2 (JointC3All.flowStartCLMC2 b X) := by
    change ContDiff ℝ 2
      (fun p => ContinuousLinearMap.toSpanSingleton ℝ (JointC3All.flowStartVelocityC2 b X p))
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Vec 2)).contDiff.comp
      hstartVelocity
  have hparam : ContDiff ℝ 2 (JointC3All.flowParameterDerivativeC2 b X) := by
    change ContDiff ℝ 2 (fun p =>
      (JointC3All.flowSpatialJacobianJointC2 X p).coprod (JointC3All.flowStartCLMC2 b X p))
    exact (ContinuousLinearMap.coprodEquivL (S := ℝ) (E := Vec 2)
      (F := ℝ) (G := Vec 2)).contDiff.comp (hJ.prodMk hstartCLM)
  have htimeCLM : ContDiff ℝ 2 (fun p =>
      ContinuousLinearMap.toSpanSingleton ℝ (JointC3All.flowTimeVelocityC2 b X p)) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Vec 2)).contDiff.comp htime
  have hD : ContDiff ℝ 2 (JointC3All.flowJointDerivativeC2 b X) := by
    change ContDiff ℝ 2 (fun p =>
      (ContinuousLinearMap.toSpanSingleton ℝ (JointC3All.flowTimeVelocityC2 b X p)).coprod
        (JointC3All.flowParameterDerivativeC2 b X p))
    exact (ContinuousLinearMap.coprodEquivL (S := ℝ) (E := ℝ)
      (F := Vec 2 × ℝ) (G := Vec 2)).contDiff.comp (htimeCLM.prodMk hparam)
  rw [show (3 : ℕ∞ω) = (2 : ℕ) + 1 by norm_num,
    contDiff_succ_iff_hasFDerivAt]
  exact ⟨JointC3All.flowJointDerivativeC2 b X, hD, fun p => by
    have h := flow_joint_hasFDerivAt_explicit hb hX p
    simpa [JointC3All.flowJointDerivativeC2, JointC3All.flowParameterDerivativeC2,
        JointC3All.flowStartCLMC2,
      JointC3All.flowStartVelocityC2, JointC3All.flowTimeVelocityC2,
          JointC3All.flowSpatialJacobianJointC2,
      flowJointDerivativeFormula] using h⟩

/-- Joint C³ regularity of the inverse flow follows by permuting target and
start times. -/
theorem flow_inverse_joint_contDiff_three_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 3 (fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) := by
  have hperm : ContDiff ℝ 3
      (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1, p.1)) := by fun_prop
  simpa only [Function.comp_def] using (flow_joint_contDiff_three_all hb hX).comp hperm

end

end AVenhance.Infra.Flow
