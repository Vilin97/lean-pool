/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSpatialDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Joint continuity of the spatial derivative in all flow parameters. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

theorem flow_reference_derivative_inverse
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (r : ℝ) (x : Vec 2) (s : ℝ) (z : Vec 2) (hz : z = X r x s) :
    let A := fderiv ℝ (fun y => X s y r) z
    let B := fderiv ℝ (fun y => X r y s) x
    A.IsInvertible ∧ A.inverse = B := by
  dsimp
  let F : Vec 2 → Vec 2 := fun y => X s y r
  let G : Vec 2 → Vec 2 := fun y => X r y s
  have hLip : ∃ L : ℝ, ∀ u y w, ‖b u y - b u w‖ ≤ L * ‖y - w‖ := by
    obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
    exact ⟨L, hL⟩
  have hFG (y : Vec 2) : F (G y) = y := by
    calc
      F (G y) = X s y s := by
        dsimp [F, G]
        exact flow_group_law b hLip hX y s r s
      _ = y := hX.1 y s
  have hGF (y : Vec 2) : G (F y) = y := by
    calc
      G (F y) = X r y r := by
        dsimp [F, G]
        exact flow_group_law b hLip hX y r s r
      _ = y := hX.1 y r
  have hF : HasFDerivAt F (fderiv ℝ F z) z := by
    exact ((flow_spatial_contDiff_one hb hX r s).differentiable (by norm_num) z).hasFDerivAt
  have hG : HasFDerivAt G (fderiv ℝ G x) x := by
    exact ((flow_spatial_contDiff_one hb hX s r).differentiable (by norm_num) x).hasFDerivAt
  have hF' : HasFDerivAt F (fderiv ℝ F z) (G x) := by
    simpa [G, hz] using hF
  have hFcomp := HasFDerivAt.comp x hF' hG
  have hFid : HasFDerivAt id ((fderiv ℝ F z).comp (fderiv ℝ G x)) x := by
    exact hFcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (hFG y).symm)
  have hAB : (fderiv ℝ F z).comp (fderiv ℝ G x) = ContinuousLinearMap.id ℝ (Vec 2) :=
    hFid.unique (hasFDerivAt_id x)
  have hFz : F z = x := by simpa [F, G, hz] using hFG x
  have hG' : HasFDerivAt G (fderiv ℝ G x) (F z) := by
    simpa [hFz] using hG
  have hGcomp := HasFDerivAt.comp z hG' hF
  have hGid : HasFDerivAt id ((fderiv ℝ G x).comp (fderiv ℝ F z)) z := by
    exact hGcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (hGF y).symm)
  have hBA : (fderiv ℝ G x).comp (fderiv ℝ F z) = ContinuousLinearMap.id ℝ (Vec 2) :=
    hGid.unique (hasFDerivAt_id z)
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hAB hBA,
    ContinuousLinearMap.inverse_eq hAB hBA⟩

theorem flow_spatialFDeriv_reference_factor
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (r : ℝ) (x : Vec 2) (s t : ℝ) :
    fderiv ℝ (fun y => X t y s) x =
      (fderiv ℝ (fun y => X t y r) (X r x s)).comp
        (fderiv ℝ (fun y => X s y r) (X r x s)).inverse := by
  let G : Vec 2 → Vec 2 := fun y => X r y s
  let F : Vec 2 → Vec 2 := fun y => X t y r
  let z := X r x s
  have hLip : ∃ L : ℝ, ∀ u y w, ‖b u y - b u w‖ ≤ L * ‖y - w‖ := by
    obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
    exact ⟨L, hL⟩
  have hG : HasFDerivAt G (fderiv ℝ G x) x := by
    exact ((flow_spatial_contDiff_one hb hX s r).differentiable (by norm_num) x).hasFDerivAt
  have hF : HasFDerivAt F (fderiv ℝ F z) z := by
    exact ((flow_spatial_contDiff_one hb hX r t).differentiable (by norm_num) z).hasFDerivAt
  have hF' : HasFDerivAt F (fderiv ℝ F z) (G x) := by
    simpa [G, z] using hF
  have hchain := HasFDerivAt.comp x hF' hG
  have hflow (y : Vec 2) : F (G y) = X t y s := by
    dsimp [F, G]
    exact flow_group_law b hLip hX y s r t
  have hchain' : HasFDerivAt (fun y => X t y s)
      ((fderiv ℝ F z).comp (fderiv ℝ G x)) x :=
    hchain.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (hflow y).symm)
  have horig : HasFDerivAt (fun y => X t y s)
      (fderiv ℝ (fun y => X t y s) x) x := by
    exact ((flow_spatial_contDiff_one hb hX s t).differentiable (by norm_num) x).hasFDerivAt
  have hderiv := horig.unique hchain'
  obtain ⟨_, hinv⟩ := flow_reference_derivative_inverse hb hX r x s z rfl
  rw [← hinv] at hderiv
  exact hderiv

theorem JointSpatialDerivativeAll.flow_fixedStart_spatialFDeriv_continuousAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (r T u : ℝ) (z : Vec 2) (hru : r < u) (huT : u < T) :
    ContinuousAt (fun q : ℝ × Vec 2 => fderiv ℝ (fun y => X q.1 y r) q.2) (u, z) := by
  have hJ := flow_spatialFDeriv_jointContinuousOn_of_le hb hX r T (le_of_lt (lt_trans hru huT))
  have hopen : IsOpen (Ioo r T ×ˢ (univ : Set (Vec 2))) := isOpen_Ioo.prod isOpen_univ
  have hmem : (u, z) ∈ Ioo r T ×ˢ (univ : Set (Vec 2)) := ⟨⟨hru, huT⟩, mem_univ _⟩
  have hnhds : Icc r T ×ˢ (univ : Set (Vec 2)) ∈ 𝓝 (u, z) :=
    Filter.mem_of_superset (hopen.mem_nhds hmem) (fun q hq =>
      ⟨Ioo_subset_Icc_self hq.1, hq.2⟩)
  exact hJ.continuousAt hnhds

/-- The spatial Fréchet derivative of a smooth flow is jointly continuous in
target time, initial point, and initial time. -/
theorem flow_spatialFDeriv_jointContinuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (fun p : ℝ × Vec 2 × ℝ =>
      fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  rcases p₀ with ⟨t₀, x₀, s₀⟩
  let r : ℝ := min t₀ s₀ - 1
  let T : ℝ := max t₀ s₀ + 1
  have hrt : r < t₀ := by dsimp [r]; linarith [min_le_left t₀ s₀]
  have hrs : r < s₀ := by dsimp [r]; linarith [min_le_right t₀ s₀]
  have htT : t₀ < T := by dsimp [T]; linarith [le_max_left t₀ s₀]
  have hsT : s₀ < T := by dsimp [T]; linarith [le_max_right t₀ s₀]
  let Z : ℝ × Vec 2 × ℝ → Vec 2 := fun p => X r p.2.1 p.2.2
  let J : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun q =>
    fderiv ℝ (fun y => X q.1 y r) q.2
  let A : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p => J (p.1, Z p)
  let B : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p => J (p.2.2, Z p)
  let C : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p => A p |>.comp (B p).inverse
  let z₀ : Vec 2 := X r x₀ s₀
  have hflow : Continuous (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) :=
    flow_continuous_joint_of_smoothPeriodic hb hX
  have hZ : Continuous Z := by
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (r, p.2.1, p.2.2)) := by fun_prop
    exact hflow.comp hmap
  have hAtTarget := JointSpatialDerivativeAll.flow_fixedStart_spatialFDeriv_continuousAt
    hb hX r T t₀ z₀ hrt htT
  have hAtSource := JointSpatialDerivativeAll.flow_fixedStart_spatialFDeriv_continuousAt
    hb hX r T s₀ z₀ hrs hsT
  have hmapTarget : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.1, Z p)) := by fun_prop
  have hmapSource : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.2.2, Z p)) := by fun_prop
  have hA : ContinuousAt A (t₀, x₀, s₀) := by
    exact ContinuousAt.comp_of_eq hAtTarget hmapTarget.continuousAt (by simp [Z, z₀])
  have hB : ContinuousAt B (t₀, x₀, s₀) := by
    exact ContinuousAt.comp_of_eq hAtSource hmapSource.continuousAt (by simp [Z, z₀])
  have hBInv : (B (t₀, x₀, s₀)).IsInvertible := by
    obtain ⟨hInv, _⟩ := flow_reference_derivative_inverse hb hX r x₀ s₀ z₀ rfl
    simpa [B, J, z₀] using hInv
  have hInvAt : ContinuousAt ContinuousLinearMap.inverse (B (t₀, x₀, s₀)) :=
    (hBInv.contDiffAt_map_inverse (n := (0 : ℕ∞))).continuousAt
  have hBinv : ContinuousAt (fun p => (B p).inverse) (t₀, x₀, s₀) := by
    exact hInvAt.comp hB
  have hC : ContinuousAt C (t₀, x₀, s₀) := by
    have hcomp : Continuous (fun q :
        (Vec 2 →L[ℝ] Vec 2) × (Vec 2 →L[ℝ] Vec 2) => q.1.comp q.2) := by fun_prop
    change ContinuousAt
      ((fun q : (Vec 2 →L[ℝ] Vec 2) × (Vec 2 →L[ℝ] Vec 2) => q.1.comp q.2) ∘
        (fun p => (A p, (B p).inverse))) (t₀, x₀, s₀)
    exact hcomp.continuousAt.comp (hA.prodMk hBinv)
  have hfactor (p : ℝ × Vec 2 × ℝ) :
      fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1 = C p := by
    dsimp [C, A, B, J, Z]
    exact flow_spatialFDeriv_reference_factor hb hX r p.2.1 p.2.2 p.1
  have hfun :
      (fun p : ℝ × Vec 2 × ℝ => fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1) = C :=
    funext hfactor
  rw [hfun]
  exact hC

end AVenhance.Infra.Flow
