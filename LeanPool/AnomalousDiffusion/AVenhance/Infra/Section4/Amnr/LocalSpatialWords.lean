/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowJointSource

/-! Spatial-word bridges on the actual open cutoff neighborhood. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- An open joint smoothness domain containing the whole time slice is
sufficient to identify actual ordered spatial words with slice derivatives. -/
theorem amnrWord_spatial_slice_on_vertical_domain {U : Set AmnrSpace} (hU : IsOpen U)
    {f : AmnrSpace → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (b : AmnrSpace → Vec 2) (α : List (Fin 2)) (t : ℝ)
    (hvertical : ∀ x, (t, x) ∈ U) (x : Vec 2) :
    amnrWord b (α.map some) f (t, x) = amnrSpaceWord α (fun y => f (t, y)) x := by
  rw [amnrWord_spatial_independent b (fun _ => (0 : Vec 2)) α f]
  induction α generalizing x with
  | nil => rfl
  | cons i α ih =>
    have hg := amnrWord_contDiffOn_infty hU
      (contDiffOn_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : AmnrSpace => (0 : Vec 2)) U)
      hf (α.map some)
    have hd := (hg.contDiffAt (hU.mem_nhds (hvertical x))).differentiableAt (by simp)
    simp only [List.map_cons, amnrWord]
    rw [amnrOp_space hd i]
    have heq : (fun y => amnrWord (fun _ => (0 : Vec 2)) (α.map some) f (t, y)) =
        amnrSpaceWord α (fun y => f (t, y)) := funext ih
    rw [heq]
    rfl

/-- One constant controls the entire finite spatial budget of the actual
pulled Jacobian's ordered words. -/
def amnrFlowGradientSpatialConstant (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * amnrFlowSpatialSourceConstant N ^ (N + 1)

theorem amnrFlowGradientSpatialConstant_pos (N : ℕ) : 0 < amnrFlowGradientSpatialConstant N := by
  have := amnrFlowSpatialSourceConstant_pos N
  unfold amnrFlowGradientSpatialConstant
  positivity

/-- The actual spatial part of the source flow primitive now has its full
paper budget and a scale-independent constant. -/
theorem amnr_flowGrad_spatialWord_abs_le_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (l : ℤ) (z : AmnrSpace)
    (ht : |z.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m)
    (α : List (Fin 2)) (hbudget : α.length ≤ AVenhance.Nstar β) (i j : Fin 2) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
      (fun y => I.flowGrad hΦ m l y.1 y.2 i j) z| ≤
      amnrFlowGradientSpatialConstant (AVenhance.Nstar β) *
        (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ α.length := by
  let U := amnrSourceFlowDomain I m l
  have hU := amnrSourceFlowDomain_isOpen I m l
  have hG := amnr_flowGrad_contDiffOn_infty_of_A3 I hΦ hreg hm l i j
  have hvertical : ∀ y : Vec 2, (z.1, y) ∈ U := fun y =>
    amnr_cutoff_window_mem_sourceFlowDomain I hm l (z.1, y) ht
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => I.flowGrad hΦ m l z.1 y i j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    exact (hG.contDiffAt (hU.mem_nhds (hvertical y))).comp y (contDiffAt_const.prodMk contDiffAt_id)
  rw [amnrWord_spatial_slice_on_vertical_domain hU hG _ α z.1 hvertical,
    amnrSpaceWord_eq_iteratedFDeriv hs α]
  have hp : ∏ k : Fin α.length, ‖amnrSpatialDirections α k‖ = 1 := by
    rw [amnrSpatialDirections_eq]
    have hb (p : Fin 2) : ‖basisVec p‖ = 1 := by fin_cases p <;> simp [basisVec, Pi.norm_single]
    simp only [hb, Finset.prod_const_one]
  have hh := (iteratedFDeriv ℝ α.length (fun y => I.flowGrad hΦ m l z.1 y i j) z.2).le_opNorm
      (amnrSpatialDirections α)
  rw [hp, mul_one, Real.norm_eq_abs] at hh
  refine hh.trans ((amnr_flowGrad_iteratedFDeriv_norm_le_of_A3 I hΦ hreg hm l z.1 ht
    α.length hbudget i j z.2).trans ?_)
  have hK : 1 ≤ amnrFlowSpatialSourceConstant (AVenhance.Nstar β) :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (amnrJacobianJetConstant_two_le _ _)
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
      - 1)
  apply mul_le_mul_of_nonneg_right ?_ (by positivity)
  unfold amnrFlowGradientSpatialConstant
  exact mul_le_mul (by exact_mod_cast Nat.factorial_le hbudget)
    (pow_le_pow_right₀ hK (by omega)) (by positivity) (by positivity)

end AVenhance.Infra.Section4
