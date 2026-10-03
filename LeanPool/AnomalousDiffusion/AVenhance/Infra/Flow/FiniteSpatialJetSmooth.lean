/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialJetIdentification
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! All finite recursive jet flows are smooth at each fixed start time. -/

@[expose] public section

open Homogenization
open Module
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- The next jet flow makes the reconstructed state derivative smooth. -/
theorem spatialJetFlowDerivativeOperator_contDiff_of_next
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n k : ℕ) (s : ℝ)
    (hnext : ContDiff ℝ k
      (fun p : ℝ × SpatialJetState (n + 1) =>
        spatialJetFlow hb X hX (n + 1) p.1 p.2 s)) :
    ContDiff ℝ k (fun p : ℝ × SpatialJetState n =>
      spatialJetFlowDerivativeOperator hb hX n p.1 s p.2) := by
  let E := SpatialJetState n
  let basis : Basis (Fin (finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let buildLinear : (Fin (finrank ℝ E) → E) →ₗ[ℝ] E →L[ℝ] E :=
    { toFun := fun values => basis.constrL values
      map_add' := by
        intro f g
        ext v
        simp [Module.Basis.constrL_apply, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        ext v
        simp [Module.Basis.constrL_apply, Finset.smul_sum, smul_smul, mul_comm] }
  let build : (Fin (finrank ℝ E) → E) →L[ℝ] E →L[ℝ] E :=
    LinearMap.toContinuousLinearMap buildLinear
  have hbuild : ContDiff ℝ ∞ build := build.contDiff
  let P : SpatialJetState (n + 1) →L[ℝ] E :=
    (ContinuousLinearMap.proj (0 : Fin 2)).comp
      (ContinuousLinearMap.snd ℝ E (Fin 2 → E))
  let values : (ℝ × E) → (Fin (finrank ℝ E) → E) := fun p i =>
    P (spatialJetFlow hb X hX (n + 1) p.1
      (p.2, fun j => if j = (0 : Fin 2) then basis i else 0) s)
  have hvalues : ContDiff ℝ k values := by
    apply contDiff_pi.2
    intro i
    let input : ℝ × E → ℝ × SpatialJetState (n + 1) := fun p =>
      (p.1, (p.2, fun j => if j = (0 : Fin 2) then basis i else 0))
    have hinput : ContDiff ℝ ∞ input := by fun_prop
    have hflow : ContDiff ℝ k
        (fun p : ℝ × E =>
          spatialJetFlow hb X hX (n + 1) p.1
            (p.2, fun j => if j = (0 : Fin 2) then basis i else 0) s) := by
      exact hnext.comp (hinput.of_le (by norm_num : (k : ℕ∞ω) ≤ ∞))
    have hP : ContDiff ℝ ∞ (P : SpatialJetState (n + 1) → E) := P.contDiff
    change ContDiff ℝ k (fun p : ℝ × E => P
      (spatialJetFlow hb X hX (n + 1) p.1
        (p.2, fun j => if j = (0 : Fin 2) then basis i else 0) s))
    exact (hP.of_le (by norm_num : (k : ℕ∞ω) ≤ ∞)).comp hflow
  have heq : (fun p : ℝ × E =>
      spatialJetFlowDerivativeOperator hb hX n p.1 s p.2) =
      fun p => build (values p) := by
    funext p
    rfl
  rw [heq]
  exact hbuild.of_le (by norm_num : (k : ℕ∞ω) ≤ ∞) |>.comp hvalues

theorem FiniteSpatialJetSmooth.spatialJetFlow_fixed_start_contDiff_nat_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X) (s : ℝ) :
    ∀ k n : ℕ, ContDiff ℝ k
      (fun p : ℝ × SpatialJetState n =>
        spatialJetFlow hb X hX n p.1 p.2 s) := by
  intro k
  induction k with
  | zero =>
      intro n
      exact (spatialJetFlow_fixed_start_contDiff_one hb hX n s).of_le (by norm_num)
  | succ k ih =>
      intro n
      have hflow : ContDiff ℝ k
          (fun p : ℝ × SpatialJetState n =>
            spatialJetFlow hb X hX n p.1 p.2 s) := ih n
      have hnext : ContDiff ℝ k
          (fun p : ℝ × SpatialJetState (n + 1) =>
            spatialJetFlow hb X hX (n + 1) p.1 p.2 s) := ih (n + 1)
      let velocity : ℝ × SpatialJetState n → SpatialJetState n := fun p =>
        spatialJetField b n p.1 (spatialJetFlow hb X hX n p.1 p.2 s)
      have hvelocity : ContDiff ℝ k velocity := by
        have hpair : ContDiff ℝ k
            (fun p : ℝ × SpatialJetState n =>
              (p.1, spatialJetFlow hb X hX n p.1 p.2 s)) :=
          contDiff_fst.prodMk hflow
        exact ((spatialJetField_smooth hb n).of_le
          (by norm_num : (k : ℕ∞ω) ≤ ∞)).comp hpair
      let dtimeCLM : ℝ × SpatialJetState n → ℝ →L[ℝ] SpatialJetState n := fun p =>
        ContinuousLinearMap.toSpanSingleton ℝ (velocity p)
      have hdtimeCLM : ContDiff ℝ k dtimeCLM := by
        exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ)
          (E := SpatialJetState n)).contDiff.comp hvelocity
      let dparam : ℝ × SpatialJetState n →
          SpatialJetState n →L[ℝ] SpatialJetState n := fun p =>
        spatialJetFlowDerivativeOperator hb hX n p.1 s p.2
      have hdparam : ContDiff ℝ k dparam := by
        change ContDiff ℝ k (fun p : ℝ × SpatialJetState n =>
          spatialJetFlowDerivativeOperator hb hX n p.1 s p.2)
        exact spatialJetFlowDerivativeOperator_contDiff_of_next hb hX n k s hnext
      let derivative : ℝ × SpatialJetState n →
          (ℝ × SpatialJetState n) →L[ℝ] SpatialJetState n := fun p =>
        (dtimeCLM p).coprod (dparam p)
      have hderivative : ContDiff ℝ k derivative := by
        change ContDiff ℝ k (fun p => (dtimeCLM p).coprod (dparam p))
        exact (ContinuousLinearMap.coprodEquivL (S := ℝ)
          (E := ℝ) (F := SpatialJetState n) (G := SpatialJetState n)).contDiff.comp
            (hdtimeCLM.prodMk hdparam)
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      exact ⟨derivative, hderivative, fun p => by
        simpa [derivative, dtimeCLM, dparam, velocity] using
          spatialJetFlow_fixed_start_hasFDerivAt hb hX n s p⟩

/-- Every finite recursively augmented flow is jointly C∞ in target time and
its initial state when the start time is fixed. -/
theorem spatialJetFlow_fixed_start_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X)
    (n : ℕ) (s : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × SpatialJetState n =>
      spatialJetFlow hb X hX n p.1 p.2 s) := by
  rw [contDiff_infty]
  intro k
  exact FiniteSpatialJetSmooth.spatialJetFlow_fixed_start_contDiff_nat_all hb hX s k n

/-- The original flow is smooth jointly in target time and initial position
for every fixed start time. -/
theorem flow_target_initial_contDiff_infty_fixed_start
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X) (s : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => X p.1 p.2 s) := by
  let input : ℝ × Vec 2 → ℝ × SpatialJetState 1 := fun p =>
    (p.1, spatialJetIdentitySeed 1 p.2)
  have hinput : ContDiff ℝ ∞ input := by
    have hseed : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => spatialJetIdentitySeed 1 p.2) :=
      (spatialJetIdentitySeed_smooth 1).comp contDiff_snd
    exact contDiff_fst.prodMk hseed
  have hjet := spatialJetFlow_fixed_start_contDiff_infty hb hX 1 s
  have hcomp : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => spatialJetFlow hb X hX 1 p.1
        (spatialJetIdentitySeed 1 p.2) s) := by
    have h := hjet.comp hinput
    simpa [input, Function.comp_def] using h
  have hposition : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 =>
        (spatialJetFlow hb X hX 1 p.1 (spatialJetIdentitySeed 1 p.2) s).1) := by
    exact (ContinuousLinearMap.fst ℝ (SpatialJetState 0)
      (Fin 2 → SpatialJetState 0)).contDiff.comp hcomp
  have heq : (fun p : ℝ × Vec 2 =>
      (spatialJetFlow hb X hX 1 p.1 (spatialJetIdentitySeed 1 p.2) s).1) =
      fun p => X p.1 p.2 s := by
    funext p
    exact congrArg Prod.fst
      (spatialJetFlow_one_identity_components hb hX p.1 p.2 s)
  rw [← heq]
  exact hposition

end

end AVenhance.Infra.Flow
