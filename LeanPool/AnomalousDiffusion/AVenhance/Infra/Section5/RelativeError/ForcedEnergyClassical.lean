/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyClassicalExt
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsTestFunction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.AdvDiffOp
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest

/-!
# A classical solution is a weak solution

The regularity clauses of `IsWeakSolutionGrad` follow from joint continuity up to `t = 0`; the
weak identity follows from integration by parts in time and in space against the periodic
smooth test functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.WeakUniqueness

local instance classicalFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance classicalFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- The closed unit cell. -/
def forcedClosedCell : Set (Vec 2) := Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem forcedClosedCell_compact : IsCompact forcedClosedCell :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem unitCube_ae_eq_closedCell : AVenhance.unitCube =ᵐ[volume] forcedClosedCell := by
  simpa [AVenhance.unitCube, forcedClosedCell, volume_pi] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))

theorem unitCube_subset_closedCell : AVenhance.unitCube ⊆ forcedClosedCell := by
  intro x hx
  simp only [AVenhance.unitCube, forcedClosedCell, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
  exact fun j => ⟨(hx j).1.le, (hx j).2.le⟩

theorem classical_contDiffOn {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} (hθ : AVenhance.IsClassicalSol b κ (fun _ _ => 0) g θ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ) classicalHalfSpace := hθ.1

/-- Regularity clauses (1)-(7) of the weak-solution predicate for a classical solution. -/
theorem classical_weak_regularity {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hθ : AVenhance.IsClassicalSol b κ (fun _ _ => 0) g θ) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (θ t) ∧ MemL2On AVenhance.unitCube (θ t)) ∧
    (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.l2NormSq (θ t) ≤ C) ∧
    MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 (volume.restrict AVenhance.timeCube) ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (θ p.1) p.2 i) 2
      (volume.restrict AVenhance.timeCube)) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AVenhance.IsPeriodicH1With (θ t) (fun x => AVenhance.spaceGrad (θ t) x)) ∧
    Integrable (fun p : ℝ × Vec 2 =>
      vecDot (b p.1 p.2) (AVenhance.spaceGrad (θ p.1) p.2))
      (volume.restrict AVenhance.timeCube) ∧
    (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in AVenhance.unitCube, θ t x * ψ x) (Set.Icc (0 : ℝ) 1)) := by
  have hC := classical_contDiffOn hθ
  have hslice (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ 1 (θ t) :=
    (AVenhance.Infra.Section5.classicalSol_space_contDiff_of_nonneg hθ ht).of_le (by simp)
  have hae : ∀ᵐ p ∂(volume.restrict AVenhance.timeCube), 0 < p.1 := by
    filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp using hp.1.1
  have hgradMem (i : Fin 2) :
      MemLp (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (θ p.1) p.2 i) 2
        (volume.restrict AVenhance.timeCube) := by
    refine (weak_continuous_memLp_two_timeCube (clGradExt_continuous hC i)).ae_eq ?_
    filter_upwards [hae] with p hp using clGradExt_eq hC hp.le i
  refine ⟨fun t ht => ⟨hθ.2.1 t ht.1, weak_continuous_memL2On (hslice t ht.1).continuous⟩,
    ?_, ?_, hgradMem, ?_, ?_, ?_⟩
  · -- uniform bound of the energy
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod forcedClosedCell_compact).exists_bound_of_continuousOn
      (f := clExt θ) (clExt_continuous hC).continuousOn
    refine ⟨M ^ 2 * (volume.restrict AVenhance.unitCube).real univ, fun t ht => ?_⟩
    have hbound : ∀ x ∈ AVenhance.unitCube, ‖θ t x ^ 2‖ ≤ M ^ 2 := by
      intro x hx
      have := hM (t, x) ⟨ht, unitCube_subset_closedCell hx⟩
      rw [clExt_eq (p := (t, x)) ht.1] at this
      rw [Real.norm_eq_abs, abs_pow]
      have h0 : 0 ≤ ‖θ t x‖ := norm_nonneg _
      simp only [Real.norm_eq_abs] at this
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := AVenhance.unitCube)
      (f := fun x => θ t x ^ 2) (C := M ^ 2) (by
        unfold AVenhance.unitCube
        rw [volume_pi, Measure.pi_pi]
        simp [Real.volume_Ioo]) hbound
    calc AVenhance.l2NormSq (θ t) ≤ ‖∫ x in AVenhance.unitCube, θ t x ^ 2‖ := le_abs_self _
      _ ≤ M ^ 2 * (volume.restrict AVenhance.unitCube).real univ := by
        simpa [Measure.real, Measure.restrict_apply_univ] using this
  · refine (weak_continuous_memLp_two_timeCube (clExt_continuous hC)).ae_eq ?_
    filter_upwards [hae] with p hp using clExt_eq hp.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact isPeriodicH1With_of_contDiff (hslice t ht.1.le) (hθ.2.1 t ht.1.le)
  · have hcont : Continuous (fun p : ℝ × Vec 2 =>
        vecDot (b (max p.1 0) p.2) (fun i => clGradExt θ i p)) := by
      simp only [vecDot]
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (hb.comp clMap_continuous)).mul (clGradExt_continuous hC i)
    have hmem := (weak_continuous_memLp_two_timeCube hcont).integrable (by norm_num)
    refine hmem.congr ?_
    filter_upwards [hae] with p hp
    simp only [vecDot, max_eq_left hp.le]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [clGradExt_eq hC hp.le i]
  · intro ψ hψ _
    have hcontParam : Continuous (fun t : ℝ => ∫ x in forcedClosedCell,
        clExt θ (t, x) * ψ x) := by
      refine continuous_parametric_integral_of_continuous (f := fun t x => clExt θ (t, x) * ψ x)
        ?_ forcedClosedCell_compact
      exact ((clExt_continuous hC).comp (continuous_fst.prodMk continuous_snd)).mul
        (hψ.continuous.comp continuous_snd)
    refine hcontParam.continuousOn.congr fun t ht => ?_
    have : ∫ x in AVenhance.unitCube, θ t x * ψ x =
        ∫ x in AVenhance.unitCube, clExt θ (t, x) * ψ x :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [clExt_eq (p := (t, x)) ht.1])
    rw [this]
    exact setIntegral_congr_set unitCube_ae_eq_closedCell

/-- A continuous function is integrable on the time cell. -/
theorem continuous_integrable_timeCube {F : ℝ × Vec 2 → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict AVenhance.timeCube) :=
  (weak_continuous_memLp_two_timeCube hF).integrable (by norm_num)

/-- A continuous function is integrable on the unit cube. -/
theorem continuous_integrableOn_unitCube' {f : Vec 2 → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict AVenhance.unitCube) :=
  (hf.continuousOn.integrableOn_compact forcedClosedCell_compact).mono_set
    unitCube_subset_closedCell

/-- Fubini on the time cell, time outermost. -/
theorem timeCube_integral_eq_time_space {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    ∫ p in AVenhance.timeCube, F p =
      ∫ t in Set.Ioo (0 : ℝ) 1, ∫ x in AVenhance.unitCube, F (t, x) := by
  rw [forced_timeCube_measure_eq_product] at hF ⊢
  exact integral_prod F hF

/-- Fubini on the time cell, space outermost. -/
theorem timeCube_integral_eq_space_time {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    ∫ p in AVenhance.timeCube, F p =
      ∫ x in AVenhance.unitCube, ∫ t in Set.Ioo (0 : ℝ) 1, F (t, x) := by
  rw [forced_timeCube_measure_eq_product] at hF ⊢
  exact integral_prod_symm F hF

/-- Time derivative of a test function is continuous. -/
theorem test_timeDeriv_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) :=
  (AVenhance.Infra.Parabolic.FourierGalerkin.spacetimeTestTimeDerivative_contDiff hφ).continuous

/-- Integration by parts in time for one spatial point. -/
theorem classical_time_ibp {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} (hθ : AVenhance.IsClassicalSol b κ (fun _ _ => 0) g θ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : AVenhance.IsTestFunction φ) (x : Vec 2) :
    ∫ t in (0 : ℝ)..1, (-(clExt θ (t, x)) * deriv (fun s => φ s x) t) =
      g x * φ 0 x + ∫ t in (0 : ℝ)..1, clTimeExt θ (t, x) * φ t x := by
  have hC := classical_contDiffOn hθ
  have hline : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
  have hu : Continuous (fun t : ℝ => clExt θ (t, x)) := (clExt_continuous hC).comp hline
  have hu' : Continuous (fun t : ℝ => clTimeExt θ (t, x)) := (clTimeExt_continuous hC).comp hline
  have hv : Continuous (fun t : ℝ => φ t x) := hφ.1.continuous.comp hline
  have hv' : Continuous (fun t : ℝ => deriv (fun s => φ s x) t) :=
    (test_timeDeriv_continuous hφ.1).comp hline
  have huu' : ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun s => clExt θ (s, x)) (clTimeExt θ (t, x)) t := by
    intro t ht
    simp only [min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
    have hd := classical_deriv_eq_joint hC ht.1 x
    have heq : (fun s => θ s x) =ᶠ[𝓝 t] fun s => clExt θ (s, x) := by
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      exact (clExt_eq (p := (s, x)) (le_of_lt hs)).symm
    have := hd.congr_of_eventuallyEq heq.symm
    simpa [clTimeExt, max_eq_left ht.1.le] using this
  have hvv' : ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun s => φ s x) (deriv (fun s => φ s x) t) t := by
    intro t _
    have hdiff : Differentiable ℝ (fun s : ℝ => φ s x) :=
      (hφ.1.differentiable (by simp)).comp (differentiable_id.prodMk (differentiable_const x))
    exact (hdiff t).hasDerivAt
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) hu.continuousOn hv.continuousOn huu' hvv'
    (hu'.intervalIntegrable 0 1) (hv'.intervalIntegrable 0 1)
  have h1 : φ 1 x = 0 := hφ.2.2 1 le_rfl x
  have h0 : clExt θ (0, x) = g x := by
    rw [clExt_eq (p := ((0 : ℝ), x)) le_rfl]
    exact hθ.2.2.1 x
  simp only [h1, h0, mul_zero, zero_sub] at hIBP
  have hneg : ∫ t in (0 : ℝ)..1, (-(clExt θ (t, x)) * deriv (fun s => φ s x) t) =
      -∫ t in (0 : ℝ)..1, clExt θ (t, x) * deriv (fun s => φ s x) t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  rw [hneg, hIBP]
  ring

theorem vecDot_comm' (a c : Vec 2) : vecDot a c = vecDot c a := by
  simp [vecDot, mul_comm]

/-- Integration by parts in space at one positive time. -/
theorem classical_space_ibp {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} (hθ : AVenhance.IsClassicalSol b κ (fun _ _ => 0) g θ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : AVenhance.IsTestFunction φ) {t : ℝ} (ht : 0 < t) :
    ∫ x in AVenhance.unitCube, κ * vecDot (fun i => clGradExt θ i (t, x))
        (AVenhance.spaceGrad (φ t) x) =
      -∫ x in AVenhance.unitCube,
        (clTimeExt θ (t, x) + vecDot (b t x) (fun i => clGradExt θ i (t, x))) * φ t x := by
  have hC := classical_contDiffOn hθ
  have hf : ContDiff ℝ (⊤ : ℕ∞) (φ t) :=
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (θ t) :=
    AVenhance.Infra.Section5.classicalSol_space_contDiff_of_nonneg hθ ht.le
  have hlap := AVenhance.Infra.Classical.integral_unitCell_lap_mul hf hg (hφ.2.1 t) (hθ.2.1 t ht.le)
  rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube,
    AVenhance.Infra.Torus.integral_unitCell_eq_unitCube] at hlap
  have hpde (x : Vec 2) : κ * AVenhance.spaceLap (θ t) x =
      clTimeExt θ (t, x) + vecDot (b t x) (fun i => clGradExt θ i (t, x)) := by
    have h := hθ.2.2.2 t ht x
    unfold AVenhance.advDiffOp at h
    have e1 : clTimeExt θ (t, x) = deriv (fun s => θ s x) t := clTimeExt_eq hC (p := (t, x)) ht
    have e2 : (fun i => clGradExt θ i (t, x)) = AVenhance.spaceGrad (θ t) x := by
      funext i
      exact clGradExt_eq hC (p := (t, x)) ht.le i
    rw [e1, e2]
    linarith
  have hcomm : ∫ x in AVenhance.unitCube, κ * vecDot (fun i => clGradExt θ i (t, x))
        (AVenhance.spaceGrad (φ t) x) =
      κ * ∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (φ t) x) (AVenhance.spaceGrad (θ t) x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have e2 : (fun i => clGradExt θ i (t, x)) = AVenhance.spaceGrad (θ t) x := by
      funext i
      exact clGradExt_eq hC (p := (t, x)) ht.le i
    simp only [e2]
    rw [vecDot_comm']
  have h2 : ∫ x in AVenhance.unitCube,
      vecDot (AVenhance.spaceGrad (φ t) x) (AVenhance.spaceGrad (θ t) x) =
      -∫ x in AVenhance.unitCube, φ t x * AVenhance.spaceLap (θ t) x := by linarith [hlap]
  rw [hcomm, h2, mul_neg, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change κ * (φ t x * AVenhance.spaceLap (θ t) x) = _
  rw [show κ * (φ t x * AVenhance.spaceLap (θ t) x) = φ t x * (κ * AVenhance.spaceLap (θ t) x)
    by ring, hpde x]
  ring

/-- The weak identity (clause 8) of the weak-solution predicate. -/
theorem classical_weak_identity {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hθ : AVenhance.IsClassicalSol b κ (fun _ _ => 0) g θ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : AVenhance.IsTestFunction φ) :
    ∫ p in AVenhance.timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + vecDot (b p.1 p.2) (AVenhance.spaceGrad (θ p.1) p.2) * φ p.1 p.2
        + κ * vecDot (AVenhance.spaceGrad (θ p.1) p.2) (AVenhance.spaceGrad (φ p.1) p.2))
      = ∫ x in AVenhance.unitCube, g x * φ 0 x := by
  have hC := classical_contDiffOn hθ
  have hae : ∀ᵐ p ∂(volume.restrict AVenhance.timeCube), 0 < p.1 := by
    filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp using hp.1.1
  have hφc : Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2) := hφ.1.continuous
  have hφsp (i : Fin 2) : Continuous (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (φ p.1) p.2 i) := by
    have : Continuous (fun p : ℝ × Vec 2 => (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p)
        (0, basisVec i)) := (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    refine this.congr fun p => Eq.symm ?_
    have hd : HasFDerivAt (fun q : ℝ × Vec 2 => φ q.1 q.2)
        (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) (p.1, p.2)) (p.1, p.2) :=
      (hφ.1.differentiable (by simp) (p.1, p.2)).hasFDerivAt
    have hl : HasFDerivAt (fun x : Vec 2 => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hcomp := hd.comp p.2 hl
    change fderiv ℝ (φ p.1) p.2 (basisVec i) = _
    have e : φ p.1 = (fun q : ℝ × Vec 2 => φ q.1 q.2) ∘ fun x : Vec 2 => (p.1, x) := rfl
    rw [e, hcomp.fderiv]
    simp [ContinuousLinearMap.inr]
  let T : ℝ × Vec 2 → ℝ := fun p => deriv (fun s => φ s p.2) p.1
  have hT : Continuous T := test_timeDeriv_continuous hφ.1
  let Af : ℝ × Vec 2 → ℝ := fun p => -(clExt θ p) * T p
  let Bf : ℝ × Vec 2 → ℝ := fun p => vecDot (b p.1 p.2) (fun i => clGradExt θ i p) * φ p.1 p.2
  let Cf : ℝ × Vec 2 → ℝ := fun p => κ * vecDot (fun i => clGradExt θ i p)
    (AVenhance.spaceGrad (φ p.1) p.2)
  let Pf : ℝ × Vec 2 → ℝ := fun p => clTimeExt θ p * φ p.1 p.2
  have hdotc (U V : ℝ × Vec 2 → Vec 2) (hU : ∀ i, Continuous fun p => U p i)
      (hV : ∀ i, Continuous fun p => V p i) : Continuous (fun p => vecDot (U p) (V p)) := by
    simp only [vecDot]
    exact continuous_finsetSum _ fun i _ => (hU i).mul (hV i)
  have hbc (i : Fin 2) : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2 i) :=
    (continuous_apply i).comp hb
  have hAc : Continuous Af := (clExt_continuous hC).neg.mul hT
  have hBc : Continuous Bf :=
    (hdotc (fun p => b p.1 p.2) (fun p i => clGradExt θ i p) hbc
      (fun i => clGradExt_continuous hC i)).mul hφc
  have hCc : Continuous Cf :=
    continuous_const.mul (hdotc (fun p i => clGradExt θ i p) (fun p => AVenhance.spaceGrad (φ p.1)
        p.2)
      (fun i => clGradExt_continuous hC i) hφsp)
  have hPc : Continuous Pf := (clTimeExt_continuous hC).mul hφc
  have hAi := continuous_integrable_timeCube hAc
  have hBi := continuous_integrable_timeCube hBc
  have hCi := continuous_integrable_timeCube hCc
  have hPi := continuous_integrable_timeCube hPc
  -- the integrand is `Af + Bf + Cf` on the cube
  have hcongr : ∫ p in AVenhance.timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + vecDot (b p.1 p.2) (AVenhance.spaceGrad (θ p.1) p.2) * φ p.1 p.2
        + κ * vecDot (AVenhance.spaceGrad (θ p.1) p.2) (AVenhance.spaceGrad (φ p.1) p.2)) =
      ∫ p in AVenhance.timeCube, (Af p + Bf p + Cf p) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    have e1 : clExt θ p = θ p.1 p.2 := clExt_eq hp.le
    have e2 : (fun i => clGradExt θ i p) = AVenhance.spaceGrad (θ p.1) p.2 := by
      funext i
      exact clGradExt_eq hC hp.le i
    simp only [Af, Bf, Cf, T, e1, e2]
  -- time integration by parts
  have hAint : ∫ p in AVenhance.timeCube, Af p =
      (∫ x in AVenhance.unitCube, g x * φ 0 x) + ∫ p in AVenhance.timeCube, Pf p := by
    have hg0 : Continuous (fun x => g x * φ 0 x) := by
      have : g = θ 0 := funext fun x => (hθ.2.2.1 x).symm
      rw [this]
      exact (AVenhance.Infra.Section5.classicalSol_space_contDiff_of_nonneg hθ
          le_rfl).continuous.mul
        (hφ.1.continuous.comp (continuous_const.prodMk continuous_id))
    have hinner (x : Vec 2) : ∫ t in Set.Ioo (0 : ℝ) 1, Af (t, x) =
        g x * φ 0 x + ∫ t in Set.Ioo (0 : ℝ) 1, Pf (t, x) := by
      rw [weakEnergy_Ioo_intervalIntegral zero_le_one, weakEnergy_Ioo_intervalIntegral zero_le_one]
      exact classical_time_ibp hθ hφ x
    have hPint : Integrable (fun x => ∫ t in Set.Ioo (0 : ℝ) 1, Pf (t, x))
        (volume.restrict AVenhance.unitCube) := by
      have := hPi
      rw [forced_timeCube_measure_eq_product] at this
      exact this.integral_prod_right
    rw [timeCube_integral_eq_space_time hAi, timeCube_integral_eq_space_time hPi]
    simp_rw [hinner]
    rw [integral_add (continuous_integrableOn_unitCube' hg0) hPint]
  -- spatial integration by parts
  have hPB : ∫ p in AVenhance.timeCube, (Pf p + Bf p) =
      (∫ p in AVenhance.timeCube, Pf p) + ∫ p in AVenhance.timeCube, Bf p :=
    integral_add hPi hBi
  have hFi : Integrable (fun p => -(Pf p + Bf p)) (volume.restrict AVenhance.timeCube) :=
    (hPi.add hBi).neg
  have hCint : ∫ p in AVenhance.timeCube, Cf p =
      -((∫ p in AVenhance.timeCube, Pf p) + ∫ p in AVenhance.timeCube, Bf p) := by
    rw [← hPB, ← integral_neg, timeCube_integral_eq_time_space hCi,
      timeCube_integral_eq_time_space hFi]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have := classical_space_ibp hθ hφ ht.1
    simp only [Cf, Pf, Bf]
    rw [this, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change -((clTimeExt θ (t, x) + vecDot (b t x) fun i => clGradExt θ i (t, x)) * φ t x) = _
    ring
  have hAB : Integrable (fun p => Af p + Bf p) (volume.restrict AVenhance.timeCube) := hAi.add hBi
  have hsum : ∫ p in AVenhance.timeCube, (Af p + Bf p + Cf p) =
      (∫ p in AVenhance.timeCube, Af p) + (∫ p in AVenhance.timeCube, Bf p) +
        ∫ p in AVenhance.timeCube, Cf p := by
    rw [integral_add hAB hCi, integral_add hAi hBi]
  rw [hcongr, hsum, hAint, hCint]
  ring

/-- A classical solution with a continuous drift is a weak solution, with its
classical gradient as weak gradient. -/
theorem classical_isWeakSolutionGrad {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hθ : AVenhance.IsClassicalSol b κ (fun _ _ => 0) g θ) :
    AVenhance.IsWeakSolutionGrad b κ g θ (fun t x => AVenhance.spaceGrad (θ t) x) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := classical_weak_regularity hb hθ
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun φ hφ => classical_weak_identity hb hθ hφ⟩

end AVenhance.Infra.Section5.RelativeError

end
