/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Amnr
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowIsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Continuity
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Base infrastructure for the AMNR tensors. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Material differentiation in the coordinates used by the recurrence. -/
def amnrMaterial (b : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  deriv (fun s => f s x) t + vecDot (b t x) (AVenhance.spaceGrad (f t) x)

/-- A cutoff-flow average with a freely chosen factor in each summand. -/
def amnrFlowAverageGen {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (Q : ℤ → (ℝ × Vec 2) → Fin 2 → Fin 2 → ℝ)
    (j k i p : Fin 2) (z : ℝ × Vec 2) : ℝ :=
  ∑' l : ℤ, I.hatXiML m l z.1 *
    (Q l z i j * I.flowGrad hΦ m l z.1 z.2 k p)

/-- A general memory multiplier for a cutoff-flow factor. -/
def amnrSeedMultiplierGen {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (n : ℕ) (Q : ℤ → (ℝ × Vec 2) → Fin 2 → Fin 2 → ℝ)
    (j k i p : Fin 2) (z : ℝ × Vec 2) : ℝ :=
  -(I.LMN κ m n z.1) * amnrFlowAverageGen I hΦ m Q j k i p z

/-- The left-Jacobian seed factor, with `(F_l)ᵀ_{ij}` inside the same cutoff sum
as `(F_l)_{kp}`. -/
def amnrSeedMultiplierA0Plus {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (n : ℕ) (j k i p : Fin 2) (z : ℝ × Vec 2) : ℝ :=
  amnrSeedMultiplierGen I hΦ m κ n
    (fun l z i j => I.flowGrad hΦ m l z.1 z.2 j i) j k i p z

/-- Cutoff average in the left-Jacobian seed. -/
def amnrFlowAverageA0Plus {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (j k i p : Fin 2) (z : ℝ × Vec 2) : ℝ :=
  amnrFlowAverageGen I hΦ m
    (fun l z i j => I.flowGrad hΦ m l z.1 z.2 j i) j k i p z

/-- Exact recurrence, with its minus sign and tensor contraction. -/
theorem Amnr_succ {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (n : ℕ) (T : ℝ → Vec 2 → ℝ)
    (r : ℕ) (t : ℝ) (x : Vec 2) (i j k : Fin 2) :
    I.Amnr hΦ m κ n T (r + 1) t x i j k =
      amnrMaterial (AVenhance.streamVel (Φ (m - 1)))
        (fun s y => I.Amnr hΦ m κ n T r s y i j k) t x -
        ∑ p : Fin 2, AVenhance.spaceGrad
          (fun y => AVenhance.streamVel (Φ (m - 1)) t y i) x p *
          I.Amnr hΦ m κ n T r t x p j k := rfl

/-- The corrected truncation leaves one spatial derivative at the remainder. -/
theorem Jcut_budget {β : ℝ} (hN : 1 ≤ AVenhance.Nstar β) :
    2 * AVenhance.Jcut β + 1 ≤ AVenhance.Nstar β := by
  unfold AVenhance.Jcut
  omega

/-- Measurability of the flow-gradient entries follows from joint flow continuity. -/
theorem flowGrad_measurable {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (k p : Fin 2) :
    Measurable (fun z : ℝ × Vec 2 => I.flowGrad hΦ m l z.1 z.2 k p) := by
  let b := AVenhance.streamVel (Φ (m - 1))
  have hb := (hΦ.adm_pred m).vel_continuous
  have hL := (hΦ.adm_pred m).vel_lipschitz
  have hflow := AVenhance.flow_isFlow b hb hL
  obtain ⟨L, hLip⟩ := hL
  have hc := Flow.flow_continuous_joint b hLip hflow
  have hX : Continuous (fun z : ℝ × Vec 2 => I.xFlow hΦ m l z.1 z.2) := by
    change Continuous (fun z : ℝ × Vec 2 => AVenhance.flow b hb ⟨L, hLip⟩
      z.1 z.2 ((l : ℝ) * AVenhance.tauPP β I.Λ m))
    exact hc.comp (show Continuous (fun z : ℝ × Vec 2 =>
      (z.1, z.2, (l : ℝ) * AVenhance.tauPP β I.Λ m)) by fun_prop)
  have hInv : Continuous (fun z : ℝ × Vec 2 => I.xFlowInv hΦ m l z.1 z.2) := by
    change Continuous (fun z : ℝ × Vec 2 => AVenhance.flow b hb ⟨L, hLip⟩
      ((l : ℝ) * AVenhance.tauPP β I.Λ m) z.2 z.1)
    exact hc.comp (show Continuous (fun z : ℝ × Vec 2 =>
      ((l : ℝ) * AVenhance.tauPP β I.Λ m, z.2, z.1)) by fun_prop)
  have hXp : Continuous (fun z : ℝ × Vec 2 => I.xFlow hΦ m l z.1 z.2 p) := by
    exact (continuous_apply p).comp hX
  have hd := measurable_fderiv_apply_const_with_param ℝ
    (f := fun t x => I.xFlow hΦ m l t x p) hXp (basisVec k)
  exact hd.comp ((continuous_fst.prodMk hInv).measurable)

/-- Explicit finite-order memory constant, uniform in n and the scale. -/
def amnrMemoryConstant (β C₀ : ℝ) : ℝ :=
  ((AVenhance.Nstar β).factorial : ℝ) * 2 ^ AVenhance.Nstar β *
    2 ^ AVenhance.Nstar β * C₀ ^ 2 / (2 * Real.pi ^ 2)

end AVenhance.Infra.Section4
