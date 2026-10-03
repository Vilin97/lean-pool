/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.WeakBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Ansatz
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsTIterates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents

/-! Conditional infrastructure for conjunct (i) of step-down estimate.  The step-down estimate and
    big-bound estimate
statement modules are intentionally not imported.  Their source-scale estimates,
the corrected initial-data estimate, and the classical forced-energy estimate
enter as separate hypotheses below. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open AVenhance
open AVenhance.Infra.Torus
open scoped ENNReal

namespace AVenhance.Infra.Section5

theorem IndyStepDownPartI.transfer_add {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    (hg : MemL2On unitCube g) :
    Infra.Heat.frozenCellToTorusL2 (hf.add hg) =
      Infra.Heat.frozenCellToTorusL2 hf + Infra.Heat.frozenCellToTorusL2 hg := by
  apply Lp.ext
  have h1 := (Infra.Heat.memLp_frozenCellTransfer hf).coeFn_toLp
  have h2 := (Infra.Heat.memLp_frozenCellTransfer hg).coeFn_toLp
  have h3 := (Infra.Heat.memLp_frozenCellTransfer (hf.add hg)).coeFn_toLp
  filter_upwards [h1, h2, h3,
    Lp.coeFn_add (Infra.Heat.frozenCellToTorusL2 hf)
      (Infra.Heat.frozenCellToTorusL2 hg)] with x hx1 hx2 hx3 hx4
  change (Infra.Heat.frozenCellToTorusL2 (hf.add hg) :
    UnitAddTorus (Fin 2) → ℂ) x = _ at hx3
  change (Infra.Heat.frozenCellToTorusL2 hf : UnitAddTorus (Fin 2) → ℂ) x = _ at hx1
  change (Infra.Heat.frozenCellToTorusL2 hg : UnitAddTorus (Fin 2) → ℂ) x = _ at hx2
  rw [hx3, hx4]
  simp only [Pi.add_apply]
  rw [hx1, hx2]
  simp only [periodicToTorus, Complex.ofReal_add]

theorem IndyStepDownPartI.transfer_norm {f : Vec 2 → ℝ} (hf : MemL2On unitCube f) :
    ‖Infra.Heat.frozenCellToTorusL2 hf‖ = Real.sqrt (l2NormSq f) := by
  rw [← Infra.Heat.normSq_frozenCellToTorusL2_eq hf,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Minkowski's inequality in the actual cell L2 carrier. -/
theorem sqrt_l2NormSq_add_le {f g : Vec 2 → ℝ}
    (hf : MemL2On unitCube f) (hg : MemL2On unitCube g) :
    Real.sqrt (l2NormSq (fun x => f x + g x)) ≤
      Real.sqrt (l2NormSq f) + Real.sqrt (l2NormSq g) := by
  have hnorm := norm_add_le
    (Infra.Heat.frozenCellToTorusL2 hf) (Infra.Heat.frozenCellToTorusL2 hg)
  rw [← IndyStepDownPartI.transfer_add hf hg, IndyStepDownPartI.transfer_norm (hf.add hg),
      IndyStepDownPartI.transfer_norm hf,
    IndyStepDownPartI.transfer_norm hg] at hnorm
  exact hnorm

variable {β : ℝ} (I : Ingredients β)

/-- Conjunct (i) of step-down estimate, conditional on the independently sourced big-bound estimate,
Section 4 approximation, initial-defect, and classical energy estimates.

hA7 is the real source-scale form of the big-bound estimate assembly bound. hEnergy is
the forced energy estimate for the actual difference theta_m - theta_tilde_m;
its right side uses only that difference's initial datum and the normalized
negative norm of the ansatz residual. hInitial is the aggregate initial defect
bound at scale epsilon^delta. The identity below gives epsilon^(4 delta)
for the oscillatory corrector contribution; the separate H_m term in
e.Hm.Linfty is only controlled at epsilon^delta. The two Section 4 inputs are
the L2 bounds corresponding to e.tildethetam.to.Tm and e.Tm.thetam.
No step-down estimate conclusion is assumed. -/
theorem indyStepDown_part_i_conditional
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ I.Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsStreamSeq I Φ) (m M : ℕ) (κ : ℝ)
    (θ₀ : Vec 2 → ℝ) (θm θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hκm : 0 < I.kappaSeq κ M m)
    (_hT : I.IsTIterates hΦ m (I.kappaSeq κ M m)
      (I.kappaSeq κ M (m - 1)) θ₀ θprev T)
    (C₇ Cᵢ Cₐ Cₜ Cenergy : ℝ)
    (hC₇ : 0 ≤ C₇) (hCenergy : 0 ≤ Cenergy)
    (hU : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MemL2On unitCube (fun x => θm t x -
        I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x))
    (hAT : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MemL2On unitCube (fun x => I.ansatz hΦ m (I.kappaSeq κ M m)
        (T (Nstar β)) t x - T (Nstar β) t x))
    (hTP : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MemL2On unitCube (fun x => T (Nstar β) t x - θprev t x))
    (hAP : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MemL2On unitCube (fun x => I.ansatz hΦ m (I.kappaSeq κ M m)
        (T (Nstar β)) t x - θprev t x))
    (hA7 : timeHMinusOneNorm (fun t x =>
      advDiffOp (streamVel (Φ m)) (I.kappaSeq κ M m)
        (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β))) t x) ≤
      ENNReal.ofReal (C₇ * epsilon β I.Λ (m - 1) ^ delta β *
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (l2NormSq θ₀)))
    (hInitial : Real.sqrt (l2NormSq (fun x => θm 0 x -
      I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) 0 x)) ≤
      Cᵢ * epsilon β I.Λ (m - 1) ^ delta β *
        Real.sqrt (l2NormSq θ₀))
    (hEnergy : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x -
        I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) +
        Real.sqrt (I.kappaSeq κ M m) *
          Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (θm s) x - spaceGrad
              (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
      Cenergy * (Real.sqrt (l2NormSq (fun x => θm 0 x -
        I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) 0 x)) +
        (timeHMinusOneNorm (fun s x =>
          advDiffOp (streamVel (Φ m)) (I.kappaSeq κ M m)
            (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β))) s x)).toReal /
          Real.sqrt (I.kappaSeq κ M m)))
    (hSectionFourAnsatz : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m (I.kappaSeq κ M m)
        (T (Nstar β)) t x - T (Nstar β) t x)) ≤
        Cₐ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀))
    (hSectionFourIterate : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) ≤
        Cₜ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) +
        Real.sqrt (I.kappaSeq κ M m) *
          Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (θm s) x - spaceGrad
              (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
        C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by
  let e : ℝ := epsilon β I.Λ (m - 1)
  let d : ℝ := delta β
  let N : ℝ := Real.sqrt (l2NormSq θ₀)
  let κm : ℝ := I.kappaSeq κ M m
  let resid : ℝ → Vec 2 → ℝ := fun t x =>
    advDiffOp (streamVel (Φ m)) κm (I.ansatz hΦ m κm (T (Nstar β))) t x
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hA7scaled : (timeHMinusOneNorm resid).toReal / Real.sqrt κm ≤
      C₇ * (e ^ d) * N := by
    have hbound : timeHMinusOneNorm resid ≤ ENNReal.ofReal
        (C₇ * (e ^ d) * Real.sqrt κm * N) := by
      simpa only [resid, κm, e, d, mul_assoc] using hA7
    have hnonneg : 0 ≤ C₇ * (e ^ d) * Real.sqrt κm * N := by positivity
    have hreal := ENNReal.toReal_mono (by simp) hbound
    rw [ENNReal.toReal_ofReal hnonneg] at hreal
    have hκroot : 0 < Real.sqrt κm := Real.sqrt_pos.2 hκm
    rw [div_le_iff₀ hκroot]
    nlinarith [hreal]
  have hInitialδ : Real.sqrt (l2NormSq (fun x => θm 0 x -
      I.ansatz hΦ m κm (T (Nstar β)) 0 x)) ≤ Cᵢ * (e ^ d) * N := by
    simpa [e, d, N] using hInitial
  have henergySource : Cenergy * (Real.sqrt (l2NormSq (fun x => θm 0 x -
      I.ansatz hΦ m κm (T (Nstar β)) 0 x)) +
      (timeHMinusOneNorm resid).toReal / Real.sqrt κm) ≤
      Cenergy * (Cᵢ + C₇) * (e ^ d) * N := by
    have hsum : Real.sqrt (l2NormSq (fun x => θm 0 x -
        I.ansatz hΦ m κm (T (Nstar β)) 0 x)) +
        (timeHMinusOneNorm resid).toReal / Real.sqrt κm ≤
        (Cᵢ + C₇) * (e ^ d) * N := by
      nlinarith [hInitialδ, hA7scaled]
    have hmul := mul_le_mul_of_nonneg_left hsum hCenergy
    nlinarith only [hmul]
  refine ⟨Cenergy * (Cᵢ + C₇) + Cₐ + Cₜ, ?_⟩
  intro t ht
  have hEnergyAt := hEnergy t ht
  have hEnergyBound : Real.sqrt (l2NormSq (fun x => θm t x -
        I.ansatz hΦ m κm (T (Nstar β)) t x)) +
        Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (θm s) x - spaceGrad
            (I.ansatz hΦ m κm (T (Nstar β)) s) x)) ≤
      Cenergy * (Cᵢ + C₇) * (e ^ d) * N := by
    exact hEnergyAt.trans henergySource
  have hTriInner := sqrt_l2NormSq_add_le
    (hAT t ht) (hTP t ht)
  have hSumEq : (fun x => I.ansatz hΦ m κm (T (Nstar β)) t x - θprev t x) =
      (fun x => (I.ansatz hΦ m κm (T (Nstar β)) t x -
        T (Nstar β) t x) + (T (Nstar β) t x - θprev t x)) := by
    funext x
    ring
  have hApproxTri : Real.sqrt (l2NormSq (fun x =>
      I.ansatz hΦ m κm (T (Nstar β)) t x - θprev t x)) ≤
      Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κm
        (T (Nstar β)) t x - T (Nstar β) t x)) +
      Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) := by
    simpa [κm, ← hSumEq] using hTriInner
  have hTriOuter := sqrt_l2NormSq_add_le (hU t ht) (hAP t ht)
  have hOuterEq : (fun x => θm t x - θprev t x) =
      (fun x => (θm t x - I.ansatz hΦ m κm (T (Nstar β)) t x) +
        (I.ansatz hΦ m κm (T (Nstar β)) t x - θprev t x)) := by
    funext x
    ring
  have hThetaTri : Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤
      Real.sqrt (l2NormSq (fun x => θm t x -
        I.ansatz hΦ m κm (T (Nstar β)) t x)) +
      Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κm
        (T (Nstar β)) t x - θprev t x)) := by
    simpa [κm, ← hOuterEq] using hTriOuter
  have ha : Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κm
      (T (Nstar β)) t x - T (Nstar β) t x)) ≤ Cₐ * (e ^ d) * N := by
    simpa [e, d, N] using hSectionFourAnsatz t ht
  have ht' : Real.sqrt (l2NormSq (fun x =>
      T (Nstar β) t x - θprev t x)) ≤ Cₜ * (e ^ d) * N := by
    simpa [e, d, N] using hSectionFourIterate t ht
  have hAnsatzSource : Real.sqrt (l2NormSq (fun x =>
      I.ansatz hΦ m κm (T (Nstar β)) t x - θprev t x)) ≤
      (Cₐ + Cₜ) * (e ^ d) * N := by
    calc
      _ ≤ Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κm
          (T (Nstar β)) t x - T (Nstar β) t x)) +
          Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) :=
        hApproxTri
      _ ≤ Cₐ * (e ^ d) * N + Cₜ * (e ^ d) * N := add_le_add ha ht'
      _ = (Cₐ + Cₜ) * (e ^ d) * N := by ring
  have hfinal :
      Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) +
        Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (θm s) x - spaceGrad
            (I.ansatz hΦ m κm (T (Nstar β)) s) x)) ≤
        (Cenergy * (Cᵢ + C₇) + Cₐ + Cₜ) * (e ^ d) * N := by
    calc
      _ ≤ (Real.sqrt (l2NormSq (fun x => θm t x -
        I.ansatz hΦ m κm (T (Nstar β)) t x)) +
        Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (θm s) x - spaceGrad
            (I.ansatz hΦ m κm (T (Nstar β)) s) x))) +
        Real.sqrt (l2NormSq (fun x =>
          I.ansatz hΦ m κm (T (Nstar β)) t x - θprev t x)) :=
        by linarith [hThetaTri]
      _ ≤ Cenergy * (Cᵢ + C₇) * (e ^ d) * N +
          Real.sqrt (l2NormSq (fun x =>
            I.ansatz hΦ m κm (T (Nstar β)) t x - θprev t x)) :=
        by linarith [hEnergyBound]
      _ ≤ Cenergy * (Cᵢ + C₇) * (e ^ d) * N +
          (Cₐ + Cₜ) * (e ^ d) * N := by linarith [hAnsatzSource]
      _ = (Cenergy * (Cᵢ + C₇) + Cₐ + Cₜ) * (e ^ d) * N := by ring
  simpa [e, d, N, κm] using hfinal

end AVenhance.Infra.Section5

end
