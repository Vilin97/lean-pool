/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.IndyStepDownPartI
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Estimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzRegularityIoi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIEnergyIoi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic

/-! # Step-down part (i) wiring: `IndyStepDownPartIStatement` from the explicit inputs

`indystepdown_part_i_of_inputs` turns the conditional conjunct-(i) theorem
`indyStepDown_part_i_conditional` into the literal step-down estimate conjunct-(i) proposition
`IndyStepDownPartIStatement β C₀`, given the literal big-bound estimate proposition
    `BigBoundStatement β C₀`
(the conclusion of the public statement is taken literally) and, for each
admissible instance, the Prop-valued `IndyPartIInputs`.

Conjunct (ii) (the ratio form) is deliberately untouched.

Hypotheses of `indyStepDown_part_i_conditional` that are *derived here* and so are not fields:
* the four `MemL2On` hypotheses `hU hAT hTP hAP`.  They follow from continuity of the classical
  solutions `θ_m`, `θ_{m-1}` and of the iterate `T_{m-1}` on each time slice, continuity of the
  `ΧTilde`-corrector series of the ansatz (finite sum at fixed time of continuous terms), and the
  smoothness of the slices of `HTilde_m` at positive times (`Hm_slice_contDiff_pos`);
* the `HTilde_m` regularity (joint `C^∞` on `(0,∞) × ℝ²`, smooth and periodic positive-time slices):
  unconditional for the actual iterates (`PartIHmRegularity*`), so no longer an input;
* the classical forced energy estimate `IndyPartIInputs.energy` (with `Cenergy = 2`), proved from
  `forced_energy_estimate_Ioi` using that regularity, the ansatz regularity on the open half space
  (`ansatz_contDiffOn_two_Ioi`) and the finiteness of the `L²H⁻¹` norm of the ansatz residual
  (which follows from the big-bound estimate hypothesis);

**Open-time form.**  The `Amnr` uses two-sided time derivatives, so `θTilde_m(0)` and the
regularity of `HTilde_m` at `t = 0` depend on the arbitrary negative-time extension of `T`.
    Everything
that involves the ansatz is therefore stated for `t > 0` (initial defect as `s → 0⁺`, the ansatz
bound on `(0,1]`); `t = 0` is recovered in `indyStepDown_part_i_conditional_Ioc` from
`θ_m(0) = θ₀ = θ_{m-1}(0)` and the time-independence of the gradient term.
* the big-bound estimate hypothesis `hA7` (from the big-bound estimate body, by
    `timeHMinusOneNorm_le_of_bigbound_conclusion`);
* `0 ≤ C₇` (take `max C 0`), positivity of `κ_m`, and `hβ hβ' hΛ` (from the `Ingredients` API). -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

/-! ### Slice continuity of the pieces of the ansatz -/

section Regularity

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The spatial gradient of a `C²` function is continuous. -/
theorem continuous_spaceGrad_of_contDiff_two {g : Vec 2 → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (spaceGrad g) := by
  have hd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  exact continuous_pi fun i => hd.clm_apply continuous_const

/-- The shear field `u_{m,k}` is continuous. -/
theorem continuous_uShear (β : ℝ) (Λ m : ℕ) (k : ℤ) : Continuous (uShear β Λ m k) := by
  unfold uShear
  split_ifs
  · refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one,
    Matrix.cons_val_fin_one] <;> fun_prop
  · refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one,
    Matrix.cons_val_fin_one] <;> fun_prop
  · exact continuous_const

/-- The twisted corrector `ΧTilde_{m,k}(t,·)` is continuous at each fixed time. -/
theorem continuous_chiTilde (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) :
    Continuous (I.chiTilde hΦ m κm k t) := by
  have hflow : Continuous (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
    ((xFlowInv_joint_contDiff_one I hΦ m (lIdx β I.Λ m k)).continuous).comp
      (Continuous.prodMk_right t)
  unfold Ingredients.chiTilde Ingredients.chiMK
  exact ((continuous_uShear β I.Λ m k).const_smul (-(I.corrTime κm m k t))).comp hflow

/-- At a fixed time, the series of the ansatz is continuous in the position, provided the
iterate `T_{m-1}(t)` is `C²` in the position. -/
theorem continuous_ansatz_series (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hT : ContDiff ℝ 2 (T t)) :
    Continuous (fun x => ∑' k : ℤ, I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        (spaceGrad (fun y => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) := by
  let S : Finset ℤ := (I.xiMK_support_finite m t).toFinset
  have hzero (k : ℤ) (hk : k ∉ S) : I.xiMK m k t = 0 := by
    by_contra hne
    exact hk ((I.xiMK_support_finite m t).mem_toFinset.mpr hne)
  have hfun : (fun x => ∑' k : ℤ, I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        (spaceGrad (fun y => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) =
      fun x => ∑ k ∈ S, I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        (spaceGrad (fun y => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) := by
    funext x
    apply tsum_eq_sum
    intro k hk
    simp [hzero k hk]
  rw [hfun]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  have hflow : Continuous (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
    ((xFlowInv_joint_contDiff_one I hΦ m (lIdx β I.Λ m k)).continuous).comp
      (Continuous.prodMk_right t)
  have hcomp : ContDiff ℝ 2 (fun y => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y)) :=
    hT.comp (xFlow_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t)
  have hgrad := (continuous_spaceGrad_of_contDiff_two hcomp).comp hflow
  unfold vecDot
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp (continuous_chiTilde I hΦ m κm k t)).mul
    ((continuous_apply i).comp hgrad)

/-- The iterate `T_{m-1} = T (Nstar β)` is smooth in the position at every nonnegative time. -/
theorem tNstar_contDiff_of_nonneg {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hΦ : IsStreamSeq I Φ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (T (Nstar β) t) := by
  by_cases h0 : Nstar β = 0
  · rw [h0, hT.1]
    exact classicalSol_space_contDiff_of_nonneg hθprev ht
  · exact classicalSol_space_contDiff_of_nonneg
      (hT.2 (Nstar β) (Nat.one_le_iff_ne_zero.mpr h0) le_rfl) ht

end Regularity

/-! ### The explicit conditional theorem (constant exposed, open-time) -/

section Explicit

variable {β : ℝ} (I : Ingredients β)

/-- `AVenhance.Infra.Section5.indyStepDown_part_i_conditional` with its constant named, and with the
ansatz-dependent hypotheses on the half-open time interval `(0,1]` only.  The `Amnr` uses
two-sided time derivatives, so `θTilde_m` and `HTilde_m` at `t = 0` depend on the arbitrary
    negative-time
extension of `T`; none of the hypotheses below mentions the ansatz at `t = 0`.  The initial defect
enters through the energy hypothesis `hEnergy` (with the constant `D = Cᵢ ε^δ ‖θ₀‖`, a bound valid
for the energy estimate by `forced_energy_estimate_Ioi` once the defect is small as `s → 0⁺`).

The conclusion is still on the closed interval `[0,1]`: at `t = 0` the first term vanishes
(`θ_m(0) = θ₀ = θ_{m-1}(0)`) and the gradient term does not depend on `t`, so it is bounded by the
`t = 1` instance. -/
theorem indyStepDown_part_i_conditional_Ioc
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ I.Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsStreamSeq I Φ) (m M : ℕ) (κ : ℝ)
    (θ₀ : Vec 2 → ℝ) (θm θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hκm : 0 < I.kappaSeq κ M m)
    (hθm0 : ∀ x, θm 0 x = θ₀ x) (hθprev0 : ∀ x, θprev 0 x = θ₀ x)
    (C₇ Cᵢ Cₐ Cₜ Cenergy : ℝ)
    (hC₇ : 0 ≤ C₇) (hCenergy : 0 ≤ Cenergy)
    (hU : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => θm t x -
        I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x))
    (hAT : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => I.ansatz hΦ m (I.kappaSeq κ M m)
        (T (Nstar β)) t x - T (Nstar β) t x))
    (hTP : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => T (Nstar β) t x - θprev t x))
    (hAP : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => I.ansatz hΦ m (I.kappaSeq κ M m)
        (T (Nstar β)) t x - θprev t x))
    (hA7 : timeHMinusOneNorm (fun t x =>
      advDiffOp (streamVel (Φ m)) (I.kappaSeq κ M m)
        (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β))) t x) ≤
      ENNReal.ofReal (C₇ * epsilon β I.Λ (m - 1) ^ delta β *
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (l2NormSq θ₀)))
    (hEnergy : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x -
        I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) +
        Real.sqrt (I.kappaSeq κ M m) *
          Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (θm s) x - spaceGrad
              (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
      Cenergy * (Cᵢ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) +
        (timeHMinusOneNorm (fun s x =>
          advDiffOp (streamVel (Φ m)) (I.kappaSeq κ M m)
            (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β))) s x)).toReal /
          Real.sqrt (I.kappaSeq κ M m)))
    (hSectionFourAnsatz : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m (I.kappaSeq κ M m)
        (T (Nstar β)) t x - T (Nstar β) t x)) ≤
        Cₐ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀))
    (hSectionFourIterate : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) ≤
        Cₜ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) +
        Real.sqrt (I.kappaSeq κ M m) *
          Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (θm s) x - spaceGrad
              (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
        (Cenergy * (Cᵢ + C₇) + Cₐ + Cₜ) * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq
            θ₀) := by
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
  have henergySource : Cenergy * (Cᵢ * (e ^ d) * N +
      (timeHMinusOneNorm resid).toReal / Real.sqrt κm) ≤
      Cenergy * (Cᵢ + C₇) * (e ^ d) * N := by
    have hsum : Cᵢ * (e ^ d) * N +
        (timeHMinusOneNorm resid).toReal / Real.sqrt κm ≤
        (Cᵢ + C₇) * (e ^ d) * N := by
      nlinarith [hA7scaled]
    have hmul := mul_le_mul_of_nonneg_left hsum hCenergy
    nlinarith only [hmul]
  have hIoc : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) +
        Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (θm s) x - spaceGrad
            (I.ansatz hΦ m κm (T (Nstar β)) s) x)) ≤
        (Cenergy * (Cᵢ + C₇) + Cₐ + Cₜ) * (e ^ d) * N := by
    intro t ht
    have hEnergyBound : Real.sqrt (l2NormSq (fun x => θm t x -
          I.ansatz hΦ m κm (T (Nstar β)) t x)) +
          Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (θm s) x - spaceGrad
              (I.ansatz hΦ m κm (T (Nstar β)) s) x)) ≤
        Cenergy * (Cᵢ + C₇) * (e ^ d) * N := by
      exact (hEnergy t ht).trans henergySource
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
      simpa [e, d, N] using hSectionFourIterate t ⟨ht.1.le, ht.2⟩
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
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · -- `t = 0`: the first term vanishes and the gradient term is `t`-independent
    have hzero : (fun x => θm t x - θprev t x) = fun _ => (0 : ℝ) := by
      funext x
      rw [← h0, hθm0 x, hθprev0 x, sub_self]
    have hl2 : Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) = 0 := by
      rw [hzero]
      simp [l2NormSq]
    have h1 := hIoc 1 ⟨one_pos, le_rfl⟩
    have hnn : 0 ≤ Real.sqrt (l2NormSq (fun x => θm 1 x - θprev 1 x)) := Real.sqrt_nonneg _
    have hfin : Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
        spaceGrad (θm s) x - spaceGrad (I.ansatz hΦ m κm (T (Nstar β)) s) x)) ≤
        (Cenergy * (Cᵢ + C₇) + Cₐ + Cₜ) * (e ^ d) * N := by linarith
    rw [hl2, zero_add]
    simpa [e, d, N, κm] using hfin
  · simpa [e, d, N, κm] using hIoc t ⟨hpos, ht.2⟩

end Explicit

/-! ### The inputs structure -/

section Inputs

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The remaining estimates feeding step-down part (i), for one instance (`κm = κ_m`, `θm = θ_m`,
`θprev = θ_{m-1}`, `T = T^{(·)}` the iterates, `T_{m-1} = T (Nstar β)`).  No field is (or contains)
the step-down estimate conclusion or the big-bound estimate; the four `MemL2On` hypotheses of the
    conditional theorem, the
`HTilde_m` regularity and the classical forced energy estimate are *not* fields (see
`IndyPartIInputs.memL2` and `IndyPartIInputs.energy`).

* `hInitial`: the aggregate initial defect `‖θ_m(s) − θTilde_m(s)‖_{L²} ≤ Cᵢ ε^δ ‖θ₀‖` for all small
  `s > 0` (`s → 0⁺`; the ansatz at `t = 0` itself depends on the negative-time extension of `T`).
  Source: `e.tildethetam.to.Tm` initial data (oscillatory corrector gives `ε^{4δ}`,
  `HTilde_m` only `ε^δ`).
* `hSectionFourAnsatz`: `‖θTilde_m(t) − T_{m-1}(t)‖_{L²} ≤ Cₐ ε^δ ‖θ₀‖` for `t ∈ (0,1]`.  Source:
  `e.tildethetam.to.Tm` (8882–9133).
* `hSectionFourIterate`: `‖T_{m-1}(t) − θ_{m-1}(t)‖_{L²} ≤ Cₜ ε^δ ‖θ₀‖`.  Source: `e.Tm.thetam`
  / `l.Tm.minus.thetam`. -/
structure IndyPartIInputs (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (θ₀ : Vec 2 → ℝ)
    (θm θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ)
    (Cᵢ Cₐ Cₜ : ℝ) : Prop where
  /-- Aggregate initial defect from the right, `e.tildethetam.to.Tm` initial data. -/
  hInitial : InitialLayerContract I hΦ m κm θm T Cᵢ (Real.sqrt (l2NormSq θ₀))
  /-- `e.tildethetam.to.Tm`, 8882–9133, for `t ∈ (0,1]`. -/
  hSectionFourAnsatz : SectionFourAnsatzContract I hΦ m κm θ₀ T Cₐ
  /-- `e.Tm.thetam` / `l.Tm.minus.thetam`. -/
  hSectionFourIterate : SectionFourIterateContract I m θ₀ θprev T Cₜ

variable {I} {hΦ : IsStreamSeq I Φ} {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
  {θm θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ} {Cᵢ Cₐ Cₜ : ℝ}

/-- The four `MemL2On` hypotheses of `indyStepDown_part_i_conditional_Ioc` on `(0,1]`, derived from
the premises (`θ_m`, `θ_{m-1}` classical solutions, `T` the iterates) and the unconditional
positive-time smoothness of `HTilde_m` (`Hm_slice_contDiff_pos`; a smooth slice is continuous, hence
`L²` on the cube).  The inputs record `_h` is not used: this is a statement about the actual
iterates, stated as a method for uniformity with `IndyPartIInputs.energy`. -/
theorem IndyPartIInputs.memL2 (_h : IndyPartIInputs I hΦ m κm θ₀ θm θprev T Cᵢ Cₐ Cₜ)
    (hm : 1 ≤ m) (hκm : 0 < κm) {κ' : ℝ}
    (hθm : IsClassicalSol (streamVel (Φ m)) κ' (fun _ _ => 0) θ₀ θm)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    (∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => θm t x - I.ansatz hΦ m κm (T (Nstar β)) t x)) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => I.ansatz hΦ m κm (T (Nstar β)) t x - T (Nstar β) t x)) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => T (Nstar β) t x - θprev t x)) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => I.ansatz hΦ m κm (T (Nstar β)) t x - θprev t x)) := by
  have hH : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemL2On unitCube (fun x => I.Hm hΦ m κm (T (Nstar β)) t x) := fun t ht =>
    memL2On_unitCube_of_continuous
      (Hm_slice_contDiff_pos I hΦ hm hκm hθprev hT ht.1).continuous
  have hTs : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ContDiff ℝ ∞ (T (Nstar β) t) := fun t ht =>
    tNstar_contDiff_of_nonneg I hθprev hT ht.1.le
  have hSc : ∀ t ∈ Set.Ioc (0 : ℝ) 1, Continuous (fun x => ∑' k : ℤ, I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        (spaceGrad (fun y => T (Nstar β) t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) := fun t ht =>
    continuous_ansatz_series I hΦ m κm ((hTs t ht).of_le (by norm_num))
  have hΘ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, Continuous (θm t) := fun t ht =>
    (classicalSol_space_contDiff_of_nonneg hθm ht.1.le).continuous
  have hP : ∀ t ∈ Set.Ioc (0 : ℝ) 1, Continuous (θprev t) := fun t ht =>
    (classicalSol_space_contDiff_of_nonneg hθprev ht.1.le).continuous
  have hTc : ∀ t ∈ Set.Ioc (0 : ℝ) 1, Continuous (T (Nstar β) t) := fun t ht =>
    (hTs t ht).continuous
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have hc : Continuous (fun x => θm t x - T (Nstar β) t x - ∑' k : ℤ, I.xiMK m k t *
        vecDot (I.chiTilde hΦ m κm k t x)
          (spaceGrad (fun y => T (Nstar β) t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) :=
      ((hΘ t ht).sub (hTc t ht)).sub (hSc t ht)
    have := (memL2On_unitCube_of_continuous hc).sub (hH t ht)
    convert this using 1
    funext x
    simp only [Ingredients.ansatz, Pi.sub_apply]
    ring
  · have := (memL2On_unitCube_of_continuous (hSc t ht)).add (hH t ht)
    convert this using 1
    funext x
    simp only [Ingredients.ansatz, Pi.add_apply]
    ring
  · exact memL2On_unitCube_of_continuous ((hTc t ht).sub (hP t ht))
  · have hc : Continuous (fun x => T (Nstar β) t x - θprev t x + ∑' k : ℤ, I.xiMK m k t *
        vecDot (I.chiTilde hΦ m κm k t x)
          (spaceGrad (fun y => T (Nstar β) t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) :=
      ((hTc t ht).sub (hP t ht)).add (hSc t ht)
    have := (memL2On_unitCube_of_continuous hc).add (hH t ht)
    convert this using 1
    funext x
    simp only [Ingredients.ansatz, Pi.add_apply]
    ring

/-- The iterate `T_{m-1} = T (Nstar β)` is a classical solution of some forced equation (for
`Nstar β = 0` it is `θ_{m-1}`), hence jointly smooth and periodic in the position. -/
theorem tNstar_isClassicalSol {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {hΦ : IsStreamSeq I Φ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ∃ F : ℝ → Vec 2 → ℝ,
      IsClassicalSol (streamVel (Φ (m - 1))) κprev F θ₀ (T (Nstar β)) := by
  by_cases h0 : Nstar β = 0
  · rw [h0, hT.1]
    exact ⟨_, hθprev⟩
  · exact ⟨_, hT.2 (Nstar β) (Nat.one_le_iff_ne_zero.mpr h0) le_rfl⟩

/-- **The classical forced energy estimate for `θ_m − θTilde_m`** (`Cenergy = 2`) on `(0,1]`,
    derived
    from
`forced_energy_estimate_Ioi` with `u = θ_m`, `v = θTilde_m`, `φ = Φ m`: the admissibility of `Φ m`
    is
`hΦ.adm_pred (m + 1)`, the regularity of the ansatz on the open half space comes from the
unconditional `HTilde_m` regularity (`PartIHmRegularity*`) and the iterate `T_{m-1}`, the initial
    defect
is the field `hInitial` (as `s → 0⁺`), and `hfin` is the finiteness of the `L²H⁻¹` norm of the
ansatz residual. -/
theorem IndyPartIInputs.energy (h : IndyPartIInputs I hΦ m κm θ₀ θm θprev T Cᵢ Cₐ Cₜ)
    (hm : 1 ≤ m) (hκm : 0 < κm)
    (hθm : IsClassicalSol (streamVel (Φ m)) κm (fun _ _ => 0) θ₀ θm)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hfin : timeHMinusOneNorm (fun s x =>
      advDiffOp (streamVel (Φ m)) κm (I.ansatz hΦ m κm (T (Nstar β))) s x) ≠ ⊤) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x -
        I.ansatz hΦ m κm (T (Nstar β)) t x)) +
        Real.sqrt κm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (θm s) x - spaceGrad (I.ansatz hΦ m κm (T (Nstar β)) s) x)) ≤
      2 * (Cᵢ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) +
        (timeHMinusOneNorm (fun s x =>
          advDiffOp (streamVel (Φ m)) κm
            (I.ansatz hΦ m κm (T (Nstar β))) s x)).toReal / Real.sqrt κm) := by
  have hadm : IsAdmissibleStream (Φ m) := by
    simpa using hΦ.adm_pred (m + 1)
  obtain ⟨F, hF⟩ := tNstar_isClassicalSol (I := I) hθprev hT
  have hTjoint : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => T (Nstar β) p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    hF.1.mono (Set.prod_mono Set.Ioi_subset_Ici_self le_rfl)
  have hHjoint := Hm_contDiffOn_Ioi_top I hΦ hm hκm hθprev hT
  have hv : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.ansatz hΦ m κm (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    ansatz_contDiffOn_two_Ioi I hΦ m κm hTjoint (hHjoint.of_le (by simp))
  have hvs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (I.ansatz hΦ m κm (T (Nstar β)) t) :=
    fun t ht => ansatz_slice_contDiff I hΦ m κm
      (classicalSol_space_contDiff_of_nonneg hF ht.le)
      (Hm_slice_contDiff_pos I hΦ hm hκm hθprev hT ht)
  have hvp : ∀ t, 0 < t → IsZ2Periodic (I.ansatz hΦ m κm (T (Nstar β)) t) :=
    fun t ht => ansatz_periodic I hΦ m κm
      ((classicalSol_space_contDiff_of_nonneg hF ht.le).of_le (by norm_num)) (hF.2.1 t ht.le)
      (Hm_periodic_pos I hΦ hm hκm hθprev hT ht)
  exact forced_energy_estimate_Ioi hadm hκm hθm hv hvs hvp hfin h.hInitial

end Inputs

/-! ### The step-down part (i) wiring theorem -/

/-- **Family contract for step-down part (i)** (`IndyStepDownV2Inputs.partI`): constants `C₁`
    (Λ-threshold), `Cᵢ`,
`Cₐ`, `Cₜ` chosen before `I`, then `IndyPartIInputs` on the step-down premise block
    `OnA8Instances`. -/
def PartIFamilyContract (β C₀ : ℝ) : Prop :=
  ∃ C₁ Cᵢ Cₐ Cₜ : ℝ, OnA8Instances β C₀ C₁ (fun I _Φ hΦ κ M _R θ₀ m θm θprev T =>
    IndyPartIInputs I hΦ m (I.kappaSeq κ M m) θ₀ θm θprev T Cᵢ Cₐ Cₜ)

/-- **Step-down part (i) wiring.**  Given the big-bound estimate proposition `BigBoundStatement β
    C₀` and, for every
admissible instance with `C₁ ≤ Λ`, the explicit `IndyPartIInputs` (the remaining
    §4/initial-layer/energy
estimates), the step-down estimate conjunct-(i) proposition `IndyStepDownPartIStatement β C₀`
    holds with
`C = max (max C₇ C₁) (2 * (Cᵢ + max C₇ 0) + Cₐ + Cₜ)`, `C₇` the big-bound estimate constant. -/
theorem indystepdown_part_i_of_inputs (β C₀ : ℝ)
    (hA7 : BigBoundStatement β C₀)
    (hin : PartIFamilyContract β C₀) :
    IndyStepDownPartIStatement β C₀ := by
  obtain ⟨C₇', hA7'⟩ := hA7
  obtain ⟨C₁, Cᵢ, Cₐ, Cₜ, h⟩ := hin
  refine ⟨max (max C₇' C₁) (2 * (Cᵢ + max C₇' 0) + Cₐ + Cₜ), ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T
    hθm hθprev hT
  have hΛ7 : C₇' ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ
  have hΛ1 : C₁ ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ
  have hinp := h I hz hx hh hΛ1 Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
    θm θprev T hθm hθprev hT
  have h7 := hA7' I hz hx hh hΛ7 Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
    θprev T hθprev hT
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hepos : ∀ n : ℕ, 0 < epsilon β I.Λ n := fun n =>
    Infra.Cutoff.epsilon_pos hβ hβ' I.two_pow_seven_le
  have hκpos : 0 < κ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos (hepos M) _))
      (Set.mem_Icc.mp hperm).1
  have hκm : 0 < I.kappaSeq κ M m := LeftToShow.kappaSeq_pos I hκpos M m
  have hm1 : 1 ≤ m := by
    have hstar : 2 ≤ mTheta0 β I.Λ R := (mTheta0_spec hβ hβ' I.two_pow_seven_le hR).1
    omega
  obtain ⟨hU, hAT, hTP, hAP⟩ := hinp.memL2 hm1 hκm hθm hθprev hT
  have hN0 : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hed0 : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β := Real.rpow_nonneg (hepos _).le _
  have hA7real : timeHMinusOneNorm (fun t x =>
      advDiffOp (streamVel (Φ m)) (I.kappaSeq κ M m)
        (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β))) t x) ≤
      ENNReal.ofReal (max C₇' 0 * epsilon β I.Λ (m - 1) ^ delta β *
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (l2NormSq θ₀)) := by
    refine (timeHMinusOneNorm_le_of_bigbound_conclusion h7 hκm).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hsq : 0 ≤ Real.sqrt (I.kappaSeq κ M m) := Real.sqrt_nonneg _
    have hle : C₇' * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) ≤
        max C₇' 0 * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hed0) hN0
    calc C₇' * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) *
          Real.sqrt (I.kappaSeq κ M m)
        ≤ max C₇' 0 * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) *
          Real.sqrt (I.kappaSeq κ M m) := mul_le_mul_of_nonneg_right hle hsq
      _ = max C₇' 0 * epsilon β I.Λ (m - 1) ^ delta β *
          Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (l2NormSq θ₀) := by ring
  have hEnergy := hinp.energy hm1 hκm hθm hθprev hT
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA7real)
  have hmain := indyStepDown_part_i_conditional_Ioc I hβ hβ' I.two_pow_seven_le Φ hΦ m M κ θ₀
    θm θprev T hκm hθm.2.2.1 hθprev.2.2.1 (max C₇' 0) Cᵢ Cₐ Cₜ 2 (le_max_right _ _)
    (by norm_num) hU hAT hTP hAP hA7real hEnergy hinp.hSectionFourAnsatz
    hinp.hSectionFourIterate
  intro t ht
  refine (hmain t ht).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hed0) hN0

/-- Step-down estimate conjunct (i) from the big-bound estimate input list and the step-down part
    (i) input list (composition of
`bigbound_of_inputs` and `indystepdown_part_i_of_inputs`); no statement file is used. -/
theorem indystepdown_part_i_of_all_inputs (β C₀ : ℝ)
    (hbb : BigBoundFamilyContract β C₀)
    (hin : PartIFamilyContract β C₀) :
    IndyStepDownPartIStatement β C₀ :=
  indystepdown_part_i_of_inputs β C₀ (bigbound_of_inputs β C₀ hbb) hin

end AVenhance.Infra.Section5.Integration
end
