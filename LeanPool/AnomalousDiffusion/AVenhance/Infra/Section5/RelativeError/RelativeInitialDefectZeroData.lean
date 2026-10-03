/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectContractPositive
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaClassicalUniqueness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Uniqueness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergyClassical

/-! Exact zero-amplitude initial layer. Homogeneous classical uniqueness and
the actual T forcing recursion are used, independently of negative times. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

theorem RelativeInitialDefectZeroData.relative_zero_data_classical_solution
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {F : ℝ → Vec 2 → ℝ}
    (hF : ∀ t : ℝ, 0 < t → ∀ x, F t x = 0) :
    IsClassicalSol (streamVel φ) κ F (fun _ : Vec 2 => 0) (fun _ _ => 0) := by
  refine ⟨contDiffOn_const, ?_, ?_, ?_⟩
  · intro t ht k x
    rfl
  · intro x
    rfl
  · intro t ht x
    simp [advDiffOp, spaceLap, spaceGrad, Homogenization.vecDot, hF t ht x]

theorem RelativeInitialDefectZeroData.relative_zero_data_solution_is_zero
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {κ : ℝ}
    (hκ : 0 < κ) {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) (fun _ => 0) θ) :
    ∀ t : ℝ, 0 ≤ t → θ t = fun _ => 0 := by
  have hz := RelativeInitialDefectZeroData.relative_zero_data_classical_solution (φ := φ) (κ := κ)
      (F := fun _ _ => 0)
    (by intro t ht x; rfl)
  have heq := AVenhance.Infra.Classical.streamVel_classical_unique φ hφ κ hκ (fun _ _ => 0)
    (fun _ => 0) (θ := θ) (ψ := fun _ _ => 0) hθ hz
  intro t ht
  funext x
  exact (heq t ht x).symm

theorem relative_initial_TIterates_zero_of_zero_data
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} {κm κprev : ℝ}
    (hκprev : 0 < κprev) {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) (fun _ => 0) θprev)
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev (fun _ => 0) θprev T) :
    ∀ i : ℕ, i ≤ Nstar β → ∀ t : ℝ, 0 ≤ t → T i t = fun _ => 0 := by
  have hφ : IsAdmissibleStream (Φ (m - 1)) :=
    hΦ.adm_pred m
  have hprevZero := RelativeInitialDefectZeroData.relative_zero_data_solution_is_zero hφ hκprev
      hθprev
  intro i
  induction i with
  | zero =>
      intro hi t ht
      rw [hT.1]
      exact hprevZero t ht
  | succ i ih =>
      intro hi t ht
      let F : ℝ → Vec 2 → ℝ := I.TForcing hΦ m κm κprev (T i)
      have hFzero : ∀ s : ℝ, 0 < s → ∀ x, F s x = 0 := by
        intro s hs x
        have hTiZero := ih (by omega) s hs.le
        have hgrad : spaceGrad (T i s) = 0 := by
          rw [hTiZero]
          funext x j
          simp [spaceGrad]
        simp [F, Ingredients.TForcing, hgrad, AVenhance.vecDiv, Matrix.mulVec_zero,
          spaceGrad]
      have hTi : IsClassicalSol (streamVel (Φ (m - 1))) κprev F
          (fun _ => 0) (T (i + 1)) := by
        simpa [F, Nat.add_sub_cancel] using
          hT.2 (i + 1) (by omega) (by omega : i + 1 ≤ Nstar β)
      have hzTi := RelativeInitialDefectZeroData.relative_zero_data_classical_solution (φ := Φ (m
          - 1))
        (κ := κprev) (F := F) hFzero
      have heq := AVenhance.Infra.Classical.streamVel_classical_unique
        (Φ (m - 1)) hφ κprev hκprev F
        (fun _ => 0) hTi hzTi
      funext x
      exact (heq t ht x).symm

/-- A vanishing previous-scale dissipation amplitude forces the datum to zero
by the mean-zero classical energy lower bound. -/
theorem relative_initial_datum_zero_of_amplitude_zero
    {φ : ℝ → Vec 2 → ℝ} {ν : ℝ} {g : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (hν : 0 < ν)
    (hsol : IsClassicalSol (streamVel φ) ν (fun _ _ => 0) g θ)
    (hmean : MeanZeroOn unitCube g)
    (hS : Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x)) = 0) :
    g = 0 := by
  have hroot : Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x)) = 0 :=
    (mul_eq_zero.mp hS).resolve_left (Real.sqrt_pos.2 hν).ne'
  have henergy : spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x) = 0 := by
    have he0 : 0 ≤ spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x) :=
      integral_nonneg fun _ => vecNormSq_nonneg _
    have hs := congrArg (fun z : ℝ => z ^ 2) hroot
    simpa only [Real.sq_sqrt he0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hs
  have hlower := classical_dissipation_lower hφ hν hsol hmean
  rw [henergy, mul_zero] at hlower
  have hfactor : 0 < min (1 / 4 : ℝ) (2 * Real.pi ^ 2 * ν) := by positivity
  have hnorm : l2NormSq g = 0 := le_antisymm
    (nonpos_of_mul_nonpos_right hlower hfactor) (integral_nonneg fun _ => sq_nonneg _)
  have hg0 : θ 0 = g := funext hsol.2.2.1
  have hgs := AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hsol.1 (t := 0) le_rfl
  rw [hg0] at hgs
  have hgp := hsol.2.1 0 le_rfl
  rw [hg0] at hgp
  exact AVenhance.Infra.Section4.theta_continuous_periodic_eq_zero_of_l2NormSq_eq_zero hgs hgp hnorm

/-- Exact actual error vanishes at small positive times when the datum is zero
and the proved Hm bound has zero amplitude. -/
theorem relative_initial_defect_zero_of_zero_data {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν)
    {g : Vec 2 → ℝ} {θm θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol (streamVel (Φ m)) κ (fun _ _ => 0) g θm)
    (hp : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κ ν g θprev T) (hg : g = 0)
    (hHm : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (I.Hm hΦ m κ (T (Nstar β)) s)) ≤ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Real.sqrt (l2NormSq (fun x => θm s x -
      I.ansatz hΦ m κ (T (Nstar β)) s x)) = 0 := by
  have hu' : IsClassicalSol (streamVel (Φ m)) κ (fun _ _ => 0) (fun _ => 0) θm := by
    simpa only [hg, Pi.zero_def] using hu
  have hp' : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) (fun _ => 0) θprev := by
    simpa only [hg, Pi.zero_def] using hp
  have hT' : I.IsTIterates hΦ m κ ν (fun _ => 0) θprev T := by
    simpa only [hg, Pi.zero_def] using hT
  have hφm : IsAdmissibleStream (Φ m) := by
    simpa only [Nat.add_sub_cancel] using hΦ.adm_pred (m + 1)
  have huZero := RelativeInitialDefectZeroData.relative_zero_data_solution_is_zero hφm hκ hu'
  have hTZero := relative_initial_TIterates_zero_of_zero_data I hΦ hν hp' hT'
  filter_upwards [hHm, self_mem_nhdsWithin] with t ht htpos
  have hUzero : T (Nstar β) t = fun _ => 0 := hTZero _ le_rfl t htpos.le
  have hHzero : Real.sqrt (l2NormSq (I.Hm hΦ m κ (T (Nstar β)) t)) = 0 :=
    le_antisymm ht (Real.sqrt_nonneg _)
  have hansatz : I.ansatz hΦ m κ (T (Nstar β)) t = I.Hm hΦ m κ (T (Nstar β)) t := by
    funext x
    rw [Ingredients.ansatz, hUzero]
    have hsum : (∑' k : ℤ, I.xiMK m k t * vecDot (I.chiTilde hΦ m κ k t x)
        (spaceGrad (fun y => (fun _ : Vec 2 => (0 : ℝ))
          (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) = 0 := by
      calc
        _ = ∑' k : ℤ, (0 : ℝ) := tsum_congr fun k => by simp [spaceGrad, vecDot]
        _ = 0 := tsum_zero
    rw [hsum]
    simp only [zero_add]
  have hdiff : (fun x => θm t x - I.ansatz hΦ m κ (T (Nstar β)) t x) =
      fun x => -(I.Hm hΦ m κ (T (Nstar β)) t x) := by
    funext x
    rw [huZero t htpos.le, hansatz]
    simp only [zero_sub]
  rw [hdiff]
  have hneg : l2NormSq (fun x => -(I.Hm hΦ m κ (T (Nstar β)) t x)) =
      l2NormSq (I.Hm hΦ m κ (T (Nstar β)) t) := by
    unfold l2NormSq
    simp only [neg_sq]
  rw [hneg, hHzero]

end AVenhance.Infra.Section5.RelativeError
