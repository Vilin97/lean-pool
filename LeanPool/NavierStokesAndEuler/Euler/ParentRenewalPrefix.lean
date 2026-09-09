/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! Finite-prefix control of the actual coupling recurrence. Each step
may use only the bounds already proved on its preceding prefix. -/

@[expose] public section


noncomputable section

namespace EulerParentRenewalPrefix

open Finset EulerPacketSourceScaleChoice EulerPacketSourceScaleGuards
  EulerPacketSourceScaleActual EulerScale

theorem relative_step_error {a b e : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (he : 0 ≤ e) (h : |b / a - 1| ≤ e) : |b-a| ≤ 2*e := by
  have hid : (b/a-1)*a=b-a := by field_simp
  calc
    |b-a| = |b/a-1| * a := by rw [← hid,abs_mul,abs_of_pos ha]
    _ ≤ e*a := mul_le_mul_of_nonneg_right h ha.le
    _ ≤ e*2 := mul_le_mul_of_nonneg_left ha2 he
    _ = 2*e := by ring

theorem partial_sum_le {e : ℕ → ℝ} {η : ℝ} (he : SmallSeries e η) (n : ℕ) :
    ∑ i ∈ range n, e i ≤ η :=
  (he.summable.sum_le_tsum (range n) (fun i _ => he.nonneg i)).trans he.total_le

theorem bounds_of_accumulated_error {e : ℕ → ℝ} {η v : ℝ}
    (he : SmallSeries e η) (hη : η ≤ 1 / 4) (n : ℕ)
    (hv : |v - 1| ≤ 2 * ∑ i ∈ range n, e i) : 1/2 ≤ v ∧ v ≤ 2 := by
  have hs := partial_sum_le he n
  have ha := abs_le.mp hv
  constructor <;> linarith only [hs,hη,ha.1,ha.2]

theorem accumulate_step {a e : ℕ → ℝ} (n : ℕ)
    (ha : 1 / 2 ≤ a n) (ha2 : a n ≤ 2) (he : 0 ≤ e n)
    (hprev : |a n - 1| ≤ 2 * ∑ i ∈ range n, e i)
    (hstep : |a (n + 1) / a n - 1| ≤ e n) :
    |a (n+1)-1| ≤ 2*∑ i ∈ range (n+1), e i := by
  have hi := relative_step_error (by linarith only [ha] : 0 < a n) ha2 he hstep
  have ht := abs_add_le (a (n+1)-a n) (a n-1)
  rw [show a (n+1)-a n+(a n-1)=a (n+1)-1 by ring] at ht
  rw [sum_range_succ]
  linarith only [hi,hprev,ht]

/-- No bound on a future coupling is an input. The step estimate can
be established only after the previous finite prefix has been bounded. -/
theorem coupling_prefix {a e : ℕ → ℝ} {η : ℝ} (N : ℕ)
    (he : SmallSeries e η) (hη : η ≤ 1 / 4) (hzero : a 0 = 1)
    (hstep : ∀ n < N, (∀ i ≤ n, 1 / 2 ≤ a i ∧ a i ≤ 2) →
      |a (n + 1) / a n - 1| ≤ e n) :
    ∀ n ≤ N, (1/2 ≤ a n ∧ a n ≤ 2) ∧ |a n-1| ≤ 2*∑ i ∈ range n, e i := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp only [hzero,sub_self,abs_zero,sum_range_zero,mul_zero]; norm_num
    | succ n =>
      have hp := ih n (by omega) (by omega)
      have hprefix : ∀ i ≤ n, 1/2 ≤ a i ∧ a i ≤ 2 := by
        intro i hi
        exact (ih i (by omega) (by omega)).1
      have hs := accumulate_step n hp.1.1 hp.1.2 (he.nonneg n) hp.2
        (hstep n (by omega) hprefix)
      exact ⟨bounds_of_accumulated_error he hη (n+1) hs,hs⟩

/-- The same finite induction propagates the normalized tilt invariant
along with the coupling. Its hypotheses mention only already-built stages. -/
theorem coupling_and_tilt_prefix {a β x e : ℕ → ℝ} {η : ℝ} (N : ℕ)
    (he : SmallSeries e η) (hη : η ≤ 1 / 4) (hzero : a 0 = 1)
    (hβzero : 1 / 2 ≤ β 0 * (x 0) ^ 2 ∧ β 0 * (x 0) ^ 2 ≤ 2)
    (hstep : ∀ n < N,
      (∀ i ≤ n, (1 / 2 ≤ a i ∧ a i ≤ 2) ∧ (1 / 2 ≤ β i * (x i) ^ 2 ∧ β i * (x i) ^ 2 ≤ 2)) →
      |a (n + 1) / a n - 1| ≤ e n ∧
        (1 / 2 ≤ β (n + 1) * (x (n + 1)) ^ 2 ∧ β (n + 1) * (x (n + 1)) ^ 2 ≤ 2)) :
    ∀ n ≤ N, (1/2 ≤ a n ∧ a n ≤ 2) ∧
      (1/2 ≤ β n*(x n)^2 ∧ β n*(x n)^2 ≤ 2) ∧
      |a n-1| ≤ 2*∑ i ∈ range n, e i := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero =>
      refine ⟨?_,hβzero,?_⟩ <;> simp only [hzero,sub_self,abs_zero,sum_range_zero,mul_zero] <;>
          norm_num
    | succ n =>
      have hp := ih n (by omega) (by omega)
      have hprefix : ∀ i ≤ n,
          (1/2 ≤ a i ∧ a i ≤ 2) ∧ (1/2 ≤ β i*(x i)^2 ∧ β i*(x i)^2 ≤ 2) := by
        intro i hi
        have h := ih i (by omega) (by omega)
        exact ⟨h.1,h.2.1⟩
      have ht := hstep n (by omega) hprefix
      have hs := accumulate_step n hp.1.1 hp.1.2 (he.nonneg n) hp.2.2 ht.1
      exact ⟨bounds_of_accumulated_error he hη (n+1) hs,ht.2,hs⟩

theorem stage_congr_at {J D : ℕ} {C c X K : ℝ} {a β b γ : ℕ → ℝ} {n : ℕ}
    (G : StageGuards J D C c X K a β n) (ha : a n = b n) (hβ : β n = γ n) :
    StageGuards J D C c X K b γ n where
  epsilon_pos := by simpa only [ha] using G.epsilon_pos
  epsilon_small := by simpa only [ha] using G.epsilon_small
  sigma_pos := by simpa only [hβ] using G.sigma_pos
  sigma_small := by simpa only [hβ] using G.sigma_small
  reciprocal_pos := G.reciprocal_pos
  reciprocal_small := G.reciprocal_small
  target_from_sigma := by simpa only [hβ] using G.target_from_sigma
  target_le_horizon := by simpa only [ha,hβ] using G.target_le_horizon
  horizon_le_Theta := by simpa only [ha,hβ] using G.horizon_le_Theta
  extra_time := by simpa only [ha,hβ] using G.extra_time
  next_width := G.next_width
  geometry_small := by simpa only [geometryError,ha] using G.geometry_small
  compression := by simpa only [ha,hβ] using G.compression

/-- Extend just the current scalar values to a bounded artificial
sequence, apply the uniform theorem, then transfer its local conclusion.
No hypotheses on any future stage are required. -/
theorem stage_guards_at (J D : ℕ) (hJ : 3 ≤ J) (C c X K δ : ℝ)
    (hC : 4 ≤ C) (hX : 8 ≤ X) (hK : 1 ≤ K) (hδ : δ ≤ 1 / 2)
    (hδK : 1000000 * K * δ ≤ 1) (hb : ActualBounds J D C c X δ)
    (a β : ℕ → ℝ) (n : ℕ)
    (ha : 1 / 2 ≤ a n) (ha2 : a n ≤ 2)
    (hβ : 1 / 2 ≤ β n * (scaleSequence J X n) ^ 2)
    (hβ2 : β n * (scaleSequence J X n) ^ 2 ≤ 2) :
    StageGuards J D C c X K a β n := by
  let b : ℕ → ℝ := fun _ => a n
  let γ : ℕ → ℝ := fun i => β n*(scaleSequence J X n)^2/(scaleSequence J X i)^2
  have hx := quadratic_growth_pos J (by omega) (scaleSequence J X)
    (show 0 < X by linarith only [hX]) (scaleSequence_succ J X)
  have hγ (i : ℕ) : γ i*(scaleSequence J X i)^2=β n*(scaleSequence J X n)^2 := by
    dsimp only [γ]
    exact div_mul_cancel₀ _ (pow_ne_zero _ (hx i).ne')
  have H := stage_guards J D hJ C c X K δ hC hX hK hδ hδK hb b γ
    (fun _ => ha) (fun _ => ha2)
    (fun i => by rw [hγ i]; exact hβ) (fun i => by rw [hγ i]; exact hβ2) n
  apply stage_congr_at (b := a) (γ := β) H rfl
  dsimp only [γ]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ (hx n).ne')

end EulerParentRenewalPrefix
