/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.Pieces
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.HolderTimeL2Le
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsHolderTimeL2

/-! # Hölder-seminorm bookkeeping for the analytic case of `r.LeBron.2`

Monotonicity in the constant and in the exponent, extraction of the seminorm from
`HolderTimeL2Le`, the `L²` triangle inequality for `L²` slices, and the telescoping chain lemma. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem IsHolderTimeL2.mono_const {μ H H' : ℝ} {θ : ℝ → Vec 2 → ℝ}
    (h : IsHolderTimeL2 μ H θ) (hH : H ≤ H') : IsHolderTimeL2 μ H' θ := fun s hs t ht =>
  (h s hs t ht).trans (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (abs_nonneg _) _))

theorem abs_sub_le_one_of_mem {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |t - s| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

theorem IsHolderTimeL2.mono_exp {μ μ' H : ℝ} {θ : ℝ → Vec 2 → ℝ} (hμ' : 0 < μ') (hμ : μ' ≤ μ)
    (hH : 0 ≤ H) (h : IsHolderTimeL2 μ H θ) : IsHolderTimeL2 μ' H θ := by
  intro s hs t ht
  refine (h s hs t ht).trans (mul_le_mul_of_nonneg_left ?_ hH)
  exact Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) (abs_sub_le_one_of_mem hs ht) hμ'.le hμ

theorem holderTimeL2Le_isHolder {μ H : ℝ} {θ : ℝ → Vec 2 → ℝ} (h : HolderTimeL2Le μ H θ) :
    IsHolderTimeL2 μ H θ := by
  obtain ⟨-, A, B, hAB, hA, hB⟩ := h
  have hA0 : 0 ≤ A := (Real.sqrt_nonneg _).trans (hA 0 ⟨le_rfl, zero_le_one⟩)
  exact IsHolderTimeL2.mono_const hB (by linarith)

/-- Triangle inequality for a sum of two `L²` functions. -/
theorem sqrt_l2NormSq_sub_le_memL2 {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    (hg : MemL2On unitCube g) :
    Real.sqrt (l2NormSq (fun x => f x - g x)) ≤ Real.sqrt (l2NormSq f) + Real.sqrt (l2NormSq g) :=
        by
  have h := Infra.Section5.sqrt_l2NormSq_add_le (f := f) (g := fun x => -g x) hf hg.neg
  have e : l2NormSq (fun x => -g x) = l2NormSq g := by simp [l2NormSq]
  rw [e] at h
  simpa [sub_eq_add_neg] using h

/-- Telescoping chain: a base Hölder bound at `n₀` plus Hölder bounds for the increments. -/
theorem chain_holder {f : ℕ → ℝ → Vec 2 → ℝ} {μ A : ℝ} {c : ℕ → ℝ} {n₀ : ℕ}
    (hbase : IsHolderTimeL2 μ A (f n₀)) :
    ∀ M : ℕ, n₀ ≤ M →
    (∀ n, n₀ ≤ n → n ≤ M → ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (f n t)) →
    (∀ n, n₀ < n → n ≤ M →
      IsHolderTimeL2 μ (c n) (fun t x => f n t x - f (n - 1) t x)) →
    IsHolderTimeL2 μ (A + ∑ n ∈ Finset.Ioc n₀ M, c n) (f M) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro _ _
    simpa using hbase
  | succ M hM ih =>
    intro hcont hstep
    have ih' := ih (fun n h1 h2 => hcont n h1 (by omega)) (fun n h1 h2 => hstep n h1 (by omega))
    have hD := hstep (M + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hD
    rw [Finset.sum_Ioc_succ_top hM]
    intro s hs t ht
    have e : (fun x => f (M + 1) t x - f (M + 1) s x) =
        fun x => (f M t x - f M s x) +
          ((f (M + 1) t x - f M t x) - (f (M + 1) s x - f M s x)) := by
      funext x; ring
    rw [e]
    have hc1 := hcont M hM (by omega)
    have hc2 := hcont (M + 1) (by omega) le_rfl
    have h := Infra.Section5.Integration.sqrt_l2NormSq_add_le_of_continuous
      (f := fun x => f M t x - f M s x)
      (g := fun x => (f (M + 1) t x - f M t x) - (f (M + 1) s x - f M s x))
      ((hc1 t ht).sub (hc1 s hs)) (((hc2 t ht).sub (hc1 t ht)).sub ((hc2 s hs).sub (hc1 s hs)))
    have h1 := ih' s hs t ht
    have h2 := hD s hs t ht
    calc _ ≤ _ := h
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring

/-- Splitting `θ = θ_M + (θ − θ_M)` in the Hölder seminorm. -/
theorem holder_split {μ H₁ H₂ : ℝ} {θ θM : ℝ → Vec 2 → ℝ}
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ t))
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θM t))
    (h1 : IsHolderTimeL2 μ H₁ θM) (h2 : IsHolderTimeL2 μ H₂ (fun t x => θ t x - θM t x)) :
    IsHolderTimeL2 μ (H₁ + H₂) θ := by
  intro s hs t ht
  have e : (fun x => θ t x - θ s x) = fun x => (θM t x - θM s x) +
      ((θ t x - θM t x) - (θ s x - θM s x)) := by
    funext x; ring
  rw [e]
  have hf : MemL2On unitCube (fun x => θM t x - θM s x) := (hM t ht).sub (hM s hs)
  have hg : MemL2On unitCube (fun x => (θ t x - θM t x) - (θ s x - θM s x)) :=
    ((hθ t ht).sub (hM t ht)).sub ((hθ s hs).sub (hM s hs))
  have h := Infra.Section5.sqrt_l2NormSq_add_le hf hg
  have a1 := h1 s hs t ht
  have a2 := h2 s hs t ht
  calc _ ≤ _ := h
    _ ≤ _ := add_le_add a1 a2
    _ = _ := by ring

end AVenhance.Infra.FullTheorem
