/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.Pieces
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.KappaBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IndyStepDown
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.ClassicalWellposed
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesExist
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TLemmasNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds

/-! # One level of the chain, telescoping, and the `L²` triangle for norms

* `abs_sqrt_l2_sub_le`: `|‖f‖ − ‖g‖| ≤ ‖f − g‖` for `L²(unitCube)` functions;
* `step_sup`: the sup part (i) of the step-down estimate for one classical level, with the iterate
    witness
  from `RelativeError.exists_TIterates`;
* `telescope_l2`: the sum of the level increments bounds `‖θ_k − θ_{n₀}‖`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSel

open AVenhance

theorem l2NormSq_sub_comm (f g : Vec 2 → ℝ) :
    l2NormSq (fun x => g x - f x) = l2NormSq (fun x => f x - g x) := by
  unfold l2NormSq
  congr 1
  funext x
  ring

theorem abs_sqrt_l2_sub_le {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f) (hg : MemL2On unitCube g) :
    |Real.sqrt (l2NormSq f) - Real.sqrt (l2NormSq g)| ≤
      Real.sqrt (l2NormSq (fun x => f x - g x)) := by
  have hfg : MemL2On unitCube (fun x => f x - g x) := hf.sub hg
  have hgf : MemL2On unitCube (fun x => g x - f x) := hg.sub hf
  have h1 := Infra.Section4.sqrt_l2NormSq_add_le (f := fun x => f x - g x) (g := g) hfg hg
  have h2 := Infra.Section4.sqrt_l2NormSq_add_le (f := fun x => g x - f x) (g := f) hgf hf
  have e1 : (fun x => (f x - g x) + g x) = f := by funext x; ring
  have e2 : (fun x => (g x - f x) + f x) = g := by funext x; ring
  rw [e1] at h1
  rw [e2, l2NormSq_sub_comm] at h2
  rw [abs_le]
  constructor <;> linarith

/-- The `L²` norm of a difference along a telescoping chain of continuous slices. -/
theorem telescope_l2 {θs : ℕ → ℝ → Vec 2 → ℝ} {n₀ M : ℕ} {t : ℝ} {a : ℕ → ℝ}
    (hc : ∀ j, n₀ ≤ j → j ≤ M → Continuous (θs j t))
    (hstep : ∀ l, n₀ < l → l ≤ M →
      Real.sqrt (l2NormSq (fun x => θs l t x - θs (l - 1) t x)) ≤ a l) :
    ∀ k, n₀ ≤ k → k ≤ M →
      Real.sqrt (l2NormSq (fun x => θs k t x - θs n₀ t x)) ≤ ∑ l ∈ Finset.Ioc n₀ k, a l := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; simp [l2NormSq]
  | succ k hk ih =>
    intro hkM
    rw [Finset.sum_Ioc_succ_top hk]
    have h1 := ih (by omega)
    have h2 := hstep (k + 1) (by omega) hkM
    simp only [Nat.add_sub_cancel] at h2
    have hm1 : MemL2On unitCube (fun x => θs (k + 1) t x - θs k t x) :=
      Infra.Section5.Integration.memL2On_unitCube_of_continuous
        ((hc (k + 1) (by omega) hkM).sub (hc k hk (by omega)))
    have hm2 : MemL2On unitCube (fun x => θs k t x - θs n₀ t x) :=
      Infra.Section5.Integration.memL2On_unitCube_of_continuous
        ((hc k hk (by omega)).sub (hc n₀ le_rfl (by omega)))
    have h3 := Infra.Section4.sqrt_l2NormSq_add_le hm1 hm2
    have e : (fun x => (θs (k + 1) t x - θs k t x) + (θs k t x - θs n₀ t x)) =
        fun x => θs (k + 1) t x - θs n₀ t x := by funext x; ring
    rw [e] at h3
    linarith

/-- Sup part (i) of the step-down estimate for one classical level, uniform in the permitted data.
-/
theorem step_sup (β C₀ : ℝ) :
    ∃ C₈ : ℝ, 0 ≤ C₈ ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      C₈ ≤ (I.Λ : ℝ) → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R → ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ →
        MeanZeroOn unitCube θ₀ → IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      0 < I.kappaSeq κ M m → 0 < I.kappaSeq κ M (m - 1) →
      ∀ θm θprev : ℝ → Vec 2 → ℝ,
        IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) θ₀ θm →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤
          C₈ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by
  obtain ⟨C₈, hA8⟩ := AVenhance.indystepdown β C₀
  refine ⟨max C₈ 0, le_max_right _ _, ?_⟩
  intro I hz hx hh hCΛ Φ hΦ κ hκ M hM hκM R hR θ₀ hθ₀ hper hmean han m hmm hmM hκmpos hκppos
    θm θprev hθm hθprev t ht
  have hC₈Λ : C₈ ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hCΛ
  have hm2 : 2 ≤ m := by
    have := (mTheta0_isLeast I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.1
    omega
  have hsolv : ∀ j : ℕ, Infra.Section5.RelativeError.ClassicalSolvable (streamVel (Φ j)) := by
    intro j ν hν g hg hgp F hF hFp
    exact (AVenhance.classical_wellposed (Φ j) (streamSeq_isAdmissible hΦ j)
      ν hν F hF hFp g hg hgp).imp fun θ hθ => hθ.1
  obtain ⟨T, hT⟩ := Infra.Section5.RelativeError.exists_TIterates I hΦ (m := m) (by omega) hκmpos
      hκppos
    (hsolv (m - 1)) hθ₀ hper hθprev
  have hsup8 := (hA8 I hz hx hh hC₈Λ Φ hΦ κ hκ M hM hκM R hR θ₀ hθ₀ hper hmean han m hmm hmM
    θm θprev T hθm hθprev hT).1 t ht
  have h2 : 0 ≤ Real.sqrt (I.kappaSeq κ M m) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x -
        spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h3 : Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤
      C₈ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by linarith
  have hEd : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hs0 : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  calc _ ≤ C₈ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := h3
    _ ≤ max C₈ 0 * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by
        gcongr; exact le_max_left _ _

end AVenhance.Infra.FullTheorem.NoSel
