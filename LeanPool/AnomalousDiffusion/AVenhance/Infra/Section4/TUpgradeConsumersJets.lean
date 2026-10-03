/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersFinal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth

/-! # TUpgrade Consumers Jets

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem TUpgradeConsumersJets.fin_cast_of_heq {a b : ℕ} {j : Fin a} {k : Fin b}
    (hab : a = b) (h : HEq j k) : Fin.cast hab j = k := by
  subst b
  exact eq_of_heq h

/-- Convert the positive ordered-word part of the upgrade to the exact
Frechet-jet carrier used by RelativeLeaves. -/
theorem iterate_positive_temperature_jets_of_word_bound
    {u : ℝ → Vec 2 → ℝ} {κ S P D ρ A : ℝ}
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ (⊤ : ℕ∞) (u t))
    (hS : 0 ≤ S) (hP : 0 ≤ P) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hPA : P ≤ A) (hDA : D ≤ A)
    (hb : ∀ v w : List (Fin 2), v.length = w.length → 1 ≤ v.length →
      ∀ t, 0 ≤ t → t ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (u t))) + Real.sqrt κ *
        Real.sqrt (spaceTimeGradNormSq (fun s => spaceGrad (iterateSpatialWord w (u s)))) ≤
      S * P * (v.length.factorial : ℝ) * (D / ρ) ^ v.length) :
    Infra.Section5.RelativeError.PositiveTemperatureJets A ρ S u := by
  have hA : 0 ≤ A := hP.trans hPA
  intro n i hn t ht
  let w := List.ofFn i
  have hw : w.length = n := List.length_ofFn
  have heq : iterateSpatialWord w (u t) = fun x => iteratedFDeriv ℝ n (u t) x
      (fun j => basisVec (i j)) := by
    have hidx : (⟨w.length, fun j => basisVec (w.get j)⟩ : Σ k, Fin k → Vec 2) =
        ⟨n, fun j => basisVec (i j)⟩ := by
      apply Sigma.ext hw
      apply Function.hfunext
      · exact congrArg Fin hw
      · intro j k hj
        apply heq_of_eq
        dsimp only [w]
        simp only [List.get_ofFn]
        change basisVec (i (Fin.cast hw j)) = basisVec (i k)
        rw [TUpgradeConsumersJets.fin_cast_of_heq hw hj]
    have hjets := congrArg (fun p : Σ k, Fin k → Vec 2 =>
      fun x => iteratedFDeriv ℝ p.1 (u t) x p.2) hidx
    exact (iterateSpatialWord_eq_iteratedFDeriv (hu t ht) w).trans hjets
  have hbound := hb w w rfl (by omega) t ht.1 ht.2
  have hdrop : Real.sqrt (l2NormSq (iterateSpatialWord w (u t))) ≤
      S * P * (n.factorial : ℝ) * (D / ρ) ^ n := by
    rw [hw] at hbound
    exact (le_add_of_nonneg_right (by positivity)).trans hbound
  rw [heq] at hdrop
  have hp := pow_le_pow_left₀ (div_nonneg hD hρ.le)
    (div_le_div_of_nonneg_right hDA hρ.le) n
  calc
    _ ≤ S * P * (n.factorial : ℝ) * (D / ρ) ^ n := hdrop
    _ ≤ A * S * (n.factorial : ℝ) * (A / ρ) ^ n := by
      have hcoef : S * P * (n.factorial : ℝ) ≤ A * S * (n.factorial : ℝ) := by
        simpa only [mul_comm S P, mul_comm S A] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPA hS)
            (Nat.cast_nonneg n.factorial)
      exact mul_le_mul hcoef hp (by positivity) (by positivity)

end AVenhance.Infra.Section4
