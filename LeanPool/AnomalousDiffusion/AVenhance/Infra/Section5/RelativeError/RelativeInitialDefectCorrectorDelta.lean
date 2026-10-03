/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectTrace
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIInitial

/-! Relative initial corrector at the epsilon-delta scale on the full
Ingredients beta range, using the exact gradient-only initial trace. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory AVenhance
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
open AVenhance.Infra.Section5.LeftToShow
namespace AVenhance.Infra.Section5.RelativeError

/-- The initial corrector has the required relative epsilon-delta scale on
all physical Ingredients, without an extra lower restriction on beta. -/
theorem relative_initial_corrector_delta_uniform (β C₀ Ctrace : ℝ)
    :
    ∃ Ccorr : ℝ, 0 ≤ Ccorr ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsStreamSeq I Φ)
        (g : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ (u : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
      I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) g u T →
      ∀ S : ℝ, 0 ≤ S →
      (∀ i : Fin 2, Real.sqrt (l2NormSq (fun x => spaceGrad g x i)) ≤
        Ctrace * ((1 : ℕ).factorial : ℝ) *
          (Ctrace / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ (1 : ℕ) * S) →
      Real.sqrt (l2NormSq (fun x => ∑' k : ℤ, I.xiMK m k 0 *
        vecDot (I.chiTilde hΦ m (I.kappaSeq κ M m) k 0 x)
          (spaceGrad (fun y => T (Nstar β) 0 (I.xFlow hΦ m (lIdx β I.Λ m k) 0 y))
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) 0 x)))) ≤
        Ccorr * epsilon β I.Λ (m - 1) ^ delta β * S := by
  obtain ⟨c, C, hc, hcC, hrec⟩ := l_recurse β C₀
  let K := max (max 1 (min c (1 / 2))⁻¹) (1 + Infra.Ingredients.supergeoConstant β)
  refine ⟨48 * Ctrace ^ 2 * K ^ 2, by positivity, ?_⟩
  intro I hz hx hh κ hκp M hM hperm m hm hmM Φ hΦ g hg u T hT S hS htrace
  let e := epsilon β I.Λ (m - 1)
  let r := e ^ (1 + gamma β / 2)
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hr : 0 < r := Real.rpow_pos_of_pos he _
  have hκ : 0 < κ := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (Real.rpow_pos_of_pos
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _)).trans_le hperm.1
  obtain ⟨hκm, hχ⟩ := chiSup_analytic_scale_of_A5 I hm hmM hκ hperm hM hz hx hh hκp
    hc hcC (hrec I hz hx hh κ hκp M hM hperm) hr le_rfl
  have hgrad := relative_initial_gradient_of_trace hg hr hS htrace
  have hT0 : T (Nstar β) 0 = g := funext (tIterates_classicalSol hT).2.2.1
  have hcorrector := relative_initial_corrector_explicit I hΦ (m := m) (by omega) hκm hg
    (T (Nstar β)) hT0
  have hchi0 := chiSup_nonneg I hκm m
  change _ ≤ (24 * chiSup I (I.kappaSeq κ M m) m) * Real.sqrt (gradNormSq (spaceGrad g))
    at hcorrector
  have hinv : r⁻¹ = e ^ (-(1 + gamma β / 2)) := by
    dsimp [r]
    rw [Real.rpow_neg he.le]
  calc
    _ ≤ (24 * chiSup I (I.kappaSeq κ M m) m) * Real.sqrt (gradNormSq (spaceGrad g)) := hcorrector
    _ ≤ (24 * chiSup I (I.kappaSeq κ M m) m) * ((2 * Ctrace ^ 2) * S / r) :=
      mul_le_mul_of_nonneg_left hgrad (by positivity)
    _ = (48 * Ctrace ^ 2 * S) * (chiSup I (I.kappaSeq κ M m) m * e ^ (-(1 + gamma β / 2))) := by
      rw [div_eq_mul_inv, hinv]
      ring
    _ ≤ (48 * Ctrace ^ 2 * S) * (K ^ 2 * e ^ delta β) :=
      mul_le_mul_of_nonneg_left hχ (by positivity)
    _ = _ := by dsimp [e]; ring

end AVenhance.Infra.Section5.RelativeError
