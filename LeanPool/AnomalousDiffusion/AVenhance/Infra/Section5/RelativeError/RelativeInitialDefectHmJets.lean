/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectHmUniform
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEndpointJets

/-! Relative Hm initial-layer control from gradient-only iterate spatial jets.
The endpoint recursion checks the mixed budget through terminal Jcut. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section4
namespace AVenhance.Infra.Section5.RelativeError

/-- The relative Hm bound is produced from upstream spatial jets, with abstract
amplitude S >= 0. No Hm-source bound is assumed. -/
theorem relative_initial_Hm_uniform_of_jets (β C₀ Cg Cl : ℝ) (hCg : 0 ≤ Cg) (hCl : 1 ≤ Cl) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      ∀ S : ℝ, 0 ≤ S →
        -- positive S-normalised spatial jets of the gradient of every partial iterate
        (∀ i, i ≤ Nstar β → ∀ (p : Fin 2) (α : List (Fin 2)), α.length ≤ Nstar β →
          eLpNorm (Infra.Section4.amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
              (α.map some) (Infra.Section4.amnrTGradient (T i) p)) 2
            ((volume.restrict (Set.uIoc 0 1)).prod (volume.restrict unitCube)) ≤
          ENNReal.ofReal (Cg * S / Real.sqrt (I.kappaSeq κ M (m - 1)) *
            (Cl * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ α.length)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) (tauPP β I.Λ m / 2),
        Real.sqrt (l2NormSq (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t)) ≤
          CH * epsilon β I.Λ (m - 1) ^ delta β * S := by
  obtain ⟨CA, hCA, ΛA, hA⟩ := relative_initial_Amnr_gradient_of_jets β C₀ Cg Cl hCg hCl
  obtain ⟨CH, hCH, ΛH, hH⟩ := relative_initial_Hm_uniform_of_gradient_profiles β C₀ CA hCA
  refine ⟨CH, hCH, max ΛA ΛH, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hθprev hT S hS hjets
  exact hH I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκp M hM hperm m hm hmM
    θ₀ θprev T hθprev hT S hS
    (hA I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκp M hM hperm m hm hmM
      θ₀ θprev T hθprev hT S hS hjets)

end AVenhance.Infra.Section5.RelativeError
