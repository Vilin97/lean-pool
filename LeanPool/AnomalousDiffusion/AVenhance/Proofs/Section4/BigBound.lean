/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A7DatumClosure

/-! Proof of the big-bound estimate (`AVenhance.bigbound`).

The statement below is identical to the one (copied from
`AVenhance/Section4/BigBound.lean`); the statement file is not imported. The proof is
`Infra.Section5.Contracts.bigbound_closed`: the big-bound estimate from the Section 5 residual
    identity (repaired
decomposition, ten slot names) and every big-bound input produced at the datum amplitude, including
`Normie3CenteredSourceContract` (normie3⁺, exact zero cell mean). -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Proofs

/-- Big-bound estimate proof. Its statement is identical to `AVenhance.bigbound`. -/
theorem bigbound (β : ℝ) (C₀ : ℝ) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        ENNReal.ofReal (I.kappaSeq κ M m ^ (-(1 / 2 : ℝ))) *
            (∫⁻ t in Set.Ioo (0 : ℝ) 1,
              hMinusOneNorm (fun x => advDiffOp (streamVel (Φ m)) (I.kappaSeq κ M m)
                (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β))) t x) ^ 2) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)) :=
  Infra.Section5.Contracts.bigbound_closed β C₀

end AVenhance.Proofs

end
