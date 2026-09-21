/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalParameters
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartPreservation

/-!
# The minimal decomposition lemma

A bounded flag decomposition can be expressed in its support-generated
lattice coordinates for every sufficiently large prime. The new decomposition
has the same nodes and local weights, is minimal, and preserves gaps,
reducedness, element completeness, and realized faces under chart pullback.
The coordinate growth function depends only on dimension, and the prime
threshold depends only on dimension and the original uniform box bound.
-/

namespace EGZ

open FlagDecomposition

/-- Uniform form of the paper's minimal decomposition lemma. The output is
the actual recharted decomposition, so its node poset is definitionally the
original node poset. Local and cumulative lifted weights are identified by
the chart maps; retained mass and every node gap are unchanged. -/
theorem minimalization_lemma (d : ℕ) :
    ∃ A : ℕ → ℕ, Monotone A ∧ (∀ K, K ≤ A K) ∧
      ∀ BK : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
            (K : Φ.flag.Node → ℕ), Φ.IsKBounded K → (∀ x, K x ≤ BK) →
            ∃ (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))
              (hp : Odd p)
              (hinj : ∀ x, Function.Injective ((Rechart.chart Φ C x).modp p))
              (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q),
              let Ψ := Rechart.decomposition Φ C hp hinj hcenter
              Ψ.IsMinimal ∧
              Ψ.IsKBounded (fun x ↦ A (K x)) ∧
              (∀ x, Ψ.localWeight x = Φ.localWeight x) ∧
              (∀ x, Ψ.cumulativeWeight x = Φ.cumulativeWeight x) ∧
              Ψ.retainedWeight = Φ.retainedWeight ∧
              Ψ.retainedMass = Φ.retainedMass ∧
              (∀ x, Ψ.gap x = Φ.gap x) ∧
              (∀ x q, Ψ.hat x q = Φ.hat x ((C x).map q)) ∧
              (∀ x q, Ψ.localLift x q = Φ.localLift x ((C x).map q)) ∧
              (Ψ.IsReduced ↔ Φ.IsReduced) ∧
              (∀ x t δ, Φ.IsCompleteElement x t δ → Ψ.IsCompleteElement x t δ) ∧
              (∀ x (Γ : (Φ.flag.polytope x).Face), Φ.IsRealizedFace x Γ →
                Ψ.IsRealizedFace x ((Rechart.subdivisionMap Φ C hp hinj hcenter).face
                  x Γ (Rechart.face_preimage_nonempty Φ C x Γ))) := by
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_rechart_parameters d
  refine ⟨A, hAmono, hAge, ?_⟩
  intro BK
  obtain ⟨p₀, hp₀, hparams⟩ := hA BK
  refine ⟨p₀, hp₀, ?_⟩
  intro p _ _ hpp f Φ K hΦ hBK
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨C, hinj, hcenter, hbox, _hpoly⟩ := hparams p hpp f Φ K hΦ hBK
  refine ⟨C, hp, hinj, hcenter,
    Rechart.decomposition_isMinimal Φ C hp hinj hcenter,
    Rechart.decomposition_isKBounded Φ C hp hinj hcenter hΦ hbox,
    fun _ ↦ rfl, fun _ ↦ rfl, rfl, rfl,
    Rechart.decomposition_gap Φ C hp hinj hcenter,
    Rechart.decomposition_hat Φ C hp hinj hcenter,
    Rechart.decomposition_localLift Φ C hp hinj hcenter,
    Rechart.decomposition_isReduced_iff Φ C hp hinj hcenter,
    Rechart.decomposition_isCompleteElement Φ C hp hinj hcenter,
    Rechart.decomposition_isRealizedFace Φ C hp hinj hcenter⟩

end EGZ
