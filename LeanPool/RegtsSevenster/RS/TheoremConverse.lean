/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseIdentity

/-!
# The Regts–Sevenster theorem, both directions

The super-Gram identity is a theorem
(`EdgeSubset.superGramIdentity`), so the converse holds with no
hypothesis at all: every mixed partition function is an
edge-rank-bounded parameter.  With it the characterization and the
quantitative round trip rest on Deligne alone.
-/

namespace RS



/-- The converse rank bound with the exact total dimension as its
base, including the zero-dimensional model. -/
theorem mixedPartition_edgeRankBounded {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) :
    EdgeRankBounded (fun W => mixedPartition h W) (k + 2 * ℓ) :=
  edgeRankBounded_of_superGram (fragmentTensor h)
    (EdgeSubset.superGramIdentity h)

/-- **THE CONVERSE** (Regts–Sevenster, arXiv:1807.04494, Theorem 6):
every mixed partition function is an edge-rank-bounded parameter,
with base `max 1 (k + 2ℓ)`. -/
theorem regts_sevenster_converse : RegtsSevensterConverseStatement :=
  EdgeSubset.regtsSevensterConverse

/-- **The rank bound from a bounded mixed partition function.** -/
theorem edgeRankBounded_of_mixedBounded
    {f : ClosedFragment → ℂ} {B : ℕ}
    (hf : IsMixedPartitionFunctionBounded f B) :
    EdgeRankBounded f (max 1 (2 * B)) := by
  obtain ⟨k, ℓ, h, hk, hℓ, hval⟩ := hf
  obtain ⟨g, hg⟩ := regts_sevenster_converse k ℓ h
  have hfg : f = g.val := by
    funext W
    rw [hval W, hg W]
  rw [hfg]
  exact g.rank_bounded.mono (by omega)

/-- **THE CHARACTERIZATION**, conditional on Deligne alone: a
fragment parameter has bounded edge rank exactly when it is a mixed
partition function. -/
theorem regts_sevenster_iff
    (hDeligne : DeligneTheoremStatement.{1, 1})
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f := by
  constructor
  · rintro ⟨R, hR⟩
    exact regts_sevenster_deligne_only hDeligne R
      ⟨f, hempty, hiso, hR⟩
  · rintro ⟨k, ℓ, h, hval⟩
    obtain ⟨g, hg⟩ := regts_sevenster_converse k ℓ h
    refine ⟨max 1 (k + 2 * ℓ), ?_⟩
    have hf : f = fun W => mixedPartition h W := funext hval
    have hgv : g.val = fun W => mixedPartition h W := funext hg
    rw [hf, ← hgv]
    exact g.rank_bounded

/-- **THE QUANTITATIVE ROUND TRIP**, conditional on Deligne alone:
edge rank `R` gives dimension `⌊2eR⌋`, and dimension `B` gives edge
rank base `max 1 (2B)`. -/
theorem regts_sevenster_quant_roundtrip
    (hDeligne : DeligneTheoremStatement.{1, 1})
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∀ R, EdgeRankBounded f R →
      IsMixedPartitionFunctionBounded f
        ⌊2 * Real.exp 1 * (R : ℝ)⌋₊) ∧
    (∀ B, IsMixedPartitionFunctionBounded f B →
      EdgeRankBounded f (max 1 (2 * B))) := by
  constructor
  · intro R hR
    exact regts_sevenster_quant_deligne_only hDeligne R
      ⟨f, hempty, hiso, hR⟩
  · intro B hf
    exact edgeRankBounded_of_mixedBounded hf

end RS
