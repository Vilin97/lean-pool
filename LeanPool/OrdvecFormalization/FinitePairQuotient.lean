/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteProductQuotient

/-!
# Pair quotients

Retrieval decisions are naturally pairwise: query observation times document
observation.  This file packages the product quotient and the corresponding
same-compressed-pair invariance/falsifier theorems.
-/

namespace OrdvecFormalization

/-- Product quotient for query/document pairs. -/
abbrev pairQuotient {Ωq Ωd Zq Zd : Type}
    (Cq : Ωq → Zq) (Cd : Ωd → Zd) : Ωq × Ωd → Zq × Zd :=
  productMap Cq Cd

@[simp]
theorem pairQuotient_apply {Ωq Ωd Zq Zd : Type}
    (Cq : Ωq → Zq) (Cd : Ωd → Zd) (pair : Ωq × Ωd) :
    pairQuotient Cq Cd pair = (Cq pair.1, Cd pair.2) := rfl

theorem pairQuotient_eq_iff {Ωq Ωd Zq Zd : Type}
    (Cq : Ωq → Zq) (Cd : Ωd → Zd)
    (pair₁ pair₂ : Ωq × Ωd) :
    pairQuotient Cq Cd pair₁ = pairQuotient Cq Cd pair₂ ↔
      Cq pair₁.1 = Cq pair₂.1 ∧ Cd pair₁.2 = Cd pair₂.2 :=
  productMap_eq_iff Cq Cd pair₁ pair₂

/--
A pairwise target that factors through the product quotient is invariant under
same query bucket and same document bucket.
-/
theorem pairRuleFactorsThrough_same_on_quotient_fibers {Ωq Ωd Zq Zd A : Type}
    (Cq : Ωq → Zq) (Cd : Ωd → Zd) (target : Ωq × Ωd → A)
    (hfac : RuleFactorsThrough (pairQuotient Cq Cd) target)
    {pair₁ pair₂ : Ωq × Ωd}
    (hq : Cq pair₁.1 = Cq pair₂.1)
    (hd : Cd pair₁.2 = Cd pair₂.2) :
    target pair₁ = target pair₂ := by
  rcases pair₁ with ⟨q₁, d₁⟩
  rcases pair₂ with ⟨q₂, d₂⟩
  exact ruleFactorsThrough_product_fiberInvariant Cq Cd target hfac hq hd

/--
If two sampled query/document pairs have the same product quotient but
different labels, no pairwise quotient-factorized target fits the sample.
-/
theorem no_pair_compatible_target_of_sample_collision {Ωq Ωd Zq Zd A : Type}
    (Cq : Ωq → Zq) (Cd : Ωd → Zd)
    (label : Ωq × Ωd → A) (sample : Finset (Ωq × Ωd))
    {pair₁ pair₂ : Ωq × Ωd}
    (hpair₁ : pair₁ ∈ sample) (hpair₂ : pair₂ ∈ sample)
    (hq : Cq pair₁.1 = Cq pair₂.1)
    (hd : Cd pair₁.2 = Cd pair₂.2)
    (hlabel : label pair₁ ≠ label pair₂) :
    ¬ ∃ target : Ωq × Ωd → A,
      QuotientCompatible (pairQuotient Cq Cd) target ∧
        FullTargetFitsSample label target sample :=
  no_compatible_target_of_sample_collision (pairQuotient Cq Cd) label sample
    hpair₁ hpair₂ (Prod.ext hq hd) hlabel

end OrdvecFormalization
