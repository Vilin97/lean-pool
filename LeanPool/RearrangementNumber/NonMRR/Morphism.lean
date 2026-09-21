/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Catalogue
import LeanPool.RearrangementNumber.NonMRR.RiemannBaire

/-!
# The morphism into the slaloms

This is the explicit Galois–Tukey morphism of Lemma 4.1 in the manuscript.
Its challenge map sends `e` to `e` together with the conditional series selected
from each catalogue indexed by `g`. Its response map records the exceptional
blocks of a growth function and a permutation.
-/

open Filter

namespace NonMRR

/-- The rearrangement relation on conditionally convergent real series.
The rearrangement theorem supplies a response to every challenge. -/
def rearrangementRelation : Relation where
  Challenge := ConditionalSeries
  Response := Equiv.Perm ℕ
  relates := Rearranges
  total := exists_rearranges

/-- The relation norm agrees with the cardinal-minimum definition of `rr`. -/
theorem rearrangementRelation_norm_eq_rr : rearrangementRelation.norm = rr := rfl

/-- The explicit morphism from the sequential bounding/rearrangement relation
to slaloms of width `8 * (2^(n+1))^4`. -/
noncomputable def blockMorphism :
    Relation.Morphism (boundingRelation.sequential rearrangementRelation)
      (slalomRelation blockCapacity blockCapacity_pos) where
  challenge e := (e, fun g => walshCatalogue.challengeSeries e g)
  response := walshCatalogue.response
  map_rel e p h :=
    walshCatalogue.catches_of_rearranges blockTolerance_summable blockTolerance_nonneg
      e p.1 p.2 h.1 h.2

/-- The concrete width bound of the block construction tends to infinity. -/
theorem blockCapacity_tendsto_atTop : Tendsto blockCapacity atTop atTop := by
  have hge (n : ℕ) : n ≤ blockCapacity n := by
    have hden : n ≤ blockDenominator n :=
      (Nat.le_succ n).trans (Nat.lt_two_pow_self (n := n + 1)).le
    have hpow : blockDenominator n ≤ blockDenominator n ^ 4 :=
      le_self_pow₀ (blockDenominator_pos n) (by decide)
    exact (hden.trans hpow).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 8))
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hn.trans (hge n)

/-- Lemma 4.1: a positive width tending to infinity admits a morphism from
the sequential bounding/rearrangement relation into its slalom relation. -/
theorem exists_divergent_slalom_morphism :
    ∃ r : ℕ → ℕ, ∃ hr : ∀ n, 0 < r n,
      Tendsto r atTop atTop ∧
        Nonempty (Relation.Morphism (boundingRelation.sequential rearrangementRelation)
          (slalomRelation r hr)) :=
  ⟨blockCapacity, blockCapacity_pos, blockCapacity_tendsto_atTop, ⟨blockMorphism⟩⟩

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
