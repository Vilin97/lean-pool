/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram

VENDORED into AINTLIB (2026-07-04) from WilliamCoram/PhD (unmerged tail of
PhD/PR'd/MvGaussNorm.lean + PhD/ToPR/MvGaussNorm.lean), building on the merged
`Mathlib.RingTheory.MvPowerSeries.GaussNorm`.

TRIMMED (2026-07-18, v4.33 bump): the following vendored declarations have been
MERGED INTO MATHLIB under the same names and are now provided by
`Mathlib.RingTheory.MvPowerSeries.GaussNorm`:
`Finset.Nonempty.map_sum_le_sup'_map`, `gaussNorm_mul_le`, `AchievesGaussNorm`,
`ultrametric_strict`, `antidiagonal_dominant`, `gaussNorm_le_mul`, `gaussNorm_neg`,
`gaussNorm_mul_eq_mul`. Only the not-yet-upstreamed helpers remain here.
-/
import Mathlib.RingTheory.MvPowerSeries.GaussNorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.WithAbs
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramMvRestricted

/-! # Gauss norm extras (vendored remainder — see the trim note above) -/

namespace MvPowerSeries

variable {R σ : Type*} (v : R → ℝ) (c : σ → ℝ)

section Semiring

variable [Semiring R]

-- this is a weakening of `exists_norm_finset_prod_le_of_nonempty`
lemma exists_map_finset_prod_le_of_nonempty {α S : Type*} [Semiring S] [LinearOrder S]
    [AddCommMonoid α] (g : α → S) {ι : Type*} {t : Finset ι} (ht : t.Nonempty) (f : ι → α)
    (Ultra : ∀ a b, g (a + b) ≤ max (g a) (g b)) : ∃ i ∈ t, g (∑ j ∈ t, f j) ≤ g (f i) := by
  simpa [Finset.le_sup'_iff] using Finset.Nonempty.map_sum_le_sup'_map g ht f Ultra

-- this is a weakening of `exists_norm_multiset_prod_le`
lemma exists_map_multiset_prod_le {α S : Type*} [Semiring S] [LinearOrder S]
    [AddCommMonoid α] (g : α → S) {ι : Type*} (Zero : g 0 = 0) (Nonneg : ∀ a, g a ≥ 0)
    (Ultra : ∀ a b, g (a + b) ≤ max (g a) (g b)) (t : Finset ι) [Nonempty ι]
    (f : ι → α) : ∃ i, (t.Nonempty → i ∈ t) ∧ g (∑ j ∈ t, f j) ≤ g (f i) := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [Zero, Nonneg]
  · exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ ↦ h, h'⟩) <|
      exists_map_finset_prod_le_of_nonempty g ht f Ultra

end Semiring

variable [Ring R]

-- this is a version of Fabrizio's apply_sum_eq_of_lt (in Algebra/Order/Ring/IsNonarchimedean)
-- but in our generality of function f + hypothesis
lemma apply_sum_eq_of_lt {α β S : Type*} [Semiring S] [LinearOrder S]
    [AddCommGroup α] (f : α → S) (Ultra : ∀ a b, f (a + b) ≤ max (f a) (f b)) {s : Finset β}
    {l : β → α} (Neg : ∀ a, f a = f (-a)) {k : β} (hk : k ∈ s)
    (hmax : ∀ j ∈ s, j ≠ k → f (l j) < f (l k)) :
    f (∑ i ∈ s, l i) = f (l k) := by
  by_cases hcard : s.card = 1
  · grind [Finset.card_eq_one.mp hcard]
  · classical
    rw [← Finset.add_sum_erase _ _ hk]
    have hNonempty : (s.erase k).Nonempty :=
      Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (by grind))
    have hrest_le := (Finset.Nonempty.map_sum_le_sup'_map f hNonempty l Ultra)
    simp only [Finset.le_sup'_iff, Finset.mem_erase, ne_eq] at hrest_le
    rw [ultrametric_strict f Ultra Neg (by grind), max_eq_left (le_of_lt (by grind))]

end MvPowerSeries
