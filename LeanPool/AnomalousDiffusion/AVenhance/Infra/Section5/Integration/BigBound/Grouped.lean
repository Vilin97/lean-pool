/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound.Centered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Assembly

/-! # Grouped mean-zero assembly: the centered ten-term family

Only the *sum* `twistie4 + twistie5 + normie3` of the ten §5.1 terms is mean zero
(the grouped mean-zero decomposition (12)/(13)); the three are not individually so.  The centered
    family
`section5CenteredTerm` replaces the slots `3` (`twistie4`), `4` (`twistie5`) and `8` (`normie3`) of
`section5Term` by their `centerCell`.  On `t ∈ (0,1)` it has the same pointwise sum as the original
family (`sum_section5CenteredTerm_eq`), and the triangle inequality in the exact `HDot⁻¹` time norm
holds for any finite family of jointly continuous terms (`timeHMinusOneNorm_sum_range_le`). -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

/-! ### Triangle inequality for a finite jointly continuous family -/

/-- A finite sum of jointly continuous terms obeys the triangle inequality in the `HDot⁻¹` time norm
(`L²` regularity and time measurability of every partial sum come from joint continuity). -/
theorem timeHMinusOneNorm_sum_range_le {u : ℕ → ℝ → Vec 2 → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hu : ∀ i, i < n → ContinuousOn (fun p : ℝ × Vec 2 => u i p.1 p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) :
    timeHMinusOneNorm (fun t x => ∑ i ∈ Finset.range n, u i t x) ≤
      ∑ i ∈ Finset.range n, timeHMinusOneNorm (u i) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hpre : ContinuousOn
        (fun p : ℝ × Vec 2 => ∑ i ∈ Finset.range n, u i p.1 p.2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) :=
      continuousOn_finsetSum _ fun i hi => hu i (by have := Finset.mem_range.mp hi; omega)
    have hlast := hu n (by omega)
    simp only [Finset.sum_range_succ]
    calc timeHMinusOneNorm (fun t x => ∑ i ∈ Finset.range n, u i t x + u n t x)
        ≤ timeHMinusOneNorm (fun t x => ∑ i ∈ Finset.range n, u i t x) +
            timeHMinusOneNorm (u n) :=
          timeHMinusOneNorm_add_le
            (f := fun t x => ∑ i ∈ Finset.range n, u i t x)
            (fun _ ht => memL2On_of_continuousOn_slice (F := fun t x => ∑ i ∈ Finset.range n, u i
                t x)
              hpre ht)
            (fun _ ht => memL2On_of_continuousOn_slice hlast ht)
            (aemeasurable_hMinusOneNorm_of_continuousOn
              (F := fun t x => ∑ i ∈ Finset.range n, u i t x) hpre)
            (aemeasurable_hMinusOneNorm_of_continuousOn hlast)
      _ ≤ _ := add_le_add (ih fun i hi => hu i (by omega)) le_rfl

/-! ### The centered family -/

section Centered

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The ten §5.1 terms with the three grouped slots `3` (`twistie4`), `4` (`twistie5`) and
`8` (`normie3`) replaced by their unit-cube centering. -/
def section5CenteredTerm (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (i : ℕ) : ℝ → Vec 2 → ℝ :=
  match i with
  | 3 => fun t x => centerCell (section5Term I hΦ m κm T d e 3 t) x
  | 4 => fun t x => centerCell (section5Term I hΦ m κm T d e 4 t) x
  | 8 => fun t x => centerCell (section5Term I hΦ m κm T d e 8 t) x
  | i => section5Term I hΦ m κm T d e i

/-- On a time where the slots are `L²` and the group `twistie4 + twistie5 + normie3` has mean zero,
the centered ten-term sum equals the original ten-term sum. -/
theorem sum_section5CenteredTerm_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hL2 : ∀ i, i < 10 → MemL2On unitCube (section5Term I hΦ m κm T d e i t))
    (hgroup : MeanZeroOn unitCube (fun x =>
      twistie4 I hΦ m κm T t x + twistie5 I hΦ m κm T t x + normie3 I hΦ m κm T t x))
    (x : Vec 2) :
    ∑ i ∈ Finset.range 10, section5CenteredTerm I hΦ m κm T d e i t x =
      ∑ i ∈ Finset.range 10, section5Term I hΦ m κm T d e i t x := by
  have h3 : MemL2On unitCube (twistie4 I hΦ m κm T t) := hL2 3 (by norm_num)
  have h4 : MemL2On unitCube (twistie5 I hΦ m κm T t) := hL2 4 (by norm_num)
  have h8 : MemL2On unitCube (normie3 I hΦ m κm T t) := hL2 8 (by norm_num)
  have key := centerCell_add_add h3 h4 h8 hgroup x
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, section5CenteredTerm, section5Term]
  linarith

end Centered

end AVenhance.Infra.Section5.Integration
end
