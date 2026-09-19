/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.CenteredMaximal.Lattice.Smear

/-!
# The lower bound `Φ ≤ c₂`

The period cell `cell = [-hgap, hgap) × [-vgap/2, vgap/2)` minus the four open slots is `goodSet`;
it has area at least `2 hgap vgap - 4 slotW slotH`, and every point of it has a level-one witness
using atoms of the neighbouring cells (`exists_isWitness_of_abs`). The `(2N + 1)²` translates
`goodCopy k l`, `|k|, |l| ≤ N`, are disjoint and lie in the level set of `smeared N ε` at height
`1 - 2ε`, while `‖smeared N ε‖₁ ≤ (2N + 3)² (1 + heavy)`. With `ε = 1 / (2N + 3)` a weak type bound
`C` therefore satisfies `C ≥ ((2N + 1)/(2N + 3))³ Φ`, and `N → ∞` gives `C ≥ Φ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace LeanPool.CenteredMaximal.Lattice

/-- The period cell `[-hgap, hgap) × [-vgap/2, vgap/2)`. -/
def cell : Set (Fin 2 → ℝ) :=
  univ.pi fun i => Ico (![-hgap, -vgap / 2] i) (![hgap, vgap / 2] i)

/-- The four open slots, one in each quadrant, excluded from the witnessed region. -/
def slots : Set (Fin 2 → ℝ) :=
  {z | root / 2 < |z 0| ∧ |z 0| < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < |z 1| ∧
    |z 1| < vgap - sideLH2 / 2}

/-- The witnessed part of the period cell. -/
def goodSet : Set (Fin 2 → ℝ) := cell \ slots

/-- The period vector of the cell with index `(k, l)`. -/
def shift (k l : ℤ) : Fin 2 → ℝ := ![2 * k * hgap, l * vgap]

/-- The translate of `goodSet` into the cell with index `(k, l)`. -/
def goodCopy (k l : ℤ) : Set (Fin 2 → ℝ) := (fun z => -shift k l + z) ⁻¹' goodSet

theorem mem_cell {z : Fin 2 → ℝ} :
    z ∈ cell ↔ (-hgap ≤ z 0 ∧ z 0 < hgap) ∧ (-(vgap / 2) ≤ z 1 ∧ z 1 < vgap / 2) := by
  simp [cell, Fin.forall_fin_two, neg_div]

theorem measurableSet_slots : MeasurableSet slots := by
  have h₀ : Measurable fun z : Fin 2 → ℝ => |z 0| :=
    (continuous_abs.comp (continuous_apply 0)).measurable
  have h₁ : Measurable fun z : Fin 2 → ℝ => |z 1| :=
    (continuous_abs.comp (continuous_apply 1)).measurable
  exact (measurableSet_lt measurable_const h₀).inter ((measurableSet_lt h₀ measurable_const).inter
    ((measurableSet_lt measurable_const h₁).inter (measurableSet_lt h₁ measurable_const)))

theorem measurableSet_goodSet : MeasurableSet goodSet :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ico).diff measurableSet_slots

theorem volume_cell : volume cell = ENNReal.ofReal (2 * hgap * vgap) := by
  rw [cell, Real.volume_pi_Ico, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← ENNReal.ofReal_mul (by linarith [hgap_pos])]
  congr 1
  ring

private theorem mem_union_of_abs {a b x : ℝ} (ha : a < |x|) (hb : |x| < b) :
    x ∈ Ioo a b ∪ Ioo (-b) (-a) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at ha hb
    exact Or.inl ⟨ha, hb⟩
  · rw [abs_of_neg hx] at ha hb
    exact Or.inr ⟨by linarith, by linarith⟩

private theorem volume_preimage_abs_Ioo_le {a b : ℝ} : volume (abs ⁻¹' Ioo a b) ≤
    ENNReal.ofReal (b - a) + ENNReal.ofReal (b - a) :=
  calc volume (abs ⁻¹' Ioo a b) ≤ volume (Ioo a b ∪ Ioo (-b) (-a)) :=
        measure_mono fun _ ⟨ha, hb⟩ ↦ mem_union_of_abs ha hb
    _ ≤ _ := (measure_union_le _ _).trans_eq <| by simp [neg_add_eq_sub]

/-- The four open slots, each a `slotW × slotH` rectangle, have total area at most
`4 slotW slotH`, written in `ℝ≥0∞` as `(slotW + slotW) * (slotH + slotH)`. -/
theorem volume_slots_le : volume slots ≤ (ENNReal.ofReal slotW + ENNReal.ofReal slotW) *
    (ENNReal.ofReal slotH + ENNReal.ofReal slotH) :=
  calc volume slots
    _ ≤ volume (univ.pi ![abs ⁻¹' Ioo (root / 2) (2 * hgap - sideLHL2 / 2),
          abs ⁻¹' Ioo (sideH1 / 2) (vgap - sideLH2 / 2)]) :=
      measure_mono fun _ ⟨h₁, h₂, h₃, h₄⟩ ↦ mem_univ_pi.2 <| Fin.forall_fin_two.2 ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    _ = _ * _ := (volume_pi_pi _).trans (Fin.prod_univ_two _)
    _ ≤ _ := mul_le_mul' volume_preimage_abs_Ioo_le volume_preimage_abs_Ioo_le

/-- The witnessed part `goodSet = cell \ slots` of the period cell has area at least
`2 hgap vgap - 4 slotW slotH`: the area of `cell` (`volume_cell`) minus the bound `volume_slots_le`
on the four slots. -/
theorem ofReal_le_volume_goodSet : ENNReal.ofReal (2 * hgap * vgap - 4 * (slotW * slotH)) ≤
    volume goodSet := by
  -- the left side is `volume cell - 4 * (slotW * slotH)`, computed in `ℝ≥0∞`
  rw [ENNReal.ofReal_sub _ (mul_pos four_pos (mul_pos slotW_pos slotH_pos)).le, ← volume_cell,
    ENNReal.ofReal_mul zero_le_four, ENNReal.ofReal_mul slotW_pos.le, ENNReal.ofReal_ofNat]
  -- `volume_slots_le` bounds the slots, and `volume cell - volume slots ≤ volume (cell \ slots)`
  exact (tsub_le_tsub_left (volume_slots_le.trans_eq (by ring)) _).trans le_measure_sdiff

theorem volume_goodCopy (k l : ℤ) : volume (goodCopy k l) = volume goodSet :=
  measure_preimage_add volume (-shift k l) goodSet

theorem measurableSet_goodCopy (k l : ℤ) : MeasurableSet (goodCopy k l) :=
  measurableSet_goodSet.preimage (measurable_const_add _)

theorem mem_goodCopy {k l : ℤ} {z : Fin 2 → ℝ} :
    z ∈ goodCopy k l ↔ ![z 0 - 2 * k * hgap, z 1 - l * vgap] ∈ goodSet := by
  have : -shift k l + z = ![z 0 - 2 * k * hgap, z 1 - l * vgap] := by
    ext i
    fin_cases i <;> simp [shift] <;> ring
  rw [goodCopy, Set.mem_preimage, this]

/-- The translates `goodCopy k l`, `(k, l) : ℤ × ℤ`, of `goodSet` are pairwise disjoint. The index
set is all of `ℤ × ℤ`: restrict it to a finite box with `Set.PairwiseDisjoint.subset` before adding
up volumes with `measure_biUnion_finset`, as `ofReal_le_volume_levelSet` does. -/
theorem pairwiseDisjoint_goodCopy :
    (univ : Set (ℤ × ℤ)).PairwiseDisjoint fun p => goodCopy p.1 p.2 := by
  rintro ⟨k, l⟩ - ⟨k', l'⟩ - hne
  refine Set.disjoint_left.2 fun z hz hz' ↦ hne ?_
  simp only [mem_goodCopy, goodSet, Set.mem_sdiff, mem_cell, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hz hz'
  -- distinct integers are at distance at least one, but `z` lying in both half-open cells puts
  -- `k, k'` (in units of `2 * hgap`) and `l, l'` (in units of `vgap`) less than one apart
  refine Prod.ext (Int.pairwise_one_le_dist.eq ?_) (Int.pairwise_one_le_dist.eq ?_) <;>
    refine not_le.2 <| (Int.dist_eq _ _).trans_lt <| abs_sub_lt_iff.2 ⟨?_, ?_⟩ <;> nlinarith

/-- Every point `z` of the translate `goodCopy k l` has a level-one witness `(L, A)` whose atoms lie
in `nearBox k l`. This is `exists_isWitness_of_abs` (the cell centred at the origin) moved to the
cell with index `(k, l)`; `nearBox_subset_atomBox` then puts the atoms inside `atomBox N` when
`|k|, |l| ≤ N`, as in `ofReal_le_volume_levelSet`. -/
theorem exists_isWitness_of_mem_goodCopy {k l : ℤ} {z : Fin 2 → ℝ} (hz : z ∈ goodCopy k l) :
    ∃ L A, A ⊆ nearBox k l ∧ IsWitness (z 0) (z 1) L A := by
  -- the untranslated point lies in the cell centred at the origin and (unfolding `slots`) outside
  -- the four slots, so it has a witness with atoms in `nearBox 0 0`
  obtain ⟨hcell, hslot⟩ := mem_goodCopy.1 hz
  obtain ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩ := mem_cell.1 hcell
  obtain ⟨L, A, hA, hw⟩ :=
    exists_isWitness_of_abs (abs_le.2 ⟨hx₁, hx₂.le⟩) (abs_le.2 ⟨hy₁, hy₂.le⟩) hslot
  -- translating the witness by `(2 * k, l)` moves it to `z` and its atoms into `nearBox k l`
  exact ⟨L, _, map_addRight_subset_nearBox hA k l, by simpa using hw.translate k l⟩

/-- For `|k|, |l| ≤ N`, the atoms `nearBox k l` available to a witness in the cell with index
`(k, l)` are kept in `atomBox N`: the columns `2k - 2, …, 2k + 2` lie in `-2N - 2, …, 2N + 2` and
the rows `l - 1, …, l + 1` lie in `-N - 1, …, N + 1`. -/
theorem nearBox_subset_atomBox {N : ℕ} {k l : ℤ} (hk : |k| ≤ N) (hl : |l| ≤ N) :
    nearBox k l ⊆ atomBox N := by
  grind [nearBox, atomBox]

/-- The level set of `smeared N ε` at height `1 - 2ε` has measure at least `(2N + 1)²` times the
lower bound `2 hgap vgap - 4 slotW slotH` on the area of `goodSet` (`ofReal_le_volume_goodSet`), for
every `ε > 0`: it contains the `(2N + 1)²` disjoint copies `goodCopy k l`, `|k|, |l| ≤ N`, of
`goodSet`. This is the level-set side of the weak type inequality in `ofReal_mul_phi_le`. -/
theorem ofReal_le_volume_levelSet (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH))) ≤
      volume {z | ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z} := by
  -- the `(2N + 1)²` indices `(k, l)` with `|k|, |l| ≤ N`
  set S := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N
  have hcard : S.card = (2 * N + 1) ^ 2 := by grind [Finset.card_product, Int.card_Icc]
  calc ENNReal.ofReal ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH)))
      = S.card • ENNReal.ofReal (2 * hgap * vgap - 4 * (slotW * slotH)) := by
        rw [← ENNReal.ofReal_nsmul, hcard, nsmul_eq_mul]
        norm_cast
    -- each copy `goodCopy k l` is a translate of `goodSet`, so has at least that area
    _ ≤ ∑ p ∈ S, volume (goodCopy p.1 p.2) :=
        S.card_nsmul_le_sum _ _ fun _ _ ↦
          ofReal_le_volume_goodSet.trans_eq (volume_goodCopy ..).symm
    -- the copies are pairwise disjoint
    _ = volume (⋃ p ∈ S, goodCopy p.1 p.2) :=
        (measure_biUnion_finset (pairwiseDisjoint_goodCopy.subset (subset_univ _))
          fun p _ ↦ measurableSet_goodCopy p.1 p.2).symm
    -- every point of a copy has a witness with atoms in `nearBox k l ⊆ atomBox N`, so it lies in
    -- the level set
    _ ≤ _ := measure_mono <| iUnion₂_subset fun p hp z hz ↦ by
        obtain ⟨L, A, hA, hw⟩ := exists_isWitness_of_mem_goodCopy hz
        refine lt_maximalFunction_smeared hε (hA.trans <| nearBox_subset_atomBox ?_ ?_) hw <;> grind

private theorem ofReal_mul_ofReal_le_of_isWeakTypeBound {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (1 - 2 * ε) *
        ENNReal.ofReal ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH))) ≤
      C * ENNReal.ofReal ((2 * N + 3) ^ 2 * (1 + heavy)) :=
  -- the weak type inequality for `smeared N ε` at level `1 - 2ε`, with the level set bounded below
  -- by `ofReal_le_volume_levelSet` and the mass `‖smeared N ε‖₁` bounded above
  (mul_le_mul_right (ofReal_le_volume_levelSet N hε) _).trans <|
    (hC _ (integrable_smeared N ε) _).trans <| mul_le_mul_right
      ((lintegral_smeared N hε).trans_le <| ENNReal.ofReal_le_ofReal (sum_colWeight_atomBox_le N)) _

private theorem div_pow_three_mul_phi_eq (N : ℕ) : ((2 * N + 1) / (2 * N + 3)) ^ 3 * phi =
    (2 * N + 1) / (2 * N + 3) * ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH))) /
      ((2 * N + 3) ^ 2 * (1 + heavy)) := by
  rw [phi_eq]
  have := heavy_pos
  field_simp

/-- A weak type bound in dimension two is at least `((2N + 1)/(2N + 3))³ Φ`, for every `N`. This is
the finite-`N` form of `ofReal_phi_le`, which lets `N → ∞`. -/
theorem ofReal_mul_phi_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) (N : ℕ) :
    ENNReal.ofReal (((2 * N + 1) / (2 * N + 3)) ^ 3 * phi) ≤ C := by
  -- test the weak type bound on `smeared N ε` with `ε = 1 / (2N + 3)`, whose level `1 - 2ε` is
  -- `(2N + 1)/(2N + 3)`, and divide by the mass bound `(2N + 3)² (1 + heavy)`
  have hq : 1 - 2 * (1 / (2 * N + 3)) = ((2 * N + 1) / (2 * N + 3) : ℝ) := by
    field_simp
    ring
  rw [div_pow_three_mul_phi_eq,
    ENNReal.ofReal_div_of_pos (mul_pos (by positivity) (add_pos one_pos heavy_pos)),
    ENNReal.ofReal_mul (by positivity), ← hq]
  exact ENNReal.div_le_of_le_mul (ofReal_mul_ofReal_le_of_isWeakTypeBound hC N (by positivity))

/-- Every weak type bound in dimension two is at least `Φ`. Taking the infimum over all such `C`
with `le_weakTypeConstant` gives `Φ ≤ c₂`; `ofReal_mul_phi_le` is the weaker bound
`((2N + 1)/(2N + 3))³ Φ ≤ C` for a single `N`. -/
theorem ofReal_phi_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) : ENNReal.ofReal phi ≤ C := by
  -- the finite-`N` bounds `ofReal_mul_phi_le` tend to `Φ`, as `(2N + 1)/(2N + 3) → 1`
  refine le_of_tendsto' (x := atTop) (ENNReal.tendsto_ofReal ?_) (ofReal_mul_phi_le hC)
  simpa [add_comm] using
    ((tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 3 2 two_ne_zero).pow 3).mul_const phi

end LeanPool.CenteredMaximal.Lattice
