/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.Ramification
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.Order.MonotoneContinuity
/-!
# The Herbrand function

This file supplies the group-theoretic content of
the Herbrand-function sum formula.  The old `AntitoneNormalSubgroupFiltration.herbrandStep` starts
with `|G₀| / |G₀|`; the normalized Herbrand function has, on `(m,m+1)`,
slope `|Gₘ₊₁| / |G₀|`.  We therefore deliberately use a new,
shifted definition here.

The definition is made on all of `ℝ`.  Below zero it is the identity, so
its restriction to `[-1,∞)` is exactly the normalized function on this range.
-/

@[expose] public section

noncomputable section

universe u

namespace RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G] [Finite G]
variable (F : AntitoneNormalSubgroupFiltration G)

/-- Each subgroup in the finite ambient group has a finite enumeration. -/
local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Classical decidability of subgroup membership for the Herbrand filtration formulas. -/
local instance subgroupMembershipDecidable (H : Subgroup G) (x : G) :
    Decidable (x ∈ H) :=
  Classical.propDecidable _

/-- The slope of the Herbrand function on `(i,i+1)`.  This is the shifted
quantity `|G_(i+1)| / |G_0|`, not the pre-existing `herbrandStep i`. -/
noncomputable def herbrandSlope (i : ℕ) : ℝ :=
  (Nat.card (F.lower (i + 1)) : ℝ) / Nat.card (F.lower 0)

/-- The value of the normalized Herbrand function at a natural number. -/
noncomputable def herbrandValueNat (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (herbrandSlope F) i

omit [Finite G] in
/-- States the theorem `herbrandValueNat_zero`. -/
@[simp] theorem herbrandValueNat_zero : (herbrandValueNat F) 0 = 0 := by
  simp [herbrandValueNat]

omit [Finite G] in
/-- States the theorem `herbrandValueNat_succ`. -/
theorem herbrandValueNat_succ (n : ℕ) :
    (herbrandValueNat F) (n + 1) =
      (herbrandValueNat F) n + (herbrandSlope F) n := by
  simp [herbrandValueNat, Finset.sum_range_succ]

/-- States the theorem `herbrandSlope_pos`. -/
theorem herbrandSlope_pos (i : ℕ) :
    0 < (herbrandSlope F) i := by
  have hi : 0 < Nat.card (F.lower (i + 1)) := Finite.card_pos
  have h0 : 0 < Nat.card (F.lower 0) := Finite.card_pos
  exact div_pos (Nat.cast_pos.mpr hi) (Nat.cast_pos.mpr h0)

/-- States the theorem `herbrandSlope_nonneg`. -/
theorem herbrandSlope_nonneg (i : ℕ) :
    0 ≤ (herbrandSlope F) i :=
  ((herbrandSlope_pos F) i).le

/-- States the theorem `one_div_card_le_herbrandSlope`. -/
theorem one_div_card_le_herbrandSlope (i : ℕ) :
    (1 : ℝ) / Nat.card (F.lower 0) ≤ (herbrandSlope F) i := by
  rw [herbrandSlope]
  have h0 : (0 : ℝ) < Nat.card (F.lower 0) := by
    exact_mod_cast (show 0 < Nat.card (F.lower 0) from Finite.card_pos)
  apply (div_le_div_iff_of_pos_right h0).2
  exact_mod_cast (show 0 < Nat.card (F.lower (i + 1)) from Finite.card_pos)

/-- States the theorem `herbrandValueNat_nonneg`. -/
theorem herbrandValueNat_nonneg (n : ℕ) :
    0 ≤ (herbrandValueNat F) n := by
  exact Finset.sum_nonneg fun i _ => (herbrandSlope_nonneg F) i

/-- States the theorem `nat_div_card_le_herbrandValueNat`. -/
theorem nat_div_card_le_herbrandValueNat (n : ℕ) :
    (n : ℝ) / Nat.card (F.lower 0) ≤ (herbrandValueNat F) n := by
  rw [herbrandValueNat]
  calc
    (n : ℝ) / Nat.card (F.lower 0) =
        ∑ _i ∈ Finset.range n, (1 : ℝ) / Nat.card (F.lower 0) := by
          simp [div_eq_mul_inv]
    _ ≤ ∑ i ∈ Finset.range n, (herbrandSlope F) i := by
      exact Finset.sum_le_sum fun i _ => (one_div_card_le_herbrandSlope F) i

/-- States the theorem `herbrandValueNat_strictMono`. -/
theorem herbrandValueNat_strictMono : StrictMono (herbrandValueNat F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [(herbrandValueNat_succ F)]
  exact lt_add_of_pos_right _ ((herbrandSlope_pos F) n)

/-- The Herbrand-function sum formula, in its explicit piecewise-linear form. -/
noncomputable def herbrandFunction (s : ℝ) : ℝ :=
  if 0 ≤ s then
    let m := ⌊s⌋₊
    (herbrandValueNat F) m +
      (s - (m : ℝ)) * (herbrandSlope F) m
  else
    s

omit [Finite G] in
/-- The Herbrand function depends only on the cardinalities of the lower
groups.  This comparison lemma is useful when a Galois group is replaced by
an isomorphic subgroup or quotient model. -/
theorem herbrandFunction_eq_of_card_lower_eq
    {G' : Type*} [Group G']
    (F' : AntitoneNormalSubgroupFiltration G')
    (hcard : ∀ n : ℕ, Nat.card (F.lower n) = Nat.card (F'.lower n))
    (s : ℝ) :
    (herbrandFunction F) s = (herbrandFunction F') s := by
  have hslope : ∀ n : ℕ,
      (herbrandSlope F) n = (herbrandSlope F') n := by
    intro n
    simp only [herbrandSlope, hcard]
  have hnat : ∀ n : ℕ,
      (herbrandValueNat F) n = (herbrandValueNat F') n := by
    intro n
    simp only [herbrandValueNat, hslope]
  by_cases hs : 0 ≤ s
  · simp only [herbrandFunction, hs, ↓reduceIte, hnat, hslope]
  · simp only [herbrandFunction, hs, ↓reduceIte]

omit [Finite G] in
/-- States the theorem `herbrandFunction_of_nonpos`. -/
theorem herbrandFunction_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    (herbrandFunction F) s = s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [herbrandFunction]
  · have hns : ¬ 0 ≤ s := not_le.mpr hs
    simp [herbrandFunction, hns]

omit [Finite G] in
/-- States the theorem `herbrandFunction_zero`. -/
@[simp] theorem herbrandFunction_zero : (herbrandFunction F) 0 = 0 := by
  simp [herbrandFunction]

omit [Finite G] in
/-- States the theorem `herbrandFunction_neg_one`. -/
@[simp] theorem herbrandFunction_neg_one : (herbrandFunction F) (-1) = -1 := by
  exact (herbrandFunction_of_nonpos F) (by norm_num)

omit [Finite G] in
/-- States the theorem `herbrandFunction_of_floor`. -/
theorem herbrandFunction_of_floor {s : ℝ} (hs : 0 ≤ s) (m : ℕ)
    (hm : ⌊s⌋₊ = m) :
    (herbrandFunction F) s = (herbrandValueNat F) m +
      (s - (m : ℝ)) * (herbrandSlope F) m := by
  simp [herbrandFunction, hs, hm]

omit [Finite G] in
/-- States the theorem `herbrandFunction_nat`. -/
@[simp] theorem herbrandFunction_nat (n : ℕ) :
    (herbrandFunction F) (n : ℝ) = (herbrandValueNat F) n := by
  simp [herbrandFunction]

/-- The first Herbrand value is the ratio of the first two lower-group orders. -/
theorem herbrandFunction_one_eq :
    (herbrandFunction F) 1 =
      (Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0) := by
  rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num,
    herbrandFunction_nat, show (1 : ℕ) = 0 + 1 by omega,
    herbrandValueNat_succ]
  simp [herbrandValueNat_zero, herbrandSlope]

/-- The first Herbrand value lies strictly above zero and at most one. -/
theorem herbrandFunction_one_pos_le_one :
    0 < (herbrandFunction F) 1 ∧ (herbrandFunction F) 1 ≤ 1 := by
  have hden : (0 : ℝ) < Nat.card (F.lower 0) := by
    exact_mod_cast (show 0 < Nat.card (F.lower 0) from Finite.card_pos)
  have hnum : (0 : ℝ) < Nat.card (F.lower 1) := by
    exact_mod_cast (show 0 < Nat.card (F.lower 1) from Finite.card_pos)
  have hsub : F.lower 1 ≤ F.lower 0 := F.antitone (by omega)
  let incl : F.lower 1 → F.lower 0 := fun x => ⟨x.1, hsub x.2⟩
  have hincl : Function.Injective incl := by
    intro x y h
    have hval : (x : G) = (y : G) :=
      congrArg (fun z : F.lower 0 => (z : G)) h
    exact Subtype.ext hval
  have hcard : Nat.card (F.lower 1) ≤ Nat.card (F.lower 0) :=
    Nat.card_le_card_of_injective incl hincl
  rw [herbrandFunction_one_eq]
  constructor
  · exact div_pos hnum hden
  · apply (div_le_iff₀ hden).2
    simpa using (Nat.cast_le.mpr hcard :
      (Nat.card (F.lower 1) : ℝ) ≤ Nat.card (F.lower 0))

omit [Finite G] in
/-- The defining affine formula on a half-open unit interval. -/
theorem herbrandFunction_eq_on_Ico (m : ℕ) {s : ℝ}
    (hms : (m : ℝ) ≤ s) (hsm : s < m + 1) :
    (herbrandFunction F) s = (herbrandValueNat F) m +
      (s - (m : ℝ)) * (herbrandSlope F) m := by
  apply (herbrandFunction_of_floor F) (le_trans (Nat.cast_nonneg m) hms) m
  exact (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg m) hms)).2 ⟨hms, by simpa using hsm⟩

omit [Finite G] in
/-- The closed-interval form.  At the right endpoint the
two adjacent affine expressions agree. -/
theorem herbrandFunction_eq_on_Icc (m : ℕ) {s : ℝ}
    (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (herbrandFunction F) s = (herbrandValueNat F) m +
      (s - (m : ℝ)) * (herbrandSlope F) m := by
  rcases hsm.eq_or_lt with hsm | hsm
  · subst s
    rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_num,
      (herbrandFunction_nat F), (herbrandValueNat_succ F)]
    norm_num
  · exact (herbrandFunction_eq_on_Ico F) m hms hsm

/-- The displayed formula immediately preceding the Herbrand-function sum formula. -/
theorem herbrandFunction_eq_card_sum_of_mem_Icc (m : ℕ) {s : ℝ}
    (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (herbrandFunction F) s =
      ((∑ i ∈ Finset.range m, (Nat.card (F.lower (i + 1)) : ℝ)) +
          (s - m) * Nat.card (F.lower (m + 1))) /
        Nat.card (F.lower 0) := by
  rw [(herbrandFunction_eq_on_Icc F) m hms hsm]
  simp_rw [herbrandValueNat, herbrandSlope, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have h0 : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (show 0 < Nat.card (F.lower 0) from Finite.card_pos))
  field_simp

/-- States the theorem `herbrandFunction_nonneg`. -/
theorem herbrandFunction_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (herbrandFunction F) s := by
  rw [(herbrandFunction_of_floor F) hs ⌊s⌋₊ rfl]
  exact add_nonneg ((herbrandValueNat_nonneg F) ⌊s⌋₊)
    (mul_nonneg (sub_nonneg.mpr (Nat.floor_le hs))
      ((herbrandSlope_nonneg F) ⌊s⌋₊))

/-- The Herbrand function is strictly increasing, as asserted after
the Herbrand quotient theorem. -/
theorem herbrandFunction_strictMono : StrictMono (herbrandFunction F) := by
  intro s t hst
  by_cases ht : t ≤ 0
  · rw [(herbrandFunction_of_nonpos F) (le_trans hst.le ht),
      (herbrandFunction_of_nonpos F) ht]
    exact hst
  by_cases hs : s < 0
  · rw [(herbrandFunction_of_nonpos F) hs.le]
    exact lt_of_lt_of_le hs ((herbrandFunction_nonneg F) (le_of_not_ge ht))
  have hs0 : 0 ≤ s := le_of_not_gt hs
  have ht0 : 0 ≤ t := hs0.trans hst.le
  let m := ⌊s⌋₊
  let n := ⌊t⌋₊
  have hmle : (m : ℝ) ≤ s := Nat.floor_le hs0
  have hmlt : s < m + 1 := by
    exact (Nat.floor_eq_iff hs0).1 rfl |>.2
  have hnle : (n : ℝ) ≤ t := Nat.floor_le ht0
  have hnlt : t < n + 1 := by
    exact (Nat.floor_eq_iff ht0).1 rfl |>.2
  have hmn : m ≤ n := Nat.floor_mono hst.le
  rw [(herbrandFunction_eq_on_Ico F) m hmle hmlt,
    (herbrandFunction_eq_on_Ico F) n hnle hnlt]
  rcases hmn.eq_or_lt with hmn | hmn
  · rw [← hmn]
    nlinarith [(herbrandSlope_pos F) m]
  · have hs_upper :
        (herbrandValueNat F) m + (s - m) * (herbrandSlope F) m <
          (herbrandValueNat F) (m + 1) := by
      rw [(herbrandValueNat_succ F)]
      nlinarith [(herbrandSlope_pos F) m]
    have hnat : (herbrandValueNat F) (m + 1) ≤ (herbrandValueNat F) n := by
      exact (herbrandValueNat_strictMono F).monotone (by omega)
    have ht_lower : (herbrandValueNat F) n ≤
        (herbrandValueNat F) n + (t - n) * (herbrandSlope F) n := by
      exact le_add_of_nonneg_right
        (mul_nonneg (by exact sub_nonneg.mpr hnle)
          ((herbrandSlope_nonneg F) n))
    exact hs_upper.trans_le (hnat.trans ht_lower)

/-- States the theorem `herbrandFunction_surjective`. -/
theorem herbrandFunction_surjective : Function.Surjective (herbrandFunction F) := by
  intro y
  by_cases hy : y ≤ 0
  · exact ⟨y, (herbrandFunction_of_nonpos F) hy⟩
  have hy0 : 0 < y := lt_of_not_ge hy
  let d : ℝ := Nat.card (F.lower 0)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (show 0 < Nat.card (F.lower 0) from Finite.card_pos)
  obtain ⟨N, hN⟩ := exists_nat_gt (y * d)
  have hyN : y ≤ (herbrandValueNat F) N := by
    apply le_trans ?_ ((nat_div_card_le_herbrandValueNat F) N)
    change y ≤ (N : ℝ) / d
    exact (le_div_iff₀ hd).2 hN.le
  let hex : ∃ n : ℕ, y ≤ (herbrandValueNat F) n := ⟨N, hyN⟩
  let n := Nat.find hex
  have hn_upper : y ≤ (herbrandValueNat F) n := Nat.find_spec hex
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hn0, (herbrandValueNat_zero F)] at hn_upper
    exact hy hn_upper
  let m := n - 1
  have hn_eq : n = m + 1 := by
    dsimp [m]
    omega
  have hm_lt_n : m < n := by omega
  have hm_lower : (herbrandValueNat F) m < y := by
    exact lt_of_not_ge (Nat.find_min hex hm_lt_n)
  let x : ℝ := m +
    (y - (herbrandValueNat F) m) / (herbrandSlope F) m
  have hx_lower : (m : ℝ) ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right
      (div_nonneg (sub_nonneg.mpr hm_lower.le) ((herbrandSlope_nonneg F) m))
  have hx_upper : x ≤ m + 1 := by
    have hyadd : y ≤
        (herbrandValueNat F) m + (herbrandSlope F) m := by
      rw [← (herbrandValueNat_succ F), ← hn_eq]
      exact hn_upper
    have hfrac :
        (y - (herbrandValueNat F) m) / (herbrandSlope F) m ≤ 1 :=
      (div_le_one ((herbrandSlope_pos F) m)).2 (by linarith)
    dsimp [x]
    linarith
  refine ⟨x, ?_⟩
  rw [(herbrandFunction_eq_on_Icc F) m hx_lower hx_upper]
  dsimp [x]
  field_simp [((herbrandSlope_pos F) m).ne']
  ring

/-- Continuity of the piecewise-linear Herbrand function. -/
theorem continuous_herbrandFunction : Continuous (herbrandFunction F) :=
  (herbrandFunction_strictMono F).monotone.continuous_of_surjective
    (herbrandFunction_surjective F)

/-- The inverse Herbrand function `ψ`. -/
noncomputable def inverseHerbrandFunction (t : ℝ) : ℝ :=
  Function.invFun (herbrandFunction F) t

/-- States the theorem `herbrandFunction_inverseHerbrandFunction`. -/
@[simp] theorem herbrandFunction_inverseHerbrandFunction (t : ℝ) :
    (herbrandFunction F) ((inverseHerbrandFunction F) t) = t :=
  Function.rightInverse_invFun (herbrandFunction_surjective F) t

/-- States the theorem `inverseHerbrandFunction_herbrandFunction`. -/
@[simp] theorem inverseHerbrandFunction_herbrandFunction (s : ℝ) :
    (inverseHerbrandFunction F) ((herbrandFunction F) s) = s :=
  Function.leftInverse_invFun (herbrandFunction_strictMono F).injective s

/-- States the theorem `inverseHerbrandFunction_strictMono`. -/
theorem inverseHerbrandFunction_strictMono : StrictMono (inverseHerbrandFunction F) := by
  intro s t hst
  apply (herbrandFunction_strictMono F).lt_iff_lt.mp
  simpa using hst

/-- States the theorem `inverseHerbrandFunction_surjective`. -/
theorem inverseHerbrandFunction_surjective : Function.Surjective (inverseHerbrandFunction F) := by
  intro s
  exact ⟨(herbrandFunction F) s, (inverseHerbrandFunction_herbrandFunction F) s⟩

/-- States the theorem `continuous_inverseHerbrandFunction`. -/
theorem continuous_inverseHerbrandFunction : Continuous (inverseHerbrandFunction F) :=
  (inverseHerbrandFunction_strictMono F).monotone.continuous_of_surjective
    (inverseHerbrandFunction_surjective F)

/-- The mutually inverse Herbrand functions as an order isomorphism of the
real line.  Its canonical form uses the restriction to `[-1,∞)`. -/
noncomputable def herbrandOrderIso : ℝ ≃o ℝ where
  toFun := (herbrandFunction F)
  invFun := (inverseHerbrandFunction F)
  left_inv := (inverseHerbrandFunction_herbrandFunction F)
  right_inv := (herbrandFunction_inverseHerbrandFunction F)
  map_rel_iff' := (herbrandFunction_strictMono F).le_iff_le

/-- States the theorem `herbrandFunction_mem_Ici_neg_one_iff`. -/
theorem herbrandFunction_mem_Ici_neg_one_iff {s : ℝ} :
    (herbrandFunction F) s ∈ Set.Ici (-1) ↔ s ∈ Set.Ici (-1) := by
  change -1 ≤ (herbrandFunction F) s ↔ -1 ≤ s
  simpa only [(herbrandFunction_neg_one F)] using
    ((herbrandFunction_strictMono F).le_iff_le :
      (herbrandFunction F) (-1) ≤ (herbrandFunction F) s ↔ (-1 : ℝ) ≤ s)

/-- States the theorem `inverseHerbrandFunction_mem_Ici_neg_one_iff`. -/
theorem inverseHerbrandFunction_mem_Ici_neg_one_iff {t : ℝ} :
    (inverseHerbrandFunction F) t ∈ Set.Ici (-1) ↔ t ∈ Set.Ici (-1) := by
  change -1 ≤ (inverseHerbrandFunction F) t ↔ -1 ≤ t
  have hψ : (inverseHerbrandFunction F) (-1) = -1 := by
    simpa only [(herbrandFunction_neg_one F)] using
      (inverseHerbrandFunction_herbrandFunction F) (-1)
  simpa only [hψ] using
    ((inverseHerbrandFunction_strictMono F).le_iff_le :
      (inverseHerbrandFunction F) (-1) ≤ (inverseHerbrandFunction F) t ↔ (-1 : ℝ) ≤ t)

/-- The number of positive lower-numbered levels, truncated at `n`, through
which an inertia element survives.  For a classical depth `i(σ)`, this is
`min (i(σ) - 1) n`. -/
noncomputable def truncatedLowerDepth (n : ℕ) (σ : F.lower 0) : ℕ := by
  classical
  exact ((Finset.range n).filter fun i => (σ : G) ∈ F.lower (i + 1)).card

/-- States the theorem `card_lower_succ_eq_sum_indicator`. -/
theorem card_lower_succ_eq_sum_indicator (i : ℕ) :
    Nat.card (F.lower (i + 1)) =
      ∑ σ : F.lower 0, if (σ : G) ∈ F.lower (i + 1) then 1 else 0 := by
  classical
  let ι : F.lower (i + 1) → F.lower 0 := fun σ =>
    ⟨(σ : G), F.antitone (Nat.zero_le (i + 1)) σ.property⟩
  have hι : Function.Injective ι := by
    intro σ τ h
    exact Subtype.ext (congrArg (fun x : F.lower 0 => (x : G)) h)
  rw [Nat.card_eq_fintype_card]
  change Finset.univ.card =
    ∑ σ : F.lower 0, if (σ : G) ∈ F.lower (i + 1) then 1 else 0
  rw [← Finset.card_image_of_injective Finset.univ hι]
  rw [show (∑ σ : F.lower 0,
      if (σ : G) ∈ F.lower (i + 1) then 1 else 0) =
      (Finset.univ.filter fun σ : F.lower 0 =>
        (σ : G) ∈ F.lower (i + 1)).card by simp]
  congr 1
  ext σ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨τ, hτ⟩
    have hcoe : (τ : G) = (σ : G) :=
      congrArg (fun z : F.lower 0 => (z : G)) hτ
    rw [← hcoe]
    exact τ.property
  · intro hσ
    refine ⟨⟨(σ : G), hσ⟩, ?_⟩
    exact Subtype.ext rfl

/-- The Herbrand-function sum formula at an integral argument, in the intrinsic depth form.
It is the defining identity
`g₀⁻¹ ∑σ (min {i(σ), n+1} - 1)` with the truncated depth
expressed directly by membership in the lower groups. -/
theorem herbrandValueNat_eq_depth_sum (n : ℕ) :
    (herbrandValueNat F) n =
      (∑ σ : F.lower 0, ((truncatedLowerDepth F) n σ : ℝ)) /
        Nat.card (F.lower 0) := by
  classical
  rw [herbrandValueNat]
  simp_rw [herbrandSlope, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [(card_lower_succ_eq_sum_indicator F)]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [show (truncatedLowerDepth F) n σ =
      ∑ i ∈ Finset.range n, if (σ : G) ∈ F.lower (i + 1) then 1 else 0 by
    simp [truncatedLowerDepth]]
  push_cast
  rfl

/-- The Herbrand-function sum formula for a general real argument in `[m,m+1]`.  The first
sum is the intrinsic version of `∑σ (min {i(σ),m+1}-1)`; the last
term records the elements surviving in `G_(m+1)` for the fractional part. -/
theorem herbrandFunction_eq_depth_sum_of_mem_Icc (m : ℕ) {s : ℝ}
    (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (herbrandFunction F) s =
      ((∑ σ : F.lower 0, ((truncatedLowerDepth F) m σ : ℝ)) +
          (s - m) * Nat.card (F.lower (m + 1))) /
        Nat.card (F.lower 0) := by
  rw [(herbrandFunction_eq_on_Icc F) m hms hsm,
    (herbrandValueNat_eq_depth_sum F)]
  rw [herbrandSlope]
  have h0 : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (show 0 < Nat.card (F.lower 0) from Finite.card_pos))
  field_simp

end AntitoneNormalSubgroupFiltration
end RamificationTheory.DiscreteValuationField
