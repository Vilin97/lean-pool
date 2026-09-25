/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SetGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Finite growth with disjoint exchange supports

Binary sums grow by adding one translate. A polynomial initial stage and
a multiplicative stage produce more than half of the group; two disjoint
such families then cover the whole group.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Module

namespace EGZ.Expansion

section FiniteSums

variable {E A G : Type*} [DecidableEq E] [DecidableEq A]
  [AddCommGroup G] [DecidableEq G]

/-- All sums obtained by choosing any subfamily of a finite family. -/
def binarySums (shift : E → G) (F : Finset E) : Finset G :=
  F.powerset.image fun J ↦ ∑ e ∈ J, shift e

omit [DecidableEq E] in
@[simp] theorem binarySums_empty (shift : E → G) : binarySums shift ∅ = {0} := by
  simp [binarySums]

omit [DecidableEq E] in
theorem zero_mem_binarySums (shift : E → G) (F : Finset E) : 0 ∈ binarySums shift F := by
  exact Finset.mem_image.mpr ⟨∅, by simp, by simp⟩

theorem binarySums_insert (shift : E → G) (F : Finset E) {e : E} (he : e ∉ F) :
    binarySums shift (insert e F) =
      translate (binarySums shift F) (shift e) ∪ binarySums shift F := by
  rw [binarySums, Finset.powerset_insert, Finset.image_union, Finset.image_image]
  rw [Finset.union_comm]
  congr 1
  ext x
  simp only [Finset.mem_image, mem_translate, binarySums, Function.comp_apply]
  constructor
  · rintro ⟨J, hJ, rfl⟩
    refine ⟨J, hJ, ?_⟩
    rw [Finset.sum_insert (Finset.notMem_of_mem_powerset_of_notMem hJ he)]
    abel
  · rintro ⟨J, hJ, hx⟩
    refine ⟨J, hJ, ?_⟩
    rw [Finset.sum_insert (Finset.notMem_of_mem_powerset_of_notMem hJ he)]
    rw [hx]
    abel

omit [DecidableEq E] in
/-- Subset sums can be expressed as Boolean choices indexed by the selected
family, the form used by the exchange-completion argument. -/
theorem exists_bool_choice_of_mem_binarySums (shift : E → G) (F : Finset E)
    {x : G} (hx : x ∈ binarySums shift F) :
    ∃ choice : F → Bool, (∑ e : F, if choice e then shift e.val else 0) = x := by
  classical
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hx
  have hJF := Finset.mem_powerset.mp hJ
  refine ⟨fun e ↦ decide (e.val ∈ J), ?_⟩
  simp only [decide_eq_true_eq]
  have hcoe := Finset.sum_coe_sort F (fun e ↦ if e ∈ J then shift e else 0)
  rw [hcoe, ← Finset.sum_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter, and_iff_right_iff_imp]
  exact fun h ↦ hJF h

/-- Atoms reserved by a family of exchanges. -/
def usedAtoms (support : E → Finset A) (F : Finset E) : Finset A := F.biUnion support

omit [DecidableEq E] in
theorem card_usedAtoms_le (support : E → Finset A) (F : Finset E) {B : ℕ}
    (hB : ∀ e, (support e).card ≤ B) : (usedAtoms support F).card ≤ B * F.card := by
  simpa only [usedAtoms, Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul F support B (fun e _ ↦ hB e)

@[simp] theorem usedAtoms_insert (support : E → Finset A) (F : Finset E) (e : E) :
    usedAtoms support (insert e F) = support e ∪ usedAtoms support F := by
  simp [usedAtoms]

omit [DecidableEq E] in
theorem new_exchange_of_positive_boundary (support : E → Finset A) (shift : E → G)
    (hzero : ∀ e, support e = ∅ → shift e = 0) (F : Finset E) (Y : Finset G)
    {e : E} (he : Disjoint (support e) (usedAtoms support F))
    (hpos : 0 < boundary Y (shift e)) : e ∉ F := by
  intro heF
  have hsub : support e ⊆ usedAtoms support F := Finset.subset_biUnion_of_mem support heF
  have hemp : support e = ∅ := disjoint_self.mp (he.mono_right hsub)
  simp only [hzero e hemp, boundary_zero, lt_self_iff_false] at hpos

/-- A family uses disjoint supports and avoids all previously reserved atoms. -/
def Admissible (support : E → Finset A) (U : Finset A) (F : Finset E) : Prop :=
  (F : Set E).Pairwise (fun e f ↦ Disjoint (support e) (support f)) ∧
    Disjoint (usedAtoms support F) U

omit [DecidableEq E] in
theorem admissible_empty (support : E → Finset A) (U : Finset A) :
    Admissible support U ∅ := by simp [Admissible, usedAtoms]

theorem Admissible.insert {support : E → Finset A} {U : Finset A} {F : Finset E}
    (hF : Admissible support U F) {e : E}
    (he : Disjoint (support e) (U ∪ usedAtoms support F)) :
    Admissible support U (insert e F) := by
  have hU := (Finset.disjoint_union_right.mp he).1
  have hused := (Finset.disjoint_union_right.mp he).2
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_insert]
    apply hF.1.insert
    intro f hf _
    have hh := hused.mono_right (Finset.subset_biUnion_of_mem support hf)
    exact ⟨hh, hh.symm⟩
  · rw [usedAtoms_insert]
    exact Finset.disjoint_union_left.mpr ⟨hU, hF.2⟩

/-- A finite greedy iteration, retaining the current family whenever its
size already meets the next target. The optional stopping predicate is
returned explicitly. -/
theorem iterate_binary_growth (support : E → Finset A) (shift : E → G)
    (U : Finset A) (F₀ : Finset E) (hF₀ : Admissible support U F₀)
    (N : ℕ) (target : ℕ → ℝ) (stop : Finset E → Prop)
    (hstart : target 0 ≤ (binarySums shift F₀).card)
    (step : ∀ i < N, ∀ F : Finset E, F₀ ⊆ F → Admissible support U F →
      F.card ≤ F₀.card + i → ¬ stop F → target i ≤ (binarySums shift F).card →
      (binarySums shift F).card < target (i + 1) →
      ∃ e : E, e ∉ F ∧ Disjoint (support e) (U ∪ usedAtoms support F) ∧
        target (i + 1) ≤ (binarySums shift (insert e F)).card) :
    ∃ F : Finset E, F₀ ⊆ F ∧ Admissible support U F ∧ F.card ≤ F₀.card + N ∧
      (stop F ∨ target N ≤ (binarySums shift F).card) := by
  classical
  have build : ∀ n ≤ N, ∃ F : Finset E, F₀ ⊆ F ∧ Admissible support U F ∧
      F.card ≤ F₀.card + n ∧ (stop F ∨ target n ≤ (binarySums shift F).card) := by
    intro n hn
    induction n with
    | zero => exact ⟨F₀, Finset.Subset.refl _, hF₀, by simp, Or.inr hstart⟩
    | succ n ih =>
      obtain ⟨F, hsub, hF, hcard, halt | hsize⟩ := ih (by omega)
      · exact ⟨F, hsub, hF, by omega, Or.inl halt⟩
      by_cases halt : stop F
      · exact ⟨F, hsub, hF, by omega, Or.inl halt⟩
      by_cases hnext : target (n + 1) ≤ (binarySums shift F).card
      · exact ⟨F, hsub, hF, by omega, Or.inr hnext⟩
      obtain ⟨e, he, heU, hnew⟩ := step n (by omega) F hsub hF hcard halt hsize (lt_of_not_ge hnext)
      exact ⟨insert e F, hsub.trans (Finset.subset_insert _ _), hF.insert heU,
        by rw [Finset.card_insert_of_notMem he]; omega, Or.inr hnew⟩
  exact build N le_rfl

end FiniteSums

/-- A convenient integer reciprocal step for polynomial growth. -/
def growthDenominator (d : ℕ) : ℕ := 6 * d * d * 2 ^ d

theorem growthDenominator_pos {d : ℕ} (hd : 0 < d) : 0 < growthDenominator d := by
  unfold growthDenominator
  positivity

/-- Increasing the root of the set size by a fixed reciprocal costs no
more than the boundary provided by the basis estimate. -/
theorem polynomial_growth_step {d : ℕ} (hd : 0 < d) {x : ℝ} (hx : 1 ≤ x) :
    (x + (growthDenominator d : ℝ)⁻¹) ^ d ≤
      x ^ d + x ^ (d - 1) / (6 * d) := by
  let H : ℝ := growthDenominator d
  have hH : 0 < H := by
    change (0 : ℝ) < growthDenominator d
    exact_mod_cast growthDenominator_pos hd
  have hHone : 1 ≤ H := by
    change (1 : ℝ) ≤ growthDenominator d
    exact_mod_cast growthDenominator_pos hd
  have hh : 0 ≤ H⁻¹ := inv_nonneg.mpr hH.le
  have hhone : H⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hHone
  have hx0 : 0 ≤ x := by linarith
  have hxh : 0 ≤ x + H⁻¹ := add_nonneg hx0 hh
  have hdiff := abs_pow_sub_pow_le (a := x + H⁻¹) (b := x) (n := d)
  rw [show x + H⁻¹ - x = H⁻¹ by ring, abs_of_nonneg hh,
    abs_of_nonneg hxh, abs_of_nonneg hx0, max_eq_left (by linarith)] at hdiff
  have hpow : (x + H⁻¹) ^ (d - 1) ≤ (2 * x) ^ (d - 1) :=
    pow_le_pow_left₀ hxh (by linarith) _
  have htwo : (2 : ℝ) ^ (d - 1) ≤ 2 ^ d :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1)
  have hfactor : H⁻¹ * d * 2 ^ d = (6 * d : ℝ)⁻¹ := by
    dsimp [H, growthDenominator]
    push_cast
    field_simp
  calc
    (x + H⁻¹) ^ d ≤ x ^ d + |(x + H⁻¹) ^ d - x ^ d| := by
      linarith [le_abs_self ((x + H⁻¹) ^ d - x ^ d)]
    _ ≤ x ^ d + H⁻¹ * d * (x + H⁻¹) ^ (d - 1) := add_le_add_right hdiff _
    _ ≤ x ^ d + H⁻¹ * d * (2 * x) ^ (d - 1) := by gcongr
    _ ≤ x ^ d + H⁻¹ * d * 2 ^ d * x ^ (d - 1) := by
      simp only [mul_pow]
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htwo (pow_nonneg hx0 (d - 1)))
        (show 0 ≤ H⁻¹ * d by positivity)
      simpa only [mul_assoc] using add_le_add_right h (x ^ d)
    _ = x ^ d + x ^ (d - 1) / (6 * d) := by rw [hfactor]; ring

section Stages

variable {E A : Type*} [DecidableEq E] [DecidableEq A]
  {p d B budget : ℕ} [NeZero p] [Fact p.Prime]
  (support : E → Finset A) (shift : E → FpCoord p d)

omit [DecidableEq E] in
omit [NeZero p] in
theorem exists_polynomial_growth (hd : 0 < d)
    (hB : ∀ e, (support e).card ≤ B)
    (hzero : ∀ e, support e = ∅ → shift e = 0)
    (hbasis : ∀ U : Finset A, U.card ≤ budget →
      ∃ b : Basis (Fin d) (ZMod p) (FpCoord p d),
        ∀ i, ∃ e : E, Disjoint (support e) U ∧ shift e = b i)
    (U : Finset A) (N : ℕ) (hbudget : U.card + B * N ≤ budget)
    (hsmall : 2 * (1 + N / (growthDenominator d : ℝ)) ≤ p) :
    ∃ F : Finset E, Admissible support U F ∧ F.card ≤ N ∧
      (1 + N / (growthDenominator d : ℝ)) ^ d ≤ (binarySums shift F).card := by
  classical
  let H : ℝ := growthDenominator d
  have hH : 0 < H := by
    change (0 : ℝ) < growthDenominator d
    exact_mod_cast growthDenominator_pos hd
  let target : ℕ → ℝ := fun i ↦ (1 + i / H) ^ d
  obtain ⟨F, _, hF, hcard, hsize⟩ := iterate_binary_growth support shift U ∅
    (admissible_empty support U) N target (fun _ ↦ False)
    (by simp [target]) (by
      intro i hi F _ hF hcard _ hsize hnext
      have hc : F.card ≤ i := by simpa using hcard
      have hused : (U ∪ usedAtoms support F).card ≤ budget := calc
        _ ≤ U.card + (usedAtoms support F).card := Finset.card_union_le _ _
        _ ≤ U.card + B * i := Nat.add_le_add_left
          ((card_usedAtoms_le support F hB).trans (Nat.mul_le_mul_left B hc)) _
        _ ≤ budget := (Nat.add_le_add_left (Nat.mul_le_mul_left B hi.le) _).trans hbudget
      obtain ⟨b, hb⟩ := hbasis (U ∪ usedAtoms support F) hused
      let Y := binarySums shift F
      let x : ℝ := (Y.card : ℝ) ^ ((d : ℝ)⁻¹)
      have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hxpow : x ^ d = (Y.card : ℝ) :=
        Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
      have hone : (1 : ℝ) ≤ Y.card := by
        exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_binarySums shift F⟩
      have hx : 1 ≤ x :=
        (pow_le_pow_iff_left₀ (n := d) (by norm_num) hx0 (by omega)).mp
          (by simpa [hxpow] using hone)
      have hix : 1 + (i : ℝ) / H ≤ x :=
        (pow_le_pow_iff_left₀ (n := d) (by positivity) hx0 (by omega)).mp
          (by simpa only [target, hxpow] using hsize)
      have hxnext : x < 1 + ((i + 1 : ℕ) : ℝ) / H :=
        (pow_lt_pow_iff_left₀ (n := d) hx0 (by positivity) (by omega)).mp
          (by simpa only [target, hxpow] using hnext)
      have hnextN : 1 + ((i + 1 : ℕ) : ℝ) / H ≤ 1 + (N : ℝ) / H := by
        apply add_le_add_right
        exact div_le_div_of_nonneg_right (by exact_mod_cast hi) hH.le
      have hxp : 2 * x ≤ p := by
        have : 2 * (1 + (N : ℝ) / H) ≤ p := hsmall
        linarith
      obtain ⟨j, hj⟩ := exists_basis_boundary_real b hd Y x hx hxpow.symm hxp
      obtain ⟨e, heU, he⟩ := hb j
      have hbd : x ^ (d - 1) ≤ 6 * d * (boundary Y (shift e) : ℝ) := by simpa only [he] using hj
      have hbdpos : 0 < boundary Y (shift e) := by
        have hh : 0 < x ^ (d - 1) := pow_pos (by linarith) _
        by_contra hn
        have hz : boundary Y (shift e) = 0 := by omega
        simp only [hz, Nat.cast_zero, mul_zero] at hbd
        linarith
      have henot := new_exchange_of_positive_boundary support shift hzero F Y
        (Finset.disjoint_union_right.mp heU).2 hbdpos
      refine ⟨e, henot, heU, ?_⟩
      rw [binarySums_insert shift F henot, ← boundary_add_card]
      push_cast
      have hinc : (x + H⁻¹) ^ d ≤ x ^ d + (boundary Y (shift e) : ℝ) :=
        (polynomial_growth_step hd hx).trans (add_le_add_right
          ((div_le_iff₀ (by positivity : (0 : ℝ) < 6 * d)).mpr (by nlinarith [hbd])) _)
      have htarget : target (i + 1) ≤ (x + H⁻¹) ^ d := by
        dsimp only [target]
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        rw [add_div, one_div]
        linarith
      have hh := htarget.trans hinc
      simpa only [hxpow, add_comm] using hh)
  exact ⟨F, hF, by simpa using hcard, hsize.resolve_left id⟩

omit [DecidableEq E] in
theorem exists_multiplicative_growth
    (hB : ∀ e, (support e).card ≤ B)
    (hzero : ∀ e, support e = ∅ → shift e = 0)
    {a : ℝ} (ha : 0 < a)
    (hgrowth : ∀ U : Finset A, U.card ≤ budget →
      ∀ Y : Finset (FpCoord p d), 2 * Y.card ≤ p ^ d →
      ∃ e : E, Disjoint (support e) U ∧ a * Y.card ≤ p * (boundary Y (shift e) : ℝ))
    (U : Finset A) (F₀ : Finset E) (hF₀ : Admissible support U F₀)
    {seed : ℝ} (hseed : 0 < seed) (hsize : seed ≤ (binarySums shift F₀).card)
    (N : ℕ) (hbudget : U.card + B * (F₀.card + N) ≤ budget)
    (hlarge : (p : ℝ) ^ d < 2 * (seed * (1 + N * a / p))) :
    ∃ F : Finset E, F₀ ⊆ F ∧ Admissible support U F ∧
      F.card ≤ F₀.card + N ∧ p ^ d < 2 * (binarySums shift F).card := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  let target : ℕ → ℝ := fun i ↦ seed * (1 + i * a / p)
  obtain ⟨F, hsub, hF, hcard, hstop⟩ := iterate_binary_growth support shift U F₀ hF₀ N target
    (fun F ↦ p ^ d < 2 * (binarySums shift F).card)
    (by simpa [target] using hsize) (by
      intro i hi F _ hF hcard hstop hsize _
      have hused : (U ∪ usedAtoms support F).card ≤ budget := calc
        _ ≤ U.card + (usedAtoms support F).card := Finset.card_union_le _ _
        _ ≤ U.card + B * (F₀.card + i) := Nat.add_le_add_left
          ((card_usedAtoms_le support F hB).trans (Nat.mul_le_mul_left B hcard)) _
        _ ≤ budget := (Nat.add_le_add_left (Nat.mul_le_mul_left B (by omega)) _).trans hbudget
      let Y := binarySums shift F
      obtain ⟨e, heU, he⟩ := hgrowth (U ∪ usedAtoms support F) hused Y (le_of_not_gt hstop)
      have hseedY : seed ≤ (Y.card : ℝ) :=
        (show seed ≤ target i by
          dsimp [target]
          nlinarith [div_nonneg (mul_nonneg (Nat.cast_nonneg i) ha.le) hp.le]).trans hsize
      have hbdpos : 0 < boundary Y (shift e) := by
        have hpos : 0 < a * (Y.card : ℝ) := mul_pos ha (hseed.trans_le hseedY)
        by_contra hn
        have hz : boundary Y (shift e) = 0 := by omega
        simp only [hz, Nat.cast_zero, mul_zero] at he
        linarith
      have henot := new_exchange_of_positive_boundary support shift hzero F Y
        (Finset.disjoint_union_right.mp heU).2 hbdpos
      refine ⟨e, henot, heU, ?_⟩
      rw [binarySums_insert shift F henot, ← boundary_add_card]
      push_cast
      have hincr : seed * a / p ≤ (boundary Y (shift e) : ℝ) :=
        (div_le_iff₀ hp).mpr (by nlinarith [mul_le_mul_of_nonneg_left hseedY ha.le])
      have htarget : target (i + 1) = target i + seed * a / p := by
        dsimp [target]
        push_cast
        ring
      rw [htarget]
      exact (add_le_add hsize hincr).trans_eq (add_comm _ _))
  refine ⟨F, hsub, hF, hcard, ?_⟩
  rcases hstop with hstop | hstop
  · exact hstop
  · have hh : (p : ℝ) ^ d < 2 * (binarySums shift F).card :=
      hlarge.trans_le (mul_le_mul_of_nonneg_left hstop (by norm_num))
    exact_mod_cast hh

end Stages

section Cover

variable {E A G : Type*} [DecidableEq E] [DecidableEq A]
  [AddCommGroup G] [DecidableEq G]

theorem Admissible.union {support : E → Finset A} {U : Finset A} {F J : Finset E}
    (hF : Admissible support U F) (hJ : Admissible support (U ∪ usedAtoms support F) J) :
    Admissible support U (F ∪ J) := by
  have hcross := (Finset.disjoint_union_right.mp hJ.2).2
  have hpair (e : E) (he : e ∈ F) (f : E) (hf : f ∈ J) :
      Disjoint (support e) (support f) :=
    (hcross.mono (Finset.subset_biUnion_of_mem support hf)
      (Finset.subset_biUnion_of_mem support he)).symm
  refine ⟨?_, ?_⟩
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact hF.1 he hf hne
    · exact hpair e he f hf
    · exact (hpair f hf e he).symm
    · exact hJ.1 he hf hne
  · simp only [usedAtoms, Finset.union_biUnion, Finset.disjoint_union_left]
    exact ⟨hF.2, (Finset.disjoint_union_right.mp hJ.2).1⟩

theorem add_mem_binarySums_union (support : E → Finset A) (shift : E → G)
    (hzero : ∀ e, support e = ∅ → shift e = 0)
    {F J : Finset E} (hdis : Disjoint (usedAtoms support F) (usedAtoms support J))
    {x y : G} (hx : x ∈ binarySums shift F) (hy : y ∈ binarySums shift J) :
    x + y ∈ binarySums shift (F ∪ J) := by
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hy
  have hLF := Finset.mem_powerset.mp hL
  have hMJ := Finset.mem_powerset.mp hM
  have hsum : (∑ e ∈ L ∩ M, shift e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have heL := (Finset.mem_inter.mp he).1
    have heM := (Finset.mem_inter.mp he).2
    apply hzero
    exact disjoint_self.mp (hdis.mono
      (Finset.subset_biUnion_of_mem support (hLF heL))
      (Finset.subset_biUnion_of_mem support (hMJ heM)))
  refine Finset.mem_image.mpr
    ⟨L ∪ M, Finset.mem_powerset.mpr (Finset.union_subset_union hLF hMJ), ?_⟩
  have h := Finset.sum_union_inter (s₁ := L) (s₂ := M) (f := shift)
  simpa only [hsum, add_zero] using h

theorem binarySums_cover_of_two_large [Fintype G]
    (support : E → Finset A) (shift : E → G)
    (hzero : ∀ e, support e = ∅ → shift e = 0)
    {F J : Finset E} (hdis : Disjoint (usedAtoms support F) (usedAtoms support J))
    (hF : Fintype.card G < 2 * (binarySums shift F).card)
    (hJ : Fintype.card G < 2 * (binarySums shift J).card) :
    binarySums shift (F ∪ J) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro g
  let S := binarySums shift F
  let T := binarySums shift J
  let V := T.image (fun y ↦ g - y)
  have hV : V.card = T.card := Finset.card_image_of_injective _ (fun _ _ h ↦ sub_right_injective h)
  have hcard : (Finset.univ : Finset G).card < S.card + V.card := by
    rw [Finset.card_univ, hV]
    change Fintype.card G < (binarySums shift F).card + (binarySums shift J).card
    omega
  obtain ⟨x, hx⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ S) (Finset.subset_univ V) hcard
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
  have hsum : x + y = g := by rw [← hxy]; abel
  rw [← hsum]
  exact add_mem_binarySums_union support shift hzero hdis (Finset.mem_inter.mp hx).1 hy

end Cover

section FiniteCriterion

variable {E A : Type*} [DecidableEq E] [DecidableEq A]
  {p d B budget : ℕ} [NeZero p] [Fact p.Prime]
  (support : E → Finset A) (shift : E → FpCoord p d)

omit [DecidableEq E] in
theorem exists_half_binarySums (hd : 0 < d)
    (hB : ∀ e, (support e).card ≤ B)
    (hzero : ∀ e, support e = ∅ → shift e = 0)
    (hbasis : ∀ U : Finset A, U.card ≤ budget →
      ∃ b : Basis (Fin d) (ZMod p) (FpCoord p d),
        ∀ i, ∃ e : E, Disjoint (support e) U ∧ shift e = b i)
    {a : ℝ} (ha : 0 < a)
    (hgrowth : ∀ U : Finset A, U.card ≤ budget →
      ∀ Y : Finset (FpCoord p d), 2 * Y.card ≤ p ^ d →
      ∃ e : E, Disjoint (support e) U ∧ a * Y.card ≤ p * (boundary Y (shift e) : ℝ))
    (U : Finset A) (n m : ℕ) (hbudget : U.card + B * (n + m) ≤ budget)
    (hsmall : 2 * (1 + n / (growthDenominator d : ℝ)) ≤ p)
    (hlarge : (p : ℝ) ^ d <
      2 * ((1 + n / (growthDenominator d : ℝ)) ^ d * (1 + m * a / p))) :
    ∃ F : Finset E, Admissible support U F ∧ F.card ≤ n + m ∧
      p ^ d < 2 * (binarySums shift F).card := by
  classical
  obtain ⟨F₀, hF₀, hcard₀, hsize₀⟩ := exists_polynomial_growth support shift hd hB hzero hbasis U n
    ((Nat.add_le_add_left (Nat.mul_le_mul_left B (Nat.le_add_right n m)) _).trans hbudget) hsmall
  have hseed : 0 < (1 + n / (growthDenominator d : ℝ)) ^ d := by positivity
  obtain ⟨F, _, hF, hcard, hsize⟩ := exists_multiplicative_growth support shift hB hzero ha hgrowth
    U F₀ hF₀ hseed hsize₀ m
    ((Nat.add_le_add_left (Nat.mul_le_mul_left B (Nat.add_le_add_right hcard₀ m)) _).trans
      hbudget) hlarge
  exact ⟨F, hF, hcard.trans (Nat.add_le_add_right hcard₀ m), hsize⟩

omit [DecidableEq E] in
/-- Explicit finite criterion for complete binary-sum coverage using
pairwise disjoint exchange supports. -/
theorem exists_binarySums_cover_finite (hd : 0 < d)
    (hB : ∀ e, (support e).card ≤ B)
    (hzero : ∀ e, support e = ∅ → shift e = 0)
    (hbasis : ∀ U : Finset A, U.card ≤ budget →
      ∃ b : Basis (Fin d) (ZMod p) (FpCoord p d),
        ∀ i, ∃ e : E, Disjoint (support e) U ∧ shift e = b i)
    {a : ℝ} (ha : 0 < a)
    (hgrowth : ∀ U : Finset A, U.card ≤ budget →
      ∀ Y : Finset (FpCoord p d), 2 * Y.card ≤ p ^ d →
      ∃ e : E, Disjoint (support e) U ∧ a * Y.card ≤ p * (boundary Y (shift e) : ℝ))
    (n m : ℕ) (hbudget : B * (2 * (n + m)) ≤ budget)
    (hsmall : 2 * (1 + n / (growthDenominator d : ℝ)) ≤ p)
    (hlarge : (p : ℝ) ^ d <
      2 * ((1 + n / (growthDenominator d : ℝ)) ^ d * (1 + m * a / p))) :
    ∃ F : Finset E, Admissible support ∅ F ∧ F.card ≤ 2 * (n + m) ∧
      (usedAtoms support F).card ≤ budget ∧ binarySums shift F = Finset.univ := by
  classical
  have hbudget₁ : (∅ : Finset A).card + B * (n + m) ≤ budget := by
    simp only [Finset.card_empty, zero_add]
    exact (Nat.mul_le_mul_left B (by omega)).trans hbudget
  obtain ⟨F, hF, hcardF, hsizeF⟩ :=
    exists_half_binarySums support shift hd hB hzero hbasis ha hgrowth
    ∅ n m hbudget₁ hsmall hlarge
  have hbudget₂ : (usedAtoms support F).card + B * (n + m) ≤ budget := by
    have hh := (card_usedAtoms_le support F hB).trans (Nat.mul_le_mul_left B hcardF)
    nlinarith [hbudget]
  obtain ⟨J, hJ, hcardJ, hsizeJ⟩ :=
    exists_half_binarySums support shift hd hB hzero hbasis ha hgrowth
    (usedAtoms support F) n m hbudget₂ hsmall hlarge
  have hJ' : Admissible support (∅ ∪ usedAtoms support F) J := by simpa using hJ
  have hcard : (F ∪ J).card ≤ 2 * (n + m) :=
    (Finset.card_union_le F J).trans (by omega)
  refine ⟨F ∪ J, hF.union hJ', hcard,
    ((card_usedAtoms_le support (F ∪ J) hB).trans (Nat.mul_le_mul_left B hcard)).trans hbudget, ?_⟩
  apply binarySums_cover_of_two_large support shift hzero hJ.2.symm
  · simpa [FpCoord] using hsizeF
  · simpa [FpCoord] using hsizeJ

end FiniteCriterion

/-- Uniform numerical parameters for a linear atom budget. The two stages
may have equal length; a deliberately generous fixed growth rate suffices. -/
theorem exists_binary_growth_parameters (d B : ℕ) (hd : 0 < d) (c : ℝ) (hc : 0 < c) :
    ∃ a : ℝ, ∃ p₀ : ℕ, 0 < a ∧ ∀ p : ℕ, p₀ ≤ p →
      ∃ n : ℕ, (B * (2 * (n + n)) : ℝ) ≤ c * p ∧
        2 * (1 + n / (growthDenominator d : ℝ)) ≤ p ∧
        (p : ℝ) ^ d < 2 * ((1 + n / (growthDenominator d : ℝ)) ^ d *
          (1 + n * a / p)) := by
  let L : ℕ := max 8 ⌈4 * B / c⌉₊
  have hL8 : 8 ≤ L := le_max_left _ _
  have hL : 0 < L := by omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hcL : 4 * (B : ℝ) ≤ c * L := by
    have hh : 4 * (B : ℝ) / c ≤ L := (Nat.le_ceil _).trans
      (Nat.cast_le.mpr (show ⌈4 * (B : ℝ) / c⌉₊ ≤ L from le_max_right _ _))
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith
  let H : ℝ := growthDenominator d
  have hH : 0 < H := by
    change (0 : ℝ) < growthDenominator d
    exact_mod_cast growthDenominator_pos hd
  have hHone : 1 ≤ H := by
    change (1 : ℝ) ≤ growthDenominator d
    exact_mod_cast growthDenominator_pos hd
  let Q : ℝ := (2 * L * H) ^ d
  have hQ : 0 < Q := pow_pos (by positivity) _
  let a : ℝ := 2 * L * Q
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, 2 * L, ha, ?_⟩
  intro p hp
  let n : ℕ := p / L
  have hn : 1 ≤ n := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hmul : L * n ≤ p := Nat.mul_div_le p L
  have hLmul : L ≤ L * n := by simpa using Nat.mul_le_mul_left L hn
  have hrem : p % L < L := Nat.mod_lt p hL
  have hid : L * n + p % L = p := Nat.div_add_mod p L
  have hplow : p ≤ 2 * L * n := by nlinarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmulR : (L : ℝ) * n ≤ p := by exact_mod_cast hmul
  have hplowR : (p : ℝ) ≤ 2 * L * n := by exact_mod_cast hplow
  refine ⟨n, ?_, ?_, ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_right hcL (Nat.cast_nonneg n)
    have h₂ := mul_le_mul_of_nonneg_left hmulR hc.le
    nlinarith
  · have hndiv : (n : ℝ) / H ≤ n := div_le_self (Nat.cast_nonneg n) hHone
    have h4n : (4 : ℝ) * n ≤ p := by
      have h4L : (4 : ℝ) ≤ L := by exact_mod_cast (show 4 ≤ L by omega)
      nlinarith [mul_le_mul_of_nonneg_right h4L (Nat.cast_nonneg n)]
    change 2 * (1 + (n : ℝ) / H) ≤ p
    linarith
  · let seed : ℝ := (1 + n / H) ^ d
    have hseed : 0 < seed := by dsimp [seed]; positivity
    have hbase : (p : ℝ) ≤ (2 * L * H) * (1 + n / H) := by
      have heq : (2 * L * H) * (1 + n / H) = 2 * L * H + 2 * L * n := by
        field_simp
      rw [heq]
      nlinarith [mul_pos hLR hH]
    have hpow : (p : ℝ) ^ d ≤ Q * seed := by
      simpa only [mul_pow, Q, seed] using pow_le_pow_left₀ hpR.le hbase d
    have hfactor : Q ≤ n * a / p := by
      apply (le_div_iff₀ hpR).2
      have hh := mul_le_mul_of_nonneg_right hplowR hQ.le
      dsimp [a]
      nlinarith
    have hmulQ := mul_le_mul_of_nonneg_left hfactor hseed.le
    change (p : ℝ) ^ d < 2 * (seed * (1 + n * a / p))
    nlinarith [pow_pos hpR d]

universe u v

/-- For a sufficiently large fixed growth rate, a linear atom budget
supports a family of disjoint exchanges whose binary sums cover the group.
The growth rate and prime threshold are chosen before all exchange data. -/
theorem exists_binarySums_cover_uniform (d B : ℕ) (hd : 0 < d) (c : ℝ) (hc : 0 < c) :
    ∃ a : ℝ, ∃ p₀ : ℕ, 0 < a ∧
      ∀ p : ℕ, ∀ (_ : NeZero p) (_ : Fact p.Prime), p₀ ≤ p →
      ∀ (E : Type u) (A : Type v), ∀ (_ : DecidableEq E) (_ : DecidableEq A),
      ∀ (support : E → Finset A) (shift : E → FpCoord p d),
      (∀ e, (support e).card ≤ B) →
      (∀ e, support e = ∅ → shift e = 0) →
      (∀ U : Finset A, (U.card : ℝ) ≤ c * p →
        ∃ b : Basis (Fin d) (ZMod p) (FpCoord p d),
          ∀ i, ∃ e : E, Disjoint (support e) U ∧ shift e = b i) →
      (∀ U : Finset A, (U.card : ℝ) ≤ c * p →
        ∀ Y : Finset (FpCoord p d), 2 * Y.card ≤ p ^ d →
        ∃ e : E, Disjoint (support e) U ∧ a * Y.card ≤ p * (boundary Y (shift e) : ℝ)) →
      ∃ F : Finset E,
        (F : Set E).Pairwise (fun e f ↦ Disjoint (support e) (support f)) ∧
        ((usedAtoms support F).card : ℝ) ≤ c * p ∧
        binarySums shift F = Finset.univ := by
  obtain ⟨a, p₀, ha, hparams⟩ := exists_binary_growth_parameters d B hd c hc
  refine ⟨a, p₀, ha, ?_⟩
  intro p hpzero hpprime hp E A _ _ support shift hB hzero hbasis hgrowth
  obtain ⟨n, hn, hsmall, hlarge⟩ := hparams p hp
  let budget : ℕ := ⌊c * p⌋₊
  have hbudgetReal : (budget : ℝ) ≤ c * p := Nat.floor_le (by positivity)
  have hnatbudget : B * (2 * (n + n)) ≤ budget :=
    (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hn)
  have hbasis' (U : Finset A) (hU : U.card ≤ budget) :=
    hbasis U ((Nat.cast_le.mpr hU).trans hbudgetReal)
  have hgrowth' (U : Finset A) (hU : U.card ≤ budget) :=
    hgrowth U ((Nat.cast_le.mpr hU).trans hbudgetReal)
  obtain ⟨F, hF, _, hused, hcover⟩ := exists_binarySums_cover_finite support shift hd hB hzero
    hbasis' ha hgrowth' n n hnatbudget hsmall hlarge
  exact ⟨F, hF.1, (Nat.cast_le.mpr hused).trans hbudgetReal, hcover⟩

end EGZ.Expansion
