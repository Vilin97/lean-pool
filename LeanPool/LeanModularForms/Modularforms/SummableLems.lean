/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import LeanPool.LeanModularForms.Modularforms.ExpLems
public import LeanPool.LeanModularForms.Modularforms.Upperhalfplane
public import LeanPool.LeanModularForms.Modularforms.BigO
public import LeanPool.LeanModularForms.Modularforms.Equivs
public import LeanPool.LeanModularForms.Modularforms.TsumderivWithin

/-! # SummableLems -/


@[expose] public section


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

private lemma neg_eq_comp_negEquiv {α : Type*} (f : ℤ → α) :
    (fun d => f (-d)) = (fun d => f d) ∘ negEquiv.toFun := by
  funext
  rfl

theorem int_sum_neg {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T2Space α] (f : ℤ → α) :
  ∑' d : ℤ, f d = ∑' d, f (-d) := by
  rw [neg_eq_comp_negEquiv]
  exact (negEquiv.tsum_eq f).symm

theorem summable_neg {α : Type*} [TopologicalSpace α] [AddCommMonoid α] (f : ℤ → α)
    (hf : Summable f) : Summable fun d => f (-d) := by
  rw [neg_eq_comp_negEquiv]
  exact negEquiv.summable_iff.mpr hf


lemma aux33 (f : ℕ → ℂ) (hf : Summable f) : ∑' n, f (n) =
    limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.range N, f (n)) := by
  rw [Filter.Tendsto.limUnder_eq]
  exact hf.hasSum.comp tendsto_finset_range

/- this is being Pr'd-/
lemma tsum_pnat_eq_tsum_succ3 {α : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
  (f : ℕ → α) : ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1) := by apply tsum_pnat_eq_tsum_succ



theorem nat_pos_tsum2 {α : Type _} [TopologicalSpace α] [AddCommMonoid α]
    (f : ℕ → α) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f := by
  apply PNat.coe_injective.summable_iff
  intro x hx
  simp only [mem_range, not_exists] at *
  by_cases h : 0 < x
  · simpa using hx ⟨x,h⟩
  simp only [not_lt, nonpos_iff_eq_zero] at *
  rw [h]
  exact hf

theorem tsum_pNat {α : Type _} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [T2Space α]
  [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n := by
  by_cases hf2 : Summable f
  · rw [hf2.tsum_eq_zero_add, hf, zero_add]
    exact tsum_pnat_eq_tsum_succ
  have h1 := tsum_eq_zero_of_not_summable hf2
  rw [← nat_pos_tsum2 f hf] at hf2
  have h2 := tsum_eq_zero_of_not_summable hf2
  simp [h1, h2]


lemma tsum_pnat_eq_tsum_succ4 {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α]
  (f : ℕ → α) (hf : Summable f) : f 0 + ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f n := by
  rw [Summable.tsum_eq_zero_add hf]
  simp only [add_right_inj]
  apply tsum_pnat_eq_tsum_succ

/-- Closed form for ∑ n·rⁿ over ℕ+ when ‖r‖ < 1. -/
lemma tsum_pnat_coe_mul_geometric {r : ℝ} (hr : ‖r‖ < 1) :
    (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2 := by
  rw [tsum_pNat (f := fun n => (n : ℝ) * r ^ n) (by simp)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hr

theorem nat_pos_tsum2' {α : Type*} [TopologicalSpace α] [AddCommMonoid α] (f : ℕ → α) :
    (Summable fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1) := by
  rw [← Equiv.summable_iff _root_.Equiv.pnatEquivNat]
  constructor
  · intro hf
    exact hf.congr fun b => by simp
  intro hf
  exact hf.congr fun b => by simp

theorem int_nat_sum {α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
  [CompleteSpace α]
  (f : ℤ → α) : Summable f → Summable fun x : ℕ => f x := by
  have : IsCompl (Set.range (Int.ofNat : ℕ → ℤ)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) _
      exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  rw [← summable_subtype_and_compl (s := Set.range (Int.ofNat : ℕ → ℤ))]
  rintro ⟨h_left, h_right⟩
  rw [← (Equiv.ofInjective (Int.ofNat : ℕ → ℤ) Nat.cast_injective).symm.summable_iff]
  apply Summable.congr h_left
  intro b
  simp only [comp_apply]
  apply congr_arg
  exact Eq.symm (Equiv.apply_ofInjective_symm Nat.cast_injective b)

theorem HasSum.nonneg_add_neg {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α] {a b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n)
      a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b) := by
  convert hnonneg.int_rec hneg using 1
  ext (i | j) <;> rfl


theorem HasSum.pos_add_zero_add_neg {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α] {a b : α} {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n +
      1)) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b) :=
  haveI : ∀ g : ℕ → α, HasSum (fun k => g (k + 1)) a → HasSum g (a + g 0) := by
    intro g hg
    simpa using (hasSum_nat_add_iff _).mp hg
  (this (fun n => f n) hpos).nonneg_add_neg hneg

theorem upp_half_not_ints (z : ℍ) (n : ℤ) : (z : ℂ) ≠ n :=
  UpperHalfPlane.ne_intCast z n


lemma aus (a b : ℂ) : a + b ≠ 0 ↔ a ≠ -b :=
  Iff.ne (Iff.symm eq_neg_iff_add_eq_zero)

lemma pnat_inv_sub_squares (z : ℍ) :
  (fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n)) = fun n : ℕ+ => 2 * z.1 * (1 / (z ^ 2 - n ^ 2)):=
  by
  funext n
  field_simp
  rw [one_div_add_one_div]
  · norm_cast
    ring_nf
    have h2 := upp_half_not_ints z n
    simp only [Int.cast_natCast, ne_eq, PNat.pow_coe, Nat.cast_pow] at *
  · have h1 := upp_half_not_ints z (n)
    norm_cast at *
    rw [@sub_eq_zero]
    apply UpperHalfPlane.ne_intCast
  have := UpperHalfPlane.ne_intCast z (-(n : ℤ))
  rw [aus]
  aesop


lemma upper_half_plane_ne_int_pow_two (z : ℍ) (n : ℤ) : (z : ℂ) ^ 2 - n ^ 2 ≠ 0 := by
  intro h
  rw [sq_sub_sq, mul_eq_zero] at h
  cases h with
  | inr h =>
    have := upp_half_not_ints z n
    rw [sub_eq_zero] at h
    apply absurd h this
  | inl h =>
    have := upp_half_not_ints z (-n)
    rw [add_eq_zero_iff_eq_neg] at h
    simp only [Int.cast_neg, ne_eq] at *
    apply absurd h this

theorem upbnd (z : ℍ) (d : ℤ) : (d ^ 2 : ℝ) * r z ^ 2 ≤ ‖((z : ℂ) ^ 2 - d ^ 2)‖ := by
  by_cases hd : d ≠ 0
  · have h1 : (z ^ 2 : ℂ) - d ^ 2 = d ^ 2 * (1 / d * z - 1) * (1 / d * z + 1) := by
      ring_nf
      simp [hd]
    rw [h1]
    simp only [one_div, Complex.norm_mul, norm_pow, norm_intCast, sq_abs, ge_iff_le]
    rw [mul_assoc]
    gcongr
    rw [pow_two]
    gcongr
    · exact (r_pos _).le
    · have h1 := auxbound2 z ((d : ℝ)⁻¹) (d := -1) (by norm_num)
      apply le_trans h1
      apply le_of_eq
      congr
      simp only [ofReal_inv, ofReal_intCast, ofReal_neg, ofReal_one]
      ring
    · have h1 := auxbound2 z ((d : ℝ)⁻¹) (d := 1) (by norm_num)
      apply le_trans h1
      apply le_of_eq
      congr
      simp only [ofReal_inv, ofReal_intCast]
  · simp only [ne_eq, Decidable.not_not] at hd
    simp only [hd, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      sub_zero, norm_pow, norm_nonneg, pow_nonneg]



/- This is from the mod forms repo -/
theorem lhs_summable (z : ℍ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n) := by
  have h1 := pnat_inv_sub_squares z
  rw [h1]
  apply Summable.mul_left
  apply summable_norm_iff.1
  simp only [one_div, norm_inv]
  have hs : Summable fun n : ℕ+ => (r z ^ 2 * n ^ 2)⁻¹ := by
    simp only [mul_inv_rev]
    apply Summable.mul_right
    have hrr : Summable fun (i : ℕ) ↦ ((i : ℝ) ^ 2)⁻¹ := by simp
    apply hrr.subtype
  apply Summable.of_nonneg_of_le _ _ hs
  · intro b
    rw [inv_nonneg]
    simp
  intro b
  rw [inv_le_inv₀]
  · rw [mul_comm]
    apply upbnd z
  · simp at *
    simpa using (upper_half_plane_ne_int_pow_two z b)
  apply mul_pos
  · norm_cast
    apply pow_pos
    apply r_pos
  have hb := b.2
  norm_cast
  apply pow_pos
  simpa using hb


theorem sum_int_even {α : Type*} [UniformSpace α] [CommRing α] [IsUniformAddGroup α]
    [CompleteSpace α] [T2Space α] (f : ℤ → α) (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) :
    ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n := by
  have hpos : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ+, f n) := by
    rw [← _root_.Equiv.pnatEquivNat.hasSum_iff]
    simp_rw [Equiv.pnatEquivNat] at *
    simp only [Equiv.coe_fn_mk] at *
    have hf3 : Summable ((fun n : ℕ => f (↑n + 1)) ∘ PNat.natPred) := by
      have hs : Summable fun n : ℕ+ => f n := (int_nat_sum f hf2).subtype _
      apply Summable.congr hs
      intro b; simp; congr; simp
    rw [Summable.hasSum_iff hf3]
    congr
    funext
    simp
    congr
    norm_cast
    simp
  have hneg : HasSum (fun n : ℕ => f (-n.succ)) (∑' n : ℕ+, f n) := by
    have h1 : (fun n : ℕ => f (-↑n.succ)) = fun n : ℕ => f ↑n.succ := by
      funext n
      exact (hf _).symm
    rw [h1]
    convert hpos using 2 with n
    push_cast
    ring
  have := (HasSum.pos_add_zero_add_neg hpos hneg).tsum_eq
  rw [this]
  ring

lemma neg_div_neg_aux (a b : ℂ) : -a/b = a / -b := by ring


theorem summable_diff (z : ℍ) (d : ℤ) :
    Summable fun m : ℕ+ ↦ 1 / (-(d : ℂ) / ↑z - ↑↑m) + 1 / (-↑d / ↑z + ↑↑m) := by
  by_cases hd : d = 0
  · rw [hd]
    simp only [Int.cast_zero, neg_zero, zero_div, zero_sub, one_div, zero_add]
    conv =>
      enter [1]
      ext m
      ring_nf
    apply summable_zero
  by_cases hd2 : 0 < d
  · have := lhs_summable ⟨ -d / z, by simpa using pos_nat_div_upper d hd2 z⟩
    apply this.congr
    intro b
    simp
  let D := (-d).natAbs
  have hd : 0 < D := by aesop
  have hd22 : (D : ℂ) = -d := by
    simp only [Int.natAbs_neg, D]
    have : 0 ≤ -d := by linarith
    have := Int.natAbs_of_nonneg this
    norm_cast
    rw [← this, Int.natAbs_neg]
    rfl
  have := lhs_summable ⟨ -D/ z, by simpa using pnat_div_upper ⟨D, hd⟩ z⟩
  rw [← summable_mul_left_iff (a := -1) (by norm_num)]
  simp only [not_lt, one_div, neg_mul, one_mul, neg_add_rev] at *
  rw [hd22] at this
  apply this.congr
  intro b
  field_simp
  congr 1 <;> grind

lemma arg1 (a b c d e f g h : ℂ) : e / f + g / h - a / b - c / d = e / f + g / h + a / -b + c / -d
    := by ring

lemma sum_int_pnat3 (z : ℍ) (d : ℤ) :
  ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d))
      =
  (2 / z) * ∑' m : ℕ+,
    ((1 / (-(d : ℂ)/↑z - m) + 1 / (-d/↑z + m))) := by
  rw [← Summable.tsum_mul_left]
  · congr
    funext m
    have he : ∀ m d : ℂ , ((m : ℂ) * z + d) = z * ((d : ℂ)/z + m) := by
      intro m
      ring_nf
      have : (z : ℂ) ≠ (0 : ℂ) := ne_zero z
      field_simp
      exact fun _ ↦ trivial
    rw [arg1]
    ring_nf
    rw [add_comm]
    have : (z : ℂ) ≠ (0 : ℂ) := ne_zero z
    field_simp
  · apply summable_diff

lemma pow_max (x y : ℕ) : (max x y)^2 = max (x^2) (y ^ 2) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (Nat.pow_le_pow_left h 2)]
  · rw [max_eq_left h, max_eq_left (Nat.pow_le_pow_left h 2)]

theorem extracted_abs_norm_summable (z : ℍ) (i : ℤ) :
  Summable fun m ↦ 1 / (r z ^ 2 * 2⁻¹ * ‖![m, i]‖ ^ 2) := by
  have hS : Summable fun m : ℤ => 1 / (r z ^ 2 * 2⁻¹ * m ^ 2) := by
    simp only [one_div, mul_inv_rev, inv_inv]
    apply Summable.mul_right
    norm_cast
    have := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    simpa only [Int.cast_pow, one_div] using this
  apply hS.of_norm_bounded_eventually
  rw [Filter.eventually_iff_exists_mem]
  use (Finset.Icc (-|i|) (|i|))ᶜ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mem_cofinite, compl_compl,
    mem_compl_iff, one_div, mul_inv_rev, norm_mul, norm_inv, norm_pow]
  simp only [Finset.coe_Icc, Real.norm_ofNat, inv_inv,
    Real.norm_eq_abs, _root_.sq_abs]
  refine ⟨finite_Icc .., ?_⟩
  intro y hy
  apply le_of_eq
  simp only [mul_eq_mul_right_iff, inv_inj, mul_eq_zero, OfNat.ofNat_ne_zero,
    inv_eq_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or]
  left
  simp only [norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
  have hg : ((y.natAbs : ℝ) ⊔ ↑i.natAbs) ^ 2 = y.natAbs ^ 2 ⊔ i.natAbs ^ 2 := by
    zify
    norm_cast
    rw [pow_max]
  have hg2 : y.natAbs ^ 2 ⊔ i.natAbs ^ 2 = y.natAbs ^ 2:= by
    simp only [sup_eq_left]
    have hii : i^2 ≤ y^2 := by
      rw [@sq_le_sq]
      simp only [mem_Icc, not_and, not_le] at hy
      rw [@le_abs']
      by_cases hh : -|i| ≤ y
      · have hhy := hy hh
        right
        exact hhy.le
      simp only [not_le] at hh
      left
      exact hh.le
    zify
    aesop
  aesop


private lemma aux (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a⁻¹ ≤ c * b⁻¹ ↔ b ≤ c * a :=
    by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [inv_eq_one_div] at h
    rw [mul_one_div, le_div_comm₀ _ hb] at h
    · simp only [one_div, div_inv_eq_mul] at h
      exact h
    simp only [one_div, inv_pos]
    exact ha
  · simp_rw [inv_eq_one_div]
    rw [← div_le_comm₀ _ ha]
    · simp only [one_div, mul_inv_rev, inv_inv]
      rw [propext (mul_inv_le_iff₀ hc), mul_comm]
      exact h
    simp only [one_div]
    apply mul_pos hc (inv_pos.mpr hb)

lemma summable_hammerTime_nat {α : Type} [NormedField α] [CompleteSpace α] (f : ℕ → α) (a : ℝ) (hab
  : 1 < a)
    (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ (a : ℝ))⁻¹) :
    Summable fun n => (f n)⁻¹ := by
  apply summable_of_isBigO _ hf
  have := Real.summable_nat_rpow_inv.mpr hab
  apply this.congr
  intro b
  simp

theorem summable_diff_denom (z : ℍ) (i : ℤ) :
  Summable fun (m : ℤ) ↦ ((m : ℂ) * ↑z + ↑i + 1)⁻¹ * ((m : ℂ) * ↑z + ↑i)⁻¹ := by
  conv =>
    enter [1]
    ext m
    rw [← mul_inv]
  apply summable_inv_of_isBigO_rpow_inv one_lt_two
  have h1 := linear_bigO' (i+1) z
  have h2 := linear_bigO' i z
  have h3 := h2.mul h1
  apply h3.congr
  · intro n
    rw [mul_comm]
    simp
    ring
  · intro n
    norm_cast
    rw [pow_two]
    rw [← mul_inv]
    simp

lemma summable_pain (z : ℍ) (i : ℤ) :
  Summable (fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z + ↑i) - 1 / (↑m * ↑z + ↑i + 1)) := by
  rw [← Finset.summable_compl_iff (s := {0})]
  have h1 : (fun m : { x // x ∉ ({0} : Finset ℤ) } ↦ 1 / ((m : ℂ) * ↑z + ↑i) - 1 / (↑m * ↑z + ↑i +
    1)) =
    (fun m : { x // x ∉ ({0} : Finset ℤ) } ↦ 1 / (((m.1 : ℂ) * ↑z + ↑i)*((m : ℂ) * ↑z + ↑i + 1)))
    := by
    funext m
    rw [div_sub_div]
    · simp only [one_mul, mul_one, add_sub_cancel_left, one_div, mul_inv_rev]
    · have := linear_ne_zero (cd := ![m, i]) z ?_
      · simpa using this
      aesop
    have h2 := linear_ne_zero (cd := ![m, i + 1]) z ?_
    · simp only [Fin.isValue, Matrix.cons_val_zero, ofReal_intCast, Matrix.cons_val_one,
        ofReal_add, ofReal_one, ne_eq] at h2
      rw [add_assoc]
      exact h2
    aesop
  rw [h1]
  simp only [one_div, mul_inv_rev]
  have : Summable fun (m : ℤ) ↦ (↑(m : ℂ) * (z : ℂ) + ↑i + 1)⁻¹ * (↑(m : ℂ) * (z : ℂ) + ↑i)⁻¹ := by
    apply summable_diff_denom
  rw [← Finset.summable_compl_iff (s := {0})] at this
  apply this


theorem vector_norm_bound (b : Fin 2 → ℤ) (hb : b ≠ 0) (HB1 : b ≠ ![0, -1]) :
    ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) ≤ 2 * ‖b‖ ^ (-3 : ℝ) := by
  rw [show (-3 : ℝ) = -1 -2 by norm_num]
  have ht : b = ![b 0, b 1] := by
    ext i
    fin_cases i <;> rfl
  nth_rw 3 [Real.rpow_of_add_eq (y := -1) (z := -2) (by apply norm_nonneg) (by norm_num)
    (by norm_num)]
  rw [← mul_assoc]
  apply mul_le_mul
  · simp_rw [Real.rpow_neg_one]
    rw [aux]
    · simp only [norm_eq_max_natAbs, Nat.cast_max, Nat.succ_eq_add_one, Nat.reduceAdd,
        Matrix.cons_val_zero, Matrix.cons_val_one, max_le_iff]
      have : 2 * max ↑(b 0).natAbs ↑(b 1 + 1).natAbs = max (2*(b 0)).natAbs (2*(b 1 + 1)).natAbs :=
        by
        simp_rw [Int.natAbs_mul]
        exact (Nat.mul_max_mul_left 2 (b 0).natAbs (b 1 + 1).natAbs).symm
      refine ⟨?_ , ?_⟩
      · norm_cast
        simp only [this, Fin.isValue, le_max_iff]
        left
        simp only [Int.natAbs_mul, Int.reduceAbs]
        apply Nat.le_mul_of_pos_left _ Nat.zero_lt_two
      norm_cast
      rcases eq_or_ne (b 1) (-1) with hr | hr
      · simp only [this, le_max_iff]
        left
        simp only [hr, Int.reduceNeg, IsUnit.neg_iff, isUnit_one, Int.natAbs_of_isUnit, Fin.isValue,
          Int.natAbs_mul, Int.reduceAbs, Fin.isValue]
        have hb0 : b 0 ≠ 0 := by
          rw [ht, hr] at HB1
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Int.reduceNeg, ne_eq] at HB1
          by_contra hh
          simp only [hh, Int.reduceNeg, not_true_eq_false] at HB1
        omega
      · rw [this]
        simp only [Fin.isValue, le_max_iff]
        right
        simp only [Int.natAbs_mul, Int.reduceAbs]
        omega
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, norm_pos_iff, ne_eq,
      Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, not_and]
      intro h
      by_contra H
      rw [@add_eq_zero_iff_eq_neg] at H
      rw [ht, h, H] at HB1
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, ne_eq, not_true_eq_false] at HB1
    · exact norm_pos_iff.mpr hb
    · simp only [Nat.ofNat_pos]
  · rfl
  · apply Real.rpow_nonneg
    apply norm_nonneg
  · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    apply Real.rpow_nonneg
    apply norm_nonneg


lemma G_2_alt_summable (z : ℍ) : Summable fun (m : Fin 2 → ℤ) =>
    1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) := by
  have hk' : 2 < (3 : ℝ) := by linarith
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-3 : ℝ) * 2).of_norm_bounded_eventually
  rw [Filter.eventually_iff_exists_mem]
  use { ![0,0], ![0,-1]}ᶜ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, mem_cofinite, compl_compl,
    finite_singleton, Finite.insert, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
    Fin.isValue, one_div, mul_inv_rev, norm_mul, norm_inv, norm_pow, and_imp, true_and]
  intro b HB1 HB2
  have hk0 : 0 ≤ (2 : ℝ) := by norm_num
  have hk0' : 0 ≤ (1 : ℝ) := by norm_num
  have p1 := summand_bound z hk0 b
  let b' : Fin 2 → ℤ := ![b 0, b 1 + 1]
  have p2 := summand_bound z hk0' b'
  simp only [Nat.ofNat_nonneg, zero_le_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_add, Int.cast_one, ge_iff_le, b'] at *
  have := mul_le_mul p2 p1 ?_ ?_
  · have hpow : ‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1))‖ ^ (-2 : ℝ) =
      (‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1))‖ ^ 2)⁻¹ :=
      by norm_cast
    have hpow2 : ‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1)) + 1‖ ^ (-1 : ℝ) =
      (‖(↑((b 0) : ℂ) * (z : ℂ) + ↑(b 1)) + 1‖)⁻¹ :=
      by apply Real.rpow_neg_one
    rw [← hpow, ← hpow2]
    rw [← add_assoc] at this
    apply le_trans this
    have : r z ^ (-1 : ℝ) * ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * (r z ^ (-2 : ℝ) * ‖b‖ ^ (-2 : ℝ)) =
      r z ^ (-3 : ℝ) * ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) := by
      rw [show (-3 : ℝ) = -2 -1 by norm_num]
      nth_rw 5 [Real.rpow_of_add_eq (y := -2) (z := -1)]
      · ring
      · exact (r_pos z).le
      · norm_cast
      norm_cast
    rw [this]
    have hg : r z ^ (-3 : ℝ) * 2 * ‖b‖ ^ (-3 : ℝ) = r z ^ (-3 : ℝ) * (2 * ‖b‖ ^ (-3 : ℝ)) := by ring
    rw [hg, mul_assoc]
    apply mul_le_mul
    · rfl
    · apply vector_norm_bound
      · convert HB1
        apply symm
        simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self]
      simpa using HB2
    · positivity
    · have := (r_pos z).le
      positivity
  · apply Real.rpow_nonneg
    apply norm_nonneg
  · exact
    mul_nonneg (Real.rpow_nonneg (LT.lt.le (r_pos z)) (-1))
      (Real.rpow_nonneg (norm_nonneg ![b 0, b 1 + 1]) (-1))


/-- A correction term equal to `1` at `(0, 0)`, `2` at `(0, -1)`, and `0` elsewhere. -/
noncomputable def δ (a b : ℤ) : ℂ := if a = 0 ∧ b = 0 then 1 else if a = 0 ∧ b = -1 then 2 else 0

@[simp]
lemma δ_eq : δ 0 0 = 1 := by simp [δ]

@[simp]
lemma δ_eq2 : δ 0 (-1) = 2 := by simp [δ]

lemma δ_neq (a b : ℤ) (h : a ≠ 0) : δ a b = 0 := by simp [δ, h]

lemma G_2_alt_summable_δ (z : ℍ) : Summable fun (m : Fin 2 → ℤ) =>
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)):= by
    have this := G_2_alt_summable z
    rw [← Finset.summable_compl_iff (s := ({ ![0,0], ![0,-1]} : Finset (Fin 2 → ℤ)))] at this ⊢
    simp only [Fin.isValue, one_div, mul_inv_rev] at *
    apply this.congr
    intro b
    simp only [Fin.isValue, left_eq_add] at *
    have hb1 : b.1 ≠ ![0, 0] := by aesop
    have hb2 : b.1 ≠ ![0, -1] := by aesop
    simp only [δ, Fin.isValue, Int.reduceNeg]
    split_ifs with h1 h2
    · exfalso
      refine hb1 ?_
      funext i
      fin_cases i <;> simp [h1.1, h1.2]
    · exfalso
      refine hb2 ?_
      funext i
      fin_cases i <;> simp [h2.1, h2.2]
    rfl

private lemma G_2_alt_summable_δ_prod (z : ℍ) : Summable fun m : ℤ × ℤ ↦
    ((m.1 : ℂ) * ↑z + ↑m.2 + 1)⁻¹ * (((m.1 : ℂ) * ↑z + ↑m.2) ^ 2)⁻¹ + δ m.1 m.2 := by
  have := G_2_alt_summable_δ z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  exact this

theorem G2_prod_summable1 (z : ℍ) (b : ℤ) :
    Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ := by
  have := G_2_alt_summable z
  simp only [Fin.isValue, one_div, mul_inv_rev] at this
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at this
  apply this.prod_factor b

theorem G2_prod_summable1_δ (z : ℍ) (b : ℤ) :
    Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ + δ b c :=
  (G_2_alt_summable_δ_prod z).prod_factor b



lemma G2_alt_indexing_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)) =
    ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ)* z + n)^2 * (m * z + n +1)) + (δ m n)) := by
  rw [← (finTwoArrowEquiv _).symm.tsum_eq]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_div, mul_inv_rev]
  refine Summable.tsum_prod' (G_2_alt_summable_δ_prod z) ?_
  intro b
  simp only
  apply (G_2_alt_summable_δ_prod z).prod_factor




lemma G2_alt_indexing2_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)) =
    ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  have := G_2_alt_summable_δ_prod z
  rw [Summable.tsum_comm']
  · rw [G2_alt_indexing_δ]
  · apply this.congr
    intro b
    simp
    rfl
  · intro b
    simp only [one_div, mul_inv_rev]
    apply this.prod_factor
  intro c
  simp only [one_div, mul_inv_rev]
  have H := (G_2_alt_summable_δ z)
  rw [← swapEquiv.summable_iff] at H
  rw [← (finTwoArrowEquiv _).symm.summable_iff] at H
  simp [Fin.isValue, one_div, mul_inv_rev, swapEquiv, Equiv.coe_fn_mk,
    finTwoArrowEquiv_symm_apply] at H
  have := H.prod_factor c
  simp only [Fin.isValue, comp_apply, swap_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero] at this
  apply this




theorem summable_1 (k : ℕ) (z : ℍ) (hk : 1 ≤ k) :
    Summable fun (b : ℕ) ↦ (((z : ℂ) - ↑↑b) ^ (k + 1))⁻¹ := by
  have := summable_hammerTime_nat (fun n : ℕ => (((z : ℂ) - n) ^ (k + 1))) (k+1)
      (by norm_cast; omega) ?_
  · apply this
  norm_cast
  simp_rw [← inv_pow]
  have : (fun (n : ℕ) ↦ (↑(n ^ (k + 1)) : ℝ)⁻¹) = fun (n : ℕ) ↦ (↑(n : ℝ)⁻¹) ^ (k + 1) := by simp
  conv =>
    enter [3]
    rw [this]
  apply Asymptotics.IsBigO.pow
  have hl := linear_bigO_nat (-1) z
  conv =>
    enter [2]
    intro x
    rw [sub_eq_add_neg]
  apply Asymptotics.IsBigO.of_abs_right
  simp only [Nat.cast_pow, inv_pow, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    Nat.abs_cast, Asymptotics.isBigO_abs_right] at *
  have hl2 := Asymptotics.IsBigO.neg_left hl
  apply hl2.congr_left
  intro n
  rw [@neg_inv]
  congr
  ring

theorem summable_2 (k : ℕ) (z : ℍ) (hk : 1 ≤ k) :
    Summable fun (b : ℕ) ↦ (((z : ℂ) + ↑↑b) ^ (k + 1))⁻¹ := by
  have := summable_hammerTime_nat (fun n : ℕ => (((z : ℂ) + n) ^ (k + 1))) (k+1)
      (by norm_cast; omega) ?_
  · apply this
  norm_cast
  simp_rw [← inv_pow]
  have : (fun (n : ℕ) ↦ (↑(n ^ (k + 1)) : ℝ)⁻¹) = fun (n : ℕ) ↦ (↑(n : ℝ)⁻¹) ^ (k + 1) := by simp
  conv =>
    enter [3]
    rw [this]
  apply Asymptotics.IsBigO.pow
  have hl := linear_bigO_nat 1 z
  apply Asymptotics.IsBigO.of_abs_right
  simp only [Nat.cast_pow, inv_pow, Int.cast_one, one_mul, Nat.abs_cast,
    Asymptotics.isBigO_abs_right] at *
  exact hl



theorem summable_3 (m : ℕ) (y : {z : ℂ | 0 < z.im}) :
    Summable fun n : ℕ+ =>
      (-1 : ℂ) ^ m * ↑m ! * (1 / (y - ↑n) ^ (m + 1)) + (-1) ^ m * ↑m ! * (1 / (y + ↑n) ^ (m + 1)) :=
  by
  by_cases hm : m = 0
  · simp_rw [hm]
    simp
    have := lhs_summable (⟨y, y.2⟩ : ℍ)
    simpa using this
  have hm2 : 2 ≤ m + 1 := by
    have : 1 ≤ m := by apply Nat.one_le_iff_ne_zero.mpr hm;
    linarith
  simp_rw [← mul_add]
  rw [summable_mul_left_iff]
  · apply Summable.add
    · have h0 := summable_1 m (⟨y, y.2⟩ : ℍ) (by linarith)
      simp only [Nat.reduceLeDiff, mem_setOf_eq, one_div] at *
      apply h0.subtype
    have h1 := summable_2 m (⟨y, y.2⟩ : ℍ) (by linarith)
    simp only [Nat.reduceLeDiff, mem_setOf_eq, one_div] at *
    apply h1.subtype
  simp [Nat.factorial_ne_zero]

theorem summable_iter_derv' (k : ℕ) (y : ℍ') :
    Summable fun n : ℕ => (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * y) :=
  by
  apply Summable.of_norm
  simp only [mem_setOf_eq, Complex.norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
    norm_I, mul_one]
  simp_rw [mul_pow, mul_assoc]
  apply Summable.mul_left
  apply Summable.mul_left
  conv =>
    enter [1]
    ext n
    rw [← norm_pow, ← norm_mul]
    rw [show cexp (2 * (↑π * (Complex.I * (↑n * ↑y)))) = cexp (2 * (↑π * (Complex.I * (↑y)))) ^ n by
      rw [← Complex.exp_nsmul]
      congr
      ring]
  apply summable_norm_pow_mul_geometric_of_norm_lt_one
  have := exp_upperHalfPlane_lt_one (⟨y, y.2⟩ : ℍ)
  simp only [mem_setOf_eq, gt_iff_lt] at *
  simp_rw [← mul_assoc] at *
  exact this


theorem sigma_eq_sum_div' (k n : ℕ) : sigma k n = ∑ d ∈ Nat.divisors n, (n / d) ^ k := by
  simp only [sigma, ArithmeticFunction.coe_mk]
  rw [← Nat.sum_div_divisors]


theorem a33 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z * c) := by
  apply Summable.of_norm
  conv =>
    enter [1]
    ext a
    rw [show cexp (2 * ↑π * Complex.I * ↑e * z * ↑a) = cexp (2 * ↑π * Complex.I * (↑e)* z) ^ (a : ℕ)
      by rw [← Complex.exp_nsmul]; congr; ring]
  have := summable_norm_pow_mul_geometric_of_norm_lt_one
    (r := cexp (2 * ↑π * Complex.I * (↑e)* z)) k ?_
  · apply this.subtype
  simp only [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, natCast_re,
    natCast_im, coe_re, zero_add, coe_im, zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

lemma hsum (k : ℕ) (z : ℍ) : Summable fun b : ℕ+ => ∑ _ ∈ (b : ℕ).divisors, b ^ k *
    ‖exp (2 * ↑π * Complex.I * ↑z * b)‖ := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hs := summable_norm_iff.mpr (a33 (k+1) 1 z)
    apply Summable.of_nonneg_of_le _ _ hs
    · simp only [Nat.cast_pos, Finset.card_pos, Nat.nonempty_divisors, ne_eq, PNat.ne_zero,
        not_false_eq_true, mul_nonneg_iff_of_pos_left, PNat.pos, pow_pos, norm_nonneg, implies_true]
    intro b
    simp only [PNat.val_ofNat, Nat.cast_one, mul_one, Complex.norm_mul, norm_pow, norm_natCast]
    rw [← mul_assoc]
    gcongr
    rw [pow_add, mul_comm]
    gcongr
    simpa using Nat.card_divisors_le_self (b : ℕ)

theorem summable_auxil_1 (k : ℕ) (z : ℍ) :
  Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦
  ↑(↑(c.snd) : ℕ × ℕ).1 ^ k *
    cexp (2 * ↑π * Complex.I * ↑z * ↑(↑(c.snd) : ℕ × ℕ).1 * ↑↑(↑(c.snd) : ℕ × ℕ).2) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg]
  constructor
  · apply fun n => (hasSum_fintype _).summable
  · simp only [Complex.norm_mul, norm_pow, RCLike.norm_natCast, tsum_fintype, Finset.univ_eq_attach]
    have H (n : ℕ+) := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
      (x.1 : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x.1 * x.2)‖)
    have H2 (n : ℕ+) := Nat.sum_divisorsAntidiagonal ((fun (x : ℕ) => fun (y : ℕ) =>
      (x : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x * y)‖)) (n := n)
    conv =>
      enter [1]
      ext b
      simp
      rw [H b, H2 b]
    have hsum := hsum k z
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro b
      apply Finset.sum_nonneg
      intro i hi
      simp
    · intro b
      apply Finset.sum_le_sum
      intro i hi
      simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at hi
      gcongr
      · apply Nat.le_of_dvd b.2 hi
      apply le_of_eq
      have hni : (i : ℂ) * (b / i : ℕ) = b := by
        norm_cast
        simp only [Finset.sum_const, nsmul_eq_mul] at *
        exact Nat.mul_div_cancel' hi
      rw [mul_assoc, hni]
  · intro i
    simp







lemma sum_range_zero (f : ℤ → ℂ) (n : ℕ) : ∑ m ∈ Finset.range (n+1), f m = f 0 +
  ∑ m ∈ Finset.range n, f (m+1) := by rw [Finset.sum_range_succ', add_comm]; simp



theorem exp_series_ite_deriv_uexp2 (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z))
    {z : ℂ | 0 < z.im} x =
    ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s))
    {z : ℂ | 0 < z.im} x := by
  induction k generalizing x with
  | zero => simp only [iteratedDerivWithin_zero]
  | succ k IH =>
    rw [iteratedDerivWithin_succ]
    have HH :
      derivWithin (iteratedDerivWithin k (fun z => ∑' n : ℕ,
                                            Complex.exp (2 * ↑π * Complex.I * n * z))
        {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im}
          x =
        derivWithin
          (fun z =>
            ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s))
                                          {z : ℂ | 0 < z.im} z)
          {z : ℂ | 0 < z.im} x := by
      apply derivWithin_congr
      · intro y hy
        apply IH ⟨y, hy⟩
      apply IH x
    simp_rw [HH]
    rw [derivWithin_tsum_fun']
    · apply tsum_congr
      intro b
      rw [iteratedDerivWithin_succ]
    · exact isOpen_lt (by fun_prop) (by fun_prop)
    · exact x.2
    · intro y hy
      apply Summable.congr (summable_iter_derv' k ⟨y, hy⟩)
      intro b
      apply symm
      apply exp_iter_deriv_within k b hy
    · intro K hK1 hK2
      let K2 := Set.image (Set.inclusion hK1) univ
      have hKK2 : IsCompact (Set.image (inclusion hK1) univ) := by
        apply IsCompact.image_of_continuousOn
        · exact isCompact_iff_isCompact_univ.mp hK2
        · exact continuous_inclusion hK1 |>.continuousOn
      apply iter_deriv_comp_bound2 K hK1 hK2 k
    apply der_iter_eq_der_aux2

theorem exp_series_ite_deriv_uexp'' (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z))
    {z : ℂ | 0 < z.im} x =
    ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * x) := by
  rw [exp_series_ite_deriv_uexp2 k x]
  apply tsum_congr
  intro b
  apply exp_iter_deriv_within k b x.2

theorem exp_series_ite_deriv_uexp''' (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) ℍ')
      (fun x : ℂ => ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n *
        x)) ℍ' := by
  intro x hx
  apply exp_series_ite_deriv_uexp'' k ⟨x, hx⟩


theorem tsum_uexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) ℍ' := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m _
  apply DifferentiableOn.congr _ (exp_series_ite_deriv_uexp''' m)
  intro x hx
  apply HasDerivWithinAt.differentiableWithinAt
  refine hasDerivWithinAt_tsum_fun _ upper_half_plane_isOpen _ hx ?_ ?_ (by fun_prop)
  · intro y hy
    apply summable_iter_derv' m ⟨y, hy⟩
  intro K hK1 hK2
  obtain ⟨u, hu, hu2⟩ := iter_deriv_comp_bound3 K hK1 hK2 (m + 1)
  refine ⟨u, hu, ?_⟩
  intro n r
  have HU2 := hu2 n r
  simp only [ge_iff_le]
  apply le_trans _ HU2
  apply le_of_eq
  norm_cast
  simp only [ofReal_mul, ofReal_ofNat]
  rw [derivWithin_fun_mul (by fun_prop) (by fun_prop),
    derivWithin_cexp (by fun_prop) (upper_half_plane_isOpen.uniqueDiffOn _ <| by aesop),
    derivWithin_const_mul _ (by fun_prop)]
  simp only [derivWithin_fun_const, Pi.zero_apply, zero_mul, zero_add, Complex.norm_mul, norm_pow,
    norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one, RCLike.norm_natCast]
  have hr : derivWithin (fun y ↦ y) ℍ' ↑r = 1 := by
    apply derivWithin_id
    apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
    aesop
  rw [hr]
  simp
  ring

theorem iter_der_within_add (k : ℕ+) (x : {z : ℂ | 0 < z.im}) :
    iteratedDerivWithin k
        (fun z => ↑π * Complex.I - (2 * ↑π * Complex.I) •
        ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * n * z)) {z : ℂ | 0 < z.im} x =
      -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) *
      Complex.exp (2 * ↑π * Complex.I * n * x) := by
  rw [iteratedDerivWithin_const_sub (PNat.pos k)]
  simp only [smul_eq_mul, mem_setOf_eq, neg_mul]
  rw [iteratedDerivWithin_fun_neg,
    iteratedDerivWithin_const_mul x.2 <| IsOpen.uniqueDiffOn upper_half_plane_isOpen]
  · congr
    have := exp_series_ite_deriv_uexp2 k x
    rw [this]
    apply tsum_congr
    intro b
    have := exp_iter_deriv_within k b x.2
    simpa using this
  apply tsum_uexp_contDiffOn k
  exact x.2

theorem iter_exp_eqOn (k : ℕ+) :
    EqOn
      (iteratedDerivWithin k
        (fun z => ↑π * Complex.I - (2 * ↑π * Complex.I) • ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I
          * n * z)) {z : ℂ | 0 < z.im})
      (fun x : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π *
          Complex.I * n * x))
      {z : ℂ | 0 < z.im} := by
  intro z hz
  apply iter_der_within_add k ⟨z, hz⟩

theorem summable_iter_aut (k : ℕ) (z : ℍ) :
    Summable fun n : ℕ+ => iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n))
      {z : ℂ | 0 < z.im} z := by
  have := fun d : ℕ+ => iter_div_aut_add d k z.2
  simp only [Int.cast_natCast, one_div, Pi.add_apply] at *
  have ht := (summable_congr (L := SummationFilter.unconditional _) this).2 ?_
  · norm_cast at *
  by_cases hk : 1 ≤ k
  · conv =>
      enter [1]
      ext b
      rw [← mul_add]
    rw [summable_mul_left_iff]
    · exact .add ((summable_1 k z hk).subtype _) ((summable_2 k z hk).subtype _)
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
      Nat.cast_eq_zero, false_or]
    exact Nat.factorial_ne_zero k
  · simp only [not_le, Nat.lt_one_iff] at hk
    simp_rw [hk]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add, pow_one, one_mul]
    simpa using lhs_summable z




lemma sub_bound (s : ℍ) (A B : ℝ) (hB : 0 < B) (hs : s ∈ verticalStrip A B) (k : ℕ)
    (n : ℕ+) :
    ‖((-1 : ℂ) ^ (k + 1) * (k + 1)! * (1 / (s - n) ^ (k + 2)))‖ ≤
    ‖((k + 1)! / r ⟨⟨A, B⟩, by simp [hB]⟩ ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹‖ := by
  simp only [one_div, norm_pow, norm_neg, one_mem, CStarRing.norm_of_mem_unitary, one_pow,
    RCLike.norm_natCast, one_mul, norm_inv, norm_mul, norm_div, Real.norm_eq_abs, norm_zpow]
  rw [div_eq_mul_inv, mul_assoc]
  gcongr
  have := summand_bound_of_mem_verticalStrip (k := (k + 2)) (by norm_cast; omega) ![1,-n] hB hs
  simp only [Fin.isValue, Matrix.cons_val_zero, Int.cast_one, one_mul, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_natCast, neg_add_rev, ge_iff_le] at *
  simp_rw [← zpow_natCast, ← zpow_neg]
  have hnorm : ‖(![1, -↑↑n] : Fin 2 → ℤ)‖ = (n : ℝ) := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp only [Fin.isValue, Matrix.cons_val_zero, isUnit_one, Int.natAbs_of_isUnit,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.natAbs_neg, Int.natAbs_natCast,
      Nat.cast_max, Nat.cast_one]
    rw [max_eq_right (by exact_mod_cast n.2)]
  have habs : |r (⟨⟨A, B⟩, hB⟩ : ℍ)| = r ⟨⟨A, B⟩, hB⟩ :=
    abs_of_nonneg (EisensteinSeries.r_pos _).le
  rw [hnorm] at this
  have hcast : (-(2 : ℝ) + -↑k) = ((-2 + -↑k : ℤ) : ℝ) := by push_cast; ring
  rw [hcast] at this
  simp only [Real.rpow_intCast] at this
  have hexp : (-(↑(k + 2) : ℤ)) = -2 + -↑k := by push_cast; ring
  have hexp2 : (-((k : ℤ) + 2)) = -2 + -↑k := by ring
  rw [show (s : ℂ) - n = s + -↑↑n by ring, habs, hexp, hexp2]
  exact this


lemma add_bound (s : ℍ) (A B : ℝ) (hB : 0 < B) (hs : s ∈ verticalStrip A B) (k : ℕ)
    (n : ℕ+) :
    ‖((-1 : ℂ) ^ (k + 1) * (k + 1)! * (1 / (s + n) ^ (k + 2)))‖ ≤
    ‖((k + 1)! / r ⟨⟨A, B⟩, by simp [hB]⟩ ^ (k + 2)) * ((n : ℝ) ^ ((k : ℤ) +2))⁻¹‖ := by
  simp only [one_div, norm_pow, norm_neg, one_mem, CStarRing.norm_of_mem_unitary, one_pow,
    RCLike.norm_natCast, one_mul, norm_inv, norm_mul, norm_div, Real.norm_eq_abs, norm_zpow]
  rw [div_eq_mul_inv, mul_assoc]
  gcongr
  have := summand_bound_of_mem_verticalStrip (k := (k + 2)) (by norm_cast; omega) ![1,n] hB hs
  simp only [Fin.isValue, Matrix.cons_val_zero, Int.cast_one, one_mul, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_natCast, neg_add_rev, ge_iff_le] at *
  simp_rw [← zpow_natCast, ← zpow_neg]
  have hnorm : ‖(![1, ↑↑n] : Fin 2 → ℤ)‖ = (n : ℝ) := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp only [Fin.isValue, Matrix.cons_val_zero, isUnit_one, Int.natAbs_of_isUnit,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.natAbs_natCast,
      Nat.cast_max, Nat.cast_one]
    rw [max_eq_right (by exact_mod_cast n.2)]
  have habs : |r (⟨⟨A, B⟩, hB⟩ : ℍ)| = r ⟨⟨A, B⟩, hB⟩ :=
    abs_of_nonneg (EisensteinSeries.r_pos _).le
  rw [hnorm] at this
  have hcast : (-(2 : ℝ) + -↑k) = ((-2 + -↑k : ℤ) : ℝ) := by push_cast; ring
  rw [hcast] at this
  simp only [Real.rpow_intCast] at this
  have hexp : (-(↑(k + 2) : ℤ)) = -2 + -↑k := by push_cast; ring
  have hexp2 : (-((k : ℤ) + 2)) = -2 + -↑k := by ring
  rw [show (s : ℂ) + n = s + ↑↑n by ring, habs, hexp, hexp2]
  exact this

theorem aut_bound_on_comp (K : Set ℍ) (hk2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ+ → ℝ,
      Summable u ∧
        ∀ (n : ℕ+) (s : K),
        ‖(derivWithin (fun z : ℂ =>
        iteratedDerivWithin k (fun z : ℂ => (z - (n : ℂ))⁻¹ + (z + n)⁻¹) {z : ℂ | 0 < z.im} z)
        {z : ℂ | 0 < z.im} s)‖ ≤
            u n := by
  by_cases h1 : Set.Nonempty K
  · have H := UpperHalfPlane.subset_verticalStrip_of_isCompact hk2
    obtain ⟨A, B, hB, hAB⟩ := H
    let zAB : ℍ := ⟨⟨A, B⟩, by simp [hB]⟩
    refine ⟨fun a : ℕ+ => 2 * ‖((k + 1)! / r (zAB) ^ (k + 2)) * ((a : ℝ) ^ ((k : ℤ) +2))⁻¹‖,
      ?_, ?_⟩
    conv =>
      enter [1]
      ext a
      rw [norm_mul]
      rw [← mul_assoc]
    · apply Summable.mul_left
      simp only [norm_inv, norm_zpow, RCLike.norm_natCast]
      have : Summable fun (i : ℕ) ↦ ((i : ℝ) ^ ((k : ℤ) + 2))⁻¹ := by
        have := (Real.summable_nat_rpow_inv (p := k + 2)).mpr (by linarith)
        apply this.congr
        intro n
        norm_cast
      apply this.subtype
    intro n s
    rw [← iteratedDerivWithin_succ]
    have HT := iter_div_aut_add n (k + 1) s.1.2
    simp only [Int.cast_natCast, one_div, Pi.add_apply] at HT
    rw [HT]
    apply le_trans (norm_add_le _ _)
    simp_rw [mul_assoc]
    rw [two_mul]
    apply add_le_add
    · simpa using sub_bound s.1 A B hB (hAB s.2) k n
    · simpa using add_bound s.1 A B hB (hAB s.2) k n
  refine ⟨fun _ => 0, summable_zero, ?_⟩
  intro n
  rw [not_nonempty_iff_eq_empty] at h1
  intro r
  exfalso
  have hr := r.2
  simp_rw [h1] at hr
  simp at hr

theorem diff_on_aux (k : ℕ) (n : ℕ+) :
    DifferentiableOn ℂ
      ((fun t : ℂ => (-1 : ℂ) ^ k * k ! * (1 / (t - n) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + n) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  have this (n : ℕ+) (z : ℂ) (hz : 0 < z.im) : (z + n) ^ (k + 1) ≠ 0 := by
    simpa using upper_ne_int ⟨z, hz⟩ n
  have this (n : ℕ+) (z : ℂ) (hz : 0 < z.im) : (z - n) ^ (k + 1) ≠ 0 := by
    simpa [sub_eq_add_neg] using upper_ne_int ⟨z, hz⟩ (-n)
  fun_prop (disch := aesop)

theorem diff_at_aux (s : {z : ℂ | 0 < z.im}) (k : ℕ) (n : ℕ+) :
    DifferentiableAt ℂ
      (fun z : ℂ => iteratedDerivWithin k (fun z : ℂ => (z - ↑n)⁻¹ + (z + ↑n)⁻¹) {z : ℂ | 0 < z.im}
        z)
      ↑s := by
  have := iter_div_aut_add n k
  apply DifferentiableOn.differentiableAt
  · apply DifferentiableOn.congr (diff_on_aux k n)
    intro r hr
    have ht := this hr
    simp only [Int.cast_natCast, one_div, mem_setOf_eq, Pi.add_apply] at *
    apply ht
  exact (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simp)

theorem aut_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ) :
    iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} x
      =
      ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im} x
        := by
  induction k generalizing x with
  | zero => simp only [iteratedDerivWithin_zero]
  | succ k IH =>
    rw [iteratedDerivWithin_succ]
    have HH :
      derivWithin (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n)))
        {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} x =
        derivWithin
          (fun z => ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n))
                                                     {z : ℂ | 0 < z.im} z)
          {z : ℂ | 0 < z.im}
          x := by
      apply derivWithin_congr
      · intro y hy
        apply IH ⟨y, hy⟩
      apply IH x
    simp_rw [HH]
    simp only [one_div]
    rw [derivWithin_tsum_fun']
    · apply tsum_congr
      intro b
      rw [iteratedDerivWithin_succ]
    · refine isOpen_lt ?_ ?_
      · fun_prop
      · fun_prop
    · simpa using x.2
    · intro y hy
      simpa using summable_iter_aut k ⟨y, hy⟩
    · intro K hK hK2
      let toUpper : K → ℍ := fun z => ⟨z, by simpa using hK z.2⟩
      let K2 : Set ℍ := Set.image toUpper univ
      have htoUpper : Continuous toUpper := by
        simpa [toUpper] using
          (Continuous.upperHalfPlaneMk (f := fun z : K => (z : ℂ)) continuous_subtype_val
            (fun z => by simpa using hK z.2))
      have hKK2 : IsCompact K2 := by
        have hK2' : IsCompact (Set.univ : Set K) := isCompact_iff_isCompact_univ.mp hK2
        simpa [K2, toUpper] using hK2'.image htoUpper
      have := aut_bound_on_comp K2 hKK2 k
      obtain ⟨u, hu1, hu2⟩ := this
      refine ⟨u, hu1, ?_⟩
      intro n s
      have hsK2 : toUpper s ∈ K2 := by refine ⟨s, by simp, rfl⟩
      exact hu2 n ⟨toUpper s, hsK2⟩
    intro n r
    apply diff_at_aux

theorem tsum_ider_der_eq (k : ℕ) (x : {z : ℂ | 0 < z.im}) :
    ∑' n : ℕ+, iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z : ℂ | 0 < z.im} x =
      ∑' n : ℕ+,
        ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) + (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))) :=
  by
  apply tsum_congr
  intro b
  have h2 := iter_div_aut_add b k x.2
  simpa using h2



theorem auxp_series_ite_deriv_uexp''' (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n)))
    {z : ℂ | 0 < z.im})
    (fun x : ℂ =>
      ∑' n : ℕ+,
        ((-1 : ℂ) ^ k * k ! * (1 / (x - n) ^ (k + 1)) + (-1) ^ k * k ! * (1 / (x + n) ^ (k + 1))))
    {z : ℂ | 0 < z.im} := by
  intro x hx
  have := aut_series_ite_deriv_uexp2 k ⟨x, hx⟩
  simp only [one_div] at *
  rw [this]
  have h2 := tsum_ider_der_eq k ⟨x, hx⟩
  simpa using h2



theorem tsum_aexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im} := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm
  have h1 := auxp_series_ite_deriv_uexp''' m
  apply DifferentiableOn.congr _ h1
  intro x hx
  apply HasDerivWithinAt.differentiableWithinAt
  apply hasDerivWithinAt_tsum_fun _ (isOpen_lt (by fun_prop) (by fun_prop)) _ hx
  · intro y hy
    apply summable_3 m ⟨y, hy⟩
  · intro K hK1 hK2
    let toUpper : K → ℍ := fun z => ⟨z, by simpa using hK1 z.2⟩
    let K2 : Set ℍ := Set.image toUpper univ
    have htoUpper : Continuous toUpper := by
      simpa [toUpper] using
        (Continuous.upperHalfPlaneMk (f := fun z : K => (z : ℂ)) continuous_subtype_val
          (fun z => by simpa using hK1 z.2))
    have hKK2 : IsCompact K2 := by
      have hK2' : IsCompact (Set.univ : Set K) := isCompact_iff_isCompact_univ.mp hK2
      simpa [K2, toUpper] using hK2'.image htoUpper
    have := aut_bound_on_comp K2 hKK2 m
    obtain ⟨u, hu1, hu2⟩ := this
    refine ⟨u, hu1, ?_⟩
    intro n s
    have hsK2 : toUpper s ∈ K2 := by refine ⟨s, by simp, rfl⟩
    have := hu2 n ⟨toUpper s, hsK2⟩
    apply le_trans _ this
    apply le_of_eq
    congr 1
    apply derivWithin_congr
    · have h21 := (iter_div_aut_add n m).symm
      simp only [Nat.cast_le, one_div, mem_setOf_eq, Subtype.forall, Int.cast_natCast] at *
      intro v hv
      have h22 := h21 hv
      simp only [mem_setOf_eq, Pi.add_apply] at *
      rw [← h22]
    have hss : s.1 ∈ {z : ℂ | 0 < z.im} := by simpa using hK1 s.2
    have h21 := (iter_div_aut_add n m).symm hss
    simpa using h21
  intro n r
  have:= (diff_on_aux m n)
  have hN : {z : ℂ | 0 < z.im} ∈ 𝓝 r.1 := by
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt (by fun_prop) (by fun_prop)
    apply r.2
  apply DifferentiableOn.differentiableAt _ hN
  simp only [Nat.cast_le, one_div, mem_setOf_eq] at *
  apply this


theorem aux_iter_der_tsum (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
    iteratedDerivWithin k
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 <
          z.im} x =
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ (k + 1 : ℕ) := by
  rw [iteratedDerivWithin_add ?_ ?_]
  · have h1 := aut_iter_deriv 0 k x.2
    simp only [Int.cast_zero, add_zero, one_div] at *
    rw [h1]
    have := aut_series_ite_deriv_uexp2 k x
    simp only [one_div] at *
    rw [this]
    have h2 := tsum_ider_der_eq k ⟨x, x.2⟩
    simp only [one_div] at h2
    rw [h2, tsum_int_eq_zero_add_tsum_pnat]
    · simp only [Int.cast_zero, add_zero, Int.cast_natCast, Int.cast_neg]
      rw [Summable.tsum_add]
      · rw [tsum_mul_left, tsum_mul_left, mul_add, mul_add]
        conv =>
          enter [2]
          rw [add_assoc]
          conv =>
            enter [2]
            rw [add_comm]
        ring_nf
      · rw [summable_mul_left_iff]
        · apply (summable_1 k x hk).subtype
        · simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
          Nat.cast_eq_zero, false_or]
          exact Nat.factorial_ne_zero k
      · rw [summable_mul_left_iff]
        · apply (summable_2 k x hk).subtype
        · simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
          Nat.cast_eq_zero, false_or]
          exact Nat.factorial_ne_zero k
    · rw [summable_int_iff_summable_nat_and_neg]
      refine ⟨?_, ?_⟩
      · apply (summable_2 k x hk)
      apply (summable_1 k x hk).congr
      intro n
      congr
      simp
      rfl
  · have := (aut_contDiffOn 0 k)
    simp only [Int.cast_zero, sub_zero, one_div] at *
    apply this.contDiffWithinAt
    exact x.2
  · apply tsum_aexp_contDiffOn k
    exact x.2
  · exact x.2
  · refine IsOpen.uniqueDiffOn ?_
    refine isOpen_lt ?_ ?_
    · fun_prop
    · fun_prop

theorem aux_iter_der_tsum_eqOn (k : ℕ) (hk : 2 ≤ k) :
    EqOn (iteratedDerivWithin (k - 1)
    ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))) {z : ℂ | 0 < z.im})
    (fun z : ℂ => (-1) ^ (k - 1) * (k - 1)! * ∑' n : ℤ, 1 / (z + n) ^ (k : ℕ)) {z : ℂ | 0 < z.im}
    := by
  intro z hz
  have hk0 : 1 ≤ k - 1 := le_tsub_of_add_le_left hk
  have := aux_iter_der_tsum (k - 1) hk0 ⟨z, hz⟩
  have hk1 : k - 1 + 1 = k := by
    apply Nat.sub_add_cancel
    linarith
  rw [hk1] at this
  norm_cast at *


theorem pos_sum_eq (k : ℕ) (hk : 0 < k) :
    (fun x : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π *
          Complex.I * n * x)) =
      fun x : ℂ =>
      -(2 * ↑π * Complex.I) * ∑' n : ℕ+, (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π *
        Complex.I * n * x) := by
  ext1 x
  simp only [neg_mul, neg_inj, mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
    ofReal_eq_zero, Real.pi_ne_zero, or_self, I_ne_zero, or_false]
  apply symm
  have := tsum_pNat fun n : ℕ => (2 * ↑π * Complex.I * n) ^ (k : ℕ) * Complex.exp (2 * ↑π *
    Complex.I * n * x)
  simp only [CharP.cast_eq_zero, mul_zero, zero_mul, exp_zero, mul_one, pow_eq_zero_iff', ne_eq,
    true_and] at this
  apply this
  linarith

theorem cot_series_repr (z : ℍ) :
    ↑π * cot (↑π * z) - 1 / z = ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
  have := cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement z)
  simp only [one_div] at *
  have hrw := tsum_pnat_eq_tsum_succ3 fun n : ℕ => (1 / ((z : ℂ) - n) + 1 / (z + n))
  simp only [one_div, Nat.cast_add, Nat.cast_one] at hrw
  rw [hrw]
  apply this


lemma EisensteinSeries_Identity (z : ℍ) :
    1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n := by
  have h1 := cot_series_repr z
  rw [pi_mul_cot_pi_q_exp z] at h1
  rw [← h1]
  ring


theorem q_exp_iden'' (k : ℕ) (hk : 2 ≤ k) :
    EqOn (fun z : ℂ => (-1 : ℂ) ^ (k - 1) * (k - 1)! * ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k)
      (fun z : ℂ =>
        -(2 * ↑π * Complex.I) * ∑' n : ℕ+, (2 * ↑π * Complex.I * n) ^ ((k - 1) : ℕ) * Complex.exp (2
          * ↑π * Complex.I * n * z))
      {z : ℂ | 0 < z.im} := by
  have := (aux_iter_der_tsum_eqOn k hk).symm
  apply EqOn.trans this
  have hkpos : 0 < k - 1 := by
    apply Nat.sub_pos_of_lt
    linarith
  have h2 := (iter_exp_eqOn (⟨k - 1, hkpos⟩ : ℕ+)).symm
  simp only [one_div, PNat.mk_coe, neg_mul, smul_eq_mul] at *
  have h3 := pos_sum_eq (k - 1) hkpos
  simp only [neg_mul] at h3
  rw [h3] at h2
  apply EqOn.symm
  apply EqOn.trans h2
  apply iteratedDerivWithin_congr
  intro z hz
  simp only [Pi.add_apply]
  have := EisensteinSeries_Identity ⟨z, hz⟩
  simp only [tsub_pos_iff_lt, one_div] at *
  rw [this]
  congr
  ext n
  rw [← Complex.exp_nsmul]
  congr
  ring

theorem q_exp_iden (k : ℕ) (hk : 2 ≤ k) (z : ℍ) :
    ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k =
      (-2 * ↑π * Complex.I) ^ k / (k - 1)! * ∑' n : ℕ+, n ^ ((k - 1)) * Complex.exp (2 * ↑π *
        Complex.I * z * n) := by
  have := q_exp_iden'' k hk z.2
  have hkk : 1 ≤ (k: ℤ) := by linarith
  simp only [one_div, neg_mul, Nat.one_le_cast] at *
  have hk2 : (-1 : ℂ) ^ ((k - 1)) * (k - 1)! ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
      Nat.cast_eq_zero, Nat.factorial_ne_zero, or_self, not_false_eq_true]
  rw [← mul_right_inj' hk2]
  rw [this]
  have h3 : (-1) ^ ((k - 1)) * ↑(k - 1)! * ((-(2 * ↑π * Complex.I)) ^ k / ↑(k - 1)!) = -(2 * ↑π *
    Complex.I) ^ k := by
    rw [mul_div, div_eq_mul_one_div, div_eq_inv_mul]
    simp_rw [← mul_assoc]
    simp only [mul_one]
    have hj : (-1) ^ (↑k - 1) * ↑(k - 1)! * (-(2 * ↑π * Complex.I)) ^ (k : ℕ) * (↑(k - 1)! : ℂ)⁻¹ =
       (-1) ^ (↑k - 1) * (-(2 * ↑π * Complex.I)) ^ (k : ℕ) * (↑(k - 1)! * (↑(k - 1)!)⁻¹) := by ring
    rw [hj]
    have h2 : (↑(k - 1)! : ℂ) * (↑(k - 1)!)⁻¹ = 1 := by
      rw [mul_inv_cancel₀]
      norm_cast
      apply Nat.factorial_ne_zero
    rw [h2]
    simp only [mul_one]
    rw [mul_comm, neg_pow, mul_comm, ← mul_assoc, ← pow_add, Odd.neg_one_pow]
    · ring
    have hkk : (k - 1) + k = 2 * k - 1 := by
        rw [add_comm, ← Nat.add_sub_assoc]
        · rw [two_mul]
        linarith
    rw [hkk]
    apply Nat.Even.sub_odd
    · nlinarith
    · simp
    exact odd_one
  rw [← mul_assoc]
  norm_cast at *
  simp only [Int.reduceNegSucc, Int.reduceNeg, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, ofReal_mul, ofReal_ofNat, mul_eq_zero, pow_eq_zero_iff',
    neg_eq_zero, one_ne_zero, ne_eq, false_and, Int.natCast_eq_zero, false_or, PNat.pow_coe,
    Nat.cast_pow] at *
  rw [h3]
  have hee :
    ∑' n : ℕ+, (2 * ↑π * Complex.I * ((n : ℕ) : ℂ)) ^ ((k - 1) : ℕ) *
      exp (2 * ↑π * Complex.I * ((n : ℕ) : ℂ) * ↑z) =
      (2 * ↑π * Complex.I) ^ (k - 1) * ∑' n : ℕ+, n ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * n) :=
    by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro b
    rw [← mul_assoc]
    ring_nf
  simp only [neg_mul, neg_inj] at *
  rw [hee, ← mul_assoc]
  have he2 : 2 * ↑π * Complex.I * (2 * ↑π * Complex.I) ^ (k - 1) = (2 * ↑π * Complex.I) ^ k := by
    have hke : k = 1 + (k - 1) := by
      apply symm; apply Nat.add_sub_of_le
      linarith
    nth_rw 2 [hke]
    norm_cast
    rw [pow_add]
    simp
  rw [he2]



theorem tsum_sigma_eqn2 (k : ℕ) (z : ℍ) :
    ∑' (c : Fin 2 → ℕ+), (c 0 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c 0 * c 1) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * z * e) := by
  rw [← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq, ← sigmaAntidiagonalEquivProd.tsum_eq]
  simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
    Equiv.coe_fn_mk, Fin.isValue, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
  simp_rw [sigma_eq_sum_div']
  simp only [Nat.cast_sum, Nat.cast_pow]
  rw [(summable_auxil_1 k z).tsum_sigma]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach]
  have := @Nat.sum_divisorsAntidiagonal' ℂ _ (fun (x : ℕ) => fun (y : ℕ) =>
    (x : ℂ) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * z * x * y)) n
  have H := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
    (x.1 : ℂ) ^ (k : ℕ) * Complex.exp (2 * ↑π * Complex.I * z * x.1 * x.2))
  rw [H, this, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', Nat.cast_eq_zero, Nat.div_eq_zero_iff, ne_eq]
  left
  congr 1
  have hni : (n / i : ℕ) * (i : ℂ) = n := by
    norm_cast
    simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at *
    exact Nat.div_mul_cancel hi
  rw [mul_assoc, hni]

/-This is proven in the modular forms repo. -/
lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (show 1 < (k : ℝ) by norm_cast)
  lift k to ℕ using (by linarith)
  have := linear_bigO_pow n z k
  norm_cast at *

/-This is straight from the mod forms repo-/
theorem tsum_sigma_eqn {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c.1 * c.2) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * e * z) := by
  rw [← (piFinTwoEquiv fun _ => ℕ+).tsum_eq]
  have := tsum_sigma_eqn2 k z
  simp only [piFinTwoEquiv_apply, Fin.isValue]
  grind

lemma exp_aux (z : ℍ) (n : ℕ) : cexp (2 * ↑π * Complex.I * n * ↑z) =
    cexp (2 * ↑π * Complex.I * ↑z) ^ n := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem summable_exp_pow (z : ℍ) : Summable fun i : ℕ ↦
     ‖(cexp (2 * ↑π * Complex.I * (↑i + 1) * z))‖ := by
  conv =>
    enter [1]
    ext i
    rw [show ((i : ℂ) + 1) = ((i + 1) : ℕ) by simp, exp_aux, norm_pow]
  rw [summable_nat_add_iff 1]
  simp only [summable_geometric_iff_norm_lt_one, norm_norm]
  apply exp_upperHalfPlane_lt_one

/-The exponential factor in `a1` has norm `< 1`. -/
lemma a1_norm_lt_one (e : ℕ+) (z : ℍ) :
    ‖cexp (2 * ↑π * Complex.I * ↑z * ↑↑e)‖ < 1 := by
  simp only [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, natCast_re, neg_mul, zero_add, natCast_im, Real.exp_lt_one_iff, Left.neg_neg_iff,
    Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_right]
  positivity

/-The summand of `a1` (before the scalar factor) is summable. -/
lemma a1_summable_norm (e : ℕ+) (z : ℍ) :
    Summable fun a : ℕ => ‖cexp (2 * ↑π * Complex.I * ↑z * ↑↑e * ↑↑a)‖ := by
  have hpow : (fun a : ℕ ↦ ‖cexp (2 * ↑π * Complex.I * ↑z * ↑↑e * ↑↑a)‖) =
      fun a : ℕ ↦ ‖cexp (2 * ↑π * Complex.I * ↑z * ↑↑e) ^ (a : ℕ)‖ := by
    funext a
    rw [← Complex.exp_nat_mul]
    congr 2
    ring
  rw [hpow]
  exact summable_norm_iff.mpr
    (summable_geometric_iff_norm_lt_one.mpr (a1_norm_lt_one e z))

/-This is straight from the mod forms repo-/
theorem a1 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * e * c) :=
  (Summable.of_norm (a1_summable_norm e z)).mul_left _


/-This is straight from the mod forms repo-/
theorem a4 (k : ℕ) (z : ℍ) :
    Summable (uncurry fun b c : ℕ+ => ↑b ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑c * ↑z * ↑b)) := by
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk]
  apply (summable_auxil_1 (k - 1) z).congr
  intro b
  simp only [comp_apply, uncurry_apply_pair, PNat.mk_coe, mul_eq_mul_left_iff, pow_eq_zero_iff',
    Nat.cast_eq_zero, ne_eq]
  left; ring_nf

lemma t9 (z : ℍ) : ∑' m : ℕ,
  ( 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n)) = -
    8 * π ^ 2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2 * π * Complex.I * n * z) := by
  have := tsum_pnat_eq_tsum_succ3 (fun m => 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ ((2 - 1)) * Complex.exp (2 * ↑π * Complex.I * (m) * z * n))
  simp only [neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one,
    div_one, pow_one, Nat.cast_add] at *
  rw [← this]
  have := tsum_sigma_eqn z (k := 1)
  rw [tsum_mul_left, ← this]
  have he : 2 * (2 * ↑π * Complex.I) ^ 2 = - 8 * π ^ 2 := by
     rw [pow_two]
     ring_nf
     simp only [I_sq, mul_neg, mul_one, neg_mul]
  rw [he]
  simp only [neg_mul, pow_one, neg_inj, mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
    ne_eq, not_false_eq_true, pow_eq_zero_iff, ofReal_eq_zero, false_or]
  left
  symm
  simp only [pow_one, neg_mul] at *
  rw [Summable.tsum_prod, Summable.tsum_comm']
  · congr
    funext m
    congr
    funext n
    simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false]
    congr 1
    ring
  · have := (a4 2 z).prod_symm
    simp only [Nat.add_one_sub_one, pow_one] at *
    apply this.congr
    intro b
    rw [Prod.swap]
    simp [uncurry]
    ring_nf
  · intro e
    have := a33 (k := 1) e z
    simp only [pow_one] at *
    apply this.congr
    intro b
    ring_nf
  · intro e
    have := a1 2 e z
    simp only [Nat.add_one_sub_one, pow_one] at *
    apply this.subtype
  have := a4 2 z
  apply this.congr
  intro b
  simp [uncurry]
  congr 1
  ring



lemma summable_pnats (f : ℕ → ℂ) : Summable (fun n : ℕ+ => f n) ↔ Summable f := by
  rw [nat_pos_tsum2', summable_nat_add_iff]
lemma auxf (a b c d : ℂ) : a / b - (c / d) = a / b + (c / -d) := by ring

theorem summable_diff_right_a (z : ℍ) (d : ℕ+) :
  Summable fun n : ℕ ↦ 1 / ((n : ℂ) * ↑z - ↑↑d) - 1 / (↑↑n * ↑z + ↑↑d) := by
  rw [← summable_pnats]
  have := (summable_diff z d).mul_left ((z : ℂ))⁻¹
  apply this.congr
  intro b
  have hz := ne_zero z
  simp at *
  grind

theorem summable_diff_right (z : ℍ) (d : ℕ+) :
  Summable fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z - ↑↑d) - 1 / (↑m * ↑z + ↑↑d) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply summable_diff_right_a
  · rw [← summable_pnats]
    have := (summable_diff z d).mul_left ((z : ℂ))⁻¹
    apply this.congr
    intro b
    have hz := ne_zero z
    simp at *
    grind

lemma sum_int_pnatt (z : ℍ) (d : ℕ+) :
  2/ d + ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z - d) - 1 / (↑m * ↑z + d)) = ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d))
      := by
  rw [tsum_int_eq_zero_add_tsum_pnat (summable_diff_right z d)]
  simp only [Int.cast_zero, zero_mul, zero_sub, one_div, zero_add, Int.cast_natCast, Int.cast_neg,
    neg_mul]
  ring_nf
  rw [← Summable.tsum_add]
  · congr
    funext m
    ring
  · have := (summable_diff_right z d)
    rw [summable_int_iff_summable_nat_and_neg] at this
    have H := this.1
    simp only [Int.cast_natCast, one_div, Int.cast_neg, neg_mul] at *
    have v : Summable fun (n : ℕ) ↦ (-↑(d : ℂ) + (n : ℂ) * ↑z)⁻¹ - (↑↑d + (n : ℂ)* ↑z)⁻¹ := by
      apply H.congr
      intro b
      ring
    apply v.subtype
  · have := (summable_diff_right z d)
    rw [summable_int_iff_summable_nat_and_neg] at this
    have H := this.2
    simp only [Int.cast_natCast, one_div, Int.cast_neg, neg_mul] at *
    have v : Summable fun (n : ℕ) ↦ ( - ↑(d : ℂ)- z * ((n : ℂ)))⁻¹ - (↑↑d - z * ((n : ℂ)))⁻¹ := by
      apply H.congr
      intro b
      ring
    apply v.subtype

lemma sum_int_pnat2_pnat (z : ℍ) (d : ℕ+) :
  ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z - d) - 1 / (↑m * ↑z + d)) = -2/d + ∑' m : ℕ+,
    ((1 / ((m : ℂ) * ↑z - d) + 1 / (-↑m * ↑z + -d)) - (1 / ((m : ℂ) * ↑z + d)) - 1 / (-↑m * ↑z + d))
      := by
  rw [← sum_int_pnatt]
  ring
