/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sign.Defs

/-!
# Subsum conditions
-/


open Finset SignType

variable {n k : ℕ} (a : Fin n → ℤ)

/-- The subsum condition: any subset of the tuple summing to 0
is either empty or the whole tuple. -/
def SSC : Prop :=
  ∀ b, b.Nonempty → bᶜ.Nonempty → ∑ i ∈ b, a i ≠ 0

/-- A subsum block for `a` is an index set that must be constant in any sign weighting
of the tuple's elements that leads to a zero sum. -/
def IsSubsumBlock (s : Finset (Fin n)) : Prop :=
  ∀ b : Fin n → SignType, ∑ i, b i * a i = 0 → ∃ c, ∀ i ∈ s, b i = c

/-- The strong subsum condition, defined as all `Fin n` being a subsum block. -/
def StrongSSC : Prop :=
  IsSubsumBlock a univ

variable {a}

lemma StrongSSC.SSC (h : StrongSSC a) : SSC a := by
  unfold _root_.SSC StrongSSC IsSubsumBlock at *
  contrapose! h
  obtain ⟨b, n₁, n₂, hs⟩ := h
  refine ⟨fun i ↦ if i ∈ b then pos else zero, ?_, fun c ↦ ?_⟩
  · simp_rw [pos_eq_one, zero_eq_zero, apply_ite, coe_one, coe_zero, ite_mul, one_mul, zero_mul,
      ← sum_filter, filter_univ_mem, hs]
  · obtain ⟨i₁, mi₁⟩ := n₁
    obtain ⟨i₂, mi₂⟩ := n₂
    simp_rw [mem_univ, true_and]
    match c with
    | zero => exact ⟨i₁, by simp_all⟩
    | neg => exact ⟨i₁, by simp_all⟩
    | pos => exact ⟨i₂, by simp_all⟩

lemma SSC.ne_zero (ha : SSC a) (hn : 2 ≤ n) {i : Fin n} : a i ≠ 0 := by
  unfold SSC at ha
  contrapose! ha
  refine ⟨{i}, by simp, ?_, ?_⟩
  · rw [← card_pos, card_compl, Fintype.card_fin, card_singleton]
    exact Nat.zero_lt_sub_of_lt hn
  · rwa [sum_singleton]

lemma StrongSSC.ne_zero (ha : StrongSSC a) (hn : 2 ≤ n) {i : Fin n} : a i ≠ 0 :=
  ha.SSC.ne_zero hn

lemma StrongSSC.perm (h : StrongSSC a) (e : Equiv.Perm (Fin n)) : StrongSSC (a ∘ e) := fun b hs ↦ by
  have : b = (b ∘ e.symm) ∘ e := by simp [Function.comp_assoc]
  conv_lhs at hs =>
    enter [2, i]
    rw [this, Function.comp_apply]
    enter [2]
    rw [Function.comp_apply]
  rw [e.sum_comp univ (fun i ↦ (b ∘ e.symm) i * a i) (by simp)] at hs
  specialize h _ hs
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i _ ↦ ?_⟩
  specialize hc (e i) (mem_univ _)
  simpa using hc

lemma strongSSC_perm_iff (e : Equiv.Perm (Fin n)) : StrongSSC a ↔ StrongSSC (a ∘ e) where
  mp h := h.perm e
  mpr h := by simpa [Function.comp_assoc] using h.perm e.symm

lemma StrongSSC.injective (h : StrongSSC a) : a.Injective := fun i j e ↦ by
  unfold StrongSSC IsSubsumBlock at h
  contrapose! h
  refine ⟨fun k ↦ if k = i then pos else if k = j then neg else zero, ?_, fun c ↦ ?_⟩
  · simp only [apply_ite SignType.cast, ite_mul]
    rw [← Fintype.sum_subset (s := {i, j}) (fun k hk ↦ by contrapose! hk; simp_all), sum_pair h]
    simp [h.symm, e]
  · simp_rw [mem_univ, true_and]
    match c with
    | zero => exact ⟨i, by simp⟩
    | neg => exact ⟨i, by simp⟩
    | pos => exact ⟨j, by simp [h.symm]⟩

/-- Upstreamable to mathlib! [Mathlib.Algebra.BigOperators.Group.Finset.Basic] -/
lemma Finset.natAbs_prod {ι : Type*} {s : Finset ι} {f : ι → ℤ} :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction with simp_all [Int.natAbs_mul]

lemma StrongSSC.one_lt_natAbs_prod (ha : StrongSSC a) (hn : 3 ≤ n) : 1 < (∏ i, a i).natAbs := by
  rw [Finset.natAbs_prod]
  have g (i : Fin n) : 1 ≤ (a i).natAbs := by
    rw [Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero]
    exact ha.ne_zero (by lia)
  refine (one_lt_prod_iff_of_one_le fun i _ ↦ g i).mpr ?_
  simp_rw [mem_univ, true_and]
  contrapose! ha
  replace ha (i : Fin n) : a i = 1 ∨ a i = -1 := by
    rw [← Int.natAbs_eq_natAbs_iff]
    exact le_antisymm (ha _) (g _)
  let nzn : NeZero n := ⟨by lia⟩
  obtain h | h | h : a 0 = a 1 ∨ a 1 = a 2 ∨ a 2 = a 0 := by grind [ha 0, ha 1, ha 2]
  all_goals
    apply StrongSSC.injective.mt
    rw [Function.not_injective_iff]
    refine ⟨_, _, h, ?_⟩
    simp_rw [Fin.ne_iff_vne, Fin.coe_ofNat_eq_mod]
    rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
    decide

section TupReduce

variable (s : Finset (Fin n)) (hk : k = n - #s)

/-- The order-preserving bijection from `Fin k` to `sᶜ`, where `k = n - #s`. -/
def complRank (i : Fin k) : Fin n :=
  sᶜ.orderEmbOfFin (by simp [card_compl]) (i.cast hk)

lemma complRank_01 : complRank {0, 1} (n.add_sub_cancel 2).symm = (Fin.addNat · 2) :=
  (orderEmbOfFin_unique _ (by simp [Fin.ext_iff]) (Fin.strictMono_addNat 2)).symm

variable (a) in
/-- `tupReduce a s hk` is the tuple with `∑ i ∈ s, a i` at the last index
and the remaining elements of `a` appended in order.
`hk : k = n - #s` mitigates definitional equality problems. -/
def tupReduce : Fin (k + 1) → ℤ :=
  Fin.lastCases (∑ i ∈ s, a i) fun i ↦ a (complRank s hk i)

variable {s hk}

lemma injective_complRank : (complRank s hk).Injective := fun i j h ↦ by
  simpa [complRank] using h

lemma image_complRank_univ : univ.image (complRank s hk) = sᶜ := by
  unfold complRank
  subst hk
  simp_all

end TupReduce

namespace IsSubsumBlock

variable {i j : Fin n} {s t : Finset (Fin n)}

lemma empty : IsSubsumBlock a ∅ := fun b h ↦ by simp

lemma singleton : IsSubsumBlock a {i} := fun b h ↦ by simp

lemma subset (hs : IsSubsumBlock a s) (ht : t ⊆ s) : IsSubsumBlock a t := fun b h ↦
  (hs b h).imp fun _ hc _ mi ↦ hc _ (ht mi)

lemma union (hs : IsSubsumBlock a s) (ht : IsSubsumBlock a t) (hd : ¬Disjoint s t) :
    IsSubsumBlock a (s ∪ t) := fun b h ↦ by
  obtain ⟨c, hc⟩ := hs b h
  obtain ⟨c', hc'⟩ := ht b h
  have e : c = c' := by
    obtain ⟨i, hi₁, hi₂⟩ := not_disjoint_iff.mp hd
    grind
  exact ⟨c, fun i mi ↦ by grind⟩

theorem of_sum_natAbs_lt (f : Fin k ↪ Fin n)
    (hf : ∀ b : Fin k → SignType, (¬∃ c, ∀ i, b i = c) →
      ∑ i ∉ univ.map f, (a i).natAbs < (∑ i, b i * a (f i)).natAbs) :
    IsSubsumBlock a (univ.map f) := fun b hs ↦ by
  contrapose! hs
  simp only [mem_map, mem_univ, true_and, ↓existsAndEq] at hs
  specialize hf (b ∘ f)
  simp only [Function.comp_apply, not_exists, not_forall] at hf
  specialize hf hs
  rw [← sum_add_sum_compl (univ.map f), Ne, add_eq_zero_iff_eq_neg', sum_map]
  suffices (∑ i ∉ univ.map f, b i * a i).natAbs ≠ (∑ i, b (f i) * a (f i)).natAbs by
    contrapose this
    rw [this, Int.natAbs_neg]
  refine Int.natAbs_sum_le .. |>.trans (sum_le_sum fun i _ ↦ ?_) |>.trans_lt hf |>.ne
  cases b i <;> simp

/-- If there are two elements of opposite signs, each dominating the remaining `n - 2` elements
(in the sense of violating the triangle inequality), the two elements form a subsum block. -/
theorem pair_of_sum_natAbs_lt (hi : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a i).natAbs)
    (hj : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a j).natAbs) (hprod : a i * a j ≤ 0) :
    IsSubsumBlock a {i, j} := by
  obtain rfl | hn := eq_or_ne i j
  · simp [singleton]
  let f : Fin 2 ↪ Fin n := ⟨fun | 0 => i | 1 => j, fun i₁ i₂ h ↦ by grind⟩
  have mf : univ.map f = {i, j} := by ext k; simp [f]; grind
  rw [← mf]
  refine of_sum_natAbs_lt _ fun b ncb ↦ ?_
  simp_rw [Fin.sum_univ_two, mf, f, Function.Embedding.coeFn_mk]
  suffices ∀ (b₁ b₂ : SignType),
      b₁ ≠ b₂ → ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (b₁ * a i + b₂ * a j).natAbs by
    apply this
    contrapose! ncb
    refine ⟨b 0, fun i ↦ ?_⟩
    obtain rfl | rfl : i = 0 ∨ i = 1 := by lia
    · rfl
    · exact ncb.symm
  intro b₁ b₂ hb
  cases b₁ <;> cases b₂ <;> simp at hb
  case zero.neg => simpa using hj
  case zero.pos => simpa using hj
  case neg.zero => simpa using hi
  case pos.zero => simpa using hi
  all_goals
    rw [Int.mul_nonpos_iff] at hprod
    simp only [pos_eq_one, neg_eq_neg_one, coe_neg, coe_one]
    grind

/-- Reduce a subsum block to a single element when proving the strong subsum condition. -/
theorem strongSSC_tupReduce (p : IsSubsumBlock a s) (hk : k = n - #s)
    (h : StrongSSC (tupReduce a s hk)) : StrongSSC a := by
  unfold StrongSSC IsSubsumBlock at *
  contrapose! h
  obtain ⟨b, hs, hc⟩ := h
  obtain ⟨c₀, hc₀⟩ := p _ hs
  refine ⟨Fin.lastCases c₀ (b ∘ complRank s hk), ?_, fun c ↦ ?_⟩
  · simp_rw [Fin.sum_univ_castSucc, tupReduce, Fin.lastCases_last, Fin.lastCases_castSucc,
      Function.comp_apply]
    have io : (SetLike.coe univ).InjOn (complRank s hk) := by simp [injective_complRank]
    rw [← sum_image (f := fun i ↦ (b i) * a i) io, image_complRank_univ, mul_sum]
    have s_eq : ∑ i ∈ s, c₀ * a i = ∑ i ∈ s, b i * a i := sum_congr rfl fun i mi ↦ by rw [hc₀ _ mi]
    rwa [s_eq, sum_compl_add_sum]
  · obtain rfl | hn := eq_or_ne c₀ c
    · obtain ⟨i, -, hi⟩ := hc c₀
      have key : i ∈ sᶜ := by
        contrapose! hi
        exact hc₀ _ (notMem_compl.mp hi)
      rw [← image_complRank_univ (hk := hk), mem_image_univ_iff_mem_range, Set.mem_range] at key
      obtain ⟨j, rfl⟩ := key
      exact ⟨j.castSucc, mem_univ _, by simp [hi]⟩
    · exact ⟨Fin.last _, mem_univ _, by simpa⟩

end IsSubsumBlock
