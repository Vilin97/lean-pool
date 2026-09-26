/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences

/-!
# Sumsets of well-ordered sets of reals

The two geometric inputs to Berarducci's convolution formula in Section 7.

Berarducci, Lemma 7.1: the closure of the pointwise sum of two partially well-ordered subsets of
`ℝ` is the sum of their closures. Berarducci, Lemma 7.4: for `δ ≤ γ` sufficiently close to
`γ`,
every point of `B × C` on the line of sum `δ` is dominated coordinatewise by exactly one point of
`B × C` on the line of sum `γ`.

Both rest on one construction: a sequence in `B + C` converging to `x` can be replaced by a
subsequence whose two factor sequences are monotone, hence convergent, with limits in the two
closures summing to `x`. Well-ordering supplies the monotone subsequences and completeness of `ℝ`
supplies their limits; Berarducci, Remark 7.3 records that Lemma 7.1 fails over `ℚ`.

Uniqueness in Lemma 7.4 is separate and uses only well-ordering: the line of sum `γ` meets
`B × C` in finitely many points, so the first coordinates of those points are separated by some
`d > 0`, and two distinct dominating points would force `γ - δ ≥ d`.

The inclusion `closure B + closure C ⊆ closure (B + C)` holds for arbitrary sets and is stated
separately. Lemma 7.4 is applied to the closed supports of two series, so the module also proves
that the closure of a partially well-ordered set of reals is partially well ordered: a strictly
decreasing sequence in the closure can be pushed down to one in the set itself.
-/

public noncomputable section

open Pointwise Filter Topology

namespace Set

private theorem exists_mem_Ioc_of_mem_closure {B : Set ℝ} (hB : B.IsPWO) {x y : ℝ}
    (hx : x ∈ closure B) (hy : y < x) : ∃ b ∈ B, y < b ∧ b ≤ x := by
  by_contra hcon
  push Not at hcon
  have habove : ∀ b ∈ B, y < b → x < b := by
    intro b hbB hyb
    exact lt_of_not_ge fun hbx ↦ absurd hbx (not_le.mpr (hcon b hbB hyb))
  set U := B ∩ Set.Ioi x with hU
  have hUwf : U.IsWF := hB.isWF.mono Set.inter_subset_left
  have hUne : U.Nonempty := by
    obtain ⟨b, hbB, hb⟩ := Metric.mem_closure_iff.mp hx (x - y) (by linarith)
    rw [Real.dist_eq, abs_lt] at hb
    exact ⟨b, hbB, habove b hbB (by linarith [hb.1])⟩
  set m := hUwf.min hUne with hm
  have hmU : m ∈ U := hUwf.min_mem hUne
  have hmx : x < m := hmU.2
  obtain ⟨b', hb'B, hb'⟩ :=
    Metric.mem_closure_iff.mp hx (min (m - x) (x - y)) (lt_min (by linarith) (by linarith))
  rw [Real.dist_eq, abs_lt] at hb'
  have hb'y : y < b' := by
    have := hb'.1
    have hle : min (m - x) (x - y) ≤ x - y := min_le_right _ _
    linarith
  have hb'x : x < b' := habove b' hb'B hb'y
  have hb'm : b' < m := by
    have := hb'.2
    have hle : min (m - x) (x - y) ≤ m - x := min_le_left _ _
    linarith
  exact absurd hb'm (not_lt.mpr (hUwf.min_le hUne ⟨hb'B, hb'x⟩))

/-- The closure of a partially well-ordered set of reals is partially well ordered. -/
theorem isPWO_closure {B : Set ℝ} (hB : B.IsPWO) : (closure B).IsPWO := by
  rw [Set.isPWO_iff_isWF, Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  choose b hbB hb using fun n ↦
    exists_mem_Ioc_of_mem_closure hB (hmem n) (hf (Nat.lt_succ_self n))
  have hAnti : StrictAnti b := by
    refine strictAnti_nat_of_succ_lt fun n ↦ ?_
    exact lt_of_le_of_lt (hb (n + 1)).2 (hb n).1
  exact (Set.isWF_iff_no_descending_seq.mp hB.isWF) b hAnti hbB

private theorem exists_monotone_limits_of_add_tendsto
    {B C : Set ℝ} (hB : B.IsPWO) (hC : C.IsPWO) {x : ℝ}
    {b c : ℕ → ℝ} (hb : ∀ n, b n ∈ B) (hc : ∀ n, c n ∈ C)
    (hlim : Tendsto (fun n ↦ b n + c n) atTop (𝓝 x)) :
    ∃ (g : ℕ → ℕ) (β ξ : ℝ), StrictMono g ∧ β ∈ closure B ∧ ξ ∈ closure C ∧
      β + ξ = x ∧ (∀ n, b (g n) ≤ β) ∧ ∀ n, c (g n) ≤ ξ := by
  obtain ⟨g₁, hg₁⟩ := hB.exists_monotone_subseq hb
  obtain ⟨g₂, hg₂⟩ :=
    hC.exists_monotone_subseq (f := fun n ↦ c (g₁ n)) fun n ↦ hc (g₁ n)
  set g : ℕ → ℕ := fun n ↦ g₁ (g₂ n) with hgDef
  have hgMono : StrictMono g := g₁.strictMono.comp g₂.strictMono
  set B' : ℕ → ℝ := fun n ↦ b (g n) with hB'Def
  set C' : ℕ → ℝ := fun n ↦ c (g n) with hC'Def
  have hB'mono : Monotone B' := fun _ _ hmn ↦ hg₁ (g₂.strictMono.monotone hmn)
  have hC'mono : Monotone C' := fun _ _ hmn ↦ hg₂ hmn
  have hsumLim : Tendsto (fun n ↦ B' n + C' n) atTop (𝓝 x) :=
    hlim.comp hgMono.tendsto_atTop
  have hbound : ∀ n, B' n + C' n ≤ x := (hB'mono.add hC'mono).ge_of_tendsto hsumLim
  have hB'bdd : BddAbove (Set.range B') := by
    refine ⟨x - C' 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h0 := hC'mono (Nat.zero_le n)
    have hn := hbound n
    linarith
  have hC'bdd : BddAbove (Set.range C') := by
    refine ⟨x - B' 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h0 := hB'mono (Nat.zero_le n)
    have hn := hbound n
    linarith
  have hB'lim : Tendsto B' atTop (𝓝 (⨆ n, B' n)) := tendsto_atTop_ciSup hB'mono hB'bdd
  have hC'lim : Tendsto C' atTop (𝓝 (⨆ n, C' n)) := tendsto_atTop_ciSup hC'mono hC'bdd
  refine ⟨g, ⨆ n, B' n, ⨆ n, C' n, hgMono,
    mem_closure_of_tendsto hB'lim (by filter_upwards with n using hb (g n)),
    mem_closure_of_tendsto hC'lim (by filter_upwards with n using hc (g n)), ?_,
    fun n ↦ le_ciSup hB'bdd n, fun n ↦ le_ciSup hC'bdd n⟩
  exact tendsto_nhds_unique (hB'lim.add hC'lim) hsumLim

theorem closure_add_closure_subset (B C : Set ℝ) :
    closure B + closure C ⊆ closure (B + C) := by
  rw [← Set.image2_add, ← Set.image2_add, ← Set.image_prod, ← Set.image_prod,
    ← closure_prod_eq]
  exact image_closure_subset_closure_image (by fun_prop)

theorem IsPWO.closure_add {B C : Set ℝ} (hB : B.IsPWO) (hC : C.IsPWO) :
    closure (B + C) = closure B + closure C := by
  refine Set.Subset.antisymm ?_ (closure_add_closure_subset B C)
  intro x hx
  obtain ⟨y, hy, hyx⟩ := mem_closure_iff_seq_limit.mp hx
  choose b hb c hc hbc using fun n ↦ Set.mem_add.mp (hy n)
  have hlim : Tendsto (fun n ↦ b n + c n) atTop (𝓝 x) := by
    simpa only [hbc] using hyx
  obtain ⟨_, β, ξ, _, hβ, hξ, hsum, -, -⟩ :=
    exists_monotone_limits_of_add_tendsto hB hC hb hc hlim
  exact hsum ▸ Set.add_mem_add hβ hξ

/-- Berarducci, Section 7: a line `β + ξ = γ` meets `B × C` in finitely many points. -/
theorem IsPWO.finite_sub_mem {B C : Set ℝ} (hB : B.IsPWO) (hC : C.IsPWO) (γ : ℝ) :
    {β | β ∈ B ∧ γ - β ∈ C}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set e := hinf.natEmbedding with he
  set u : ℕ → ℝ := fun n ↦ (e n : ℝ) with hu
  have huInj : Function.Injective u := fun m n hmn ↦ e.injective (Subtype.ext hmn)
  have huB : ∀ n, u n ∈ B := fun n ↦ (e n).2.1
  have huC : ∀ n, γ - u n ∈ C := fun n ↦ (e n).2.2
  obtain ⟨g, hg⟩ := hB.exists_monotone_subseq huB
  set v : ℕ → ℝ := fun n ↦ u (g n) with hv
  have hvMono : Monotone v := fun _ _ hmn ↦ hg hmn
  have hvInj : Function.Injective v := huInj.comp g.injective
  have hvStrict : StrictMono v := hvMono.strictMono_of_injective hvInj
  have hwAnti : StrictAnti (fun n ↦ γ - v n) := fun _ _ hmn ↦
    sub_lt_sub_left (hvStrict hmn) γ
  exact (Set.isWF_iff_no_descending_seq.mp hC.isWF) _ hwAnti fun n ↦ huC (g n)

private theorem exists_pos_forall_le_abs_sub {S : Set ℝ} (hS : S.Finite) :
    ∃ d > (0 : ℝ), ∀ β₁ ∈ S, ∀ β₂ ∈ S,
      β₁ ≠ β₂ → d ≤ |β₁ - β₂| := by
  classical
  set T := hS.toFinset with hT
  set P := (T ×ˢ T).filter fun p ↦ p.1 ≠ p.2 with hP
  by_cases hPne : P.Nonempty
  · refine ⟨P.inf' hPne fun p ↦ |p.1 - p.2|, ?_, ?_⟩
    · rw [gt_iff_lt, Finset.lt_inf'_iff]
      intro p hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact abs_pos.mpr (sub_ne_zero.mpr hne)
    · intro β₁ h₁ β₂ h₂ hne
      have hmem : (β₁, β₂) ∈ P := by
        simp only [hP, Finset.mem_filter, Finset.mem_product, hT,
          Set.Finite.mem_toFinset]
        exact ⟨⟨h₁, h₂⟩, hne⟩
      exact Finset.inf'_le (fun p ↦ |p.1 - p.2|) hmem
  · refine ⟨1, one_pos, fun β₁ h₁ β₂ h₂ hne ↦ absurd ⟨(β₁, β₂), ?_⟩ hPne⟩
    simp only [hP, Finset.mem_filter, Finset.mem_product, hT,
      Set.Finite.mem_toFinset]
    exact ⟨⟨h₁, h₂⟩, hne⟩

private theorem eventually_unique_dominating {B C : Set ℝ}
    (hB : B.IsPWO) (hC : C.IsPWO) (γ : ℝ) :
    ∀ᶠ δ in 𝓝[≤] γ, ∀ β' ξ' : ℝ, β' + ξ' = δ → ∀ β₁ β₂ : ℝ,
      (β₁ ∈ B ∧ γ - β₁ ∈ C ∧ β' ≤ β₁ ∧ ξ' ≤ γ - β₁) →
        (β₂ ∈ B ∧ γ - β₂ ∈ C ∧ β' ≤ β₂ ∧
          ξ' ≤ γ - β₂) →
        β₁ = β₂ := by
  obtain ⟨d, hd, hgap⟩ := exists_pos_forall_le_abs_sub (hB.finite_sub_mem hC γ)
  have hnear : ∀ᶠ δ in 𝓝[≤] γ, γ - d < δ :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by linarith))
  filter_upwards [hnear] with δ hδ β' ξ' hsum β₁ β₂ h₁ h₂
  by_contra hne
  have hd₁₂ : d ≤ |β₁ - β₂| :=
    hgap β₁ ⟨h₁.1, h₁.2.1⟩ β₂ ⟨h₂.1, h₂.2.1⟩ hne
  rcases abs_cases (β₁ - β₂) with ⟨habs, _⟩ | ⟨habs, _⟩
  · have : δ ≤ γ - d := by
      have h := h₂.2.2.1
      have h' := h₁.2.2.2
      rw [habs] at hd₁₂
      linarith
    linarith
  · have : δ ≤ γ - d := by
      have h := h₁.2.2.1
      have h' := h₂.2.2.2
      rw [habs] at hd₁₂
      linarith
    linarith

private theorem eventually_exists_dominating {B C : Set ℝ}
    (hB : B.IsPWO) (hC : C.IsPWO) (hBc : IsClosed B) (hCc : IsClosed C) (γ : ℝ) :
    ∀ᶠ δ in 𝓝[≤] γ, ∀ β' ∈ B, ∀ ξ' ∈ C, β' + ξ' = δ →
      ∃ β, β ∈ B ∧ γ - β ∈ C ∧ β' ≤ β ∧ ξ' ≤ γ - β := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨δ, hδ, hδp⟩ := Filter.exists_seq_forall_of_frequently hcon
  simp only [not_forall, not_exists] at hδp
  choose b hb c hc hbc hno using hδp
  have hlim : Tendsto (fun n ↦ b n + c n) atTop (𝓝 γ) := by
    have hδγ : Tendsto δ atTop (𝓝 γ) := hδ.mono_right nhdsWithin_le_nhds
    simpa only [hbc] using hδγ
  obtain ⟨g, β, ξ, _, hβ, hξ, hsum, hble, hcle⟩ :=
    exists_monotone_limits_of_add_tendsto hB hC hb hc hlim
  have hβB : β ∈ B := hBc.closure_eq ▸ hβ
  have hξC : ξ ∈ C := hCc.closure_eq ▸ hξ
  have hγβ : γ - β = ξ := by linarith
  exact hno (g 0) β ⟨hβB, by rw [hγβ]; exact hξC, hble 0, by rw [hγβ]; exact hcle 0⟩

/-- Berarducci, Lemma 7.4: for `δ ≤ γ` sufficiently close to `γ`, every point of
`B × C` on the line of sum `δ` is dominated by exactly one point of `B × C` on the line of
sum `γ`. -/
theorem IsPWO.eventually_existsUnique_dominating {B C : Set ℝ}
    (hB : B.IsPWO) (hC : C.IsPWO) (hBc : IsClosed B) (hCc : IsClosed C) (γ : ℝ) :
    ∀ᶠ δ in 𝓝[≤] γ, ∀ β' ∈ B, ∀ ξ' ∈ C, β' + ξ' = δ →
      ∃! β, β ∈ B ∧ γ - β ∈ C ∧ β' ≤ β ∧ ξ' ≤ γ - β := by
  filter_upwards [eventually_exists_dominating hB hC hBc hCc γ,
    eventually_unique_dominating hB hC γ] with δ hex huniq β' hβ' ξ' hξ' hsum
  obtain ⟨β, hβ⟩ := hex β' hβ' ξ' hξ' hsum
  exact ⟨β, hβ, fun β₂ h₂ ↦ huniq β' ξ' hsum β₂ β h₂ hβ⟩

end Set
