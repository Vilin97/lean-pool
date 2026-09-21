/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.Function
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.Tower
/-!
# The fibre average in Herbrand's theorem

This file formalizes the remaining finite-group calculation in
the Herbrand quotient theorem.  For a normal subgroup `H`, the depth on `G`
defines the lower filtration

`H_s = {τ : H | s + 1 ≤ depth τ}`.

For a nonidentity class in `G ⧸ H`, all depths in its fibre are finite, so
their normalized average is a definition rather than an assumed quotient
depth.  The main theorem identifies this average, at a representative of
maximal depth, with the Herbrand function of the above filtration.  The
valued-field equality between this average and the actual quotient depth is
the separate input of the quotient-depth identity.
-/

noncomputable section

universe u

namespace RamificationTheory.DiscreteValuationField
namespace HerbrandGroupTheory
namespace NonarchimedeanDepth

variable {G : Type u} [Group G]

variable (D : NonarchimedeanDepth G)

/-- States the theorem `depth_inv`. -/
theorem depth_inv (σ : G) : D.depth σ⁻¹ = D.depth σ := by
  by_contra h
  have hmin := D.depth_mul_eq_min_of_ne h
  have htop : min (D.depth σ⁻¹) (D.depth σ) = ⊤ := by
    rw [← hmin]
    simp [D.depth_one]
  have hσinv : D.depth σ⁻¹ = ⊤ := (min_eq_top.mp htop).1
  have hσ : D.depth σ = ⊤ := (min_eq_top.mp htop).2
  exact h (hσinv.trans hσ.symm)

variable (H : Subgroup G) [H.Normal]

noncomputable local instance averageSubgroupFintype [Finite G] : Fintype H :=
  Fintype.ofFinite H

noncomputable local instance averageQuotientFiberFintype [Finite G] (q : G ⧸ H) :
    Fintype (QuotientFiber H q) :=
  Fintype.ofFinite (QuotientFiber H q)

/-- The `n`th lower group of `H` cut out by the ambient depth:
`H_n = {τ | n + 1 ≤ depth τ}`. -/
def depthLowerSubgroup (n : ℕ) : Subgroup H where
  carrier := {τ | WithTop.some (n + 1) ≤ D.depth (τ : G)}
  one_mem' := by simp [D.depth_one]
  mul_mem' := by
    intro σ τ hσ hτ
    exact le_trans (le_min hσ hτ) (D.depth_mul_ge_min (σ : G) (τ : G))
  inv_mem' := by
    intro σ hσ
    simpa [D.depth_inv] using hσ

omit [H.Normal] in
/-- States the theorem `mem_depthLowerSubgroup_iff`. -/
@[simp] theorem mem_depthLowerSubgroup_iff (n : ℕ) (τ : H) :
    τ ∈ D.depthLowerSubgroup H n ↔
      WithTop.some (n + 1) ≤ D.depth (τ : G) :=
  Iff.rfl

/-- The exact lower filtration on `H` induced by `D`.  Conjugation
invariance of the depth supplies normality of every level. -/
def depthLowerFiltration : AntitoneNormalSubgroupFiltration H where
  lower := D.depthLowerSubgroup H
  lower_normal := by
    intro n
    constructor
    intro τ hτ σ
    change WithTop.some (n + 1) ≤ D.depth (((σ * τ * σ⁻¹ : H) : G))
    rw [show (((σ * τ * σ⁻¹ : H) : G)) =
        (σ : G) * (τ : G) * (σ : G)⁻¹ by rfl, D.depth_conj]
    exact hτ
  antitone := fun {m n} hmn τ hτ => by
    change WithTop.some (m + 1) ≤ D.depth (τ : G)
    have hmn' : m + 1 ≤ n + 1 := Nat.add_le_add_right hmn 1
    exact le_trans (WithTop.coe_le_coe.2 hmn') hτ

omit [H.Normal] in
/-- States the theorem `depthLowerFiltration_lower`. -/
@[simp] theorem depthLowerFiltration_lower (n : ℕ) :
    (D.depthLowerFiltration H).lower n = D.depthLowerSubgroup H n :=
  rfl

/-- The ramification index in the purely group-theoretic calculation,
namely `|H_0|`. -/
def depthRamificationIndex [Finite G] : ℕ :=
  Nat.card ((D.depthLowerFiltration H).lower 0)

/-- The actual normalized average of the finite depths in a nontrivial
quotient fibre.  No quotient-depth datum is included in this definition. -/
def quotientFiberAverage [Fintype G] {q : G ⧸ H} (hq : q ≠ 1) : ℝ :=
  (∑ γ : QuotientFiber H q, (D.quotientFiberDepth H hq γ : ℝ)) /
    D.depthRamificationIndex H

omit [H.Normal] in
/-- States the theorem `truncatedLowerDepth_add_one`. -/
theorem truncatedLowerDepth_add_one (n : ℕ)
    (τ : (D.depthLowerFiltration H).lower 0) :
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.truncatedLowerDepth (D.depthLowerFiltration H)) n τ + 1 =
      WithTop.untopD (α := ℕ) 0
        (min (D.depth ((τ : H) : G)) (WithTop.some (n + 1))) := by
  classical
  by_cases htop : D.depth ((τ : H) : G) = ⊤
  · have hfilter :
        (Finset.range n).filter (fun i =>
            (τ : H) ∈ (D.depthLowerFiltration H).lower (i + 1)) =
          Finset.range n := by
      ext i
      simp [depthLowerFiltration, depthLowerSubgroup, htop]
    rw [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.truncatedLowerDepth, hfilter]
    simp only [Finset.card_range, htop, min_eq_right le_top,
      WithTop.untopD_coe]
  · let k := (D.depth ((τ : H) : G)).untop htop
    have hdepth : WithTop.some k = D.depth ((τ : H) : G) :=
      WithTop.coe_untop _ _
    have hk : 1 ≤ k := by
      have hprop := τ.property
      change WithTop.some 1 ≤ D.depth ((τ : H) : G) at hprop
      rw [← hdepth] at hprop
      exact WithTop.coe_le_coe.mp hprop
    have hfilter :
        (Finset.range n).filter (fun i =>
            (τ : H) ∈ (D.depthLowerFiltration H).lower (i + 1)) =
          Finset.range (min n (k - 1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range,
        mem_depthLowerSubgroup_iff, depthLowerFiltration_lower]
      rw [← hdepth]
      constructor
      · rintro ⟨hin, hle⟩
        have hle' : i + 1 + 1 ≤ k := WithTop.coe_le_coe.mp hle
        simp only [lt_min_iff]
        omega
      · intro hi
        simp only [lt_min_iff] at hi
        refine ⟨hi.1, WithTop.coe_le_coe.2 ?_⟩
        omega
    rw [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.truncatedLowerDepth, hfilter, ← hdepth]
    rw [← WithTop.coe_min]
    simp only [Finset.card_range, WithTop.untopD_coe]
    omega

omit [H.Normal] in
/-- States the theorem `depth_eq_zero_of_not_mem_lower_zero`. -/
theorem depth_eq_zero_of_not_mem_lower_zero (τ : H)
    (hτ : τ ∉ (D.depthLowerFiltration H).lower 0) :
    D.depth (τ : G) = (0 : ℕ) := by
  have hnot : ¬ (1 : ℕ) ≤ D.depth (τ : G) := hτ
  by_cases htop : D.depth (τ : G) = ⊤
  · rw [htop] at hnot
    simp at hnot
  · let k := (D.depth (τ : G)).untop htop
    have hdepth : WithTop.some k = D.depth (τ : G) :=
      WithTop.coe_untop _ _
    rw [← hdepth] at hnot ⊢
    have hk : ¬ 1 ≤ k := by
      intro hk
      exact hnot (WithTop.coe_le_coe.2 hk)
    have : k = 0 := by omega
    simp [this]

omit [H.Normal] in
/-- The truncation sum over all of `H` is the inertia-cardinality constant
plus the Herbrand depth sum over `H_0`. -/
theorem sum_min_depth_eq_card_add_truncated (n : ℕ) [Fintype G] :
    (∑ τ : H,
        (WithTop.untopD (α := ℕ) 0
          (min (D.depth (τ : G)) (WithTop.some (n + 1))) : ℝ)) =
      D.depthRamificationIndex H +
        ∑ τ : (D.depthLowerFiltration H).lower 0,
          ((RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.truncatedLowerDepth (D.depthLowerFiltration H)) n τ : ℝ) := by
  classical
  let F := D.depthLowerFiltration H
  let p : H → Prop := fun τ => τ ∈ F.lower 0
  let f : H → ℝ := fun τ =>
    (WithTop.untopD (α := ℕ) 0
      (min (D.depth (τ : G)) (WithTop.some (n + 1))) : ℝ)
  have hout : ∀ τ ∈ (Finset.univ : Finset H), τ ∉ Finset.univ.filter p → f τ = 0 := by
    intro τ _ hτ
    have hnot : τ ∉ F.lower 0 := by simpa [p] using hτ
    have hzero : D.depth (τ : G) = (0 : ℕ) := by
      simpa [F] using D.depth_eq_zero_of_not_mem_lower_zero H τ hnot
    simp [f, hzero]
  calc
    (∑ τ : H,
        (WithTop.untopD (α := ℕ) 0
          (min (D.depth (τ : G)) (WithTop.some (n + 1))) : ℝ)) =
        ∑ τ : H, f τ := rfl
    _ = ∑ τ ∈ Finset.univ.filter p, f τ :=
      (Finset.sum_subset (Finset.filter_subset _ _) hout).symm
    _ = ∑ τ : F.lower 0, f (τ : H) := by
      apply Finset.sum_subtype
      intro τ
      simp [p]
    _ = ∑ τ : F.lower 0,
        ((1 : ℝ) + ((RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.truncatedLowerDepth F) n τ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro τ _
      dsimp [f, F]
      exact_mod_cast (by
        simpa [add_comm] using (D.truncatedLowerDepth_add_one H n τ).symm)
    _ = D.depthRamificationIndex H +
        ∑ τ : F.lower 0, ((RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.truncatedLowerDepth F) n τ : ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ _τ : F.lower 0, (1 : ℝ)) =
            (Fintype.card (F.lower 0) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        _ = (D.depthRamificationIndex H : ℝ) :=
          congrArg (fun k : ℕ => (k : ℝ))
            (Fintype.card_eq_nat_card (α := F.lower 0))

/-- The natural-argument calculation at the heart of Herbrand's theorem.
For a maximal representative of depth `n + 1`, the normalized fibre
average minus one is the Herbrand function of `H` at `n`.

The proof uses the maximal-representative fibre-sum identity and exactly the
integral Herbrand sum formula. -/
theorem quotientFiberAverage_sub_one_eq_herbrandValueNat_of_depth_eq_succ
    [Fintype G] {q : G ⧸ H} (hq : q ≠ 1) {σ : G}
    (hσq : QuotientGroup.mk' H σ = q)
    (hmax : ∀ γ : G, QuotientGroup.mk' H γ = q →
      D.depth γ ≤ D.depth σ)
    (n : ℕ) (hdepth : D.depth σ = WithTop.some (n + 1)) :
    D.quotientFiberAverage H hq - 1 =
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat (D.depthLowerFiltration H)) n := by
  classical
  let F := D.depthLowerFiltration H
  let f : WithTop ℕ → ℝ := fun d =>
    (WithTop.untopD (α := ℕ) 0 d : ℝ)
  have hsum0 := D.sum_depth_quotientFiber_eq_sum_min_of_maximal_representative
    H f (σ := σ) (by
      intro γ hγ
      exact hmax γ (hγ.trans hσq))
  rw [hσq] at hsum0
  have hsumLeft :
      (∑ γ : QuotientFiber H q, f (D.depth (γ : G))) =
        ∑ γ : QuotientFiber H q,
          (D.quotientFiberDepth H hq γ : ℝ) := by
    apply Finset.sum_congr rfl
    intro γ _
    dsimp [f]
    rw [← D.coe_quotientFiberDepth H hq γ]
    exact_mod_cast WithTop.untopD_coe 0 (D.quotientFiberDepth H hq γ)
  have hsum :
      (∑ γ : QuotientFiber H q,
          (D.quotientFiberDepth H hq γ : ℝ)) =
        ∑ τ : H,
          (WithTop.untopD (α := ℕ) 0
            (min (D.depth (τ : G)) (WithTop.some (n + 1))) : ℝ) := by
    rw [← hsumLeft, hsum0]
    apply Finset.sum_congr rfl
    intro τ _
    simp only [f, hdepth]
  have hdecomp := D.sum_min_depth_eq_card_add_truncated H n
  rw [← hsum] at hdecomp
  rw [quotientFiberAverage, hdecomp]
  rw [show (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat (D.depthLowerFiltration H)) n =
      (∑ τ : (D.depthLowerFiltration H).lower 0,
          ((RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.truncatedLowerDepth (D.depthLowerFiltration H)) n τ : ℝ)) /
        D.depthRamificationIndex H by
    simpa [depthRamificationIndex] using
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat_eq_depth_sum (D.depthLowerFiltration H) n]
  have he : (D.depthRamificationIndex H : ℝ) ≠ 0 := by
    exact_mod_cast
      (show 0 < Nat.card ((D.depthLowerFiltration H).lower 0) from
        Finite.card_pos).ne'
  field_simp
  ring

/-- The missing `m = 0` endpoint of the fibre calculation.  If a maximal
representative has depth zero, every element of its fibre has depth zero,
so the actual normalized average is zero. -/
theorem quotientFiberAverage_eq_zero_of_maximal_depth_zero
    [Fintype G] {q : G ⧸ H} (hq : q ≠ 1) {σ : G}
    (hmax : ∀ γ : G, QuotientGroup.mk' H γ = q →
      D.depth γ ≤ D.depth σ)
    (hdepth : D.depth σ = WithTop.some 0) :
    D.quotientFiberAverage H hq = 0 := by
  classical
  have hzero : ∀ γ : QuotientFiber H q,
      D.quotientFiberDepth H hq γ = 0 := by
    intro γ
    have hle : D.depth (γ : G) ≤ WithTop.some 0 := by
      rw [← hdepth]
      exact hmax γ γ.property
    have hdepthγ : D.depth (γ : G) = WithTop.some 0 :=
      le_antisymm hle (bot_le : WithTop.some 0 ≤ D.depth (γ : G))
    apply WithTop.coe_injective
    calc
      WithTop.some (D.quotientFiberDepth H hq γ) = D.depth (γ : G) :=
        D.coe_quotientFiberDepth H hq γ
      _ = WithTop.some 0 := hdepthγ
  simp [quotientFiberAverage, hzero]

/-- The fibre-average identity in the exact form used in the Herbrand quotient theorem.
The finite natural depth of the chosen maximal representative is used in the
real argument `m - 1`, including the endpoint `m = 0`. -/
theorem quotientFiberAverage_sub_one_eq_herbrandFunction_of_maximal
    [Fintype G] {q : G ⧸ H} (hq : q ≠ 1) {σ : G}
    (hσq : QuotientGroup.mk' H σ = q)
    (hmax : ∀ γ : G, QuotientGroup.mk' H γ = q →
      D.depth γ ≤ D.depth σ) :
    D.quotientFiberAverage H hq - 1 =
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (D.depthLowerFiltration H))
        ((D.quotientFiberDepth H hq ⟨σ, hσq⟩ : ℝ) - 1) := by
  by_cases hm : D.quotientFiberDepth H hq ⟨σ, hσq⟩ = 0
  · have hdepth : D.depth σ = WithTop.some 0 := by
      calc
        D.depth σ = WithTop.some (D.quotientFiberDepth H hq ⟨σ, hσq⟩) :=
          (D.coe_quotientFiberDepth H hq ⟨σ, hσq⟩).symm
        _ = WithTop.some 0 := congrArg WithTop.some hm
    have havg := D.quotientFiberAverage_eq_zero_of_maximal_depth_zero
      H hq hmax hdepth
    rw [havg, hm]
    norm_num
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hdepth : D.depth σ = WithTop.some (n + 1) := by
      calc
        D.depth σ = WithTop.some (D.quotientFiberDepth H hq ⟨σ, hσq⟩) :=
          (D.coe_quotientFiberDepth H hq ⟨σ, hσq⟩).symm
        _ = WithTop.some n.succ := congrArg WithTop.some hn
        _ = WithTop.some (n + 1) := by rw [Nat.succ_eq_add_one]
    have hnat :=
      D.quotientFiberAverage_sub_one_eq_herbrandValueNat_of_depth_eq_succ
        H hq hσq hmax n hdepth
    rw [hn]
    norm_num
    exact hnat

/-- Natural-threshold form of the last equivalence in the proof of
Herbrand's theorem.  The normalized average is at least `η_H(s) + 1`
exactly when its quotient fibre contains an element of depth at least
`s + 1`. -/
theorem quotientFiberAverage_ge_herbrandFunction_add_one_iff_exists
    [Fintype G] {q : G ⧸ H} (hq : q ≠ 1) {σ : G}
    (hσq : QuotientGroup.mk' H σ = q)
    (hmax : ∀ γ : G, QuotientGroup.mk' H γ = q →
      D.depth γ ≤ D.depth σ)
    (s : ℕ) :
    D.quotientFiberAverage H hq ≥
        (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (D.depthLowerFiltration H)) s + 1 ↔
      ∃ γ : QuotientFiber H q,
        WithTop.some (s + 1) ≤ D.depth (γ : G) := by
  let F := D.depthLowerFiltration H
  let m := D.quotientFiberDepth H hq ⟨σ, hσq⟩
  have hdepth : D.depth σ = WithTop.some m :=
    (D.coe_quotientFiberDepth H hq ⟨σ, hσq⟩).symm
  have havg := D.quotientFiberAverage_sub_one_eq_herbrandFunction_of_maximal
    H hq hσq hmax
  have hfiber :
      (∃ γ : QuotientFiber H q,
          WithTop.some (s + 1) ≤ D.depth (γ : G)) ↔
        WithTop.some (s + 1) ≤ D.depth σ := by
    constructor
    · rintro ⟨γ, hγ⟩
      exact hγ.trans (hmax γ γ.property)
    · intro hσ
      exact ⟨⟨σ, hσq⟩, hσ⟩
  have hrealNat :
      (s : ℝ) ≤ (m : ℝ) - 1 ↔ s + 1 ≤ m := by
    constructor
    · intro h
      have h' : (s + 1 : ℕ) ≤ (m : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h'
    · intro h
      have h' : (s + 1 : ℝ) ≤ m := by exact_mod_cast h
      linarith
  have hwithTopNat :
      WithTop.some (s + 1) ≤ D.depth σ ↔ s + 1 ≤ m := by
    rw [hdepth]
    exact WithTop.coe_le_coe
  rw [hfiber, hwithTopNat, ← hrealNat]
  change D.quotientFiberAverage H hq ≥ (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction F) s + 1 ↔ _
  rw [show D.quotientFiberAverage H hq ≥ (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction F) s + 1 ↔
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction F) s ≤ D.quotientFiberAverage H hq - 1 by
    constructor <;> intro h <;> linarith]
  rw [havg]
  exact (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_strictMono F).le_iff_le

/-- Every nontrivial quotient fibre admits a maximal representative for
which the Herbrand fibre-average identity holds. -/
theorem exists_maximal_representative_quotientFiberAverage [Fintype G]
    {q : G ⧸ H} (hq : q ≠ 1) :
    ∃ σ : G, ∃ hσq : QuotientGroup.mk' H σ = q,
      (∀ γ : G, QuotientGroup.mk' H γ = q →
        D.depth γ ≤ D.depth σ) ∧
      D.quotientFiberAverage H hq - 1 =
        (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (D.depthLowerFiltration H))
          ((D.quotientFiberDepth H hq ⟨σ, hσq⟩ : ℝ) - 1) := by
  obtain ⟨σ, hσq, hmax⟩ := D.exists_maximal_depth_representative H hq
  refine ⟨σ, hσq, hmax, ?_⟩
  exact D.quotientFiberAverage_sub_one_eq_herbrandFunction_of_maximal
    H hq hσq hmax

end NonarchimedeanDepth
end HerbrandGroupTheory
end RamificationTheory.DiscreteValuationField
