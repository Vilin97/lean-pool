/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointSectionSelection
public import Mathlib.Tactic

/-!
# One-point pole-order semigroups
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section

/-- The elements at most `n` missing from an additive submonoid of `ℕ`. -/
noncomputable def addSubmonoidGapsBelowOrAt
    (H : AddSubmonoid ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun i => i ∉ H)

private noncomputable def addSubmonoidMembersBelowOrAt
    (H : AddSubmonoid ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun i => i ∈ H)

private noncomputable def addSubmonoidPositiveMembersBelow
    (H : AddSubmonoid ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun i => i + 1 ∈ H)

/-- Reflection through `i ↦ n - i` proves the elementary conductor bound:
if at most `g` elements up to `n` are gaps and `n ≥ 2g`, then `n` belongs to
the additive submonoid. -/
theorem addSubmonoid_mem_of_card_gaps_le
    (H : AddSubmonoid ℕ) (n g : ℕ)
    (hgaps : (addSubmonoidGapsBelowOrAt H n).card ≤ g)
    (hlarge : 2 * g ≤ n) :
    n ∈ H := by
  classical
  by_contra hn
  let members := addSubmonoidMembersBelowOrAt H n
  let gaps := addSubmonoidGapsBelowOrAt H n
  have hreflect : members.card ≤ gaps.card := by
    apply Finset.card_le_card_of_injOn (fun i => n - i)
    · intro i hi
      have hi' : i < n + 1 ∧ i ∈ H := by
        have hiFin : i ∈ addSubmonoidMembersBelowOrAt H n := hi
        simpa only [addSubmonoidMembersBelowOrAt, Finset.mem_filter,
          Finset.mem_range] using hiFin
      have hreflected : n - i ∉ H := by
        intro hreflected
        have hsum : n - i + i = n :=
          Nat.sub_add_cancel (Nat.le_of_lt_succ hi'.1)
        apply hn
        rw [← hsum]
        exact H.add_mem hreflected hi'.2
      have hreflectedRange : n - i < n + 1 := Nat.sub_lt_succ n i
      have hreflectedFin : n - i ∈ addSubmonoidGapsBelowOrAt H n := by
        rw [addSubmonoidGapsBelowOrAt, Finset.mem_filter, Finset.mem_range]
        exact ⟨hreflectedRange, hreflected⟩
      exact hreflectedFin
    · intro i hi j hj heq
      have hi' : i < n + 1 ∧ i ∈ H := by
        have hiFin : i ∈ addSubmonoidMembersBelowOrAt H n := hi
        simpa only [addSubmonoidMembersBelowOrAt, Finset.mem_filter,
          Finset.mem_range] using hiFin
      have hj' : j < n + 1 ∧ j ∈ H := by
        have hjFin : j ∈ addSubmonoidMembersBelowOrAt H n := hj
        simpa only [addSubmonoidMembersBelowOrAt, Finset.mem_filter,
          Finset.mem_range] using hjFin
      have hiSum : n - i + i = n :=
        Nat.sub_add_cancel (Nat.le_of_lt_succ hi'.1)
      have hjSum : n - j + j = n :=
        Nat.sub_add_cancel (Nat.le_of_lt_succ hj'.1)
      change n - i = n - j at heq
      apply Nat.add_left_cancel (n := n - j)
      calc
        (n - j) + i = (n - i) + i := by rw [heq]
        _ = n := hiSum
        _ = (n - j) + j := hjSum.symm
  have hpartition : members.card + gaps.card = n + 1 := by
    simpa only [members, gaps, addSubmonoidMembersBelowOrAt,
      addSubmonoidGapsBelowOrAt, Finset.card_range] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.range (n + 1)) (p := fun i => i ∈ H))
  have hgap : gaps.card ≤ g := by
    simpa only [gaps] using hgaps
  omega

private theorem one_add_card_positive_members_eq_card_members
    (H : AddSubmonoid ℕ) : ∀ n : ℕ,
    1 + (addSubmonoidPositiveMembersBelow H n).card =
      (addSubmonoidMembersBelowOrAt H n).card := by
  classical
  intro n
  induction n with
  | zero =>
      change 1 = ((Finset.range 1).filter (fun i => i ∈ H)).card
      simp only [Finset.range_one, Finset.filter_singleton]
      rw [ite_eq_left H.zero_mem]
      simp
  | succ n ih =>
      by_cases hn : n + 1 ∈ H
      · have hpositive :
            (addSubmonoidPositiveMembersBelow H (n + 1)).card =
              (addSubmonoidPositiveMembersBelow H n).card + 1 := by
          rw [addSubmonoidPositiveMembersBelow, Finset.range_add_one,
            Finset.filter_insert, ite_eq_left hn, Finset.card_insert_of_notMem]
          · rfl
          · simp
        have hmembers :
            (addSubmonoidMembersBelowOrAt H (n + 1)).card =
              (addSubmonoidMembersBelowOrAt H n).card + 1 := by
          rw [addSubmonoidMembersBelowOrAt]
          rw [show n + 1 + 1 = (n + 1) + 1 by omega,
            Finset.range_add_one, Finset.filter_insert, ite_eq_left hn,
            Finset.card_insert_of_notMem]
          · rfl
          · simp
        rw [hpositive, hmembers]
        omega
      · have hpositive :
            (addSubmonoidPositiveMembersBelow H (n + 1)).card =
              (addSubmonoidPositiveMembersBelow H n).card := by
          rw [addSubmonoidPositiveMembersBelow, Finset.range_add_one,
            Finset.filter_insert, ite_eq_right hn,
            addSubmonoidPositiveMembersBelow]
        have hmembers :
            (addSubmonoidMembersBelowOrAt H (n + 1)).card =
              (addSubmonoidMembersBelowOrAt H n).card := by
          rw [addSubmonoidMembersBelowOrAt]
          rw [show n + 1 + 1 = (n + 1) + 1 by omega,
            Finset.range_add_one, Finset.filter_insert, ite_eq_right hn,
            addSubmonoidMembersBelowOrAt]
        rw [hpositive, hmembers]
        exact ih

private theorem card_gaps_le_of_card_positive_members_ge
    (H : AddSubmonoid ℕ) (n g : ℕ)
    (hmembers : n - g ≤
      (addSubmonoidPositiveMembersBelow H n).card)
    (hgn : g ≤ n) :
    (addSubmonoidGapsBelowOrAt H n).card ≤ g := by
  classical
  let members := addSubmonoidMembersBelowOrAt H n
  let gaps := addSubmonoidGapsBelowOrAt H n
  have hmemberCard : 1 +
      (addSubmonoidPositiveMembersBelow H n).card = members.card := by
    simpa only [members] using one_add_card_positive_members_eq_card_members H n
  have hpartition : members.card + gaps.card = n + 1 := by
    simpa only [members, gaps, addSubmonoidMembersBelowOrAt,
      addSubmonoidGapsBelowOrAt, Finset.card_range] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.range (n + 1)) (p := fun i => i ∈ H))
  change gaps.card ≤ g
  omega

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance onePointPoleSemigroupConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance onePointPoleSemigroupConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Exact pole orders at `P` of nonzero functions regular away from `P`. -/
def onePointPoleOrderSemigroup
    (P : FiniteExtensionPlace K L) : AddSubmonoid ℕ where
  carrier := {n | ∃ x : L, x ≠ 0 ∧
    finiteExtensionPrincipalDivisor K L x P = -(n : ℤ) ∧
    ∀ v, v ≠ P → 0 ≤ finiteExtensionPrincipalDivisor K L x v}
  zero_mem' := by
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · rw [finiteExtensionPrincipalDivisor_one K L]
      simp
    · intro v hv
      rw [finiteExtensionPrincipalDivisor_one K L]
      simp
  add_mem' := by
    rintro m n ⟨x, hx0, hxP, hxAway⟩ ⟨y, hy0, hyP, hyAway⟩
    refine ⟨x * y, mul_ne_zero hx0 hy0, ?_, ?_⟩
    · rw [finiteExtensionPrincipalDivisor_mul K L x y hx0 hy0,
        Finsupp.add_apply, hxP, hyP]
      push_cast
      ring
    · intro v hv
      rw [finiteExtensionPrincipalDivisor_mul K L x y hx0 hy0,
        Finsupp.add_apply]
      exact add_nonneg (hxAway v hv) (hyAway v hv)

omit [Fintype K] in
omit [DecidableEq K] in
@[simp]
theorem mem_onePointPoleOrderSemigroup_iff
    (P : FiniteExtensionPlace K L) (n : ℕ) :
    n ∈ onePointPoleOrderSemigroup K L P ↔
      ∃ x : L, x ≠ 0 ∧
        finiteExtensionPrincipalDivisor K L x P = -(n : ℤ) ∧
        ∀ v, v ≠ P → 0 ≤ finiteExtensionPrincipalDivisor K L x v :=
  Iff.rfl

/-- A positive exact pole order is equivalent to strict growth at that level. -/
theorem succ_mem_onePointPoleOrderSemigroup_iff_lt
    (P : FiniteExtensionPlace K L) (n : ℕ) :
    n + 1 ∈ onePointPoleOrderSemigroup K L P ↔
      finiteExtensionOnePointRiemannSpace K L P n <
        finiteExtensionOnePointRiemannSpace K L P (n + 1) := by
  constructor
  · rintro ⟨x, hx0, hxP, hxAway⟩
    have hxSucc : x ∈ finiteExtensionOnePointRiemannSpace K L P (n + 1) := by
      rw [mem_finiteExtensionOnePointRiemannSpace_iff]
      exact Or.inr ⟨hx0, by rw [hxP], hxAway⟩
    have hxNot : x ∉ finiteExtensionOnePointRiemannSpace K L P n := by
      intro hx
      rcases (mem_finiteExtensionOnePointRiemannSpace_iff K L P n x).mp hx with
        rfl | ⟨_, hxLower, _⟩
      · exact hx0 rfl
      · rw [hxP] at hxLower
        omega
    apply lt_of_le_of_ne (finiteExtensionOnePointRiemannSpace_mono K L P (by omega))
    intro heq
    apply hxNot
    rw [heq]
    exact hxSucc
  · intro hstrict
    obtain ⟨x, hxSucc, hxNot⟩ := SetLike.exists_of_lt hstrict
    obtain ⟨hx0, hxP⟩ :=
      onePointRiemannSpace_order_eq_neg_succ_of_mem_not_mem K L P n hxSucc hxNot
    rcases (mem_finiteExtensionOnePointRiemannSpace_iff K L P (n + 1) x).mp
        hxSucc with rfl | ⟨_, _, hxAway⟩
    · exact (hx0 rfl).elim
    · exact ⟨x, hx0, hxP, hxAway⟩

/-- A degree-one place whose one-point spaces satisfy the coarse Riemann lower
bound has every pole order at least twice the genus budget. -/
theorem mem_onePointPoleOrderSemigroup_of_two_mul_le
    (P : FiniteExtensionPlace K L)
    (hdegree : finiteExtensionPlaceDegree K L P = 1)
    (hconstants : algebraicClosure K L = ⊥)
    (g n : ℕ)
    (hlower : ∀ m : ℕ,
      m + 1 ≤ Module.finrank K
        (finiteExtensionOnePointRiemannSpace K L P m) + g)
    (hlarge : 2 * g ≤ n) :
    n ∈ onePointPoleOrderSemigroup K L P := by
  have hgn : g ≤ n := by omega
  have hlower' : 1 + finiteExtensionPlaceDegree K L P * (n - g) ≤
      Module.finrank K (finiteExtensionOnePointRiemannSpace K L P n) := by
    have h := hlower n
    rw [hdegree]
    simp only [one_mul]
    omega
  have hstrict : n - g ≤
      (strictFiltrationLevels
        (fun m => finiteExtensionOnePointRiemannSpace K L P m) n).card :=
    le_card_onePointStrictLevels_of_finrank_lower K L P n (n - g)
      hconstants hlower'
  have hstrictEq :
      strictFiltrationLevels
          (fun m => finiteExtensionOnePointRiemannSpace K L P m) n =
        addSubmonoidPositiveMembersBelow
          (onePointPoleOrderSemigroup K L P) n := by
    classical
    ext i
    simp only [strictFiltrationLevels, addSubmonoidPositiveMembersBelow,
      Finset.mem_filter, Finset.mem_range]
    rw [succ_mem_onePointPoleOrderSemigroup_iff_lt K L P i]
  have hpositive : n - g ≤
      (addSubmonoidPositiveMembersBelow
        (onePointPoleOrderSemigroup K L P) n).card := by
    rw [← hstrictEq]
    exact hstrict
  apply addSubmonoid_mem_of_card_gaps_le
    (onePointPoleOrderSemigroup K L P) n g
  · exact card_gaps_le_of_card_positive_members_ge
      (onePointPoleOrderSemigroup K L P) n g hpositive hgn
  · exact hlarge

end

end BGS.HasseWeil
