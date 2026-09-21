/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.CardinalControl

/-!
# The regular cardinal used for bookkeeping

We use `θ = 2^𝔠` for the uniform stage bound and its successor `κ = θ⁺`
for the recursion.  The identities below are precisely the cardinal arithmetic
used in the manuscript.
-/

namespace ScottishBook155

open scoped Cardinal

universe u

/-- Uniform cardinal bound for every Banach stage. -/
def stageCardinal : Cardinal := 2 ^ Cardinal.continuum

/-- Regular successor cardinal indexing the final recursion. -/
noncomputable def recursionCardinal : Cardinal := Order.succ stageCardinal

theorem aleph0_le_stageCardinal : Cardinal.aleph0 ≤ stageCardinal := by
  exact Cardinal.aleph0_lt_continuum.le.trans
    (Cardinal.cantor Cardinal.continuum).le

theorem real_mk_le_stageCardinal : Cardinal.mk ℝ ≤ stageCardinal := by
  rw [Cardinal.mk_real]
  exact (Cardinal.cantor Cardinal.continuum).le

theorem stageCardinal_power_aleph0 :
    stageCardinal ^ Cardinal.aleph0 = stageCardinal := by
  rw [stageCardinal, ← Cardinal.power_mul, Cardinal.continuum_mul_aleph0]

theorem stageCardinal_lt_recursionCardinal :
    stageCardinal < recursionCardinal := by
  rw [recursionCardinal]
  exact Order.lt_succ _

theorem recursionCardinal_isRegular : recursionCardinal.IsRegular :=
  Cardinal.isRegular_succ aleph0_le_stageCardinal

theorem aleph0_lt_recursionCardinal :
    Cardinal.aleph0 < recursionCardinal :=
  aleph0_le_stageCardinal.trans_lt stageCardinal_lt_recursionCardinal

/-- A same-universe well-ordered type of recursion indices. -/
abbrev RecursionIndex := recursionCardinal.ord.ToType

noncomputable instance recursionIndexNonempty :
    Nonempty (RecursionIndex.{u}) := by
  apply Cardinal.mk_ne_zero_iff.mp
  rw [Cardinal.mk_ord_toType]
  exact ne_of_gt (Cardinal.aleph0_pos.trans aleph0_lt_recursionCardinal)

noncomputable instance recursionIndexOrderBot :
    OrderBot (RecursionIndex.{u}) :=
  WellFoundedLT.toOrderBot _

noncomputable instance recursionIndexNoMaxOrder :
    NoMaxOrder (RecursionIndex.{u}) :=
  Cardinal.noMaxOrder aleph0_lt_recursionCardinal.le

theorem mk_recursionIndex : Cardinal.mk RecursionIndex = recursionCardinal := by
  exact Cardinal.mk_ord_toType recursionCardinal

theorem initialSegment_mk_lt (i : RecursionIndex) :
    Cardinal.mk (Set.Iio i) < recursionCardinal := by
  exact Cardinal.mk_Iio_toType_ord_lt i

theorem initialSegment_mk_le_stageCardinal (i : RecursionIndex) :
    Cardinal.mk (Set.Iio i) ≤ stageCardinal := by
  have h := initialSegment_mk_lt i
  change Cardinal.mk (Set.Iio i) < Order.succ stageCardinal at h
  exact Order.lt_succ_iff.mp h

theorem initialClosedSegment_mk_le (i : RecursionIndex) :
    Cardinal.mk (Set.Iic i) ≤ stageCardinal := by
  have hiio : Cardinal.mk (Set.Iio i) ≤ stageCardinal := by
    have h := initialSegment_mk_lt i
    change Cardinal.mk (Set.Iio i) < Order.succ stageCardinal at h
    exact Order.lt_succ_iff.mp h
  let e : Set.Iic i ↪ Option (Set.Iio i) :=
    ⟨fun x => if h : x.1 < i then some ⟨x.1, h⟩ else none, by
      intro x y hxy
      by_cases hx : x.1 < i
      · by_cases hy : y.1 < i
        · simp only [hx, hy, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hxy
          exact Subtype.ext hxy
        · simp only [hx, hy, ↓reduceDIte] at hxy
          cases hxy
      · by_cases hy : y.1 < i
        · simp only [hx, hy, ↓reduceDIte] at hxy
          cases hxy
        · have hxi : x.1 = i := le_antisymm x.2 (le_of_not_gt hx)
          have hyi : y.1 = i := le_antisymm y.2 (le_of_not_gt hy)
          exact Subtype.ext (hxi.trans hyi.symm)⟩
  calc
    Cardinal.mk (Set.Iic i) ≤ Cardinal.mk (Option (Set.Iio i)) :=
      Cardinal.mk_le_of_injective e.injective
    _ = Cardinal.mk (Set.Iio i) + 1 := Cardinal.mk_option
    _ ≤ max (max (Cardinal.mk (Set.Iio i)) 1) Cardinal.aleph0 :=
      Cardinal.add_le_max _ _
    _ ≤ stageCardinal := max_le
      (max_le hiio (Cardinal.one_le_aleph0.trans aleph0_le_stageCardinal))
      aleph0_le_stageCardinal

/-- Every strict tail of the recursion order still has full cardinality. -/
theorem tail_mk (i : RecursionIndex) :
    Cardinal.mk (Set.Ioi i) = recursionCardinal := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans_eq mk_recursionIndex
  · by_contra h
    have htail_lt : Cardinal.mk (Set.Ioi i) < recursionCardinal :=
      lt_of_not_ge h
    have htail : Cardinal.mk (Set.Ioi i) ≤ stageCardinal := by
      change Cardinal.mk (Set.Ioi i) < Order.succ stageCardinal at htail_lt
      exact Order.lt_succ_iff.mp htail_lt
    have hsum : Cardinal.mk (Set.Iic i) + Cardinal.mk (Set.Ioi i) ≤
        stageCardinal := by
      exact (Cardinal.add_le_max _ _).trans
        (max_le (max_le (initialClosedSegment_mk_le i) htail)
          aleph0_le_stageCardinal)
    have hlex : Cardinal.mk (Set.Iic i ⊕ₗ Set.Ioi i) ≤ stageCardinal := by
      change Cardinal.mk (Set.Iic i ⊕ Set.Ioi i) ≤ stageCardinal
      simpa [Cardinal.mk_sum, Cardinal.lift_id] using hsum
    have hwhole : recursionCardinal ≤ stageCardinal := by
      calc
        recursionCardinal = Cardinal.mk RecursionIndex := mk_recursionIndex.symm
        _ = Cardinal.mk (Set.Iic i ⊕ₗ Set.Ioi i) :=
          (Cardinal.mk_congr (OrderIso.sumLexIicIoi i).toEquiv).symm
        _ ≤ stageCardinal := hlex
    exact (not_le_of_gt stageCardinal_lt_recursionCardinal) hwhole

/-- Any inhabited type within the uniform stage bound admits a recursion-indexed
enumeration, with repetitions allowed. -/
noncomputable def stageEnumeration {X : Type} [Zero X]
    (hX : Cardinal.mk X ≤ stageCardinal) : RecursionIndex.{0} → X := by
  classical
  have hcard : Cardinal.mk X ≤ Cardinal.mk (RecursionIndex.{0}) := by
    calc
      Cardinal.mk X ≤ stageCardinal := hX
      _ ≤ recursionCardinal := stageCardinal_lt_recursionCardinal.le
      _ = Cardinal.mk (RecursionIndex.{0}) := mk_recursionIndex.symm
  let e : X ↪ RecursionIndex.{0} :=
    Classical.choice (Cardinal.lift_mk_le'.mp (by simpa using hcard))
  let ee : X ≃ Set.range e := Equiv.ofInjective e e.injective
  exact fun i => if h : i ∈ Set.range e then
    ee.symm ⟨i, h⟩ else 0

theorem stageEnumeration_surjective {X : Type} [Zero X]
    (hX : Cardinal.mk X ≤ stageCardinal) :
    Function.Surjective (stageEnumeration hX) := by
  classical
  unfold stageEnumeration
  dsimp only
  let e : X ↪ RecursionIndex.{0} := Classical.choice
    (Cardinal.lift_mk_le'.mp (by
      simpa using hX.trans stageCardinal_lt_recursionCardinal.le |>.trans_eq
        mk_recursionIndex.symm))
  let ee : X ≃ Set.range e := Equiv.ofInjective e e.injective
  intro x
  refine ⟨e x, ?_⟩
  change (if h : e x ∈ Set.range e then
    ee.symm ⟨e x, h⟩ else 0) = x
  simp [ee]

end ScottishBook155
