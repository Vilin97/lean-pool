/-
Copyright (c) 2026 Luka Opravš. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luka Opravš
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
# Pólya's enumeration theorem

We interpret functions `X → Y` as colorings of `X` with colors in `Y`. The element `x : X` is
colored with color `(f x) : Y` in the coloring `f : X → Y`.

We interpret `g : G` as a transformation that permutes the elements of `X` into an equivalent
configuration. If we color the elements of `X` with `f : X → Y` and then permute `X` with `g : G`,
we obtain an equivalent configuration which now has the coloring `x ↦ (f (g⁻¹ • x))`. Note that
`g⁻¹` appears in the definition of the new coloring because the color of the element `x` in the
new permuted configuration must match the color of its preimage `g⁻¹ • x` in the original
configuration. Thus, for any `g : G`, we consider the colorings `f` and `x ↦ (f (g⁻¹ • x))` to
be equivalent.

Given a group action of `G` on `X`, we define an instance of group action of `G` on `X → Y`,
which transforms colorings into equivalent colorings. This group action induces an equivalence
relation defined by `f₁ ∼ f₂ ↔ ∃ g, f₁ = g • f₂`. Two colorings are equivalent when one can be
transformed into the other by some element of `G`. The quotient of `X → Y` by this relation
contains the orbits (equivalence classes) of equivalent colorings. The number of distinct
colorings is the cardinality of this set.

We define a notion of cycles for elements in the group `G` acting on `X`. Every `g : G` induces
a permutation of `X` through its action. The cycles of `g : G` are defined as the equivalence
classes of `X` quotiented by the equivalence relation of being in the same cycle:
`x₁ ∼ x₂ ↔ ∃ k : ℤ, (permutation of g)ᵏ x₁ = x₂`.

We prove *Pólya's enumeration theorem* and its commonly used variant, in which the sum ranges
over the possible numbers of cycles instead of the elements of the group `G`.

For additional information, refer to
<https://en.wikipedia.org/wiki/P%C3%B3lya_enumeration_theorem>.
-/

universe u v w

namespace LeanPool.PolyaEnumerationTheorem

namespace DistinctColorings

variable (X : Type u) (Y : Type v) (G : Type w) [Group G] [MulAction G X]

/-- Group action of `G` on `X → Y` with `g • f ↦ (x ↦ f (g⁻¹ • x))`. -/
instance MulActionColorings : MulAction G (X → Y) where
  smul := fun g f x ↦ f (g⁻¹ • x)
  one_smul := by
    intro f
    ext x
    change f ((1 : G)⁻¹ • x) = f x
    rw [inv_one, one_smul]
  mul_smul := by
    intro g g' f
    ext x
    change f ((g * g')⁻¹ • x) = f (g'⁻¹ • g⁻¹ • x)
    rw [mul_inv_rev, mul_smul]

/-- The relation defined by `f₁ ∼ f₂ ↔ ∃ g, f₁ = g • f₂` is decidable. This instance enables
    inference of `Fintype (Quotient (MulAction.orbitRel G (X → Y)))` and guarantees that the
    number of distinct colorings can be computed when `X`, `Y` and `G` are finite and `X` and `Y`
    have decidable equalities. -/
instance instDecidableRelForallEquivOfDecidableEqOfFintypeLeanPool
    [Fintype X] [DecidableEq Y] [Fintype G] :
    DecidableRel (@HasEquiv.Equiv (X → Y)
      (@instHasEquivOfSetoid (X → Y) (MulAction.orbitRel G (X → Y)))) :=
  fun f₁ f₂ ↦
    if h : ∃ g, g • f₂ = f₁
    then isTrue h
    else isFalse h

/-- Number of distinct colorings is the cardinality of the quotient of `X → Y` by the equivalence
    relation `f₁ ∼ f₂ ↔ ∃ g, f₁ = g • f₂`. -/
abbrev numDistinctColorings [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] : ℕ :=
  Fintype.card (Quotient (MulAction.orbitRel G (X → Y)))

end DistinctColorings


namespace CyclesOfGroupElements

variable (X : Type u)

/-- The cycles of `g : G` are defined as the quotient of `X` by the equivalence relation of being
    in the same cycle of `g`: `x₁ ∼ x₂ ↔ ∃ k : ℤ, (permutation of g)ᵏ x₁ = x₂`. Cycles are
    unordered, and cycles of length 1 are also considered proper cycles. This definition of
    cycles differs from the standard definition of cycles in Mathlib, because cycles of length 1
    are recognized as proper cycles. -/
abbrev CyclesOfGroup {G : Type v} [Group G] [MulAction G X] (g : G) : Type u :=
  Quotient (Equiv.Perm.SameCycle.setoid (@MulAction.toPerm _ X _ _ g))

/-- Instance of `DecidableRel` for relation of being in the same cycle. Enables deciding for
    arbitrary elements of `X` and arbitrary permutation of `X` if the elements are in the same
    cycle of the permutation. This instance enables inference of `Fintype` and `DecidableEq` for
    `CyclesOfGroup` when `X` is finite and has decidable equality. -/
instance instDecidableRelEquivOfFintypeOfDecidableEqLeanPool
    {f : Equiv.Perm X} [Fintype X] [DecidableEq X] :
    DecidableRel (@HasEquiv.Equiv X
      (@instHasEquivOfSetoid X (Equiv.Perm.SameCycle.setoid f))) :=
  Equiv.Perm.instDecidableRelSameCycle f

/-- The number of cycles in the permutation of `g`. Cycles with only a single element are also
    counted (e.g. `c[0, 1] : Equiv.Perm (Fin 3)` has two cycles). -/
abbrev numCyclesOfGroup {G : Type v} [Group G] [MulAction G X] (g : G)
    [Fintype (CyclesOfGroup X g)] : ℕ :=
  Fintype.card (CyclesOfGroup X g)

/-- The number of elements in the group `G` that have exactly `i` cycles. -/
abbrev numGroupOfNumCycles (G : Type v) [Group G] [MulAction G X] [Fintype G]
    [∀ g : G, Fintype (CyclesOfGroup X g)] (i : ℕ) : ℕ :=
  Finset.card {g : G | numCyclesOfGroup X g = i}

end CyclesOfGroupElements


namespace Theorem

open DistinctColorings CyclesOfGroupElements

variable {X : Type u} {Y : Type v} {G : Type w} [Group G] [MulAction G X]

/-!
The proof of *Pólya's enumeration theorem* uses the set of fixed points of `g`, denoted by
`MulAction.fixedBy (X → Y) g`. This set consists of all colorings `f : X → Y` that are invariant
under the action of `g`, i.e., those satisfying `g • f = f`.
-/

/-- For any `g : G` we have: a coloring `f` is in fixed points of `g` if and only if `f` maps
    all elements in the same cycle of `g` to the same color. Only left to right implication of
    this lemma is used in the proof of *Pólya's enumeration theorem*. -/
lemma f_mem_fixedBy_iff_forall_eq_to_eq (g : G) (f : X → Y) :
    f ∈ (MulAction.fixedBy (X → Y) g) ↔ ∀ a b,
      (⟦a⟧ : Quotient (Equiv.Perm.SameCycle.setoid (MulAction.toPerm g))) = ⟦b⟧ → f a = f b := by
  have hfix_iff : f ∈ MulAction.fixedBy (X → Y) g ↔ ∀ x, f (g⁻¹ • x) = f x := by
    rw [MulAction.mem_fixedBy]
    refine ⟨fun hf x => ?_, fun hf => funext fun x => ?_⟩
    · simpa [HSMul.hSMul] using congr_fun hf x
    · simpa [HSMul.hSMul] using hf x
  rw [hfix_iff]
  constructor
  · intro h a b hab
    obtain ⟨k, hk⟩ := Quotient.exact hab
    rw [← hk]
    have hpow : ∀ k : ℤ, ((MulAction.toPerm g) ^ k) a = (g ^ k) • a := by
      intro k
      rw [← MulAction.coe_toPermHom, show ((MulAction.toPermHom G X g) ^ k) a
            = (MulAction.toPermHom G X (g ^ k)) a from by rw [map_zpow]]
      rfl
    rw [hpow]
    have h_fix_g : ∀ y, f (g • y) = f y := fun y => by
      have key := h (g • y)
      rw [← mul_smul, inv_mul_cancel, one_smul] at key
      exact key.symm
    have h_fix : ∀ (k : ℤ) (y : X), f ((g ^ k) • y) = f y := by
      intro k y
      induction k with
      | zero => simp
      | succ n hn =>
        rw [zpow_add_one,
          show g ^ (↑n : ℤ) * g = g * g ^ (↑n : ℤ) from by group, mul_smul, h_fix_g, hn]
      | pred n hn =>
        rw [zpow_sub_one,
          show g ^ (-↑n : ℤ) * g⁻¹ = g⁻¹ * g ^ (-↑n : ℤ) from by group, mul_smul, h, hn]
    exact (h_fix k a).symm
  · intro hyp x
    apply hyp
    apply Quotient.sound
    refine ⟨1, ?_⟩
    rw [zpow_one]
    change g • (g⁻¹ • x) = x
    rw [← mul_smul, mul_inv_cancel, one_smul]

/-- A function that maps a coloring from fixed points of `g` to a coloring of cycles. Colorings
    that are fixed by `g` map all elements of a cycle of `g` to the same color by lemma
    `f_mem_fixedBy_iff_forall_eq_to_eq`. We can transform each such coloring to a coloring of
    cycles of `g` by coloring each cycle with the color of its elements. -/
def cycleColoringOfFixedByColoring (g : G) (f : MulAction.fixedBy (X → Y) g) :
    (CyclesOfGroup X g) → Y :=
  Quotient.lift f (by
    intro a b hab
    exact (f_mem_fixedBy_iff_forall_eq_to_eq g f.1).1 f.2 a b (Quotient.sound hab))

/-- A function that maps a coloring of cycles to a coloring in fixed points of `g`. We color each
    element with the color of its cycle. The resulting function is in fixed points of `g` because
    `g⁻¹ • x` and `x` are in the same cycle of `g`. -/
def fixedByColoringOfCycleColoring (g : G) (f : (CyclesOfGroup X g) → Y) :
    MulAction.fixedBy (X → Y) g :=
  ⟨fun x ↦ f ⟦x⟧,
  by
    ext x
    change f ⟦g⁻¹ • x⟧ = f ⟦x⟧
    apply congrArg
    apply Quotient.sound
    refine ⟨1, ?_⟩
    rw [zpow_one]
    change g • (g⁻¹ • x) = x
    rw [← mul_smul, mul_inv_cancel, one_smul]⟩

/-- Functions `cycleColoringOfFixedByColoring` and `fixedByColoringOfCycleColoring` are
    inverses and form a bijection. -/
def equivOfFixedByColoringOfCycleColoring (g : G) :
    (CyclesOfGroup X g → Y) ≃ (MulAction.fixedBy (X → Y) g) :=
  ⟨fixedByColoringOfCycleColoring g, cycleColoringOfFixedByColoring g,
  by
    intro f
    ext x
    rcases Quotient.mk_surjective x with ⟨y, hy⟩
    rw [← hy]
    rfl,
  by
    intro _
    rfl⟩

/-- For any `g : G` we have: the number of colors raised to the power of the number of cycles of
    `g` is equal to the number of colorings that are fixed by `g`. -/
lemma forall_card_pow_numCyclesOfGroup_eq_card_fixedBy [Fintype Y]
    [∀ g : G, Fintype (MulAction.fixedBy (X → Y) g)]
    [∀ g : G, Fintype (CyclesOfGroup X g)] :
    ∀ g : G, Fintype.card Y ^ (numCyclesOfGroup X g) =
      Fintype.card (MulAction.fixedBy (X → Y) g) := by
  classical
  intro g
  unfold numCyclesOfGroup
  rw [← @Fintype.card_fun]
  apply Fintype.card_congr
  exact equivOfFixedByColoringOfCycleColoring g

variable (X : Type u) (Y : Type v) (G : Type w) [Group G] [MulAction G X] [Fintype Y] [Fintype G]
    [Fintype (Quotient (MulAction.orbitRel G (X → Y)))]

/-- A version of *Pólya's enumeration theorem* where the number of distinct colorings of `X`
    with colors in `Y`, under the group action of `G` on `X`, is multiplied by the cardinality of
    the group `G`. -/
theorem numDistinctColorings_mul_card_group_eq_sum_card_pow_numCyclesOfGroup
    [Finite (X → Y)]
    [∀ g : G, Fintype (CyclesOfGroup X g)] :
    (numDistinctColorings X Y G) * (Fintype.card G)
      = ∑ g : G, (Fintype.card Y) ^ (numCyclesOfGroup X g) := by
  haveI : ∀ g : G, Fintype (MulAction.fixedBy (X → Y) g) := fun _ => Fintype.ofFinite _
  rw [numDistinctColorings,
    Fintype.sum_congr _ _ forall_card_pow_numCyclesOfGroup_eq_card_fixedBy]
  symm
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X → Y)

/-- *Pólya's enumeration theorem*: Provides a formula for the number of distinct colorings of `X`
    with colors in `Y`, under the group action of `G` on `X`. -/
theorem numDistinctColorings_eq_sum_card_pow_numCyclesOfGroup_div_card_group
    [Finite (X → Y)]
    [∀ g : G, Fintype (CyclesOfGroup X g)] :
    numDistinctColorings X Y G =
      (∑ g : G, (Fintype.card Y) ^ (numCyclesOfGroup X g)) / (Fintype.card G) := by
  haveI : ∀ g : G, Fintype (MulAction.fixedBy (X → Y) g) := fun _ => Fintype.ofFinite _
  exact Nat.eq_div_of_mul_eq_left Fintype.card_ne_zero
    (numDistinctColorings_mul_card_group_eq_sum_card_pow_numCyclesOfGroup X Y G)

/-- A version of *Pólya's enumeration theorem* where the sum ranges over the possible numbers of
    cycles, and the number of distinct colorings of `X` with colors in `Y`, under the group action
    of `G` on `X`, is multiplied by the cardinality of the group `G`. -/
theorem numDistinctColorings_mul_card_group_eq_sum_numGroupOfNumCycles_mul_card_pow [Fintype X]
    [Finite (X → Y)]
    [∀ g : G, DecidableRel (@HasEquiv.Equiv X
      (@instHasEquivOfSetoid X (Equiv.Perm.SameCycle.setoid (MulAction.toPerm g))))] :
    (numDistinctColorings X Y G) * (Fintype.card G) =
      ∑ i : Fin (Fintype.card X + 1),
        (numGroupOfNumCycles X G i.1) * (Fintype.card Y) ^ i.1 := by
  rw [numDistinctColorings_mul_card_group_eq_sum_card_pow_numCyclesOfGroup]
  calc
    ∑ g : G, (Fintype.card Y) ^ (numCyclesOfGroup X g) =
        ∑ i : Fin (Fintype.card X + 1), ∑ _ ∈ {g : G | numCyclesOfGroup X g = i},
          (Fintype.card Y) ^ i.1 := by
      rw [← Finset.sum_fiberwise _ (fun g ↦ (⟨numCyclesOfGroup X g,
        by
          apply Order.lt_add_one_iff.2
          apply Fintype.card_quotient_le⟩
        : Fin (Fintype.card X + 1))) _]
      congr
      ext
      apply Finset.sum_congr
      · ext
        simp [Fin.ext_iff]
      · intro _ hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
        rw [hg]
    _ = ∑ i : Fin (Fintype.card X + 1),
          (numGroupOfNumCycles X G i.1) * (Fintype.card Y) ^ i.1 := by simp

end Theorem

/-- Short alias for *Pólya's enumeration theorem*. -/
theorem polya_theorem (X : Type u) (Y : Type v) (G : Type w) [Group G] [MulAction G X]
    [Fintype Y] [Fintype G] [Fintype (Quotient (MulAction.orbitRel G (X → Y)))]
    [Finite (X → Y)]
    [∀ g : G, Fintype (CyclesOfGroupElements.CyclesOfGroup X g)] :
    DistinctColorings.numDistinctColorings X Y G =
      (∑ g : G, (Fintype.card Y) ^ (CyclesOfGroupElements.numCyclesOfGroup X g))
        / (Fintype.card G) :=
  Theorem.numDistinctColorings_eq_sum_card_pow_numCyclesOfGroup_div_card_group X Y G

end LeanPool.PolyaEnumerationTheorem
