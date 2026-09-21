/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.ComponentsSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Lifts
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.PairBounds
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Boundary
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Convolution
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Separation
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood

/-!
# Lower translated truncations and homogeneous evaluations

The condition studied here is that a nonpositive series has degree at most `m`, while every proper
translated truncation has degree strictly below `m`. It is preserved by constants, sums, products,
and powers: the finite convolution identity writes a proper truncation of a product as a finite sum
of translated truncation products, and in each summand at least one factor is proper, so every
summand drops. Consequently a weighted homogeneous polynomial evaluated at series satisfying the
corresponding bounds satisfies them at the weighted degree. These estimates are used for the
boundary terms and the cofactors associated with homogeneous ideal generators when the degree is
a limit ordinal.
-/

public noncomputable section

open Set MvPolynomial
open scoped NatOrdinal

universe u v w

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- The degree is at most `m`, and every proper translated truncation has degree strictly below
`m`. -/
def HasLowerTruncationDegree (b : Nonpositive G K) (m : NatOrdinal.{u}) : Prop :=
  ν b ≤ m ∧ ∀ y : G, y < 0 → ν (translatedTruncLE y b) < m

theorem hasLowerTruncationDegree_iff {b : Nonpositive G K} {m : NatOrdinal.{u}} :
    HasLowerTruncationDegree b m ↔
      ν b ≤ m ∧ ∀ y : G, y < 0 → ν (translatedTruncLE y b) < m :=
  (Iff.rfl)

theorem HasLowerTruncationDegree.degree_le {b : Nonpositive G K} {m : NatOrdinal.{u}}
    (h : HasLowerTruncationDegree b m) : ν b ≤ m :=
  h.1

theorem HasLowerTruncationDegree.degree_translatedTruncLE_lt
    {b : Nonpositive G K} {m : NatOrdinal.{u}}
    (h : HasLowerTruncationDegree b m) {y : G} (hy : y < 0) : ν (translatedTruncLE y b) < m :=
  h.2 y hy

/-- If a series satisfies the bounds at `m`, then every nonpositive translated truncation has
degree at most `m`. -/
theorem HasLowerTruncationDegree.degree_translatedTruncLE_le
    {b : Nonpositive G K} {m : NatOrdinal.{u}}
    (h : HasLowerTruncationDegree b m) {y : G} (hy : y ≤ 0) : ν (translatedTruncLE y b) ≤ m := by
  rcases eq_or_lt_of_le hy with hy0 | hyneg
  · subst hy0
    rw [translatedTruncLE_zero]
    exact h.1
  · exact (h.2 y hyneg).le

/-- The zero series satisfies the bounds at every degree. -/
theorem hasLowerTruncationDegree_zero (m : NatOrdinal.{u}) :
    HasLowerTruncationDegree (0 : Nonpositive G K) m := by
  constructor
  · rw [(ν).map_zero]
    exact bot_le
  · intro y _
    rw [map_zero, (ν).map_zero]
    exact WithBot.bot_lt_coe m

/-- A constant series satisfies the bounds at degree zero. -/
theorem hasLowerTruncationDegree_algebraMap (k : K) :
    HasLowerTruncationDegree (algebraMap K (Nonpositive G K) k) 0 := by
  constructor
  · rw [algebraMap_apply]
    exact degree_C_le k
  · intro y hy
    rw [degree_translatedTruncLE_eq, if_neg ?_]
    · exact WithBot.bot_lt_coe 0
    · intro hmem
      have hclos := (mem_closedSupport _ _).mp hmem
      have hsub : ((algebraMap K (Nonpositive G K) k : Nonpositive G K) :
          HahnSeries G K).support ⊆ {0} := by
        rw [algebraMap_apply, coe_C, HahnSeries.C_apply]
        exact HahnSeries.support_single_subset
      have hy0 : y ∈ ({0} : Set G) :=
        closure_minimal hsub isClosed_singleton hclos
      exact hy.ne (mem_singleton_iff.mp hy0)

/-- The identity series satisfies the bounds at degree zero. -/
theorem hasLowerTruncationDegree_one : HasLowerTruncationDegree (1 : Nonpositive G K) 0 := by
  have h := hasLowerTruncationDegree_algebraMap (G := G) (K := K) 1
  rwa [map_one] at h

/-- Sums preserve the bounds at a common degree. -/
theorem HasLowerTruncationDegree.add {a b : Nonpositive G K} {m : NatOrdinal.{u}}
    (ha : HasLowerTruncationDegree a m) (hb : HasLowerTruncationDegree b m) :
    HasLowerTruncationDegree (a + b) m := by
  constructor
  · exact ((ν).map_add_le_max a b).trans (max_le ha.1 hb.1)
  · intro y hy
    rw [map_add]
    exact ((ν).map_add_le_max _ _).trans_lt (max_lt (ha.2 y hy) (hb.2 y hy))

/-- If two series satisfy the bounds at `m` and `n`, their product satisfies them at `m + n`: in
the finite convolution of a proper product truncation, every summand has a proper factor. -/
theorem HasLowerTruncationDegree.mul {a b : Nonpositive G K} {m n p : NatOrdinal.{u}}
    (hp : p = m + n) (ha : HasLowerTruncationDegree a m)
    (hb : HasLowerTruncationDegree b n) : HasLowerTruncationDegree (a * b) p := by
  subst hp
  constructor
  · exact ((ν).map_mul_le_add a b).trans (by
      rw [WithBot.coe_add]
      exact add_le_add ha.1 hb.1)
  · intro y hy
    classical
    have herr : ν (translatedTruncLE y (a * b) -
        ∑ q ∈ (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) y,
          translatedTruncLE q.1 a * translatedTruncLE q.2 b) = ⊥ := by
      rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply]
      have hcoe : ((translatedTruncLE y (a * b) -
          ∑ q ∈ (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) y,
            translatedTruncLE q.1 a * translatedTruncLE q.2 b : Nonpositive G K) :
          HahnSeries G K) =
          translate (-y) (truncLE y ((a : HahnSeries G K) * (b : HahnSeries G K))) -
            ∑ q ∈ (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) y,
              translate (-q.1) (truncLE q.1 (a : HahnSeries G K)) *
                translate (-q.2) (truncLE q.2 (b : HahnSeries G K)) := by
        simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum,
          Subring.coe_mul, coe_translatedTruncLE]
      rw [hcoe, (a : HahnSeries G K).cantorBendixsonValue_convolution_error
        (b : HahnSeries G K) y, NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]
    have hsum : ν (∑ q ∈ (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) y,
        translatedTruncLE q.1 a * translatedTruncLE q.2 b) < (m + n : NatOrdinal) := by
      apply (ν).map_sum_lt_of_forall_lt _ _ (WithBot.bot_lt_coe _)
      intro q hq
      obtain ⟨hq1, hq2, hqsum⟩ := ((a : HahnSeries G K).mem_closedSupportAddFiber
        (b : HahnSeries G K) y q).mp hq
      have hq1le : q.1 ≤ 0 := closure_minimal a.property isClosed_Iic
        ((mem_closedSupport _ _).mp hq1)
      have hq2le : q.2 ≤ 0 := closure_minimal b.property isClosed_Iic
        ((mem_closedSupport _ _).mp hq2)
      have hone : q.1 < 0 ∨ q.2 < 0 := by
        rcases lt_or_eq_of_le hq1le with hq1neg | hq1zero
        · exact Or.inl hq1neg
        · refine Or.inr ?_
          have hq2y : q.2 = y := by
            rw [← hqsum, hq1zero, zero_add]
          exact hq2y ▸ hy
      rcases hone with hq1neg | hq2neg
      · rw [mul_comm]
        exact degree_mul_lt_of_le_of_lt_of_separated (translatedTruncLE q.2 b)
          (translatedTruncLE q.1 a) n m (m + n) (hb.degree_translatedTruncLE_le hq2le)
          (ha.2 q.1 hq1neg) (fun θ hθ ↦ by
            rw [add_comm m n]
            exact add_lt_add_of_le_of_lt le_rfl hθ)
      · exact degree_mul_lt_of_le_of_lt_of_separated (translatedTruncLE q.1 a)
          (translatedTruncLE q.2 b) m n (m + n) (ha.degree_translatedTruncLE_le hq1le)
          (hb.2 q.2 hq2neg) (fun θ hθ ↦ add_lt_add_of_le_of_lt le_rfl hθ)
    have hsplit : translatedTruncLE y (a * b) =
        (translatedTruncLE y (a * b) -
          ∑ q ∈ (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) y,
            translatedTruncLE q.1 a * translatedTruncLE q.2 b) +
          ∑ q ∈ (a : HahnSeries G K).closedSupportAddFiber (b : HahnSeries G K) y,
            translatedTruncLE q.1 a * translatedTruncLE q.2 b := by
      abel
    rw [hsplit]
    exact ((ν).map_add_le_max _ _).trans_lt
      (max_lt (by rw [herr]; exact WithBot.bot_lt_coe _) hsum)

/-- If a series satisfies the bounds at `m`, its `n`th power satisfies them at `n • m`. -/
theorem HasLowerTruncationDegree.pow {b : Nonpositive G K} {m : NatOrdinal.{u}}
    (hb : HasLowerTruncationDegree b m) (n : ℕ) : HasLowerTruncationDegree (b ^ n) (n • m) := by
  induction n with
  | zero =>
      rw [pow_zero, zero_smul]
      exact hasLowerTruncationDegree_one
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul (succ_nsmul m n) hb

/-- A finite product satisfies the bounds at the sum of the assigned degrees. -/
theorem hasLowerTruncationDegree_prod {ι' : Type w} {s : Finset ι'} {a : ι' → Nonpositive G K}
    {m : ι' → NatOrdinal.{u}} (h : ∀ i ∈ s, HasLowerTruncationDegree (a i) (m i)) :
    HasLowerTruncationDegree (∏ i ∈ s, a i) (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact hasLowerTruncationDegree_one
  | cons i s hi ih =>
      rw [Finset.prod_cons]
      exact (h i (Finset.mem_cons_self i s)).mul (Finset.sum_cons hi)
        (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}

/-- A weighted homogeneous polynomial evaluated at series satisfying the assigned bounds also
satisfies the bounds at its weight. -/
theorem hasLowerTruncationDegree_aeval (hV : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    {F : MvPolynomial ι K} {β : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F β) :
    HasLowerTruncationDegree (aeval V F) β := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero =>
      rw [map_zero]
      exact hasLowerTruncationDegree_zero β
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact ihp.add ihq
  | monomial d r hr =>
      rw [← hr, aeval_monomial, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      exact (hasLowerTruncationDegree_algebraMap r).mul (zero_add _).symm
        (hasLowerTruncationDegree_prod fun i _ ↦ (hV i).pow (d i))

/-- **The uniform polynomial window.** If every homogeneous class of degree below `α` is a
homogeneous polynomial in the prescribed classes, then every proper translated truncation of the
evaluation of a weighted homogeneous polynomial of degree `β` at such representatives is
congruent,
modulo series bounded strictly below zero, to the evaluation of a polynomial all of whose
monomial weights are strictly below `β`. The bound is uniform in the cutoff: it does not degrade
as the cutoff approaches zero, and no cofinal sequence of cutoffs is chosen. -/
theorem exists_forall_weight_lt_and_degree_translatedTruncLE_sub_aeval_eq_bot
    (xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded)
    (hVrep : ∀ i, Represents (V i) (wt i) (xg i))
    (hV : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α →
      ∀ y ∈ DirectSum.rangeLof K
        (cantorBendixsonDegreeValuation (G := G) (R := K)).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ MvPolynomial.aeval xg F = y)
    {F : MvPolynomial ι K} {β : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F β)
    (hβα : β < α) {γ : G} (hγ : γ < 0) :
    ∃ F' : MvPolynomial ι K, (∀ d ∈ F'.support, (Finsupp.weight wt) d < β) ∧
      ν (translatedTruncLE γ (aeval V F) - aeval V F') = ⊥ := by
  have hdrop : ν (translatedTruncLE γ (aeval V F)) < (β : WithBot NatOrdinal) :=
    (hasLowerTruncationDegree_aeval hV hF).degree_translatedTruncLE_lt hγ
  obtain ⟨F', hF'd, -, hF'bot⟩ :=
    exists_forall_weight_lt_and_degree_sub_aeval_eq_bot xg hVrep α hgen
      (translatedTruncLE γ (aeval V F)) (hdrop.trans (WithBot.coe_lt_coe.mpr hβα))
  refine ⟨F', fun d hd ↦ ?_, hF'bot⟩
  exact WithBot.coe_lt_coe.mp ((hF'd d hd).trans_lt hdrop)

private theorem degree_mul_le_of_lt_of_lt_of_bound {p q : Nonpositive G K}
    {σ₁ σ₂ B : NatOrdinal.{u}} (hp : ν p < (σ₁ : WithBot NatOrdinal))
    (hq : ν q < (σ₂ : WithBot NatOrdinal))
    (hB : ∀ θ₁ θ₂ : NatOrdinal.{u}, θ₁ < σ₁ → θ₂ < σ₂ → θ₁ + θ₂ ≤ B) :
    ν (p * q) ≤ (B : WithBot NatOrdinal) := by
  have hmul := (ν).map_mul_le_add p q
  cases hp' : ν p using WithBot.recBotCoe with
  | bot =>
      rw [hp', WithBot.bot_add] at hmul
      exact hmul.trans bot_le
  | coe θ₁ =>
      cases hq' : ν q using WithBot.recBotCoe with
      | bot =>
          rw [hq', WithBot.add_bot] at hmul
          exact hmul.trans bot_le
      | coe θ₂ =>
          rw [hp', hq', ← WithBot.coe_add] at hmul
          refine hmul.trans (WithBot.coe_le_coe.mpr (hB θ₁ θ₂ ?_ ?_))
          · rwa [hp', WithBot.coe_lt_coe] at hp
          · rwa [hq', WithBot.coe_lt_coe] at hq

/-- **The uniform two-truncation window.** For series satisfying the bounds at nonzero degrees,
the Leibniz remainder of a product -- the finite convolution with both boundary terms removed --
is bounded by a single degree strictly below the product degree, uniformly in the cutoff. Every
interior term of the convolution truncates both factors, so its degree is a natural sum with both
summands lowered, and the ordinal two-summand bound is uniform. -/
theorem exists_lt_forall_degree_leibnizRemainder_le
    {a b : Nonpositive G K} {σ₁ σ₂ : NatOrdinal.{u}}
    (ha : HasLowerTruncationDegree a σ₁) (hb : HasLowerTruncationDegree b σ₂)
    (hσ₁ : σ₁ ≠ 0) (hσ₂ : σ₂ ≠ 0) :
    ∃ μ' : NatOrdinal.{u}, μ' < σ₁ + σ₂ ∧ ∀ γ : G, γ < 0 →
      ν (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b -
        a * translatedTruncLE γ b) ≤ (μ' : WithBot NatOrdinal) := by
  classical
  obtain ⟨e₁, he₁⟩ := NatOrdinal.exists_leastTerm_eq_wpow hσ₁
  obtain ⟨e₂, he₂⟩ := NatOrdinal.exists_leastTerm_eq_wpow hσ₂
  obtain ⟨B, hBlt, hBbound⟩ :=
    NatOrdinal.exists_lt_forall_add_add_le (O := 0) hσ₁ hσ₂ he₁ he₂
  have hBbound' : ∀ θ₁ θ₂ : NatOrdinal.{u}, θ₁ < σ₁ → θ₂ < σ₂ → θ₁ + θ₂ ≤ B := by
    intro θ₁ θ₂ h₁ h₂
    have := hBbound θ₁ θ₂ h₁ h₂
    rwa [zero_add] at this
  refine ⟨B, by rwa [zero_add] at hBlt, fun γ hγ ↦ ?_⟩
  have hremValue := HahnSeries.cantorBendixsonValue_leibnizRemainder_lt_of_forall
    (a : HahnSeries G K) (b : HahnSeries G K) a.property b.property hγ
    (ρ := (ω^ (B + 1)).val) (NatOrdinal.wpow_pos (B + 1)) (fun x y _ hx _ hy _ ↦ by
      have hprod : ν (translatedTruncLE x a * translatedTruncLE y b) <
          ((B + 1 : NatOrdinal) : WithBot NatOrdinal) :=
        (degree_mul_le_of_lt_of_lt_of_bound (ha.degree_translatedTruncLE_lt hx)
          (hb.degree_translatedTruncLE_lt hy) hBbound').trans_lt
          (WithBot.coe_lt_coe.mpr (lt_add_one B))
      rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
        NatOrdinal.cantorDegree_lt_coe_iff] at hprod
      exact NatOrdinal.of.lt_iff_lt.mp
        (by simpa only [coe_translatedTruncLE, Subring.coe_mul, NatOrdinal.of_val] using hprod))
  have hrem : ν (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b -
      a * translatedTruncLE γ b) < ((B + 1 : NatOrdinal) : WithBot NatOrdinal) := by
    rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
      NatOrdinal.cantorDegree_lt_coe_iff]
    change NatOrdinal.of (((translatedTruncLE γ (a * b) : Nonpositive G K) : HahnSeries G K) -
      (translatedTruncLE γ a : Nonpositive G K) * b -
      (a : HahnSeries G K) * translatedTruncLE γ b).cantorBendixsonValue < ω^ (B + 1)
    exact NatOrdinal.of.lt_iff_lt.mpr (by
      simpa only [coe_translatedTruncLE, Subring.coe_mul, NatOrdinal.val_wpow] using hremValue)
  cases hv : ν (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b -
      a * translatedTruncLE γ b) using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
      rw [hv, WithBot.coe_lt_coe] at hrem
      exact WithBot.coe_le_coe.mpr (Order.lt_add_one_iff.mp hrem)

/-! ### Congruence modulo series bounded strictly below zero -/

theorem degree_mul_eq_bot_of_left {a b : Nonpositive G K} (ha : ν a = ⊥) : ν (a * b) = ⊥ := by
  have := (ν).map_mul_le_add a b
  rw [ha, WithBot.bot_add] at this
  exact le_bot_iff.mp this

theorem degree_mul_eq_bot_of_right {a b : Nonpositive G K} (hb : ν b = ⊥) : ν (a * b) = ⊥ := by
  have := (ν).map_mul_le_add a b
  rw [hb, WithBot.add_bot] at this
  exact le_bot_iff.mp this

/-- Congruence modulo series bounded strictly below zero is multiplicative. -/
theorem degree_sub_eq_bot_mul {a a' b b' : Nonpositive G K}
    (ha : ν (a - a') = ⊥) (hb : ν (b - b') = ⊥) : ν (a * b - a' * b') = ⊥ := by
  have hsplit : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [hsplit]
  refine le_bot_iff.mp (((ν).map_add_le_max _ _).trans ?_)
  rw [degree_mul_eq_bot_of_right hb, degree_mul_eq_bot_of_left ha, max_self]

/-- Congruence modulo series bounded strictly below zero is additive over finite sums. -/
theorem degree_sub_eq_bot_sum {ι' : Type w} (s : Finset ι') (f g : ι' → Nonpositive G K)
    (h : ∀ i ∈ s, ν (f i - g i) = ⊥) :
    ν ((∑ i ∈ s, f i) - ∑ i ∈ s, g i) = ⊥ := by
  classical
  rw [← Finset.sum_sub_distrib]
  exact le_bot_iff.mp ((ν).map_sum_le_of_forall_le _ _ ⊥ fun i hi ↦ (h i hi).le)

/-- The finite convolution identity in degree form: a translated truncation of a product agrees,
modulo series bounded strictly below zero, with the finite sum over the closed-support fiber of
the products of translated truncations. -/
theorem degree_translatedTruncLE_mul_sub_sum_eq_bot (b d : Nonpositive G K) (γ : G) :
    ν (translatedTruncLE γ (b * d) -
      ∑ q ∈ (b : HahnSeries G K).closedSupportAddFiber (d : HahnSeries G K) γ,
        translatedTruncLE q.1 b * translatedTruncLE q.2 d) = ⊥ := by
  classical
  rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply]
  have hcoe : ((translatedTruncLE γ (b * d) -
      ∑ q ∈ (b : HahnSeries G K).closedSupportAddFiber (d : HahnSeries G K) γ,
        translatedTruncLE q.1 b * translatedTruncLE q.2 d : Nonpositive G K) :
      HahnSeries G K) =
      translate (-γ) (truncLE γ ((b : HahnSeries G K) * (d : HahnSeries G K))) -
        ∑ q ∈ (b : HahnSeries G K).closedSupportAddFiber (d : HahnSeries G K) γ,
          translate (-q.1) (truncLE q.1 (b : HahnSeries G K)) *
            translate (-q.2) (truncLE q.2 (d : HahnSeries G K)) := by
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum,
      Subring.coe_mul, coe_translatedTruncLE]
  rw [hcoe, (b : HahnSeries G K).cantorBendixsonValue_convolution_error
    (d : HahnSeries G K) γ, NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]

variable {ι : Type w} {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}

/-- **The convolution polynomial identity.** If polynomials represent the translated truncations
of two factors at every cutoff, then the convolution sum of those polynomials over the
closed-support fiber represents the translated truncation of the product. No canonical choice of
representing polynomial is needed: any choices work, because congruence modulo series bounded
strictly below zero is a ring congruence. -/
theorem degree_translatedTruncLE_mul_sub_aeval_sum_eq_bot
    (b d : Nonpositive G K) (γ : G)
    (Fb Fd : G → MvPolynomial ι K)
    (hFb : ∀ x : G, ν (translatedTruncLE x b - aeval V (Fb x)) = ⊥)
    (hFd : ∀ y : G, ν (translatedTruncLE y d - aeval V (Fd y)) = ⊥) :
    ν (translatedTruncLE γ (b * d) -
      aeval V (∑ q ∈ (b : HahnSeries G K).closedSupportAddFiber (d : HahnSeries G K) γ,
        Fb q.1 * Fd q.2)) = ⊥ := by
  classical
  set S := (b : HahnSeries G K).closedSupportAddFiber (d : HahnSeries G K) γ with hS
  have hterm : ∀ q ∈ S, ν (translatedTruncLE q.1 b * translatedTruncLE q.2 d -
      aeval V (Fb q.1 * Fd q.2)) = ⊥ := by
    intro q _
    rw [map_mul]
    exact degree_sub_eq_bot_mul (hFb q.1) (hFd q.2)
  have hsum : ν ((∑ q ∈ S, translatedTruncLE q.1 b * translatedTruncLE q.2 d) -
      ∑ q ∈ S, aeval V (Fb q.1 * Fd q.2)) = ⊥ :=
    degree_sub_eq_bot_sum S _ _ hterm
  have hsplit : translatedTruncLE γ (b * d) -
      aeval V (∑ q ∈ S, Fb q.1 * Fd q.2) =
      (translatedTruncLE γ (b * d) -
        ∑ q ∈ S, translatedTruncLE q.1 b * translatedTruncLE q.2 d) +
        ((∑ q ∈ S, translatedTruncLE q.1 b * translatedTruncLE q.2 d) -
          ∑ q ∈ S, aeval V (Fb q.1 * Fd q.2)) := by
    rw [map_sum]
    abel
  rw [hsplit]
  refine le_bot_iff.mp (((ν).map_add_le_max _ _).trans ?_)
  rw [degree_translatedTruncLE_mul_sub_sum_eq_bot b d γ, hsum, max_self]

/-- **The power Leibniz rule with a uniform remainder.** For a series of nonzero lower-truncation
degree,
the translated truncation of a power differs from the expected single-truncation term by a
remainder bounded by a fixed degree strictly below the power degree, uniformly in the cutoff.
Each step of the induction uses the two-factor window and absorbs the previous remainder. -/
theorem exists_lt_forall_degree_pow_leibniz_le {a : Nonpositive G K} {m : NatOrdinal.{u}}
    (ha : HasLowerTruncationDegree a m) (hm : m ≠ 0) (n : ℕ) :
    ∃ lam : NatOrdinal.{u}, lam < (n + 1) • m ∧ ∀ γ : G, γ < 0 →
      ν (translatedTruncLE γ (a ^ (n + 1)) -
        (n + 1 : ℕ) • (translatedTruncLE γ a * a ^ n)) ≤ (lam : WithBot NatOrdinal) := by
  induction n with
  | zero =>
      refine ⟨0, ?_, fun γ _ ↦ ?_⟩
      · simpa only [zero_add, one_smul] using pos_iff_ne_zero.mpr hm
      · simp only [zero_add, pow_one, pow_zero, mul_one, one_smul, sub_self]
        rw [(ν).map_zero]
        exact bot_le
  | succ n ih =>
      obtain ⟨lam, hlam, hbound⟩ := ih
      have hpow : HasLowerTruncationDegree (a ^ (n + 1)) ((n + 1) • m) := ha.pow (n + 1)
      have hne : ((n + 1) • m : NatOrdinal) ≠ 0 := by
        intro h0
        have hle : m ≤ (n + 1) • m := by
          have h1 : (1 : ℕ) • m ≤ (n + 1) • m :=
            nsmul_le_nsmul_left (zero_le (a := m)) (by omega)
          simpa only [one_smul] using h1
        exact hm (le_antisymm (h0 ▸ hle) (zero_le (a := m)))
      obtain ⟨B, hBlt, hBbound⟩ :=
        exists_lt_forall_degree_leibnizRemainder_le ha hpow hm hne
      have hsucc : (n + 1 + 1) • m = m + (n + 1) • m := by
        rw [succ_nsmul, add_comm]
      refine ⟨max B (m + lam), ?_, fun γ hγ ↦ ?_⟩
      · rw [hsucc]
        exact max_lt hBlt (add_lt_add_of_le_of_lt le_rfl hlam)
      · have hsplit : translatedTruncLE γ (a ^ (n + 1 + 1)) -
            (n + 1 + 1 : ℕ) • (translatedTruncLE γ a * a ^ (n + 1)) =
            (translatedTruncLE γ (a * a ^ (n + 1)) -
              translatedTruncLE γ a * a ^ (n + 1) - a * translatedTruncLE γ (a ^ (n + 1))) +
              a * (translatedTruncLE γ (a ^ (n + 1)) -
                (n + 1 : ℕ) • (translatedTruncLE γ a * a ^ n)) := by
          have hpowsucc : a ^ (n + 1 + 1) = a * a ^ (n + 1) := by ring
          have hmulsmul : a * ((n + 1 : ℕ) • (translatedTruncLE γ a * a ^ n)) =
              (n + 1 : ℕ) • (translatedTruncLE γ a * a ^ (n + 1)) := by
            rw [mul_smul_comm]
            congr 1
            rw [pow_succ]
            ring
          rw [hpowsucc, mul_sub, hmulsmul, succ_nsmul, add_smul, one_smul]
          abel
        rw [hsplit]
        refine ((ν).map_add_le_max _ _).trans (max_le ?_ ?_)
        · exact (hBbound γ hγ).trans (WithBot.coe_le_coe.mpr (le_max_left _ _))
        · refine ((ν).map_mul_le_add a _).trans ?_
          refine (add_le_add ha.degree_le (hbound γ hγ)).trans ?_
          rw [← WithBot.coe_add]
          exact WithBot.coe_le_coe.mpr (le_max_right _ _)

/-! ### The monomial Leibniz expansion -/

open Finsupp in
/-- **The monomial Leibniz expansion with a uniform remainder.** The translated truncation of a
monomial evaluated at series satisfying the assigned bounds differs from the sum of its evaluated
partial derivatives against the truncated variables by a remainder bounded by a fixed degree
strictly below the monomial degree, uniformly in the cutoff. The induction peels one power block
at a time, using the two-factor window to separate it and the power rule inside it. -/
theorem exists_lt_forall_degree_monomial_leibniz_le
    (hV : ∀ i, HasLowerTruncationDegree (V i) (wt i)) (hwt : ∀ i, wt i ≠ 0) (t : Finset ι) :
    ∀ d : ι →₀ ℕ, d ≠ 0 → d.support ⊆ t →
      ∃ lam : NatOrdinal.{u}, lam < Finsupp.weight wt d ∧ ∀ γ : G, γ < 0 →
        ν (translatedTruncLE γ (aeval V (MvPolynomial.monomial d (1 : K))) -
          ∑ i ∈ t, aeval V (MvPolynomial.pderiv i (MvPolynomial.monomial d (1 : K))) *
            translatedTruncLE γ (V i)) ≤ (lam : WithBot NatOrdinal) := by
  classical
  intro d
  induction d using Finsupp.induction with
  | zero => exact fun h ↦ absurd rfl h
  | @single_add i b d' hi hb ih =>
      intro _ hsupp
      have hit : i ∈ t := by
        apply hsupp
        rw [Finsupp.support_add_eq (by
          rw [Finsupp.support_single i hb]
          exact Finset.disjoint_singleton_left.mpr hi)]
        exact Finset.mem_union_left _ (by
          rw [Finsupp.support_single i hb]
          exact Finset.mem_singleton_self i)
      have hweight : Finsupp.weight wt (Finsupp.single i b + d') =
          b • wt i + Finsupp.weight wt d' := by
        rw [map_add, Finsupp.weight_single]
      obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
      -- The monomial splits into a power block and the rest.
      have hsplit : (MvPolynomial.monomial (Finsupp.single i (n + 1) + d') (1 : K)) =
          MvPolynomial.X i ^ (n + 1) * MvPolynomial.monomial d' (1 : K) :=
        MvPolynomial.monomial_single_add
      have hpowBounds : HasLowerTruncationDegree (V i ^ (n + 1)) ((n + 1) • wt i) :=
        (hV i).pow (n + 1)
      have hpowne : ((n + 1) • wt i : NatOrdinal) ≠ 0 := by
        intro h0
        have hle : wt i ≤ (n + 1) • wt i := by
          have h1 : (1 : ℕ) • wt i ≤ (n + 1) • wt i :=
            nsmul_le_nsmul_left (zero_le (a := wt i)) (by omega)
          simpa only [one_smul] using h1
        exact hwt i (le_antisymm (h0 ▸ hle) (zero_le (a := wt i)))
      -- The evaluated partial derivatives of the power block.
      have hpderivPow : ∀ j : ι, aeval V (MvPolynomial.pderiv j
          (MvPolynomial.X i ^ (n + 1) : MvPolynomial ι K)) =
          if j = i then (n + 1 : ℕ) • (V i ^ n) else 0 := by
        intro j
        rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X]
        by_cases hji : j = i
        · subst hji
          rw [Pi.single_eq_same, if_pos rfl, mul_one, map_mul, map_pow, MvPolynomial.aeval_X,
            map_natCast, Nat.add_sub_cancel, nsmul_eq_mul]
        · rw [Pi.single_eq_of_ne (Ne.symm hji), if_neg hji, mul_zero, map_zero]
      have hA : aeval V (MvPolynomial.monomial (Finsupp.single i (n + 1) + d') (1 : K)) =
          V i ^ (n + 1) * aeval V (MvPolynomial.monomial d' (1 : K)) := by
        rw [hsplit, map_mul, map_pow, MvPolynomial.aeval_X]
      -- The evaluated partial derivatives of the whole monomial split by the Leibniz rule.
      have hsum : ∀ γ : G,
          ∑ j ∈ t, aeval V (MvPolynomial.pderiv j
              (MvPolynomial.monomial (Finsupp.single i (n + 1) + d') (1 : K))) *
                translatedTruncLE γ (V j) =
            ((n + 1 : ℕ) • (V i ^ n) * aeval V (MvPolynomial.monomial d' (1 : K))) *
                translatedTruncLE γ (V i) +
              V i ^ (n + 1) *
                ∑ j ∈ t, aeval V (MvPolynomial.pderiv j (MvPolynomial.monomial d' (1 : K))) *
                  translatedTruncLE γ (V j) := by
        intro γ
        have hterm : ∀ j ∈ t, aeval V (MvPolynomial.pderiv j
            (MvPolynomial.monomial (Finsupp.single i (n + 1) + d') (1 : K))) *
              translatedTruncLE γ (V j) =
            (if j = i then ((n + 1 : ℕ) • (V i ^ n) *
              aeval V (MvPolynomial.monomial d' (1 : K))) * translatedTruncLE γ (V i) else 0) +
              V i ^ (n + 1) * (aeval V (MvPolynomial.pderiv j
                (MvPolynomial.monomial d' (1 : K))) * translatedTruncLE γ (V j)) := by
          intro j _
          have e1 : aeval V (MvPolynomial.pderiv j (MvPolynomial.X i ^ (n + 1)) *
              MvPolynomial.monomial d' (1 : K)) =
              (if j = i then (n + 1 : ℕ) • (V i ^ n) else 0) *
                aeval V (MvPolynomial.monomial d' (1 : K)) := by
            rw [map_mul, hpderivPow j]
          have e2 : aeval V ((MvPolynomial.X i ^ (n + 1) : MvPolynomial ι K) *
              MvPolynomial.pderiv j (MvPolynomial.monomial d' (1 : K))) =
              V i ^ (n + 1) * aeval V (MvPolynomial.pderiv j
                (MvPolynomial.monomial d' (1 : K))) := by
            rw [map_mul, map_pow, MvPolynomial.aeval_X]
          rw [hsplit, MvPolynomial.pderiv_mul, map_add, e1, e2, add_mul]
          congr 1
          · by_cases hji : j = i
            · rw [if_pos hji, if_pos hji, hji]
            · rw [if_neg hji, if_neg hji, zero_mul, zero_mul]
          · ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_ite_eq' t i (fun _ ↦ ((n + 1 : ℕ) • (V i ^ n) *
            aeval V (MvPolynomial.monomial d' (1 : K))) * translatedTruncLE γ (V i)),
          if_pos hit]
      obtain ⟨lamA, hlamA, hboundA⟩ :=
        exists_lt_forall_degree_pow_leibniz_le (hV i) (hwt i) n
      by_cases hd0 : d' = 0
      · subst hd0
        refine ⟨lamA, ?_, fun γ hγ ↦ ?_⟩
        · rw [hweight, map_zero, add_zero]
          exact hlamA
        · have hone : aeval V (MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : K)) = 1 := by
            simp
          have hinner : ∑ j ∈ t, aeval V (MvPolynomial.pderiv j
              (MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : K))) * translatedTruncLE γ (V j) = 0 := by
            refine Finset.sum_eq_zero fun j _ ↦ ?_
            rw [MvPolynomial.monomial_zero', MvPolynomial.pderiv_C, map_zero, zero_mul]
          have hgoal : translatedTruncLE γ
              (aeval V (MvPolynomial.monomial (Finsupp.single i (n + 1) + 0) (1 : K))) -
              ∑ j ∈ t, aeval V (MvPolynomial.pderiv j
                (MvPolynomial.monomial (Finsupp.single i (n + 1) + 0) (1 : K))) *
                  translatedTruncLE γ (V j) =
              translatedTruncLE γ (V i ^ (n + 1)) -
                (n + 1 : ℕ) • (translatedTruncLE γ (V i) * V i ^ n) := by
            rw [hsum γ, hA, hone, hinner]
            ring_nf
          rw [hgoal]
          exact hboundA γ hγ
      · obtain ⟨lamB, hlamB, hboundB⟩ := ih hd0 (fun j hj ↦ hsupp (by
          rw [Finsupp.support_add_eq (by
            rw [Finsupp.support_single i hb]
            exact Finset.disjoint_singleton_left.mpr hi)]
          exact Finset.mem_union_right _ hj))
        have hBhom : IsWeightedHomogeneous wt (MvPolynomial.monomial d' (1 : K))
            (Finsupp.weight wt d') :=
          MvPolynomial.isWeightedHomogeneous_monomial wt d' 1 rfl
        have hBBounds : HasLowerTruncationDegree (aeval V (MvPolynomial.monomial d' (1 : K)))
            (Finsupp.weight wt d') := hasLowerTruncationDegree_aeval hV hBhom
        have hBne : Finsupp.weight wt d' ≠ 0 := by
          intro h0
          obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hd0
          have hle : wt j ≤ Finsupp.weight wt d' :=
            Finsupp.le_weight_of_ne_zero (w := wt) (fun _ ↦ zero_le (a := wt _))
              (Finsupp.mem_support_iff.mp hj)
          exact hwt j (le_antisymm (h0 ▸ hle) (zero_le (a := wt j)))
        obtain ⟨Bwin, hBwin, hboundWin⟩ :=
          exists_lt_forall_degree_leibnizRemainder_le hpowBounds hBBounds hpowne hBne
        refine ⟨max Bwin (max (lamA + Finsupp.weight wt d') ((n + 1) • wt i + lamB)), ?_,
          fun γ hγ ↦ ?_⟩
        · rw [hweight]
          exact max_lt hBwin (max_lt (add_lt_add_of_lt_of_le hlamA le_rfl)
            (add_lt_add_of_le_of_lt le_rfl hlamB))
        · have hdecomp : translatedTruncLE γ
              (aeval V (MvPolynomial.monomial (Finsupp.single i (n + 1) + d') (1 : K))) -
              ∑ j ∈ t, aeval V (MvPolynomial.pderiv j
                (MvPolynomial.monomial (Finsupp.single i (n + 1) + d') (1 : K))) *
                  translatedTruncLE γ (V j) =
              (translatedTruncLE γ (V i ^ (n + 1) *
                  aeval V (MvPolynomial.monomial d' (1 : K))) -
                translatedTruncLE γ (V i ^ (n + 1)) *
                  aeval V (MvPolynomial.monomial d' (1 : K)) -
                V i ^ (n + 1) * translatedTruncLE γ
                  (aeval V (MvPolynomial.monomial d' (1 : K)))) +
              ((translatedTruncLE γ (V i ^ (n + 1)) -
                  (n + 1 : ℕ) • (translatedTruncLE γ (V i) * V i ^ n)) *
                aeval V (MvPolynomial.monomial d' (1 : K)) +
              V i ^ (n + 1) * (translatedTruncLE γ
                  (aeval V (MvPolynomial.monomial d' (1 : K))) -
                ∑ j ∈ t, aeval V (MvPolynomial.pderiv j
                  (MvPolynomial.monomial d' (1 : K))) * translatedTruncLE γ (V j))) := by
            rw [hsum γ, hA]
            ring
          rw [hdecomp]
          refine ((ν).map_add_le_max _ _).trans (max_le ?_ ?_)
          · exact (hboundWin γ hγ).trans (WithBot.coe_le_coe.mpr (le_max_left _ _))
          · refine ((ν).map_add_le_max _ _).trans (max_le ?_ ?_)
            · refine ((ν).map_mul_le_add _ _).trans ?_
              refine (add_le_add (hboundA γ hγ) hBBounds.degree_le).trans ?_
              rw [← WithBot.coe_add]
              exact WithBot.coe_le_coe.mpr ((le_max_left _ _).trans (le_max_right _ _))
            · refine ((ν).map_mul_le_add _ _).trans ?_
              refine (add_le_add hpowBounds.degree_le (hboundB γ hγ)).trans ?_
              rw [← WithBot.coe_add]
              exact WithBot.coe_le_coe.mpr ((le_max_right _ _).trans (le_max_right _ _))

/-- Scaling by a coefficient does not raise the degree. -/
theorem degree_smul_le (k : K) (b : Nonpositive G K) : ν (k • b) ≤ ν b := by
  have hsm : k • b = C k * b := by
    rw [← algebraMap_apply, Algebra.smul_def]
  rw [hsm]
  refine ((ν).map_mul_le_add _ _).trans ?_
  have h0 : ν (C k : Nonpositive G K) ≤ (0 : NatOrdinal) := degree_C_le k
  calc ν (C k : Nonpositive G K) + ν b ≤ ((0 : NatOrdinal) : WithBot NatOrdinal) + ν b :=
        add_le_add h0 le_rfl
    _ = ν b := by
        cases hb : ν b using WithBot.recBotCoe with
        | bot => rw [WithBot.add_bot]
        | coe d => rw [← WithBot.coe_add, zero_add]

open Finsupp in
/-- **The homogeneous Leibniz expansion with a uniform remainder.** For a weighted homogeneous
polynomial of nonzero degree evaluated at series satisfying the assigned bounds, the translated
truncation differs from the sum of the evaluated partial derivatives against the truncated
variables by a remainder bounded by a fixed degree strictly below the polynomial degree,
uniformly in the cutoff. Each monomial contributes its own bound and the finitely many bounds are
taken together.

This is the analytic input required by the differentiated relation when the degree is a limit
ordinal. -/
theorem exists_lt_forall_degree_homogeneous_leibniz_le
    (hV : ∀ i, HasLowerTruncationDegree (V i) (wt i)) (hwt : ∀ i, wt i ≠ 0) (t : Finset ι)
    {F : MvPolynomial ι K} {c : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F c)
    (hc : c ≠ 0) (hFt : ∀ d ∈ F.support, d.support ⊆ t) :
    ∃ lam : NatOrdinal.{u}, lam < c ∧ ∀ γ : G, γ < 0 →
      ν (translatedTruncLE γ (aeval V F) -
        ∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i)) ≤
        (lam : WithBot NatOrdinal) := by
  classical
  -- Each monomial of `F` has weight `c`, hence is nonzero, and contributes its own bound.
  have hmon : ∀ d ∈ F.support, d ≠ 0 ∧ Finsupp.weight wt d = c := by
    intro d hd
    have hw : Finsupp.weight wt d = c := hF (MvPolynomial.mem_support_iff.mp hd)
    refine ⟨fun h0 ↦ ?_, hw⟩
    rw [h0, map_zero] at hw
    exact hc hw.symm
  have hchoice : ∀ d ∈ F.support, ∃ lam : NatOrdinal.{u}, lam < c ∧ ∀ γ : G, γ < 0 →
      ν (translatedTruncLE γ (aeval V (MvPolynomial.monomial d (1 : K))) -
        ∑ i ∈ t, aeval V (MvPolynomial.pderiv i (MvPolynomial.monomial d (1 : K))) *
          translatedTruncLE γ (V i)) ≤ (lam : WithBot NatOrdinal) := by
    intro d hd
    obtain ⟨hd0, hw⟩ := hmon d hd
    obtain ⟨lam, hlam, hbound⟩ :=
      exists_lt_forall_degree_monomial_leibniz_le hV hwt t d hd0 (hFt d hd)
    exact ⟨lam, hw ▸ hlam, hbound⟩
  choose lamOf hlamOf hboundOf using hchoice
  set L : {d // d ∈ F.support} → NatOrdinal.{u} := fun d ↦ lamOf d.1 d.2 with hL
  refine ⟨F.support.attach.sup L, ?_, fun γ hγ ↦ ?_⟩
  · refine Finset.sup_lt_iff (pos_iff_ne_zero.mpr hc) |>.mpr ?_
    intro d _
    exact hlamOf d.1 d.2
  · have hFsum : F = ∑ d ∈ F.support.attach,
        MvPolynomial.C (MvPolynomial.coeff d.1 F) * MvPolynomial.monomial d.1 (1 : K) := by
      conv_lhs => rw [F.as_sum]
      rw [← Finset.sum_attach F.support
        (fun d ↦ MvPolynomial.monomial d (MvPolynomial.coeff d F))]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      rw [MvPolynomial.C_mul_monomial, mul_one]
    have hleft : translatedTruncLE γ (aeval V F) =
        ∑ d ∈ F.support.attach, MvPolynomial.coeff d.1 F •
          translatedTruncLE γ (aeval V (MvPolynomial.monomial d.1 (1 : K))) := by
      conv_lhs => rw [hFsum]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      rw [map_mul, MvPolynomial.aeval_C, ← Algebra.smul_def, translatedTruncLE_smul]
    have hright : ∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i) =
        ∑ d ∈ F.support.attach, MvPolynomial.coeff d.1 F •
          ∑ i ∈ t, aeval V (MvPolynomial.pderiv i
            (MvPolynomial.monomial d.1 (1 : K))) * translatedTruncLE γ (V i) := by
      have hinner : ∀ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i) =
          ∑ d ∈ F.support.attach, MvPolynomial.coeff d.1 F •
            (aeval V (MvPolynomial.pderiv i (MvPolynomial.monomial d.1 (1 : K))) *
              translatedTruncLE γ (V i)) := by
        intro i _
        conv_lhs => rw [hFsum]
        rw [map_sum, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        rw [MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.aeval_C, ← Algebra.smul_def,
          smul_mul_assoc]
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      exact Finset.sum_congr rfl fun d _ ↦ (Finset.smul_sum).symm
    rw [hleft, hright, ← Finset.sum_sub_distrib]
    have hcongr : ∀ d ∈ F.support.attach,
        MvPolynomial.coeff d.1 F • translatedTruncLE γ
            (aeval V (MvPolynomial.monomial d.1 (1 : K))) -
          MvPolynomial.coeff d.1 F • ∑ i ∈ t, aeval V (MvPolynomial.pderiv i
            (MvPolynomial.monomial d.1 (1 : K))) * translatedTruncLE γ (V i) =
          MvPolynomial.coeff d.1 F •
            (translatedTruncLE γ (aeval V (MvPolynomial.monomial d.1 (1 : K))) -
              ∑ i ∈ t, aeval V (MvPolynomial.pderiv i
                (MvPolynomial.monomial d.1 (1 : K))) * translatedTruncLE γ (V i)) :=
      fun d _ ↦ (smul_sub _ _ _).symm
    rw [Finset.sum_congr rfl hcongr]
    refine (ν).map_sum_le_of_forall_le _ _ _ fun d _ ↦ ?_
    refine (degree_smul_le _ _).trans ?_
    exact (hboundOf d.1 d.2 γ hγ).trans
      (WithBot.coe_le_coe.mpr (Finset.le_sup (f := L) (Finset.mem_attach _ d)))

/-- **The differentiated relation.** If a weighted homogeneous polynomial of nonzero degree
evaluates to zero in the associated graded ring, then at all sufficiently late negative cutoffs
the sum of its evaluated partial derivatives against the truncated variables has degree bounded
by a single degree strictly below the polynomial degree.

The evaluated relation itself has degree strictly below the polynomial degree, so its truncations
eventually drop below a fixed bound; the Leibniz expansion contributes its own fixed bound; and
the two combine. This is the analytic condition required for a relation whose degree is a limit
ordinal, at a chosen cutoff. -/
theorem exists_lt_forall_degree_differentiatedRelation_le
    (xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded)
    (hVrep : ∀ i, Represents (V i) (wt i) (xg i))
    (hV : ∀ i, HasLowerTruncationDegree (V i) (wt i)) (hwt : ∀ i, wt i ≠ 0) (t : Finset ι)
    {F : MvPolynomial ι K} {c : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F c)
    (hc : c ≠ 0) (hFt : ∀ d ∈ F.support, d.support ⊆ t)
    (hrel : MvPolynomial.aeval xg F = 0) :
    ∃ lam : NatOrdinal.{u}, lam < c ∧ ∃ l : G, l < 0 ∧ ∀ γ : G, l < γ → γ < 0 →
      ν (∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i)) ≤
        (lam : WithBot NatOrdinal) := by
  classical
  -- The evaluated relation is a lift of the zero class, hence has degree below `c`.
  have hrep : Represents (aeval V F) c 0 := by
    have h := represents_aeval xg hVrep hF
    rwa [hrel] at h
  obtain ⟨c₀, hc₀lt, hc₀le⟩ := exists_le_of_degree_lt hrep.degree_lt_of_eq_zero hc
  -- Its truncations eventually drop below that degree.
  obtain ⟨l, hl, hcut⟩ := eventually_nhdsLT_iff_exists.mp
    (eventually_degree_translatedTruncLE_lt (aeval V F) c₀ hc₀le)
  obtain ⟨lam₁, hlam₁, hbound₁⟩ :=
    exists_lt_forall_degree_homogeneous_leibniz_le hV hwt t hF hc hFt
  refine ⟨max c₀ lam₁, max_lt hc₀lt hlam₁, l, hl, fun γ hlγ hγ0 ↦ ?_⟩
  have hsplit : ∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i) =
      translatedTruncLE γ (aeval V F) -
        (translatedTruncLE γ (aeval V F) -
          ∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i)) := by
    abel
  rw [hsplit]
  refine ((ν).map_sub_le_max _ _).trans (max_le ?_ ?_)
  · exact (hcut γ hlγ hγ0).le.trans (WithBot.coe_le_coe.mpr (le_max_left _ _))
  · exact (hbound₁ γ hγ0).trans (WithBot.coe_le_coe.mpr (le_max_right _ _))

/-! ### Separation data for the cofactor construction -/

open Classical in
/-- **The differentiated relation in polynomial form.** Replacing each truncated variable by a
polynomial that represents it turns the differentiated relation into a statement about a single
evaluated polynomial: a combination of the partial derivatives of the relation, with cofactors
whose monomials have weight strictly below that of the variable they multiply, evaluates to
something of degree bounded strictly below the degree of the relation.

The hypotheses on the representatives make every proper truncation drop strictly below its own
weight; the substitution is exact modulo series bounded strictly below zero, which the degree
bound absorbs. This is the form in which the relation can be compared against the graded pieces
of the polynomial ring. -/
theorem exists_lt_forall_degree_polynomialDifferentiatedRelation_le
    (xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded)
    (hVrep : ∀ i, Represents (V i) (wt i) (xg i))
    (hV : ∀ i, HasLowerTruncationDegree (V i) (wt i)) (hwt : ∀ i, wt i ≠ 0) (t : Finset ι)
    {F : MvPolynomial ι K} {c : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F c)
    (hc : c ≠ 0) (hFt : ∀ d ∈ F.support, d.support ⊆ t)
    (hrel : MvPolynomial.aeval xg F = 0) (hwtle : ∀ i ∈ t, wt i ≤ c)
    (hgen : ∀ β : NatOrdinal.{u}, β < c → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ P : MvPolynomial ι K, IsWeightedHomogeneous wt P β ∧ MvPolynomial.aeval xg P = y) :
    ∃ lam : NatOrdinal.{u}, lam < c ∧ ∃ l : G, l < 0 ∧ ∀ γ : G, l < γ → γ < 0 →
      ∃ P : ι → MvPolynomial ι K,
        (∀ i ∈ t, ∀ d ∈ (P i).support, Finsupp.weight wt d < wt i) ∧
        ν (aeval V (∑ i ∈ t, MvPolynomial.pderiv i F * P i)) ≤ (lam : WithBot NatOrdinal) := by
  classical
  obtain ⟨lam, hlam, l, hl, hbound⟩ :=
    exists_lt_forall_degree_differentiatedRelation_le xg hVrep hV hwt t hF hc hFt hrel
  refine ⟨lam, hlam, l, hl, fun γ hlγ hγ0 ↦ ?_⟩
  -- a polynomial representing each truncated variable, of weight below that variable's
  have hrep : ∀ i ∈ t, ∃ Q : MvPolynomial ι K,
      (∀ d ∈ Q.support, Finsupp.weight wt d < wt i) ∧
      ν (translatedTruncLE γ (V i) - aeval V Q) = ⊥ := by
    intro i hi
    have hlt : ν (translatedTruncLE γ (V i)) < (wt i : WithBot NatOrdinal) :=
      ((hasLowerTruncationDegree_iff).mp (hV i)).2 γ hγ0
    obtain ⟨Q, -, hQw, hQ⟩ :=
      exists_forall_weight_lt_and_degree_sub_aeval_eq_bot xg hVrep (wt i)
        (fun β hβ y hy ↦ hgen β (lt_of_lt_of_le hβ (hwtle i hi)) y hy)
        (translatedTruncLE γ (V i)) hlt
    exact ⟨Q, hQw, hQ⟩
  choose Q hQw hQ using hrep
  refine ⟨fun i ↦ if hi : i ∈ t then Q i hi else 0, fun i hi ↦ by
    simpa only [dif_pos hi] using hQw i hi, ?_⟩
  -- substituting is exact modulo series bounded strictly below zero
  have hsub : ν ((∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i)) -
      ∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) *
        aeval V (if hi : i ∈ t then Q i hi else 0)) = ⊥ := by
    refine degree_sub_eq_bot_sum t _ _ fun i hi ↦ ?_
    rw [dif_pos hi]
    exact degree_sub_eq_bot_mul (by simp) (hQ i hi)
  have hval : aeval V (∑ i ∈ t, MvPolynomial.pderiv i F *
      (if hi : i ∈ t then Q i hi else 0)) =
      ∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) *
        aeval V (if hi : i ∈ t then Q i hi else 0) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ map_mul _ _ _
  rw [hval]
  have hsplit : (∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) *
      aeval V (if hi : i ∈ t then Q i hi else 0)) =
      (∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i)) -
      ((∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) * translatedTruncLE γ (V i)) -
        ∑ i ∈ t, aeval V (MvPolynomial.pderiv i F) *
          aeval V (if hi : i ∈ t then Q i hi else 0)) := by ring
  rw [hsplit]
  refine ((ν).map_sub_le_max _ _).trans ?_
  rw [hsub]
  exact max_le (hbound γ hlγ hγ0) bot_le

/-- **The syzygy carried by the differentiated relation.** With evaluation injective in every
degree below that of the relation, the combination of partial derivatives produced above has all
its monomials of weight bounded strictly below the degree of the relation: in every degree between
that bound and the relation's own, the partial derivatives of the relation satisfy a syzygy.

The weight bound on the combination is forced by the shapes of its factors -- a monomial of
`∂F/∂X_i` weighs the relation's degree less that of `X_i`, and its cofactor weighs less than `X_i`
-- and injectivity then turns the degree bound on the evaluation into a bound on the weights
themselves. -/
theorem exists_lt_forall_weight_le_polynomialSyzygy
    (xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded)
    (hVrep : ∀ i, Represents (V i) (wt i) (xg i))
    (hV : ∀ i, HasLowerTruncationDegree (V i) (wt i)) (hwt : ∀ i, wt i ≠ 0) (t : Finset ι)
    {F : MvPolynomial ι K} {c : NatOrdinal.{u}} (hF : IsWeightedHomogeneous wt F c)
    (hc : c ≠ 0) (hFt : ∀ d ∈ F.support, d.support ⊆ t)
    (hrel : MvPolynomial.aeval xg F = 0) (hwtle : ∀ i ∈ t, wt i ≤ c)
    (hgen : ∀ β : NatOrdinal.{u}, β < c → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ P : MvPolynomial ι K, IsWeightedHomogeneous wt P β ∧ MvPolynomial.aeval xg P = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (P : MvPolynomial ι K), β < c →
      IsWeightedHomogeneous wt P β → MvPolynomial.aeval xg P = 0 → P = 0) :
    ∃ lam : NatOrdinal.{u}, lam < c ∧ ∃ l : G, l < 0 ∧ ∀ γ : G, l < γ → γ < 0 →
      ∃ P : ι → MvPolynomial ι K,
        (∀ i ∈ t, ∀ d ∈ (P i).support, Finsupp.weight wt d < wt i) ∧
        ∀ d ∈ (∑ i ∈ t, MvPolynomial.pderiv i F * P i).support,
          Finsupp.weight wt d ≤ lam := by
  classical
  obtain ⟨lam, hlam, l, hl, hb⟩ :=
    exists_lt_forall_degree_polynomialDifferentiatedRelation_le xg hVrep hV hwt t hF hc hFt hrel
      hwtle hgen
  refine ⟨lam, hlam, l, hl, fun γ hlγ hγ0 ↦ ?_⟩
  obtain ⟨P, hPw, hPd⟩ := hb γ hlγ hγ0
  refine ⟨P, hPw, fun d hd ↦ ?_⟩
  -- every monomial of the combination weighs less than the relation
  have hSw : ∀ d ∈ (∑ i ∈ t, MvPolynomial.pderiv i F * P i).support,
      Finsupp.weight wt d < c := by
    intro d' hd'
    obtain ⟨i, hi, hmem⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd')
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hmem)
    obtain ⟨e₀, he₀, hwe⟩ := MvPolynomial.exists_add_eq_weight_of_mem_support_pderiv wt hd₁
    rw [map_add]
    calc Finsupp.weight wt d₁ + Finsupp.weight wt d₂
        < Finsupp.weight wt d₁ + wt i := by
          exact add_lt_add_of_le_of_lt le_rfl (hPw i hi d₂ hd₂)
      _ = Finsupp.weight wt e₀ := hwe
      _ = c := hF (MvPolynomial.mem_support_iff.mp he₀)
  have hle := forall_weight_le_degree_aeval_of_injective xg hVrep hinj hSw d hd
  exact_mod_cast hle.trans hPd

omit [CharZero K] in
/-- **Syzygy propagation.** At every degree above the bound the syzygy provides, the part of
`(∂F/∂X_{v'}) · P_{v'}` in that degree and higher lies in the ideal generated by the remaining
partial derivatives of the relation.

The whole combination has no monomials that high, so the term at `v'` is the negative of the rest,
and the rest is visibly a combination of the other partial derivatives. Those are homogeneous, so
passing to the part in high degrees keeps the membership. -/
theorem componentsGE_mul_mem_span_of_polynomialSyzygy
    {t : Finset ι} {F : MvPolynomial ι K} {c : NatOrdinal.{u}}
    (hF : IsWeightedHomogeneous wt F c) {P : ι → MvPolynomial ι K} {lam : NatOrdinal.{u}}
    (hS : ∀ d ∈ (∑ i ∈ t, MvPolynomial.pderiv i F * P i).support,
      Finsupp.weight wt d ≤ lam)
    (v' : ι) (hv' : v' ∈ t) {τ : NatOrdinal.{u}} (hτ : lam < τ) :
    MvPolynomial.componentsGE wt τ (MvPolynomial.pderiv v' F * P v') ∈
      Ideal.span (Set.range fun j : {j : ι // j ∈ t ∧ j ≠ v'} ↦ MvPolynomial.pderiv j.1 F) := by
  classical
  -- the whole combination has nothing that high
  have hzero : MvPolynomial.componentsGE wt τ (∑ i ∈ t, MvPolynomial.pderiv i F * P i) = 0 :=
    MvPolynomial.componentsGE_eq_zero_of_forall_lt wt fun d hd ↦ (hS d hd).trans_lt hτ
  rw [← Finset.add_sum_erase _ _ hv', MvPolynomial.componentsGE_add] at hzero
  have hneg : MvPolynomial.componentsGE wt τ (MvPolynomial.pderiv v' F * P v') =
      -MvPolynomial.componentsGE wt τ
        (∑ i ∈ t.erase v', MvPolynomial.pderiv i F * P i) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hzero
  rw [hneg]
  refine neg_mem ?_
  -- the remaining partial derivatives are homogeneous
  have hhom : ∀ j : {j : ι // j ∈ t ∧ j ≠ v'},
      ∃ β, IsWeightedHomogeneous wt (MvPolynomial.pderiv j.1 F) β := by
    intro j
    by_cases h : ∃ β, β + wt j.1 = c
    · obtain ⟨β, hβ⟩ := h
      exact ⟨β, MvPolynomial.isWeightedHomogeneous_pderiv wt hF j.1 hβ⟩
    · exact ⟨0, by
        rw [MvPolynomial.pderiv_eq_zero_of_isWeightedHomogeneous wt hF j.1 h]
        exact MvPolynomial.isWeightedHomogeneous_zero _ _ _⟩
  choose β hβ using hhom
  haveI : Finite {j : ι // j ∈ t ∧ j ≠ v'} :=
    (t.finite_toSet.subset fun j (hj : j ∈ t ∧ j ≠ v') ↦ hj.1).to_subtype
  refine MvPolynomial.componentsGE_mem_span wt hβ ?_ τ
  refine Ideal.sum_mem _ fun i hi ↦ ?_
  exact Ideal.mul_mem_right _ _
    (Ideal.subset_span ⟨⟨i, Finset.mem_of_mem_erase hi, Finset.ne_of_mem_erase hi⟩, rfl⟩)

end HahnSeries.Nonpositive
