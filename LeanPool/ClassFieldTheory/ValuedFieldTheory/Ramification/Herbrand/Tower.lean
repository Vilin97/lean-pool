/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.Ramification
/-!
# Finite-group sources for Herbrand's theorem

This file isolates the part of the Herbrand quotient theorem which is
independent of valuations.  A discrete nonarchimedean depth has the two
properties of `i(σ) = v(σ(a) - a)` used in the ramification-depth proof: multiplication
does not decrease the minimum depth, and it is exactly the minimum when the
two depths differ.

For a finite group modulo a normal subgroup, every nontrivial quotient fibre
has a representative of maximal (finite) depth.  The main result below proves
the identity

`i(σ τ) = min (i(σ), i(τ))`

for such a representative `σ` and every `τ` in the normal subgroup.  The
remaining valued-field input for the Herbrand quotient theorem is the quotient-depth identity:
  the depth
on the quotient is the normalized sum of the depths in this fibre.  That
input is deliberately not packaged here as a hypothesis or data field.
-/

@[expose] public section

noncomputable
section

universe u

namespace RamificationTheory.DiscreteValuationField
namespace HerbrandGroupTheory

variable {G : Type u} [Group G]

/-- The purely group-theoretic laws of the discrete depth used in the proof
of Herbrand's theorem.  The value `⊤` occurs exactly at the identity. -/
structure NonarchimedeanDepth (G : Type u) [Group G] where
  /-- The discrete nonarchimedean depth of each group element. -/
  depth : G → WithTop ℕ
  /-- An element has infinite depth exactly when it is the identity. -/
  depth_eq_top_iff : ∀ σ, depth σ = ⊤ ↔ σ = 1
  /-- The depth of a product is at least the minimum depth of its factors. -/
  depth_mul_ge_min : ∀ σ τ, min (depth σ) (depth τ) ≤ depth (σ * τ)
  /-- Factors of unequal depth give a product whose depth is their minimum. -/
  depth_mul_eq_min_of_ne :
    ∀ {σ τ}, depth σ ≠ depth τ → depth (σ * τ) = min (depth σ) (depth τ)
  /-- Depth is invariant under conjugation. -/
  depth_conj : ∀ γ σ, depth (γ * σ * γ⁻¹) = depth σ

namespace NonarchimedeanDepth

variable (D : NonarchimedeanDepth G)

/-- States the theorem `depth_one`. -/
@[simp] theorem depth_one : D.depth 1 = ⊤ :=
  (D.depth_eq_top_iff 1).2 rfl

/-- States the theorem `depth_ne_top_iff`. -/
theorem depth_ne_top_iff {σ : G} : D.depth σ ≠ ⊤ ↔ σ ≠ 1 := by
  rw [not_iff_not]
  exact D.depth_eq_top_iff σ

variable (H : Subgroup G) [H.Normal]

/-- The fibre of the canonical quotient map over `q`. -/
abbrev QuotientFiber (q : G ⧸ H) : Type u :=
  {σ : G // QuotientGroup.mk' H σ = q}

/-- A subgroup of a finite group is equipped with its finite enumeration. -/
noncomputable local instance subgroupFintype [Finite G] : Fintype H :=
  Fintype.ofFinite H

/-- The finite ambient group is equipped with an enumeration for the depth sums. -/
noncomputable local instance groupFintype [Finite G] : Fintype G :=
  Fintype.ofFinite G

/-- Each fiber of the quotient map from a finite group has a finite enumeration. -/
noncomputable local instance quotientFiberFintype [Finite G] (q : G ⧸ H) :
    Fintype (QuotientFiber H q) :=
  Fintype.ofFinite (QuotientFiber H q)

/-- The quotient of the finite ambient group is equipped with a finite enumeration. -/
noncomputable local instance quotientFintype [Finite G] : Fintype (G ⧸ H) :=
  Fintype.ofFinite (G ⧸ H)

/-- Provides the instance `quotientFiber_nonempty`. -/
instance quotientFiber_nonempty (q : G ⧸ H) : Nonempty (QuotientFiber H q) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective H q
  exact ⟨⟨σ, rfl⟩⟩

/-- States the theorem `ne_one_of_mem_quotientFiber`. -/
theorem ne_one_of_mem_quotientFiber {q : G ⧸ H} (hq : q ≠ 1)
    (σ : QuotientFiber H q) : (σ : G) ≠ 1 := by
  intro hσ
  apply hq
  rw [← σ.property, hσ]
  simp

/-- States the theorem `depth_ne_top_of_mem_quotientFiber`. -/
theorem depth_ne_top_of_mem_quotientFiber {q : G ⧸ H} (hq : q ≠ 1)
    (σ : QuotientFiber H q) : D.depth (σ : G) ≠ ⊤ :=
  D.depth_ne_top_iff.2 (ne_one_of_mem_quotientFiber H hq σ)

/-- The finite natural depth of an element in a nontrivial quotient fibre. -/
def quotientFiberDepth {q : G ⧸ H} (hq : q ≠ 1)
    (σ : QuotientFiber H q) : ℕ :=
  (D.depth (σ : G)).untop (D.depth_ne_top_of_mem_quotientFiber H hq σ)

/-- States the theorem `coe_quotientFiberDepth`. -/
theorem coe_quotientFiberDepth {q : G ⧸ H} (hq : q ≠ 1)
    (σ : QuotientFiber H q) :
    (D.quotientFiberDepth H hq σ : WithTop ℕ) = D.depth (σ : G) :=
  WithTop.coe_untop _ _

/-- Every nontrivial fibre of a finite quotient has a representative of
maximal depth.  The conclusion is stated back in `WithTop ℕ`, rather than in
terms of the auxiliary `untop`, so it can be fed directly into the valuation
identity used in the Herbrand quotient theorem. -/
theorem exists_maximal_depth_representative [Finite G]
    {q : G ⧸ H} (hq : q ≠ 1) :
    ∃ σ : G, QuotientGroup.mk' H σ = q ∧
      ∀ γ : G, QuotientGroup.mk' H γ = q → D.depth γ ≤ D.depth σ := by
  classical
  obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image
    (Finset.univ : Finset (QuotientFiber H q))
    (D.quotientFiberDepth H hq) Finset.univ_nonempty
  refine ⟨σ, σ.property, ?_⟩
  intro γ hγ
  let γ' : QuotientFiber H q := ⟨γ, hγ⟩
  have hnat : D.quotientFiberDepth H hq γ' ≤
      D.quotientFiberDepth H hq σ := hσ γ' (Finset.mem_univ γ')
  rw [← D.coe_quotientFiberDepth H hq γ',
    ← D.coe_quotientFiberDepth H hq σ]
  exact WithTop.coe_le_coe.2 hnat

/-- A right coset is naturally equivalent to the corresponding quotient
fibre.  This is the finite-sum reindexing used after choosing a maximal-depth
representative. -/
def rightCosetEquivQuotientFiber (σ : G) : H ≃ QuotientFiber H (QuotientGroup.mk' H σ) where
  toFun τ := ⟨σ * τ, by
    rw [map_mul]
    simp [(QuotientGroup.eq_one_iff (N := H) (x := (τ : G))).2 τ.property]⟩
  invFun γ := ⟨σ⁻¹ * γ, by
    apply (QuotientGroup.eq_one_iff (N := H) (x := σ⁻¹ * (γ : G))).1
    change QuotientGroup.mk' H (σ⁻¹ * (γ : G)) = 1
    rw [map_mul, map_inv, γ.property]
    simp⟩
  left_inv τ := by
    apply Subtype.ext
    simp
  right_inv γ := by
    apply Subtype.ext
    simp

/-- States the theorem `card_quotientFiber`. -/
theorem card_quotientFiber [Finite G] (σ : G) :
    Fintype.card (QuotientFiber H (QuotientGroup.mk' H σ)) = Fintype.card H := by
  classical
  exact (Fintype.card_congr (rightCosetEquivQuotientFiber H σ)).symm

/-- Reindex a sum over a quotient fibre by multiplication with elements of
the normal subgroup. -/
theorem sum_quotientFiber_eq_sum_subgroup [Finite G]
    {M : Type*} [AddCommMonoid M] (f : G → M) (σ : G) :
    (∑ γ : QuotientFiber H (QuotientGroup.mk' H σ), f (γ : G)) =
      ∑ τ : H, f (σ * τ) := by
  classical
  simpa using Fintype.sum_equiv
    (rightCosetEquivQuotientFiber H σ).symm
    (fun γ : QuotientFiber H (QuotientGroup.mk' H σ) => f (γ : G))
    (fun τ : H => f (σ * τ)) (fun γ => by
      change f (γ : G) = f (σ * (σ⁻¹ * (γ : G)))
      simp)

/-- Partition a finite sum over `G` into the fibres of the quotient map. -/
theorem sum_quotientFiber [Finite G]
    {M : Type*} [AddCommMonoid M] (f : G → M) :
    (∑ q : G ⧸ H, ∑ σ : QuotientFiber H q, f (σ : G)) = ∑ σ : G, f σ := by
  classical
  calc
    (∑ q : G ⧸ H, ∑ σ : QuotientFiber H q, f (σ : G)) =
        ∑ z : (q : G ⧸ H) × QuotientFiber H q, f (z.2 : G) :=
      (Fintype.sum_sigma
        (fun z : (q : G ⧸ H) × QuotientFiber H q => f (z.2 : G))).symm
    _ = ∑ σ : G, f σ := Fintype.sum_equiv
      (Equiv.sigmaFiberEquiv (QuotientGroup.mk' H))
      (fun z : (q : G ⧸ H) × QuotientFiber H q => f (z.2 : G))
      f (fun _ => rfl)

/-- The maximal-representative identity in the proof of Herbrand's theorem.
If `σ` has maximal depth in its quotient fibre, then multiplication by every
`τ ∈ H` truncates the depth exactly at `i(σ)`. -/
theorem depth_mul_eq_min_of_maximal_representative
    {σ : G}
    (hmax : ∀ γ : G, QuotientGroup.mk' H γ = QuotientGroup.mk' H σ →
      D.depth γ ≤ D.depth σ)
    (τ : H) :
    D.depth (σ * τ) = min (D.depth (τ : G)) (D.depth σ) := by
  have hfiber : QuotientGroup.mk' H (σ * (τ : G)) = QuotientGroup.mk' H σ := by
    rw [map_mul]
    simp [(QuotientGroup.eq_one_iff (N := H) (x := (τ : G))).2 τ.property]
  rcases lt_trichotomy (D.depth (τ : G)) (D.depth σ) with hlt | heq | hgt
  · simpa [min_comm] using D.depth_mul_eq_min_of_ne hlt.ne'
  · rw [heq, min_self]
    apply le_antisymm (hmax _ hfiber)
    simpa [heq] using D.depth_mul_ge_min σ (τ : G)
  · simpa [min_comm] using D.depth_mul_eq_min_of_ne hgt.ne

/-- The fibre-sum form of the maximal-representative identity.  Composing
`f` with a finite-depth cast gives exactly the sum appearing in
the Herbrand quotient theorem, after the quotient-depth identity supplies the quotient-depth
  average. -/
theorem sum_depth_quotientFiber_eq_sum_min_of_maximal_representative
    [Finite G] {M : Type*} [AddCommMonoid M]
    (f : WithTop ℕ → M) {σ : G}
    (hmax : ∀ γ : G, QuotientGroup.mk' H γ = QuotientGroup.mk' H σ →
      D.depth γ ≤ D.depth σ) :
    (∑ γ : QuotientFiber H (QuotientGroup.mk' H σ), f (D.depth (γ : G))) =
      ∑ τ : H, f (min (D.depth (τ : G)) (D.depth σ)) := by
  rw [sum_quotientFiber_eq_sum_subgroup H (fun γ => f (D.depth γ)) σ]
  apply Finset.sum_congr rfl
  intro τ _
  rw [D.depth_mul_eq_min_of_maximal_representative H hmax τ]

/-- Combined existence form used verbatim in the group-theoretic step of
the Herbrand quotient theorem. -/
theorem exists_representative_depth_mul_eq_min [Finite G]
    {q : G ⧸ H} (hq : q ≠ 1) :
    ∃ σ : G, QuotientGroup.mk' H σ = q ∧
      ∀ τ : H, D.depth (σ * τ) = min (D.depth (τ : G)) (D.depth σ) := by
  obtain ⟨σ, hσq, hmax⟩ := D.exists_maximal_depth_representative H hq
  refine ⟨σ, hσq, ?_⟩
  intro τ
  apply D.depth_mul_eq_min_of_maximal_representative H
  intro γ hγ
  exact hmax γ (hγ.trans hσq)

/-- Existence form of the fibre-sum identity for a nontrivial quotient
element. -/
theorem exists_representative_sum_depth_eq_sum_min [Finite G]
    {M : Type*} [AddCommMonoid M] (f : WithTop ℕ → M)
    {q : G ⧸ H} (hq : q ≠ 1) :
    ∃ σ : G, QuotientGroup.mk' H σ = q ∧
      (∑ γ : QuotientFiber H q, f (D.depth (γ : G))) =
        ∑ τ : H, f (min (D.depth (τ : G)) (D.depth σ)) := by
  obtain ⟨σ, hσq, hmax⟩ := D.exists_maximal_depth_representative H hq
  refine ⟨σ, hσq, ?_⟩
  rw [← hσq]
  apply D.sum_depth_quotientFiber_eq_sum_min_of_maximal_representative H f
  intro γ hγ
  exact hmax γ (hγ.trans hσq)

end NonarchimedeanDepth
end HerbrandGroupTheory
end RamificationTheory.DiscreteValuationField
