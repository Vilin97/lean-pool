/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import Mathlib

/-!
# Finite combinatorics used in the Wallace construction

This file formalizes the finite torsion-free-group bookkeeping used in Sections 4 and 5 of the
current paper:

* the reindexing part of the triangular enumeration;
* extraction of finite bounded-independent sets;
* uniform integer dependence for bounded finite vectors;
* bounded deletion of at most `|A|` points.

The paper writes integer bounds as `|c| ≤ M`.  We use `Int.natAbs c ≤ M`, which is
definitionally the corresponding natural-number inequality.
-/

open scoped BigOperators
open Set

universe u v

namespace Wallace
namespace FiniteCombinatorics

noncomputable section

section Triangular

variable {I : Type u} {T : Type v} [LinearOrder I]

/-- The support condition in the triangular enumeration: every coordinate occurring in a term of
the sequence lies strictly below its assigned index. -/
def SupportedBelow (s : ℕ → I →₀ ℤ) (i : I) : Prop :=
  ∀ n j, j ∈ (s n).support → j < i

end Triangular

section Relations

variable {G : Type u} [AddCommGroup G]

/-- A finite set is `M`-independent if every integer relation whose coefficients have absolute
value at most `M` is trivial.  This is the paper's definition, specialized to a finite set. -/
def BoundedIndependent (M : ℕ) (X : Finset G) : Prop :=
  ∀ c : G → ℤ, (∀ x ∈ X, Int.natAbs (c x) ≤ M) →
    (∑ x ∈ X, c x • x) = 0 → ∀ x ∈ X, c x = 0

/-- A point is forbidden over `B` if it satisfies one of the finitely many bounded equations used
in the bounded-independence extraction argument. -/
def Forbidden (M : ℕ) (B : Finset G) (x : G) : Prop :=
  ∃ (q : ℤ) (c : B → ℤ), q ≠ 0 ∧ Int.natAbs q ≤ M ∧
    (∀ b, Int.natAbs (c b) ≤ M) ∧
      q • x + ∑ b, c b • (b : G) = 0

/-- The finite interval of integer coefficients of absolute value at most `M`. -/
def boundedIntFinset (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

@[simp]
theorem mem_boundedIntFinset_iff {M : ℕ} {z : ℤ} :
    z ∈ boundedIntFinset M ↔ Int.natAbs z ≤ M := by
  simp only [boundedIntFinset, Finset.mem_Icc]
  constructor
  · intro h
    have habs : |z| ≤ (M : ℤ) := abs_le.mpr h
    have hcast : (Int.natAbs z : ℤ) ≤ (M : ℤ) := by
      rw [Int.abs_eq_natAbs] at habs
      exact habs
    exact Int.ofNat_le.mp hcast
  · intro h
    apply abs_le.mp
    have hcast : (Int.natAbs z : ℤ) ≤ (M : ℤ) := Int.ofNat_le.mpr h
    rw [Int.abs_eq_natAbs]
    exact hcast

/-- All bounded coefficient functions on a finite set. -/
def coefficientPatterns (M : ℕ) (B : Finset G) : Finset (B → ℤ) := by
  classical
  exact Fintype.piFinset fun _ ↦ boundedIntFinset M

omit [AddCommGroup G] in
@[simp] theorem mem_coefficientPatterns_iff {M : ℕ} {B : Finset G} {c : B → ℤ} :
    c ∈ coefficientPatterns M B ↔ ∀ b, Int.natAbs (c b) ≤ M := by
  classical
  rw [coefficientPatterns, Fintype.mem_piFinset]
  simp only [mem_boundedIntFinset_iff]

noncomputable def equationSolution (B : Finset G) (q : ℤ) (c : B → ℤ) : G :=
  by
    classical
    exact if h : ∃ x : G, q • x + ∑ b, c b • (b : G) = 0 then Classical.choose h else 0

theorem equationSolution_spec {B : Finset G} {q : ℤ} {c : B → ℤ}
    (h : ∃ x : G, q • x + ∑ b, c b • (b : G) = 0) :
    q • equationSolution B q c + ∑ b, c b • (b : G) = 0 := by
  classical
  simp only [equationSolution, dif_pos h]
  exact Classical.choose_spec h

/-- A concrete finite set containing every forbidden point. -/
noncomputable def forbiddenFinset (M : ℕ) (B : Finset G) : Finset G :=
  by
    classical
    exact ((boundedIntFinset M).erase 0 ×ˢ coefficientPatterns M B).image
      (fun p ↦ equationSolution B p.1 p.2)

theorem forbidden_mem_forbiddenFinset [IsAddTorsionFree G]
    {M : ℕ} {B : Finset G} {x : G} (hx : Forbidden M B x) :
    x ∈ forbiddenFinset M B := by
  classical
  rcases hx with ⟨q, c, hq0, hqM, hcM, hx⟩
  have hqmem : q ∈ (boundedIntFinset M).erase 0 := by
    simp [hq0, hqM]
  have hcmem : c ∈ coefficientPatterns M B :=
    mem_coefficientPatterns_iff.mpr hcM
  have hw := equationSolution_spec (B := B) (q := q) (c := c) ⟨x, hx⟩
  have hqx : q • x = q • equationSolution B q c := by
    calc
      q • x = -(∑ b, c b • (b : G)) := eq_neg_of_add_eq_zero_left hx
      _ = q • equationSolution B q c := (eq_neg_of_add_eq_zero_left hw).symm
  have hxeq : x = equationSolution B q c :=
    zsmul_right_injective hq0 hqx
  rw [hxeq]
  exact Finset.mem_image.mpr ⟨(q, c), Finset.mem_product.mpr ⟨hqmem, hcmem⟩, rfl⟩

theorem boundedIndependent_insert_of_not_forbidden [IsAddTorsionFree G] [DecidableEq G]
    {M : ℕ} {Y : Finset G} {x : G}
    (hY : BoundedIndependent M Y) (hxY : x ∉ Y)
    (hx : ¬ Forbidden M Y x) : BoundedIndependent M (insert x Y) := by
  classical
  intro c hc hsum
  have hsum' : c x • x + ∑ y ∈ Y, c y • y = 0 := by
    simpa [Finset.sum_insert, hxY] using hsum
  have hcx : c x = 0 := by
    by_contra hcx0
    apply hx
    let cY : Y → ℤ := fun y ↦ c y
    refine ⟨c x, cY, hcx0, hc x (Finset.mem_insert_self x Y), ?_, ?_⟩
    · intro y
      exact hc y (Finset.mem_insert_of_mem y.property)
    · rw [← Finset.sum_finset_coe] at hsum'
      exact hsum'
  have hsumY : ∑ y ∈ Y, c y • y = 0 := by
    simpa [hcx] using hsum'
  have hcY : ∀ y ∈ Y, c y = 0 :=
    hY c (fun y hy ↦ hc y (Finset.mem_insert_of_mem hy)) hsumY
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hzY
  · exact hcx
  · exact hcY z hzY

section IntegerDependence

/-- `s+1` integer vectors in `ℤ^s` have a nontrivial integer dependence.

We first obtain a rational dependence by the dimension theorem and then clear all denominators
using mathlib's localization API. -/
theorem exists_integer_dependence (s : ℕ) (b : Fin (s + 1) → Fin s → ℤ) :
    ∃ coeff : Fin (s + 1) → ℤ,
      (∃ i, coeff i ≠ 0) ∧ ∀ j, ∑ i, coeff i * b i j = 0 := by
  classical
  let v : Fin (s + 1) → (Fin s → ℚ) := fun i j ↦ (b i j : ℚ)
  have hv : ¬ LinearIndependent ℚ v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp at hcard
  obtain ⟨g, hgsum, i₀, hgi₀⟩ := Fintype.not_linearIndependent_iff.mp hv
  let D : Submonoid.pos ℤ :=
    IsLocalization.commonDenom (Submonoid.pos ℤ) Finset.univ g
  let coeff : Fin (s + 1) → ℤ := fun i ↦
    IsLocalization.integerMultiple (Submonoid.pos ℤ) Finset.univ g
      ⟨i, Finset.mem_univ i⟩
  have hcoeffCast (i : Fin (s + 1)) : (coeff i : ℚ) = (D : ℤ) • g i := by
    exact IsLocalization.map_integerMultiple (Submonoid.pos ℤ) Finset.univ g
      ⟨i, Finset.mem_univ i⟩
  have hD0 : (D : ℤ) ≠ 0 := ne_of_gt D.property
  have hcoeffi₀ : coeff i₀ ≠ 0 := by
    intro hzero
    have hz : (D : ℤ) • g i₀ = 0 := by
      rw [← hcoeffCast]
      simp [hzero]
    have : g i₀ = 0 := by
      simpa [hD0] using hz
    exact hgi₀ this
  refine ⟨coeff, ⟨i₀, hcoeffi₀⟩, ?_⟩
  intro j
  have hcoord : ∑ i, g i * (b i j : ℚ) = 0 := by
    have := congrFun hgsum j
    simpa [v, smul_eq_mul] using this
  have hcast : ((∑ i, coeff i * b i j : ℤ) : ℚ) = 0 := by
    simp only [Int.cast_sum, Int.cast_mul]
    simp_rw [hcoeffCast]
    simp_rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    simp [hcoord]
  exact_mod_cast hcast

/-- Integer coefficients in `[-Q,Q]`, as a finite type. -/
abbrev BoundedInt (Q : ℕ) := ↑(boundedIntFinset Q)

/-- All bounded vector families of every dimension at most `r`. -/
structure BoundedVectorFamily (r Q : ℕ) where
  size : Fin (r + 1)
  vec : Fin (size + 1) → Fin size → BoundedInt Q
deriving Fintype

noncomputable def chosenIntegerDependence {r Q : ℕ} (B : BoundedVectorFamily r Q) :
    Fin (B.size + 1) → ℤ :=
  Classical.choose <| exists_integer_dependence B.size fun i j ↦ B.vec i j

theorem chosenIntegerDependence_spec {r Q : ℕ} (B : BoundedVectorFamily r Q) :
    (∃ i, chosenIntegerDependence B i ≠ 0) ∧
      ∀ j, ∑ i, chosenIntegerDependence B i * (B.vec i j : ℤ) = 0 :=
  Classical.choose_spec <| exists_integer_dependence B.size fun i j ↦ B.vec i j

noncomputable def familyDependenceBound {r Q : ℕ} (B : BoundedVectorFamily r Q) : ℕ :=
  Finset.univ.sup fun i ↦ Int.natAbs (chosenIntegerDependence B i)

/-- A uniform bound for an integer dependence among any `s+1` vectors in `ℤ^s`, for `s ≤ r`,
whose entries have absolute value at most `Q`.  Finiteness of the parameter space gives the
uniformity; no unproved determinant estimate is used. -/
noncomputable def integerDependenceBound (r Q : ℕ) : ℕ :=
  Finset.univ.sup fun B : BoundedVectorFamily r Q ↦ familyDependenceBound B

theorem exists_uniform_integer_dependence
    {r Q s : ℕ} (hs : s ≤ r) (b : Fin (s + 1) → Fin s → ℤ)
    (hb : ∀ i j, Int.natAbs (b i j) ≤ Q) :
    ∃ coeff : Fin (s + 1) → ℤ,
      (∃ i, coeff i ≠ 0) ∧
        (∀ j, ∑ i, coeff i * b i j = 0) ∧
          ∀ i, Int.natAbs (coeff i) ≤ integerDependenceBound r Q := by
  classical
  let B : BoundedVectorFamily r Q :=
    { size := ⟨s, Nat.lt_succ_iff.mpr hs⟩
      vec := fun i j ↦ ⟨b i j, mem_boundedIntFinset_iff.mpr (hb i j)⟩ }
  let coeff : Fin (s + 1) → ℤ := chosenIntegerDependence B
  have hspec := chosenIntegerDependence_spec B
  refine ⟨coeff, hspec.1, ?_, ?_⟩
  · intro j
    exact hspec.2 j
  · intro i
    apply le_trans (Finset.le_sup (s := Finset.univ) (f := fun k ↦
      Int.natAbs (chosenIntegerDependence B k)) (Finset.mem_univ i))
    exact Finset.le_sup (s := Finset.univ) (f := familyDependenceBound)
      (Finset.mem_univ B)

end IntegerDependence

section BoundedDeletion

/-- A bounded relation using both the finite families `A` and `Y`. -/
def HasMixedRelation (Q : ℕ) (A Y : Finset G) : Prop :=
  ∃ (b c : G → ℤ),
    (∀ a ∈ A, Int.natAbs (b a) ≤ Q) ∧
    (∀ y ∈ Y, Int.natAbs (c y) ≤ Q) ∧
    (∃ a ∈ A, b a ≠ 0) ∧
    (∃ y ∈ Y, c y ≠ 0) ∧
      (∑ a ∈ A, b a • a) + ∑ y ∈ Y, c y • y = 0

def MixedRelationFree (Q : ℕ) (A Y : Finset G) : Prop :=
  ¬ HasMixedRelation Q A Y

theorem mixedRelationFree_empty (Q : ℕ) (A : Finset G) :
    MixedRelationFree Q A ∅ := by
  rintro ⟨b, c, hb, hc, hb0, hc0, hsum⟩
  simp at hc0

/-- A maximal relation-free subset of `X`.  Maximality is by cardinality and therefore implies
that adjoining any omitted point creates a mixed relation. -/
theorem exists_maximal_mixedRelationFree [DecidableEq G] (Q : ℕ) (A X : Finset G) :
    ∃ Y : Finset G, Y ⊆ X ∧ MixedRelationFree Q A Y ∧
      ∀ x ∈ X, x ∉ Y → HasMixedRelation Q A (insert x Y) := by
  classical
  let candidates : Finset (Finset G) :=
    X.powerset.filter fun Y ↦ MixedRelationFree Q A Y
  have hempty : ∅ ∈ candidates := by
    simp [candidates, mixedRelationFree_empty]
  have hne : candidates.Nonempty := ⟨∅, hempty⟩
  obtain ⟨Y, hYmem, hYmax⟩ := candidates.exists_mem_eq_sup hne Finset.card
  have hYX : Y ⊆ X := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hYmem).1
  have hYfree : MixedRelationFree Q A Y := (Finset.mem_filter.mp hYmem).2
  refine ⟨Y, hYX, hYfree, ?_⟩
  intro x hxX hxY
  by_contra hfree
  have hinsertX : insert x Y ⊆ X := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzY
    · exact hxX
    · exact hYX hzY
  have hinsertMem : insert x Y ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hinsertX, hfree⟩
  have hle : (insert x Y).card ≤ candidates.sup Finset.card :=
    Finset.le_sup (s := candidates) (f := Finset.card) hinsertMem
  rw [hYmax, Finset.card_insert_of_notMem hxY] at hle
  omega

theorem mixedRelation_insert_witness [DecidableEq G]
    {Q : ℕ} {A Y : Finset G} {x : G}
    (hY : MixedRelationFree Q A Y) (hxY : x ∉ Y)
    (hrel : HasMixedRelation Q A (insert x Y)) :
    ∃ (b c : G → ℤ),
      (∀ a ∈ A, Int.natAbs (b a) ≤ Q) ∧
      (∀ z ∈ insert x Y, Int.natAbs (c z) ≤ Q) ∧
      (∃ a ∈ A, b a ≠ 0) ∧ c x ≠ 0 ∧
        (∑ a ∈ A, b a • a) + ∑ z ∈ insert x Y, c z • z = 0 := by
  rcases hrel with ⟨b, c, hbQ, hcQ, hb0, hc0, hsum⟩
  have hcx : c x ≠ 0 := by
    intro hcx0
    apply hY
    refine ⟨b, c, hbQ, ?_, hb0, ?_, ?_⟩
    · intro y hy
      exact hcQ y (Finset.mem_insert_of_mem hy)
    · rcases hc0 with ⟨z, hz, hcz⟩
      rcases Finset.mem_insert.mp hz with rfl | hzY
      · exact (hcz hcx0).elim
      · exact ⟨z, hzY, hcz⟩
    · simpa [Finset.sum_insert, hxY, hcx0] using hsum
  exact ⟨b, c, hbQ, hcQ, hb0, hcx, hsum⟩

/-- The independence threshold from the current paper.  Here `integerDependenceBound r Q` is
the finite maximum denoted by `B(r,Q)`, so this is exactly `M(r,Q) = (r+1) B(r,Q) Q`. -/
noncomputable def deletionIndependenceBound (r Q : ℕ) : ℕ :=
  (r + 1) * (integerDependenceBound r Q * Q)

/-- **Bounded deletion** (Lemma `lem:bounded-deletion` in the paper).

From an adequately bounded-independent finite set `X`, delete at most `|A|` points so that no
bounded relation uses both `A` and the retained set.  The threshold and the conclusion—including
the sharp deletion count `|X \ Y| ≤ |A|`—are the ones in the paper. -/
theorem bounded_deletion [IsAddTorsionFree G] [DecidableEq G]
    (r Q : ℕ) (A X : Finset G) (hAr : A.card ≤ r)
    (hX : BoundedIndependent (deletionIndependenceBound r Q) X) :
    ∃ Y : Finset G, Y ⊆ X ∧ (X \ Y).card ≤ A.card ∧ MixedRelationFree Q A Y := by
  classical
  obtain ⟨Y, hYX, hYfree, hYmax⟩ := exists_maximal_mixedRelationFree Q A X
  refine ⟨Y, hYX, ?_, hYfree⟩
  by_contra hcard
  have hlarge : A.card + 1 ≤ (X \ Y).card := by omega
  obtain ⟨D, hDsub, hDcard⟩ :=
    Finset.exists_subset_card_eq hlarge
  let s := A.card
  let eA : Fin s ≃ A := A.equivFin.symm
  let eD : Fin (s + 1) ≃ D :=
    (finCongr hDcard.symm).trans D.equivFin.symm
  let point : Fin (s + 1) → G := fun i ↦ (eD i : G)
  have hpointD (i : Fin (s + 1)) : point i ∈ D := (eD i).property
  have hpointX (i : Fin (s + 1)) : point i ∈ X :=
    (Finset.mem_sdiff.mp (hDsub (hpointD i))).1
  have hpointY (i : Fin (s + 1)) : point i ∉ Y :=
    (Finset.mem_sdiff.mp (hDsub (hpointD i))).2
  have hwitness (i : Fin (s + 1)) :=
    mixedRelation_insert_witness hYfree (hpointY i)
      (hYmax (point i) (hpointX i) (hpointY i))
  choose b c hbQ hcQ hb0 hcx hsum using hwitness
  obtain ⟨coeff, hcoeff0, hcoeffDep, hcoeffBound⟩ :=
    exists_uniform_integer_dependence hAr
      (fun i j ↦ b i (eA j))
      (fun i j ↦ hbQ i (eA j) (eA j).property)
  let cN : Fin (s + 1) → G → ℤ := fun i z ↦
    if z ∈ insert (point i) Y then c i z else 0
  have hcNBound (i : Fin (s + 1)) (z : G) : Int.natAbs (cN i z) ≤ Q := by
    by_cases hz : z ∈ insert (point i) Y
    · rw [show cN i z = c i z by simp only [cN, if_pos hz]]
      exact hcQ i z hz
    · rw [show cN i z = 0 by simp only [cN, if_neg hz]]
      simp
  have hcNPoint (i : Fin (s + 1)) : cN i (point i) ≠ 0 := by
    simpa [cN] using hcx i
  have hsumN (i : Fin (s + 1)) :
      (∑ a ∈ A, b i a • a) +
        ∑ z ∈ insert (point i) Y, cN i z • z = 0 := by
    rw [← hsum i]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    rw [show cN i z = c i z by simp only [cN, if_pos hz]]
  let k : G → ℤ := fun z ↦ ∑ i, coeff i * cN i z
  have hkBound : ∀ z ∈ X,
      Int.natAbs (k z) ≤ deletionIndependenceBound r Q := by
    intro z hzX
    calc
      Int.natAbs (k z) ≤ ∑ i ∈ (Finset.univ : Finset (Fin (s + 1))),
          Int.natAbs (coeff i * cN i z) := by
            simpa [k] using Int.natAbs_sum_le
              (Finset.univ : Finset (Fin (s + 1)))
              (fun i ↦ coeff i * cN i z)
      _ = ∑ i : Fin (s + 1), Int.natAbs (coeff i) * Int.natAbs (cN i z) := by
            simp [Int.natAbs_mul]
      _ ≤ ∑ _i : Fin (s + 1), integerDependenceBound r Q * Q := by
            exact Finset.sum_le_sum fun i _ ↦
              Nat.mul_le_mul (hcoeffBound i) (hcNBound i z)
      _ = (s + 1) * (integerDependenceBound r Q * Q) := by simp
      _ ≤ (r + 1) * (integerDependenceBound r Q * Q) := by
            exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hAr 1)
      _ = deletionIndependenceBound r Q := rfl
  have hApart :
      ∑ i, coeff i • (∑ a ∈ A, b i a • a) = 0 := by
    calc
      ∑ i, coeff i • (∑ a ∈ A, b i a • a) =
          ∑ a ∈ A, (∑ i, coeff i * b i a) • a := by
            simp_rw [Finset.smul_sum, smul_smul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a ha
            exact (Finset.sum_smul (s := Finset.univ)
              (f := fun i ↦ coeff i * b i a) (x := a)).symm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hdep := hcoeffDep (eA.symm ⟨a, ha⟩)
        have hea : (eA (eA.symm ⟨a, ha⟩) : G) = a := by simp
        simp only [hea] at hdep
        rw [hdep, zero_zsmul]
  have htotal :
      ∑ i, coeff i •
        ((∑ a ∈ A, b i a • a) +
          ∑ z ∈ insert (point i) Y, cN i z • z) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hsumN i, smul_zero]
  have hXpart :
      ∑ i, coeff i •
        (∑ z ∈ insert (point i) Y, cN i z • z) = 0 := by
    have hsplit := htotal
    simp only [smul_add, Finset.sum_add_distrib] at hsplit
    rw [hApart, zero_add] at hsplit
    exact hsplit
  have hinsertX (i : Fin (s + 1)) : insert (point i) Y ⊆ X := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzY
    · exact hpointX i
    · exact hYX hzY
  have hkSumEq :
      (∑ z ∈ X, k z • z) =
        ∑ i, coeff i •
          (∑ z ∈ insert (point i) Y, cN i z • z) := by
    calc
      (∑ z ∈ X, k z • z) =
          ∑ z ∈ X, ∑ i, (coeff i * cN i z) • z := by
            apply Finset.sum_congr rfl
            intro z hz
            change (∑ i, coeff i * cN i z) • z =
              ∑ i, (coeff i * cN i z) • z
            exact Finset.sum_smul (s := Finset.univ)
              (f := fun i ↦ coeff i * cN i z) (x := z)
      _ = ∑ i, ∑ z ∈ X, (coeff i * cN i z) • z := by
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ z ∈ insert (point i) Y,
          (coeff i * cN i z) • z := by
            apply Finset.sum_congr rfl
            intro i hi
            symm
            apply Finset.sum_subset (hinsertX i)
            intro z hzX hznot
            have hcz : cN i z = 0 := by simp only [cN, if_neg hznot]
            simp [hcz]
      _ = ∑ i, coeff i •
          (∑ z ∈ insert (point i) Y, cN i z • z) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp_rw [Finset.smul_sum, smul_smul]
  have hkSum : ∑ z ∈ X, k z • z = 0 := hkSumEq.trans hXpart
  have hkZero : ∀ z ∈ X, k z = 0 := hX k hkBound hkSum
  obtain ⟨i₀, hi₀⟩ := hcoeff0
  have hcNOther (i : Fin (s + 1)) (hi : i ≠ i₀) : cN i (point i₀) = 0 := by
    have hne : point i₀ ≠ point i := by
      intro heq
      apply hi
      exact eD.injective (Subtype.ext heq.symm)
    simp [cN, hne, hpointY i₀]
  have hkPoint : k (point i₀) = coeff i₀ * cN i₀ (point i₀) := by
    dsimp [k]
    rw [Fintype.sum_eq_single i₀]
    intro i hi
    rw [hcNOther i hi]
    simp
  have hkPointNe : k (point i₀) ≠ 0 := by
    rw [hkPoint]
    exact mul_ne_zero hi₀ (hcNPoint i₀)
  exact hkPointNe (hkZero (point i₀) (hpointX i₀))

end BoundedDeletion

end Relations

end
end FiniteCombinatorics
end Wallace
