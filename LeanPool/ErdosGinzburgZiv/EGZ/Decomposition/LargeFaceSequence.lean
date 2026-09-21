/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LargeFaceGeometry
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.WeightedIncidence

/-!
# A uniform bound for successive large faces

Nested polytopes with no repeated restricted face admit only boundedly many
faces which each carry a fixed positive fraction of a common finite weight
and lose a fixed fraction of that mass on every proper subface. The bound
depends only on the dimension and these two fractions.
-/

open scoped BigOperators

namespace EGZ

attribute [local instance] Classical.propDecidable

namespace LargeFaceSequence

variable {α : Type*} [Fintype α] {d : ℕ}

/-- Affine rank of a finite set of atoms in the coordinate space. -/
noncomputable def rank (q : α → RealCoord d) (S : Finset α) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (q '' (S : Set α))).direction

/-- Atoms lying in the affine span of a finite configuration. -/
def closure (q : α → RealCoord d) (S : Finset α) : Set α :=
  q ⁻¹' (affineSpan ℝ (q '' (S : Set α)) : Set (RealCoord d))

omit [Fintype α] in
theorem rank_le (q : α → RealCoord d) (S : Finset α) : rank q S ≤ d := by
  simpa [rank] using (affineSpan ℝ (q '' (S : Set α))).direction.finrank_le

omit [Fintype α] in
theorem rank_insert_lt [Finite α] (q : α → RealCoord d) (S : Finset α) (hS : S.Nonempty)
    (a : α) (ha : a ∉ closure q S) : rank q S < rank q (insert a S) := by
  classical
  let := Fintype.ofFinite α
  classical
  have hspan : affineSpan ℝ (q '' (S : Set α)) <
      affineSpan ℝ (q '' (↑(insert a S) : Set α)) := by
    refine lt_of_le_of_ne (affineSpan_mono ℝ (Set.image_mono (by simp))) ?_
    intro heq
    apply ha
    change q a ∈ affineSpan ℝ (q '' (S : Set α))
    rw [heq]
    exact subset_affineSpan ℝ _ ⟨a, Finset.mem_insert_self _ _, rfl⟩
  exact Submodule.finrank_lt_finrank_of_lt (AffineSubspace.direction_lt_of_nonempty
    hspan (((show (S : Set α).Nonempty from hS).image q).affineSpan ℝ))

end LargeFaceSequence

/-- A uniform large-face bound. The common total weight is positive; each
face has mass at least `η` times that total, and each proper subface loses
at least the fraction `δ` of its face's mass. -/
theorem card_largeFaceSequence_le {α : Type*} [Fintype α] {d N : ℕ}
    (q : α → RealCoord d) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hM : 0 < ∑ a, w a) (P : Fin N → RationalPolytope d) (Γ : ∀ i, (P i).Face)
    (hnested : ∀ i j, i < j → (P j).carrier ⊆ (P i).carrier)
    (hdistinct : ∀ i j, i < j → (Γ i).carrier ∩ (P j).carrier ≠ (Γ j).carrier)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η)
    (hlarge : ∀ i, η * (∑ a, w a) ≤ WeightedIncidence.mass w (q ⁻¹' (Γ i).carrier))
    (hproper : ∀ i (Δ : (P i).Face), Δ.carrier ⊂ (Γ i).carrier →
      WeightedIncidence.mass w (q ⁻¹' Δ.carrier) ≤
        (1 - δ) * WeightedIncidence.mass w (q ⁻¹' (Γ i).carrier)) :
    (N : ℝ) ≤ WeightedIncidence.bound (d + 1) (δ * η) d / η := by
  classical
  let F : Fin N → Set α := fun i ↦ q ⁻¹' (Γ i).carrier
  let E : Finset α → Finset (Fin N) := fun S ↦
    Finset.univ.filter fun i ↦ (Γ i).MinimallyContains (q '' (S : Set α))
  have hE : ∀ S, S.Nonempty → (E S).card ≤ d + 1 := by
    intro S hS
    exact RationalPolytope.Face.card_minimallyContains_le P Γ hnested hdistinct
      ((show (S : Set α).Nonempty from hS).image q)
  have hescape : ∀ S, S.Nonempty → ∀ i ∈ WeightedIncidence.containing F S, i ∉ E S →
      (δ * η) * (∑ a, w a) ≤
        WeightedIncidence.mass w (F i \ LargeFaceSequence.closure q S) := by
    intro S hS i hi hiE
    have hSΓ : q '' (S : Set α) ⊆ (Γ i).carrier := by
      rintro _ ⟨a, ha, rfl⟩
      exact (WeightedIncidence.mem_containing F S i).mp hi a ha
    have hn : ¬ (Γ i).MinimallyContains (q '' (S : Set α)) := by
      simpa [E] using hiE
    obtain ⟨Δ, hSΔ, hΔΓ⟩ := (Γ i).exists_proper_subface_of_not_minimallyContains
      ((show (S : Set α).Nonempty from hS).image q) hSΓ hn
    have hinter : F i ∩ LargeFaceSequence.closure q S ⊆ q ⁻¹' Δ.carrier := by
      intro a ha
      exact Δ.mem_of_mem_affineSpan_subset hSΔ ((Γ i).subset_polytope ha.1) ha.2
    have hsmall := (WeightedIncidence.mass_mono w hw hinter).trans (hproper i Δ hΔΓ)
    have hsplit := WeightedIncidence.mass_diff_add_inter w (F i)
      (LargeFaceSequence.closure q S)
    have hl := mul_le_mul_of_nonneg_left (hlarge i) hδ.le
    change δ * (η * ∑ a, w a) ≤ δ * WeightedIncidence.mass w (F i) at hl
    nlinarith
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    WeightedIncidence.card_family_le w hw hM F (LargeFaceSequence.rank q)
      (LargeFaceSequence.closure q) E (d + 1) d (δ * η) η (mul_pos hδ hη) hη
      (LargeFaceSequence.rank_le q) (LargeFaceSequence.rank_insert_lt q) hE hescape hlarge

/-- Proposition `large` for a finitely supported measure, with its explicit
bound. The necessary positive initial-mass hypothesis is stated explicitly.
Weights outside the first polytope are harmless and are restricted away in
the proof. The weak proper-subface inequality suffices. -/
theorem card_largeFaceSequence_le_paper {α : Type*} [Fintype α] {d N : ℕ}
    (q : α → RealCoord d) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (P : Fin (N + 1) → RationalPolytope d) (Γ : ∀ i, (P i).Face)
    (hnested : ∀ i j, i < j → (P j).carrier ⊆ (P i).carrier)
    (hdistinct : ∀ i j, i < j → (Γ i).carrier ∩ (P j).carrier ≠ (Γ j).carrier)
    (ε : ℝ) (hε : 0 < ε)
    (hM : 0 < WeightedIncidence.mass w (q ⁻¹' (P 0).carrier))
    (hfinal : ε * WeightedIncidence.mass w (q ⁻¹' (P 0).carrier) ≤
      WeightedIncidence.mass w (q ⁻¹' (P (Fin.last N)).carrier))
    (hlarge : ∀ i, ε * WeightedIncidence.mass w (q ⁻¹' (P i).carrier) ≤
      WeightedIncidence.mass w (q ⁻¹' (Γ i).carrier))
    (hproper : ∀ i (Δ : (P i).Face), Δ.carrier ⊂ (Γ i).carrier →
      WeightedIncidence.mass w (q ⁻¹' Δ.carrier) ≤
        (1 - ε) * WeightedIncidence.mass w (q ⁻¹' (Γ i).carrier)) :
    ((N + 1 : ℕ) : ℝ) ≤ ((ε ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2) := by
  classical
  let U : Set α := q ⁻¹' (P 0).carrier
  let u : α → ℝ := fun a ↦ if a ∈ U then w a else 0
  have hu : ∀ a, 0 ≤ u a := by
    intro a
    dsimp [u]
    split_ifs
    · exact hw a
    · exact le_rfl
  have htotal : (∑ a, u a) = WeightedIncidence.mass w U := rfl
  have hfirst : ∀ i, (P i).carrier ⊆ (P 0).carrier := by
    intro i
    rcases eq_or_lt_of_le (Fin.zero_le i) with hi | hi
    · simpa only [hi] using (Set.Subset.refl (P i).carrier)
    · exact hnested 0 i hi
  have hlast : ∀ i, (P (Fin.last N)).carrier ⊆ (P i).carrier := by
    intro i
    rcases eq_or_lt_of_le (Fin.le_last i) with hi | hi
    · simpa only [hi] using (Set.Subset.refl (P (Fin.last N)).carrier)
    · exact hnested i (Fin.last N) hi
  have hfaceMass : ∀ i (Δ : (P i).Face),
      WeightedIncidence.mass u (q ⁻¹' Δ.carrier) =
        WeightedIncidence.mass w (q ⁻¹' Δ.carrier) := by
    intro i Δ
    exact WeightedIncidence.mass_restrict_eq_of_subset w U (q ⁻¹' Δ.carrier)
      (fun _ ha ↦ hfirst i (Δ.subset_polytope ha))
  have hη : 0 < ε ^ 2 := pow_pos hε _
  have hlarge' : ∀ i, ε ^ 2 * (∑ a, u a) ≤
      WeightedIncidence.mass u (q ⁻¹' (Γ i).carrier) := by
    intro i
    rw [hfaceMass, htotal]
    have hPi := hfinal.trans (WeightedIncidence.mass_mono w hw
      (fun _ ha ↦ hlast i ha))
    change ε * WeightedIncidence.mass w (q ⁻¹' (P 0).carrier) ≤
      WeightedIncidence.mass w (q ⁻¹' (P i).carrier) at hPi
    have hmul := mul_le_mul_of_nonneg_left hPi hε.le
    have hi := hlarge i
    dsimp [U]
    nlinarith
  have hproper' : ∀ i (Δ : (P i).Face), Δ.carrier ⊂ (Γ i).carrier →
      WeightedIncidence.mass u (q ⁻¹' Δ.carrier) ≤
        (1 - ε) * WeightedIncidence.mass u (q ⁻¹' (Γ i).carrier) := by
    intro i Δ hΔ
    simpa only [hfaceMass] using hproper i Δ hΔ
  have hbound := card_largeFaceSequence_le q u hu (htotal ▸ hM) P Γ hnested hdistinct
    ε (ε ^ 2) hε hη hlarge' hproper'
  rw [show ε * ε ^ 2 = ε ^ 3 by ring] at hbound
  have hpow := WeightedIncidence.bound_le_pow
    (by positivity : (0 : ℝ) ≤ d + 1) (pow_pos hε 3) d
  let X : ℝ := (ε ^ 3)⁻¹ + (d : ℝ) + 2
  have hpow' : WeightedIncidence.bound (d + 1) (ε ^ 3) d ≤ X ^ (d + 1) := by
    have hXeq : (d : ℝ) + 1 + 1 + (ε ^ 3)⁻¹ = X := by dsimp [X]; ring
    rwa [hXeq] at hpow
  have hεone : ε ≤ 1 := by
    have hh : WeightedIncidence.mass w (q ⁻¹' (P (Fin.last N)).carrier) ≤
        WeightedIncidence.mass w (q ⁻¹' (P 0).carrier) :=
      WeightedIncidence.mass_mono w hw (fun _ ha ↦ hfirst (Fin.last N) ha)
    nlinarith
  have hinv : (ε ^ 2)⁻¹ ≤ (ε ^ 3)⁻¹ := by
    apply (inv_le_inv₀ (pow_pos hε 2) (pow_pos hε 3)).mpr
    nlinarith [sq_nonneg ε]
  have hinvX : (ε ^ 2)⁻¹ ≤ X := by
    dsimp [X]
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hX : 0 ≤ X := by dsimp [X]; positivity
  calc
    ((N + 1 : ℕ) : ℝ) ≤ WeightedIncidence.bound (d + 1) (ε ^ 3) d / ε ^ 2 := hbound
    _ ≤ X ^ (d + 1) / ε ^ 2 := div_le_div_of_nonneg_right hpow' hη.le
    _ ≤ X ^ (d + 1) * X := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinvX (pow_nonneg hX _)
    _ = X ^ (d + 2) := (pow_succ X (d + 1)).symm

end EGZ
