/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FacePreservation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Geometric rank bounds for repeated large faces

For a fixed nonempty set of points, faces which are least among the faces
containing that set have strictly decreasing dimension in a nested polytope
sequence satisfying the no-repetition condition.
-/

@[expose] public section

namespace EGZ.RationalPolytope.Face

attribute [local instance] Classical.propDecidable

/-- An exposed face contains every polytope point in the affine span of its carrier. -/
theorem mem_of_mem_affineSpan {d : ℕ} {P : RationalPolytope d} (Γ : P.Face)
    {q : RealCoord d} (hqP : q ∈ P.carrier)
    (hq : q ∈ affineSpan ℝ Γ.carrier) : q ∈ Γ.carrier := by
  obtain ⟨ξ, a, hξ, hΓ⟩ := Γ.is_exposed
  have heq : ξ q = a := AffineMap.eqOn_affineSpan
    (f := ξ) (g := AffineMap.const ℝ (RealCoord d) a)
    (fun z hz ↦ (hΓ ▸ hz).2) hq
  rw [hΓ]
  exact ⟨hqP, heq⟩

theorem mem_of_mem_affineSpan_subset {d : ℕ} {P : RationalPolytope d} (Γ : P.Face)
    {S : Set (RealCoord d)} (hS : S ⊆ Γ.carrier) {q : RealCoord d}
    (hqP : q ∈ P.carrier) (hq : q ∈ affineSpan ℝ S) : q ∈ Γ.carrier :=
  Γ.mem_of_mem_affineSpan hqP (affineSpan_mono ℝ hS hq)

/-- Dimension of the affine hull of a face. -/
noncomputable def dimension {d : ℕ} {P : RationalPolytope d} (Γ : P.Face) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ Γ.carrier).direction

theorem dimension_le {d : ℕ} {P : RationalPolytope d} (Γ : P.Face) : Γ.dimension ≤ d := by
  simpa [dimension] using (affineSpan ℝ Γ.carrier).direction.finrank_le

/-- If an upper carrier contains a face and a point of the same polytope
outside it, its affine dimension is strictly greater. -/
theorem dimension_lt_of_subset_of_witness {d : ℕ} {P Q : RationalPolytope d}
    (Γ : P.Face) (Δ : Q.Face) (hsub : Γ.carrier ⊆ Δ.carrier)
    (hw : ∃ q ∈ Δ.carrier, q ∈ P.carrier ∧ q ∉ Γ.carrier) : Γ.dimension < Δ.dimension := by
  obtain ⟨q, hqΔ, hqP, hqΓ⟩ := hw
  have hspan : affineSpan ℝ Γ.carrier < affineSpan ℝ Δ.carrier := by
    refine lt_of_le_of_ne (affineSpan_mono ℝ hsub) ?_
    intro heq
    apply hqΓ
    apply Γ.mem_of_mem_affineSpan hqP
    rw [heq]
    exact subset_affineSpan ℝ _ hqΔ
  exact Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hspan (Γ.nonempty.affineSpan ℝ))

/-- A face is the least face containing a prescribed set. -/
def MinimallyContains {d : ℕ} {P : RationalPolytope d} (Γ : P.Face)
    (S : Set (RealCoord d)) : Prop :=
  S ⊆ Γ.carrier ∧ ∀ Δ : P.Face, S ⊆ Δ.carrier → Γ.carrier ⊆ Δ.carrier

/-- Failure of leastness supplies a proper subface still containing the set. -/
theorem exists_proper_subface_of_not_minimallyContains {d : ℕ} {P : RationalPolytope d}
    (Γ : P.Face) {S : Set (RealCoord d)} (hSne : S.Nonempty) (hS : S ⊆ Γ.carrier)
    (hnot : ¬ Γ.MinimallyContains S) :
    ∃ Δ : P.Face, S ⊆ Δ.carrier ∧ Δ.carrier ⊂ Γ.carrier := by
  classical
  have hn : ¬ ∀ Δ : P.Face, S ⊆ Δ.carrier → Γ.carrier ⊆ Δ.carrier :=
    fun h ↦ hnot ⟨hS, h⟩
  obtain ⟨Δ, hΔ⟩ := not_forall.mp hn
  obtain ⟨hΔS, hΓΔ⟩ := Classical.not_imp.mp hΔ
  obtain ⟨q, hq⟩ := hSne
  let E := Γ.interOfNonempty Δ ⟨q, hS hq, hΔS hq⟩
  refine ⟨E, fun _ hz ↦ ⟨hS hz, hΔS hz⟩, ?_⟩
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left, ?_⟩
  intro heq
  apply hΓΔ
  intro z hz
  have hzE : z ∈ E.carrier := heq.symm ▸ hz
  exact hzE.2

/-- Least containing faces have strictly decreasing dimensions across two
nested polytopes when the old face does not restrict to the new one. -/
theorem dimension_lt_of_nested_minimallyContains {d : ℕ} {P Q : RationalPolytope d}
    (Γ : P.Face) (Δ : Q.Face) (hQP : Q.carrier ⊆ P.carrier)
    {S : Set (RealCoord d)} (hSne : S.Nonempty) (hSΓ : S ⊆ Γ.carrier)
    (hΔ : Δ.MinimallyContains S) (hne : Γ.carrier ∩ Q.carrier ≠ Δ.carrier) :
    Δ.dimension < Γ.dimension := by
  obtain ⟨q, hqS⟩ := hSne
  let E : Q.Face := Γ.preimage (AffineMap.id ℝ (RealCoord d)) hQP
    ⟨q, Δ.subset_polytope (hΔ.1 hqS), hSΓ hqS⟩
  have hΔE : Δ.carrier ⊆ E.carrier := hΔ.2 E
    (fun _ hz ↦ ⟨Δ.subset_polytope (hΔ.1 hz), hSΓ hz⟩)
  apply Δ.dimension_lt_of_subset_of_witness Γ (fun _ hz ↦ (hΔE hz).2)
  have hn : ¬ Γ.carrier ∩ Q.carrier ⊆ Δ.carrier := by
    intro h
    apply hne
    exact Set.Subset.antisymm h (fun _ hz ↦ ⟨(hΔE hz).2, (hΔE hz).1⟩)
  obtain ⟨z, ⟨hzΓ, hzQ⟩, hzΔ⟩ := Set.not_subset.mp hn
  exact ⟨z, hzΓ, hzQ, hzΔ⟩

/-- At most `d+1` members of a nested no-repetition sequence can be least
containing faces for a fixed nonempty set. -/
theorem card_minimallyContains_le {d N : ℕ} (P : Fin N → RationalPolytope d)
    (Γ : ∀ i, (P i).Face)
    (hnested : ∀ i j, i < j → (P j).carrier ⊆ (P i).carrier)
    (hdistinct : ∀ i j, i < j → (Γ i).carrier ∩ (P j).carrier ≠ (Γ j).carrier)
    {S : Set (RealCoord d)} (hS : S.Nonempty) :
    (Finset.univ.filter fun i ↦ (Γ i).MinimallyContains S).card ≤ d + 1 := by
  classical
  let E := {i : Fin N // (Γ i).MinimallyContains S}
  let r : E → Fin (d + 1) := fun i ↦ ⟨(Γ i).dimension, Nat.lt_succ_of_le (Γ i).dimension_le⟩
  have hr : Function.Injective r := by
    intro i j hij
    have heq : (Γ i).dimension = (Γ j).dimension := congrArg Fin.val hij
    apply Subtype.ext
    rcases lt_trichotomy i.1 j.1 with hlt | he | hgt
    · have h := (Γ i).dimension_lt_of_nested_minimallyContains (Γ j)
        (hnested i j hlt) hS i.2.1 j.2 (hdistinct i j hlt)
      omega
    · exact he
    · have h := (Γ j).dimension_lt_of_nested_minimallyContains (Γ i)
        (hnested j i hgt) hS j.2.1 i.2 (hdistinct j i hgt)
      omega
  simpa [E, Fintype.card_subtype] using Fintype.card_le_of_injective r hr

end EGZ.RationalPolytope.Face
