/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Coordinate
import Mathlib.Data.Fintype.OfMap

/-!
# Finite exposed-face API for rational polytopes

Every nonempty exposed face of a finitely generated polytope is the convex
hull of the generators which it contains.  Consequently the custom face
type used by this project is finite, even though an exposure is stored using
arbitrary real affine data.
-/

namespace EGZ.RationalPolytope

namespace Face

/-- The generators of `P` which lie on a face.  This finite set uniquely
determines the face. -/
noncomputable def generatorFinset {n : ℕ} {P : RationalPolytope n}
    (F : P.Face) : Finset (RealCoord n) := by
  classical
  exact P.generators.filter (fun q ↦ q ∈ F.carrier)

theorem generatorFinset_subset {n : ℕ} {P : RationalPolytope n}
    (F : P.Face) : F.generatorFinset ⊆ P.generators := by
  classical
  unfold generatorFinset
  exact Finset.filter_subset _ _

/-- An exposed face is the convex hull of precisely the chosen generators
which lie on it. -/
theorem carrier_eq_convexHull_generatorFinset {n : ℕ}
    {P : RationalPolytope n} (F : P.Face) :
    F.carrier = convexHull ℝ (↑F.generatorFinset : Set (RealCoord n)) := by
  classical
  obtain ⟨functional, level, hleP, hcarrier⟩ := F.is_exposed
  have hle : ∀ q ∈ P.generators, functional q ≤ level := by
    intro q hq
    apply hleP q
    rw [P.carrier_eq_convexHull]
    exact subset_convexHull ℝ _ (by exact hq)
  have hfilter :
      P.generators.filter (fun q ↦ functional q = level) =
        F.generatorFinset := by
    ext q
    simp only [Finset.mem_filter, generatorFinset]
    constructor
    · rintro ⟨hqgen, hqlevel⟩
      refine ⟨hqgen, ?_⟩
      rw [hcarrier]
      exact ⟨by
        rw [P.carrier_eq_convexHull]
        exact subset_convexHull ℝ _ (by exact hqgen), hqlevel⟩
    · rintro ⟨hqgen, hqF⟩
      refine ⟨hqgen, ?_⟩
      rw [hcarrier] at hqF
      exact hqF.2
  calc
    F.carrier =
        {q | q ∈ convexHull ℝ (↑P.generators : Set (RealCoord n)) ∧
          functional q = level} := by
      rw [hcarrier, P.carrier_eq_convexHull]
    _ = convexHull ℝ
          (↑(P.generators.filter (fun q ↦ functional q = level)) :
            Set (RealCoord n)) :=
      convexHull_supportingLevel_eq P.generators functional level hle
    _ = convexHull ℝ (↑F.generatorFinset : Set (RealCoord n)) := by
      rw [hfilter]

/-- Every nonempty exposed face contains at least one generator of the
ambient polytope. -/
theorem generatorFinset_nonempty {n : ℕ} {P : RationalPolytope n}
    (F : P.Face) : F.generatorFinset.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hface := F.nonempty
  rw [F.carrier_eq_convexHull_generatorFinset, h] at hface
  simp at hface

theorem generatorFinset_injective {n : ℕ} {P : RationalPolytope n} :
    Function.Injective (@generatorFinset n P) := by
  intro F G hFG
  apply Face.ext
  rw [F.carrier_eq_convexHull_generatorFinset,
    G.carrier_eq_convexHull_generatorFinset, hFG]

/-- A code for a face as a member of the powerset of the given generating
finset. -/
noncomputable def generatorCode {n : ℕ} {P : RationalPolytope n}
    (F : P.Face) : {s : Finset (RealCoord n) // s ∈ P.generators.powerset} :=
  ⟨F.generatorFinset, Finset.mem_powerset.mpr F.generatorFinset_subset⟩

theorem generatorCode_injective {n : ℕ} {P : RationalPolytope n} :
    Function.Injective (@generatorCode n P) := by
  intro F G hFG
  apply generatorFinset_injective
  exact congrArg Subtype.val hFG

noncomputable instance faceFintype {n : ℕ} (P : RationalPolytope n) :
    Fintype P.Face := by
  classical
  exact Fintype.ofInjective (@generatorCode n P) generatorCode_injective

/-- A face carrier is convex. -/
theorem convex {n : ℕ} {P : RationalPolytope n} (F : P.Face) :
    Convex ℝ F.carrier := by
  rw [F.carrier_eq_convexHull_generatorFinset]
  exact convex_convexHull ℝ _

noncomputable instance facePartialOrder {n : ℕ} (P : RationalPolytope n) :
    PartialOrder P.Face :=
  PartialOrder.lift (fun F ↦ F.carrier) (fun _ _ h ↦ Face.ext h)

@[simp]
theorem le_iff_carrier_subset {n : ℕ} {P : RationalPolytope n}
    {F G : P.Face} : F ≤ G ↔ F.carrier ⊆ G.carrier := Iff.rfl

/-- The whole polytope is its top exposed face. -/
def top {n : ℕ} (P : RationalPolytope n) : P.Face where
  carrier := P.carrier
  is_exposed := by
    refine ⟨0, 0, ?_, ?_⟩
    · simp
    · ext q
      simp
  nonempty := P.nonempty

@[simp]
theorem top_carrier {n : ℕ} (P : RationalPolytope n) :
    (top P).carrier = P.carrier := rfl

noncomputable instance faceOrderTop {n : ℕ} (P : RationalPolytope n) :
    OrderTop P.Face where
  top := top P
  le_top F := F.subset_polytope

/-- The intersection of two faces is a face whenever it is nonempty. -/
def interOfNonempty {n : ℕ} {P : RationalPolytope n}
    (F G : P.Face) (hnonempty : (F.carrier ∩ G.carrier).Nonempty) : P.Face where
  carrier := F.carrier ∩ G.carrier
  is_exposed := by
    obtain ⟨f, a, hfa, hF⟩ := F.is_exposed
    obtain ⟨g, b, hgb, hG⟩ := G.is_exposed
    refine ⟨f + g, a + b, ?_, ?_⟩
    · intro q hq
      exact add_le_add (hfa q hq) (hgb q hq)
    · ext q
      rw [Set.mem_inter_iff, hF, hG]
      change
        ((q ∈ P.carrier ∧ f q = a) ∧ q ∈ P.carrier ∧ g q = b) ↔
          q ∈ P.carrier ∧ f q + g q = a + b
      constructor
      · rintro ⟨⟨hqP, hfq⟩, _, hgq⟩
        exact ⟨hqP, by rw [hfq, hgq]⟩
      · rintro ⟨hqP, hsum⟩
        have hf_le := hfa q hqP
        have hg_le := hgb q hqP
        constructor <;> constructor
        · exact hqP
        · linarith
        · exact hqP
        · linarith
  nonempty := hnonempty

@[simp]
theorem interOfNonempty_carrier {n : ℕ} {P : RationalPolytope n}
    (F G : P.Face) (hnonempty : (F.carrier ∩ G.carrier).Nonempty) :
    (interOfNonempty F G hnonempty).carrier = F.carrier ∩ G.carrier := rfl

private theorem exists_commonUpper_card {n : ℕ} {P : RationalPolytope n}
    (F G : P.Face) :
    ∃ k : ℕ, ∃ H : P.Face,
      F ≤ H ∧ G ≤ H ∧ H.generatorFinset.card = k := by
  refine ⟨(⊤ : P.Face).generatorFinset.card, ⊤, le_top, le_top, rfl⟩

/-- The least number of generators among common upper faces. -/
private noncomputable def commonUpperMinCard {n : ℕ}
    {P : RationalPolytope n} (F G : P.Face) : ℕ := by
  classical
  exact Nat.find (exists_commonUpper_card F G)

private theorem commonUpperMinCard_spec {n : ℕ}
    {P : RationalPolytope n} (F G : P.Face) :
    ∃ H : P.Face, F ≤ H ∧ G ≤ H ∧
      H.generatorFinset.card = commonUpperMinCard F G := by
  classical
  exact Nat.find_spec (exists_commonUpper_card F G)

private theorem commonUpperMinCard_min {n : ℕ}
    {P : RationalPolytope n} (F G H : P.Face)
    (hFH : F ≤ H) (hGH : G ≤ H) :
    commonUpperMinCard F G ≤ H.generatorFinset.card := by
  classical
  exact Nat.find_min' (exists_commonUpper_card F G)
    ⟨H, hFH, hGH, rfl⟩

/-- The common upper face with the fewest generating points.  Intersecting
with any other common upper face proves that it is the least one. -/
noncomputable def supFace {n : ℕ} {P : RationalPolytope n}
    (F G : P.Face) : P.Face :=
  Classical.choose (commonUpperMinCard_spec F G)

private theorem supFace_spec {n : ℕ} {P : RationalPolytope n}
    (F G : P.Face) :
    F ≤ supFace F G ∧ G ≤ supFace F G ∧
      (supFace F G).generatorFinset.card =
        commonUpperMinCard F G :=
  Classical.choose_spec (commonUpperMinCard_spec F G)

private theorem supFace_card_min {n : ℕ} {P : RationalPolytope n}
    (F G H : P.Face) (hFH : F ≤ H) (hGH : G ≤ H) :
    (supFace F G).generatorFinset.card ≤ H.generatorFinset.card := by
  rw [(supFace_spec F G).2.2]
  exact commonUpperMinCard_min F G H hFH hGH

private theorem supFace_le_commonUpper {n : ℕ} {P : RationalPolytope n}
    (F G H : P.Face) (hFH : F ≤ H) (hGH : G ≤ H) :
    supFace F G ≤ H := by
  classical
  let J := supFace F G
  have hFJ : F ≤ J := (supFace_spec F G).1
  have hGJ : G ≤ J := (supFace_spec F G).2.1
  by_contra hJH
  rw [le_iff_carrier_subset] at hJH
  obtain ⟨q, hqJ, hqH⟩ := Set.not_subset.mp hJH
  have hnonempty : (J.carrier ∩ H.carrier).Nonempty := by
    obtain ⟨x, hxF⟩ := F.nonempty
    exact ⟨x, hFJ hxF, hFH hxF⟩
  let I : P.Face := interOfNonempty J H hnonempty
  have hFI : F ≤ I := by
    intro x hx
    exact ⟨hFJ hx, hFH hx⟩
  have hGI : G ≤ I := by
    intro x hx
    exact ⟨hGJ hx, hGH hx⟩
  have hgen_subset : I.generatorFinset ⊆ J.generatorFinset := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hx'.2.1⟩
  have hgen_ne : I.generatorFinset ≠ J.generatorFinset := by
    intro heq
    apply hqH
    rw [J.carrier_eq_convexHull_generatorFinset] at hqJ
    apply convexHull_min (s := (↑J.generatorFinset : Set (RealCoord n)))
        (t := H.carrier) _ H.convex hqJ
    intro x hxgen
    have hxI : x ∈ I.generatorFinset := by
      rw [heq]
      exact hxgen
    exact (Finset.mem_filter.mp hxI).2.2
  have hcard_lt : I.generatorFinset.card < J.generatorFinset.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hgen_subset, hgen_ne⟩)
  exact (Nat.not_lt_of_ge (supFace_card_min F G I hFI hGI)) hcard_lt

theorem supFace_isLUB {n : ℕ} {P : RationalPolytope n}
    (F G : P.Face) : IsLUB {F, G} (supFace F G) := by
  constructor
  · intro H hH
    rcases Set.mem_insert_iff.mp hH with hHF | hHG
    · subst H
      exact (supFace_spec F G).1
    · have hHG' : H = G := Set.mem_singleton_iff.mp hHG
      subst H
      exact (supFace_spec F G).2.1
  · intro H hH
    apply supFace_le_commonUpper F G H
    · exact hH (by simp)
    · exact hH (by simp)

noncomputable instance faceSemilatticeSup {n : ℕ} (P : RationalPolytope n) :
    SemilatticeSup P.Face :=
  SemilatticeSup.ofIsLUB supFace (fun F G ↦ supFace_isLUB F G)

end Face

end EGZ.RationalPolytope
