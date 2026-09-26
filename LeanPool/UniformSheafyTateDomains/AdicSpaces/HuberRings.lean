/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Polynomial.Subring
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Bounded

/-!
# Huber Rings (f-adic Rings)

We define **Huber rings** (also called **f-adic rings**) and **Tate rings**,
following §6 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `PairOfDefinition A` : A pair of definition `(A₀, I)` for a topological ring `A`,
  consisting of an open subring `A₀` whose subspace topology is `I`-adic for a
  finitely generated ideal `I ⊆ A₀` (Definition 6.1).
* `IsHuberRing A` : A topological ring is a Huber ring if it admits a pair
  of definition.
* `IsTateRing A` : A Huber ring with a topologically nilpotent unit (Definition 6.10).

## Main results

* `PairOfDefinition.pow_isOpen` : Each power `Iⁿ` is open in `A₀`.
* `PairOfDefinition.pow_image_isOpen` : The image of `Iⁿ` in `A` is open.
* `PairOfDefinition.isTopologicallyNilpotent_of_mem` : Elements of `I` are
  topologically nilpotent in `A` (Corollary 6.4(3)).
* `PairOfDefinition.hasBasis_nhds_zero` : The images of `Iⁿ` in `A` form a
  neighborhood basis of `0`.
* `PairOfDefinition.idealOfDefinition_pow_isOpen` : Each power `Jⁿ` of the ideal
  of definition (in `A`) is open.
* `PairOfDefinition.ideal_isOpen_of_nilpotent_le_radical` : Backward direction
  of Lemma 6.6: if all topologically nilpotent elements are in `√𝔞`, then `𝔞`
  is open.
* `PairOfDefinition.isBounded_A₀` : The ring of definition `A₀` is bounded
  (Corollary 6.4(2)).
* `PairOfDefinition.mem_powerBoundedSubring` : Elements of `A₀` are power-bounded:
  `A₀ ⊆ A°`.
* `PairOfDefinition.exists_fg_le_topologicalNilradical` : Connection to the
  `hJ` hypothesis of `OpenIdeals.lean` (Remark 6.7).
* `IsTateRing.isOpen_topologicalNilradical` : In a Tate ring, `A°°` is open
  (Proposition 6.13(1)).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6
-/

@[expose] public section

/-- A **pair of definition** `(A₀, I)` for a topological ring `A` consists of an
open subring `A₀ ⊆ A` and a finitely generated ideal `I ⊆ A₀` such that the subspace
topology on `A₀` equals the `I`-adic topology (Definition 6.1 of Wedhorn). -/
structure PairOfDefinition (A : Type*) [CommRing A] [TopologicalSpace A] where
  /-- The ring of definition `A₀`, an open subring of `A`. -/
  A₀ : Subring A
  /-- The ideal of definition `I`, an ideal of `A₀`. -/
  I : Ideal A₀
  /-- `A₀` is open in `A`. -/
  isOpen : IsOpen (A₀ : Set A)
  /-- `I` is finitely generated. -/
  fg : I.FG
  /-- The subspace topology on `A₀` is the `I`-adic topology. -/
  isAdic : IsAdic I

/-- A topological ring `A` is a **Huber ring** (or **f-adic ring**) if it admits a
pair of definition (Definition 6.1 of Wedhorn). -/
class IsHuberRing (A : Type*) [CommRing A] [TopologicalSpace A] : Prop
    extends IsTopologicalRing A where
  /-- There exists a pair of definition. -/
  exists_pairOfDefinition : Nonempty (PairOfDefinition A)

/-- A Huber ring is a **Tate ring** if it contains a topologically nilpotent unit
(Definition 6.10 of Wedhorn). -/
class IsTateRing (A : Type*) [CommRing A] [TopologicalSpace A] : Prop
    extends IsHuberRing A where
  /-- There exists a topologically nilpotent unit. -/
  exists_topologicallyNilpotent_unit : ∃ u : Aˣ, IsTopologicallyNilpotent (u : A)

namespace PairOfDefinition

open Filter Topology Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Each power `Iⁿ` is open in `A₀` (in the subspace topology). -/
theorem pow_isOpen (P : PairOfDefinition A) (n : ℕ) :
    IsOpen ((P.I ^ n : Ideal P.A₀) : Set P.A₀) :=
  (isAdic_iff.mp P.isAdic).1 n

/-- The image of `Iⁿ` in `A` is open. -/
theorem pow_image_isOpen (P : PairOfDefinition A) (n : ℕ) :
    IsOpen (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) :=
  P.isOpen.isOpenMap_subtype_val _ (P.pow_isOpen n)

omit [IsTopologicalRing A] in
/-- Elements of the ideal of definition `I` are topologically nilpotent in `A`
(see Corollary 6.4(3) of Wedhorn). -/
theorem isTopologicallyNilpotent_of_mem (P : PairOfDefinition A) {a : P.A₀} (ha : a ∈ P.I) :
    IsTopologicallyNilpotent (a : A) := by
  have h₀ : IsTopologicallyNilpotent a :=
    P.isAdic.hasBasis_nhds_zero.tendsto_right_iff.mpr fun n _ ↦
      Filter.eventually_atTop.mpr ⟨n, fun m hm ↦
        Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ha m)⟩
  exact h₀.map (φ := P.A₀.subtype) continuous_subtype_val

/-- The images of `Iⁿ` in `A` form a neighborhood basis of `0`. -/
theorem hasBasis_nhds_zero (P : PairOfDefinition A) :
    (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) :=
  Filter.HasBasis.mk fun U ↦ by
    constructor
    · intro hU
      have hU' : Subtype.val ⁻¹' U ∈ 𝓝 (0 : ↥P.A₀) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU)
      obtain ⟨n, -, hn⟩ := P.isAdic.hasBasis_nhds_zero.mem_iff.mp hU'
      exact ⟨n, trivial, (Set.image_mono hn).trans (Set.image_preimage_subset _ _)⟩
    · rintro ⟨n, -, hn⟩
      exact mem_nhds_iff.mpr
        ⟨_, hn, P.pow_image_isOpen n, Set.mem_image_of_mem _ (P.I ^ n).zero_mem⟩

/-- In a Huber ring, `nhds 0` is countably generated: the ℕ-indexed basis
`{I^n}` from the pair of definition gives a countable basis. -/
theorem isCountablyGenerated_nhds_zero (P : PairOfDefinition A) :
    (𝓝 (0 : A)).IsCountablyGenerated :=
  P.hasBasis_nhds_zero.isCountablyGenerated

/-! ### Lemma 6.6 of Wedhorn (backward direction) -/

/-- The ideal of `A` generated by the ideal of definition `I ⊆ A₀`. -/
def idealOfDefinition (P : PairOfDefinition A) : Ideal A :=
  Ideal.map P.A₀.subtype P.I

omit [IsTopologicalRing A] in
/-- The ideal of definition is finitely generated. -/
theorem idealOfDefinition_fg (P : PairOfDefinition A) : P.idealOfDefinition.FG :=
  P.fg.map _

/-- Each power `Jⁿ` of the ideal of definition (in `A`) is open. -/
theorem idealOfDefinition_pow_isOpen (P : PairOfDefinition A) (n : ℕ) :
    IsOpen ((P.idealOfDefinition ^ n : Ideal A) : Set A) := by
  have h_sub : Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) ⊆
      ((P.idealOfDefinition ^ n : Ideal A) : Set A) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [idealOfDefinition, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hy
  change IsOpen ((P.idealOfDefinition ^ n).toAddSubgroup : Set A)
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((P.pow_image_isOpen n).mem_nhds (Set.mem_image_of_mem _ (P.I ^ n).zero_mem))
    ((Submodule.coe_toAddSubgroup (P.idealOfDefinition ^ n)).symm ▸ h_sub))

/-- Backward direction of Lemma 6.6 of Wedhorn: if every topologically nilpotent
element lies in `√𝔞`, then `𝔞` is open. -/
theorem ideal_isOpen_of_nilpotent_le_radical (P : PairOfDefinition A) {𝔞 : Ideal A}
    (h : ∀ a : A, IsTopologicallyNilpotent a → a ∈ 𝔞.radical) : IsOpen (𝔞 : Set A) := by
  have hJ_le : P.idealOfDefinition ≤ 𝔞.radical := by
    rw [idealOfDefinition, Ideal.map_le_iff_le_comap]
    exact fun _ hy ↦ h _ (P.isTopologicallyNilpotent_of_mem hy)
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ_le P.idealOfDefinition_fg
  have h_sub : Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀) ⊆ (𝔞 : Set A) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hm (by rw [idealOfDefinition, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hy)
  change IsOpen (𝔞.toAddSubgroup : Set A)
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((P.pow_image_isOpen m).mem_nhds (Set.mem_image_of_mem _ (P.I ^ m).zero_mem))
    ((Submodule.coe_toAddSubgroup 𝔞).symm ▸ h_sub))

/-! ### Corollary 6.4 of Wedhorn -/

/-- The ring of definition `A₀` is bounded in `A` (Corollary 6.4(2) of Wedhorn). -/
theorem isBounded_subring (P : PairOfDefinition A) :
    ∀ U ∈ 𝓝 (0 : A), ∃ V ∈ 𝓝 (0 : A), (P.A₀ : Set A) * V ⊆ U := by
  intro U hU
  obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hU
  refine ⟨_, P.hasBasis_nhds_zero.mem_of_mem trivial (i := n), ?_⟩
  rintro _ ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
  exact hn ⟨⟨a, ha⟩ * y, Ideal.mul_mem_left _ _ hy, MulMemClass.coe_mul ..⟩

/-- The ring of definition `A₀` is bounded (Corollary 6.4(2) of Wedhorn). -/
theorem isBounded_A₀ (P : PairOfDefinition A) :
    TopologicalRing.IsBounded (P.A₀ : Set A) :=
  P.isBounded_subring

/-- Elements of the ring of definition `A₀` are power-bounded: `A₀ ⊆ A°`
(Corollary 6.4(2) of Wedhorn). -/
theorem mem_powerBoundedSubring (P : PairOfDefinition A) {a : A} (ha : a ∈ P.A₀) :
    TopologicalRing.IsPowerBounded a :=
  P.isBounded_A₀.subset (Set.range_subset_iff.mpr fun n ↦ P.A₀.pow_mem ha n)

/-- A pair of definition makes `A` a non-archimedean additive group: the images of the powers
`Iⁿ` of the ideal of definition form an open additive-subgroup basis at `0`
(Corollary 6.4(1) of Wedhorn). -/
theorem nonarchimedeanAddGroup (P : PairOfDefinition A) : NonarchimedeanAddGroup A where
  is_nonarchimedean := by
    intro U hU
    obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hU
    refine ⟨⟨(P.I ^ n).toAddSubgroup.map P.A₀.subtype.toAddMonoidHom, ?_⟩, ?_⟩
    · change IsOpen (Subtype.val '' ((P.I ^ n).toAddSubgroup : Set P.A₀))
      rw [Submodule.coe_toAddSubgroup]; exact P.pow_image_isOpen n
    · change Subtype.val '' ((P.I ^ n).toAddSubgroup : Set P.A₀) ⊆ U
      rw [Submodule.coe_toAddSubgroup]; exact hn

/-! ### Connection to the topological nilradical (Remark 6.7 of Wedhorn) -/

section LinearTopology

variable [IsLinearTopology A A]

omit [IsTopologicalRing A] in
/-- The ideal of definition is contained in the topological nilradical
(Remark 6.7 of Wedhorn). -/
theorem idealOfDefinition_le_topologicalNilradical (P : PairOfDefinition A) :
    P.idealOfDefinition ≤ topologicalNilradical A := by
  rw [idealOfDefinition, Ideal.map_le_iff_le_comap]
  exact fun _ hy ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
    (P.isTopologicallyNilpotent_of_mem hy)

/-- The pair of definition produces the `hJ` hypothesis needed by `OpenIdeals.lean`. -/
theorem exists_fg_le_topologicalNilradical (P : PairOfDefinition A) :
    ∃ J : Ideal A, J.FG ∧ J ≤ topologicalNilradical A ∧
      ∀ n : ℕ, IsOpen ((J ^ n : Ideal A) : Set A) :=
  ⟨P.idealOfDefinition, P.idealOfDefinition_fg,
    P.idealOfDefinition_le_topologicalNilradical, P.idealOfDefinition_pow_isOpen⟩

/-- Every topologically nilpotent element lies in the radical of the ideal
of definition (Remark 6.7 of Wedhorn). -/
theorem topologicalNilradical_le_idealOfDefinition_radical (P : PairOfDefinition A) :
    topologicalNilradical A ≤ P.idealOfDefinition.radical := by
  intro a ha
  obtain ⟨n, y, hy, hval⟩ :=
    ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp ha).eventually
      ((P.pow_image_isOpen 1).mem_nhds
        (Set.mem_image_of_mem _ (P.I ^ 1).zero_mem))).exists
  exact Ideal.mem_radical_iff.mpr
    ⟨n, by rw [← hval, idealOfDefinition]; exact Ideal.mem_map_of_mem _ (pow_one P.I ▸ hy)⟩

end LinearTopology

/-- Topologically nilpotent elements of `A` lie in the radical of the ideal of definition
(Remark 6.7 of Wedhorn). This version avoids `topologicalNilradical` (which requires
`IsLinearTopology`) by working directly with `IsTopologicallyNilpotent`. -/
theorem isTopologicallyNilpotent_mem_idealOfDefinition_radical (P : PairOfDefinition A) {a : A}
    (ha : IsTopologicallyNilpotent a) : a ∈ P.idealOfDefinition.radical := by
  obtain ⟨n, y, hy, hval⟩ :=
    (ha.eventually
      ((P.pow_image_isOpen 1).mem_nhds
        (Set.mem_image_of_mem _ (P.I ^ 1).zero_mem))).exists
  exact Ideal.mem_radical_iff.mpr
    ⟨n, by rw [← hval, idealOfDefinition]; exact Ideal.mem_map_of_mem _ (pow_one P.I ▸ hy)⟩

/-- The power-bounded subring `A°` is open in any Huber ring (Proposition 6.4(4) of Wedhorn).
The proof uses only the pair of definition `P` (a `PairOfDefinition` always exists for a Huber
ring), so it needs no `[IsLinearTopology A A]` — which is in any case unsatisfiable for Tate
rings. -/
theorem isOpen_powerBoundedSubring (P : PairOfDefinition A) :
    IsOpen (TopologicalRing.powerBoundedSubring A) := by
  -- `A°` is realised as an `AddSubgroup` via `powerBoundedSubring.toSubring`, which is a
  -- subring precisely because `A` is non-archimedean — a structure supplied directly by `P`.
  let : NonarchimedeanAddGroup A := P.nonarchimedeanAddGroup
  have h_le : P.A₀.toAddSubgroup ≤
      (TopologicalRing.powerBoundedSubring.toSubring A).toAddSubgroup :=
    fun _ ha ↦ P.mem_powerBoundedSubring ha
  have := AddSubgroup.isOpen_mono h_le (show IsOpen (P.A₀.toAddSubgroup : Set A)
    from P.isOpen)
  rwa [show ((TopologicalRing.powerBoundedSubring.toSubring A).toAddSubgroup : Set A) =
    TopologicalRing.powerBoundedSubring A from rfl] at this

end PairOfDefinition

/-! ### Huber rings are nonarchimedean (Corollary 6.4(1) of Wedhorn) -/

/-- A Huber ring has a nonarchimedean additive group topology: every neighborhood of `0`
contains an open additive subgroup (Corollary 6.4(1) of Wedhorn). -/
instance IsHuberRing.nonarchimedeanAddGroup {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsHuberRing A] : NonarchimedeanAddGroup A :=
  (‹IsHuberRing A›.exists_pairOfDefinition.some).nonarchimedeanAddGroup

/-- A Huber ring is first countable: the pair of definition gives a countable
neighborhood basis `{I^n}` at 0, and translations extend this to every point.
This derives `[FirstCountableTopology A]` automatically, removing the need
to state it as a separate hypothesis. -/
instance IsHuberRing.firstCountableTopology {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsHuberRing A] : FirstCountableTopology A := by
  obtain ⟨P⟩ := ‹IsHuberRing A›.exists_pairOfDefinition
  let : IsTopologicalRing A := IsHuberRing.toIsTopologicalRing
  let : IsTopologicalAddGroup A := IsTopologicalRing.isTopologicalAddGroup
  let h0 : (nhds (0 : A)).IsCountablyGenerated :=
    P.hasBasis_nhds_zero.isCountablyGenerated
  refine ⟨fun a => ?_⟩
  rw [← map_add_left_nhds_zero a]
  exact Filter.map.isCountablyGenerated _ _

/-! ### Tate rings: A°° is open (Proposition 6.13(1) of Wedhorn) -/

section TateRing

open Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTateRing A] [IsLinearTopology A A]

/-- In a Tate ring with linear topology, the topological nilradical `A°°` is open
(Proposition 6.13(1) of Wedhorn). -/
theorem IsTateRing.isOpen_topologicalNilradical :
    IsOpen ((topologicalNilradical A : Ideal A) : Set A) := by
  obtain ⟨P⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
  obtain ⟨u, hu⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have hsub : (u : A) • (P.A₀ : Set A) ⊆
      ((topologicalNilradical A : Ideal A) : Set A) := by
    rintro _ ⟨a, ha, rfl⟩
    change (u : A) * a ∈ topologicalNilradical A
    rw [mul_comm]
    exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      ((P.mem_powerBoundedSubring ha).isTopologicallyNilpotent_mul hu)
  change IsOpen ((topologicalNilradical A).toAddSubgroup : Set A)
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((u.isUnit.isOpenMap_smul _ P.isOpen).mem_nhds ⟨0, P.A₀.zero_mem, smul_zero _⟩)
    ((Submodule.coe_toAddSubgroup (topologicalNilradical A)).symm ▸ hsub))

/-- The `Set` version of `isOpen_topologicalNilradical`. -/
theorem IsTateRing.isOpen_topologicallyNilpotentElements :
    IsOpen (TopologicalRing.topologicallyNilpotentElements A) := by
  have heq : TopologicalRing.topologicallyNilpotentElements A
      = ((topologicalNilradical A : Ideal A) : Set A) := by
    ext a
    simp only [TopologicalRing.topologicallyNilpotentElements, Set.mem_ofPred_eq, SetLike.mem_coe,
      IsTopologicallyNilpotent.mem_topologicalNilradical_iff]
  rw [heq]
  exact IsTateRing.isOpen_topologicalNilradical (A := A)

omit [IsLinearTopology A A] in
/-- **`A°°` is open (Wedhorn Prop 6.13(1)) — no `[IsLinearTopology]`.** Faithful version: `A°°`
is the open additive subgroup `topNilpAddSubgroup`, open because `u·A₀ ⊆ A°°` is an open
neighbourhood of `0` (`u` a topologically nilpotent *unit*, `A₀` an open ring of definition,
`u·a` topologically nilpotent for `a ∈ A₀` power-bounded). Uses only `[IsTateRing A]` (which
supplies `NonarchimedeanAddGroup A` as an instance), NOT the Tate-unsatisfiable
`[IsLinearTopology A A]`. This is the input Lemma 7.31 / Cor 7.32 actually need. -/
theorem IsTateRing.isOpen_topologicallyNilpotentElements_nonarch :
    IsOpen (TopologicalRing.topologicallyNilpotentElements A) := by
  obtain ⟨P⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
  obtain ⟨u, hu⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have hsub : (u : A) • (P.A₀ : Set A) ⊆
      (TopologicalRing.topNilpAddSubgroup A : Set A) := by
    rintro _ ⟨a, ha, rfl⟩
    change IsTopologicallyNilpotent ((u : A) • a)
    rw [smul_eq_mul, mul_comm]
    exact (P.mem_powerBoundedSubring ha).isTopologicallyNilpotent_mul hu
  have hopen : IsOpen ((TopologicalRing.topNilpAddSubgroup A : AddSubgroup A) : Set A) :=
    AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
      ((u.isUnit.isOpenMap_smul _ P.isOpen).mem_nhds
        ⟨0, P.A₀.zero_mem, smul_zero _⟩) hsub)
  exact hopen

omit [IsLinearTopology A A] in
/-- A continuous ring homomorphism from a Tate ring preserves topologically nilpotent units. -/
theorem IsTateRing.map_topologicallyNilpotent_unit {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) : ∃ v : Bˣ, IsTopologicallyNilpotent (v : B) := by
  obtain ⟨u, hu⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  refine ⟨u.map φ, ?_⟩
  change IsTopologicallyNilpotent (φ u)
  exact hu.map hφ

omit [IsLinearTopology A A] in
/-- A Huber ring that receives a continuous ring hom from a Tate ring is itself
Tate (Remark 6.11 of Wedhorn). -/
theorem IsTateRing.of_continuous_map {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsHuberRing B] {φ : A →+* B} (hφ : Continuous φ) :
    IsTateRing B where
  exists_topologicallyNilpotent_unit := IsTateRing.map_topologicallyNilpotent_unit hφ

end TateRing

/-! ### Topologically nilpotent elements and the ideal of definition -/

section TopNilAndI

open Filter Topology Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- If `u ∈ A₀` is topologically nilpotent in `A`, then `u^N ∈ I` for some `N`. -/
theorem PairOfDefinition.exists_pow_mem_I (P : PairOfDefinition A) {u : A}
    (hu_mem : u ∈ P.A₀) (hu_nil : IsTopologicallyNilpotent u) :
    ∃ N : ℕ, (⟨u, hu_mem⟩ : P.A₀) ^ N ∈ P.I := by
  have h_nhds : P.A₀.subtype '' ((P.I : Ideal P.A₀) : Set P.A₀) ∈ 𝓝 (0 : A) :=
    (pow_one P.I ▸ P.pow_image_isOpen 1).mem_nhds
      ⟨0, P.I.zero_mem, rfl⟩
  obtain ⟨N, ⟨⟨y, hy_mem⟩, hy_I, hval⟩⟩ := hu_nil.exists_pow_mem_of_mem_nhds h_nhds
  exact ⟨N, by rwa [show (⟨u, hu_mem⟩ : P.A₀) ^ N = ⟨y, hy_mem⟩ from
    Subtype.ext (by simpa [SubmonoidClass.coe_pow] using hval.symm)]⟩

/-- If `u` is a unit in `A` with `u ∈ A₀`, then `I^m ≤ Ideal.span {u_A₀ ^ N}`
for some `m`. -/
theorem PairOfDefinition.exists_pow_I_le_span_unit (P : PairOfDefinition A) {u : Aˣ}
    (hu_mem : (u : A) ∈ P.A₀) (N : ℕ) :
    ∃ m : ℕ, P.I ^ m ≤ Ideal.span {(⟨(u : A), hu_mem⟩ : P.A₀) ^ N} := by
  have h_open : IsOpen ((u ^ N : Aˣ) • (P.A₀ : Set A)) := isOpenMap_smul (u ^ N) _ P.isOpen
  obtain ⟨m, -, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (h_open.mem_nhds ⟨0, P.A₀.zero_mem, smul_zero _⟩)
  refine ⟨m, fun x hx ↦ ?_⟩
  obtain ⟨b, hb_mem, hb_eq⟩ := hm ⟨x, hx, rfl⟩
  have hval : (↑x : A) = (↑u) ^ N * b := by
    have : (↑(u ^ N : Aˣ) : A) * b = ↑x := by rw [← smul_eq_mul]; exact hb_eq
    rw [Units.val_pow_eq_pow_val] at this; exact this.symm
  exact (show x = (⟨(u : A), hu_mem⟩ : P.A₀) ^ N * ⟨b, hb_mem⟩ from
    Subtype.ext (by simpa using hval)).symm ▸
    Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end TopNilAndI

/-! ### Radicals of ideals generating the same adic topology -/

section RadicalEquiv

variable {R : Type*} [CommRing R] [TopologicalSpace R]

omit [TopologicalSpace R] in
/-- If `a ∈ I` and `I^m ⊆ (a)` for some `m`, then `I.radical = (a).radical`. -/
theorem Ideal.radical_eq_of_mem_and_pow_le {I : Ideal R} {a : R} (ha : a ∈ I) {m : ℕ}
    (hm : I ^ m ≤ Ideal.span {a}) : I.radical = (Ideal.span {a}).radical := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hx
    exact Ideal.mem_radical_iff.mpr ⟨k * m, hm (pow_mul x k m ▸ Ideal.pow_mem_pow hk m)⟩
  · exact Ideal.radical_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

omit [TopologicalSpace R] in
/-- The radical of a principal ideal is unchanged by taking powers of the generator. -/
theorem Ideal.radical_span_pow {a : R} {n : ℕ} (hn : 0 < n) :
    (Ideal.span {a ^ n}).radical = (Ideal.span {a}).radical := by
  rw [← Ideal.span_singleton_pow]
  apply le_antisymm
  · exact Ideal.radical_mono (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hn))
  · intro x hx
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hx
    exact Ideal.mem_radical_iff.mpr ⟨k * n, pow_mul x k n ▸ Ideal.pow_mem_pow hk n⟩

end RadicalEquiv

/-! ### IsAdic for interleaved ideals (Remark 6.12 of Wedhorn) -/

section InterleavedIsAdic

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- If `J ≤ I` and `I^m ≤ J`, then the `I`-adic topology is also `J`-adic
(Remark 6.12 of Wedhorn). -/
theorem PairOfDefinition.isAdic_of_interleaving (P : PairOfDefinition A) {J : Ideal P.A₀}
    (hJ_le : J ≤ P.I) {m : ℕ} (hI_le : P.I ^ m ≤ J) : IsAdic J := by
  have hJ_pow_le : ∀ n, J ^ n ≤ P.I ^ n := fun n ↦ pow_le_pow_left' hJ_le n
  have hI_pow_le : ∀ n, P.I ^ (m * n) ≤ J ^ n := fun n ↦
    pow_mul P.I m n ▸ pow_le_pow_left' hI_le n
  rw [isAdic_iff]
  constructor
  · intro n
    change IsOpen ((J ^ n).toAddSubgroup : Set P.A₀)
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset
        ((P.pow_isOpen (m * n)).mem_nhds (P.I ^ (m * n)).zero_mem)
        ((Submodule.coe_toAddSubgroup (J ^ n)).symm ▸ (hI_pow_le n)))
  · intro s hs
    obtain ⟨k, -, hk⟩ := P.isAdic.hasBasis_nhds_zero.mem_iff.mp hs
    exact ⟨k, fun x hx ↦ hk (hJ_pow_le k hx)⟩

end InterleavedIsAdic

/-! ### Power of topologically nilpotent is topologically nilpotent -/

/-- A positive power of a topologically nilpotent element is topologically nilpotent. -/
theorem isTopologicallyNilpotent_pow {A : Type*} [TopologicalSpace A] [MonoidWithZero A] {a : A}
    (ha : IsTopologicallyNilpotent a) {K : ℕ} (hK : 0 < K) :
    IsTopologicallyNilpotent (a ^ K) := by
  change Filter.Tendsto (fun n ↦ (a ^ K) ^ n) Filter.atTop (nhds 0)
  simp_rw [← pow_mul]
  exact ha.comp (Filter.tendsto_atTop_atTop_of_monotone
    (fun _ _ h ↦ Nat.mul_le_mul_left K h)
    (fun b ↦ ⟨b, le_mul_of_one_le_left (Nat.zero_le b) hK⟩))

/-! ### Principal pair of definition -/

section PrincipalPair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Replace the ideal of definition with a principal ideal `span{a}`, keeping the same `A₀`. -/
def PairOfDefinition.withPrincipal (P : PairOfDefinition A) {a : P.A₀} (ha : a ∈ P.I) {m : ℕ}
    (hm : P.I ^ m ≤ Ideal.span {a}) : PairOfDefinition A where
  A₀ := P.A₀
  I := Ideal.span {a}
  isOpen := P.isOpen
  fg := ⟨{a}, by simp [Finset.coe_singleton]⟩
  isAdic := P.isAdic_of_interleaving
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)) hm

/-- The ring of definition of `withPrincipal` equals the original. -/
@[simp]
theorem PairOfDefinition.withPrincipal_A₀ (P : PairOfDefinition A) {a : P.A₀} (ha : a ∈ P.I)
    {m : ℕ} (hm : P.I ^ m ≤ Ideal.span {a}) : (P.withPrincipal ha hm).A₀ = P.A₀ := rfl

/-- The ideal of definition of `withPrincipal` is `span {a}`. -/
@[simp]
theorem PairOfDefinition.withPrincipal_I (P : PairOfDefinition A) {a : P.A₀} (ha : a ∈ P.I)
    {m : ℕ} (hm : P.I ^ m ≤ Ideal.span {a}) : (P.withPrincipal ha hm).I = Ideal.span {a} := rfl

/-- A **principal pair of definition** for a topological ring `A`: a pair of
definition `(A₀, I)` together with a generator `π ∈ A₀` such that `I = (π)` and
`π` is a unit in `A`. In a Tate ring, principal pairs exist (Wedhorn 6.14). -/
structure PrincipalPairOfDefinition (A : Type*) [CommRing A] [TopologicalSpace A]
    extends PairOfDefinition A where
  /-- The generator of `I`. -/
  π : toPairOfDefinition.A₀
  /-- `I` is the principal ideal generated by `π`. -/
  I_eq_span : toPairOfDefinition.I = Ideal.span {π}
  /-- `π` is a unit in `A`. -/
  π_isUnit : IsUnit ((π : A))

/-- **Wedhorn Lemma 6.14, pinned ring of definition:** in a Tate ring, ANY pair of
definition refines to a principal pair with the SAME ring of definition
(`withPrincipal` keeps `A₀`; the generator is a power of the topologically nilpotent
unit, landed in `A₀` by openness). -/
theorem PairOfDefinition.exists_principal_same_A₀
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTateRing A]
    (P : PairOfDefinition A) :
    ∃ (P' : PairOfDefinition A) (π : P'.A₀),
      P'.A₀ = P.A₀ ∧ P'.I = Ideal.span {π} ∧ IsUnit ((π : A)) := by
  obtain ⟨u, hu_nilp⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  -- Step 1: Some power `u^k` of `u` lies in `P.A₀`, since `P.A₀` is open and
  -- `u` is topologically nilpotent.
  have h_nhds : (P.A₀ : Set A) ∈ nhds (0 : A) := P.isOpen.mem_nhds P.A₀.zero_mem
  have h_eventually : ∀ᶠ n in Filter.atTop, (u : A) ^ n ∈ P.A₀ := hu_nilp h_nhds
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp h_eventually
  -- Use k := K + 1 so that u^k is a positive power (hence a unit, topologically nilpotent).
  set k : ℕ := K + 1 with hk_def
  have hk_pos : 0 < k := Nat.succ_pos K
  -- `u^k : Aˣ` is a unit, its value in A is `(u : A)^k`.
  have hu_k_mem : ((u : A) ^ k) ∈ P.A₀ := hK k (Nat.le_succ K)
  have hu_k_nilp : IsTopologicallyNilpotent ((u : A) ^ k) :=
    isTopologicallyNilpotent_pow hu_nilp hk_pos
  -- View `u^k` as an element of `P.A₀`.
  set u_k : P.A₀ := ⟨((u : A) ^ k), hu_k_mem⟩ with hu_k_def
  -- Step 2: Some power `u_k^N` lies in `P.I`, by `exists_pow_mem_I`.
  have hu_k_val : (u_k : A) = (u : A) ^ k := rfl
  obtain ⟨N, hN_mem⟩ :
      ∃ N : ℕ, u_k ^ N ∈ P.I := by
    have := P.exists_pow_mem_I (u := (u : A) ^ k) hu_k_mem hu_k_nilp
    obtain ⟨N, hN⟩ := this
    exact ⟨N, hN⟩
  -- Define π := u_k^N.
  set π : P.A₀ := u_k ^ N with hπ_def
  have hπ_mem_I : π ∈ P.I := hN_mem
  -- Step 3: `P.I^m ≤ span {π}` for some `m`, via `exists_pow_I_le_span_unit`
  -- applied with the unit `u^k : Aˣ` and exponent `N`.
  have hu_k_unit_val : ((u ^ k : Aˣ) : A) ∈ P.A₀ := by
    rw [Units.val_pow_eq_pow_val]; exact hu_k_mem
  obtain ⟨m, hm_le⟩ := P.exists_pow_I_le_span_unit (u := u ^ k) hu_k_unit_val N
  -- Step 4: Build the principal pair via `P.withPrincipal`.
  -- The generator element in the lemma is `(⟨((u ^ k : Aˣ) : A), hu_k_unit_val⟩ : P.A₀) ^ N`,
  -- which equals `π` since `((u ^ k : Aˣ) : A) = (u : A) ^ k`.
  have hgen_eq :
      (⟨((u ^ k : Aˣ) : A), hu_k_unit_val⟩ : P.A₀) ^ N = π := by
    rw [hπ_def, hu_k_def]
    apply congr_arg (· ^ N)
    exact Subtype.ext (Units.val_pow_eq_pow_val u k)
  rw [hgen_eq] at hm_le
  -- Now construct `withPrincipal`.
  refine ⟨P.withPrincipal hπ_mem_I hm_le, π, rfl, rfl, ?_⟩
  -- Step 5: `(π : A)` is a unit. Since `π = u_k^N` and `(u_k : A) = (u : A)^k`,
  -- we have `(π : A) = (u : A) ^ (k * N)`, which is the value of a unit.
  have : (π : A) = ((u ^ (k * N) : Aˣ) : A) := by
    rw [hπ_def]
    show ((u_k ^ N : P.A₀) : A) = _
    rw [SubmonoidClass.coe_pow, hu_k_val, ← pow_mul, Units.val_pow_eq_pow_val]
  rw [this]
  exact Units.isUnit _

/-- **Wedhorn Lemma 6.14 (our version):** a Tate ring admits a pair of definition
whose ideal of definition is principal and whose generator (viewed in `A`) is a
topologically nilpotent unit. Corollary of `PairOfDefinition.exists_principal_same_A₀`. -/
theorem IsTateRing.exists_principal_pairOfDefinition
    (A : Type*) [CommRing A] [TopologicalSpace A] [IsTateRing A] :
    ∃ (P : PairOfDefinition A) (π : P.A₀),
      P.I = Ideal.span {π} ∧ IsUnit ((π : A)) := by
  obtain ⟨P⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
  obtain ⟨P', π, -, h1, h2⟩ := P.exists_principal_same_A₀
  exact ⟨P', π, h1, h2⟩

/-- A canonical principal pair of definition for a Tate ring, obtained via
`IsTateRing.exists_principal_pairOfDefinition` and `Classical.choice`. -/
noncomputable def IsTateRing.principalPair (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTateRing A] : PrincipalPairOfDefinition A :=
  let h := IsTateRing.exists_principal_pairOfDefinition A
  { toPairOfDefinition := h.choose
    π := h.choose_spec.choose
    I_eq_span := h.choose_spec.choose_spec.1
    π_isUnit := h.choose_spec.choose_spec.2 }

end PrincipalPair

/-! ### Enlarging the ring of definition (Remark after Definition 6.1 of Wedhorn)

Given a pair of definition `(A₀, I)` for a Huber ring `A` and a finite set `T ⊆ A`,
we construct a new pair of definition with ring of definition `Subring.closure (A₀ ∪ T)`.
The new ideal of definition is the image of `I` under the inclusion `A₀ ↪ B₀`.
-/

section AdjoinFinset

open Filter Topology Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The inclusion `P.A₀ ≤ Subring.closure (↑P.A₀ ∪ ↑T)`, used to construct the
ring homomorphism `P.A₀ →+* Subring.closure (↑P.A₀ ∪ ↑T)`. -/
theorem PairOfDefinition.le_adjoin_A₀ (P : PairOfDefinition A) (T : Finset A) :
    P.A₀ ≤ Subring.closure ((P.A₀ : Set A) ∪ ↑T) :=
  fun _ ha ↦ Subring.subset_closure (Set.subset_union_left ha)

/-- In a nonarchimedean topological ring, `AddSubgroup.closure` of a bounded set is bounded.
Given open additive subgroup `G ⊆ U` and `V` with `S * V ⊆ G`, we use
`AddSubgroup.closure_induction` (which has no multiplication case) to show
`AddSubgroup.closure(S) * V ⊆ G`. -/
private theorem isBounded_addSubgroup_closure [NonarchimedeanRing A]
    {S : Set A} (hS : TopologicalRing.IsBounded S) :
    TopologicalRing.IsBounded (AddSubgroup.closure S : Set A) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hSV⟩ := hS (G : Set A) (G.isOpen.mem_nhds G.zero_mem)
  -- Key lemma: ∀ s ∈ AddSubgroup.closure S, ∀ w ∈ V, s * w ∈ G
  have hcl : ∀ s ∈ AddSubgroup.closure S, ∀ w ∈ V, s * w ∈ (G : Set A) := by
    intro s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx => intro w hw; exact hSV (Set.mul_mem_mul hx hw)
    | zero => intro w _; simp [show (0 : A) ∈ (G : Set A) from G.zero_mem]
    | add _ _ _ _ h₁ h₂ => intro w hw; rw [add_mul]; exact G.add_mem (h₁ w hw) (h₂ w hw)
    | neg _ _ h₁ => intro w hw; rw [neg_mul]; exact G.neg_mem (h₁ w hw)
  exact ⟨V, hV, fun z hz => by
    obtain ⟨s, hs, v, hv, rfl⟩ := Set.mem_mul.mp hz
    exact hGU (hcl s hs v hv)⟩

theorem PairOfDefinition.isBounded_adjoin (P : PairOfDefinition A) (T : Finset A)
    (hT : ∀ t ∈ T, TopologicalRing.IsPowerBounded t)
    [NonarchimedeanRing A] :
    TopologicalRing.IsBounded ((Subring.closure ((P.A₀ : Set A) ∪ ↑T)) : Set A) := by
  classical
  -- Strategy: induction on T. At each step, adding a power-bounded element t
  -- enlarges the ring to a subset of AddSubgroup.closure(B_old * range(a^·)),
  -- which is bounded by isBounded_addSubgroup_closure.
  induction T using Finset.induction with
  | empty =>
    have : Subring.closure ((P.A₀ : Set A) ∪ ↑(∅ : Finset A)) = P.A₀ := by
      simp [Subring.closure_eq]
    rw [this]; exact P.isBounded_A₀
  | @insert a S ha ih =>
    have hT_S : ∀ t ∈ S, TopologicalRing.IsPowerBounded t :=
      fun t ht => hT t (Finset.mem_insert_of_mem ht)
    specialize ih hT_S
    set B_old := Subring.closure ((P.A₀ : Set A) ∪ ↑S)
    have ha_pb : TopologicalRing.IsPowerBounded a := hT a (Finset.mem_insert_self a S)
    -- B_old * range(a^·) is bounded (product of bounded sets)
    have hAM_bounded : TopologicalRing.IsBounded ((B_old : Set A) * Set.range (a ^ · : ℕ → A)) :=
      ih.mul ha_pb
    -- Subring.closure(A₀ ∪ insert a S) ⊆ AddSubgroup.closure(B_old * range(a^·))
    -- This is a subring: AddSubgroup.closure is closed under +, -, 0, and
    -- mul is handled by distributing products of sums into sums of products.
    -- We construct an intermediate subring to use Subring.closure_le.
    -- Define the subring structure on C = AddSubgroup.closure(B_old * range(a^·)).
    set BM := (B_old : Set A) * Set.range (a ^ · : ℕ → A)
    -- C is closed under multiplication: products of generators collapse.
    -- Use closure_induction₂ to handle both arguments simultaneously.
    have hC_mul : ∀ x ∈ AddSubgroup.closure BM, ∀ y ∈ AddSubgroup.closure BM,
        x * y ∈ AddSubgroup.closure BM := by
      intro x hx y hy
      induction hx, hy using AddSubgroup.closure_induction₂ with
      | mem u v hu hv =>
        obtain ⟨b₁, hb₁, _, ⟨k₁, rfl⟩, rfl⟩ := Set.mem_mul.mp hu
        obtain ⟨b₂, hb₂, _, ⟨k₂, rfl⟩, rfl⟩ := Set.mem_mul.mp hv
        apply AddSubgroup.subset_closure
        rw [show b₁ * a ^ k₁ * (b₂ * a ^ k₂) = (b₁ * b₂) * a ^ (k₁ + k₂) by ring]
        exact Set.mul_mem_mul (B_old.mul_mem hb₁ hb₂) ⟨k₁ + k₂, rfl⟩
      | zero_left _ _ => simp
      | zero_right _ _ => simp
      | add_left _ _ _ _ _ _ ih₁ ih₂ =>
        rw [add_mul]; exact (AddSubgroup.closure BM).add_mem ih₁ ih₂
      | add_right _ _ _ _ _ _ ih₁ ih₂ =>
        rw [mul_add]; exact (AddSubgroup.closure BM).add_mem ih₁ ih₂
      | neg_left _ _ _ _ ih₁ =>
        rw [neg_mul]; exact (AddSubgroup.closure BM).neg_mem ih₁
      | neg_right _ _ _ _ ih₁ =>
        rw [mul_neg]; exact (AddSubgroup.closure BM).neg_mem ih₁
    -- Build a Subring from C
    -- Helper: membership in BM via x = b * a^k
    have mem_BM (b : A) (hb : b ∈ B_old) (k : ℕ) : b * a ^ k ∈ BM :=
      Set.mul_mem_mul hb ⟨k, rfl⟩
    set C_subring : Subring A :=
      { carrier := AddSubgroup.closure BM
        mul_mem' := fun {_ _} ha hb => hC_mul _ ha _ hb
        one_mem' := by
          rw [show (1 : A) = 1 * a ^ 0 by simp]
          exact AddSubgroup.subset_closure (mem_BM 1 B_old.one_mem 0)
        zero_mem' := (AddSubgroup.closure BM).zero_mem
        add_mem' := fun {_ _} ha hb => (AddSubgroup.closure BM).add_mem ha hb
        neg_mem' := fun {_} ha => (AddSubgroup.closure BM).neg_mem ha }
    -- Show generators are in C_subring
    have h_sub : (P.A₀ : Set A) ∪ ↑(insert a S) ⊆ (C_subring : Set A) := by
      rw [Finset.coe_insert]
      intro x hx
      change x ∈ (AddSubgroup.closure BM : Set A)
      rcases hx with hx_A₀ | hx_a
      · -- x ∈ A₀: x ∈ B_old (via A₀ ⊆ A₀ ∪ S), so x = x * a^0
        rw [show x = x * a ^ 0 by simp]
        exact AddSubgroup.subset_closure
          (mem_BM x (Subring.subset_closure (Set.mem_union_left _ hx_A₀)) 0)
      · rcases Set.mem_insert_iff.mp hx_a with hxa | hx_S
        · -- x = a = 1 * a^1
          rw [hxa, show a = 1 * a ^ 1 by simp]
          exact AddSubgroup.subset_closure (mem_BM 1 B_old.one_mem 1)
        · -- x ∈ S: x ∈ B_old (via S ⊆ A₀ ∪ S), so x = x * a^0
          rw [show x = x * a ^ 0 by simp]
          exact AddSubgroup.subset_closure
            (mem_BM x (Subring.subset_closure (Set.mem_union_right _ hx_S)) 0)
    -- Subring.closure ⊆ C_subring ⊆ AddSubgroup.closure BM
    exact (isBounded_addSubgroup_closure hAM_bounded).subset (Subring.closure_le.mpr h_sub)

/-- Adjoin a finite set of power-bounded elements to the ring of definition.
The new ring of definition is `Subring.closure (A₀ ∪ ↑T)` and the new ideal
is the image of `I` under the inclusion. This gives a valid pair of definition
(Remark after Definition 6.1 of Wedhorn).

The power-boundedness hypothesis on elements of `T` ensures that `B₀ = A₀[T]`
is a bounded subring of `A`, which is needed to show that the `I'`-adic topology
equals the subspace topology (the "shrinking" direction of `isAdic_iff`). -/
def PairOfDefinition.adjoin (P : PairOfDefinition A) (T : Finset A)
    (hT : ∀ t ∈ T, TopologicalRing.IsPowerBounded t)
    [NonarchimedeanRing A] :
    PairOfDefinition A where
  A₀ := Subring.closure ((P.A₀ : Set A) ∪ ↑T)
  I := Ideal.map (Subring.inclusion (P.le_adjoin_A₀ T)) P.I
  isOpen := by
    apply AddSubgroup.isOpen_of_mem_nhds
      (Subring.closure ((P.A₀ : Set A) ∪ ↑T)).toAddSubgroup
    exact Filter.mem_of_superset (P.isOpen.mem_nhds P.A₀.zero_mem)
      (P.le_adjoin_A₀ T)
  fg := P.fg.map _
  isAdic := by
    set B₀ := Subring.closure ((P.A₀ : Set A) ∪ ↑T)
    set incl := Subring.inclusion (P.le_adjoin_A₀ T)
    set I' := Ideal.map incl P.I
    rw [isAdic_iff]
    constructor
    · -- Part 1: Each I'^n is open in B₀ (subspace topology)
      intro n
      apply AddSubgroup.isOpen_of_mem_nhds (I' ^ n).toAddSubgroup (g := 0)
      rw [Submodule.coe_toAddSubgroup]
      -- I'^n ⊇ incl(I^n), and incl(I^n) maps to an open set in A
      have h_nhds : Subtype.val ⁻¹' (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) ∈
          𝓝 (0 : B₀) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds
          (show Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) ∈ 𝓝 (0 : A) from
            (P.pow_image_isOpen n).mem_nhds ⟨0, (P.I ^ n).zero_mem, rfl⟩)
      apply Filter.mem_of_superset h_nhds
      -- Show val⁻¹'(val '' I^n) ⊆ I'^n
      intro ⟨x, hx_mem⟩ hx
      simp only [Set.mem_preimage] at hx
      obtain ⟨⟨y, hy_A₀⟩, hy_In, hval⟩ := hx
      -- x = y as elements of A, so incl(⟨y, hy_A₀⟩) corresponds to ⟨x, hx_mem⟩
      have heq : (⟨x, hx_mem⟩ : B₀) = incl ⟨y, hy_A₀⟩ := by
        ext; exact hval.symm
      rw [heq, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hy_In
    · -- Part 2: The powers I'^n shrink to any nhd of 0 in B₀.
      -- I'^n = Ideal.map incl (P.I^n). Elements are B₀-linear combinations
      -- of incl(a) with a ∈ P.I^n. Their A-values lie in B₀ · val''(P.I^n) ⊆ G.
      intro s hs
      rw [nhds_induced] at hs
      obtain ⟨U_A, hU_A, hU_sub⟩ := Filter.mem_comap.mp hs
      obtain ⟨G, hGU⟩ := NonarchimedeanRing.is_nonarchimedean U_A hU_A
      obtain ⟨V, hV, hBV⟩ := P.isBounded_adjoin T hT (G : Set A)
        (G.isOpen.mem_nhds G.zero_mem)
      obtain ⟨n, _, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hV
      refine ⟨n, fun x hx_In => hU_sub (Set.mem_preimage.mpr (hGU ?_))⟩
      -- x ∈ I'^n = (Ideal.map incl P.I)^n = Ideal.map incl (P.I^n)
      have hx_map : x ∈ Ideal.map incl (P.I ^ n) := Ideal.map_pow incl P.I n ▸ hx_In
      -- Ideal.map f J = Submodule.span _ (f '' J). Use mem_span_set for Finsupp.
      set img_set := incl '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)
      obtain ⟨f, hf_supp, hf_sum⟩ := Submodule.mem_span_set.mp hx_map
      -- val(x) = val(∑ f(i) • i) = ∑ val(f(i)) * val(i)
      -- Each term: val(f(i)) ∈ B₀, val(i) ∈ val''(P.I^n) ⊆ V.
      -- So val(f(i)) * val(i) ∈ B₀ * V ⊆ G. Sum ∈ G (additive subgroup).
      rw [← hf_sum]
      change (Finsupp.sum f fun i a => a • i : B₀).val ∈ (G : Set A)
      simp only [Finsupp.sum, smul_eq_mul]
      rw [show ((∑ x ∈ f.support, f x * x : B₀) : A) =
          ∑ x ∈ f.support, ((f x * x : B₀) : A) from map_sum B₀.subtype _ _]
      apply G.toAddSubgroup.sum_mem
      intro i hi
      have hi_img : i ∈ img_set := hf_supp (Finset.mem_coe.mpr hi)
      obtain ⟨a, ha, rfl⟩ := hi_img
      -- Goal: ((f (incl a) * incl a : B₀) : A) ∈ G
      have : ((f (incl a) * incl a : B₀) : A) = (f (incl a) : A) * (a : A) := by
        rw [MulMemClass.coe_mul, Subring.coe_inclusion]
      rw [this]
      exact hBV (Set.mul_mem_mul (f (incl a)).2 (hn ⟨a, ha, rfl⟩))

/-- The original ring of definition is contained in the enlarged one. -/
theorem PairOfDefinition.adjoin_A₀_le (P : PairOfDefinition A) (T : Finset A)
    (hT : ∀ t ∈ T, TopologicalRing.IsPowerBounded t)
    [NonarchimedeanRing A] :
    P.A₀ ≤ (P.adjoin T hT).A₀ := by
  change P.A₀ ≤ Subring.closure ((P.A₀ : Set A) ∪ ↑T)
  exact P.le_adjoin_A₀ T

/-- Every element of `T` belongs to the enlarged ring of definition. -/
theorem PairOfDefinition.mem_adjoin_of_mem_T (P : PairOfDefinition A) (T : Finset A)
    (hT : ∀ t ∈ T, TopologicalRing.IsPowerBounded t)
    [NonarchimedeanRing A]
    {t : A} (ht : t ∈ T) : t ∈ (P.adjoin T hT).A₀ := by
  change t ∈ Subring.closure ((P.A₀ : Set A) ∪ ↑T)
  exact Subring.subset_closure (Set.mem_union_right _ (Finset.mem_coe.mpr ht))

/-- **`A°` is integrally closed** (Wedhorn 5.30(4), general form): if `x` satisfies a monic
polynomial with power-bounded coefficients, then `x` is power-bounded. Proof: the finitely many
power-bounded coefficients, adjoined to a ring of definition `A₀`, generate a *bounded* subring
(`isBounded_adjoin`); `x` is integral over it, hence power-bounded
(`IsBounded.isPowerBounded_of_isIntegral`). This is the "integral over `A°` ⟹ `A°`" form, replacing
the narrower "integral over a fixed *bounded* subring" — the faithful Wedhorn route for the affinoid
`B⁺ ⊆ B°` axiom (avoids the over-strong uniform-boundedness statement). -/
theorem PairOfDefinition.isPowerBounded_of_monic_powerBounded_eval
    (P : PairOfDefinition A) [NonarchimedeanRing A]
    {x : A} {p : Polynomial A} (hp_monic : p.Monic)
    (hp_coeff : ∀ i, TopologicalRing.IsPowerBounded (p.coeff i))
    (hp_eval : p.eval x = 0) :
    TopologicalRing.IsPowerBounded x := by
  classical
  set T : Finset A := (Finset.range (p.natDegree + 1)).image p.coeff with hT_def
  have hT_pb : ∀ t ∈ T, TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [hT_def, Finset.mem_image] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact hp_coeff i
  set B' : Subring A := Subring.closure ((P.A₀ : Set A) ∪ ↑T) with hB'_def
  have hB'_bounded : TopologicalRing.IsBounded (B' : Set A) := P.isBounded_adjoin T hT_pb
  have hcoeff_mem : ∀ i, p.coeff i ∈ B' := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · exact Subring.subset_closure (Set.mem_union_right _
        (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩)))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
      exact B'.zero_mem
  have hcoeffs : (↑p.coeffs : Set A) ⊆ (B' : Set A) := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨i, _, rfl⟩ := hc
    exact hcoeff_mem i
  have hint : IsIntegral (↥B') x := by
    refine ⟨p.toSubring B' hcoeffs, ?_, ?_⟩
    · rw [Polynomial.monic_toSubring]; exact hp_monic
    · change Polynomial.eval₂ (algebraMap (↥B') A) x (p.toSubring B' hcoeffs) = 0
      rw [Polynomial.eval₂_eq_eval_map,
        show (algebraMap (↥B') A) = B'.subtype from rfl, Polynomial.map_toSubring]
      exact hp_eval
  exact hB'_bounded.isPowerBounded_of_isIntegral hint

end AdjoinFinset

/-! ### Adic homomorphisms (Definition 6.23 of Wedhorn) -/

section AdicHom

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]

/-- The restriction of a ring hom `φ : A →+* B` to subrings `A₀` and `B₀`, given that
`φ` maps `A₀` into `B₀`. -/
def PairOfDefinition.restrictRingHom (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (φ : A →+* B) (h : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀) : PA.A₀ →+* PB.A₀ :=
  (φ.comp PA.A₀.subtype).codRestrict PB.A₀ fun a ↦ h a a.2

/-- A ring homomorphism between Huber rings is **adic** if compatible pairs of
definition have ideals with equal radicals (Definition 6.23 of Wedhorn). -/
def IsAdicHom (φ : A →+* B) : Prop :=
  ∃ (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (h : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀),
    (Ideal.map (PA.restrictRingHom PB φ h) PA.I).radical = PB.I.radical

end AdicHom

/-! ### Proposition 6.25 of Wedhorn: continuous from Tate ⟹ adic -/

section Prop625

open Filter Topology Pointwise

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B]

/-- The `restrictRingHom` for `withPrincipal` pairs equals the original. -/
private theorem restrictRingHom_withPrincipal (PA : PairOfDefinition A)
    (PB : PairOfDefinition B) (φ : A →+* B) (h : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    {aA : PA.A₀} (haA : aA ∈ PA.I) {mA : ℕ} (hmA : PA.I ^ mA ≤ Ideal.span {aA})
    {aB : PB.A₀} (haB : aB ∈ PB.I) {mB : ℕ} (hmB : PB.I ^ mB ≤ Ideal.span {aB}) :
    (PA.withPrincipal haA hmA).restrictRingHom (PB.withPrincipal haB hmB) φ h =
    PA.restrictRingHom PB φ h := rfl

/-- If `a ^ e = b ^ e'` for positive `e, e'`, then `a` and `b` are in each other's
span-radicals. -/
private theorem radical_span_eq_of_pow_eq {R : Type*} [CommRing R] {a b : R} {e e' : ℕ}
    (he : 0 < e) (he' : 0 < e') (h : a ^ e = b ^ e') :
    (Ideal.span {a}).radical = (Ideal.span {b}).radical := by
  have ha_rad : a ∈ (Ideal.span {b}).radical := by
    rw [Ideal.mem_radical_iff]; refine ⟨e, ?_⟩; rw [h]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp he')
    rw [hj]
    exact Ideal.pow_le_self (Nat.succ_ne_zero j)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
  have hb_rad : b ∈ (Ideal.span {a}).radical := by
    rw [Ideal.mem_radical_iff]; refine ⟨e', ?_⟩; rw [← h]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp he)
    rw [hj]
    exact Ideal.pow_le_self (Nat.succ_ne_zero j)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
  exact le_antisymm
    (Ideal.radical_le_radical_iff.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha_rad)))
    (Ideal.radical_le_radical_iff.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hb_rad)))

/-- Given a topologically nilpotent unit `u` and a pair of definition `P`,
find exponents `K`, `N` with `0 < K`, `0 < N` such that `(u^K)^N ∈ P.I`
and `P.I^m ≤ span{(u^K)^N}` for some `m`, yielding a principal pair. -/
private theorem nilpotentUnit_principalData {C : Type*} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] (P : PairOfDefinition C) (u : Cˣ)
    (hu_nil : IsTopologicallyNilpotent (u : C)) :
    ∃ (K N : ℕ) (_ : 0 < K) (_ : 0 < N)
      (hu_K : (u : C) ^ K ∈ P.A₀)
      (_ : (⟨(u : C) ^ K, hu_K⟩ : P.A₀) ^ N ∈ P.I),
      ∃ m, P.I ^ m ≤
        Ideal.span {(⟨(u : C) ^ K, hu_K⟩ : P.A₀) ^ N} := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (hu_nil (P.isOpen.mem_nhds P.A₀.zero_mem))
  set K := max K₀ 1
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hu_K : (u : C) ^ K ∈ P.A₀ := hK₀ K (le_max_left _ _)
  obtain ⟨N₀, hN₀⟩ := P.exists_pow_mem_I hu_K
    (isTopologicallyNilpotent_pow hu_nil hK_pos)
  set N := N₀ + 1
  have hN_mem : (⟨(u : C) ^ K, hu_K⟩ : P.A₀) ^ N ∈ P.I := by
    rw [show N = 1 + N₀ from by omega, pow_add, pow_one]
    exact Ideal.mul_mem_left _ _ hN₀
  have hu_K_unit : ((u ^ K : Cˣ) : C) ∈ P.A₀ := by
    rwa [Units.val_pow_eq_pow_val]
  obtain ⟨m, hm⟩ := P.exists_pow_I_le_span_unit hu_K_unit N
  rw [show (⟨((u ^ K : Cˣ) : C), hu_K_unit⟩ : P.A₀) =
    ⟨(u : C) ^ K, hu_K⟩ from
    Subtype.ext (Units.val_pow_eq_pow_val u K)] at hm
  exact ⟨K, N, hK_pos, Nat.succ_pos N₀, hu_K, hN_mem, m, hm⟩

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- **Proposition 6.25 of Wedhorn**: a continuous ring homomorphism
from a Tate ring is adic. -/
theorem IsTateRing.isAdicHom_of_continuous_with_pairs [IsTateRing A] [IsHuberRing B]
    {φ : A →+* B} (hφ : Continuous φ) (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀) : IsAdicHom φ := by
  obtain ⟨u, hu_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have hv_nil : IsTopologicallyNilpotent (φ u) := hu_nil.map hφ
  obtain ⟨K, N, hK_pos, hN_pos, hu_K, hN_mem, mA, hmA⟩ :=
    nilpotentUnit_principalData PA u hu_nil
  set uK : PA.A₀ := ⟨(u : A) ^ K, hu_K⟩
  obtain ⟨L, M, hL_pos, hM_pos, hv_L, hM_mem, mB, hmB⟩ :=
    nilpotentUnit_principalData PB (Units.map (φ : A →* B) u)
      (show IsTopologicallyNilpotent ((Units.map (φ : A →* B) u : B))
        from Units.coe_map (φ : A →* B) u ▸ hv_nil)
  set vL : PB.A₀ := ⟨↑((Units.map (φ : A →* B)) u) ^ L, hv_L⟩ with hvL_def
  have hmB' : PB.I ^ mB ≤ Ideal.span {vL ^ M} := hmB
  refine ⟨PA.withPrincipal hN_mem hmA,
    PB.withPrincipal hM_mem hmB', h_map, ?_⟩
  simp only [restrictRingHom_withPrincipal, PairOfDefinition.withPrincipal_I]
  erw [Ideal.map_span, Set.image_singleton]
  set a : PB.A₀ := (PA.restrictRingHom PB φ h_map) (uK ^ N)
  have h_agree : a ^ (L * M) = (vL ^ M) ^ (K * N) :=
    Subtype.ext (by
      simp only [a, PairOfDefinition.restrictRingHom, uK, vL,
        SubmonoidClass.coe_pow,
         map_pow, ← pow_mul]
      change (φ (↑u ^ K)) ^ (N * (L * M)) = (φ ↑u) ^ (L * (M * (K * N)))
      rw [map_pow, ← pow_mul]
      congr 1
      ring)
  exact radical_span_eq_of_pow_eq
    (Nat.mul_pos hL_pos hM_pos)
    (Nat.mul_pos hK_pos hN_pos)
    h_agree

end Prop625
