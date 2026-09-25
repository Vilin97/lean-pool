/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.CharSplit

/-!
# Additive splitting of the completed cycle product

The completed cycle product of a permutation, generalised from
`Fin n` to an arbitrary finite carrier, splits additively over the
invariant subsets of the carrier: at a pointwise sum of scalar
sequences it equals the sum, over all invariant subsets, of the
product of the completed cycle products of the two restrictions —
to the subset and to its complement.  This is the combinatorial
heart of the induction-multiplicity identity.

The route is through orbits: the completed cycle product is the
product of `t (O.card)` over the set of all orbits of the
permutation, singleton orbits included; the splitting is then the
expansion of a product of binomials, with subsets of the orbit set
enumerating exactly the invariant subsets of the carrier.
-/

namespace RS

open Finset Equiv

variable {α : Type*}

/-! ### The completed cycle product over an arbitrary carrier -/

/-- The completed cycle product of a prospective power-sum sequence
over an arbitrary finite carrier: the product of `t` over the cycle
type, completed by `t 1` over the fixed points. -/
noncomputable def cycleFunG [Fintype α] [DecidableEq α]
    (t : ℕ → ℂ) (π : Equiv.Perm α) : ℂ :=
  (π.cycleType.map t).prod * (t 1) ^ (Fintype.card α - π.cycleType.sum)

/-- On `Fin n` the generalised completed cycle product is the
completed cycle product. -/
theorem cycleFunG_fin {n : ℕ} (t : ℕ → ℂ) (π : Equiv.Perm (Fin n)) :
    cycleFunG t π = cycleFun t π := by
  simp only [cycleFunG, cycleFun, Fintype.card_fin]

/-- The cycle type is invariant under conjugation by an equivalence
of carriers.  Universe-polymorphic form of `cycleType_permCongr`. -/
theorem cycleType_permCongr'
    [Fintype α] [DecidableEq α] {β : Type*} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (π : Equiv.Perm α) :
    (e.permCongr π).cycleType = π.cycleType := by
  let : DecidablePred (fun _ : β => True) := fun _ => .isTrue trivial
  have h : e.permCongr π =
      π.extendDomain (e.trans (Equiv.subtypeUnivEquiv
        (fun _ : β => trivial)).symm) := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype _ _ trivial]
    simp
  rw [h, Equiv.Perm.cycleType_extendDomain]

/-- The completed cycle product is invariant under conjugation by
an equivalence of carriers. -/
theorem cycleFunG_permCongr
    [Fintype α] [DecidableEq α] {β : Type*} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (t : ℕ → ℂ)
    (π : Equiv.Perm α) :
    cycleFunG t (e.permCongr π) = cycleFunG t π := by
  rw [cycleFunG, cycleFunG, cycleType_permCongr',
    (Fintype.card_congr e.symm : Fintype.card β = Fintype.card α)]

/-! ### Invariant subsets -/

/-- A finite set closed under a permutation is closed in both
directions: the permutation restricts to an injective self-map of
the set, which is onto by finiteness. -/
theorem mem_iff_of_invariant
    {π : Equiv.Perm α} {s : Finset α}
    (hs : ∀ x ∈ s, π x ∈ s) : ∀ x, π x ∈ s ↔ x ∈ s := by
  classical
  have himg : s.image π = s :=
    Finset.eq_of_subset_of_card_le
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hs x hx)
      (le_of_eq (Finset.card_image_of_injective s π.injective).symm)
  intro x
  refine ⟨fun hx => ?_, hs x⟩
  rw [← himg] at hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
  rwa [← π.injective hyx]

/-- The complement of an invariant set is invariant. -/
theorem invariant_compl [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {s : Finset α}
    (hs : ∀ x ∈ s, π x ∈ s) : ∀ x ∈ sᶜ, π x ∈ sᶜ := by
  intro x hx
  rw [Finset.mem_compl] at hx ⊢
  exact fun h => hx ((mem_iff_of_invariant hs x).mp h)

/-- Integer powers of a permutation preserve a two-sided invariant
set. -/
theorem zpow_apply_mem_of_invariant {π : Equiv.Perm α}
    {s : Finset α} (hs : ∀ x, π x ∈ s ↔ x ∈ s) {x : α}
    (hx : x ∈ s) (i : ℤ) : (π ^ i) x ∈ s := by
  rw [← Equiv.Perm.subtypePerm_apply_zpow_of_mem hs hx]
  exact Subtype.coe_prop _

/-- The restriction of a permutation to a finite subset, as a
permutation of the subtype: the two-sided restriction when the
subset is invariant, the identity otherwise. -/
def permRestrict [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (s : Finset α) :
    Equiv.Perm {x // x ∈ s} :=
  if h : ∀ x, π x ∈ s ↔ x ∈ s then π.subtypePerm h else 1

/-- On an invariant subset the restriction is `subtypePerm`. -/
theorem permRestrict_of_invariant [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {s : Finset α}
    (h : ∀ x, π x ∈ s ↔ x ∈ s) :
    permRestrict π s = π.subtypePerm h := by
  rw [permRestrict, dite_eq_left h]

/-! ### Orbits as finite sets -/

/-- The orbit of a point under a permutation, as a finite set;
singleton orbits of fixed points included. -/
def cycleOrbit [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (x : α) : Finset α :=
  Finset.univ.filter (π.SameCycle x)

/-- Membership in an orbit is the same-cycle relation. -/
theorem mem_cycleOrbit [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {x y : α} :
    y ∈ cycleOrbit π x ↔ π.SameCycle x y := by
  simp [cycleOrbit]

/-- A point lies in its own orbit. -/
theorem self_mem_cycleOrbit [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (x : α) :
    x ∈ cycleOrbit π x :=
  mem_cycleOrbit.mpr (Equiv.Perm.SameCycle.refl π x)

/-- The image of a point lies in the point's orbit. -/
theorem apply_mem_cycleOrbit [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (x : α) :
    π x ∈ cycleOrbit π x :=
  mem_cycleOrbit.mpr
    (Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl)

/-- Orbits through a common point coincide. -/
theorem cycleOrbit_eq_of_mem [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {x y : α}
    (h : y ∈ cycleOrbit π x) : cycleOrbit π y = cycleOrbit π x := by
  have hxy := mem_cycleOrbit.mp h
  ext z
  rw [mem_cycleOrbit, mem_cycleOrbit]
  exact ⟨fun hyz => hxy.trans hyz, fun hxz => hxy.symm.trans hxz⟩

/-- The orbit of a fixed point is a singleton. -/
theorem cycleOrbit_eq_singleton [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {x : α}
    (hx : π x = x) : cycleOrbit π x = {x} := by
  ext y
  rw [mem_cycleOrbit, Finset.mem_singleton]
  exact ⟨fun h => (h.eq_of_left hx).symm,
    fun h => by rw [h]⟩

/-- The orbit of a moved point is the support of its cycle. -/
theorem cycleOrbit_eq_support_cycleOf [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {x : α}
    (hx : π x ≠ x) : cycleOrbit π x = (π.cycleOf x).support := by
  ext y
  rw [mem_cycleOrbit, Equiv.Perm.mem_support_cycleOf_iff' hx]

/-- The set of orbits of a permutation, singleton orbits
included. -/
def cycleOrbits [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) : Finset (Finset α) :=
  Finset.univ.image (cycleOrbit π)

/-- Every orbit belongs to the set of orbits. -/
theorem cycleOrbit_mem_cycleOrbits [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (x : α) :
    cycleOrbit π x ∈ cycleOrbits π :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- The members of the set of orbits are the orbits. -/
theorem mem_cycleOrbits [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {O : Finset α} :
    O ∈ cycleOrbits π ↔ ∃ x, cycleOrbit π x = O := by
  simp [cycleOrbits]

/-- An orbit is the orbit of each of its points. -/
theorem eq_cycleOrbit_of_mem [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α}
    {O : Finset α} (hO : O ∈ cycleOrbits π) {x : α} (hx : x ∈ O) :
    O = cycleOrbit π x := by
  obtain ⟨y, rfl⟩ := mem_cycleOrbits.mp hO
  exact (cycleOrbit_eq_of_mem hx).symm

/-- Orbits are nonempty. -/
theorem nonempty_of_mem_cycleOrbits [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α}
    {O : Finset α} (hO : O ∈ cycleOrbits π) : O.Nonempty := by
  obtain ⟨x, rfl⟩ := mem_cycleOrbits.mp hO
  exact ⟨x, self_mem_cycleOrbit π x⟩

/-! ### The completed cycle product as an orbit product -/

/-- The singleton orbits are the fixed points. -/
theorem filter_card_one_cycleOrbits [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) :
    (cycleOrbits π).filter (fun O => O.card = 1) =
      π.supportᶜ.image (fun x => {x}) := by
  ext O
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hO, hcard⟩
    obtain ⟨x, rfl⟩ := mem_cycleOrbits.mp hO
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hxa : x = a := Finset.mem_singleton.mp
      (ha ▸ self_mem_cycleOrbit π x)
    have hfix : π x = x := by
      have h1 : π x ∈ ({a} : Finset α) :=
        ha ▸ apply_mem_cycleOrbit π x
      rw [Finset.mem_singleton] at h1
      rw [h1, hxa]
    exact ⟨x, Finset.mem_compl.mpr fun hs =>
        Equiv.Perm.mem_support.mp hs hfix,
      (cycleOrbit_eq_singleton hfix).symm⟩
  · rintro ⟨x, hx, rfl⟩
    have hfix : π x = x :=
      Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp hx)
    exact ⟨cycleOrbit_eq_singleton hfix ▸
      cycleOrbit_mem_cycleOrbits π x, Finset.card_singleton x⟩

/-- The non-singleton orbits are the supports of the cycle
factors. -/
theorem filter_card_ne_one_cycleOrbits [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) :
    (cycleOrbits π).filter (fun O => ¬O.card = 1) =
      π.cycleFactorsFinset.image Equiv.Perm.support := by
  ext O
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hO, hcard⟩
    obtain ⟨x, rfl⟩ := mem_cycleOrbits.mp hO
    have hx : π x ≠ x := fun hfix => hcard
      (by rw [cycleOrbit_eq_singleton hfix, Finset.card_singleton])
    exact ⟨π.cycleOf x,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr hx),
      (cycleOrbit_eq_support_cycleOf hx).symm⟩
  · rintro ⟨c, hc, rfl⟩
    have hcyc : c.IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    obtain ⟨a, ha⟩ := hcyc.nonempty_support
    have hπa : π a ≠ a := by
      rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 a ha]
      exact Equiv.Perm.mem_support.mp ha
    have hcc : c = π.cycleOf a := Equiv.Perm.cycle_is_cycleOf ha hc
    refine ⟨?_, ?_⟩
    · rw [hcc, ← cycleOrbit_eq_support_cycleOf hπa]
      exact cycleOrbit_mem_cycleOrbits π a
    · have h2 := hcyc.two_le_card_support
      omega

/-- **The completed cycle product is the orbit product**: the
product of `t` at the orbit sizes, over all orbits, singleton
orbits included. -/
theorem cycleFunG_eq_prod_cycleOrbits [Fintype α] [DecidableEq α]
    (t : ℕ → ℂ)
    (π : Equiv.Perm α) :
    cycleFunG t π = ∏ O ∈ cycleOrbits π, t O.card := by
  rw [← Finset.prod_filter_mul_prod_filter_not (cycleOrbits π)
    (fun O => O.card = 1) (fun O => t O.card)]
  rw [filter_card_one_cycleOrbits, filter_card_ne_one_cycleOrbits]
  rw [Finset.prod_image
    (fun x _ y _ h => Finset.singleton_injective h)]
  rw [Finset.prod_image (fun c hc c' hc' h => by
    have hcyc : Equiv.Perm.IsCycle c :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    obtain ⟨a, ha⟩ := hcyc.nonempty_support
    have ha' : a ∈ c'.support := h ▸ ha
    rw [Equiv.Perm.cycle_is_cycleOf ha hc,
      Equiv.Perm.cycle_is_cycleOf ha' hc'])]
  have hsing : ∏ x ∈ π.supportᶜ, t ({x} : Finset α).card =
      (t 1) ^ (Fintype.card α - π.cycleType.sum) := by
    rw [Finset.prod_congr rfl fun x _ => by
      rw [Finset.card_singleton]]
    rw [Finset.prod_const, Finset.card_compl,
      Equiv.Perm.sum_cycleType]
  have hbig : ∏ c ∈ π.cycleFactorsFinset, t c.support.card =
      (π.cycleType.map t).prod := by
    rw [Equiv.Perm.cycleType_def, Multiset.map_map]
    rfl
  rw [hsing, hbig, cycleFunG, mul_comm]

/-! ### Restriction to an invariant subset -/

/-- Orbits of points of a two-sided invariant set stay inside the
set. -/
theorem cycleOrbit_subset_of_invariant [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α}
    {s : Finset α} (hs : ∀ x, π x ∈ s ↔ x ∈ s) {x : α}
    (hx : x ∈ s) : cycleOrbit π x ⊆ s := by
  intro y hy
  obtain ⟨i, hi⟩ := mem_cycleOrbit.mp hy
  exact hi ▸ zpow_apply_mem_of_invariant hs hx i

/-- The orbit of the restriction to an invariant set is the orbit
of the ambient permutation, transported along the subtype map. -/
theorem cycleOrbit_subtypePerm [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {s : Finset α}
    (h : ∀ x, π x ∈ s ↔ x ∈ s) (x : {u // u ∈ s}) :
    (cycleOrbit (π.subtypePerm h) x).map
      (Function.Embedding.subtype _) = cycleOrbit π ↑x := by
  ext y
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact mem_cycleOrbit.mpr
      (Equiv.Perm.sameCycle_subtypePerm.mp (mem_cycleOrbit.mp hy'))
  · intro hy
    have hsc := mem_cycleOrbit.mp hy
    have hys : y ∈ s := cycleOrbit_subset_of_invariant h x.2 hy
    exact ⟨⟨y, hys⟩, mem_cycleOrbit.mpr
      (Equiv.Perm.sameCycle_subtypePerm.mpr hsc), rfl⟩

/-- The completed cycle product of the restriction to an invariant
set is the product over the ambient orbits inside the set. -/
theorem cycleFunG_subtypePerm [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {s : Finset α}
    (h : ∀ x, π x ∈ s ↔ x ∈ s) (t : ℕ → ℂ) :
    cycleFunG t (π.subtypePerm h) =
      ∏ O ∈ (cycleOrbits π).filter (fun O => O ⊆ s), t O.card := by
  rw [cycleFunG_eq_prod_cycleOrbits]
  refine Finset.prod_nbij'
    (fun O => O.map (Function.Embedding.subtype _))
    (fun O => O.subtype (fun u => u ∈ s)) ?_ ?_ ?_ ?_ ?_
  · intro O hO
    obtain ⟨x, rfl⟩ := mem_cycleOrbits.mp hO
    rw [cycleOrbit_subtypePerm h x, Finset.mem_filter]
    exact ⟨cycleOrbit_mem_cycleOrbits π ↑x,
      cycleOrbit_subset_of_invariant h x.2⟩
  · intro O hO
    rw [Finset.mem_filter] at hO
    obtain ⟨x, rfl⟩ := mem_cycleOrbits.mp hO.1
    have hxs : x ∈ s := hO.2 (self_mem_cycleOrbit π x)
    have hmap : ((cycleOrbit π x).subtype (fun u => u ∈ s)).map
        (Function.Embedding.subtype _) =
        (cycleOrbit (π.subtypePerm h) ⟨x, hxs⟩).map
          (Function.Embedding.subtype _) := by
      rw [Finset.subtype_map_of_mem fun y hy => hO.2 hy,
        cycleOrbit_subtypePerm h]
    rw [Finset.map_injective _ hmap]
    exact cycleOrbit_mem_cycleOrbits _ _
  · intro O _
    ext a
    simp only [Finset.mem_subtype, Finset.mem_map,
      Function.Embedding.coe_subtype]
    exact ⟨fun ⟨b, hb, hba⟩ => (Subtype.ext hba : b = a) ▸ hb,
      fun ha => ⟨a, ha, rfl⟩⟩
  · intro O hO
    rw [Finset.mem_filter] at hO
    exact Finset.subtype_map_of_mem fun y hy => hO.2 hy
  · intro O _
    rw [Finset.card_map]

/-! ### Invariant subsets are unions of orbits -/

/-- A union of orbits is an invariant set. -/
theorem biUnion_invariant [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α}
    {S : Finset (Finset α)} (hS : S ⊆ cycleOrbits π) :
    ∀ x ∈ S.biUnion id, π x ∈ S.biUnion id := by
  intro x hx
  rw [Finset.mem_biUnion] at hx ⊢
  obtain ⟨O, hO, hxO⟩ := hx
  refine ⟨O, hO, ?_⟩
  rw [eq_cycleOrbit_of_mem (hS hO) hxO]
  exact apply_mem_cycleOrbit π x

/-- An invariant set is the union of the orbits it contains. -/
theorem biUnion_filter_subset_eq [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α} {s : Finset α}
    (hs : ∀ x, π x ∈ s ↔ x ∈ s) :
    ((cycleOrbits π).filter (fun O => O ⊆ s)).biUnion id = s := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨O, hO, hxO⟩
    exact (Finset.mem_filter.mp hO).2 hxO
  · intro hx
    exact ⟨cycleOrbit π x, Finset.mem_filter.mpr
      ⟨cycleOrbit_mem_cycleOrbits π x,
        cycleOrbit_subset_of_invariant hs hx⟩,
      self_mem_cycleOrbit π x⟩

/-- The orbits inside a union of orbits are the orbits of the
union. -/
theorem filter_subset_biUnion [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α}
    {S : Finset (Finset α)} (hS : S ⊆ cycleOrbits π) :
    (cycleOrbits π).filter (fun O => O ⊆ S.biUnion id) = S := by
  ext O
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hO, hOsub⟩
    obtain ⟨x, hxO⟩ := nonempty_of_mem_cycleOrbits hO
    have hx := hOsub hxO
    rw [Finset.mem_biUnion] at hx
    obtain ⟨O', hO', hxO'⟩ := hx
    have hOO' : O = O' := by
      rw [eq_cycleOrbit_of_mem hO hxO,
        eq_cycleOrbit_of_mem (hS hO') hxO']
    exact hOO' ▸ hO'
  · intro hO
    exact ⟨hS hO, Finset.subset_biUnion_of_mem id hO⟩

/-- The orbits inside the complement of an invariant set are the
orbits not inside the set. -/
theorem filter_subset_compl_eq_sdiff [Fintype α] [DecidableEq α]
    {π : Equiv.Perm α}
    {s : Finset α} (hs : ∀ x, π x ∈ s ↔ x ∈ s) :
    (cycleOrbits π).filter (fun O => O ⊆ sᶜ) =
      cycleOrbits π \ (cycleOrbits π).filter (fun O => O ⊆ s) := by
  ext O
  rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hO, hOc⟩
    refine ⟨hO, fun hmem => ?_⟩
    obtain ⟨x, hx⟩ := nonempty_of_mem_cycleOrbits hO
    exact absurd (hmem.2 hx) (Finset.mem_compl.mp (hOc hx))
  · rintro ⟨hO, hns⟩
    refine ⟨hO, fun x hx => ?_⟩
    rw [Finset.mem_compl]
    intro hxs
    apply hns
    refine ⟨hO, ?_⟩
    rw [eq_cycleOrbit_of_mem hO hx]
    exact cycleOrbit_subset_of_invariant hs hxs

/-! ### The additive splitting -/

/-- **Additive splitting of the completed cycle product**: at a
pointwise sum of scalar sequences the completed cycle product is
the sum, over all invariant subsets of the carrier, of the product
of the completed cycle products of the restriction to the subset
in the first sequence and of the restriction to the complement in
the second.  Each orbit contributes a binomial factor, and the
expansion enumerates the invariant subsets. -/
theorem cycleFunG_add_split [Fintype α] [DecidableEq α]
    (t t' : ℕ → ℂ) (π : Equiv.Perm α) :
    cycleFunG (fun c => t c + t' c) π =
      ∑ s ∈ Finset.univ.filter
        (fun s : Finset α => ∀ x ∈ s, π x ∈ s),
        cycleFunG t (permRestrict π s) *
          cycleFunG t' (permRestrict π sᶜ) := by
  rw [cycleFunG_eq_prod_cycleOrbits]
  rw [show (∏ O ∈ cycleOrbits π, (fun c => t c + t' c) O.card) =
    ∏ O ∈ cycleOrbits π, (t O.card + t' O.card) from rfl]
  rw [Finset.prod_add]
  refine Finset.sum_nbij' (fun S => S.biUnion id)
    (fun s => (cycleOrbits π).filter (fun O => O ⊆ s))
    ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_powerset] at hS
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, biUnion_invariant hS⟩
  · intro s _
    rw [Finset.mem_powerset]
    exact Finset.filter_subset _ _
  · intro S hS
    rw [Finset.mem_powerset] at hS
    exact filter_subset_biUnion hS
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact biUnion_filter_subset_eq (mem_iff_of_invariant hs.2)
  · intro S hS
    rw [Finset.mem_powerset] at hS
    have hsinv : ∀ x, π x ∈ S.biUnion id ↔ x ∈ S.biUnion id :=
      mem_iff_of_invariant (biUnion_invariant hS)
    have hcinv : ∀ x, π x ∈ (S.biUnion id)ᶜ ↔
        x ∈ (S.biUnion id)ᶜ :=
      mem_iff_of_invariant (invariant_compl (biUnion_invariant hS))
    rw [permRestrict_of_invariant hsinv,
      permRestrict_of_invariant hcinv,
      cycleFunG_subtypePerm hsinv t, cycleFunG_subtypePerm hcinv t',
      filter_subset_biUnion hS,
      filter_subset_compl_eq_sdiff hsinv, filter_subset_biUnion hS]

/-- **Additive splitting of the completed cycle product on
`Fin n`**: the canonical form of the splitting for the shape-level
consumers. -/
theorem cycleFun_add_split {n : ℕ} (t t' : ℕ → ℂ)
    (π : Equiv.Perm (Fin n)) :
    cycleFun (fun c => t c + t' c) π =
      ∑ s ∈ Finset.univ.filter
        (fun s : Finset (Fin n) => ∀ x ∈ s, π x ∈ s),
        cycleFunG t (permRestrict π s) *
          cycleFunG t' (permRestrict π sᶜ) := by
  rw [← cycleFunG_fin, cycleFunG_add_split]
  congr 1
  ext s
  simp only [Finset.mem_filter]

end RS
