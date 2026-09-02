/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import LeanPool.CommonNeighbourConjecture.Saxl.Affine
import LeanPool.CommonNeighbourConjecture.Saxl.PermWreath.Action
import LeanPool.CommonNeighbourConjecture.Saxl.PermWreath.Symmetric

/-!
# Abstract data for counterexamples at every base size

This module contains the explicit binary permutation-module seed, arbitrary
base-array criterion, a quotient-independent finite tuple-colour interface
with canonical quotient realizations, symbolic colour growth, and the affine
exact-base-size successor bridge used by the obstruction construction.

Faithfulness and irreducibility are intentionally absent from
`EveryBaseSeed`: they are used only later to prove primitivity and are not
needed for the obstruction.
-/

namespace SaxlCounterexamples.EveryBase

open scoped BigOperators Pointwise

/-! ## Arbitrary-length base arrays -/

/-- Two tuples lie in the same orbit under the diagonal action of `H`. -/
def SameTupleOrbit (H : Type*) {V : Type*} [Group H] [MulAction H V]
    {n : Nat} (x y : Fin n → V) : Prop :=
  ∃ h : H, ∀ j, h • x j = y j

/-- The tuple rows distinguish every nonidentity element of the top group. -/
def TupleRowsDistinguishing
    (H Q : Type*) {V ι : Type*}
    [Group H] [Group Q] [MulAction H V] [MulAction Q ι]
    {n : Nat} (rows : ι → Fin n → V) : Prop :=
  ∀ q : Q,
    (∀ i, SameTupleOrbit H (rows (q⁻¹ • i)) (rows i)) → q = 1

theorem permWreath_isBaseTuple_iff
    (H Q ι V : Type*)
    [Group H] [Group Q] [MulAction H V] [MulAction Q ι]
    {n : Nat} (rows : Fin n → (ι → V)) :
    Saxl.IsBaseTuple (Saxl.PermWreath H Q ι) (ι → V) rows ↔
      (∀ i, Saxl.IsBaseTuple H V (fun j ↦ rows j i)) ∧
        TupleRowsDistinguishing H Q (fun i j ↦ rows j i) := by
  classical
  constructor
  · intro hbase
    constructor
    · intro i a ha
      let f : ι → H := Function.update (fun _ ↦ 1) i a
      have hfix : ∀ j, Saxl.PermWreath.base H Q ι f • rows j = rows j := by
        intro j
        funext k
        by_cases hki : k = i
        · subst k
          simpa [f] using ha j
        · simp [f, hki]
      have hf_one : Saxl.PermWreath.base H Q ι f = 1 := hbase _ hfix
      simpa [f] using
        congrArg (fun g : Saxl.PermWreath H Q ι ↦ g.left i) hf_one
    · intro q hq
      choose f hf using hq
      let g : Saxl.PermWreath H Q ι := ⟨f, q⟩
      have hfix : ∀ j, g • rows j = rows j := by
        intro j
        funext i
        change f i • rows j (q⁻¹ • i) = rows j i
        exact hf i j
      have hg_one : g = 1 := hbase g hfix
      simpa [g] using
        congrArg (fun k : Saxl.PermWreath H Q ι ↦ k.right) hg_one
  · rintro ⟨hcolumns, hdist⟩ g hfix
    have hright : g.right = 1 := by
      apply hdist g.right
      intro i
      refine ⟨g.left i, fun j ↦ ?_⟩
      simpa only [Saxl.permWreath_smul_apply] using
        congrFun (hfix j) i
    have hleft : g.left = 1 := by
      funext i
      apply hcolumns i (g.left i)
      intro j
      have h := congrFun (hfix j) i
      simpa [hright] using h
    apply Saxl.PermWreath.ext (X := H) (Q := Q) (ι := ι)
    · exact hleft
    · exact hright

/-- A complete finite coding of the `H`-orbits of base tuples. -/
structure TupleColourCode
    (H V : Type*) [Group H] [MulAction H V]
    (n : Nat) (C : Type*) where
  /-- The colour assigned to a tuple. -/
  colour : (Fin n → V) → C
  colour_eq_iff_sameOrbit :
    ∀ {x y : Fin n → V},
      Saxl.IsBaseTuple H V x → Saxl.IsBaseTuple H V y →
        (colour x = colour y ↔ SameTupleOrbit H x y)
  hits : ∀ c : C, ∃ x : Fin n → V,
    Saxl.IsBaseTuple H V x ∧ colour x = c

theorem permWreath_isBaseTuple_iff_colourWord
    (H Q ι V C : Type*)
    [Group H] [Group Q] [MulAction H V] [MulAction Q ι]
    {n : Nat} (code : TupleColourCode H V n C)
    (rows : Fin n → (ι → V)) :
    Saxl.IsBaseTuple (Saxl.PermWreath H Q ι) (ι → V) rows ↔
      (∀ i, Saxl.IsBaseTuple H V (fun j ↦ rows j i)) ∧
        Saxl.WordDistinguishing Q
          (fun i ↦ code.colour (fun j ↦ rows j i)) := by
  rw [permWreath_isBaseTuple_iff]
  constructor
  · rintro ⟨hcolumns, hrows⟩
    refine ⟨hcolumns, ?_⟩
    intro q hq
    apply hrows q
    intro i
    apply (code.colour_eq_iff_sameOrbit
      (hcolumns (q⁻¹ • i)) (hcolumns i)).1
    exact hq i
  · rintro ⟨hcolumns, hword⟩
    refine ⟨hcolumns, ?_⟩
    intro q hq
    apply hword q
    intro i
    apply (code.colour_eq_iff_sameOrbit
      (hcolumns (q⁻¹ • i)) (hcolumns i)).2
    exact hq i

theorem symmetricTop_isBaseTuple_iff_bijective
    (H V C : Type*) [Group H] [MulAction H V] [Finite C]
    {n : Nat} (code : TupleColourCode H V n C)
    (rows : Fin n → (C → V)) :
    Saxl.IsBaseTuple (Saxl.PermWreath H (Equiv.Perm C) C) (C → V) rows ↔
      (∀ i, Saxl.IsBaseTuple H V (fun j ↦ rows j i)) ∧
        Function.Bijective
          (fun i ↦ code.colour (fun j ↦ rows j i)) := by
  rw [permWreath_isBaseTuple_iff_colourWord]
  exact and_congr_right fun _ ↦
    Saxl.symmetricTop_wordDistinguishing_iff_bijective _

/-! ## Explicit binary permutation-module seed interface -/

/-- An odd invariant cycle avoiding a distinguished point. -/
structure AvoidingCycle
    (H Ω : Type*) [Group H] [MulAction H Ω]
    (h : H) (omega0 : Ω) where
  /-- The finite carrier of the cycle. -/
  carrier : Finset Ω
  nonempty : carrier.Nonempty
  avoids : omega0 ∉ carrier
  odd_card : Odd carrier.card
  invariant : ∀ ω, ω ∈ carrier ↔ h • ω ∈ carrier

/-- Exactly the data used by the abstract obstruction. Faithfulness and
irreducibility are deliberately absent because the cycle-sum proof does not
use them. -/
structure EveryBaseSeed where
  /-- The finite coordinate set. -/
  Ω : Type*
  /-- The seed group. -/
  H : Type*
  /-- The seed module. -/
  V : Type*
  [fintypeOmega : Fintype Ω]
  [fintypeH : Fintype H]
  [fintypeV : Fintype V]
  [decidableEqOmega : DecidableEq Ω]
  [groupH : Group H]
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module (ZMod 2) V]
  [actionHOmega : MulAction H Ω]
  [actionHV : DistribMulAction H V]
  /-- The distinguished coordinate. -/
  omega0 : Ω
  /-- The vector vanishing exactly at the distinguished coordinate. -/
  u : V
  odd_card_H : Odd (Nat.card H)
  regular_exists : ∃ v : V, Saxl.IsRegularVector H V v
  /-- The equivariant coordinate map into the binary permutation module. -/
  coord : V →+ (Ω → ZMod 2)
  coord_smul : ∀ (h : H) (v : V) (ω : Ω),
    coord (h • v) ω = coord v (h⁻¹ • ω)
  u_coord : ∀ ω, coord u ω = if ω = omega0 then 0 else 1
  /-- An avoiding cycle for every group element. -/
  avoidingCycle : ∀ h : H, AvoidingCycle H Ω h omega0

attribute [instance] EveryBaseSeed.fintypeOmega
  EveryBaseSeed.fintypeH EveryBaseSeed.fintypeV
  EveryBaseSeed.decidableEqOmega EveryBaseSeed.groupH
  EveryBaseSeed.addCommGroupV EveryBaseSeed.moduleV
  EveryBaseSeed.actionHOmega EveryBaseSeed.actionHV

/-- Sum the binary coordinates of `v` over `L`. -/
def cycleSum (S : EveryBaseSeed) (L : Finset S.Ω) (v : S.V) : ZMod 2 :=
  ∑ ω ∈ L, S.coord v ω

/-- Reindex an avoiding cycle by the action of its group element. -/
def AvoidingCycle.reindexEquiv (S : EveryBaseSeed) (h : S.H) :
    (S.avoidingCycle h).carrier ≃ (S.avoidingCycle h).carrier where
  toFun ω := ⟨h⁻¹ • ω, by
    have hi := (S.avoidingCycle h).invariant (h⁻¹ • (ω : S.Ω))
    apply hi.mpr
    simpa only [smul_inv_smul] using ω.property⟩
  invFun ω := ⟨h • ω, (S.avoidingCycle h).invariant ω |>.mp ω.property⟩
  left_inv ω := by ext; simp
  right_inv ω := by ext; simp

theorem cycleSum_smul (S : EveryBaseSeed) (h : S.H) (v : S.V) :
    cycleSum S (S.avoidingCycle h).carrier (h • v) =
      cycleSum S (S.avoidingCycle h).carrier v := by
  let L := (S.avoidingCycle h).carrier
  calc
    cycleSum S L (h • v) = ∑ ω : L, S.coord (h • v) ω := by
      symm
      exact Finset.sum_coe_sort L (fun ω ↦ S.coord (h • v) ω)
    _ = ∑ ω : L, S.coord v (h⁻¹ • (ω : S.Ω)) := by
      apply Finset.sum_congr rfl
      intro ω _
      exact S.coord_smul h v ω
    _ = ∑ ω : L, S.coord v ω := by
      exact (AvoidingCycle.reindexEquiv S h).sum_comp
        (fun ω : L ↦ S.coord v ω)
    _ = cycleSum S L v := Finset.sum_coe_sort L (fun ω ↦ S.coord v ω)

theorem cycleSum_add_smul (S : EveryBaseSeed) (h : S.H) (v : S.V) :
    cycleSum S (S.avoidingCycle h).carrier (v + h • v) = 0 := by
  rw [cycleSum, map_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [show ∑ ω ∈ (S.avoidingCycle h).carrier, S.coord (h • v) ω =
      cycleSum S (S.avoidingCycle h).carrier (h • v) by rfl,
    cycleSum_smul]
  change cycleSum S (S.avoidingCycle h).carrier v +
    cycleSum S (S.avoidingCycle h).carrier v = 0
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  have hcast : ((2 : Nat) : ZMod 2) = 0 :=
    CharP.cast_eq_zero (ZMod 2) 2
  rw [hcast, zero_smul]

theorem cycleSum_u (S : EveryBaseSeed) (h : S.H) :
    cycleSum S (S.avoidingCycle h).carrier S.u = 1 := by
  let L := (S.avoidingCycle h).carrier
  calc
    cycleSum S L S.u = ∑ _ω ∈ L, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro ω hω
      have hne : ω ≠ S.omega0 := by
        intro hEq
        subst ω
        exact (S.avoidingCycle h).avoids hω
      simp [S.u_coord, hne]
    _ = (L.card : ZMod 2) := by simp
    _ = 1 := by
      rw [← ZMod.natCast_mod L.card 2,
        (Nat.odd_iff.mp (S.avoidingCycle h).odd_card)]
      norm_num

theorem u_ne_add_smul (S : EveryBaseSeed) (h : S.H) (v : S.V) :
    S.u ≠ v + h • v := by
  intro hu
  have := congrArg (cycleSum S (S.avoidingCycle h).carrier) hu
  rw [cycleSum_u, cycleSum_add_smul] at this
  exact one_ne_zero this

/-! ## Finite regular-tuple colours and orbit profiles -/

/-- A complete code for the vector orbits of a group action. -/
structure VectorOrbitCode
    (H V : Type*) [Group H] [MulAction H V] (D : Type*) where
  /-- The colour assigned to a vector. -/
  colour : V → D
  colour_eq_iff_sameOrbit : ∀ x y : V,
    colour x = colour y ↔ ∃ h : H, h • x = y

/-- A finite colour system for the `tail + 1`-tuples used in a generalized
neighbourhood.  `firstColour` is not extra mathematics: its compatibility
field says exactly that it records the ordinary orbit of the first tuple
entry.  Keeping it explicit avoids quotient choice in executable files. -/
structure BaseArrayColours (S : EveryBaseSeed) (tail : Nat) where
  /-- Colours for regular tuples of length `tail + 1`. -/
  C : Type*
  /-- Colours for vector orbits. -/
  D : Type*
  [fintypeC : Fintype C]
  [decidableEqC : DecidableEq C]
  [decidableEqD : DecidableEq D]
  /-- The regular-tuple orbit code. -/
  tupleCode : TupleColourCode S.H S.V (tail + 1) C
  /-- The vector-orbit code. -/
  vectorCode : VectorOrbitCode S.H S.V D
  /-- Project a tuple colour to the colour of its first vector. -/
  firstColour : C → D
  firstColour_compat : ∀ (x : Fin (tail + 1) → S.V),
    Saxl.IsBaseTuple S.H S.V x →
      vectorCode.colour (x 0) = firstColour (tupleCode.colour x)

attribute [instance] BaseArrayColours.fintypeC
  BaseArrayColours.decidableEqC BaseArrayColours.decidableEqD

/-- Concrete finite types of all positive-length regular tuple orbits.  Index
`t` records colours of tuples of length `t + 1`.  Positive indexing is
essential: for a nontrivial group there are no regular zero-tuples, so a total
colour map at length zero cannot exist. -/
structure RegularTupleColourTower (S : EveryBaseSeed) where
  /-- The colour type for each positive tuple length. -/
  C : Nat → Type*
  /-- Finiteness of every colour type. -/
  fintypeC : ∀ n, Fintype (C n)
  /-- The orbit code at each positive tuple length. -/
  code : ∀ n, TupleColourCode S.H S.V (n + 1) (C n)

namespace RegularTupleColourTower

/-- The number of regular-tuple colours at level `n`. -/
def card (T : RegularTupleColourTower S) (n : Nat) : Nat :=
  @Fintype.card (T.C n) (T.fintypeC n)

/-- Choose a base-tuple representative of a colour. -/
noncomputable def representative (T : RegularTupleColourTower S)
    (n : Nat) (c : T.C n) : Fin (n + 1) → S.V :=
  Classical.choose ((T.code n).hits c)

theorem representative_isBase (T : RegularTupleColourTower S)
    (n : Nat) (c : T.C n) :
    Saxl.IsBaseTuple S.H S.V (T.representative n c) :=
  (Classical.choose_spec ((T.code n).hits c)).1

theorem representative_colour (T : RegularTupleColourTower S)
    (n : Nat) (c : T.C n) :
    (T.code n).colour (T.representative n c) = c :=
  (Classical.choose_spec ((T.code n).hits c)).2

theorem colour_nonempty (T : RegularTupleColourTower S)
    (n : Nat) : Nonempty (T.C n) := by
  obtain ⟨v, hv⟩ := S.regular_exists
  let x : Fin (n + 1) → S.V := fun _ ↦ v
  have hx : Saxl.IsBaseTuple S.H S.V x := by
    intro h hfix
    apply hv h
    exact hfix 0
  exact ⟨(T.code n).colour x⟩

/-- Append a vector to a representative and return the resulting colour. -/
noncomputable def appendColour (T : RegularTupleColourTower S) (n : Nat) :
    T.C n × S.V → T.C (n + 1) :=
  fun cv ↦ (T.code (n + 1)).colour
    (Fin.snoc (T.representative n cv.1) cv.2)

theorem appendColour_injective (T : RegularTupleColourTower S) (n : Nat) :
    Function.Injective (T.appendColour n) := by
  rintro ⟨c, v⟩ ⟨d, w⟩ hcolour
  change (T.code (n + 1)).colour
      (Fin.snoc (T.representative n c) v) =
    (T.code (n + 1)).colour
      (Fin.snoc (T.representative n d) w) at hcolour
  have hbaseC : Saxl.IsBaseTuple S.H S.V
      (Fin.snoc (T.representative n c) v) := by
    intro h hfix
    apply T.representative_isBase n c h
    intro j
    simpa using hfix j.castSucc
  have hbaseD : Saxl.IsBaseTuple S.H S.V
      (Fin.snoc (T.representative n d) w) := by
    intro h hfix
    apply T.representative_isBase n d h
    intro j
    simpa using hfix j.castSucc
  obtain ⟨h, horbit⟩ :=
    ((T.code (n + 1)).colour_eq_iff_sameOrbit hbaseC hbaseD).1 hcolour
  have hcd : c = d := by
    rw [← T.representative_colour n c, ← T.representative_colour n d]
    apply ((T.code n).colour_eq_iff_sameOrbit
      (T.representative_isBase n c) (T.representative_isBase n d)).2
    exact ⟨h, fun j ↦ by simpa using horbit j.castSucc⟩
  subst d
  have hone : h = 1 := by
    apply T.representative_isBase n c h
    intro j
    simpa using horbit j.castSucc
  have hvw : v = w := by
    have := horbit (Fin.last (n + 1))
    simpa [hone] using this
  subst w
  rfl

theorem card_mul_le_next (T : RegularTupleColourTower S) (n : Nat) :
    T.card n * Fintype.card S.V ≤ T.card (n + 1) := by
  let := T.fintypeC n
  let := T.fintypeC (n + 1)
  simpa [card] using Fintype.card_le_of_injective (T.appendColour n)
    (T.appendColour_injective n)

theorem card_lt_next [Nontrivial S.V]
    (T : RegularTupleColourTower S) (n : Nat) :
    T.card n < T.card (n + 1) := by
  let := T.fintypeC n
  let := T.fintypeC (n + 1)
  let : Nonempty (T.C n) := T.colour_nonempty n
  have hpos : 0 < Fintype.card (T.C n) := Fintype.card_pos
  have hV : 1 < Fintype.card S.V := Fintype.one_lt_card
  have hmul : Fintype.card (T.C n) <
      Fintype.card (T.C n) * Fintype.card S.V := by
    exact lt_mul_of_one_lt_right hpos hV
  exact hmul.trans_le (T.card_mul_le_next n)

theorem card_strictMono [Nontrivial S.V]
    (T : RegularTupleColourTower S) :
    StrictMono T.card := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact T.card_lt_next n

theorem card_lt_of_lt [Nontrivial S.V]
    (T : RegularTupleColourTower S) {m n : Nat} (hmn : m < n) :
    T.card m < T.card n :=
  T.card_strictMono hmn

/-- The permutation-wreath group associated to level `n`. -/
abbrev LinearGroup (T : RegularTupleColourTower S) (n : Nat) :=
  Saxl.PermWreath S.H (Equiv.Perm (T.C n)) (T.C n)

/-- The product module associated to level `n`. -/
abbrev LinearSpace (T : RegularTupleColourTower S) (n : Nat) :=
  T.C n → S.V

/-- The canonical base rows formed from all chosen representatives. -/
noncomputable def baseRows (T : RegularTupleColourTower S) (n : Nat) :
    Fin (n + 1) → T.LinearSpace n :=
  fun j c ↦ T.representative n c j

theorem baseRows_isBase (T : RegularTupleColourTower S) (n : Nat) :
    Saxl.IsBaseTuple (T.LinearGroup n) (T.LinearSpace n) (T.baseRows n) := by
  let := T.fintypeC n
  apply (symmetricTop_isBaseTuple_iff_bijective
    S.H S.V (T.C n) (T.code n) (T.baseRows n)).2
  constructor
  · exact T.representative_isBase n
  · have hword : (fun c ↦ (T.code n).colour
        (fun j ↦ T.baseRows n j c)) = id := by
      funext c
      exact T.representative_colour n c
    rw [hword]
    exact Function.bijective_id

theorem no_baseTuple_of_card_lt (T : RegularTupleColourTower S)
    {m n : Nat} (hcard : T.card m < T.card n) :
    ¬ ∃ rows : Fin (m + 1) → T.LinearSpace n,
      Saxl.IsBaseTuple (T.LinearGroup n) (T.LinearSpace n) rows := by
  let := T.fintypeC m
  let := T.fintypeC n
  rintro ⟨rows, hbase⟩
  have hword : Function.Injective
      (fun c ↦ (T.code m).colour (fun j ↦ rows j c)) := by
    rw [← Saxl.symmetricTop_wordDistinguishing_iff_injective]
    exact (permWreath_isBaseTuple_iff_colourWord
      S.H (Equiv.Perm (T.C n)) (T.C n) S.V (T.C m)
      (T.code m) rows).1 hbase |>.2
  exact Fintype.not_injective_of_card_lt _ hcard hword

end RegularTupleColourTower

/-! ## Canonical finite quotient colours

These constructions show that the positive-length colour-tower interface is
inhabited for every finite seed.  Nonbase tuples receive the colour of a fixed
constant regular tuple; on base tuples the colour is the actual diagonal
orbit quotient. -/

/-- A regular tuple of positive length `n + 1`. -/
abbrev RegularTuple (S : EveryBaseSeed) (n : Nat) :=
  {x : Fin (n + 1) → S.V // Saxl.IsBaseTuple S.H S.V x}

noncomputable instance regularTupleFintype (S : EveryBaseSeed) (n : Nat) :
    Fintype (RegularTuple S n) := by
  classical
  unfold RegularTuple
  infer_instance

/-- Orbit equivalence on regular tuples. -/
def regularTupleSetoid (S : EveryBaseSeed) (n : Nat) :
    Setoid (RegularTuple S n) where
  r x y := SameTupleOrbit S.H x.1 y.1
  iseqv := {
    refl := fun x ↦ ⟨1, fun j ↦ one_smul S.H (x.1 j)⟩
    symm := by
      rintro x y ⟨h, hh⟩
      refine ⟨h⁻¹, fun j ↦ ?_⟩
      rw [← hh j]
      exact inv_smul_smul h (x.1 j)
    trans := by
      rintro x y z ⟨h, hh⟩ ⟨k, hk⟩
      refine ⟨k * h, fun j ↦ ?_⟩
      rw [mul_smul, hh j, hk j] }

instance regularTupleSetoidInstance (S : EveryBaseSeed) (n : Nat) :
    Setoid (RegularTuple S n) := regularTupleSetoid S n

/-- The quotient colour type of regular tuples under the diagonal action. -/
abbrev RegularTupleColour (S : EveryBaseSeed) (n : Nat) :=
  Quotient (regularTupleSetoid S n)

noncomputable instance regularTupleRelDecidable
    (S : EveryBaseSeed) (n : Nat) :
    DecidableRel ((· ≈ ·) : RegularTuple S n → RegularTuple S n → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

noncomputable instance regularTupleColourFintype
    (S : EveryBaseSeed) (n : Nat) : Fintype (RegularTupleColour S n) :=
  inferInstance

noncomputable instance regularTupleColourDecidableEq
    (S : EveryBaseSeed) (n : Nat) : DecidableEq (RegularTupleColour S n) :=
  Classical.typeDecidableEq _

/-- A default constant regular tuple, used to colour nonbase tuples. -/
noncomputable def defaultRegularTuple (S : EveryBaseSeed) (n : Nat) :
    RegularTuple S n := by
  let v := Classical.choose S.regular_exists
  have hv : Saxl.IsRegularVector S.H S.V v :=
    Classical.choose_spec S.regular_exists
  refine ⟨fun _ ↦ v, ?_⟩
  intro h hfix
  apply hv h
  exact hfix 0

/-- Colour a tuple by its orbit, using the default colour when it is not a base. -/
noncomputable def regularTupleColour (S : EveryBaseSeed) (n : Nat)
    (x : Fin (n + 1) → S.V) : RegularTupleColour S n := by
  classical
  exact if hx : Saxl.IsBaseTuple S.H S.V x then
    Quotient.mk (regularTupleSetoid S n) (⟨x, hx⟩ : RegularTuple S n)
  else Quotient.mk (regularTupleSetoid S n) (defaultRegularTuple S n)

theorem regularTupleColour_eq_iff_sameOrbit (S : EveryBaseSeed) (n : Nat)
    {x y : Fin (n + 1) → S.V}
    (hx : Saxl.IsBaseTuple S.H S.V x)
    (hy : Saxl.IsBaseTuple S.H S.V y) :
    regularTupleColour S n x = regularTupleColour S n y ↔
      SameTupleOrbit S.H x y := by
  simp only [regularTupleColour, dite_eq_left hx, dite_eq_left hy]
  exact Quotient.eq

theorem regularTupleColour_hits (S : EveryBaseSeed) (n : Nat)
    (c : RegularTupleColour S n) :
    ∃ x : Fin (n + 1) → S.V,
      Saxl.IsBaseTuple S.H S.V x ∧ regularTupleColour S n x = c := by
  refine Quotient.inductionOn c ?_
  intro x
  refine ⟨x.1, x.2, ?_⟩
  rw [regularTupleColour]
  simp only [dite_eq_left x.2]

/-- The canonical orbit code for regular tuples of length `n + 1`. -/
noncomputable def regularTupleCode (S : EveryBaseSeed) (n : Nat) :
    TupleColourCode S.H S.V (n + 1) (RegularTupleColour S n) where
  colour := regularTupleColour S n
  colour_eq_iff_sameOrbit := regularTupleColour_eq_iff_sameOrbit S n
  hits := regularTupleColour_hits S n

/-- The canonical, genuinely inhabited positive regular-colour tower. -/
noncomputable def quotientRegularTupleColourTower (S : EveryBaseSeed) :
    RegularTupleColourTower S where
  C n := RegularTupleColour S n
  fintypeC n := regularTupleColourFintype S n
  code n := regularTupleCode S n

/-- Orbit equivalence on vectors in the seed module. -/
def vectorOrbitSetoid (S : EveryBaseSeed) : Setoid S.V where
  r x y := ∃ h : S.H, h • x = y
  iseqv := {
    refl := fun x ↦ ⟨1, one_smul S.H x⟩
    symm := by
      rintro x y ⟨h, hh⟩
      refine ⟨h⁻¹, ?_⟩
      rw [← hh]
      exact inv_smul_smul h x
    trans := by
      rintro x y z ⟨h, hh⟩ ⟨k, hk⟩
      refine ⟨k * h, ?_⟩
      rw [mul_smul, hh, hk] }

instance vectorOrbitSetoidInstance (S : EveryBaseSeed) : Setoid S.V :=
  vectorOrbitSetoid S

/-- The quotient colour type of vector orbits. -/
abbrev VectorOrbitColour (S : EveryBaseSeed) :=
  Quotient (vectorOrbitSetoid S)

noncomputable instance vectorOrbitRelDecidable (S : EveryBaseSeed) :
    DecidableRel ((· ≈ ·) : S.V → S.V → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

noncomputable instance vectorOrbitColourFintype (S : EveryBaseSeed) :
    Fintype (VectorOrbitColour S) := inferInstance

noncomputable instance vectorOrbitColourDecidableEq (S : EveryBaseSeed) :
    DecidableEq (VectorOrbitColour S) := Classical.typeDecidableEq _

/-- The canonical quotient code for vector orbits. -/
noncomputable def quotientVectorOrbitCode (S : EveryBaseSeed) :
    VectorOrbitCode S.H S.V (VectorOrbitColour S) where
  colour := Quotient.mk (vectorOrbitSetoid S)
  colour_eq_iff_sameOrbit _ _ := Quotient.eq

/-- Project a regular-tuple colour to the orbit colour of its first vector. -/
noncomputable def firstVectorOrbitColour (S : EveryBaseSeed) (tail : Nat) :
    RegularTupleColour S tail → VectorOrbitColour S :=
  Quotient.lift
    (fun x : RegularTuple S tail ↦
      Quotient.mk (vectorOrbitSetoid S) (x.1 0 : S.V))
    (by
      intro x y hxy
      apply Quotient.sound
      obtain ⟨h, hh⟩ := hxy
      exact ⟨h, hh 0⟩)

theorem firstVectorOrbitColour_regularTupleColour
    (S : EveryBaseSeed) (tail : Nat)
    (x : Fin (tail + 1) → S.V)
    (hx : Saxl.IsBaseTuple S.H S.V x) :
    firstVectorOrbitColour S tail (regularTupleColour S tail x) =
      Quotient.mk (vectorOrbitSetoid S) (x 0) := by
  rw [regularTupleColour]
  rw [dite_eq_left hx]
  unfold firstVectorOrbitColour
  exact Quotient.lift_mk _ _ _

/-- Canonical finite tuple/vector orbit colours used by the profile argument. -/
noncomputable def quotientBaseArrayColours (S : EveryBaseSeed) (tail : Nat) :
    BaseArrayColours S tail where
  C := RegularTupleColour S tail
  D := VectorOrbitColour S
  fintypeC := regularTupleColourFintype S tail
  decidableEqC := regularTupleColourDecidableEq S tail
  decidableEqD := vectorOrbitColourDecidableEq S
  tupleCode := regularTupleCode S tail
  vectorCode := quotientVectorOrbitCode S
  firstColour := firstVectorOrbitColour S tail
  firstColour_compat := by
    intro x hx
    exact (firstVectorOrbitColour_regularTupleColour S tail x hx).symm

/-! ## Exact tuple size and the affine successor bridge -/

/-- A technically convenient strengthening of `Saxl.ExactBaseSize`: smaller
ordered tuples are excluded even before imposing injectivity. -/
def ExactTupleBaseSize
    (G X : Type*) [Group G] [MulAction G X] (n : Nat) : Prop :=
  (∃ x : Fin n → X, Saxl.IsBaseTuple G X x) ∧
    ∀ m < n, ¬ ∃ x : Fin m → X, Saxl.IsBaseTuple G X x

theorem isBaseTuple_injective_of_no_predecessor
    {G X : Type*} [Group G] [MulAction G X]
    {n : Nat} (x : Fin (n + 1) → X)
    (hbase : Saxl.IsBaseTuple G X x)
    (hprev : ¬ ∃ y : Fin n → X, Saxl.IsBaseTuple G X y) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  obtain ⟨i', hi'⟩ :=
    (Fin.eq_self_or_eq_succAbove j i).resolve_left hne
  apply hprev
  refine ⟨fun k ↦ x (j.succAbove k), ?_⟩
  intro g hg
  apply hbase g
  intro k
  cases k using Fin.succAboveCases j with
  | x =>
      have hji : x j = x (j.succAbove i') := by
        rw [← hi']
        exact hij.symm
      calc
        g • x j = g • x (j.succAbove i') := congrArg (g • ·) hji
        _ = x (j.succAbove i') := hg i'
        _ = x j := hji.symm
  | p k => exact hg k

theorem exactBaseSize_of_exactTupleBaseSize
    {G X : Type*} [Group G] [MulAction G X] {n : Nat}
    (h : ExactTupleBaseSize G X n) : Saxl.ExactBaseSize G X n := by
  constructor
  · obtain ⟨x, hx⟩ := h.1
    refine ⟨x, ?_, hx⟩
    cases n with
    | zero => exact fun i ↦ Fin.elim0 i
    | succ n =>
        exact isBaseTuple_injective_of_no_predecessor x hx
          (h.2 n (Nat.lt_succ_self n))
  · intro m hm hset
    exact h.2 m hm ⟨hset.choose, hset.choose_spec.2⟩

theorem RegularTupleColourTower.linear_exactTupleBaseSize
    [Nontrivial S.H]
    (T : RegularTupleColourTower S) (n : Nat)
    (hcard : ∀ m < n, T.card m < T.card n) :
    ExactTupleBaseSize (T.LinearGroup n) (T.LinearSpace n) (n + 1) := by
  constructor
  · exact ⟨T.baseRows n, T.baseRows_isBase n⟩
  · intro m hm
    cases m with
    | zero =>
        rintro ⟨rows, hbase⟩
        obtain ⟨h, hh⟩ := exists_ne (1 : S.H)
        let g : T.LinearGroup n := Saxl.PermWreath.base S.H
          (Equiv.Perm (T.C n)) (T.C n) (fun _ ↦ h)
        have hg : g = 1 := hbase g (fun i ↦ Fin.elim0 i)
        apply hh
        have hleft := congrArg
          (fun k : T.LinearGroup n ↦ k.left (Classical.choice (T.colour_nonempty n)))
          hg
        simpa [g] using hleft
    | succ m =>
        have hmn : m < n := by omega
        exact T.no_baseTuple_of_card_lt (hcard m hmn)

theorem RegularTupleColourTower.linear_exactTupleBaseSize_of_seed
    [Nontrivial S.H] [Nontrivial S.V]
    (T : RegularTupleColourTower S) (n : Nat) :
    ExactTupleBaseSize (T.LinearGroup n) (T.LinearSpace n) (n + 1) :=
  T.linear_exactTupleBaseSize n (fun _m _hm ↦ T.card_lt_of_lt _hm)

theorem affine_exactTupleBaseSize_succ
    (H V : Type*) [Group H] [AddCommGroup V] [DistribMulAction H V]
    {n : Nat} (hn : 0 < n) (h : ExactTupleBaseSize H V n) :
    ExactTupleBaseSize (Saxl.AffineGroup H V) V (n + 1) := by
  constructor
  · obtain ⟨x, hx⟩ := h.1
    refine ⟨Fin.cons 0 x, ?_⟩
    exact (Saxl.affine_isBaseTuple_cons_iff H V 0 x).2 (by simpa using hx)
  · intro m hm
    cases m with
    | zero =>
        rintro ⟨x, hx⟩
        apply h.2 0 hn
        refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
        intro a _
        let g : Saxl.AffineGroup H V :=
          ⟨Multiplicative.ofAdd 0, a⟩
        have hg : g = 1 := hx g (fun i ↦ Fin.elim0 i)
        simpa [g] using congrArg SemidirectProduct.right hg
    | succ m =>
        rintro ⟨x, hx⟩
        let first : V := x 0
        let rest : Fin m → V := fun i ↦ x i.succ
        have hxcons : Fin.cons first rest = x := by
          funext i
          cases i using Fin.cases <;> rfl
        have hlinear : Saxl.IsBaseTuple H V (fun i ↦ rest i - first) :=
          (Saxl.affine_isBaseTuple_cons_iff H V first rest).1
            (by simpa [hxcons] using hx)
        apply h.2 m (Nat.lt_of_succ_lt_succ hm)
        exact ⟨_, hlinear⟩

theorem affine_exactBaseSize_succ
    (H V : Type*) [Group H] [AddCommGroup V] [DistribMulAction H V]
    {n : Nat} (hn : 0 < n) (h : ExactTupleBaseSize H V n) :
    Saxl.ExactBaseSize (Saxl.AffineGroup H V) V (n + 1) :=
  exactBaseSize_of_exactTupleBaseSize
    (affine_exactTupleBaseSize_succ H V hn h)
end SaxlCounterexamples.EveryBase
