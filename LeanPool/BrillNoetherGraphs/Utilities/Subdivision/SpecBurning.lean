/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gonality.BurnedSet
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
import Mathlib.Tactic

/-!
# Burning along a subdivided slot

The burned-set layer of `Utilities/Gonality/BurnedSet.lean` is stated for an
arbitrary `CFGraph`.  On a subdivision the fire propagates along slots, and the
moves used over and over by van Dobben de Bruyn–Smit–van der Wegen's §3 are:

* **chip-free stretches burn** (`mem_burned_slotVertex_of_chipFree_up` and its
  downward twin) — from a burned position the fire runs to the end of a
  chip-free stretch of the slot;
* **a burned/unburned split costs a chip** (`exists_chip_up`, `exists_chip_down`)
  — the first unburned vertex past the fire front is adjacent to a burned one,
  so it can afford that edge, so it carries a chip;
* **cycle blocking** (`two_le_chips_of_cycle`) — two distinct slots with the
  same endpoints form a cycle; if one endpoint burns and the other does not, the
  cycle carries at least two chips.

The cycle lemma is stated via **two internally disjoint arcs** rather than via
distinct interior vertices, which is what makes it cover the *banana* case (both
slots of length one, so the cycle has only two vertices).  There the two
witnesses coincide at the unburned endpoint, whose two edges to the burned
endpoint are parallel, and the edge *multiplicity* supplies the second chip
(`two_le_num_edges_of_parallel_unit`).  Getting this case right is what makes
the minimal tricycle `T_m` itself tractable, not merely its simple refinements.

## Numerical slot positions

`spec.slotVertex e k` is the vertex at position `k` along slot `e`, clamped to
the slot so that no proof obligation rides along.  Position `0` is the core
tail, position `spec.length e` the core head, and the positions strictly
between are the slot interior.  Statements carry explicit
`k ≤ spec.length e` hypotheses wherever clamping would otherwise silently
change the meaning.
-/

namespace Utilities.Gonality

open Finset

variable {G : CFGraph} {D : CFDiv G}

/-- Two distinct chipped vertices of a set carry at least two chips between
them, when the divisor is effective elsewhere. -/
theorem two_le_sum_of_two_chips (hEff : effective D) {S : Finset G.V}
    {x y : G.V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hx1 : 1 ≤ D x) (hy1 : 1 ≤ D y) : 2 ≤ ∑ v ∈ S, D v := by
  classical
  have hsub : ({x, y} : Finset G.V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hle : ∑ v ∈ ({x, y} : Finset G.V), D v ≤ ∑ v ∈ S, D v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => hEff v
  rw [Finset.sum_pair hxy] at hle
  omega

/-- One doubly chipped vertex of a set does as well. -/
theorem two_le_sum_of_double_chip (hEff : effective D) {S : Finset G.V} {x : G.V}
    (hx : x ∈ S) (hx2 : 2 ≤ D x) : 2 ≤ ∑ v ∈ S, D v := by
  classical
  have hsub : ({x} : Finset G.V) ⊆ S := by simpa using hx
  have hle : ∑ v ∈ ({x} : Finset G.V), D v ≤ ∑ v ∈ S, D v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => hEff v
  rw [Finset.sum_singleton] at hle
  omega

/-- Two distinct burned neighbours of an unburned vertex cost it two chips. -/
theorem two_le_of_two_burned_neighbours {q : G.V} {x u₁ u₂ : G.V}
    (hx : x ∉ burned G D q) (h1 : u₁ ∈ burned G D q) (h2 : u₂ ∈ burned G D q)
    (hne : u₁ ≠ u₂) (hp1 : 0 < numEdges G x u₁) (hp2 : 0 < numEdges G x u₂) :
    2 ≤ D x := by
  classical
  have hle := sum_burned_le_of_not_mem_burned hx
  have hsub : ({u₁, u₂} : Finset G.V) ⊆ burned G D q := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hpair : ∑ v ∈ ({u₁, u₂} : Finset G.V), (numEdges G x v : ℤ)
      ≤ ∑ v ∈ burned G D q, (numEdges G x v : ℤ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Int.natCast_nonneg _
  rw [Finset.sum_pair hne] at hpair
  omega

/-- A doubled edge to the fire costs an unburned vertex two chips. -/
theorem two_le_of_double_burned_edge {q : G.V} {x u : G.V}
    (hx : x ∉ burned G D q) (hu : u ∈ burned G D q) (hp : 2 ≤ numEdges G x u) :
    2 ≤ D x := by
  classical
  have hle := sum_burned_le_of_not_mem_burned hx
  have hsub : ({u} : Finset G.V) ⊆ burned G D q := by simpa using hu
  have hpair : ∑ v ∈ ({u} : Finset G.V), (numEdges G x v : ℤ)
      ≤ ∑ v ∈ burned G D q, (numEdges G x v : ℤ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Int.natCast_nonneg _
  rw [Finset.sum_singleton] at hpair
  omega

/-- One burned neighbour costs an unburned vertex a chip. -/
theorem one_le_of_burned_neighbour {q : G.V} {x u : G.V}
    (hx : x ∉ burned G D q) (hu : u ∈ burned G D q) (hp : 0 < numEdges G x u) :
    1 ≤ D x := by
  classical
  have hle := sum_burned_le_of_not_mem_burned hx
  have hsub : ({u} : Finset G.V) ⊆ burned G D q := by simpa using hu
  have hpair : ∑ v ∈ ({u} : Finset G.V), (numEdges G x v : ℤ)
      ≤ ∑ v ∈ burned G D q, (numEdges G x v : ℤ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Int.natCast_nonneg _
  rw [Finset.sum_singleton] at hpair
  omega

end Utilities.Gonality

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset

open Utilities.Gonality

variable {n p : ℕ} (spec : Spec n p)

/-! ## Numerical positions along a slot -/

/-- The vertex at numerical position `k` along slot `e`, clamped to the slot. -/
def slotVertex (edge : Fin p) (k : ℕ) : spec.Vertex :=
  spec.pathVertex edge ⟨min k (spec.length edge), by
    have := Nat.min_le_right k (spec.length edge); omega⟩

/-- The vertices of the closed subdivided slot `edge`. -/
def slotClosed (edge : Fin p) : Finset spec.Vertex :=
  (Finset.range (spec.length edge + 1)).image (spec.slotVertex edge)

variable {spec}

theorem slotVertex_of_le {edge : Fin p} {k : ℕ} (hk : k ≤ spec.length edge) :
    spec.slotVertex edge k = spec.pathVertex edge ⟨k, by omega⟩ := by
  unfold slotVertex
  congr 1
  exact Fin.ext (Nat.min_eq_left hk)

@[simp] theorem slotVertex_zero (edge : Fin p) :
    spec.slotVertex edge 0 = spec.coreVertex (spec.core.tail edge) := by
  rw [slotVertex_of_le (Nat.zero_le _)]
  exact spec.pathVertex_zero edge

@[simp] theorem slotVertex_length (edge : Fin p) :
    spec.slotVertex edge (spec.length edge) =
      spec.coreVertex (spec.core.head edge) := by
  rw [slotVertex_of_le (le_refl _)]
  exact spec.pathVertex_length edge

theorem mem_slotClosed {edge : Fin p} {k : ℕ} (hk : k ≤ spec.length edge) :
    spec.slotVertex edge k ∈ spec.slotClosed edge := by
  refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
  simp only [Finset.mem_range]
  omega

/-- Interior positions name interior vertices, hence remember their slot. -/
theorem slotVertex_eq_interiorVertex {edge : Fin p} {k : ℕ} (hk : 0 < k)
    (hk' : k < spec.length edge) :
    spec.slotVertex edge k = spec.interiorVertex edge ⟨k - 1, by omega⟩ := by
  rw [slotVertex_of_le (le_of_lt hk')]
  unfold pathVertex
  rw [dif_neg (by simpa using hk.ne'), dif_neg (by simpa using hk'.ne)]

theorem slotVertex_ne_coreVertex {edge : Fin p} {k : ℕ} (hk : 0 < k)
    (hk' : k < spec.length edge) (v : Fin n) :
    spec.slotVertex edge k ≠ spec.coreVertex v := by
  rw [slotVertex_eq_interiorVertex hk hk']
  simp [interiorVertex, coreVertex]

/-- Interior positions in distinct slots are distinct vertices. -/
theorem slotVertex_ne_of_slot_ne {e e' : Fin p} (hee : e ≠ e') {k k' : ℕ}
    (hk : 0 < k) (hk' : k < spec.length e)
    (hl : 0 < k') (hl' : k' < spec.length e') :
    spec.slotVertex e k ≠ spec.slotVertex e' k' := by
  rw [slotVertex_eq_interiorVertex hk hk', slotVertex_eq_interiorVertex hl hl']
  simp only [interiorVertex, ne_eq, Sum.inr.injEq]
  intro hEq
  exact hee (congrArg Sigma.fst hEq)

/-- Distinct positions in one slot are distinct vertices. -/
theorem slotVertex_injOn {edge : Fin p} {k k' : ℕ} (hk : k ≤ spec.length edge)
    (hk' : k' ≤ spec.length edge)
    (h : spec.slotVertex edge k = spec.slotVertex edge k') : k = k' := by
  rw [slotVertex_of_le hk, slotVertex_of_le hk'] at h
  simpa using congrArg Fin.val (spec.pathVertex_injective edge h)

/-- Consecutive positions along a slot are adjacent. -/
theorem slotVertex_num_edges_pos {edge : Fin p} {k : ℕ}
    (hk : k < spec.length edge) :
    0 < numEdges spec.graph (spec.slotVertex edge k)
      (spec.slotVertex edge (k + 1)) := by
  have h := spec.consecutive_num_edges_pos edge ⟨k, hk⟩
  rwa [show spec.pathVertex edge (spec.stepLeftPosition edge ⟨k, hk⟩)
        = spec.slotVertex edge k from by
      rw [slotVertex_of_le (le_of_lt hk)]; rfl,
    show spec.pathVertex edge (spec.stepRightPosition edge ⟨k, hk⟩)
        = spec.slotVertex edge (k + 1) from by
      rw [slotVertex_of_le (by omega : k + 1 ≤ spec.length edge)]; rfl] at h

theorem slotVertex_num_edges_pos' {edge : Fin p} {k : ℕ}
    (hk : k < spec.length edge) :
    0 < numEdges spec.graph (spec.slotVertex edge (k + 1))
      (spec.slotVertex edge k) := by
  rw [num_edges_symmetric]
  exact slotVertex_num_edges_pos hk

/-- **Parallel unit slots double an edge multiplicity.**  This is the ingredient
that makes the banana case of `two_le_chips_of_cycle` work. -/
theorem two_le_num_edges_of_parallel_unit {e₁ e₂ : Fin p} (hne : e₁ ≠ e₂)
    (h1 : spec.length e₁ = 1) (h2 : spec.length e₂ = 1)
    (htail : spec.core.tail e₂ = spec.core.tail e₁)
    (hhead : spec.core.head e₂ = spec.core.head e₁) :
    2 ≤ numEdges spec.graph (spec.coreVertex (spec.core.head e₁))
      (spec.coreVertex (spec.core.tail e₁)) := by
  classical
  rw [spec.num_edges_eq_card_filter_steps]
  have hstep : ∀ e : Fin p, spec.length e = 1 →
      spec.unitEdge ⟨e, ⟨0, spec.length_pos e⟩⟩ =
        (spec.coreVertex (spec.core.tail e), spec.coreVertex (spec.core.head e)) := by
    intro e he
    unfold unitEdge
    refine Prod.ext ?_ ?_
    · exact spec.stepLeft_zero e
    · have := spec.stepRight_last e
      rw [show (⟨0, by omega⟩ : Fin (spec.length e))
          = ⟨spec.length e - 1, by omega⟩ from Fin.ext (by omega)]
      exact this
  have hmem : ∀ e : Fin p, spec.length e = 1 →
      spec.core.tail e = spec.core.tail e₁ → spec.core.head e = spec.core.head e₁ →
      (⟨e, ⟨0, spec.length_pos e⟩⟩ : spec.Step) ∈
        Finset.univ.filter (fun step : spec.Step =>
          spec.unitEdge step = (spec.coreVertex (spec.core.head e₁),
            spec.coreVertex (spec.core.tail e₁)) ∨
          spec.unitEdge step = (spec.coreVertex (spec.core.tail e₁),
            spec.coreVertex (spec.core.head e₁))) := by
    intro e he ht hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    right
    rw [hstep e he, ht, hh]
  refine Finset.one_lt_card.mpr ⟨_, hmem e₁ h1 rfl rfl, _, hmem e₂ h2 htail hhead, ?_⟩
  intro hEq
  exact hne (congrArg Sigma.fst hEq)

/-! ## Chips, counted slot by slot

Every chip count in the tricycle argument is a linear combination of the `n`
core-vertex values and the `p` slot-interior totals, so the bookkeeping of
Lemma 3.6 never needs a `Finset` union.  This is the mitigation of blueprint
risk R1, one step further than the blueprint's own suggestion: not merely a
disjoint partition, but a *coordinate system*. -/

/-- The chips on the interior of slot `edge`. -/
def slotInteriorChips (sp : Spec n p) (D : CFDiv sp.graph) (edge : Fin p) : ℤ :=
  ∑ j : Fin (sp.length edge - 1), D (sp.interiorVertex edge j)

theorem slotInteriorChips_nonneg {D : CFDiv spec.graph} (hEff : effective D)
    (edge : Fin p) : 0 ≤ spec.slotInteriorChips D edge :=
  Finset.sum_nonneg fun _ _ => hEff _

/-- **The coordinate system.**  Total degree splits as the core-vertex values
plus the slot-interior totals. -/
theorem deg_eq_core_add_slotInteriorChips (D : CFDiv spec.graph) :
    deg D = (∑ v : Fin n, D (spec.coreVertex v))
      + ∑ edge : Fin p, spec.slotInteriorChips D edge := by
  have hdeg : deg D = ∑ x : spec.graph.V, D x := rfl
  rw [hdeg, Fintype.sum_sum_type]
  congr 1
  rw [show (∑ x : spec.Interior, D (Sum.inr x))
      = ∑ x ∈ (Finset.univ.sigma (fun _ : Fin p => (Finset.univ : Finset _))),
          D (Sum.inr x) from by
    congr 1]
  rw [Finset.sum_sigma]
  rfl

/-- A chip at an interior position is one of the slot's interior chips. -/
theorem apply_slotVertex_le_slotInteriorChips {D : CFDiv spec.graph}
    (hEff : effective D) {edge : Fin p} {k : ℕ} (hk : 0 < k)
    (hk' : k < spec.length edge) :
    D (spec.slotVertex edge k) ≤ spec.slotInteriorChips D edge := by
  rw [slotVertex_eq_interiorVertex hk hk']
  exact Finset.single_le_sum (f := fun j => D (spec.interiorVertex edge j))
    (fun j _ => hEff _) (Finset.mem_univ (⟨k - 1, by omega⟩ : Fin (spec.length edge - 1)))

/-! ## Chip-free stretches burn -/

variable {D : CFDiv spec.graph} {w : spec.Vertex}

/-- **The fire runs up a chip-free stretch of a slot.** -/
theorem mem_burned_slotVertex_of_chipFree_up {edge : Fin p} {a b : ℕ}
    (ha : spec.slotVertex edge a ∈ burned spec.graph D w) (hab : a ≤ b)
    (hb : b ≤ spec.length edge)
    (hfree : ∀ k, a < k → k ≤ b → D (spec.slotVertex edge k) ≤ 0) :
    spec.slotVertex edge b ∈ burned spec.graph D w := by
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp hab
    subst this
    exact ha
  | succ m ih =>
    rcases Nat.lt_or_ge a (m + 1) with hlt | hge
    · have hma : a ≤ m := by omega
      have hprev : spec.slotVertex edge m ∈ burned spec.graph D w :=
        ih hma (by omega) (fun k hk1 hk2 => hfree k hk1 (by omega))
      refine mem_burned_of_mem_burned_adj hprev ?_
      have hpos := slotVertex_num_edges_pos' (spec := spec) (edge := edge)
        (k := m) (by omega)
      have := hfree (m + 1) (by omega) (le_refl _)
      omega
    · have : a = m + 1 := by omega
      subst this
      exact ha

/-- **The fire runs down a chip-free stretch of a slot.** -/
theorem mem_burned_slotVertex_of_chipFree_down {edge : Fin p} {a b : ℕ}
    (ha : spec.slotVertex edge a ∈ burned spec.graph D w) (hba : b ≤ a)
    (ha' : a ≤ spec.length edge)
    (hfree : ∀ k, b ≤ k → k < a → D (spec.slotVertex edge k) ≤ 0) :
    spec.slotVertex edge b ∈ burned spec.graph D w := by
  obtain ⟨d, hd⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
  clear hba
  induction d generalizing b with
  | zero =>
    subst hd
    simpa using ha
  | succ m ih =>
    have hb1 : spec.slotVertex edge (b + 1) ∈ burned spec.graph D w :=
      ih (b := b + 1) (fun k hk1 hk2 => hfree k (by omega) hk2) (by omega)
    refine mem_burned_of_mem_burned_adj hb1 ?_
    have hlt : b < spec.length edge := by omega
    have hpos := slotVertex_num_edges_pos (spec := spec) (edge := edge) (k := b) hlt
    have := hfree b (le_refl _) (by omega)
    omega

/-! ## A burned/unburned split costs a chip -/

/-- Between a burned position and a later unburned one there is a *boundary*:
an unburned position whose predecessor is burned. -/
theorem exists_burned_boundary_up {edge : Fin p} {a b : ℕ}
    (ha : spec.slotVertex edge a ∈ burned spec.graph D w)
    (hb : spec.slotVertex edge b ∉ burned spec.graph D w)
    (hab : a ≤ b) (hble : b ≤ spec.length edge) :
    ∃ k, a < k ∧ k ≤ b ∧ spec.slotVertex edge (k - 1) ∈ burned spec.graph D w ∧
      spec.slotVertex edge k ∉ burned spec.graph D w := by
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp hab
    subst this
    exact absurd ha hb
  | succ m ih =>
    have ham : a ≤ m := by
      rcases Nat.lt_or_ge a (m + 1) with h | h
      · omega
      · exact absurd (by rw [show a = m + 1 by omega] at ha; exact ha) hb
    by_cases hm : spec.slotVertex edge m ∈ burned spec.graph D w
    · exact ⟨m + 1, by omega, le_refl _, by simpa using hm, hb⟩
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih hm ham (by omega)
      exact ⟨k, hk1, by omega, hk3, hk4⟩

/-- The downward boundary. -/
theorem exists_burned_boundary_down {edge : Fin p} {a b : ℕ}
    (ha : spec.slotVertex edge a ∈ burned spec.graph D w)
    (hb : spec.slotVertex edge b ∉ burned spec.graph D w)
    (hba : b ≤ a) (_hale : a ≤ spec.length edge) :
    ∃ k, b ≤ k ∧ k < a ∧ spec.slotVertex edge (k + 1) ∈ burned spec.graph D w ∧
      spec.slotVertex edge k ∉ burned spec.graph D w := by
  obtain ⟨d, hd⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
  clear hba
  induction d generalizing b with
  | zero =>
    exfalso
    apply hb
    rw [show b = a by omega]
    exact ha
  | succ m ih =>
    by_cases hb1 : spec.slotVertex edge (b + 1) ∈ burned spec.graph D w
    · exact ⟨b, le_refl _, by omega, hb1, hb⟩
    · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih hb1 (by omega)
      exact ⟨k, by omega, hk2, hk3, hk4⟩

/-- **Going up: a burned/unburned split costs a chip.** -/
theorem exists_chip_up {edge : Fin p} {a b : ℕ}
    (ha : spec.slotVertex edge a ∈ burned spec.graph D w)
    (hb : spec.slotVertex edge b ∉ burned spec.graph D w)
    (hab : a ≤ b) (hble : b ≤ spec.length edge) :
    ∃ k, a < k ∧ k ≤ b ∧ 1 ≤ D (spec.slotVertex edge k) ∧
      spec.slotVertex edge (k - 1) ∈ burned spec.graph D w ∧
      spec.slotVertex edge k ∉ burned spec.graph D w := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_burned_boundary_up ha hb hab hble
  refine ⟨k, hk1, hk2, ?_, hk3, hk4⟩
  refine one_le_of_burned_neighbour hk4 hk3 ?_
  have hlt : k - 1 < spec.length edge := by omega
  have := slotVertex_num_edges_pos' (spec := spec) (edge := edge) (k := k - 1) hlt
  rwa [show k - 1 + 1 = k by omega] at this

/-- **Going down: a burned/unburned split costs a chip.** -/
theorem exists_chip_down {edge : Fin p} {a b : ℕ}
    (ha : spec.slotVertex edge a ∈ burned spec.graph D w)
    (hb : spec.slotVertex edge b ∉ burned spec.graph D w)
    (hba : b ≤ a) (hale : a ≤ spec.length edge) :
    ∃ k, b ≤ k ∧ k < a ∧ 1 ≤ D (spec.slotVertex edge k) ∧
      spec.slotVertex edge (k + 1) ∈ burned spec.graph D w ∧
      spec.slotVertex edge k ∉ burned spec.graph D w := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_burned_boundary_down ha hb hba hale
  refine ⟨k, hk1, hk2, ?_, hk3, hk4⟩
  refine one_le_of_burned_neighbour hk4 hk3 ?_
  exact slotVertex_num_edges_pos (spec := spec) (edge := edge) (k := k) (by omega)

/-! ## Cycle blocking -/

/-- **Cycle blocking, tail burned.**  Two distinct slots with the same endpoints
form a cycle.  If the common tail is burned and the common head is not, the
cycle carries at least two chips — counted in the slot coordinate system, so
the statement is a linear inequality ready for `omega`.

The coincidence branch — both boundary witnesses landing on the unburned head —
is exactly the *banana* case (`length e₁ = length e₂ = 1`), and is where the
parallel-edge multiplicity supplies the second chip. -/
theorem two_le_chips_of_cycle_tail_burned (hEff : effective D) {e₁ e₂ : Fin p}
    (hne : e₁ ≠ e₂)
    (htail : spec.core.tail e₂ = spec.core.tail e₁)
    (hhead : spec.core.head e₂ = spec.core.head e₁)
    (hu : spec.coreVertex (spec.core.tail e₁) ∈ burned spec.graph D w)
    (hu' : spec.coreVertex (spec.core.head e₁) ∉ burned spec.graph D w) :
    2 ≤ D (spec.coreVertex (spec.core.head e₁))
      + spec.slotInteriorChips D e₁ + spec.slotInteriorChips D e₂ := by
  classical
  have ha1 : spec.slotVertex e₁ 0 ∈ burned spec.graph D w := by
    rw [slotVertex_zero]; exact hu
  have hb1 : spec.slotVertex e₁ (spec.length e₁) ∉ burned spec.graph D w := by
    rw [slotVertex_length]; exact hu'
  have ha2 : spec.slotVertex e₂ 0 ∈ burned spec.graph D w := by
    rw [slotVertex_zero, htail]; exact hu
  have hb2 : spec.slotVertex e₂ (spec.length e₂) ∉ burned spec.graph D w := by
    rw [slotVertex_length, hhead]; exact hu'
  obtain ⟨k₁, hk₁pos, hk₁le, hk₁chip, hk₁prev, -⟩ :=
    exists_chip_up ha1 hb1 (Nat.zero_le _) (le_refl _)
  obtain ⟨k₂, hk₂pos, hk₂le, hk₂chip, hk₂prev, -⟩ :=
    exists_chip_up ha2 hb2 (Nat.zero_le _) (le_refl _)
  have hn1 : 0 ≤ spec.slotInteriorChips D e₁ := slotInteriorChips_nonneg hEff e₁
  have hn2 : 0 ≤ spec.slotInteriorChips D e₂ := slotInteriorChips_nonneg hEff e₂
  have hnh : 0 ≤ D (spec.coreVertex (spec.core.head e₁)) := hEff _
  -- Each witness contributes either to its slot's interior total or to the head.
  have hc1 : 1 ≤ spec.slotInteriorChips D e₁ ∨ k₁ = spec.length e₁ := by
    rcases eq_or_lt_of_le hk₁le with heq | hlt
    · exact Or.inr heq
    · exact Or.inl (le_trans hk₁chip
        (apply_slotVertex_le_slotInteriorChips hEff hk₁pos hlt))
  have hc2 : 1 ≤ spec.slotInteriorChips D e₂ ∨ k₂ = spec.length e₂ := by
    rcases eq_or_lt_of_le hk₂le with heq | hlt
    · exact Or.inr heq
    · exact Or.inl (le_trans hk₂chip
        (apply_slotVertex_le_slotInteriorChips hEff hk₂pos hlt))
  have hhead1 : k₁ = spec.length e₁ → 1 ≤ D (spec.coreVertex (spec.core.head e₁)) := by
    intro h
    rw [h, slotVertex_length] at hk₁chip
    exact hk₁chip
  have hhead2 : k₂ = spec.length e₂ → 1 ≤ D (spec.coreVertex (spec.core.head e₁)) := by
    intro h
    rw [h, slotVertex_length, hhead] at hk₂chip
    exact hk₂chip
  rcases hc1 with h1 | h1
  · rcases hc2 with h2 | h2
    · omega
    · have := hhead2 h2; omega
  · rcases hc2 with h2 | h2
    · have := hhead1 h1; omega
    · -- Both witnesses are the head; it must carry two chips.
      subst h1
      subst h2
      have hp1 : spec.slotVertex e₁ (spec.length e₁ - 1) ∈ burned spec.graph D w :=
        hk₁prev
      have hp2 : spec.slotVertex e₂ (spec.length e₂ - 1) ∈ burned spec.graph D w :=
        hk₂prev
      have hadj1 : 0 < numEdges spec.graph (spec.coreVertex (spec.core.head e₁))
          (spec.slotVertex e₁ (spec.length e₁ - 1)) := by
        have h := slotVertex_num_edges_pos' (spec := spec) (edge := e₁)
          (k := spec.length e₁ - 1) (by have := spec.length_pos e₁; omega)
        rwa [show spec.length e₁ - 1 + 1 = spec.length e₁ from by
          have := spec.length_pos e₁; omega, slotVertex_length] at h
      have hadj2 : 0 < numEdges spec.graph (spec.coreVertex (spec.core.head e₁))
          (spec.slotVertex e₂ (spec.length e₂ - 1)) := by
        have h := slotVertex_num_edges_pos' (spec := spec) (edge := e₂)
          (k := spec.length e₂ - 1) (by have := spec.length_pos e₂; omega)
        rwa [show spec.length e₂ - 1 + 1 = spec.length e₂ from by
          have := spec.length_pos e₂; omega, slotVertex_length, hhead] at h
      have hdouble : 2 ≤ D (spec.coreVertex (spec.core.head e₁)) := by
        by_cases hone : spec.length e₁ = 1 ∧ spec.length e₂ = 1
        · -- the banana case: the two edges to the burned tail are parallel
          exact two_le_of_double_burned_edge hu' hu
            (two_le_num_edges_of_parallel_unit hne hone.1 hone.2 htail hhead)
        · refine two_le_of_two_burned_neighbours hu' hp1 hp2 ?_ hadj1 hadj2
          have hl1 := spec.length_pos e₁
          have hl2 := spec.length_pos e₂
          rcases Nat.lt_or_ge 1 (spec.length e₁) with hbig | hsmall
          · rcases Nat.lt_or_ge 1 (spec.length e₂) with hbig2 | hsmall2
            · exact slotVertex_ne_of_slot_ne hne (by omega) (by omega) (by omega)
                (by omega)
            · rw [show spec.length e₂ - 1 = 0 from by omega, slotVertex_zero]
              exact slotVertex_ne_coreVertex (by omega) (by omega) _
          · have h1' : spec.length e₁ = 1 := by omega
            have h2' : spec.length e₂ ≠ 1 := fun h => hone ⟨h1', h⟩
            rw [show spec.length e₁ - 1 = 0 from by omega, slotVertex_zero]
            exact Ne.symm (slotVertex_ne_coreVertex (by omega) (by omega) _)
      omega

/-- **Cycle blocking, head burned.**  The mirror image of
`two_le_chips_of_cycle_tail_burned`. -/
theorem two_le_chips_of_cycle_head_burned (hEff : effective D) {e₁ e₂ : Fin p}
    (hne : e₁ ≠ e₂)
    (htail : spec.core.tail e₂ = spec.core.tail e₁)
    (hhead : spec.core.head e₂ = spec.core.head e₁)
    (hu : spec.coreVertex (spec.core.head e₁) ∈ burned spec.graph D w)
    (hu' : spec.coreVertex (spec.core.tail e₁) ∉ burned spec.graph D w) :
    2 ≤ D (spec.coreVertex (spec.core.tail e₁))
      + spec.slotInteriorChips D e₁ + spec.slotInteriorChips D e₂ := by
  classical
  have ha1 : spec.slotVertex e₁ (spec.length e₁) ∈ burned spec.graph D w := by
    rw [slotVertex_length]; exact hu
  have hb1 : spec.slotVertex e₁ 0 ∉ burned spec.graph D w := by
    rw [slotVertex_zero]; exact hu'
  have ha2 : spec.slotVertex e₂ (spec.length e₂) ∈ burned spec.graph D w := by
    rw [slotVertex_length, hhead]; exact hu
  have hb2 : spec.slotVertex e₂ 0 ∉ burned spec.graph D w := by
    rw [slotVertex_zero, htail]; exact hu'
  obtain ⟨k₁, -, hk₁lt, hk₁chip, hk₁next, -⟩ :=
    exists_chip_down ha1 hb1 (Nat.zero_le _) (le_refl _)
  obtain ⟨k₂, -, hk₂lt, hk₂chip, hk₂next, -⟩ :=
    exists_chip_down ha2 hb2 (Nat.zero_le _) (le_refl _)
  have hn1 : 0 ≤ spec.slotInteriorChips D e₁ := slotInteriorChips_nonneg hEff e₁
  have hn2 : 0 ≤ spec.slotInteriorChips D e₂ := slotInteriorChips_nonneg hEff e₂
  have hnt : 0 ≤ D (spec.coreVertex (spec.core.tail e₁)) := hEff _
  have hc1 : 1 ≤ spec.slotInteriorChips D e₁ ∨ k₁ = 0 := by
    rcases Nat.eq_zero_or_pos k₁ with hz | hpos
    · exact Or.inr hz
    · exact Or.inl (le_trans hk₁chip
        (apply_slotVertex_le_slotInteriorChips hEff hpos hk₁lt))
  have hc2 : 1 ≤ spec.slotInteriorChips D e₂ ∨ k₂ = 0 := by
    rcases Nat.eq_zero_or_pos k₂ with hz | hpos
    · exact Or.inr hz
    · exact Or.inl (le_trans hk₂chip
        (apply_slotVertex_le_slotInteriorChips hEff hpos hk₂lt))
  have htail1 : k₁ = 0 → 1 ≤ D (spec.coreVertex (spec.core.tail e₁)) := by
    intro h
    rw [h, slotVertex_zero] at hk₁chip
    exact hk₁chip
  have htail2 : k₂ = 0 → 1 ≤ D (spec.coreVertex (spec.core.tail e₁)) := by
    intro h
    rw [h, slotVertex_zero, htail] at hk₂chip
    exact hk₂chip
  rcases hc1 with h1 | h1
  · rcases hc2 with h2 | h2
    · omega
    · have := htail2 h2; omega
  · rcases hc2 with h2 | h2
    · have := htail1 h1; omega
    · subst h1
      subst h2
      have hadj1 : 0 < numEdges spec.graph (spec.coreVertex (spec.core.tail e₁))
          (spec.slotVertex e₁ 1) := by
        have h := slotVertex_num_edges_pos (spec := spec) (edge := e₁) (k := 0) hk₁lt
        rwa [slotVertex_zero] at h
      have hadj2 : 0 < numEdges spec.graph (spec.coreVertex (spec.core.tail e₁))
          (spec.slotVertex e₂ 1) := by
        have h := slotVertex_num_edges_pos (spec := spec) (edge := e₂) (k := 0) hk₂lt
        rwa [slotVertex_zero, htail] at h
      have hdouble : 2 ≤ D (spec.coreVertex (spec.core.tail e₁)) := by
        by_cases hone : spec.length e₁ = 1 ∧ spec.length e₂ = 1
        · refine two_le_of_double_burned_edge hu' hu ?_
          rw [num_edges_symmetric]
          exact two_le_num_edges_of_parallel_unit hne hone.1 hone.2 htail hhead
        · refine two_le_of_two_burned_neighbours hu' hk₁next hk₂next ?_ hadj1 hadj2
          rcases Nat.lt_or_ge 1 (spec.length e₁) with hbig | hsmall
          · rcases Nat.lt_or_ge 1 (spec.length e₂) with hbig2 | hsmall2
            · exact slotVertex_ne_of_slot_ne hne Nat.one_pos hbig Nat.one_pos hbig2
            · have h2' : spec.length e₂ = 1 := by have := spec.length_pos e₂; omega
              have hv2 : spec.slotVertex e₂ 1 = spec.coreVertex (spec.core.head e₂) := by
                have hL := slotVertex_length (spec := spec) e₂
                rwa [h2'] at hL
              rw [hv2]
              exact slotVertex_ne_coreVertex Nat.one_pos hbig _
          · have h1' : spec.length e₁ = 1 := by have := spec.length_pos e₁; omega
            have h2' : spec.length e₂ ≠ 1 := fun h => hone ⟨h1', h⟩
            have hbig2 : 1 < spec.length e₂ := by have := spec.length_pos e₂; omega
            have hv1 : spec.slotVertex e₁ 1 = spec.coreVertex (spec.core.head e₁) := by
              have hL := slotVertex_length (spec := spec) e₁
              rwa [h1'] at hL
            rw [hv1]
            exact Ne.symm (slotVertex_ne_coreVertex Nat.one_pos hbig2 _)
      omega

end Utilities.Certificate.SubdivisionGraph.Spec
