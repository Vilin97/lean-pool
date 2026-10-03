/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedBoundedEdges
import LeanPool.AsymptoticTrianglePacking.Internal.NearRegularNibble
public import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoarseCellCoupled
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxAllocationSpec
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Finset.Fin
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring


/-! # BoxPlacementCount -/

open Finset

public section

namespace Nibble.AX1.BoxCount

/-- The cell sets of a prescribed size in one cluster. -/
def subs (P u : ℕ) : Finset (Finset (Fin P)) := (Finset.univ : Finset (Fin P)).powersetCard u

/-- The placements of a copy with prescribed sizes `u`: one cell set per cluster. -/
def plc (P : ℕ) (u : ZMod 3 → ℕ) : Finset (ZMod 3 → Finset (Fin P)) :=
  Fintype.piFinset (fun a => subs P (u a))

variable {P : ℕ} {u : ZMod 3 → ℕ}

theorem mem_subs {u : ℕ} {A : Finset (Fin P)} : A ∈ subs P u ↔ #A = u := by
  rw [subs, Finset.mem_powersetCard_univ]

theorem card_subs (P u : ℕ) : #(subs P u) = Nat.choose P u := by
  rw [subs, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem mem_plc {A : ZMod 3 → Finset (Fin P)} : A ∈ plc P u ↔ ∀ a, #(A a) = u a := by
  rw [plc, Fintype.mem_piFinset]
  exact forall_congr' fun a => mem_subs

/-! ### Counting the cell sets of one cluster -/

/-- The subsets of prescribed size containing a prescribed set. -/
theorem card_subs_req {u : ℕ} (B : Finset (Fin P)) (hB : #B ≤ u) :
    #((subs P u).filter (fun A => B ⊆ A)) = Nat.choose (P - #B) (u - #B) := by
  classical
  have hkey : #((subs P u).filter (fun A => B ⊆ A))
      = #(Finset.powersetCard (u - #B) ((Finset.univ : Finset (Fin P)) \ B)) := by
    refine Finset.card_bij' (fun A _ => A \ B) (fun Cc _ => Cc ∪ B) ?_ ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_filter, mem_subs] at hA
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ x, hx.2⟩
      · rw [Finset.card_sdiff_of_subset hA.2, hA.1]
    · intro Cc hCc
      rw [Finset.mem_powersetCard] at hCc
      rw [Finset.mem_filter, mem_subs]
      have hdisj : Disjoint Cc B := by
        rw [Finset.disjoint_right]
        intro x hxB hxC
        have := hCc.1 hxC
        rw [Finset.mem_sdiff] at this
        exact this.2 hxB
      refine ⟨?_, Finset.subset_union_right⟩
      rw [Finset.card_union_of_disjoint hdisj, hCc.2]
      omega
    · intro A hA
      rw [Finset.mem_filter] at hA
      show A \ B ∪ B = A
      rw [Finset.sdiff_union_of_subset hA.2]
    · intro Cc hCc
      rw [Finset.mem_powersetCard] at hCc
      have hdisj : Disjoint Cc B := by
        rw [Finset.disjoint_right]
        intro x hxB hxC
        have := hCc.1 hxC
        rw [Finset.mem_sdiff] at this
        exact this.2 hxB
      change (Cc ∪ B) \ B = Cc
      rw [Finset.union_sdiff_cancel_right hdisj]
  rw [hkey, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ B),
    Finset.card_univ, Fintype.card_fin]

/-- The absorption identity for binomial coefficients, in cleared form. -/
theorem choose_mul_step {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    n * Nat.choose (n - 1) (k - 1) = k * Nat.choose n k := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have := Nat.add_one_mul_choose_eq n' k'
  simpa [Nat.mul_comm] using this

/-- **One prescribed cell in one cluster.** -/
theorem subs_one_mul {u : ℕ} (huP : u ≤ P) (i : Fin P) :
    #((subs P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P = u * #(subs P u) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · have hempty : (subs P 0).filter (fun A => ({i} : Finset (Fin P)) ⊆ A) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      rw [Finset.mem_filter, mem_subs] at hA
      have := Finset.card_le_card hA.2
      simp [hA.1] at this
    rw [hempty]
    simp
  · have hB : #({i} : Finset (Fin P)) = 1 := Finset.card_singleton i
    rw [card_subs_req {i} (by omega), card_subs, hB, Nat.mul_comm]
    exact choose_mul_step hu huP

/-- **Two prescribed cells in one cluster.** -/
theorem subs_two_mul {u : ℕ} (huP : u ≤ P) {i i' : Fin P} (hii : i ≠ i') :
    #((subs P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A)) * (P * (P - 1))
      = u * (u - 1) * #(subs P u) := by
  have hB : #({i, i'} : Finset (Fin P)) = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hii), Finset.card_singleton]
  by_cases hu : 2 ≤ u
  · have h1 : #((subs P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A))
        = Nat.choose (P - 2) (u - 2) := by
      rw [card_subs_req _ (by omega), hB]
    have hP2 : 2 ≤ P := le_trans hu huP
    have e1 : (P - 1) * Nat.choose (P - 2) (u - 2) = (u - 1) * Nat.choose (P - 1) (u - 1) := by
      have := choose_mul_step (n := P - 1) (k := u - 1) (by omega) (by omega)
      have h2 : P - 1 - 1 = P - 2 := by omega
      have h3 : u - 1 - 1 = u - 2 := by omega
      rwa [h2, h3] at this
    have e2 : P * Nat.choose (P - 1) (u - 1) = u * Nat.choose P u :=
      choose_mul_step (by omega) huP
    rw [h1, card_subs]
    calc Nat.choose (P - 2) (u - 2) * (P * (P - 1))
        = P * ((P - 1) * Nat.choose (P - 2) (u - 2)) := by ring
      _ = P * ((u - 1) * Nat.choose (P - 1) (u - 1)) := by rw [e1]
      _ = (u - 1) * (P * Nat.choose (P - 1) (u - 1)) := by ring
      _ = (u - 1) * (u * Nat.choose P u) := by rw [e2]
      _ = u * (u - 1) * Nat.choose P u := by ring
  · have hempty : (subs P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      rw [Finset.mem_filter, mem_subs] at hA
      have := Finset.card_le_card hA.2
      rw [hB, hA.1] at this
      omega
    rw [hempty]
    have : u * (u - 1) = 0 := by
      interval_cases u <;> simp_all
    simp [this]

/-! ### Counting the placements -/

theorem succ_ne_self (p : ZMod 3) : p ≠ p + 1 := by revert p; decide

/-- Two distinct positions of a copy have a unique third. -/
theorem exists_third {p q : ZMod 3} (hpq : p ≠ q) : ∃ t : ZMod 3, p ≠ t ∧ q ≠ t := by
  revert hpq
  revert p q
  decide

/-- Three distinct positions exhaust `ZMod 3`. -/
theorem univ_eq_three {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) :
    (Finset.univ : Finset (ZMod 3)) = {p, q, t} := by
  have hcard : #({p, q, t} : Finset (ZMod 3)) = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpt]),
      Finset.card_insert_of_notMem (by simp [hqt]), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  rw [hcard, Finset.card_univ, ZMod.card]

theorem mem_three {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) (a : ZMod 3) :
    a = p ∨ a = q ∨ a = t := by
  have : a ∈ ({p, q, t} : Finset (ZMod 3)) := by
    rw [← univ_eq_three hpq hpt hqt]; exact Finset.mem_univ a
  simpa using this

/-- A product over the three positions of a copy. -/
theorem prod_three {M : Type*} [CommMonoid M] (f : ZMod 3 → M) {p q t : ZMod 3} (hpq : p ≠ q)
    (hpt : p ≠ t) (hqt : q ≠ t) : ∏ a : ZMod 3, f a = f p * f q * f t := by
  rw [univ_eq_three hpq hpt hqt, Finset.prod_insert (by simp [hpq, hpt]),
    Finset.prod_insert (by simp [hqt]), Finset.prod_singleton, mul_assoc]

/-- **The placements are the products of the cell sets**: a coordinatewise condition splits. -/
theorem card_plc_req (req : ZMod 3 → Finset (Fin P)) :
    #((plc P u).filter (fun A => ∀ a, req a ⊆ A a))
      = ∏ a : ZMod 3, #((subs P (u a)).filter (fun A => req a ⊆ A)) := by
  classical
  have hset : (plc P u).filter (fun A => ∀ a, req a ⊆ A a)
      = Fintype.piFinset (fun a => (subs P (u a)).filter (fun A => req a ⊆ A)) := by
    ext A
    simp only [Finset.mem_filter, plc, Fintype.mem_piFinset, ← forall_and]
  rw [hset, Fintype.card_piFinset]

/-- The requirement attached to a triple of prescribed cell sets. -/
private def req3 (p q _t : ZMod 3) (Bp Bq Bt : Finset (Fin P)) : ZMod 3 → Finset (Fin P) :=
  fun a => if a = p then Bp else if a = q then Bq else Bt

/-- **The master count**: a coordinatewise requirement splits into a product over the three
clusters. -/
theorem card_plc_three {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t)
    (Bp Bq Bt : Finset (Fin P)) :
    #((plc P u).filter (fun A => Bp ⊆ A p ∧ Bq ⊆ A q ∧ Bt ⊆ A t))
      = #((subs P (u p)).filter (fun A => Bp ⊆ A)) * #((subs P (u q)).filter (fun A => Bq ⊆ A))
        * #((subs P (u t)).filter (fun A => Bt ⊆ A)) := by
  classical
  have hp : req3 p q t Bp Bq Bt p = Bp := by rw [req3, ite_eq_left rfl]
  have hq : req3 p q t Bp Bq Bt q = Bq := by
    rw [req3, ite_eq_right (Ne.symm hpq), ite_eq_left rfl]
  have ht : req3 p q t Bp Bq Bt t = Bt := by
    rw [req3, ite_eq_right (Ne.symm hpt), ite_eq_right (Ne.symm hqt)]
  have hfil : (plc P u).filter (fun A => Bp ⊆ A p ∧ Bq ⊆ A q ∧ Bt ⊆ A t)
      = (plc P u).filter (fun A => ∀ a, req3 p q t Bp Bq Bt a ⊆ A a) := by
    refine Finset.filter_congr fun A _ => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩ a
      rcases mem_three hpq hpt hqt a with rfl | rfl | rfl
      · rwa [hp]
      · rwa [hq]
      · rwa [ht]
    · intro h
      exact ⟨by have := h p; rwa [hp] at this, by have := h q; rwa [hq] at this,
        by have := h t; rwa [ht] at this⟩
  rw [hfil, card_plc_req, prod_three _ hpq hpt hqt, hp, hq, ht]

/-- The empty requirement is no requirement. -/
theorem filter_empty_req (v : ℕ) :
    ((subs P v).filter (fun A => (∅ : Finset (Fin P)) ⊆ A)) = subs P v :=
  Finset.filter_true_of_mem fun _ _ => Finset.empty_subset _

theorem card_plc_prod {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) :
    #(plc P u) = #(subs P (u p)) * #(subs P (u q)) * #(subs P (u t)) := by
  rw [plc, Fintype.card_piFinset, prod_three (fun a => #(subs P (u a))) hpq hpt hqt]

theorem card_plc_pos (huP : ∀ a, u a ≤ P) : 0 < #(plc P u) := by
  rw [Finset.card_pos]
  refine ⟨fun a => (Finset.range (u a)).attachFin
      (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) (huP a)), ?_⟩
  rw [mem_plc]
  intro a
  simp

theorem card_one (huP : ∀ a, u a ≤ P) (p : ZMod 3) (i : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p)) * P = u p * #(plc P u) := by
  classical
  set q : ZMod 3 := p + 1 with hqdef
  have hpq : p ≠ q := succ_ne_self p
  obtain ⟨t, hpt, hqt⟩ := exists_third hpq
  have hfil : (plc P u).filter (fun A => i ∈ A p)
      = (plc P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A p ∧ (∅ : Finset (Fin P)) ⊆ A q
          ∧ (∅ : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp [Finset.singleton_subset_iff]
  rw [hfil, card_plc_three hpq hpt hqt, filter_empty_req, filter_empty_req,
    card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * #(subs P (u q))
        * #(subs P (u t)) * P
      = (#((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P)
        * (#(subs P (u q)) * #(subs P (u t))) := by ring
    _ = (u p * #(subs P (u p))) * (#(subs P (u q)) * #(subs P (u t))) := by
        rw [subs_one_mul (huP p) i]
    _ = u p * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

theorem card_two (huP : ∀ a, u a ≤ P) {p q : ZMod 3} (hpq : p ≠ q) (i j : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q)) * (P * P) = u p * u q * #(plc P u) := by
  classical
  obtain ⟨t, hpt, hqt⟩ := exists_third hpq
  have hfil : (plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q)
      = (plc P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A p ∧ ({j} : Finset (Fin P)) ⊆ A q
          ∧ (∅ : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp [Finset.singleton_subset_iff]
  rw [hfil, card_plc_three hpq hpt hqt, filter_empty_req, card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A))
        * #((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A))
        * #(subs P (u t)) * (P * P)
      = (#((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P)
        * (#((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A)) * P)
        * #(subs P (u t)) := by ring
    _ = (u p * #(subs P (u p))) * (u q * #(subs P (u q))) * #(subs P (u t)) := by
        rw [subs_one_mul (huP p) i, subs_one_mul (huP q) j]
    _ = u p * u q * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

theorem card_two_one (huP : ∀ a, u a ≤ P) {p q : ZMod 3} (hpq : p ≠ q) {i i' : Fin P}
    (hii : i ≠ i') (j : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p ∧ i' ∈ A p ∧ j ∈ A q)) * (P * (P - 1) * P)
      = u p * (u p - 1) * u q * #(plc P u) := by
  classical
  obtain ⟨t, hpt, hqt⟩ := exists_third hpq
  have hfil : (plc P u).filter (fun A => i ∈ A p ∧ i' ∈ A p ∧ j ∈ A q)
      = (plc P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A p
          ∧ ({j} : Finset (Fin P)) ⊆ A q ∧ (∅ : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.empty_subset,
      and_true]
    tauto
  rw [hfil, card_plc_three hpq hpt hqt, filter_empty_req, card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A))
        * #((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A))
        * #(subs P (u t)) * (P * (P - 1) * P)
      = (#((subs P (u p)).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A)) * (P * (P - 1)))
        * (#((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A)) * P)
        * #(subs P (u t)) := by ring
    _ = (u p * (u p - 1) * #(subs P (u p))) * (u q * #(subs P (u q))) * #(subs P (u t)) := by
        rw [subs_two_mul (huP p) hii, subs_one_mul (huP q) j]
    _ = u p * (u p - 1) * u q * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

theorem card_three (huP : ∀ a, u a ≤ P) {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t)
    (hqt : q ≠ t) (i j l : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q ∧ l ∈ A t)) * (P * P * P)
      = u p * u q * u t * #(plc P u) := by
  classical
  have hfil : (plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q ∧ l ∈ A t)
      = (plc P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A p ∧ ({j} : Finset (Fin P)) ⊆ A q
          ∧ ({l} : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp [Finset.singleton_subset_iff]
  rw [hfil, card_plc_three hpq hpt hqt, card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A))
        * #((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A))
        * #((subs P (u t)).filter (fun A => ({l} : Finset (Fin P)) ⊆ A)) * (P * P * P)
      = (#((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P)
        * (#((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A)) * P)
        * (#((subs P (u t)).filter (fun A => ({l} : Finset (Fin P)) ⊆ A)) * P) := by ring
    _ = (u p * #(subs P (u p))) * (u q * #(subs P (u q))) * (u t * #(subs P (u t))) := by
        rw [subs_one_mul (huP p) i, subs_one_mul (huP q) j, subs_one_mul (huP t) l]
    _ = u p * u q * u t * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

end Nibble.AX1.BoxCount

end






/-! # BoxPlacementEdge -/

open Finset

public section

namespace Nibble.AX1

/-- A cell-pair slot of an ordered cluster pair. -/
abbrev Slot (ι : Type) (P : ℕ) := ι × ι × Fin P × Fin P

/-- The ground set of the placement hypergraph: the cell-pair slots and the copy tokens. -/
abbrev PlaceVtx (ι κ : Type) (P : ℕ) := Slot ι P ⊕ κ

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ] {P : ℕ}

/-- The slot of the cell pair `(i, j)` of the cluster pair `(S, T)`, written in the orientation
prescribed by `idx`. -/
def orient (idx : ι → ℕ) (S T : ι) (i j : Fin P) : Slot ι P :=
  if idx S < idx T then (S, T, i, j) else (T, S, j, i)

/-- The rectangle that the placement `A` of the copy `c` occupies in the cluster pair
`(cl c a, cl c (a+1))`. -/
def rect (idx : ι → ℕ) (cl : κ → ZMod 3 → ι) (c : κ) (A : ZMod 3 → Finset (Fin P)) (a : ZMod 3) :
    Finset (PlaceVtx ι κ P) :=
  ((A a) ×ˢ (A (a + 1))).image (fun p => Sum.inl (orient idx (cl c a) (cl c (a + 1)) p.1 p.2))

/-- The edge of the placement `A` of the copy `c`: its token and its three rectangles. -/
def placeEdge (idx : ι → ℕ) (cl : κ → ZMod 3 → ι) (c : κ) (A : ZMod 3 → Finset (Fin P)) :
    Finset (PlaceVtx ι κ P) :=
  insert (Sum.inr c) ((Finset.univ : Finset (ZMod 3)).biUnion (rect idx cl c A))

variable {idx : ι → ℕ} {cl : κ → ZMod 3 → ι} {c : κ} {A : ZMod 3 → Finset (Fin P)}
/-- In `ZMod 3` two distinct positions are consecutive one way or the other. -/
theorem zmod3_consec {p q : ZMod 3} (hpq : p ≠ q) : q = p + 1 ∨ p = q + 1 := by
  revert hpq; revert p q; decide

/-- Two distinct positions of a copy give two distinct cluster pairs. -/
theorem zmod3_pair_ne {a b : ZMod 3} (hab : a ≠ b) :
    ¬ ((a = b ∧ a + 1 = b + 1) ∨ (a = b + 1 ∧ a + 1 = b)) := by
  revert hab; revert a b; decide

omit [DecidableEq ι] in
/-- The orientation is symmetric on distinct clusters. -/
theorem orient_symm {S T : ι} (h : idx S ≠ idx T) (i j : Fin P) :
    orient idx T S j i = orient idx S T i j := by
  rw [orient, orient]
  rcases lt_trichotomy (idx S) (idx T) with hlt | heq | hgt
  · rw [ite_eq_left hlt, ite_eq_right (by omega)]
  · exact absurd heq h
  · rw [ite_eq_left hgt, ite_eq_right (by omega)]

omit [DecidableEq ι] in
theorem orient_inj (S T : ι) :
    Function.Injective (fun p : Fin P × Fin P => orient idx S T p.1 p.2) := by
  intro p p' h
  simp only [orient] at h
  by_cases hst : idx S < idx T
  · rw [ite_eq_left hst, ite_eq_left hst] at h
    simpa [Prod.ext_iff] using h
  · rw [ite_eq_right hst, ite_eq_right hst] at h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.2.2 h.2.2.1

theorem mem_rect {a : ZMod 3} {x : Slot ι P} :
    (Sum.inl x : PlaceVtx ι κ P) ∈ rect idx cl c A a ↔
      ∃ i ∈ A a, ∃ j ∈ A (a + 1), orient idx (cl c a) (cl c (a + 1)) i j = x := by
  simp only [rect, Finset.mem_image, Finset.mem_product, Sum.inl.injEq]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hx⟩
    exact ⟨i, hi, j, hj, hx⟩
  · rintro ⟨i, hi, j, hj, hx⟩
    exact ⟨(i, j), ⟨hi, hj⟩, hx⟩

theorem inr_notMem_rect {a : ZMod 3} {c' : κ} :
    (Sum.inr c' : PlaceVtx ι κ P) ∉ rect idx cl c A a := by
  simp [rect]

/-- An edge contains exactly one token, that of its copy. -/
theorem mem_placeEdge_inr (c' : κ) :
    (Sum.inr c' : PlaceVtx ι κ P) ∈ placeEdge idx cl c A ↔ c' = c := by
  rw [placeEdge, Finset.mem_insert]
  constructor
  · rintro (h | h)
    · exact Sum.inr_injective h
    · rw [Finset.mem_biUnion] at h
      obtain ⟨a, -, ha⟩ := h
      exact absurd ha inr_notMem_rect
  · rintro rfl; exact Or.inl rfl

/-- The tokens of an edge: exactly the token of its copy. -/
theorem placeEdge_toRight : (placeEdge idx cl c A).toRight = {c} := by
  ext c'
  rw [Finset.mem_toRight, mem_placeEdge_inr, Finset.mem_singleton]

/-- **Occupying a slot.**  The placement `A` of `c` occupies the slot of the cell pair `(i, j)` in
the cluster pair `(cl c p, cl c q)` whenever `i ∈ A p` and `j ∈ A q`. -/
theorem mem_placeEdge_orient (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    {p q : ZMod 3} (hpq : p ≠ q) {i j : Fin P} (hi : i ∈ A p) (hj : j ∈ A q) :
    (Sum.inl (orient idx (cl c p) (cl c q) i j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A := by
  have hne : idx (cl c p) ≠ idx (cl c q) := fun h => hpq (hcl (hidx h))
  rw [placeEdge, Finset.mem_insert, Finset.mem_biUnion]
  refine Or.inr ?_
  rcases zmod3_consec hpq with rfl | rfl
  · exact ⟨p, Finset.mem_univ _, mem_rect.mpr ⟨i, hi, j, hj, rfl⟩⟩
  · exact ⟨q, Finset.mem_univ _, mem_rect.mpr ⟨j, hj, i, hi, orient_symm hne i j⟩⟩

/-- **The slots of an edge.**  The placement `A` of `c` occupies the slot `(S, T, i, j)` exactly
when `S` and `T` are two clusters of `c`, in the orientation prescribed by `idx`, and `i`, `j` are
cells of the corresponding two sets of `A`. -/
theorem mem_placeEdge_inl (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (S T : ι) (i j : Fin P) :
    (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A ↔
      ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧ idx S < idx T ∧ i ∈ A p ∧ j ∈ A q := by
  constructor
  · intro hmem
    rw [placeEdge, Finset.mem_insert] at hmem
    rcases hmem with h | h
    · exact absurd h (by simp)
    rw [Finset.mem_biUnion] at h
    obtain ⟨a, -, ha⟩ := h
    obtain ⟨i₀, hi₀, j₀, hj₀, hx⟩ := mem_rect.mp ha
    have hsucc : a ≠ a + 1 := BoxCount.succ_ne_self a
    have hane : cl c a ≠ cl c (a + 1) := fun h => hsucc (hcl h)
    have hidxne : idx (cl c a) ≠ idx (cl c (a + 1)) := fun h => hane (hidx h)
    rw [orient] at hx
    by_cases hlt : idx (cl c a) < idx (cl c (a + 1))
    · rw [ite_eq_left hlt] at hx
      simp only [Prod.mk.injEq] at hx
      obtain ⟨h1, h2, h3, h4⟩ := hx
      subst h1; subst h2; subst h3; subst h4
      exact ⟨a, a + 1, hsucc, rfl, rfl, hlt, hi₀, hj₀⟩
    · rw [ite_eq_right hlt] at hx
      simp only [Prod.mk.injEq] at hx
      obtain ⟨h1, h2, h3, h4⟩ := hx
      subst h1; subst h2; subst h3; subst h4
      exact ⟨a + 1, a, hsucc.symm, rfl, rfl, by omega, hj₀, hi₀⟩
  · rintro ⟨p, q, hpq, rfl, rfl, hlt, hi, hj⟩
    have := mem_placeEdge_orient (A := A) hidx hcl hpq hi hj
    rwa [orient, ite_eq_left hlt] at this

/-- **A cell pair of an edge.** -/
theorem mem_placeEdge_iff (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    {p q : ZMod 3} (hpq : p ≠ q) (i j : Fin P) :
    (Sum.inl (orient idx (cl c p) (cl c q) i j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A ↔
      i ∈ A p ∧ j ∈ A q := by
  constructor
  · intro hmem
    rw [orient] at hmem
    by_cases hlt : idx (cl c p) < idx (cl c q)
    · rw [ite_eq_left hlt] at hmem
      obtain ⟨p', q', -, h1, h2, -, hi, hj⟩ := (mem_placeEdge_inl hidx hcl _ _ _ _).mp hmem
      have hp' : p' = p := hcl h1
      have hq' : q' = q := hcl h2
      subst hp'; subst hq'
      exact ⟨hi, hj⟩
    · rw [ite_eq_right hlt] at hmem
      obtain ⟨p', q', -, h1, h2, -, hi, hj⟩ := (mem_placeEdge_inl hidx hcl _ _ _ _).mp hmem
      have hp' : p' = q := hcl h1
      have hq' : q' = p := hcl h2
      subst hp'; subst hq'
      exact ⟨hj, hi⟩
  · rintro ⟨hi, hj⟩
    exact mem_placeEdge_orient hidx hcl hpq hi hj

theorem card_rect (a : ZMod 3) : #(rect idx cl c A a) = #(A a) * #(A (a + 1)) := by
  have hinj : Function.Injective (fun p : Fin P × Fin P =>
      (Sum.inl (orient idx (cl c a) (cl c (a + 1)) p.1 p.2) : PlaceVtx ι κ P)) :=
    fun p p' h => orient_inj (idx := idx) _ _ (Sum.inl_injective h)
  rw [rect, Finset.card_image_of_injective _ hinj, Finset.card_product]

theorem rect_disjoint (hcl : Function.Injective (cl c)) {a b : ZMod 3} (hab : a ≠ b) :
    Disjoint (rect idx cl c A a) (rect idx cl c A b) := by
  rw [Finset.disjoint_left]
  rintro x ha hb
  rcases x with x | c'
  swap
  · exact inr_notMem_rect ha
  obtain ⟨i₁, -, j₁, -, hx₁⟩ := mem_rect.mp ha
  obtain ⟨i₂, -, j₂, -, hx₂⟩ := mem_rect.mp hb
  have hkey : (cl c a = cl c b ∧ cl c (a + 1) = cl c (b + 1)) ∨
      (cl c a = cl c (b + 1) ∧ cl c (a + 1) = cl c b) := by
    rw [orient] at hx₁ hx₂
    split_ifs at hx₁ hx₂ <;> subst hx₁ <;> simp only [Prod.mk.injEq] at hx₂ <;>
      first
        | exact Or.inl ⟨hx₂.1.symm, hx₂.2.1.symm⟩
        | exact Or.inr ⟨hx₂.1.symm, hx₂.2.1.symm⟩
        | exact Or.inl ⟨hx₂.2.1.symm, hx₂.1.symm⟩
        | exact Or.inr ⟨hx₂.2.1.symm, hx₂.1.symm⟩
  refine zmod3_pair_ne hab ?_
  rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hcl h1, hcl h2⟩
  · exact Or.inr ⟨hcl h1, hcl h2⟩

/-- **The size of an edge**: the token plus the three rectangles. -/
theorem placeEdge_card (hcl : Function.Injective (cl c)) :
    #(placeEdge idx cl c A) = 1 + ∑ a : ZMod 3, #(A a) * #(A (a + 1)) := by
  rw [placeEdge, Finset.card_insert_of_notMem (by
    rw [Finset.mem_biUnion]
    rintro ⟨a, -, ha⟩
    exact inr_notMem_rect ha)]
  rw [Finset.card_biUnion (fun a _ b _ hab => rect_disjoint hcl hab)]
  simp only [card_rect]
  omega

/-- **A placement is recoverable from its edge.** -/
theorem placeEdge_inj (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    {c' : κ} {A' : ZMod 3 → Finset (Fin P)} (hcl' : Function.Injective (cl c'))
    (hA : ∀ a, (A a).Nonempty) (hA' : ∀ a, (A' a).Nonempty)
    (h : placeEdge idx cl c A = placeEdge idx cl c' A') : c = c' ∧ A = A' := by
  have hcc : c = c' := by
    have hmem : (Sum.inr c : PlaceVtx ι κ P) ∈ placeEdge idx cl c' A' := by
      rw [← h, mem_placeEdge_inr]
    exact (mem_placeEdge_inr (A := A') (idx := idx) c).mp hmem
  subst hcc
  refine ⟨rfl, ?_⟩
  funext a
  ext i
  obtain ⟨j, hj⟩ := hA (a + 1)
  obtain ⟨j', hj'⟩ := hA' (a + 1)
  have hane : a ≠ a + 1 := BoxCount.succ_ne_self a
  constructor
  · intro hi
    have h1 : (Sum.inl (orient idx (cl c a) (cl c (a + 1)) i j) : PlaceVtx ι κ P)
        ∈ placeEdge idx cl c A := mem_placeEdge_orient hidx hcl hane hi hj
    rw [h] at h1
    exact ((mem_placeEdge_iff hidx hcl' hane i j).mp h1).1
  · intro hi
    have h1 : (Sum.inl (orient idx (cl c a) (cl c (a + 1)) i j') : PlaceVtx ι κ P)
        ∈ placeEdge idx cl c A' := mem_placeEdge_orient hidx hcl' hane hi hj'
    rw [← h] at h1
    exact ((mem_placeEdge_iff hidx hcl hane i j').mp h1).1

end Nibble.AX1

end


/-! # Box placement hypergraph -/

public section

open Finset

namespace Nibble.AX1

namespace BoxPlace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {P : ℕ}
  {idx : ι → ℕ} {cl : κ → ZMod 3 → ι} {sz : κ → ZMod 3 → ℕ}

/-- The number of placements of the copy `c`. -/
def placeCard (P : ℕ) (sz : κ → ZMod 3 → ℕ) (c : κ) : ℕ := #(BoxCount.plc P (sz c))

/-- **The placement hypergraph**: all placements of all copies. -/
def placeFam (P : ℕ) (idx : ι → ℕ) (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ) :
    Finset (Finset (PlaceVtx ι κ P)) :=
  Finset.univ.biUnion (fun c : κ => (BoxCount.plc P (sz c)).image (placeEdge idx cl c))

/-- **The weight of a placement**: the reciprocal of the number of placements of its copy, so that
the placements of a copy carry total weight `1`. -/
noncomputable def placeWt (P : ℕ) (sz : κ → ZMod 3 → ℕ) : Finset (PlaceVtx ι κ P) → ℝ :=
  fun U => ∑ c : κ, if (Sum.inr c : PlaceVtx ι κ P) ∈ U then ((placeCard P sz c : ℝ))⁻¹ else 0

omit [Fintype ι] in
/-- The edges of the placement hypergraph are the placements. -/
theorem mem_placeFam {U : Finset (PlaceVtx ι κ P)} (hU : U ∈ placeFam P idx cl sz) :
    ∃ (c : κ) (A : ZMod 3 → Finset (Fin P)), A ∈ BoxCount.plc P (sz c) ∧
      U = placeEdge idx cl c A := by
  rw [placeFam, Finset.mem_biUnion] at hU
  obtain ⟨c, -, hU⟩ := hU
  rw [Finset.mem_image] at hU
  obtain ⟨A, hA, rfl⟩ := hU
  exact ⟨c, A, hA, rfl⟩


/-- The contribution of one copy to the demand of the cluster pair `(S, T)`. -/
@[expose]
def boxDemandC (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ) (c : κ) (S T : ι) : ℝ :=
  ∑ a : ZMod 3, ∑ b : ZMod 3, if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0

omit [Fintype ι] [DecidableEq κ] in
theorem boxDemand_eq_sum (S T : ι) :
    boxDemand cl sz S T = ∑ c : κ, boxDemandC cl sz c S T := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem boxDemandC_nonneg (c : κ) (S T : ι) : 0 ≤ boxDemandC cl sz c S T := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split
  · positivity
  · exact le_rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem sz_mul_le_boxDemandC {c : κ} {p q : ZMod 3} {S T : ι} (hp : cl c p = S) (hq : cl c q = T) :
    (sz c p : ℝ) * (sz c q : ℝ) ≤ boxDemandC cl sz c S T := by
  have hterm : ∀ a : ZMod 3, 0 ≤ ∑ b : ZMod 3,
      if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0 := by
    intro a
    refine Finset.sum_nonneg fun b _ => ?_
    split
    · positivity
    · exact le_rfl
  have h1 : (∑ b : ZMod 3, if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0)
      ≤ boxDemandC cl sz c S T :=
    Finset.single_le_sum (f := fun a => ∑ b : ZMod 3,
      if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0)
      (fun a _ => hterm a) (Finset.mem_univ p)
  have h2 : (sz c p : ℝ) * (sz c q : ℝ)
      ≤ ∑ b : ZMod 3, if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0 := by
    have h3 : ∀ b : ZMod 3, 0 ≤
        (if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0) := by
      intro b
      split
      · positivity
      · exact le_rfl
    calc (sz c p : ℝ) * (sz c q : ℝ)
        = (if cl c p = S ∧ cl c q = T then (sz c p : ℝ) * (sz c q : ℝ) else 0) :=
          (ite_eq_left ⟨hp, hq⟩).symm
      _ ≤ _ := Finset.single_le_sum (f := fun b : ZMod 3 =>
          if cl c p = S ∧ cl c b = T then (sz c p : ℝ) * (sz c b : ℝ) else 0)
          (fun b _ => h3 b) (Finset.mem_univ q)
  linarith

/-! ### Sums over the placement hypergraph -/

section Structure

variable (hidx : Function.Injective idx) (hcl : ∀ c, Function.Injective (cl c))
  (hsz1 : ∀ c a, 1 ≤ sz c a) (hszP : ∀ c a, sz c a ≤ P)

include hsz1 in
omit [Fintype κ] [DecidableEq κ] in
theorem plc_nonempty {c : κ} {A : ZMod 3 → Finset (Fin P)} (hA : A ∈ BoxCount.plc P (sz c))
    (a : ZMod 3) : (A a).Nonempty := by
  rw [← Finset.card_pos, BoxCount.mem_plc.mp hA a]
  exact hsz1 c a

include hidx hcl hsz1 in
omit [Fintype ι] in
/-- A sum over the placement hypergraph is a sum over copies and placements. -/
theorem sum_placeFam (f : Finset (PlaceVtx ι κ P) → ℝ) :
    ∑ U ∈ placeFam P idx cl sz, f U
      = ∑ c : κ, ∑ A ∈ BoxCount.plc P (sz c), f (placeEdge idx cl c A) := by
  classical
  have hpd : (↑(Finset.univ : Finset κ) : Set κ).PairwiseDisjoint
      (fun c : κ => (BoxCount.plc P (sz c)).image (placeEdge idx cl c)) := by
    intro c _ c' _ hcc
    rw [Function.onFun, Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨A, -, rfl⟩ := hU
    obtain ⟨A', -, hA'⟩ := hU'
    have hmem : (Sum.inr c : PlaceVtx ι κ P) ∈ placeEdge idx cl c A :=
      (mem_placeEdge_inr (A := A) (idx := idx) c).mpr rfl
    rw [← hA', mem_placeEdge_inr] at hmem
    exact hcc hmem
  rw [placeFam, Finset.sum_biUnion hpd]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_image fun A hA A' hA' h => ?_
  exact (placeEdge_inj hidx (hcl c) (hcl c) (plc_nonempty hsz1 hA) (plc_nonempty hsz1 hA') h).2

include hidx hcl hsz1 in
omit [Fintype ι] in
/-- A filtered sum over the placement hypergraph. -/
theorem sum_placeFam_filter (p : Finset (PlaceVtx ι κ P) → Prop) [DecidablePred p]
    (f : Finset (PlaceVtx ι κ P) → ℝ) :
    ∑ U ∈ (placeFam P idx cl sz).filter p, f U
      = ∑ c : κ, ∑ A ∈ (BoxCount.plc P (sz c)).filter (fun A => p (placeEdge idx cl c A)),
          f (placeEdge idx cl c A) := by
  classical
  rw [Finset.sum_filter, sum_placeFam hidx hcl hsz1]
  exact Finset.sum_congr rfl fun c _ => (Finset.sum_filter _ _).symm

omit [Fintype ι] in
/-- The weight of a placement of `c` is the reciprocal of the number of placements of `c`. -/
theorem placeWt_edge (c : κ) (A : ZMod 3 → Finset (Fin P)) :
    placeWt P sz (placeEdge idx cl c A) = ((placeCard P sz c : ℝ))⁻¹ := by
  classical
  simp only [placeWt, mem_placeEdge_inr]
  rw [Finset.sum_ite_eq' Finset.univ c (fun c' => ((placeCard P sz c' : ℝ))⁻¹)]
  simp

omit [Fintype ι] in
theorem placeWt_nonneg (U : Finset (PlaceVtx ι κ P)) : 0 ≤ placeWt P sz U := by
  refine Finset.sum_nonneg fun c _ => ?_
  split
  · positivity
  · exact le_rfl

include hszP in
omit [Fintype κ] [DecidableEq κ] in
theorem placeCard_pos (c : κ) : 0 < placeCard P sz c :=
  BoxCount.card_plc_pos (fun a => hszP c a)

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The total weight is the number of copies.** -/
theorem sum_placeWt :
    ∑ U ∈ placeFam P idx cl sz, placeWt P sz U = (Fintype.card κ : ℝ) := by
  classical
  rw [sum_placeFam hidx hcl hsz1]
  have hone : ∀ c : κ,
      ∑ A ∈ BoxCount.plc P (sz c), placeWt P sz (placeEdge idx cl c A) = 1 := by
    intro c
    have hpos : 0 < placeCard P sz c := placeCard_pos hszP c
    have hposR : (0 : ℝ) < (placeCard P sz c : ℝ) := by exact_mod_cast hpos
    simp only [placeWt_edge]
    rw [Finset.sum_const, nsmul_eq_mul]
    have : (#(BoxCount.plc P (sz c)) : ℝ) = (placeCard P sz c : ℝ) := rfl
    rw [this]
    field_simp
  rw [Finset.sum_congr rfl (fun c _ => hone c), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

include hcl in
omit [Fintype ι] in
/-- Every edge is nonempty and has at most `1 + 3s₀²` vertices. -/
theorem placeFam_edge_size {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) (U : Finset (PlaceVtx ι κ P))
    (hU : U ∈ placeFam P idx cl sz) : U.Nonempty ∧ #U ≤ 1 + 3 * s₀ ^ 2 := by
  obtain ⟨c, A, hA, rfl⟩ := mem_placeFam hU
  constructor
  · exact ⟨Sum.inr c, (mem_placeEdge_inr (A := A) (idx := idx) c).mpr rfl⟩
  · rw [placeEdge_card (hcl c)]
    have hbound : ∀ a : ZMod 3, #(A a) * #(A (a + 1)) ≤ s₀ ^ 2 := by
      intro a
      rw [BoxCount.mem_plc.mp hA a, BoxCount.mem_plc.mp hA (a + 1), sq]
      exact Nat.mul_le_mul (hs c a) (hs c (a + 1))
    have hsum : ∑ a : ZMod 3, #(A a) * #(A (a + 1)) ≤ 3 * s₀ ^ 2 := by
      calc ∑ a : ZMod 3, #(A a) * #(A (a + 1)) ≤ ∑ _a : ZMod 3, s₀ ^ 2 :=
            Finset.sum_le_sum fun a _ => hbound a
        _ = 3 * s₀ ^ 2 := by simp [ZMod.card, mul_comm]
    omega

end Structure

/-! ### The count of the placements of one copy through a prescribed slot -/

/-- Two ordered pairs of distinct residues mod `3` that agree neither directly nor after a swap
have a residue outside the first pair inside the second. -/
private theorem zmod3_third : ∀ p q p' q' : ZMod 3, p ≠ q → p' ≠ q' →
    ¬ (p = p' ∧ q = q') → ¬ (p = q' ∧ q = p') →
    ∃ t : ZMod 3, t ≠ p ∧ t ≠ q ∧ (t = p' ∨ t = q') := by
  change ∀ p q p' q' : Fin 3, p ≠ q → p' ≠ q' →
    ¬ (p = p' ∧ q = q') → ¬ (p = q' ∧ q = p') →
    ∃ t : Fin 3, t ≠ p ∧ t ≠ q ∧ (t = p' ∨ t = q')
  decide

section PerCopy

variable {c : κ}

omit [Fintype κ] [DecidableEq κ] in
theorem sum_inv_const (F : Finset (ZMod 3 → Finset (Fin P))) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹ = (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹ := by
  rw [Finset.sum_const, nsmul_eq_mul]

omit [Fintype ι] [Fintype κ] in
/-- **The placements of `c` occupying a prescribed slot**: either there are none, or the slot is
the cell pair `(i, j)` of two clusters `cl c p`, `cl c q` of `c`, and then they are at most a
`sz(c,p)·sz(c,q)/P²` fraction of all placements. -/
theorem slot_count_core (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 0 < P) (S T : ι) (i j : Fin P)
    {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    F = ∅ ∨ ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧
      (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹ ≤ (sz c p : ℝ) * (sz c q : ℝ) / (P : ℝ) ^ 2 := by
  classical
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hNpos : 0 < placeCard P sz c := BoxCount.card_plc_pos hszP
  have hNR : (0 : ℝ) < (placeCard P sz c : ℝ) := by exact_mod_cast hNpos
  by_cases hex : ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧ idx S < idx T
  · obtain ⟨p, q, hpq, hp, hq, hlt⟩ := hex
    refine Or.inr ⟨p, q, hpq, hp, hq, ?_⟩
    set G := (BoxCount.plc P (sz c)).filter (fun A => i ∈ A p ∧ j ∈ A q) with hGdef
    have hFG : F ⊆ G := by
      intro A hA
      rw [hGdef, Finset.mem_filter]
      refine ⟨hFsub hA, ?_⟩
      obtain ⟨u, v, -, hu, hv, -, hiu, hjv⟩ := (mem_placeEdge_inl hidx hcl S T i j).mp (hF A hA)
      have e1 : u = p := hcl (hu.trans hp.symm)
      have e2 : v = q := hcl (hv.trans hq.symm)
      subst e1; subst e2
      exact ⟨hiu, hjv⟩
    have hcount := BoxCount.card_two (u := sz c) hszP hpq i j
    have hcard : (#F : ℝ) ≤ (#G : ℝ) := by exact_mod_cast Finset.card_le_card hFG
    have hcountR : (#G : ℝ) * ((P : ℝ) * (P : ℝ))
        = (sz c p : ℝ) * (sz c q : ℝ) * (placeCard P sz c : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount
    rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ hNR (by positivity), sq]
    linarith only [mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ (P : ℝ) * (P : ℝ)),
      hcountR]
  · refine Or.inl (Finset.eq_empty_of_forall_notMem fun A hA => ?_)
    obtain ⟨p, q, hpq, h1, h2, hlt, -, -⟩ := (mem_placeEdge_inl hidx hcl S T i j).mp (hF A hA)
    exact hex ⟨p, q, hpq, h1, h2, hlt⟩

omit [Fintype ι] [Fintype κ] in
/-- **The placements of `c` through a slot of `(S,T)` are a `demand/P²` fraction.** -/
theorem slot_count_le_demand (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 0 < P) (S T : ι) (i j : Fin P)
    {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹ ≤ boxDemandC cl sz c S T / (P : ℝ) ^ 2 := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [sum_inv_const]
  rcases slot_count_core hidx hcl hszP hP S T i j hFsub hF with rfl | ⟨p, q, -, hp, hq, h⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact div_nonneg (boxDemandC_nonneg c S T) (by positivity)
  · refine le_trans h ?_
    gcongr
    exact sz_mul_le_boxDemandC hp hq

omit [Fintype ι] [Fintype κ] in
/-- The same count is at most `s₀²/P²`. -/
theorem slot_count_le_sz (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 0 < P) {s₀ : ℕ} (hs : ∀ a, sz c a ≤ s₀) (S T : ι)
    (i j : Fin P) {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹ ≤ (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [sum_inv_const]
  rcases slot_count_core hidx hcl hszP hP S T i j hFsub hF with rfl | ⟨p, q, -, -, -, h⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  · refine le_trans h ?_
    have h1 : (sz c p : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs p
    have h2 : (sz c q : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs q
    have h3 : (0 : ℝ) ≤ (sz c p : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ (sz c q : ℝ) := Nat.cast_nonneg _
    gcongr
    nlinarith

omit [Fintype ι] [Fintype κ] in
/-- **Two slots pin a copy down in a third coordinate.**  This is the estimate that makes the
codegrees of the placement hypergraph small, and it is where the small-box restriction enters. -/
theorem two_slot_count_le (hidx : Function.Injective idx) (hcl : Function.Injective (cl c))
    (hszP : ∀ a, sz c a ≤ P) (hP : 2 ≤ P) {s₀ : ℕ} (hs : ∀ a, sz c a ≤ s₀) {S T S' T' : ι}
    {i j i' j' : Fin P} (hne : (S, T, i, j) ≠ (S', T', i', j'))
    {F : Finset (ZMod 3 → Finset (Fin P))} (hFsub : F ⊆ BoxCount.plc P (sz c))
    (hF1 : ∀ A ∈ F, (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A)
    (hF2 : ∀ A ∈ F, (Sum.inl (S', T', i', j') : PlaceVtx ι κ P) ∈ placeEdge idx cl c A) :
    ∑ _A ∈ F, ((placeCard P sz c : ℝ))⁻¹
      ≤ 18 * (s₀ : ℝ) / (P : ℝ) * (boxDemandC cl sz c S T / (P : ℝ) ^ 2) := by
  classical
  have hP0 : 0 < P := by omega
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hNpos : 0 < placeCard P sz c := BoxCount.card_plc_pos hszP
  have hNR : (0 : ℝ) < (placeCard P sz c : ℝ) := by exact_mod_cast hNpos
  have hnn : 0 ≤ 18 * (s₀ : ℝ) / (P : ℝ) * (boxDemandC cl sz c S T / (P : ℝ) ^ 2) := by
    have := boxDemandC_nonneg (cl := cl) (sz := sz) c S T
    positivity
  rw [sum_inv_const]
  by_cases hex : ∃ p q : ZMod 3, p ≠ q ∧ cl c p = S ∧ cl c q = T ∧ idx S < idx T
  · obtain ⟨p, q, hpq, hp, hq, hlt⟩ := hex
    by_cases hex' : ∃ p' q' : ZMod 3, p' ≠ q' ∧ cl c p' = S' ∧ cl c q' = T' ∧ idx S' < idx T'
    · obtain ⟨p', q', hpq', hp', hq', hlt'⟩ := hex'
      have hmemF : ∀ A ∈ F, i ∈ A p ∧ j ∈ A q ∧ i' ∈ A p' ∧ j' ∈ A q' := by
        intro A hA
        obtain ⟨u, v, -, hu, hv, -, hiu, hjv⟩ :=
          (mem_placeEdge_inl hidx hcl S T i j).mp (hF1 A hA)
        obtain ⟨u', v', -, hu', hv', -, hiu', hjv'⟩ :=
          (mem_placeEdge_inl hidx hcl S' T' i' j').mp (hF2 A hA)
        have e1 : u = p := hcl (hu.trans hp.symm)
        have e2 : v = q := hcl (hv.trans hq.symm)
        have e3 : u' = p' := hcl (hu'.trans hp'.symm)
        have e4 : v' = q' := hcl (hv'.trans hq'.symm)
        subst e1; subst e2; subst e3; subst e4
        exact ⟨hiu, hjv, hiu', hjv'⟩
      have hPcube : P ^ 3 ≤ 2 * (P * (P - 1) * P) := by
        have hstep : P ≤ 2 * (P - 1) := by omega
        calc P ^ 3 = P * P * P := by ring
          _ ≤ (2 * (P - 1)) * P * P := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hstep)
          _ = 2 * (P * (P - 1) * P) := by ring
      have hkey : #F * P ^ 3 ≤ 2 * s₀ * sz c p * sz c q * placeCard P sz c := by
        by_cases hcase : p = p' ∧ q = q'
        · obtain ⟨hpp, hqq⟩ := hcase
          subst hpp; subst hqq
          have hST : S = S' := hp.symm.trans hp'
          have hTT : T = T' := hq.symm.trans hq'
          subst hST; subst hTT
          by_cases hii : i = i'
          · subst hii
            have hjj : j ≠ j' := by
              intro h
              exact hne (by rw [h])
            set G := (BoxCount.plc P (sz c)).filter
              (fun A => j ∈ A q ∧ j' ∈ A q ∧ i ∈ A p) with hGdef
            have hFG : F ⊆ G := by
              intro A hA
              obtain ⟨h1, h2, h3, h4⟩ := hmemF A hA
              rw [hGdef, Finset.mem_filter]
              exact ⟨hFsub hA, h2, h4, h1⟩
            have hcount := BoxCount.card_two_one (u := sz c) hszP (Ne.symm hpq) hjj i
            have hGle : #G * (P * (P - 1) * P) ≤ s₀ * sz c p * sz c q * placeCard P sz c := by
              rw [hcount]
              have h5 : sz c q - 1 ≤ s₀ := le_trans (Nat.sub_le _ _) (hs q)
              calc sz c q * (sz c q - 1) * sz c p * placeCard P sz c
                  ≤ sz c q * s₀ * sz c p * placeCard P sz c :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h5))
                _ = s₀ * sz c p * sz c q * placeCard P sz c := by ring
            calc #F * P ^ 3 ≤ #G * (2 * (P * (P - 1) * P)) :=
                  Nat.mul_le_mul (Finset.card_le_card hFG) hPcube
              _ = 2 * (#G * (P * (P - 1) * P)) := by ring
              _ ≤ 2 * (s₀ * sz c p * sz c q * placeCard P sz c) := Nat.mul_le_mul_left _ hGle
              _ = 2 * s₀ * sz c p * sz c q * placeCard P sz c := by ring
          · set G := (BoxCount.plc P (sz c)).filter
              (fun A => i ∈ A p ∧ i' ∈ A p ∧ j ∈ A q) with hGdef
            have hFG : F ⊆ G := by
              intro A hA
              obtain ⟨h1, h2, h3, h4⟩ := hmemF A hA
              rw [hGdef, Finset.mem_filter]
              exact ⟨hFsub hA, h1, h3, h2⟩
            have hcount := BoxCount.card_two_one (u := sz c) hszP hpq hii j
            have hGle : #G * (P * (P - 1) * P) ≤ s₀ * sz c p * sz c q * placeCard P sz c := by
              rw [hcount]
              have h5 : sz c p - 1 ≤ s₀ := le_trans (Nat.sub_le _ _) (hs p)
              calc sz c p * (sz c p - 1) * sz c q * placeCard P sz c
                  ≤ sz c p * s₀ * sz c q * placeCard P sz c :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h5))
                _ = s₀ * sz c p * sz c q * placeCard P sz c := by ring
            calc #F * P ^ 3 ≤ #G * (2 * (P * (P - 1) * P)) :=
                  Nat.mul_le_mul (Finset.card_le_card hFG) hPcube
              _ = 2 * (#G * (P * (P - 1) * P)) := by ring
              _ ≤ 2 * (s₀ * sz c p * sz c q * placeCard P sz c) := Nat.mul_le_mul_left _ hGle
              _ = 2 * s₀ * sz c p * sz c q * placeCard P sz c := by ring
        · have hswap : ¬ (p = q' ∧ q = p') := by
            rintro ⟨h1, h2⟩
            have e1 : S = T' := by rw [← hp, h1, hq']
            have e2 : T = S' := by rw [← hq, h2, hp']
            rw [e1, e2] at hlt
            omega
          obtain ⟨t, htp, htq, ht⟩ := zmod3_third p q p' q' hpq hpq' hcase hswap
          have hpt : p ≠ t := Ne.symm htp
          have hqt : q ≠ t := Ne.symm htq
          set z : Fin P := if t = p' then i' else j' with hzdef
          have hzmem : ∀ A ∈ F, z ∈ A t := by
            intro A hA
            obtain ⟨-, -, h3, h4⟩ := hmemF A hA
            by_cases hcase2 : t = p'
            · rw [hzdef, ite_eq_left hcase2, hcase2]
              exact h3
            · rw [hzdef, ite_eq_right hcase2]
              rcases ht with h | h
              · exact absurd h hcase2
              · rw [h]; exact h4
          set G := (BoxCount.plc P (sz c)).filter
            (fun A => i ∈ A p ∧ j ∈ A q ∧ z ∈ A t) with hGdef
          have hFG : F ⊆ G := by
            intro A hA
            obtain ⟨h1, h2, -, -⟩ := hmemF A hA
            rw [hGdef, Finset.mem_filter]
            exact ⟨hFsub hA, h1, h2, hzmem A hA⟩
          have hcount := BoxCount.card_three (u := sz c) hszP hpq hpt hqt i j z
          have hGle : #G * (P * P * P) ≤ s₀ * sz c p * sz c q * placeCard P sz c := by
            rw [hcount]
            calc sz c p * sz c q * sz c t * placeCard P sz c
                ≤ sz c p * sz c q * s₀ * placeCard P sz c :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hs t))
              _ = s₀ * sz c p * sz c q * placeCard P sz c := by ring
          have hcube : P ^ 3 = P * P * P := by ring
          calc #F * P ^ 3 ≤ #G * (P * P * P) := by
                rw [hcube]
                exact Nat.mul_le_mul_right _ (Finset.card_le_card hFG)
            _ ≤ s₀ * sz c p * sz c q * placeCard P sz c := hGle
            _ ≤ 2 * (s₀ * sz c p * sz c q * placeCard P sz c) :=
                Nat.le_mul_of_pos_left _ (by norm_num)
            _ = 2 * s₀ * sz c p * sz c q * placeCard P sz c := by ring
      have hkeyR : (#F : ℝ) * (P : ℝ) ^ 3
          ≤ 2 * (s₀ : ℝ) * (sz c p : ℝ) * (sz c q : ℝ) * (placeCard P sz c : ℝ) := by
        exact_mod_cast hkey
      have hdem : (sz c p : ℝ) * (sz c q : ℝ) ≤ boxDemandC cl sz c S T :=
        sz_mul_le_boxDemandC hp hq
      have hs0 : (0 : ℝ) ≤ (s₀ : ℝ) := Nat.cast_nonneg _
      have hfinal : (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹
          ≤ 2 * (s₀ : ℝ) * ((sz c p : ℝ) * (sz c q : ℝ)) / (P : ℝ) ^ 3 := by
        rw [le_div_iff₀ (by positivity)]
        calc (#F : ℝ) * ((placeCard P sz c : ℝ))⁻¹ * (P : ℝ) ^ 3
            = ((#F : ℝ) * (P : ℝ) ^ 3) * ((placeCard P sz c : ℝ))⁻¹ := by ring
          _ ≤ (2 * (s₀ : ℝ) * (sz c p : ℝ) * (sz c q : ℝ) * (placeCard P sz c : ℝ))
              * ((placeCard P sz c : ℝ))⁻¹ := by
              gcongr
          _ = 2 * (s₀ : ℝ) * ((sz c p : ℝ) * (sz c q : ℝ)) := by
              field_simp
      refine le_trans hfinal ?_
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have hdnn : (0 : ℝ) ≤ boxDemandC cl sz c S T := boxDemandC_nonneg c S T
      have hmain : 2 * (s₀ : ℝ) * ((sz c p : ℝ) * (sz c q : ℝ))
          ≤ 18 * (s₀ : ℝ) * boxDemandC cl sz c S T := by
        linarith only [mul_nonneg hs0 (sub_nonneg.2 hdem), mul_nonneg hs0 hdnn]
      have hP3 : (0 : ℝ) ≤ (P : ℝ) ^ 3 := by positivity
      linarith only [mul_le_mul_of_nonneg_right hmain hP3, hP3]
    · have hempty : F = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
        obtain ⟨u, v, huv, hu, hv, hlt2, -, -⟩ :=
          (mem_placeEdge_inl hidx hcl S' T' i' j').mp (hF2 A hA)
        exact hex' ⟨u, v, huv, hu, hv, hlt2⟩
      rw [hempty]
      simpa using hnn
  · have hempty : F = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨u, v, huv, hu, hv, hlt2, -, -⟩ := (mem_placeEdge_inl hidx hcl S T i j).mp (hF1 A hA)
      exact hex ⟨u, v, huv, hu, hv, hlt2⟩
    rw [hempty]
    simpa using hnn

end PerCopy

/-! ### The loads and the codegrees -/

section Estimates

variable (hidx : Function.Injective idx) (hcl : ∀ c, Function.Injective (cl c))
  (hsz1 : ∀ c a, 1 ≤ sz c a) (hszP : ∀ c a, sz c a ≤ P)

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- The load of a token is exactly `1`. -/
theorem wLoad_inr (c : κ) :
    Slack.wLoad (placeFam P idx cl sz) (placeWt P sz) (Sum.inr c) = 1 := by
  classical
  rw [Slack.wLoad, sum_placeFam_filter hidx hcl hsz1]
  have hterm : ∀ c' : κ,
      ∑ A ∈ (BoxCount.plc P (sz c')).filter
          (fun A => (Sum.inr c : PlaceVtx ι κ P) ∈ placeEdge idx cl c' A),
        placeWt P sz (placeEdge idx cl c' A) = if c' = c then 1 else 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      have hfil : (BoxCount.plc P (sz c')).filter
          (fun A => (Sum.inr c' : PlaceVtx ι κ P) ∈ placeEdge idx cl c' A)
          = BoxCount.plc P (sz c') := by
        refine Finset.filter_true_of_mem fun A _ => ?_
        exact (mem_placeEdge_inr (A := A) (idx := idx) c').mpr rfl
      rw [hfil, ite_eq_left rfl]
      have hpos : 0 < placeCard P sz c' := placeCard_pos hszP c'
      have hposR : (0 : ℝ) < (placeCard P sz c' : ℝ) := by exact_mod_cast hpos
      simp only [placeWt_edge]
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (#(BoxCount.plc P (sz c')) : ℝ) = (placeCard P sz c' : ℝ) := rfl
      rw [this]
      field_simp
    · rw [ite_eq_right hcc]
      refine Finset.sum_eq_zero fun A hA => ?_
      exfalso
      rw [Finset.mem_filter, mem_placeEdge_inr] at hA
      exact hcc hA.2.symm
  rw [Finset.sum_congr rfl (fun c' _ => hterm c'),
    Finset.sum_ite_eq' Finset.univ c (fun _ => (1 : ℝ))]
  simp

include hidx hcl hsz1 in
omit [Fintype ι] in
/-- Only the slots oriented by `idx` are occupied. -/
theorem wLoad_inl_of_not_lt {S T : ι} (h : ¬ idx S < idx T) (i j : Fin P) :
    Slack.wLoad (placeFam P idx cl sz) (placeWt P sz) (Sum.inl (S, T, i, j)) = 0 := by
  classical
  rw [Slack.wLoad, sum_placeFam_filter hidx hcl hsz1]
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun A hA => ?_
  exfalso
  rw [Finset.mem_filter] at hA
  obtain ⟨-, hmem⟩ := hA
  obtain ⟨-, -, -, -, -, hlt, -, -⟩ := (mem_placeEdge_inl hidx (hcl c) S T i j).mp hmem
  exact h hlt

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The load of a slot is at most the normalised demand of its cluster pair.** -/
theorem wLoad_inl_le (hP : 0 < P) (S T : ι) (i j : Fin P) :
    Slack.wLoad (placeFam P idx cl sz) (placeWt P sz) (Sum.inl (S, T, i, j))
      ≤ boxDemand cl sz S T / (P : ℝ) ^ 2 := by
  classical
  rw [Slack.wLoad, sum_placeFam_filter hidx hcl hsz1, boxDemand_eq_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun c _ => ?_
  have hEq : ∑ A ∈ (BoxCount.plc P (sz c)).filter
      (fun A => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A),
      placeWt P sz (placeEdge idx cl c A)
      = ∑ A ∈ (BoxCount.plc P (sz c)).filter
      (fun A => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ placeEdge idx cl c A),
      ((placeCard P sz c : ℝ))⁻¹ :=
    Finset.sum_congr rfl fun A _ => placeWt_edge c A
  rw [hEq]
  exact slot_count_le_demand hidx (hcl c) (fun a => hszP c a) hP S T i j
    (Finset.filter_subset _ _) (fun A hA => (Finset.mem_filter.mp hA).2)

omit [Fintype ι] in
/-- Two tokens are never together in an edge. -/
theorem codeg_inr_inr {c c' : κ} (h : c ≠ c') :
    ∑ U ∈ ((placeFam P idx cl sz).filter (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U)).filter
        (fun U => (Sum.inr c' : PlaceVtx ι κ P) ∈ U),
      placeWt P sz U = 0 := by
  refine Finset.sum_eq_zero fun U hU => ?_
  exfalso
  rw [Finset.mem_filter, Finset.mem_filter] at hU
  obtain ⟨⟨hUK, hc⟩, hc'⟩ := hU
  obtain ⟨d, A, -, rfl⟩ := mem_placeFam hUK
  rw [mem_placeEdge_inr] at hc hc'
  exact h (hc.trans hc'.symm)

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The codegree of a slot and a token** is at most `9 s₀²/P²`. -/
theorem codeg_inl_inr_le (hP : 0 < P) {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) (c : κ) (S T : ι)
    (i j : Fin P) :
    ∑ U ∈ ((placeFam P idx cl sz).filter
          (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter
        (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U),
      placeWt P sz U ≤ 9 * (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 := by
  classical
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [Finset.filter_filter, sum_placeFam_filter hidx hcl hsz1]
  refine le_trans (Finset.sum_le_sum
    (g := fun c' : κ => if c' = c then (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 else 0)
    (fun c' _ => ?_)) ?_
  · change _ ≤ (if c' = c then (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2 else 0)
    by_cases hcc : c' = c
    · subst hcc
      rw [ite_eq_left rfl, Finset.sum_congr rfl (fun A _ => placeWt_edge c' A)]
      refine slot_count_le_sz hidx (hcl c') (fun a => hszP c' a) hP (fun a => hs c' a) S T i j
        ?_ ?_
      · intro A hA
        simp only [Finset.mem_filter] at hA
        exact hA.1
      · intro A hA
        simp only [Finset.mem_filter] at hA
        exact hA.2.1
    · rw [ite_eq_right hcc]
      refine le_of_eq (Finset.sum_eq_zero fun A hA => ?_)
      exfalso
      simp only [Finset.mem_filter] at hA
      obtain ⟨-, -, h2⟩ := hA
      rw [mem_placeEdge_inr] at h2
      exact hcc h2.symm
  · rw [Finset.sum_ite_eq' Finset.univ c (fun _ => (s₀ : ℝ) ^ 2 / (P : ℝ) ^ 2)]
    rw [ite_eq_left (Finset.mem_univ c)]
    have h9 : (0 : ℝ) ≤ (s₀ : ℝ) ^ 2 := sq_nonneg _
    rw [div_le_div_iff_of_pos_right (by positivity)]
    linarith

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **The codegree of two slots** is `O(s₀/P)` times the normalised demand: two placements sharing
two slots are pinned down in one further coordinate.  This is where the small-box restriction is
used. -/
theorem codeg_inl_inl_le (hP : 2 ≤ P) {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) {S T S' T' : ι}
    {i j i' j' : Fin P} (hne : (S, T, i, j) ≠ (S', T', i', j')) :
    ∑ U ∈ ((placeFam P idx cl sz).filter
          (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter
        (fun U => (Sum.inl (S', T', i', j') : PlaceVtx ι κ P) ∈ U),
      placeWt P sz U
      ≤ 18 * (s₀ : ℝ) / (P : ℝ) * (boxDemand cl sz S T / (P : ℝ) ^ 2) := by
  classical
  have hP0 : 0 < P := by omega
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  rw [Finset.filter_filter, sum_placeFam_filter hidx hcl hsz1, boxDemand_eq_sum]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.sum_congr rfl (fun A _ => placeWt_edge c A)]
  refine two_slot_count_le hidx (hcl c) (fun a => hszP c a) hP (fun a => hs c a) hne ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter] at hA
    exact hA.1
  · intro A hA
    simp only [Finset.mem_filter] at hA
    exact hA.2.1
  · intro A hA
    simp only [Finset.mem_filter] at hA
    exact hA.2.2

include hidx hcl hsz1 hszP in
omit [Fintype ι] in
/-- **All weighted codegrees are `O(s₀/P)`.** -/
theorem codeg_le (hP : 2 ≤ P) {s₀ : ℕ} (hs : ∀ c a, sz c a ≤ s₀) (hsP : s₀ ≤ P)
    (hdem : ∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (P : ℝ) ^ 2)
    (x z : PlaceVtx ι κ P) (hxz : x ≠ z) :
    ∑ U ∈ ((placeFam P idx cl sz).filter (fun U => x ∈ U)).filter (fun U => z ∈ U),
      placeWt P sz U ≤ 18 * (s₀ : ℝ) / (P : ℝ) := by
  classical
  have hP0 : 0 < P := by omega
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hsPR : (s₀ : ℝ) ≤ (P : ℝ) := by exact_mod_cast hsP
  have hs0R : (0 : ℝ) ≤ (s₀ : ℝ) := Nat.cast_nonneg _
  have hslotzero : ∀ (S T : ι) (i j : Fin P), ¬ idx S < idx T →
      ∀ (p : Finset (PlaceVtx ι κ P) → Prop) [DecidablePred p],
      ∑ U ∈ ((placeFam P idx cl sz).filter
          (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter p,
        placeWt P sz U = 0 := by
    intro S T i j hlt p _
    refine Finset.sum_eq_zero fun U hU => ?_
    exfalso
    rw [Finset.mem_filter, Finset.mem_filter] at hU
    obtain ⟨⟨hUK, hmem⟩, -⟩ := hU
    obtain ⟨c, A, -, rfl⟩ := mem_placeFam hUK
    obtain ⟨-, -, -, -, -, hlt2, -, -⟩ := (mem_placeEdge_inl hidx (hcl c) S T i j).mp hmem
    exact hlt hlt2
  match x, z with
  | Sum.inr c, Sum.inr c' =>
      have hcc : c ≠ c' := fun h => hxz (by rw [h])
      rw [codeg_inr_inr hcc]
      positivity
  | Sum.inl (S, T, i, j), Sum.inr c =>
      refine le_trans (codeg_inl_inr_le hidx hcl hsz1 hszP hP0 hs c S T i j) ?_
      rw [div_le_div_iff₀ (by positivity) hPR]
      nlinarith only [hs0R, hsPR, hPR, mul_nonneg hs0R (le_of_lt hPR),
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsPR hs0R) (le_of_lt hPR)]
  | Sum.inr c, Sum.inl (S, T, i, j) =>
      have hset : ((placeFam P idx cl sz).filter
            (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U)).filter
              (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)
          = ((placeFam P idx cl sz).filter
            (fun U => (Sum.inl (S, T, i, j) : PlaceVtx ι κ P) ∈ U)).filter
              (fun U => (Sum.inr c : PlaceVtx ι κ P) ∈ U) := by
        ext U
        simp only [Finset.mem_filter]
        tauto
      rw [hset]
      refine le_trans (codeg_inl_inr_le hidx hcl hsz1 hszP hP0 hs c S T i j) ?_
      rw [div_le_div_iff₀ (by positivity) hPR]
      nlinarith only [hs0R, hsPR, hPR, mul_nonneg hs0R (le_of_lt hPR),
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsPR hs0R) (le_of_lt hPR)]
  | Sum.inl (S, T, i, j), Sum.inl (S', T', i', j') =>
      have hne : (S, T, i, j) ≠ (S', T', i', j') := by
        intro h
        exact hxz (by rw [h])
      by_cases hlt : idx S < idx T
      · have hST : S ≠ T := by
          intro h
          rw [h] at hlt
          exact lt_irrefl _ hlt
        refine le_trans (codeg_inl_inl_le hidx hcl hsz1 hszP hP hs hne) ?_
        have hdd : boxDemand cl sz S T / (P : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hdem S T hST
        have hfac : (0 : ℝ) ≤ 18 * (s₀ : ℝ) / (P : ℝ) := by positivity
        nlinarith only [hdd, hfac]
      · rw [hslotzero S T i j hlt]
        positivity

end Estimates

end BoxPlace

end Nibble.AX1

end


/-! # Weighted nibble for box placement -/

public section

open Finset

namespace Nibble.AX1

namespace BoxPlace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {P : ℕ}
  {cl : κ → ZMod 3 → ι} {sz : κ → ZMod 3 → ℕ}

omit [DecidableEq κ] in
/-- **There are not too many copies.**  Every copy demands at least one cell pair in the cluster
pair of its first two clusters, so the number of copies is at most the total capacity. -/
theorem card_copies_le {ε : ℝ} (hε0 : 0 ≤ ε) (hcl : ∀ c, Function.Injective (cl c))
    (hsz1 : ∀ c a, 1 ≤ sz c a)
    (hdem : ∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (1 - ε) * (P : ℝ) ^ 2) :
    (Fintype.card κ : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
  classical
  have hfib : ∀ p : ι × ι,
      ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = p)).card : ℝ) ≤ (P : ℝ) ^ 2 := by
    rintro ⟨S, T⟩
    by_cases hex : ∃ c : κ, (cl c 0, cl c 1) = (S, T)
    · obtain ⟨c0, hc0⟩ := hex
      have hST : S ≠ T := by
        intro h
        have e0 : cl c0 0 = S := congrArg Prod.fst hc0
        have e1 : cl c0 1 = T := congrArg Prod.snd hc0
        have h01 : (0 : ZMod 3) = 1 := hcl c0 (by rw [e0, e1, h])
        exact absurd h01 (by decide +kernel)
      have hstep : ∀ c ∈ Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)),
          (1 : ℝ) ≤ boxDemandC cl sz c S T := by
        intro c hc
        rw [Finset.mem_filter] at hc
        have e0 : cl c 0 = S := congrArg Prod.fst hc.2
        have e1 : cl c 1 = T := congrArg Prod.snd hc.2
        have a0 : (1 : ℝ) ≤ (sz c 0 : ℝ) := by exact_mod_cast hsz1 c 0
        have a1 : (1 : ℝ) ≤ (sz c 1 : ℝ) := by exact_mod_cast hsz1 c 1
        have h01 : (1 : ℝ) ≤ (sz c 0 : ℝ) * (sz c 1 : ℝ) := by nlinarith
        exact le_trans h01 (sz_mul_le_boxDemandC e0 e1)
      have hle : ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T))).card : ℝ)
          ≤ boxDemand cl sz S T := by
        rw [boxDemand_eq_sum]
        calc ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T))).card : ℝ)
            = ∑ _c ∈ Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)), (1 : ℝ) := by
              simp
          _ ≤ ∑ c ∈ Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)),
              boxDemandC cl sz c S T := Finset.sum_le_sum hstep
          _ ≤ ∑ c : κ, boxDemandC cl sz c S T :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun c _ _ => boxDemandC_nonneg c S T)
      refine le_trans hle (le_trans (hdem S T hST) ?_)
      nlinarith [sq_nonneg (P : ℝ)]
    · push Not at hex
      have hemp : Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
        rw [Finset.mem_filter] at hc
        exact hex c hc.2
      rw [hemp]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hcard : Fintype.card κ
      = ∑ p : ι × ι, (Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = p)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun c _ => Finset.mem_univ _)
  rw [hcard]
  push_cast
  calc ∑ p : ι × ι, ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = p)).card : ℝ)
      ≤ ∑ _p : ι × ι, (P : ℝ) ^ 2 := Finset.sum_le_sum fun p _ => hfib p
    _ = (Fintype.card (ι × ι) : ℝ) * (P : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
        rw [Fintype.card_prod]
        push_cast
        ring

/-- The default allocation of a copy: an initial segment of the cells of the right size. -/
def defaultAlloc (P : ℕ) (sz : κ → ZMod 3 → ℕ) (hszP : ∀ c a, sz c a ≤ P) (c : κ) :
    ZMod 3 → Finset (Fin P) :=
  fun a =>
    (Finset.range (sz c a)).attachFin (fun _ hm => lt_of_lt_of_le (mem_range.mp hm) (hszP c a))

omit [Fintype κ] [DecidableEq κ] in
theorem defaultAlloc_mem (hszP : ∀ c a, sz c a ≤ P) (c : κ) :
    defaultAlloc P sz hszP c ∈ BoxCount.plc P (sz c) := by
  rw [BoxCount.mem_plc]
  intro a
  simp [defaultAlloc]

end BoxPlace

open BoxPlace

private theorem bad_area_le {κ : Type} [Fintype κ] [DecidableEq κ]
    (sz : κ → ZMod 3 → ℕ) (good : Finset κ) (s₀ P n : ℕ) (ε β C θ : ℝ)
    (hs : ∀ c a, sz c a ≤ s₀) (hs₀ : (0 : ℝ) < (s₀ : ℝ))
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθC : θ ≤ ε / (6 * C))
    (hsP : (s₀ : ℝ) ≤ θ * (P : ℝ)) (hn : (1 : ℝ) ≤ (n : ℝ))
    (hC : 0 < C) (hε : 0 < ε) (hβ : β = ε / (18 * (s₀ : ℝ) ^ 2))
    (hbad : ((Finset.univ \ good).card : ℝ)
      ≤ 3 * β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + C) :
    (∑ c ∈ Finset.univ \ good, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
      ≤ ε * (n : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
  have harea : (∑ c ∈ Finset.univ \ good, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
      ≤ ((Finset.univ \ good).card : ℝ) * (3 * (s₀ : ℝ) ^ 2) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro c _
    have hb : ∀ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ) ≤ (s₀ : ℝ) ^ 2 := by
      intro a
      have h1 : (sz c a : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs c a
      have h2 : (sz c (a + 1) : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs c (a + 1)
      have h3 : (0 : ℝ) ≤ (sz c a : ℝ) := Nat.cast_nonneg _
      have h4 : (0 : ℝ) ≤ (sz c (a + 1) : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ)
        ≤ ∑ _a : ZMod 3, (s₀ : ℝ) ^ 2 := Finset.sum_le_sum (fun a _ => hb a)
      _ = 3 * (s₀ : ℝ) ^ 2 := by simp [ZMod.card]
  refine le_trans harea ?_
  have hs₀ne : (s₀ : ℝ) ≠ 0 := ne_of_gt hs₀
  have hCpos : (0 : ℝ) < 6 * C := by linarith
  have h2a : θ * θ ≤ θ * (ε / (6 * C)) := mul_le_mul_of_nonneg_left hθC hθ.le
  have h2b : θ * (ε / (6 * C)) ≤ 1 * (ε / (6 * C)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : θ ^ 2 ≤ ε / (6 * C) := by linarith only [h2a, h2b]
  have h1 : (s₀ : ℝ) * (s₀ : ℝ) ≤ (θ * (P : ℝ)) * (θ * (P : ℝ)) :=
    mul_self_le_mul_self hs₀.le hsP
  have h1' : (s₀ : ℝ) ^ 2 ≤ θ ^ 2 * (P : ℝ) ^ 2 := by linarith only [h1]
  have hst : (s₀ : ℝ) ^ 2 ≤ ε / (6 * C) * (P : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right h2 (sq_nonneg (P : ℝ))
    linarith only [h1', hmul]
  have h3 : 3 * (s₀ : ℝ) ^ 2 * C ≤ 3 * (ε / (6 * C) * (P : ℝ) ^ 2) * C := by
    have hmul := mul_le_mul_of_nonneg_right hst hC.le
    linarith only [hmul]
  have h4 : 3 * (ε / (6 * C) * (P : ℝ) ^ 2) * C = ε / 2 * (P : ℝ) ^ 2 := by
    field_simp; ring
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn]
  have h5 : (P : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
    nlinarith only [hn2, sq_nonneg (P : ℝ)]
  have hkey : 3 * (s₀ : ℝ) ^ 2 * C ≤ ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ ε / 2)
    linarith only [h3, h4, hmul]
  have hβs : 3 * β * (3 * (s₀ : ℝ) ^ 2) = ε / 2 := by
    rw [hβ]; field_simp; ring
  calc ((Finset.univ \ good).card : ℝ) * (3 * (s₀ : ℝ) ^ 2)
      ≤ (3 * β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + C) * (3 * (s₀ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hbad (by positivity)
    _ = (3 * β * (3 * (s₀ : ℝ) ^ 2)) * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2)
        + 3 * (s₀ : ℝ) ^ 2 * C := by ring
    _ = ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + 3 * (s₀ : ℝ) ^ 2 * C := by rw [hβs]
    _ ≤ ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) := by
        linarith only [hkey]
    _ = ε * (n : ℝ) ^ 2 * (P : ℝ) ^ 2 := by ring

/-- **The small-box allocation residual, for a fixed accuracy and a fixed box bound.** -/
theorem boxAllocationResidual_main (ε : ℝ) (hε : 0 < ε) (s₀ : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∀ P : ℕ, 0 < P → (s₀ : ℝ) ≤ θ * (P : ℝ) →
      ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ),
        (∀ c, Function.Injective (cl c)) →
        (∀ c a, 1 ≤ sz c a) → (∀ c a, sz c a ≤ s₀) →
        (∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (1 - ε) * (P : ℝ) ^ 2) →
        ∃ (bad : Finset κ) (I : κ → ZMod 3 → Finset (Fin P)),
          (∀ c a, #(I c a) = sz c a) ∧
          (∀ c ∉ bad, ∀ c' ∉ bad, c ≠ c' → ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' →
            cl c a = cl c' a' → cl c b = cl c' b' →
            Disjoint (I c a) (I c' a') ∨ Disjoint (I c b) (I c' b')) ∧
          (∑ c ∈ bad, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
            ≤ ε * (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos s₀ with hs0 | hs0
  · -- no copies at all
    refine ⟨1, one_pos, le_rfl, ?_⟩
    intro P hP hsP ι κ _ _ _ _ cl sz hcl hsz1 hs hdem
    have hempty : IsEmpty κ := ⟨fun c => by have h1 := hsz1 c 0; have h2 := hs c 0; omega⟩
    refine ⟨∅, fun c => hempty.elim c, fun c => hempty.elim c,
      fun c _ => hempty.elim c, ?_⟩
    simp only [Finset.sum_empty]
    positivity
  · -- the main case
    have hs0R : (0 : ℝ) < (s₀ : ℝ) := by exact_mod_cast hs0
    have hs1R : (1 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs0
    obtain ⟨γ, hγ, C, hC, hnib⟩ :=
      fracNibble_leUniform (1 + 3 * s₀ ^ 2) (by nlinarith only [hs0]) (ε / (18 * (s₀ : ℝ) ^ 2))
        (by positivity)
    set β : ℝ := ε / (18 * (s₀ : ℝ) ^ 2) with hβdef
    have hβ : 0 < β := by rw [hβdef]; positivity
    refine ⟨min (1 / 2) (min (γ / 18) (ε / (6 * C))), lt_min (by norm_num)
      (lt_min (by positivity) (by positivity)),
      le_trans (min_le_left _ _) (by norm_num), ?_⟩
    set θ : ℝ := min (1 / 2) (min (γ / 18) (ε / (6 * C))) with hθdef
    have hθ12 : θ ≤ 1 / 2 := min_le_left _ _
    have hθγ : θ ≤ γ / 18 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hθC : θ ≤ ε / (6 * C) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hθ0 : 0 < θ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    intro P hP hsP ι κ _ _ _ _ cl sz hcl hsz1 hs hdem
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    -- `P` is large
    have h2PR : (2 : ℝ) ≤ (P : ℝ) := by nlinarith only [hsP, hθ12, hs1R, hPR]
    have h2P : 2 ≤ P := by exact_mod_cast h2PR
    have hs0P : s₀ ≤ P := by
      have : (s₀ : ℝ) ≤ (P : ℝ) := by nlinarith only [hsP, hθ12, hPR]
      exact_mod_cast this
    have hszP : ∀ c a, sz c a ≤ P := fun c a => le_trans (hs c a) hs0P
    -- an injective indexing of the clusters
    set idx : ι → ℕ := fun S => ((Fintype.equivFin ι S : Fin (Fintype.card ι)) : ℕ) with hidxdef
    have hidx : Function.Injective idx := by
      intro S T h
      have : (Fintype.equivFin ι) S = (Fintype.equivFin ι) T := by
        apply Fin.ext; exact h
      exact (Fintype.equivFin ι).injective this
    set n : ℕ := Fintype.card ι with hndef
    set K := placeFam P idx cl sz with hKdef
    set w : Finset (PlaceVtx ι κ P) → ℝ := placeWt P sz with hwdef
    have hdemP : ∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (P : ℝ) ^ 2 := by
      intro S T hST
      refine le_trans (hdem S T hST) ?_
      nlinarith [sq_nonneg (P : ℝ)]
    -- the hypotheses of the nibble
    have hedge : ∀ U ∈ K, U.Nonempty ∧ #U ≤ 1 + 3 * s₀ ^ 2 :=
      fun U hU => placeFam_edge_size hcl hs U hU
    have hw0 : ∀ U, 0 ≤ w U := fun U => placeWt_nonneg U
    have hload : ∀ v : PlaceVtx ι κ P, Slack.wLoad K w v ≤ 1 := by
      rintro (⟨S, T, i, j⟩ | c)
      · by_cases hlt : idx S < idx T
        · have hST : S ≠ T := by
            intro h; rw [h] at hlt; exact lt_irrefl _ hlt
          refine le_trans (wLoad_inl_le hidx hcl hsz1 hszP hP S T i j) ?_
          rw [div_le_one (by positivity)]
          exact hdemP S T hST
        · rw [wLoad_inl_of_not_lt hidx hcl hsz1 hlt]; norm_num
      · rw [wLoad_inr hidx hcl hsz1 hszP]
    have hbound : 18 * (s₀ : ℝ) / (P : ℝ) ≤ γ := by
      have hsθ : (s₀ : ℝ) / (P : ℝ) ≤ θ := by
        rw [div_le_iff₀ hPR]; linarith only [hsP]
      calc 18 * (s₀ : ℝ) / (P : ℝ) = 18 * ((s₀ : ℝ) / (P : ℝ)) := by ring
        _ ≤ 18 * θ := by linarith
        _ ≤ γ := by linarith only [hθγ]
    obtain ⟨M, hM, hMcard⟩ := hnib K w hedge hw0 hload (by
      intro x z hxz
      refine le_trans (le_of_eq ?_)
        (le_trans (codeg_le hidx hcl hsz1 hszP h2P hs hs0P hdemP x z hxz) hbound)
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext U
      simp only [Finset.mem_filter]
      tauto)
    -- the copies that the matching places
    set good : Finset κ := M.biUnion Finset.toRight with hgooddef
    have htoRight : ∀ U ∈ M, ∃ c : κ, U.toRight = {c} := by
      intro U hU
      obtain ⟨c, A, -, rfl⟩ := mem_placeFam (hM.subset hU)
      exact ⟨c, placeEdge_toRight⟩
    have hpwd : ∀ U ∈ M, ∀ V ∈ M, U ≠ V → Disjoint U.toRight V.toRight := by
      intro U hU V hV hUV
      obtain ⟨c, hc⟩ := htoRight U hU
      obtain ⟨d, hd⟩ := htoRight V hV
      rw [hc, hd, Finset.disjoint_singleton]
      intro hcd
      subst hcd
      have hdisj := hM.disjoint U hU V hV hUV
      have hcU : (Sum.inr c : PlaceVtx ι κ P) ∈ U := by
        have : c ∈ U.toRight := by rw [hc]; exact Finset.mem_singleton_self c
        rwa [Finset.mem_toRight] at this
      have hcV : (Sum.inr c : PlaceVtx ι κ P) ∈ V := by
        have : c ∈ V.toRight := by rw [hd]; exact Finset.mem_singleton_self c
        rwa [Finset.mem_toRight] at this
      exact absurd hcV (Finset.disjoint_left.mp hdisj hcU)
    have hgoodcard : #good = #M := by
      have hcb := Finset.card_biUnion (s := M) (t := fun U : Finset (PlaceVtx ι κ P) => U.toRight)
        (fun U hU V hV hUV => hpwd U hU V hV hUV)
      rw [hgooddef, hcb]
      rw [Finset.sum_congr rfl (fun U hU => ?_), Finset.sum_const, smul_eq_mul, mul_one]
      obtain ⟨c, hc⟩ := htoRight U hU
      change #U.toRight = 1
      rw [hc, Finset.card_singleton]
    -- the placement of each copy
    have hchoice : ∀ c : κ, ∃ A : ZMod 3 → Finset (Fin P), A ∈ BoxCount.plc P (sz c) ∧
        (c ∈ good → placeEdge idx cl c A ∈ M) := by
      intro c
      by_cases hc : c ∈ good
      · rw [hgooddef, Finset.mem_biUnion] at hc
        obtain ⟨U, hU, hcU⟩ := hc
        obtain ⟨c', A, hA, rfl⟩ := mem_placeFam (hM.subset hU)
        have : c = c' := by
          have := placeEdge_toRight (idx := idx) (cl := cl) (c := c') (A := A)
          rw [this, Finset.mem_singleton] at hcU
          exact hcU
        subst this
        exact ⟨A, hA, fun _ => hU⟩
      · exact ⟨defaultAlloc P sz hszP c, defaultAlloc_mem hszP c, fun h => absurd h hc⟩
    choose A hAmem hAM using hchoice
    have hAcard : ∀ c a, #(A c a) = sz c a := fun c a => (BoxCount.mem_plc.mp (hAmem c)) a
    have hAne : ∀ c a, (A c a).Nonempty := by
      intro c a
      rw [← Finset.card_pos, hAcard]
      exact hsz1 c a
    refine ⟨Finset.univ \ good, A, hAcard, ?_, ?_⟩
    · -- the rectangles of two placed copies are disjoint
      intro c hc c' hc' hcc a b a' b' hab ha'b' hSa hSb
      have hcg : c ∈ good := by
        by_contra h
        exact hc (Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, h⟩)
      have hcg' : c' ∈ good := by
        by_contra h
        exact hc' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ c', h⟩)
      have hE : placeEdge idx cl c (A c) ∈ M := hAM c hcg
      have hE' : placeEdge idx cl c' (A c') ∈ M := hAM c' hcg'
      have hEne : placeEdge idx cl c (A c) ≠ placeEdge idx cl c' (A c') := by
        intro h
        exact hcc (placeEdge_inj hidx (hcl c) (hcl c') (hAne c) (hAne c') h).1
      have hdisj := hM.disjoint _ hE _ hE' hEne
      by_contra hcon
      push Not at hcon
      obtain ⟨hd1, hd2⟩ := hcon
      obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp hd1
      obtain ⟨j, hj, hj'⟩ := Finset.not_disjoint_iff.mp hd2
      have hmem : (Sum.inl (orient idx (cl c a) (cl c b) i j) : PlaceVtx ι κ P)
          ∈ placeEdge idx cl c (A c) := mem_placeEdge_orient hidx (hcl c) hab hi hj
      have hmem' : (Sum.inl (orient idx (cl c a) (cl c b) i j) : PlaceVtx ι κ P)
          ∈ placeEdge idx cl c' (A c') := by
        have : orient idx (cl c a) (cl c b) i j = orient idx (cl c' a') (cl c' b') i j := by
          rw [hSa, hSb]
        rw [this]
        exact mem_placeEdge_orient hidx (hcl c') ha'b' hi' hj'
      exact (Finset.disjoint_left.mp hdisj hmem) hmem'
    · -- the copies left out have small total area
      rcases isEmpty_or_nonempty κ with hκ | hκ
      · have : (Finset.univ : Finset κ) \ good = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro c _
          exact hκ.elim c
        rw [this, Finset.sum_empty]
        positivity
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
          have : 0 < n := by
            rw [hndef]
            exact Fintype.card_pos_iff.mpr ⟨cl hκ.some 0⟩
          exact_mod_cast this
        -- the number of unplaced copies
        have hbadcard : ((Finset.univ \ good).card : ℝ) = (Fintype.card κ : ℝ) - (#M : ℝ) := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hgoodcard]
          have hMle : #M ≤ Fintype.card κ := by
            rw [← hgoodcard, ← Finset.card_univ]
            exact Finset.card_le_card (Finset.subset_univ _)
          rw [Finset.card_univ, Nat.cast_sub hMle]
        have hsumw : ∑ U ∈ K, w U = (Fintype.card κ : ℝ) := sum_placeWt hidx hcl hsz1 hszP
        have hX : (Fintype.card (PlaceVtx ι κ P) : ℝ)
            = (n : ℝ) ^ 2 * (P : ℝ) ^ 2 + (Fintype.card κ : ℝ) := by
          simp only [PlaceVtx, Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hndef]
          push_cast
          ring
        have hκle : (Fintype.card κ : ℝ) ≤ (n : ℝ) ^ 2 * (P : ℝ) ^ 2 :=
          card_copies_le hε.le hcl hsz1 hdem
        rw [hsumw, hX] at hMcard
        -- so the number of unplaced copies is at most `3β n²P² + C`
        have hbad : ((Finset.univ \ good).card : ℝ)
            ≤ 3 * β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + C := by
          have hmul : β * (Fintype.card κ : ℝ) ≤ β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hκle hβ.le
          have hexp : (1 - β) * (Fintype.card κ : ℝ)
              - β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2 + (Fintype.card κ : ℝ)) - C
              = (Fintype.card κ : ℝ) - 2 * (β * (Fintype.card κ : ℝ))
                - β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) - C := by ring
          rw [hexp] at hMcard
          rw [hbadcard]
          linarith only [hMcard, hmul]
        -- each unplaced copy has area at most `3s₀²`
        exact bad_area_le sz good s₀ P n ε β C θ hs hs0R hθ0 (by linarith) hθC hsP hn1 hC hε
          hβdef hbad

/-- **The small-box allocation residual.** -/
theorem boxAllocationResidual_holds : BoxAllocationResidual :=
  fun ε hε s₀ => boxAllocationResidual_main ε hε s₀

end Nibble.AX1

end


/-! # Unconditional AX1 -/

public section

namespace Nibble.AX1

/-- The coupled block-cover residual follows from the closed box-allocation theorem. -/
theorem blockCoverResidualCoupled_holds : BlockCoverResidualCoupled :=
  blockCoverResidualCoupled_of_boxAllocation boxAllocationResidual_holds

/-- The cover-side AX1 statement holds for every graph. -/
theorem ax1Statement_holds : AX1Statement :=
  ax1_of_boxAllocation boxAllocationResidual_holds

/-- The fractional–integral triangle-packing gap is uniformly `o(n²)`. -/
theorem nibbleGapHyp_holds : NibbleGapHyp :=
  nibbleGapHyp_of_ax1 ax1Statement_holds

end Nibble.AX1

end




/-!
# Finite near-regular hypergraph rounding: basic statement

The public statement records the finite near-regular hypergraph rounding interface used by
the nibble method. The underlying finite definitions are kept in the internal library.
-/

public section

namespace LeanPool.AsymptoticTrianglePacking

/-- The finite ceiling-carrying nibble interface for near-regular hypergraphs. -/
abbrev NearRegularNibbleTheorem : Prop :=
  Internal.NibbleTheoremMostCeil

end LeanPool.AsymptoticTrianglePacking

end


/-!
# Nibble rounding infrastructure

This module makes the ceiling-carrying finite nibble interface available to the final assembly.
The full development remains internal so that the public API is limited to stable theorem-level
statements.
-/

public section

namespace LeanPool.AsymptoticTrianglePacking

/-- The finite nibble-rounding theorem in the public interface. -/
theorem nearRegularNibbleTheorem : NearRegularNibbleTheorem :=
  Internal.nibbleTheoremMostCeil_holds

end LeanPool.AsymptoticTrianglePacking

end


/-!
# Finite near-regular hypergraph rounding

Public entry point for the finite, ceiling-carrying near-regular hypergraph nibble theorem.
-/

public section

namespace LeanPool.AsymptoticTrianglePacking

/-- The fractional and integral triangle-packing optima differ by `o(n²)`, uniformly over finite
graphs. -/
theorem trianglePackingGap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
          ε * (Fintype.card V : ℝ) ^ 2 :=
  Nibble.AX1.nibbleGapHyp_holds ε hε

/-- The fractional triangle-cover optimum exceeds the integral triangle-packing optimum by at
most `o(n²)`, uniformly over finite graphs. -/
theorem triangleCoverPackingGap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        Nibble.AX1.tau3Star G - (Nibble.YusterE.nu3 G : ℝ) ≤
          ε * (Fintype.card V : ℝ) ^ 2 :=
  Nibble.AX1.ax1Statement_holds ε hε

end LeanPool.AsymptoticTrianglePacking
