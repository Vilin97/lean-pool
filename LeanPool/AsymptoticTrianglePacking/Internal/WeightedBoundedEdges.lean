/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the weighted nibble for hypergraphs of **bounded** edge size

`Nibble.fracNibbleR_withSlack` (`Nibble.FracNibbleSlackR`) needs an exactly `(k+1)`-uniform
hypergraph.  The placement hypergraph of the box-allocation nibble is *not* uniform: the edge of a
placement of a copy `c` occupies one token plus the `∑_a sz(c,a)·sz(c,a+1)` cell slots of its three
rectangles, and that number varies with `c`.  All edges are however nonempty and of size at most
`r`, and this file removes the uniformity hypothesis under exactly that assumption.

The padding.  Put `r` *columns* of `m` dummies each and, for an edge `T` of size `t`, attach to `T`
one dummy from each of the first `r - t` columns; the weight `w T` is spread uniformly over the
`m^(r-t)` choices.  Then

* the padded family is exactly `r`-uniform;
* the load of a real vertex is unchanged, that of a dummy of column `j` is
  `(∑_{T : r - #T > j} w T)/m ≤ (∑_T w T)/m ≤ 1` as soon as `m ≥ ∑_T w T`;
* the weighted codegree of two real vertices is unchanged, that of a real vertex and a dummy is at
  most `1/m`, that of two dummies of the same column is `0` and of two dummies of different columns
  at most `(∑_T w T)/m² ≤ 1/m`;
* the total weight is unchanged, and the total slack is between `r·(m - ∑_T w T)` and
  `|X| + r·m ≤ (1+r)|X| + r(1/γ + 3)`;
* a matching of the padded family projects to a matching of `K` of the same size, because two
  padded edges coming from the same `T` meet in `T` (nonempty).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.NearRegularNibble
public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus






/-! # Fractional rounding with bounded incidence discrepancy -/

public section

open Finset

namespace Nibble.BeckFiala

variable {V : Type*} [DecidableEq V]

/-- The **floating** edges of a fractional selection: those whose value is neither `0` nor `1`. -/
noncomputable def floating (H : Finset (Finset V)) (y : Finset V → ℝ) : Finset (Finset V) :=
  H.filter (fun t => y t ≠ 0 ∧ y t ≠ 1)

omit [DecidableEq V] in
theorem floating_subset (H : Finset (Finset V)) (y : Finset V → ℝ) : floating H y ⊆ H :=
  Finset.filter_subset _ _

omit [DecidableEq V] in
theorem notMem_floating_iff {H : Finset (Finset V)} {y : Finset V → ℝ} {t : Finset V}
    (ht : t ∈ H) : t ∉ floating H y ↔ y t = 0 ∨ y t = 1 := by
  unfold floating
  simp only [Finset.mem_filter, ht, true_and, not_and_or, not_not]

/-- The **active** vertices of a floating set: those meeting more than `k` floating edges. -/
noncomputable def active (F : Finset (Finset V)) (k : ℕ) : Finset V :=
  (F.biUnion id).filter (fun x => k < (F.filter (fun t => x ∈ t)).card)

theorem mem_active_iff {F : Finset (Finset V)} {k : ℕ} {x : V} :
    x ∈ active F k ↔ k < (F.filter (fun t => x ∈ t)).card := by
  unfold active
  simp only [Finset.mem_filter, Finset.mem_biUnion, id]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) h)
    rw [Finset.mem_filter] at ht
    exact ⟨t, ht.1, ht.2⟩

/-- **Few active vertices.**  If every edge of the floating family meets at most `k` vertices and
the family is nonempty, then there are strictly fewer active vertices than floating edges. -/
theorem card_active_lt {F : Finset (Finset V)} {k : ℕ} (hk : ∀ t ∈ F, t.card ≤ k)
    (hF : F.Nonempty) : (active F k).card < F.card := by
  have hcount : ∑ x ∈ active F k, (F.filter (fun t => x ∈ t)).card
      ≤ ∑ t ∈ F, ((active F k).filter (fun x => x ∈ t)).card := by
    have h1 : ∀ x : V, (F.filter (fun t => x ∈ t)).card
        = ∑ t ∈ F, if x ∈ t then 1 else 0 := by
      intro x; rw [Finset.card_filter]
    have h2 : ∀ t : Finset V, ((active F k).filter (fun x => x ∈ t)).card
        = ∑ x ∈ active F k, if x ∈ t then 1 else 0 := by
      intro t; rw [Finset.card_filter]
    simp only [h1, h2]
    rw [Finset.sum_comm]
  have hle : ∑ t ∈ F, ((active F k).filter (fun x => x ∈ t)).card ≤ F.card * k := by
    calc ∑ t ∈ F, ((active F k).filter (fun x => x ∈ t)).card
        ≤ ∑ t ∈ F, k := by
          refine Finset.sum_le_sum fun t ht => ?_
          refine le_trans (Finset.card_le_card ?_) (hk t ht)
          intro x hx
          exact (Finset.mem_filter.mp hx).2
      _ = F.card * k := by rw [Finset.sum_const, smul_eq_mul]
  have hlow : (active F k).card * (k + 1) ≤ ∑ x ∈ active F k, (F.filter (fun t => x ∈ t)).card := by
    calc (active F k).card * (k + 1) = ∑ _x ∈ active F k, (k + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ active F k, (F.filter (fun t => x ∈ t)).card :=
          Finset.sum_le_sum fun x hx => mem_active_iff.mp hx
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  nlinarith [hcount, hle, hlow]

/-- Existence of a nonzero vector annihilated by all active constraints. -/
theorem exists_kernel_vector {F : Finset (Finset V)} {k : ℕ} (hk : ∀ t ∈ F, t.card ≤ k)
    (hF : F.Nonempty) :
    ∃ U : Finset V → ℝ, (∀ t, t ∉ F → U t = 0) ∧ (∃ t ∈ F, U t ≠ 0) ∧
      ∀ x ∈ active F k, ∑ t ∈ F.filter (fun t => x ∈ t), U t = 0 := by
  set A : Finset V := active F k with hA
  have hcard : Fintype.card {x // x ∈ A} < Fintype.card {t // t ∈ F} := by
    simpa [Fintype.card_coe] using card_active_lt hk hF
  -- the constraint map
  let φ : ({t // t ∈ F} → ℝ) →ₗ[ℝ] ({x // x ∈ A} → ℝ) :=
    { toFun := fun u x => ∑ t : {t // t ∈ F}, if (x : V) ∈ (t : Finset V) then u t else 0
      map_add' := by
        intro u v
        funext x
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ => by by_cases h : (x : V) ∈ (t : Finset V) <;> simp [h]
      map_smul' := by
        intro c u
        funext x
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by
          by_cases h : (x : V) ∈ (t : Finset V) <;> simp [h] }
  have hker : ∃ u : {t // t ∈ F} → ℝ, u ≠ 0 ∧ φ u = 0 := by
    by_contra hc
    push Not at hc
    have hinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro m hm
      by_contra hm0
      exact (hc m hm0 hm).elim
    have := LinearMap.finrank_le_finrank_of_injective (f := φ) hinj
    simp only [Module.finrank_fintype_fun_eq_card] at this
    omega
  obtain ⟨u, hu0, huker⟩ := hker
  refine ⟨fun t => if h : t ∈ F then u ⟨t, h⟩ else 0, ?_, ?_, ?_⟩
  · intro t ht; simp [ht]
  · by_contra hcon
    push Not at hcon
    apply hu0
    funext t
    have := hcon t.1 t.2
    simpa using this
  · intro x hx
    have hker0 := congrFun huker ⟨x, hx⟩
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hker0
    change ∑ t ∈ F.filter (fun t => x ∈ t), (if h : t ∈ F then u ⟨t, h⟩ else 0) = 0
    calc ∑ t ∈ F.filter (fun t => x ∈ t), (if h : t ∈ F then u ⟨t, h⟩ else 0)
        = ∑ t : {t // t ∈ F}, (if (x : V) ∈ (t : Finset V) then u t else 0) := by
          rw [Finset.sum_filter, ← Finset.sum_coe_sort F
            (fun s => if x ∈ s then (if h : s ∈ F then u ⟨s, h⟩ else 0) else 0)]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases h : (x : V) ∈ (t : Finset V) <;> simp [h, t.2]
      _ = 0 := hker0

/-- **One rounding step.**  Given a fractional selection with a nonempty floating set, there is
another one with strictly fewer floating edges, which agrees with the old one off the floating set
and has exactly the same degree at every active vertex. -/
theorem exists_step (k : ℕ) (H : Finset (Finset V)) (hk : ∀ t ∈ H, t.card ≤ k)
    (y : Finset V → ℝ) (hy0 : ∀ t ∈ H, 0 ≤ y t) (hy1 : ∀ t ∈ H, y t ≤ 1)
    (hF : (floating H y).Nonempty) :
    ∃ y' : Finset V → ℝ, (∀ t ∈ H, 0 ≤ y' t) ∧ (∀ t ∈ H, y' t ≤ 1) ∧
      (∀ t, t ∉ floating H y → y' t = y t) ∧
      (floating H y').card < (floating H y).card ∧
      (∀ x : V, k < ((floating H y).filter (fun t => x ∈ t)).card →
        ∑ t ∈ H.filter (fun t => x ∈ t), y' t = ∑ t ∈ H.filter (fun t => x ∈ t), y t) := by
  set F := floating H y with hFdef
  have hFH : F ⊆ H := floating_subset H y
  have hkF : ∀ t ∈ F, t.card ≤ k := fun t ht => hk t (hFH ht)
  -- strict bounds on floating values
  have hstrict : ∀ t ∈ F, 0 < y t ∧ y t < 1 := by
    intro t ht
    rw [hFdef, floating, Finset.mem_filter] at ht
    obtain ⟨htH, hne0, hne1⟩ := ht
    exact ⟨lt_of_le_of_ne (hy0 t htH) (Ne.symm hne0), lt_of_le_of_ne (hy1 t htH) hne1⟩
  obtain ⟨U, hUoff, ⟨t₁, ht₁F, ht₁ne⟩, hUker⟩ := exists_kernel_vector hkF hF
  -- the support of `U`
  set P : Finset (Finset V) := F.filter (fun t => U t ≠ 0) with hPdef
  have hPne : P.Nonempty := ⟨t₁, Finset.mem_filter.mpr ⟨ht₁F, ht₁ne⟩⟩
  set c : Finset V → ℝ := fun t => if 0 < U t then (1 - y t) / U t else (-(y t)) / U t with hcdef
  have hcpos : ∀ t ∈ P, 0 < c t := by
    intro t ht
    rw [hPdef, Finset.mem_filter] at ht
    obtain ⟨htF, htU⟩ := ht
    obtain ⟨hy0t, hy1t⟩ := hstrict t htF
    rw [hcdef]
    by_cases h : 0 < U t
    · simp only [h, ite_true]; exact div_pos (by linarith) h
    · simp only [h, ite_false]
      have hUneg : U t < 0 := lt_of_le_of_ne (not_lt.mp h) htU
      exact div_pos_of_neg_of_neg (by linarith) hUneg
  set lam : ℝ := (P.image c).min' (hPne.image c) with hlamdef
  have hlammem : lam ∈ P.image c := Finset.min'_mem _ _
  obtain ⟨t₀, ht₀P, ht₀c⟩ := Finset.mem_image.mp hlammem
  have hlampos : 0 < lam := by rw [← ht₀c]; exact hcpos t₀ ht₀P
  have hlamle : ∀ t ∈ P, lam ≤ c t := fun t ht =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem c ht)
  refine ⟨fun t => y t + lam * U t, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro t ht
    change (0 : ℝ) ≤ y t + lam * U t
    by_cases htF : t ∈ F
    · by_cases hU : U t = 0
      · simp only [hU, mul_zero, add_zero]; exact hy0 t ht
      · have htP : t ∈ P := Finset.mem_filter.mpr ⟨htF, hU⟩
        rcases lt_trichotomy (U t) 0 with hneg | hzero | hpos
        · have hc : c t = (-(y t)) / U t := by rw [hcdef]; simp [not_lt.mpr hneg.le]
          have h1 : lam * U t ≥ c t * U t := by
            have := hlamle t htP
            nlinarith only [hneg, this]
          have h2 : c t * U t = -(y t) := by
            rw [hc]; field_simp
          linarith only [h1, h2]
        · exact absurd hzero hU
        · have := hy0 t ht
          nlinarith [hlampos.le]
    · rw [hUoff t htF]; simpa using hy0 t ht
  · -- ≤ 1
    intro t ht
    change y t + lam * U t ≤ 1
    by_cases htF : t ∈ F
    · by_cases hU : U t = 0
      · simp only [hU, mul_zero, add_zero]; exact hy1 t ht
      · have htP : t ∈ P := Finset.mem_filter.mpr ⟨htF, hU⟩
        rcases lt_trichotomy (U t) 0 with hneg | hzero | hpos
        · have := hy1 t ht
          nlinarith [hlampos.le]
        · exact absurd hzero hU
        · have hc : c t = (1 - y t) / U t := by rw [hcdef]; simp [hpos]
          have h1 : lam * U t ≤ c t * U t := by
            have := hlamle t htP
            nlinarith only [hpos, this]
          have h2 : c t * U t = 1 - y t := by rw [hc]; field_simp
          linarith only [h1, h2]
    · rw [hUoff t htF]; simpa using hy1 t ht
  · intro t ht
    change y t + lam * U t = y t
    rw [hUoff t ht]; ring
  · -- fewer floating
    have ht₀F : t₀ ∈ F := (Finset.mem_filter.mp ht₀P).1
    have ht₀U : U t₀ ≠ 0 := (Finset.mem_filter.mp ht₀P).2
    have ht₀fix : y t₀ + lam * U t₀ = 0 ∨ y t₀ + lam * U t₀ = 1 := by
      rcases lt_trichotomy (U t₀) 0 with hneg | hzero | hpos
      · left
        have hc : c t₀ = (-(y t₀)) / U t₀ := by rw [hcdef]; simp [not_lt.mpr hneg.le]
        have : lam * U t₀ = -(y t₀) := by
          rw [← ht₀c, hc]; field_simp
        linarith only [this]
      · exact absurd hzero ht₀U
      · right
        have hc : c t₀ = (1 - y t₀) / U t₀ := by rw [hcdef]; simp [hpos]
        have : lam * U t₀ = 1 - y t₀ := by
          rw [← ht₀c, hc]; field_simp
        linarith only [this]
    have hsub : floating H (fun t => y t + lam * U t) ⊆ F.erase t₀ := by
      intro t ht
      rw [floating, Finset.mem_filter] at ht
      obtain ⟨htH, hne0, hne1⟩ := ht
      have htF : t ∈ F := by
        by_contra hcon
        rw [hUoff t hcon] at hne0 hne1
        simp only [mul_zero, add_zero] at hne0 hne1
        rcases (notMem_floating_iff (y := y) htH).mp hcon with h | h
        · exact hne0 h
        · exact hne1 h
      refine Finset.mem_erase.mpr ⟨?_, htF⟩
      rintro rfl
      rcases ht₀fix with h | h
      · exact hne0 h
      · exact hne1 h
    calc (floating H (fun t => y t + lam * U t)).card ≤ (F.erase t₀).card :=
          Finset.card_le_card hsub
      _ < F.card := Finset.card_erase_lt_of_mem ht₀F
  · -- active degrees preserved
    intro x hx
    change ∑ t ∈ H.filter (fun t => x ∈ t), (y t + lam * U t) = _
    have hxA : x ∈ active F k := mem_active_iff.mpr hx
    have hzero := hUker x hxA
    have hsplit : ∑ t ∈ H.filter (fun t => x ∈ t), (y t + lam * U t)
        = ∑ t ∈ H.filter (fun t => x ∈ t), y t
          + lam * ∑ t ∈ H.filter (fun t => x ∈ t), U t := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit]
    have hUH : ∑ t ∈ H.filter (fun t => x ∈ t), U t
        = ∑ t ∈ F.filter (fun t => x ∈ t), U t := by
      refine (Finset.sum_subset (Finset.filter_subset_filter _ hFH) ?_).symm
      intro t ht htn
      rw [Finset.mem_filter] at ht
      have : t ∉ F := by
        intro hcon
        exact htn (Finset.mem_filter.mpr ⟨hcon, ht.2⟩)
      exact hUoff t this
    rw [hUH, hzero, mul_zero, add_zero]

/-- **Beck–Fiala rounding.**  If every edge of `H` has at most `k` vertices, every fractional
selection `y : H → [0,1]` can be rounded to a subfamily `S ⊆ H` (keeping the edges of value `1` and
discarding those of value `0`) whose degree at every vertex differs from the fractional degree by at
most `k`. -/
theorem exists_rounding (k : ℕ) (H : Finset (Finset V)) (hk : ∀ t ∈ H, t.card ≤ k)
    (y : Finset V → ℝ) (hy0 : ∀ t ∈ H, 0 ≤ y t) (hy1 : ∀ t ∈ H, y t ≤ 1) :
    ∃ S ⊆ H, (∀ t ∈ H, y t = 1 → t ∈ S) ∧ (∀ t ∈ H, y t = 0 → t ∉ S) ∧
      ∀ x : V, |((S.filter (fun t => x ∈ t)).card : ℝ)
        - ∑ t ∈ H.filter (fun t => x ∈ t), y t| ≤ k := by
  generalize hn : (floating H y).card = n
  induction n using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · -- no floating edges: take the edges of value 1
      refine ⟨H.filter (fun t => y t = 1), Finset.filter_subset _ _, ?_, ?_, ?_⟩
      · intro t ht h1; exact Finset.mem_filter.mpr ⟨ht, h1⟩
      · intro t ht h0 hmem
        have := (Finset.mem_filter.mp hmem).2
        rw [h0] at this; norm_num at this
      · intro x
        have hempty : floating H y = ∅ := Finset.card_eq_zero.mp hn
        have hval : ∀ t ∈ H, y t = 0 ∨ y t = 1 := by
          intro t ht
          refine (notMem_floating_iff ht).mp ?_
          rw [hempty]; exact Finset.notMem_empty t
        have hsum : (((H.filter (fun t => y t = 1)).filter (fun t => x ∈ t)).card : ℝ)
            = ∑ t ∈ H.filter (fun t => x ∈ t), y t := by
          rw [Finset.filter_comm, Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl fun t ht => ?_
          have htH := (Finset.mem_filter.mp ht).1
          rcases hval t htH with h0 | h1
          · simp [h0]
          · simp [h1]
        rw [hsum, sub_self, abs_zero]
        exact Nat.cast_nonneg k
    · -- at least one floating edge: take a rounding step
      have hFne : (floating H y).Nonempty := by
        rw [← Finset.card_pos, hn]; exact hnpos
      obtain ⟨y', hy'0, hy'1, hoff, hlt, hact⟩ := exists_step k H hk y hy0 hy1 hFne
      obtain ⟨S, hSH, hS1, hS0, hSbound⟩ :=
        ih (floating H y').card (by omega) y' hy'0 hy'1 rfl
      refine ⟨S, hSH, ?_, ?_, ?_⟩
      · intro t ht h1
        refine hS1 t ht ?_
        rw [hoff t ((notMem_floating_iff ht).mpr (Or.inr h1))]; exact h1
      · intro t ht h0
        refine hS0 t ht ?_
        rw [hoff t ((notMem_floating_iff ht).mpr (Or.inl h0))]; exact h0
      · intro x
        by_cases hxa : k < ((floating H y).filter (fun t => x ∈ t)).card
        · rw [← hact x hxa]; exact hSbound x
        · -- inactive vertex: bound the error directly
          push Not at hxa
          have hfset : (H.filter (fun t => x ∈ t)).filter (fun t => t ∈ S)
              = S.filter (fun t => x ∈ t) := by
            ext t
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨⟨-, hx⟩, hS⟩; exact ⟨hS, hx⟩
            · rintro ⟨hS, hx⟩; exact ⟨⟨hSH hS, hx⟩, hS⟩
          have hrepr : ((S.filter (fun t => x ∈ t)).card : ℝ)
              = ∑ t ∈ H.filter (fun t => x ∈ t), (if t ∈ S then (1 : ℝ) else 0) := by
            rw [← hfset, Finset.card_filter]
            push_cast
            rfl
          rw [hrepr, ← Finset.sum_sub_distrib]
          have hterm : ∀ t ∈ H.filter (fun t => x ∈ t),
              |(if t ∈ S then (1 : ℝ) else 0) - y t|
                ≤ (if t ∈ floating H y then (1 : ℝ) else 0) := by
            intro t ht
            have htH := (Finset.mem_filter.mp ht).1
            by_cases hfl : t ∈ floating H y
            · simp only [hfl, ite_true]
              have h0 := hy0 t htH
              have h1 := hy1 t htH
              by_cases hS : t ∈ S <;> simp only [hS, ite_true, ite_false] <;>
                rw [abs_le] <;> constructor <;> linarith
            · simp only [hfl, ite_false]
              rcases (notMem_floating_iff htH).mp hfl with h | h
              · have hy' : y' t = 0 := by rw [hoff t hfl]; exact h
                have : t ∉ S := hS0 t htH hy'
                simp [this, h]
              · have hy' : y' t = 1 := by rw [hoff t hfl]; exact h
                have : t ∈ S := hS1 t htH hy'
                simp [this, h]
          calc |∑ t ∈ H.filter (fun t => x ∈ t), ((if t ∈ S then (1 : ℝ) else 0) - y t)|
              ≤ ∑ t ∈ H.filter (fun t => x ∈ t), |(if t ∈ S then (1 : ℝ) else 0) - y t| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ t ∈ H.filter (fun t => x ∈ t), (if t ∈ floating H y then (1 : ℝ) else 0) :=
                Finset.sum_le_sum hterm
            _ = (((H.filter (fun t => x ∈ t)).filter (fun t => t ∈ floating H y)).card : ℝ) := by
                rw [Finset.card_filter]; push_cast; rfl
            _ = (((floating H y).filter (fun t => x ∈ t)).card : ℝ) := by
                congr 1
                congr 1
                ext t
                simp only [Finset.mem_filter]
                constructor
                · rintro ⟨⟨-, hx⟩, hf⟩; exact ⟨hf, hx⟩
                · rintro ⟨hf, hx⟩; exact ⟨⟨floating_subset H y hf, hx⟩, hf⟩
            _ ≤ (k : ℝ) := by exact_mod_cast hxa

end Nibble.BeckFiala

end


/-! # Simultaneous fractional rounding of degrees and codegrees -/

public section

open Finset

namespace Nibble.BeckFiala

variable {V : Type*} [DecidableEq V]

/-- The subsets of `T` of size at most `2`. -/
def pairClosure (T : Finset V) : Finset (Finset V) := T.powerset.filter (fun s => s.card ≤ 2)

omit [DecidableEq V] in
theorem mem_pairClosure {T s : Finset V} : s ∈ pairClosure T ↔ s ⊆ T ∧ s.card ≤ 2 := by
  simp [pairClosure, Finset.mem_filter, Finset.mem_powerset]

/-- `T` is recovered from `pairClosure T` as the union of its members. -/
theorem biUnion_pairClosure (T : Finset V) : (pairClosure T).biUnion id = T := by
  ext v
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨s, hs, hvs⟩
    exact (mem_pairClosure.mp hs).1 hvs
  · intro hv
    exact ⟨{v}, mem_pairClosure.mpr ⟨Finset.singleton_subset_iff.mpr hv, by simp⟩, by simp⟩

omit [DecidableEq V] in
theorem pairClosure_injective :
    Function.Injective (pairClosure : Finset V → Finset (Finset V)) := by
  classical
  intro a b hab
  rw [← biUnion_pairClosure a, hab, biUnion_pairClosure]

omit [DecidableEq V] in
theorem singleton_mem_pairClosure {T : Finset V} {v : V} : {v} ∈ pairClosure T ↔ v ∈ T := by
  rw [mem_pairClosure]
  simp [Finset.singleton_subset_iff]

theorem pair_mem_pairClosure {T : Finset V} {x z : V} :
    ({x, z} : Finset V) ∈ pairClosure T ↔ (x ∈ T ∧ z ∈ T) := by
  rw [mem_pairClosure]
  constructor
  · rintro ⟨hsub, -⟩
    exact ⟨hsub (by simp), hsub (by simp)⟩
  · rintro ⟨hx, hz⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact hx
      · rw [Finset.mem_singleton] at ha'; subst ha'; exact hz
    · exact le_trans (Finset.card_insert_le _ _) (by simp)

omit [DecidableEq V] in
/-- The auxiliary vertex set of an edge has at most `1 + |T|²` elements. -/
theorem card_pairClosure_le (T : Finset V) : (pairClosure T).card ≤ 1 + T.card * T.card := by
  classical
  have hsub : pairClosure T ⊆ insert (∅ : Finset V)
      ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V))) := by
    intro s hs
    obtain ⟨hsub, hcard⟩ := mem_pairClosure.mp hs
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · exact Finset.mem_insert_self _ _
    refine Finset.mem_insert_of_mem ?_
    interval_cases h : s.card
    · exact absurd (Finset.card_eq_zero.mp h) (Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩)
    · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h
      subst hb
      refine Finset.mem_image.mpr ⟨(b, b), Finset.mem_product.mpr
        ⟨hsub (by simp), hsub (by simp)⟩, ?_⟩
      simp
    · obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp h
      exact Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr
        ⟨hsub (by simp), hsub (by simp)⟩, rfl⟩
  calc (pairClosure T).card
      ≤ (insert (∅ : Finset V) ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V)))).card :=
        Finset.card_le_card hsub
    _ ≤ 1 + ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V))).card := by
        have := Finset.card_insert_le (∅ : Finset V)
          ((T ×ˢ T).image (fun p : V × V => ({p.1, p.2} : Finset V)))
        omega
    _ ≤ 1 + (T ×ˢ T).card := by
        have := Finset.card_image_le (s := T ×ˢ T)
          (f := fun p : V × V => ({p.1, p.2} : Finset V))
        omega
    _ = 1 + T.card * T.card := by rw [Finset.card_product]

/-- **Beck–Fiala rounding with codegree control.**  Every fractional selection `y : H → [0,1]` of an
`r`-uniform hypergraph `H` can be rounded to a subhypergraph `S ⊆ H` whose degrees *and* codegrees
differ from the fractional degrees and codegrees by at most `1 + r²`. -/
theorem exists_rounding_pairs (r : ℕ) (H : Finset (Finset V)) (hunif : ∀ T ∈ H, T.card = r)
    (y : Finset V → ℝ) (hy0 : ∀ T ∈ H, 0 ≤ y T) (hy1 : ∀ T ∈ H, y T ≤ 1) :
    ∃ S ⊆ H,
      (∀ v : V, |((S.filter (fun T => v ∈ T)).card : ℝ)
          - ∑ T ∈ H.filter (fun T => v ∈ T), y T| ≤ 1 + (r : ℝ) * r) ∧
      (∀ x z : V, |((S.filter (fun T => x ∈ T ∧ z ∈ T)).card : ℝ)
          - ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), y T| ≤ 1 + (r : ℝ) * r) := by
  classical
  set k : ℕ := 1 + r * r with hkdef
  set Hs : Finset (Finset (Finset V)) := H.image pairClosure with hHsdef
  set ys : Finset (Finset V) → ℝ := fun U => y (U.biUnion id) with hysdef
  -- every auxiliary edge is a `pairClosure`
  have hmemHs : ∀ U ∈ Hs, (U.biUnion id) ∈ H ∧ U = pairClosure (U.biUnion id) := by
    intro U hU
    rw [hHsdef, Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [biUnion_pairClosure]
    exact ⟨hT, rfl⟩
  have hk : ∀ U ∈ Hs, U.card ≤ k := by
    intro U hU
    rw [hHsdef, Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    have := card_pairClosure_le T
    rw [hunif T hT] at this
    exact this
  have hys0 : ∀ U ∈ Hs, 0 ≤ ys U := fun U hU => hy0 _ (hmemHs U hU).1
  have hys1 : ∀ U ∈ Hs, ys U ≤ 1 := fun U hU => hy1 _ (hmemHs U hU).1
  obtain ⟨Ss, hSsHs, -, -, hbound⟩ := exists_rounding k Hs hk ys hys0 hys1
  -- injectivity of the projection on the auxiliary family
  have hinjOn : ∀ (A : Finset (Finset (Finset V))), A ⊆ Hs →
      Set.InjOn (fun U : Finset (Finset V) => U.biUnion id) ↑A := by
    intro A hA U hU U' hU' heq
    have h1 := (hmemHs U (hA hU)).2
    have h2 := (hmemHs U' (hA hU')).2
    have heq' : U.biUnion id = U'.biUnion id := heq
    calc U = pairClosure (U.biUnion id) := h1
      _ = pairClosure (U'.biUnion id) := by rw [heq']
      _ = U' := h2.symm
  refine ⟨Ss.image (fun U => U.biUnion id), ?_, ?_, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact (hmemHs U (hSsHs hU)).1
  · -- degrees
    intro v
    have hcard : (((Ss.image (fun U => U.biUnion id)).filter (fun T => v ∈ T)).card : ℝ)
        = ((Ss.filter (fun U => ({v} : Finset V) ∈ U)).card : ℝ) := by
      have h1 : (Ss.image (fun U => U.biUnion id)).filter (fun T => v ∈ T)
          = (Ss.filter (fun U => v ∈ U.biUnion id)).image (fun U => U.biUnion id) :=
        Finset.filter_image
      have h2 : Ss.filter (fun U => v ∈ U.biUnion id)
          = Ss.filter (fun U => ({v} : Finset V) ∈ U) := by
        refine Finset.filter_congr ?_
        intro U hU
        rw [(hmemHs U (hSsHs hU)).2]
        simp only [biUnion_pairClosure, singleton_mem_pairClosure]
      rw [h1, h2, Finset.card_image_of_injOn (hinjOn _ (Finset.Subset.trans
        (Finset.filter_subset _ _) hSsHs))]
    have hsum : ∑ U ∈ Hs.filter (fun U => ({v} : Finset V) ∈ U), ys U
        = ∑ T ∈ H.filter (fun T => v ∈ T), y T := by
      have h1 : Hs.filter (fun U => ({v} : Finset V) ∈ U)
          = (H.filter (fun T => v ∈ T)).image pairClosure := by
        rw [hHsdef, Finset.filter_image]
        congr 1
        refine Finset.filter_congr ?_
        intro T _
        simp [singleton_mem_pairClosure]
      rw [h1, Finset.sum_image (fun a _ b _ h => pairClosure_injective h)]
      exact Finset.sum_congr rfl (fun T _ => by rw [hysdef]; simp [biUnion_pairClosure])
    have h := hbound ({v} : Finset V)
    rw [hsum] at h
    rw [hcard]
    exact le_trans h (by push_cast [hkdef]; linarith)
  · -- codegrees
    intro x z
    have hcard : (((Ss.image (fun U => U.biUnion id)).filter
          (fun T => x ∈ T ∧ z ∈ T)).card : ℝ)
        = ((Ss.filter (fun U => ({x, z} : Finset V) ∈ U)).card : ℝ) := by
      have h1 : (Ss.image (fun U => U.biUnion id)).filter (fun T => x ∈ T ∧ z ∈ T)
          = (Ss.filter (fun U => x ∈ U.biUnion id ∧ z ∈ U.biUnion id)).image
              (fun U => U.biUnion id) := Finset.filter_image
      have h2 : Ss.filter (fun U => x ∈ U.biUnion id ∧ z ∈ U.biUnion id)
          = Ss.filter (fun U => ({x, z} : Finset V) ∈ U) := by
        refine Finset.filter_congr ?_
        intro U hU
        rw [(hmemHs U (hSsHs hU)).2]
        simp only [biUnion_pairClosure, pair_mem_pairClosure]
      rw [h1, h2, Finset.card_image_of_injOn (hinjOn _ (Finset.Subset.trans
        (Finset.filter_subset _ _) hSsHs))]
    have hsum : ∑ U ∈ Hs.filter (fun U => ({x, z} : Finset V) ∈ U), ys U
        = ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), y T := by
      have h1 : Hs.filter (fun U => ({x, z} : Finset V) ∈ U)
          = (H.filter (fun T => x ∈ T ∧ z ∈ T)).image pairClosure := by
        rw [hHsdef, Finset.filter_image]
        congr 1
        refine Finset.filter_congr ?_
        intro T _
        simp [pair_mem_pairClosure]
      rw [h1, Finset.sum_image (fun a _ b _ h => pairClosure_injective h)]
      exact Finset.sum_congr rfl (fun T _ => by rw [hysdef]; simp [biUnion_pairClosure])
    have h := hbound ({x, z} : Finset V)
    rw [hsum] at h
    rw [hcard]
    exact le_trans h (by push_cast [hkdef]; linarith)

end Nibble.BeckFiala

end



/-!
# Weighted hypergraph incidences

The fractional-rounding proof in Paper III uses edge weights rather than the unweighted
near-regular hypotheses of `nearRegularNibbleTheorem`. These definitions retain the exact
finite-set model of the frozen proof. The rounding theorem itself is not asserted here.
-/

public section

open Finset

namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Total edge weight incident with a vertex. -/
def weightedLoad (H : Finset (Finset V)) (w : Finset V → ℝ) (v : V) : ℝ :=
  ∑ e ∈ H.filter (fun e => v ∈ e), w e

/-- Total edge weight incident with both vertices. -/
def weightedCodegree (H : Finset (Finset V)) (w : Finset V → ℝ) (u v : V) : ℝ :=
  ∑ e ∈ H.filter (fun e => u ∈ e ∧ v ∈ e), w e

/-- Weighted handshake for an `r`-uniform finite hypergraph. -/
theorem sum_weightedLoad (H : Finset (Finset V)) (w : Finset V → ℝ) {r : ℕ}
    (hr : IsUniform H r) :
    ∑ v : V, weightedLoad H w v = (r : ℝ) * ∑ e ∈ H, w e := by
  classical
  simp_rw [weightedLoad, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hr e he, nsmul_eq_mul]

/-- A fractional matching on an `r`-uniform hypergraph has total weight at most `|V|/r`. -/
theorem weightedSum_le_card (H : Finset (Finset V)) (w : Finset V → ℝ) {r : ℕ}
    (hr : IsUniform H r) (hload : ∀ v : V, weightedLoad H w v ≤ 1) :
    (r : ℝ) * (∑ e ∈ H, w e) ≤ (Fintype.card V : ℝ) := by
  rw [← sum_weightedLoad H w hr]
  calc
    ∑ v : V, weightedLoad H w v ≤ ∑ _v : V, (1 : ℝ) :=
      Finset.sum_le_sum (fun v _ => hload v)
    _ = (Fintype.card V : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]

/-- Exact bounded-edge weighted-rounding target from the Paper III freeze.
This is a specification, not a proof or a public result. -/
def BoundedEdgeWeightedRounding : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H : Finset (Finset W)) (w : Finset W → ℝ),
        (∀ e ∈ H, e.Nonempty ∧ e.card ≤ r) →
        (∀ e, 0 ≤ w e) →
        (∀ v : W, weightedLoad H w v ≤ 1) →
        (∀ u v : W, u ≠ v → weightedCodegree H w u v ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * (∑ e ∈ H, w e) - β * (Fintype.card W : ℝ) - C ≤ (M.card : ℝ)

end Hypergraph

end


/-! # Weighted fractional-to-integral nibble bridge -/

public section

open Finset Hypergraph LeanPool.AsymptoticTrianglePacking.Internal

namespace Nibble

/-- **The weighted nibble for spread, near-perfect fractional matchings.**  No regularity and no
codegree hypothesis is placed on the hypergraph: all the hypotheses are on the fractional matching
`w`. -/
theorem fracNibble_spread_weightedCodegree (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (Exc : Finset W),
        IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ T ∈ H, w T ≤ δ) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds r hr β hβ
  set k : ℕ := 1 + r * r with hkdef
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by rw [hkdef]; omega
    exact_mod_cast this
  set D : ℕ := max ⌈d₀⌉₊ ⌈(4 * (k : ℝ)) / μ⌉₊ + 1 with hDdef
  have hDpos : 0 < D := Nat.succ_pos _
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hd₀D : d₀ ≤ (D : ℝ) := by
    have h1 : (⌈d₀⌉₊ : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (by omega : ⌈d₀⌉₊ ≤ D)
    exact le_trans (Nat.le_ceil _) h1
  have hkD : 4 * (k : ℝ) ≤ μ * (D : ℝ) := by
    have h1 : ((4 * (k : ℝ)) / μ) ≤ (⌈(4 * (k : ℝ)) / μ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(4 * (k : ℝ)) / μ⌉₊ : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (by omega : ⌈(4 * (k : ℝ)) / μ⌉₊ ≤ D)
    have h3 : ((4 * (k : ℝ)) / μ) ≤ (D : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hμ] at h3
    linarith
  refine ⟨1 / (D : ℝ), by positivity, μ / 4, by positivity, η, hη, ?_⟩
  intro W _ _ H w Exc hunif hwnn hspread hvle hvge hExc hcod
  -- the Beck–Fiala rounding of `y = D·w`
  set y : Finset W → ℝ := fun T => (D : ℝ) * w T with hydef
  have hy0 : ∀ T ∈ H, 0 ≤ y T := fun T _ => mul_nonneg hDR.le (hwnn T)
  have hy1 : ∀ T ∈ H, y T ≤ 1 := by
    intro T hT
    have h := hspread T hT
    rw [hydef]
    calc (D : ℝ) * w T ≤ (D : ℝ) * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left h hDR.le
      _ = 1 := by field_simp
  obtain ⟨S, hSH, hdeg, hcodeg⟩ :=
    BeckFiala.exists_rounding_pairs r H (fun T hT => hunif T hT) y hy0 hy1
  have hkr : (1 : ℝ) + (r : ℝ) * r = (k : ℝ) := by rw [hkdef]; push_cast; ring
  have hfrac : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), y T
      = (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T := by
    intro v; rw [hydef, ← Finset.mul_sum]
  have hfrac2 : ∀ x z : W, ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), y T
      = (D : ℝ) * ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T := by
    intro x z; rw [hydef, ← Finset.mul_sum]
  -- the rounded hypergraph is nearly `D`-regular with small codegree
  have hSunif : IsUniform S r := fun T hT => hunif T (hSH hT)
  have hdegeq : ∀ v : W, ((S.filter (fun T => v ∈ T)).card : ℝ) = (degree S v : ℝ) := by
    intro v; simp [degree]
  have hcodeq : ∀ x z : W, ((S.filter (fun T => x ∈ T ∧ z ∈ T)).card : ℝ)
      = (codegree S x z : ℝ) := by
    intro x z; simp [codegree]
  have hceil : ∀ v : W, (degree S v : ℝ) ≤ (1 + μ) * (D : ℝ) := by
    intro v
    have h := (abs_le.mp (hdeg v)).2
    rw [hfrac v, hdegeq v, hkr] at h
    have h2 : (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ (D : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hvle v) hDR.le
    linarith
  have hlow : ∀ v : W, v ∉ Exc → (1 - μ) * (D : ℝ) ≤ (degree S v : ℝ) := by
    intro v hv
    have h := (abs_le.mp (hdeg v)).1
    rw [hfrac v, hdegeq v, hkr] at h
    have h2 : (D : ℝ) * (1 - μ / 4) ≤ (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T :=
      mul_le_mul_of_nonneg_left (hvge v hv) hDR.le
    linarith
  have hScod : CodegreeBounded S (μ * (D : ℝ)) := by
    intro x z hxz
    have h := (abs_le.mp (hcodeg x z)).2
    rw [hfrac2 x z, hcodeq x z, hkr] at h
    have h2 : (D : ℝ) * ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ (D : ℝ) * (μ / 4) :=
      mul_le_mul_of_nonneg_left (hcod x z hxz) hDR.le
    linarith
  have hreg : NearlyRegularMost S (D : ℝ) μ η :=
    ⟨Exc, hExc, fun v hv => ⟨hlow v hv, hceil v⟩⟩
  obtain ⟨M, hM, hMcard⟩ := hmain S (D : ℝ) hDR hd₀D hSunif hreg hScod hceil
  refine ⟨M, ⟨Finset.Subset.trans hM.subset hSH, hM.disjoint⟩, hMcard, ?_⟩
  -- every fractional matching has total weight at most `|W|/r`
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  have hsum : (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) / r := by
    rw [le_div_iff₀ hrpos, mul_comm]
    exact Hypergraph.weightedSum_le_card H w hunif hvle
  rcases le_or_gt β 1 with h1 | h1
  · exact le_trans (mul_le_mul_of_nonneg_left hsum (by linarith)) hMcard
  · have hnn' : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hwnn T)
    have hle0 : (1 - β) * (∑ T ∈ H, w T) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn'
    exact le_trans hle0 (Nat.cast_nonneg _)

/-- **The spread hypothesis is redundant.**  Every edge contains a pair `x ≠ z`, so its weight is at
most the weighted codegree of that pair. -/
theorem weight_le_weightedCodegree {W : Type} [DecidableEq W] {r : ℕ} (hr : 2 ≤ r)
    {H : Finset (Finset W)} {w : Finset W → ℝ} {γ : ℝ} (hunif : IsUniform H r)
    (hwnn : ∀ T, 0 ≤ w T)
    (hcod : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ)
    {T : Finset W} (hT : T ∈ H) : w T ≤ γ := by
  classical
  have hcard : 1 < T.card := by
    rw [hunif T hT]; omega
  obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.mp hcard
  have hmem : T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T) := Finset.mem_filter.mpr ⟨hT, hx, hz⟩
  have hle : w T ≤ ∑ T' ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T' :=
    Finset.single_le_sum (fun T' _ => hwnn T') hmem
  exact le_trans hle (hcod x z hxz)

/-- **The weighted nibble for near-perfect fractional matchings of small weighted codegree.**  The
spread hypothesis of `Nibble.fracNibble_spread_weightedCodegree` is dropped: it follows from the
weighted codegree bound.  Still no hypothesis whatsoever on the degrees or codegrees of `H`. -/
theorem fracNibble_weightedCodegree (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (Exc : Finset W),
        IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨δ, hδ, γ, hγ, η, hη, hmain⟩ := fracNibble_spread_weightedCodegree r hr β hβ
  refine ⟨min δ γ, lt_min hδ hγ, η, hη, ?_⟩
  intro W _ _ H w Exc hunif hwnn hvle hvge hExc hcod
  have hcod' : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ :=
    fun x z hxz => le_trans (hcod x z hxz) (min_le_right _ _)
  have hcodδ : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ δ :=
    fun x z hxz => le_trans (hcod x z hxz) (min_le_left _ _)
  refine hmain H w Exc hunif hwnn
    (fun T hT => weight_le_weightedCodegree hr hunif hwnn hcodδ hT) hvle
    (fun v hv => le_trans (by have := min_le_right δ γ; linarith) (hvge v hv)) hExc hcod'

/-- **The weighted nibble for spread fractional matchings on hypergraphs of bounded codegree.**  A
fractional matching with all weights at most `δ` on a hypergraph of codegree at most `C` has
weighted codegree at most `C·δ`, so `Nibble.fracNibble_spread_weightedCodegree` applies.  This
generalises `Nibble.exists_matching_of_spread` (the case `C = 1`) to an arbitrary codegree bound,
and adds the weighted form `(1-β)∑w ≤ |M|` of the conclusion to the covering form
`(1-β)|W|/r ≤ |M|`. -/
theorem fracNibble_spread_codegree (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) (C : ℝ) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (Exc : Finset W),
        IsUniform H r →
        (∀ x z : W, x ≠ z → (codegree H x z : ℝ) ≤ C) →
        (∀ T, 0 ≤ w T) →
        (∀ T ∈ H, w T ≤ δ) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨δ, hδ, γ, hγ, η, hη, hmain⟩ := fracNibble_spread_weightedCodegree r hr β hβ
  refine ⟨min δ (γ / C), lt_min hδ (by positivity), γ, hγ, η, hη, ?_⟩
  intro W _ _ H w Exc hunif hCod hwnn hspread hvle hvge hExc
  refine hmain H w Exc hunif hwnn (fun T hT => le_trans (hspread T hT) (min_le_left _ _))
    hvle hvge hExc ?_
  intro x z hxz
  -- the weighted codegree is at most `C · δ ≤ γ`
  have hbound : ∀ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ / C := by
    intro T hT
    exact le_trans (hspread T (Finset.mem_filter.mp hT).1) (min_le_right _ _)
  calc ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T
      ≤ ∑ _T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), (γ / C) := Finset.sum_le_sum hbound
    _ = ((H.filter (fun T => x ∈ T ∧ z ∈ T)).card : ℝ) * (γ / C) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (codegree H x z : ℝ) * (γ / C) := by rw [codegree]
    _ ≤ C * (γ / C) := by
        exact mul_le_mul_of_nonneg_right (hCod x z hxz) (by positivity)
    _ = γ := by field_simp

end Nibble

end


/-! # Three-uniform weighted rounding with total slack -/

public section

open Finset Hypergraph

namespace Nibble

namespace Slack

variable {X : Type} [DecidableEq X]

/-- The `w`-load of a vertex: the total weight of the edges through it. -/
@[expose] def wLoad (K : Finset (Finset X)) (w : Finset X → ℝ) (v : X) : ℝ :=
  ∑ T ∈ K.filter (fun T => v ∈ T), w T

/-- The padded vertex type: the real vertices together with `2m` dummies, `m` on each side. -/
abbrev Pad (X : Type) (m : ℕ) := X ⊕ (Fin m × Bool)

/-- The added triple joining the real vertex `v` to the left dummy `i` and the right dummy `j`. -/
def mixTriple (m : ℕ) (v : X) (i j : Fin m) : Finset (Pad X m) :=
  {Sum.inl v, Sum.inr (i, false), Sum.inr (j, true)}

/-- The padded hypergraph: the image of `K` together with all the mixed triples. -/
def padFam [Fintype X] (K : Finset (Finset X)) (m : ℕ) : Finset (Finset (Pad X m)) :=
  K.image (Finset.image Sum.inl) ∪
    (Finset.univ : Finset (X × Fin m × Fin m)).image (fun t => mixTriple m t.1 t.2.1 t.2.2)

/-- The padded weighting. -/
noncomputable def padWt (K : Finset (Finset X)) (w : Finset X → ℝ) (m : ℕ) :
    Finset (Pad X m) → ℝ :=
  fun U => if U.toRight = ∅ then w U.toLeft
           else (∑ v ∈ U.toLeft, (1 - wLoad K w v)) / (m : ℝ) ^ 2

section
variable (K : Finset (Finset X)) (w : Finset X → ℝ) (m : ℕ)

@[simp] lemma toLeft_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → Pad X m)).toLeft = T := by
  ext x; simp

@[simp] lemma toRight_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → Pad X m)).toRight = (∅ : Finset (Fin m × Bool)) := by
  ext x; simp

@[simp] lemma mixTriple_toLeft (v : X) (i j : Fin m) :
    (mixTriple m v i j).toLeft = {v} := by
  ext x; simp [mixTriple]

@[simp] lemma mixTriple_toRight (v : X) (i j : Fin m) :
    (mixTriple m v i j).toRight = {(i, false), (j, true)} := by
  ext x; simp [mixTriple]

lemma mixTriple_card (v : X) (i j : Fin m) : (mixTriple m v i j).card = 3 := by
  simp [mixTriple, Finset.card_insert_of_notMem]

lemma mem_mixTriple_inl (v u : X) (i j : Fin m) :
    (Sum.inl u : Pad X m) ∈ mixTriple m v i j ↔ u = v := by
  simp [mixTriple]

lemma mem_mixTriple_inr (v : X) (i j : Fin m) (d : Fin m × Bool) :
    (Sum.inr d : Pad X m) ∈ mixTriple m v i j ↔ d = (i, false) ∨ d = (j, true) := by
  simp [mixTriple]

lemma mixTriple_inj {v v' : X} {i i' j j' : Fin m}
    (h : mixTriple m v i j = mixTriple m v' i' j') : v = v' ∧ i = i' ∧ j = j' := by
  have hL : ({v} : Finset X) = {v'} := by
    have := congrArg Finset.toLeft h; simpa using this
  have hR : ({(i, false), (j, true)} : Finset (Fin m × Bool)) = {(i', false), (j', true)} := by
    have := congrArg Finset.toRight h; simpa using this
  refine ⟨by simpa using hL, ?_, ?_⟩
  · have : ((i, false) : Fin m × Bool) ∈ ({(i', false), (j', true)} : Finset (Fin m × Bool)) := by
      rw [← hR]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
    rcases this with h1 | h2
    · exact h1.1
    · exact absurd h2.2 (by simp)
  · have : ((j, true) : Fin m × Bool) ∈ ({(i', false), (j', true)} : Finset (Fin m × Bool)) := by
      rw [← hR]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
    rcases this with h1 | h2
    · exact absurd h1.2 (by simp)
    · exact h2.1

lemma padWt_image_inl (T : Finset X) : padWt K w m (T.image Sum.inl) = w T := by
  simp [padWt]

lemma padWt_mixTriple (v : X) (i j : Fin m) :
    padWt K w m (mixTriple m v i j) = (1 - wLoad K w v) / (m : ℝ) ^ 2 := by
  simp [padWt]

lemma padWt_nonneg (hw : ∀ T, 0 ≤ w T) (hload : ∀ v : X, wLoad K w v ≤ 1) (U : Finset (Pad X m)) :
    0 ≤ padWt K w m U := by
  rw [padWt]
  split
  · exact hw _
  · have : 0 ≤ ∑ v ∈ U.toLeft, (1 - wLoad K w v) :=
      Finset.sum_nonneg fun v _ => by linarith only [hload v]
    positivity

end

section
variable [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) (m : ℕ)

/-- The two halves of the padded family are disjoint, and both index maps are injective: so a sum
over `padFam` splits into a sum over `K` and a sum over the mixed triples. -/
lemma sum_padFam (f : Finset (Pad X m) → ℝ) :
    ∑ U ∈ padFam K m, f U
      = (∑ T ∈ K, f (T.image Sum.inl))
        + ∑ v : X, ∑ i : Fin m, ∑ j : Fin m, f (mixTriple m v i j) := by
  classical
  have hdisj : Disjoint (K.image (Finset.image (Sum.inl : X → Pad X m)))
      ((Finset.univ : Finset (X × Fin m × Fin m)).image
        (fun t => mixTriple m t.1 t.2.1 t.2.2)) := by
    rw [Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨T, -, rfl⟩ := hU
    obtain ⟨t, -, ht⟩ := hU'
    have h1 : (T.image (Sum.inl : X → Pad X m)).toRight = ∅ := by simp
    rw [← ht] at h1
    simp at h1
  rw [padFam, Finset.sum_union hdisj]
  congr 1
  · exact Finset.sum_image (fun T _ T' _ h => Finset.image_injective Sum.inl_injective h)
  · rw [Finset.sum_image (fun t _ t' _ h => ?_)]
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun v _ => by rw [Fintype.sum_prod_type]
    · obtain ⟨h1, h2, h3⟩ := mixTriple_inj m h
      exact Prod.ext h1 (Prod.ext h2 h3)

/-- **Weighted handshake.**  For a `3`-uniform hypergraph the loads add up to `3` times the total
weight. -/
lemma sum_wLoad (h3 : IsUniform K 3) : ∑ x : X, wLoad K w x = 3 * ∑ T ∈ K, w T := by
  classical
  simp_rw [wLoad, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, h3 T hT, nsmul_eq_mul]
  norm_num

/-- The total slack of the weighting. -/
def slackTotal : ℝ := ∑ v : X, (1 - wLoad K w v)

lemma padLoad_inl (hm : 0 < m) (v : X) :
    ∑ U ∈ (padFam K m).filter (fun U => (Sum.inl v : Pad X m) ∈ U), padWt K w m U = 1 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inl v : Pad X m) ∈ T.image Sum.inl then
        padWt K w m (T.image Sum.inl) else 0) = wLoad K w v := by
    rw [wLoad, Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp [padWt_image_inl]
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inl v : Pad X m) ∈ mixTriple m u i j then padWt K w m (mixTriple m u i j) else 0)
      = if u = v then (1 - wLoad K w u) else 0 := by
    intro u
    simp only [mem_mixTriple_inl, padWt_mixTriple]
    by_cases huv : v = u
    · subst huv
      simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · rw [ite_eq_right huv, ite_eq_right (fun h => huv h.symm)]
      simp
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_ite_eq' Finset.univ v
    (fun u => 1 - wLoad K w u)]
  simp

lemma padLoad_inr (hm : 0 < m) (d : Fin m × Bool) :
    ∑ U ∈ (padFam K m).filter (fun U => (Sum.inr d : Pad X m) ∈ U), padWt K w m U
      = slackTotal K w / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inr d : Pad X m) ∈ T.image Sum.inl then
        padWt K w m (T.image Sum.inl) else 0) = 0 := by
    refine Finset.sum_eq_zero fun T _ => ?_
    simp
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inr d : Pad X m) ∈ mixTriple m u i j then padWt K w m (mixTriple m u i j) else 0)
      = (1 - wLoad K w u) / (m : ℝ) := by
    intro u
    simp only [mem_mixTriple_inr, padWt_mixTriple]
    obtain ⟨d1, b⟩ := d
    cases b
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if ((d1, false) : Fin m × Bool) = (i, false) ∨ ((d1, false) : Fin m × Bool) = (j, true)
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (m : ℝ) * ((1 - wLoad K w u) / (m : ℝ) ^ 2) := by simp
      rw [this]
      field_simp
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if ((d1, true) : Fin m × Bool) = (i, false) ∨ ((d1, true) : Fin m × Bool) = (j, true)
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (m : ℝ) * ((1 - wLoad K w u) / (m : ℝ) ^ 2) := by simp
      rw [this]
      field_simp
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add, slackTotal, Finset.sum_div]

lemma padFam_uniform (hK : IsUniform K 3) : IsUniform (padFam K m) 3 := by
  intro U hU
  rw [padFam, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact hK T hT
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact mixTriple_card m t.1 t.2.1 t.2.2

lemma slackTotal_nonneg (hload : ∀ v : X, wLoad K w v ≤ 1) : 0 ≤ slackTotal K w :=
  Finset.sum_nonneg fun v _ => by linarith only [hload v]

lemma sum_padWt (hm : 0 < m) :
    ∑ U ∈ padFam K m, padWt K w m U = (∑ T ∈ K, w T) + slackTotal K w := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [sum_padFam]
  congr 1
  · exact Finset.sum_congr rfl fun T _ => padWt_image_inl K w m T
  · rw [slackTotal]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [padWt_mixTriple, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

lemma padCodeg_inl_inl {v v' : X} (hvv : v ≠ v') :
    ∑ U ∈ (padFam K m).filter
        (fun U => (Sum.inl v : Pad X m) ∈ U ∧ (Sum.inl v' : Pad X m) ∈ U), padWt K w m U
      = ∑ T ∈ K.filter (fun T => v ∈ T ∧ v' ∈ T), w T := by
  classical
  rw [Finset.sum_filter, sum_padFam, Finset.sum_filter]
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inl v : Pad X m) ∈ mixTriple m u i j ∧ (Sum.inl v' : Pad X m) ∈ mixTriple m u i j
        then padWt K w m (mixTriple m u i j) else 0) = 0 := by
    intro u
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    rw [mem_mixTriple_inl] at h1 h2
    exact hvv (h1.trans h2.symm)
  rw [Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp [padWt_image_inl]

lemma padCodeg_inl_inr (hm : 0 < m) (v : X) (d : Fin m × Bool) :
    ∑ U ∈ (padFam K m).filter
        (fun U => (Sum.inl v : Pad X m) ∈ U ∧ (Sum.inr d : Pad X m) ∈ U), padWt K w m U
      = (1 - wLoad K w v) / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inl v : Pad X m) ∈ T.image Sum.inl ∧
        (Sum.inr d : Pad X m) ∈ T.image Sum.inl then padWt K w m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inl v : Pad X m) ∈ mixTriple m u i j ∧ (Sum.inr d : Pad X m) ∈ mixTriple m u i j
        then padWt K w m (mixTriple m u i j) else 0)
      = if u = v then (1 - wLoad K w u) / (m : ℝ) else 0 := by
    intro u
    simp only [mem_mixTriple_inl, mem_mixTriple_inr, padWt_mixTriple]
    by_cases huv : v = u
    · subst huv
      obtain ⟨d1, b⟩ := d
      cases b
      · have : ∑ i : Fin m, ∑ j : Fin m,
            (if (v = v) ∧ (((d1, false) : Fin m × Bool) = (i, false) ∨
                ((d1, false) : Fin m × Bool) = (j, true))
              then (1 - wLoad K w v) / (m : ℝ) ^ 2 else 0)
            = (m : ℝ) * ((1 - wLoad K w v) / (m : ℝ) ^ 2) := by simp
        rw [this, ite_eq_left rfl]
        field_simp
      · have : ∑ i : Fin m, ∑ j : Fin m,
            (if (v = v) ∧ (((d1, true) : Fin m × Bool) = (i, false) ∨
                ((d1, true) : Fin m × Bool) = (j, true))
              then (1 - wLoad K w v) / (m : ℝ) ^ 2 else 0)
            = (m : ℝ) * ((1 - wLoad K w v) / (m : ℝ) ^ 2) := by simp
        rw [this, ite_eq_left rfl]
        field_simp
    · rw [ite_eq_right (fun h => huv h.symm)]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, -⟩
      exact huv h
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add,
    Finset.sum_ite_eq' Finset.univ v (fun u => (1 - wLoad K w u) / (m : ℝ))]
  simp

lemma padCodeg_inr_inr (hm : 0 < m) (hload : ∀ v : X, wLoad K w v ≤ 1) {d d' : Fin m × Bool}
    (hd : d ≠ d') :
    ∑ U ∈ (padFam K m).filter
        (fun U => (Sum.inr d : Pad X m) ∈ U ∧ (Sum.inr d' : Pad X m) ∈ U), padWt K w m U
      ≤ slackTotal K w / (m : ℝ) ^ 2 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inr d : Pad X m) ∈ T.image Sum.inl ∧
        (Sum.inr d' : Pad X m) ∈ T.image Sum.inl then padWt K w m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inr d : Pad X m) ∈ mixTriple m u i j ∧ (Sum.inr d' : Pad X m) ∈ mixTriple m u i j
        then padWt K w m (mixTriple m u i j) else 0)
      ≤ (1 - wLoad K w u) / (m : ℝ) ^ 2 := by
    intro u
    have hnn : 0 ≤ (1 - wLoad K w u) / (m : ℝ) ^ 2 :=
      div_nonneg (by linarith only [hload u]) (by positivity)
    simp only [mem_mixTriple_inr, padWt_mixTriple]
    obtain ⟨a, b⟩ := d
    obtain ⟨a', b'⟩ := d'
    cases b <;> cases b'
    · have hne : a ≠ a' := fun h => hd (by rw [h])
      refine le_of_eq_of_le ?_ hnn
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, h'⟩
      simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, or_false, and_true] at h h'
      exact hne (h.trans h'.symm)
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if (((a, false) : Fin m × Bool) = (i, false) ∨ ((a, false) : Fin m × Bool) = (j, true)) ∧
              (((a', true) : Fin m × Bool) = (i, false) ∨ ((a', true) : Fin m × Bool) = (j, true))
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (1 - wLoad K w u) / (m : ℝ) ^ 2 := by simp [ite_and]
      exact le_of_eq this
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if (((a, true) : Fin m × Bool) = (i, false) ∨ ((a, true) : Fin m × Bool) = (j, true)) ∧
              (((a', false) : Fin m × Bool) = (i, false) ∨ ((a', false) : Fin m × Bool) = (j, true))
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (1 - wLoad K w u) / (m : ℝ) ^ 2 := by simp [ite_and]
      exact le_of_eq this
    · have hne : a ≠ a' := fun h => hd (by rw [h])
      refine le_of_eq_of_le ?_ hnn
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, h'⟩
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_false, false_or, and_true] at h h'
      exact hne (h.trans h'.symm)
  rw [h1, zero_add, slackTotal, Finset.sum_div]
  exact Finset.sum_le_sum fun u _ => h2 u

/-- A member of the padded family with no dummy vertices comes from `K`. -/
lemma mem_padFam_of_toRight_empty {U : Finset (Pad X m)} (hU : U ∈ padFam K m)
    (hR : U.toRight = ∅) : U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
  rw [padFam, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [toLeft_image_inl]
    exact ⟨hT, rfl⟩
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exfalso
    have : ((t.2.1, false) : Fin m × Bool) ∈ (mixTriple m t.1 t.2.1 t.2.2).toRight := by simp
    rw [hR] at this
    simp at this

/-- A member of the padded family that does use a dummy contains a *left* dummy. -/
lemma exists_left_dummy {U : Finset (Pad X m)} (hU : U ∈ padFam K m) (hR : U.toRight ≠ ∅) :
    ∃ i : Fin m, (Sum.inr (i, false) : Pad X m) ∈ U := by
  rw [padFam, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, -, rfl⟩ := hU
    exact absurd (by simp) hR
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact ⟨t.2.1, by simp [mixTriple]⟩

/-- A matching of the padded family uses at most `m` of the added triples: they are disjoint and
each contains one of the `m` left dummies. -/
lemma card_mixedPart_le (hm : 0 < m) {M : Finset (Finset (Pad X m))}
    (hM : IsMatching (padFam K m) M) :
    ((M.filter (fun U => U.toRight ≠ ∅)).card : ℝ) ≤ (m : ℝ) := by
  classical
  have hcard : (M.filter (fun U => U.toRight ≠ ∅)).card ≤ m := by
    have key : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        ∃ i : Fin m, (Sum.inr (i, false) : Pad X m) ∈ U := by
      intro U hU
      rw [Finset.mem_filter] at hU
      exact exists_left_dummy K m (hM.subset hU.1) hU.2
    set f : Finset (Pad X m) → Fin m := fun U =>
      if h : ∃ i : Fin m, (Sum.inr (i, false) : Pad X m) ∈ U then h.choose else ⟨0, hm⟩ with hf
    have hfmem : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        (Sum.inr (f U, false) : Pad X m) ∈ U := by
      intro U hU
      have h := key U hU
      rw [hf]
      simp only [dite_eq_left h]
      exact h.choose_spec
    have : (M.filter (fun U => U.toRight ≠ ∅)).card ≤ (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_le_card_of_injOn f (fun U _ => by simp) ?_
      intro U hU V hV hUV
      by_contra hne
      have hUM := (Finset.mem_filter.mp hU).1
      have hVM := (Finset.mem_filter.mp hV).1
      have hdisj := hM.disjoint U hUM V hVM hne
      have h1 := hfmem U hU
      have h2 := hfmem V hV
      rw [hUV] at h1
      exact (Finset.disjoint_left.mp hdisj h1) h2
    simpa using this
  exact_mod_cast hcard

/-- The real part of a matching of the padded family projects to a matching of `K` of the same
size. -/
lemma exists_matching_of_padMatching {M : Finset (Finset (Pad X m))}
    (hM : IsMatching (padFam K m) M) :
    ∃ M' : Finset (Finset X), IsMatching K M' ∧
      (M'.card : ℝ) = ((M.filter (fun U => U.toRight = ∅)).card : ℝ) := by
  classical
  set R := M.filter (fun U => U.toRight = ∅) with hR
  have hmem : ∀ U ∈ R, U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
    intro U hU
    rw [hR, Finset.mem_filter] at hU
    exact mem_padFam_of_toRight_empty K m (hM.subset hU.1) hU.2
  have hinj : Set.InjOn (Finset.toLeft : Finset (Pad X m) → Finset X) ↑R := by
    intro U hU V hV h
    rw [(hmem U hU).2, (hmem V hV).2, h]
  refine ⟨R.image Finset.toLeft, ⟨?_, ?_⟩, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact (hmem U hU).1
  · intro T hT T' hT' hne
    rw [Finset.mem_image] at hT hT'
    obtain ⟨U, hU, rfl⟩ := hT
    obtain ⟨V, hV, rfl⟩ := hT'
    have hUV : U ≠ V := fun h => hne (by rw [h])
    have hdisj := hM.disjoint U (Finset.mem_filter.mp hU).1 V (Finset.mem_filter.mp hV).1 hUV
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_toLeft] at hx hx'
    exact (Finset.disjoint_left.mp hdisj hx) hx'
  · rw [Finset.card_image_of_injOn hinj]

lemma padCodeg_comm (x z : Pad X m) :
    ∑ U ∈ (padFam K m).filter (fun U => x ∈ U ∧ z ∈ U), padWt K w m U
      = ∑ U ∈ (padFam K m).filter (fun U => z ∈ U ∧ x ∈ U), padWt K w m U := by
  refine Finset.sum_congr (Finset.filter_congr fun U _ => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

end

end Slack

/-- **The weighted nibble with slack.**  No near-perfection hypothesis: instead the weighting is
required to leave a total slack `S = |X| - ∑_v load v` of at least `1/γ`, and the conclusion loses
`β·|X| + 1`. -/
theorem fracNibble_withSlack (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
        IsUniform K 3 →
        (∀ T, 0 ≤ w T) →
        (∀ v : X, Slack.wLoad K w v ≤ 1) →
        (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        1 / γ ≤ (Fintype.card X : ℝ) - ∑ v : X, Slack.wLoad K w v →
        ∃ M : Finset (Finset X), IsMatching K M ∧
          (1 - β) * (∑ T ∈ K, w T) - β * (Fintype.card X : ℝ) - 1 ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ₀, hγ₀, η, hη, hmain⟩ := fracNibble_weightedCodegree 3 (by norm_num) β hβ
  have hγpos : 0 < min γ₀ 1 := lt_min hγ₀ one_pos
  refine ⟨min γ₀ 1, hγpos, ?_⟩
  intro X _ _ K w hK hw hload hcod hslack
  have hγle : min γ₀ 1 ≤ γ₀ := min_le_left _ _
  have hγ1 : min γ₀ 1 ≤ 1 := min_le_right _ _
  set γ := min γ₀ 1 with hγdef
  set S := Slack.slackTotal K w with hSdef
  have hSeq : S = (Fintype.card X : ℝ) - ∑ v : X, Slack.wLoad K w v := by
    rw [hSdef, Slack.slackTotal, Finset.sum_sub_distrib]
    simp
  have hS : 1 / γ ≤ S := by rw [hSeq]; exact hslack
  have hγS : 1 ≤ S * γ := (div_le_iff₀ hγpos).mp hS
  have hS1 : 1 ≤ S := by nlinarith
  set m := ⌈S⌉₊ with hmdef
  have hmS : S ≤ (m : ℝ) := Nat.le_ceil S
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) hmS
  have hm : 0 < m := by exact_mod_cast hmpos
  have hmlt : (m : ℝ) < S + 1 := Nat.ceil_lt_add_one (by linarith)
  have hinvm : 1 / (m : ℝ) ≤ γ := by
    rw [div_le_iff₀ hmpos]; nlinarith
  -- the padded system satisfies every hypothesis of the near-perfect weighted nibble
  have hunif := Slack.padFam_uniform K m hK
  have hnn := Slack.padWt_nonneg K w m hw hload
  have hle : ∀ v : Slack.Pad X m,
      ∑ U ∈ (Slack.padFam K m).filter (fun U => v ∈ U), Slack.padWt K w m U ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [Slack.padLoad_inl K w m hm a]
    | inr d =>
        rw [Slack.padLoad_inr K w m hm d, div_le_one hmpos]
        exact hmS
  have hge : ∀ v : Slack.Pad X m, v ∉ (∅ : Finset (Slack.Pad X m)) →
      1 - γ₀ ≤ ∑ U ∈ (Slack.padFam K m).filter (fun U => v ∈ U), Slack.padWt K w m U := by
    rintro v -
    cases v with
    | inl a => rw [Slack.padLoad_inl K w m hm a]; linarith
    | inr d =>
        rw [Slack.padLoad_inr K w m hm d, le_div_iff₀ hmpos]
        nlinarith
  have hexc : ((∅ : Finset (Slack.Pad X m)).card : ℝ)
      ≤ η * (Fintype.card (Slack.Pad X m) : ℝ) := by
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hcodeg : ∀ x z : Slack.Pad X m, x ≠ z →
      ∑ U ∈ (Slack.padFam K m).filter (fun U => x ∈ U ∧ z ∈ U), Slack.padWt K w m U ≤ γ₀ := by
    intro x z hxz
    have hmixbound : ∀ a : X, (1 - Slack.wLoad K w a) / (m : ℝ) ≤ γ₀ := by
      intro a
      have h0 : 0 ≤ Slack.wLoad K w a := Finset.sum_nonneg fun T _ => hw T
      have : (1 - Slack.wLoad K w a) / (m : ℝ) ≤ 1 / (m : ℝ) := by
        gcongr
        linarith
      linarith [hinvm]
    cases x with
    | inl a =>
        cases z with
        | inl b =>
            have hab : a ≠ b := fun h => hxz (by rw [h])
            rw [Slack.padCodeg_inl_inl K w m hab]
            exact le_trans (hcod a b hab) hγle
        | inr d =>
            rw [Slack.padCodeg_inl_inr K w m hm a d]
            exact hmixbound a
    | inr d =>
        cases z with
        | inl b =>
            rw [Slack.padCodeg_comm, Slack.padCodeg_inl_inr K w m hm b d]
            exact hmixbound b
        | inr d' =>
            have hdd : d ≠ d' := fun h => hxz (by rw [h])
            refine le_trans (Slack.padCodeg_inr_inr K w m hm hload hdd) ?_
            have hSnn : 0 ≤ S := by linarith
            have : S / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hmpos]
              nlinarith
            linarith [hinvm]
  obtain ⟨M, hM, -, hMcard⟩ :=
    hmain (Slack.padFam K m) (Slack.padWt K w m) ∅ hunif hnn hle hge hexc hcodeg
  rw [Slack.sum_padWt K w m hm] at hMcard
  have hsplit : ((M.filter (fun U => U.toRight = ∅)).card : ℝ)
      + ((M.filter (fun U => ¬ (U.toRight = ∅))).card : ℝ) = (M.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  have hmix := Slack.card_mixedPart_le K m hm hM
  obtain ⟨M', hM', hM'card⟩ := Slack.exists_matching_of_padMatching K m hM
  refine ⟨M', hM', ?_⟩
  have hloadnn : (0 : ℝ) ≤ ∑ v : X, Slack.wLoad K w v :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun T _ => hw T
  have hScard : S ≤ (Fintype.card X : ℝ) := by rw [hSeq]; linarith
  rw [hM'card]
  nlinarith only [hMcard, hmix, hsplit, hScard, hmlt, hβ.le]

-- Axiom check: `[propext, Classical.choice, Quot.sound]`.


end Nibble

end


/-! # Uniform weighted rounding with total slack -/

public section

open Finset Hypergraph

namespace Nibble

namespace SlackR

variable {X : Type} [DecidableEq X]

/-- The padded vertex type: the real vertices together with `k` columns of `m` dummies. -/
abbrev PadR (X : Type) (k m : ℕ) := X ⊕ (Fin k × Fin m)

/-- The added edge joining the real vertex `v` to the dummy `i j` of every column `j`. -/
def mixEdge (k m : ℕ) (v : X) (i : Fin k → Fin m) : Finset (PadR X k m) :=
  insert (Sum.inl v) ((univ : Finset (Fin k)).image (fun j => Sum.inr (j, i j)))

/-- The padded hypergraph: the image of `K` together with all the mixed edges. -/
def padFamR [Fintype X] (K : Finset (Finset X)) (k m : ℕ) : Finset (Finset (PadR X k m)) :=
  K.image (Finset.image Sum.inl) ∪
    (univ : Finset (X × (Fin k → Fin m))).image (fun t => mixEdge k m t.1 t.2)

/-- The padded weighting. -/
noncomputable def padWtR (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ) :
    Finset (PadR X k m) → ℝ :=
  fun U => if U.toRight = ∅ then w U.toLeft
           else (∑ v ∈ U.toLeft, (1 - Slack.wLoad K w v)) / (m : ℝ) ^ k

/-! ### Counting the dummy choices -/

/-- The number of choice functions with a prescribed value in one column. -/
theorem card_filter_eq_at (k m : ℕ) (j₀ : Fin k) (d : Fin m) :
    #(univ.filter (fun i : Fin k → Fin m => i j₀ = d)) = m ^ (k - 1) := by
  classical
  have h : (univ.filter (fun i : Fin k → Fin m => i j₀ = d))
      = Fintype.piFinset (fun j => if j = j₀ then ({d} : Finset (Fin m)) else univ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      split
      · next hj => subst hj; simpa using h
      · simp
    · intro h; have := h j₀; simpa using this
  rw [h, Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j₀)]
  rw [Finset.prod_congr rfl (fun j hj => by rw [ite_eq_right (Finset.ne_of_mem_erase hj)])]
  simp

/-- The number of choice functions with prescribed values in two distinct columns. -/
theorem card_filter_eq_at2 (k m : ℕ) {j₀ j₁ : Fin k} (hj : j₀ ≠ j₁) (d d' : Fin m) :
    #(univ.filter (fun i : Fin k → Fin m => i j₀ = d ∧ i j₁ = d')) = m ^ (k - 2) := by
  classical
  have h : (univ.filter (fun i : Fin k → Fin m => i j₀ = d ∧ i j₁ = d'))
      = Fintype.piFinset (fun j => if j = j₀ then ({d} : Finset (Fin m))
          else if j = j₁ then ({d'} : Finset (Fin m)) else univ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases h0 : j = j₀
      · subst h0; simpa using h.1
      · by_cases h1 : j = j₁
        · subst h1; simp [h0, h.2]
        · simp [h0, h1]
    · intro h
      exact ⟨by have := h j₀; simpa using this,
        by have := h j₁; simp [Ne.symm hj] at this; simpa using this⟩
  rw [h, Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j₀),
    ← Finset.mul_prod_erase (univ.erase j₀) _
      (Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ j₁⟩)]
  rw [Finset.prod_congr rfl (fun j hj' => by
    rw [ite_eq_right (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj')),
      ite_eq_right (Finset.ne_of_mem_erase hj')])]
  have hcard : #((univ.erase j₀).erase j₁) = k - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ j₁⟩),
      Finset.card_erase_of_mem (Finset.mem_univ j₀)]
    simp [Nat.sub_sub]
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hj), ite_eq_left rfl]
  simp [hcard]

/-- The sum of a constant over the choice functions with a prescribed value in one column. -/
theorem sum_ite_at (k m : ℕ) (j₀ : Fin k) (d : Fin m) (c : ℝ) :
    ∑ i : (Fin k → Fin m), (if i j₀ = d then c else 0) = c * (m : ℝ) ^ (k - 1) := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, card_filter_eq_at,
    nsmul_eq_mul]
  push_cast
  ring

/-- The sum of a constant over the choice functions with prescribed values in two columns. -/
theorem sum_ite_at2 (k m : ℕ) {j₀ j₁ : Fin k} (hj : j₀ ≠ j₁) (d d' : Fin m) (c : ℝ) :
    ∑ i : (Fin k → Fin m), (if i j₀ = d ∧ i j₁ = d' then c else 0) = c * (m : ℝ) ^ (k - 2) := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, card_filter_eq_at2 k m hj,
    nsmul_eq_mul]
  push_cast
  ring

section
variable (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ)

@[simp] lemma toLeft_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → PadR X k m)).toLeft = T := by
  ext x; simp

@[simp] lemma toRight_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → PadR X k m)).toRight = (∅ : Finset (Fin k × Fin m)) := by
  ext x; simp

@[simp] lemma mixEdge_toLeft (v : X) (i : Fin k → Fin m) :
    (mixEdge k m v i).toLeft = {v} := by
  ext x; simp [mixEdge]

@[simp] lemma mem_mixEdge_inl (v u : X) (i : Fin k → Fin m) :
    (Sum.inl u : PadR X k m) ∈ mixEdge k m v i ↔ u = v := by
  simp [mixEdge]

@[simp] lemma mem_mixEdge_inr (v : X) (i : Fin k → Fin m) (j : Fin k) (d : Fin m) :
    (Sum.inr (j, d) : PadR X k m) ∈ mixEdge k m v i ↔ i j = d := by
  simp only [mixEdge, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨j', hj'⟩)
    · exact absurd h (by simp)
    · rw [Sum.inr.injEq, Prod.ext_iff] at hj'
      obtain ⟨h1, h2⟩ := hj'
      subst h1; exact h2
  · intro h; exact Or.inr ⟨j, by rw [h]⟩

lemma mixEdge_toRight_nonempty (hk : 0 < k) (v : X) (i : Fin k → Fin m) :
    (mixEdge k m v i).toRight ≠ (∅ : Finset (Fin k × Fin m)) := by
  intro h
  have : ((⟨0, hk⟩ : Fin k), i ⟨0, hk⟩) ∈ (mixEdge k m v i).toRight := by
    rw [Finset.mem_toRight]
    exact (mem_mixEdge_inr k m v i _ _).mpr rfl
  rw [h] at this
  simp at this

lemma mixEdge_card (v : X) (i : Fin k → Fin m) : #(mixEdge k m v i) = k + 1 := by
  classical
  have hinj : Set.InjOn
      (fun j : Fin k => (Sum.inr (j, i j) : PadR X k m)) ↑(univ : Finset (Fin k)) := by
    intro a _ b _ h
    simp only [Sum.inr.injEq, Prod.ext_iff] at h
    exact h.1
  have hnot : (Sum.inl v : PadR X k m) ∉
      (univ : Finset (Fin k)).image (fun j => Sum.inr (j, i j)) := by
    simp
  rw [mixEdge, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj]
  simp

lemma mixEdge_inj {v v' : X} {i i' : Fin k → Fin m}
    (h : mixEdge k m v i = mixEdge k m v' i') : v = v' ∧ i = i' := by
  constructor
  · have hL : ({v} : Finset X) = {v'} := by
      have := congrArg Finset.toLeft h; simpa using this
    simpa using hL
  · funext j
    have h1 : (Sum.inr (j, i j) : PadR X k m) ∈ mixEdge k m v' i' := by
      rw [← h]; exact (mem_mixEdge_inr k m v i j (i j)).mpr rfl
    exact ((mem_mixEdge_inr k m v' i' j (i j)).mp h1).symm

lemma padWtR_image_inl (T : Finset X) : padWtR K w k m (T.image Sum.inl) = w T := by
  simp [padWtR]

lemma padWtR_mixEdge (hk : 0 < k) (v : X) (i : Fin k → Fin m) :
    padWtR K w k m (mixEdge k m v i) = (1 - Slack.wLoad K w v) / (m : ℝ) ^ k := by
  rw [padWtR, ite_eq_right (mixEdge_toRight_nonempty k m hk v i)]
  simp

lemma padWtR_nonneg (hw : ∀ T, 0 ≤ w T) (hload : ∀ v : X, Slack.wLoad K w v ≤ 1)
    (U : Finset (PadR X k m)) : 0 ≤ padWtR K w k m U := by
  rw [padWtR]
  split
  · exact hw _
  · have : 0 ≤ ∑ v ∈ U.toLeft, (1 - Slack.wLoad K w v) :=
      Finset.sum_nonneg fun v _ => by linarith only [hload v]
    positivity

end

section
variable [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ)

/-- A sum over the padded family splits into a sum over `K` and a sum over the mixed edges. -/
lemma sum_padFamR (hk : 0 < k) (f : Finset (PadR X k m) → ℝ) :
    ∑ U ∈ padFamR K k m, f U
      = (∑ T ∈ K, f (T.image Sum.inl))
        + ∑ v : X, ∑ i : (Fin k → Fin m), f (mixEdge k m v i) := by
  classical
  have hdisj : Disjoint (K.image (Finset.image (Sum.inl : X → PadR X k m)))
      ((univ : Finset (X × (Fin k → Fin m))).image (fun t => mixEdge k m t.1 t.2)) := by
    rw [Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨T, -, rfl⟩ := hU
    obtain ⟨t, -, ht⟩ := hU'
    have h1 : (T.image (Sum.inl : X → PadR X k m)).toRight = ∅ := by simp
    rw [← ht] at h1
    exact mixEdge_toRight_nonempty k m hk t.1 t.2 h1
  rw [padFamR, Finset.sum_union hdisj]
  congr 1
  · exact Finset.sum_image (fun T _ T' _ h => Finset.image_injective Sum.inl_injective h)
  · rw [Finset.sum_image (fun t _ t' _ h => ?_)]
    · exact Fintype.sum_prod_type _
    · obtain ⟨h1, h2⟩ := mixEdge_inj k m h
      exact Prod.ext h1 h2

lemma padFamR_uniform (hK : IsUniform K (k + 1)) : IsUniform (padFamR K k m) (k + 1) := by
  intro U hU
  rw [padFamR, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact hK T hT
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact mixEdge_card k m t.1 t.2

end

/-! ### The number of dummy choice functions -/

/-- The number of choice functions of one dummy per column, as a real number. -/
theorem card_pi_fun (d m : ℕ) : ((Fintype.card (Fin d → Fin m) : ℕ) : ℝ) = (m : ℝ) ^ d := by
  simp

/-! ### Loads, codegrees and matchings of the padded system -/

lemma pow_split_one (m k : ℕ) (hk : 0 < k) : (m : ℝ) ^ k = (m : ℝ) ^ (k - 1) * (m : ℝ) := by
  rw [← pow_succ]
  congr 1
  omega

lemma pow_split_two (m k : ℕ) (hk : 2 ≤ k) :
    (m : ℝ) ^ k = (m : ℝ) ^ (k - 2) * (m : ℝ) ^ 2 := by
  rw [← pow_add]
  congr 1
  omega

section
variable [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ)

/-- The total weight of the padded system exceeds that of `K` by exactly the total slack. -/
lemma sum_padWtR (hk : 0 < k) (hm : 0 < m) :
    ∑ U ∈ padFamR K k m, padWtR K w k m U = (∑ T ∈ K, w T) + Slack.slackTotal K w := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpk : ((m : ℝ)) ^ k ≠ 0 := ne_of_gt (pow_pos hm' k)
  rw [sum_padFamR K k m hk]
  congr 1
  · exact Finset.sum_congr rfl fun T _ => padWtR_image_inl K w k m T
  · rw [Slack.slackTotal]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [padWtR_mixEdge K w k m hk]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_pi_fun]
    field_simp

/-- Every real vertex has load exactly `1` in the padded system. -/
lemma padLoad_inl (hk : 0 < k) (hm : 0 < m) (v : X) :
    ∑ U ∈ (padFamR K k m).filter (fun U => (Sum.inl v : PadR X k m) ∈ U), padWtR K w k m U = 1 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpk : ((m : ℝ)) ^ k ≠ 0 := ne_of_gt (pow_pos hm' k)
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inl v : PadR X k m) ∈ T.image Sum.inl then
      padWtR K w k m (T.image Sum.inl) else 0) = Slack.wLoad K w v := by
    rw [Slack.wLoad, Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp [padWtR_image_inl]
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inl v : PadR X k m) ∈ mixEdge k m u i then
        padWtR K w k m (mixEdge k m u i) else 0)
      = if u = v then (1 - Slack.wLoad K w u) else 0 := by
    intro u
    simp only [mem_mixEdge_inl, padWtR_mixEdge K w k m hk]
    by_cases huv : u = v
    · subst huv
      simp only [ite_true, Finset.sum_const, Finset.card_univ, card_pi_fun,
        nsmul_eq_mul]
      field_simp
    · rw [ite_eq_right huv]
      exact Finset.sum_eq_zero fun i _ => ite_eq_right (fun h => huv h.symm)
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u),
    Finset.sum_ite_eq' Finset.univ v (fun u => 1 - Slack.wLoad K w u)]
  simp

/-- Every dummy has load exactly `S/m`. -/
lemma padLoad_inr (hk : 0 < k) (hm : 0 < m) (j : Fin k) (e : Fin m) :
    ∑ U ∈ (padFamR K k m).filter (fun U => (Sum.inr (j, e) : PadR X k m) ∈ U), padWtR K w k m U
      = Slack.slackTotal K w / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hp1 : ((m : ℝ)) ^ (k - 1) ≠ 0 := ne_of_gt (pow_pos hm' _)
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inr (j, e) : PadR X k m) ∈ T.image Sum.inl then
      padWtR K w k m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inr (j, e) : PadR X k m) ∈ mixEdge k m u i then
        padWtR K w k m (mixEdge k m u i) else 0)
      = (1 - Slack.wLoad K w u) / (m : ℝ) := by
    intro u
    simp only [mem_mixEdge_inr, padWtR_mixEdge K w k m hk]
    rw [sum_ite_at k m j e ((1 - Slack.wLoad K w u) / (m : ℝ) ^ k), pow_split_one m k hk]
    field_simp
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add, Slack.slackTotal, Finset.sum_div]

/-- The weighted codegree of two real vertices is unchanged. -/
lemma padCodeg_inl_inl (hk : 0 < k) {v v' : X} (hvv : v ≠ v') :
    ∑ U ∈ (padFamR K k m).filter
        (fun U => (Sum.inl v : PadR X k m) ∈ U ∧ (Sum.inl v' : PadR X k m) ∈ U),
      padWtR K w k m U = ∑ T ∈ K.filter (fun T => v ∈ T ∧ v' ∈ T), w T := by
  classical
  rw [Finset.sum_filter, sum_padFamR K k m hk, Finset.sum_filter]
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inl v : PadR X k m) ∈ mixEdge k m u i ∧ (Sum.inl v' : PadR X k m) ∈ mixEdge k m u i
        then padWtR K w k m (mixEdge k m u i) else 0) = 0 := by
    intro u
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    rintro ⟨ha, hb⟩
    rw [mem_mixEdge_inl] at ha hb
    exact hvv (ha.trans hb.symm)
  rw [Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp [padWtR_image_inl]

/-- The weighted codegree of a real vertex and a dummy. -/
lemma padCodeg_inl_inr (hk : 0 < k) (hm : 0 < m) (v : X) (j : Fin k) (e : Fin m) :
    ∑ U ∈ (padFamR K k m).filter
        (fun U => (Sum.inl v : PadR X k m) ∈ U ∧ (Sum.inr (j, e) : PadR X k m) ∈ U),
      padWtR K w k m U = (1 - Slack.wLoad K w v) / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hp1 : ((m : ℝ)) ^ (k - 1) ≠ 0 := ne_of_gt (pow_pos hm' _)
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inl v : PadR X k m) ∈ T.image Sum.inl ∧
      (Sum.inr (j, e) : PadR X k m) ∈ T.image Sum.inl then
        padWtR K w k m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inl v : PadR X k m) ∈ mixEdge k m u i ∧
        (Sum.inr (j, e) : PadR X k m) ∈ mixEdge k m u i
        then padWtR K w k m (mixEdge k m u i) else 0)
      = if u = v then (1 - Slack.wLoad K w u) / (m : ℝ) else 0 := by
    intro u
    simp only [mem_mixEdge_inl, mem_mixEdge_inr, padWtR_mixEdge K w k m hk]
    by_cases huv : u = v
    · subst huv
      simp only [true_and, ite_true]
      rw [sum_ite_at k m j e ((1 - Slack.wLoad K w u) / (m : ℝ) ^ k), pow_split_one m k hk]
      field_simp
    · rw [ite_eq_right huv]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right]
      rintro ⟨ha, -⟩
      exact huv ha.symm
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add,
    Finset.sum_ite_eq' Finset.univ v (fun u => (1 - Slack.wLoad K w u) / (m : ℝ))]
  simp

/-- The weighted codegree of two distinct dummies is at most `S/m²`. -/
lemma padCodeg_inr_inr (hk : 0 < k) (hm : 0 < m) (hload : ∀ v : X, Slack.wLoad K w v ≤ 1)
    {d d' : Fin k × Fin m} (hd : d ≠ d') :
    ∑ U ∈ (padFamR K k m).filter
        (fun U => (Sum.inr d : PadR X k m) ∈ U ∧ (Sum.inr d' : PadR X k m) ∈ U),
      padWtR K w k m U ≤ Slack.slackTotal K w / (m : ℝ) ^ 2 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inr d : PadR X k m) ∈ T.image Sum.inl ∧
      (Sum.inr d' : PadR X k m) ∈ T.image Sum.inl then
        padWtR K w k m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inr d : PadR X k m) ∈ mixEdge k m u i ∧
        (Sum.inr d' : PadR X k m) ∈ mixEdge k m u i
        then padWtR K w k m (mixEdge k m u i) else 0)
      ≤ (1 - Slack.wLoad K w u) / (m : ℝ) ^ 2 := by
    intro u
    have hnn : 0 ≤ (1 - Slack.wLoad K w u) / (m : ℝ) ^ 2 :=
      div_nonneg (by linarith only [hload u]) (by positivity)
    obtain ⟨j, e⟩ := d
    obtain ⟨j', e'⟩ := d'
    simp only [mem_mixEdge_inr, padWtR_mixEdge K w k m hk]
    by_cases hj : j = j'
    · subst hj
      have hee : e ≠ e' := fun h => hd (by rw [h])
      refine le_of_eq_of_le ?_ hnn
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right]
      rintro ⟨ha, hb⟩
      exact hee (ha.symm.trans hb)
    · have hk2 : 2 ≤ k := by
        by_contra hlt
        have h0 := j.isLt
        have h1 := j'.isLt
        exact hj (Fin.ext (by omega))
      have hp2 : ((m : ℝ)) ^ (k - 2) ≠ 0 := ne_of_gt (pow_pos hm' _)
      refine le_of_eq ?_
      rw [sum_ite_at2 k m hj e e' ((1 - Slack.wLoad K w u) / (m : ℝ) ^ k), pow_split_two m k hk2]
      field_simp
  rw [h1, zero_add, Slack.slackTotal, Finset.sum_div]
  exact Finset.sum_le_sum fun u _ => h2 u

lemma padCodegR_comm (x z : PadR X k m) :
    ∑ U ∈ (padFamR K k m).filter (fun U => x ∈ U ∧ z ∈ U), padWtR K w k m U
      = ∑ U ∈ (padFamR K k m).filter (fun U => z ∈ U ∧ x ∈ U), padWtR K w k m U := by
  refine Finset.sum_congr (Finset.filter_congr fun U _ => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- A member of the padded family with no dummy vertices comes from `K`. -/
lemma mem_padFamR_of_toRight_empty (hk : 0 < k) {U : Finset (PadR X k m)}
    (hU : U ∈ padFamR K k m) (hR : U.toRight = ∅) :
    U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
  rw [padFamR, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [toLeft_image_inl]
    exact ⟨hT, rfl⟩
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact absurd hR (mixEdge_toRight_nonempty k m hk t.1 t.2)

/-- A member of the padded family that uses a dummy contains a dummy of the first column. -/
lemma exists_col_zero_dummy (hk : 0 < k) {U : Finset (PadR X k m)}
    (hU : U ∈ padFamR K k m) (hR : U.toRight ≠ ∅) :
    ∃ e : Fin m, (Sum.inr (⟨0, hk⟩, e) : PadR X k m) ∈ U := by
  rw [padFamR, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, -, rfl⟩ := hU
    exact absurd (by simp) hR
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact ⟨t.2 ⟨0, hk⟩, (mem_mixEdge_inr k m t.1 t.2 _ _).mpr rfl⟩

/-- A matching of the padded family uses at most `m` of the added edges. -/
lemma card_mixedPartR_le (hk : 0 < k) (hm : 0 < m) {M : Finset (Finset (PadR X k m))}
    (hM : IsMatching (padFamR K k m) M) :
    ((M.filter (fun U => U.toRight ≠ ∅)).card : ℝ) ≤ (m : ℝ) := by
  classical
  have hcard : (M.filter (fun U => U.toRight ≠ ∅)).card ≤ m := by
    have key : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        ∃ e : Fin m, (Sum.inr (⟨0, hk⟩, e) : PadR X k m) ∈ U := by
      intro U hU
      rw [Finset.mem_filter] at hU
      exact exists_col_zero_dummy K k m hk (hM.subset hU.1) hU.2
    set f : Finset (PadR X k m) → Fin m := fun U =>
      if h : ∃ e : Fin m, (Sum.inr (⟨0, hk⟩, e) : PadR X k m) ∈ U then h.choose else ⟨0, hm⟩
      with hf
    have hfmem : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        (Sum.inr (⟨0, hk⟩, f U) : PadR X k m) ∈ U := by
      intro U hU
      have h := key U hU
      rw [hf]
      simp only [dite_eq_left h]
      exact h.choose_spec
    have : (M.filter (fun U => U.toRight ≠ ∅)).card ≤ (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_le_card_of_injOn f (fun U _ => by simp) ?_
      intro U hU V hV hUV
      by_contra hne
      have hUM := (Finset.mem_filter.mp hU).1
      have hVM := (Finset.mem_filter.mp hV).1
      have hdisj := hM.disjoint U hUM V hVM hne
      have h1 := hfmem U hU
      have h2 := hfmem V hV
      rw [hUV] at h1
      exact (Finset.disjoint_left.mp hdisj h1) h2
    simpa using this
  exact_mod_cast hcard

/-- The real part of a matching of the padded family projects to a matching of `K` of the same
size. -/
lemma exists_matching_of_padMatchingR (hk : 0 < k) {M : Finset (Finset (PadR X k m))}
    (hM : IsMatching (padFamR K k m) M) :
    ∃ M' : Finset (Finset X), IsMatching K M' ∧
      (M'.card : ℝ) = ((M.filter (fun U => U.toRight = ∅)).card : ℝ) := by
  classical
  set R := M.filter (fun U => U.toRight = ∅) with hR
  have hmem : ∀ U ∈ R, U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
    intro U hU
    rw [hR, Finset.mem_filter] at hU
    exact mem_padFamR_of_toRight_empty K k m hk (hM.subset hU.1) hU.2
  have hinj : Set.InjOn (Finset.toLeft : Finset (PadR X k m) → Finset X) ↑R := by
    intro U hU V hV h
    rw [(hmem U hU).2, (hmem V hV).2, h]
  refine ⟨R.image Finset.toLeft, ⟨?_, ?_⟩, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact (hmem U hU).1
  · intro T hT T' hT' hne
    rw [Finset.mem_image] at hT hT'
    obtain ⟨U, hU, rfl⟩ := hT
    obtain ⟨V, hV, rfl⟩ := hT'
    have hUV : U ≠ V := fun h => hne (by rw [h])
    have hdisj := hM.disjoint U (Finset.mem_filter.mp hU).1 V (Finset.mem_filter.mp hV).1 hUV
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_toLeft] at hx hx'
    exact (Finset.disjoint_left.mp hdisj hx) hx'
  · rw [Finset.card_image_of_injOn hinj]

end

/-- **The weighted nibble with slack, in uniformity `k+1`.**  No near-perfection hypothesis:
instead the weighting is required to leave a total slack of at least `1/γ`, and the conclusion
loses `β·S + 1`. -/
theorem fracNibbleR_withSlack (k : ℕ) (hk : 0 < k) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
        IsUniform K (k + 1) →
        (∀ T, 0 ≤ w T) →
        (∀ v : X, Slack.wLoad K w v ≤ 1) →
        (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        1 / γ ≤ Slack.slackTotal K w →
        ∃ M : Finset (Finset X), IsMatching K M ∧
          (1 - β) * (∑ T ∈ K, w T) - β * Slack.slackTotal K w - 1 ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ₀, hγ₀, η, hη, hmain⟩ := fracNibble_weightedCodegree (k + 1) (by omega) β hβ
  have hγpos : 0 < min γ₀ 1 := lt_min hγ₀ one_pos
  refine ⟨min γ₀ 1, hγpos, ?_⟩
  intro X _ _ K w hK hw hload hcod hslack
  have hγle : min γ₀ 1 ≤ γ₀ := min_le_left _ _
  have hγ1 : min γ₀ 1 ≤ 1 := min_le_right _ _
  set γ := min γ₀ 1 with hγdef
  set S := Slack.slackTotal K w with hSdef
  have hS : 1 / γ ≤ S := hslack
  have hγS : 1 ≤ S * γ := (div_le_iff₀ hγpos).mp hS
  have hS1 : 1 ≤ S := by nlinarith
  set m := ⌈S⌉₊ with hmdef
  have hmS : S ≤ (m : ℝ) := Nat.le_ceil S
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) hmS
  have hm : 0 < m := by exact_mod_cast hmpos
  have hmlt : (m : ℝ) < S + 1 := Nat.ceil_lt_add_one (by linarith)
  have hinvm : 1 / (m : ℝ) ≤ γ := by
    rw [div_le_iff₀ hmpos]; nlinarith
  -- the padded system satisfies every hypothesis of the near-perfect weighted nibble
  have hunif := padFamR_uniform K k m hK
  have hnn := padWtR_nonneg K w k m hw hload
  have hle : ∀ v : PadR X k m,
      ∑ U ∈ (padFamR K k m).filter (fun U => v ∈ U), padWtR K w k m U ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [padLoad_inl K w k m hk hm a]
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [padLoad_inr K w k m hk hm j e, div_le_one hmpos]
        exact hmS
  have hge : ∀ v : PadR X k m, v ∉ (∅ : Finset (PadR X k m)) →
      1 - γ₀ ≤ ∑ U ∈ (padFamR K k m).filter (fun U => v ∈ U), padWtR K w k m U := by
    rintro v -
    cases v with
    | inl a => rw [padLoad_inl K w k m hk hm a]; linarith
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [padLoad_inr K w k m hk hm j e, le_div_iff₀ hmpos]
        nlinarith
  have hexc : ((∅ : Finset (PadR X k m)).card : ℝ)
      ≤ η * (Fintype.card (PadR X k m) : ℝ) := by
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hcodeg : ∀ x z : PadR X k m, x ≠ z →
      ∑ U ∈ (padFamR K k m).filter (fun U => x ∈ U ∧ z ∈ U), padWtR K w k m U ≤ γ₀ := by
    intro x z hxz
    have hmixbound : ∀ a : X, (1 - Slack.wLoad K w a) / (m : ℝ) ≤ γ₀ := by
      intro a
      have h0 : 0 ≤ Slack.wLoad K w a := Finset.sum_nonneg fun T _ => hw T
      have : (1 - Slack.wLoad K w a) / (m : ℝ) ≤ 1 / (m : ℝ) := by
        gcongr
        linarith
      linarith [hinvm]
    cases x with
    | inl a =>
        cases z with
        | inl b =>
            have hab : a ≠ b := fun h => hxz (by rw [h])
            rw [padCodeg_inl_inl K w k m hk hab]
            exact le_trans (hcod a b hab) hγle
        | inr d =>
            obtain ⟨j, e⟩ := d
            rw [padCodeg_inl_inr K w k m hk hm a j e]
            exact hmixbound a
    | inr d =>
        obtain ⟨j, e⟩ := d
        cases z with
        | inl b =>
            rw [padCodegR_comm K w k m _ _, padCodeg_inl_inr K w k m hk hm b j e]
            exact hmixbound b
        | inr d' =>
            have hdd : (j, e) ≠ d' := fun h => hxz (by rw [h])
            refine le_trans (padCodeg_inr_inr K w k m hk hm hload hdd) ?_
            have hSnn : 0 ≤ S := by linarith
            have : S / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hmpos]
              nlinarith
            rw [← hSdef]
            linarith [hinvm]
  obtain ⟨M, hM, -, hMcard⟩ :=
    hmain (padFamR K k m) (padWtR K w k m) ∅ hunif hnn hle hge hexc hcodeg
  rw [sum_padWtR K w k m hk hm, ← hSdef] at hMcard
  have hsplit : ((M.filter (fun U => U.toRight = ∅)).card : ℝ)
      + ((M.filter (fun U => ¬ (U.toRight = ∅))).card : ℝ) = (M.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  have hmix := card_mixedPartR_le K k m hk hm hM
  obtain ⟨M', hM', hM'card⟩ := exists_matching_of_padMatchingR K k m hk hM
  refine ⟨M', hM', ?_⟩
  rw [hM'card]
  nlinarith only [hMcard, hmix, hsplit, hmlt, hβ.le]

end SlackR

export SlackR (fracNibbleR_withSlack)

-- Axiom check: `[propext, Classical.choice, Quot.sound]`.


end Nibble

end


/-! # Weighted rounding for nonuniform hypergraphs with bounded edge size -/

public section

open Finset Hypergraph

namespace Nibble

namespace LEUnif

variable {X : Type} [DecidableEq X]

/-- The padded vertex type: the real vertices together with `r` columns of `m` dummies. -/
abbrev PadV (X : Type) (r m : ℕ) := X ⊕ (Fin r × Fin m)

variable {r m : ℕ} {T : Finset X} {i : Fin (r - #T) → Fin m}

/-- The padded edge of `T` for the dummy choice `i`: one dummy in each of the first `r - #T`
columns. -/
def padEdgeD (r m : ℕ) (T : Finset X) (i : Fin (r - #T) → Fin m) : Finset (PadV X r m) :=
  T.image Sum.inl ∪ (univ : Finset (Fin (r - #T))).image
    (fun j => Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j))

/-- The padded family. -/
def padFamLE (r m : ℕ) (K : Finset (Finset X)) : Finset (Finset (PadV X r m)) :=
  K.biUnion (fun T => (univ : Finset (Fin (r - #T) → Fin m)).image (padEdgeD r m T))

/-- The padded weighting: the weight of `T` spread over its `m^(r-#T)` padded edges. -/
noncomputable def padWtLE (r m : ℕ) (w : Finset X → ℝ) : Finset (PadV X r m) → ℝ :=
  fun U => w U.toLeft / (m : ℝ) ^ (r - #U.toLeft)

@[simp] lemma mem_padEdgeD_inl {x : X} :
    (Sum.inl x : PadV X r m) ∈ padEdgeD r m T i ↔ x ∈ T := by
  simp [padEdgeD]

lemma mem_padEdgeD_inr {j : Fin r} {e : Fin m} :
    (Sum.inr (j, e) : PadV X r m) ∈ padEdgeD r m T i ↔
      ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ i j' = e := by
  constructor
  · intro h
    rw [padEdgeD, Finset.mem_union] at h
    rcases h with h | h
    · rw [Finset.mem_image] at h
      obtain ⟨x, -, hx⟩ := h
      exact absurd hx (by simp)
    · rw [Finset.mem_image] at h
      obtain ⟨j', -, hj'⟩ := h
      rw [Sum.inr.injEq, Prod.mk.injEq] at hj'
      exact ⟨j', by simpa using congrArg Fin.val hj'.1, hj'.2⟩
  · rintro ⟨j', h1, h2⟩
    rw [padEdgeD, Finset.mem_union]
    refine Or.inr ?_
    rw [Finset.mem_image]
    refine ⟨j', Finset.mem_univ _, ?_⟩
    rw [Sum.inr.injEq, Prod.mk.injEq]
    exact ⟨Fin.ext (by simpa using h1), h2⟩

@[simp] lemma padEdgeD_toLeft : (padEdgeD r m T i).toLeft = T := by
  ext x
  rw [Finset.mem_toLeft, mem_padEdgeD_inl]

lemma padEdgeD_inl_disj_inr :
    Disjoint (T.image (Sum.inl : X → PadV X r m))
      ((univ : Finset (Fin (r - #T))).image
        (fun j => Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j))) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, hb⟩ := hx'
  exact absurd hb (by simp)

lemma padEdgeD_card (hT : #T ≤ r) : #(padEdgeD r m T i) = r := by
  have hinj : Function.Injective
      (fun j : Fin (r - #T) => (Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j) : PadV X r m)) := by
    intro a b h
    simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE] at h
    exact Fin.ext h.1
  rw [padEdgeD, Finset.card_union_of_disjoint padEdgeD_inl_disj_inr,
    Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]
  omega

lemma padEdgeD_inj_i {i' : Fin (r - #T) → Fin m} (h : padEdgeD r m T i = padEdgeD r m T i') :
    i = i' := by
  funext j
  have hmem : (Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j) : PadV X r m)
      ∈ padEdgeD r m T i := by
    rw [mem_padEdgeD_inr]
    exact ⟨j, rfl, rfl⟩
  rw [h, mem_padEdgeD_inr] at hmem
  obtain ⟨j', h1, h2⟩ := hmem
  have : j' = j := Fin.ext (by simpa using h1)
  subst this
  exact h2.symm

lemma mem_padFamLE {K : Finset (Finset X)} {U : Finset (PadV X r m)} (hU : U ∈ padFamLE r m K) :
    ∃ (T : Finset X) (_ : T ∈ K) (i : Fin (r - #T) → Fin m), U = padEdgeD r m T i := by
  rw [padFamLE, Finset.mem_biUnion] at hU
  obtain ⟨T, hT, hU⟩ := hU
  rw [Finset.mem_image] at hU
  obtain ⟨i, -, rfl⟩ := hU
  exact ⟨T, hT, i, rfl⟩

lemma sum_padFamLE (K : Finset (Finset X)) (f : Finset (PadV X r m) → ℝ) :
    ∑ U ∈ padFamLE r m K, f U
      = ∑ T ∈ K, ∑ i : (Fin (r - #T) → Fin m), f (padEdgeD r m T i) := by
  classical
  have hpd : (↑K : Set (Finset X)).PairwiseDisjoint
      (fun T => (univ : Finset (Fin (r - #T) → Fin m)).image (padEdgeD r m T)) := by
    intro T hT T' hT' hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨a, -, rfl⟩ := hU
    obtain ⟨b, -, hb⟩ := hU'
    have hTT : T' = T := by
      have hc := congrArg Finset.toLeft hb
      rwa [padEdgeD_toLeft, padEdgeD_toLeft] at hc
    exact hne hTT.symm
  rw [padFamLE, Finset.sum_biUnion hpd]
  refine Finset.sum_congr rfl fun T _ => ?_
  exact Finset.sum_image fun i _ i' _ h => padEdgeD_inj_i h

lemma padWtLE_edge (w : Finset X → ℝ) :
    padWtLE r m w (padEdgeD r m T i) = w T / (m : ℝ) ^ (r - #T) := by
  rw [padWtLE, padEdgeD_toLeft]

omit [DecidableEq X] in
lemma padWtLE_nonneg (w : Finset X → ℝ) (hw : ∀ T, 0 ≤ w T) (U : Finset (PadV X r m)) :
    0 ≤ padWtLE r m w U := by
  rw [padWtLE]
  exact div_nonneg (hw _) (by positivity)

lemma padFamLE_uniform {K : Finset (Finset X)} (hK : ∀ T ∈ K, #T ≤ r) :
    IsUniform (padFamLE r m K) r := by
  intro U hU
  obtain ⟨T, hT, i, rfl⟩ := mem_padFamLE hU
  exact padEdgeD_card (hK T hT)

lemma mul_pow_sub_one_div (x y : ℝ) (hy : 0 < y) (a : ℕ) (ha : 0 < a) :
    x * y ^ (a - 1) / y ^ a = x / y := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have hy' : y ≠ 0 := ne_of_gt hy
  field_simp

lemma mul_pow_sub_two_div (x y : ℝ) (hy : 0 < y) (a : ℕ) (ha : 2 ≤ a) :
    x * y ^ (a - 2) / y ^ a = x / y ^ 2 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  have hy' : y ≠ 0 := ne_of_gt hy
  field_simp

/-- One prescribed dummy: the weight `x` spread over `m^d` choices contributes `x/m`. -/
lemma sum_col_one (hm : 0 < m) (x : ℝ) {d : ℕ} (j₀ : Fin d) (e : Fin m) :
    ∑ f : (Fin d → Fin m), (if f j₀ = e then x / (m : ℝ) ^ d else 0) = x / (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) j₀.isLt
  rw [SlackR.sum_ite_at d m j₀ e (x / (m : ℝ) ^ d), div_mul_eq_mul_div,
    mul_pow_sub_one_div _ _ hm' d hd]

/-- Two prescribed dummies in different columns contribute `x/m²`. -/
lemma sum_col_two (hm : 0 < m) (x : ℝ) {d : ℕ} {j₀ j₁ : Fin d} (hj : j₀ ≠ j₁) (e e' : Fin m) :
    ∑ f : (Fin d → Fin m), (if f j₀ = e ∧ f j₁ = e' then x / (m : ℝ) ^ d else 0)
      = x / (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd : 2 ≤ d := by
    by_contra hlt
    have h0 := j₀.isLt
    have h1 := j₁.isLt
    have : (j₀ : ℕ) = (j₁ : ℕ) := by omega
    exact hj (Fin.ext this)
  rw [SlackR.sum_ite_at2 d m hj e e' (x / (m : ℝ) ^ d), div_mul_eq_mul_div,
    mul_pow_sub_two_div _ _ hm' d hd]

omit [DecidableEq X] in
/-- The sum of the padded weight over the padded edges of one `T`. -/
lemma sum_over_i (hm : 0 < m) (w : Finset X → ℝ) (T : Finset X) :
    ∑ _i : (Fin (r - #T) → Fin m), w T / (m : ℝ) ^ (r - #T) = w T := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, SlackR.card_pi_fun]
  field_simp

lemma sum_padWtLE (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ) :
    ∑ U ∈ padFamLE r m K, padWtLE r m w U = ∑ T ∈ K, w T := by
  rw [sum_padFamLE]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [padWtLE_edge]
  exact sum_over_i hm w T

lemma padLoad_inl (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ) (v : X) :
    Slack.wLoad (padFamLE r m K) (padWtLE r m w) (Sum.inl v) = Slack.wLoad K w v := by
  classical
  rw [Slack.wLoad, Slack.wLoad, Finset.sum_filter, sum_padFamLE, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [mem_padEdgeD_inl, padWtLE_edge]
  by_cases hv : v ∈ T
  · simp only [ite_eq_left hv]
    exact sum_over_i hm w T
  · simp [hv]

lemma padLoad_inr (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ) (j : Fin r)
    (e : Fin m) :
    Slack.wLoad (padFamLE r m K) (padWtLE r m w) (Sum.inr (j, e))
      = (∑ T ∈ K.filter (fun T => (j : ℕ) < r - #T), w T) / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Slack.wLoad, Finset.sum_filter, sum_padFamLE, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [mem_padEdgeD_inr, padWtLE_edge]
  by_cases hj : (j : ℕ) < r - #T
  · rw [ite_eq_left hj]
    have hcond : ∀ f : Fin (r - #T) → Fin m,
        (∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e) ↔ f ⟨(j : ℕ), hj⟩ = e := by
      intro f
      constructor
      · rintro ⟨j', h1, h2⟩
        have : j' = ⟨(j : ℕ), hj⟩ := Fin.ext (by simpa using h1)
        rwa [this] at h2
      · intro h
        exact ⟨⟨(j : ℕ), hj⟩, rfl, h⟩
    simp only [hcond]
    exact sum_col_one hm (w T) ⟨(j : ℕ), hj⟩ e
  · rw [ite_eq_right hj, zero_div]
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [ite_eq_right]
    rintro ⟨j', h1, -⟩
    exact hj (h1 ▸ j'.isLt)

lemma padCodeg_inl_inl (K : Finset (Finset X)) (w : Finset X → ℝ) (hm : 0 < m) {v v' : X} :
    ∑ U ∈ (padFamLE r m K).filter
        (fun U => (Sum.inl v : PadV X r m) ∈ U ∧ (Sum.inl v' : PadV X r m) ∈ U),
      padWtLE r m w U = ∑ T ∈ K.filter (fun T => v ∈ T ∧ v' ∈ T), w T := by
  classical
  rw [Finset.sum_filter, sum_padFamLE, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [mem_padEdgeD_inl, padWtLE_edge]
  by_cases hv : v ∈ T ∧ v' ∈ T
  · simp only [ite_eq_left hv]
    exact sum_over_i hm w T
  · simp [hv]

lemma padCodeg_inl_inr (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ)
    (hw : ∀ T, 0 ≤ w T) (v : X) (j : Fin r) (e : Fin m) :
    ∑ U ∈ (padFamLE r m K).filter
        (fun U => (Sum.inl v : PadV X r m) ∈ U ∧ (Sum.inr (j, e) : PadV X r m) ∈ U),
      padWtLE r m w U ≤ Slack.wLoad K w v / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFamLE, Slack.wLoad, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_le_sum fun T _ => ?_
  simp only [mem_padEdgeD_inl, mem_padEdgeD_inr, padWtLE_edge]
  by_cases hv : v ∈ T
  · rw [ite_eq_left hv]
    by_cases hj : (j : ℕ) < r - #T
    · have hcond : ∀ f : Fin (r - #T) → Fin m,
          (v ∈ T ∧ ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e) ↔ f ⟨(j : ℕ), hj⟩ = e := by
        intro f
        constructor
        · rintro ⟨-, j', h1, h2⟩
          have : j' = ⟨(j : ℕ), hj⟩ := Fin.ext (by simpa using h1)
          rwa [this] at h2
        · intro h
          exact ⟨hv, ⟨(j : ℕ), hj⟩, rfl, h⟩
      simp only [hcond]
      rw [sum_col_one hm (w T) ⟨(j : ℕ), hj⟩ e]
    · have hzero : ∑ f : (Fin (r - #T) → Fin m),
          (if v ∈ T ∧ ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e
            then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
        refine Finset.sum_eq_zero fun f _ => ?_
        rw [ite_eq_right]
        rintro ⟨-, j', h1, -⟩
        exact hj (h1 ▸ j'.isLt)
      rw [hzero]
      exact div_nonneg (hw T) hm'.le
  · have hzero : ∑ f : (Fin (r - #T) → Fin m),
        (if v ∈ T ∧ ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e
          then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, -⟩
      exact hv h
    rw [hzero, ite_eq_right hv, zero_div]

lemma padCodeg_inr_inr (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ)
    (hw : ∀ T, 0 ≤ w T) {j j' : Fin r} {e e' : Fin m} (hne : (j, e) ≠ (j', e')) :
    ∑ U ∈ (padFamLE r m K).filter
        (fun U => (Sum.inr (j, e) : PadV X r m) ∈ U ∧ (Sum.inr (j', e') : PadV X r m) ∈ U),
      padWtLE r m w U ≤ (∑ T ∈ K, w T) / (m : ℝ) ^ 2 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFamLE, Finset.sum_div]
  refine Finset.sum_le_sum fun T _ => ?_
  simp only [mem_padEdgeD_inr, padWtLE_edge]
  by_cases hj : (j : ℕ) = (j' : ℕ)
  · -- same column: the two dummies cannot both occur
    have hee : e ≠ e' := by
      intro h
      exact hne (Prod.ext (Fin.ext hj) h)
    have hzero : ∑ f : (Fin (r - #T) → Fin m),
        (if (∃ a : Fin (r - #T), (a : ℕ) = (j : ℕ) ∧ f a = e) ∧
            (∃ b : Fin (r - #T), (b : ℕ) = (j' : ℕ) ∧ f b = e')
          then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [ite_eq_right]
      rintro ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩
      have : a = b := Fin.ext (by rw [ha1, hj, ← hb1])
      subst this
      exact hee (ha2.symm.trans hb2)
    rw [hzero]
    exact div_nonneg (hw T) (by positivity)
  · by_cases hjr : (j : ℕ) < r - #T ∧ (j' : ℕ) < r - #T
    · obtain ⟨hj1, hj2⟩ := hjr
      have hcond : ∀ f : Fin (r - #T) → Fin m,
          ((∃ a : Fin (r - #T), (a : ℕ) = (j : ℕ) ∧ f a = e) ∧
            (∃ b : Fin (r - #T), (b : ℕ) = (j' : ℕ) ∧ f b = e'))
            ↔ (f ⟨(j : ℕ), hj1⟩ = e ∧ f ⟨(j' : ℕ), hj2⟩ = e') := by
        intro f
        constructor
        · rintro ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩
          have hA : a = ⟨(j : ℕ), hj1⟩ := Fin.ext (by simpa using ha1)
          have hB : b = ⟨(j' : ℕ), hj2⟩ := Fin.ext (by simpa using hb1)
          exact ⟨hA ▸ ha2, hB ▸ hb2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨⟨(j : ℕ), hj1⟩, rfl, h1⟩, ⟨⟨(j' : ℕ), hj2⟩, rfl, h2⟩⟩
      simp only [hcond]
      have hjj : (⟨(j : ℕ), hj1⟩ : Fin (r - #T)) ≠ ⟨(j' : ℕ), hj2⟩ := by
        intro h
        exact hj (by simpa using congrArg Fin.val h)
      rw [sum_col_two hm (w T) hjj e e']
    · have hzero : ∑ f : (Fin (r - #T) → Fin m),
          (if (∃ a : Fin (r - #T), (a : ℕ) = (j : ℕ) ∧ f a = e) ∧
              (∃ b : Fin (r - #T), (b : ℕ) = (j' : ℕ) ∧ f b = e')
            then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
        refine Finset.sum_eq_zero fun f _ => ?_
        rw [ite_eq_right]
        rintro ⟨⟨a, ha1, -⟩, ⟨b, hb1, -⟩⟩
        exact hjr ⟨ha1 ▸ a.isLt, hb1 ▸ b.isLt⟩
      rw [hzero]
      exact div_nonneg (hw T) (by positivity)

lemma padCodegLE_comm (K : Finset (Finset X)) (w : Finset X → ℝ) (x z : PadV X r m) :
    ∑ U ∈ (padFamLE r m K).filter (fun U => x ∈ U ∧ z ∈ U), padWtLE r m w U
      = ∑ U ∈ (padFamLE r m K).filter (fun U => z ∈ U ∧ x ∈ U), padWtLE r m w U := by
  refine Finset.sum_congr (Finset.filter_congr fun U _ => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Weighted handshake.** -/
lemma sum_wLoad_eq [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) :
    ∑ v : X, Slack.wLoad K w v = ∑ T ∈ K, (#T : ℝ) * w T := by
  classical
  simp_rw [Slack.wLoad, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- A matching of the padded family projects to a matching of `K` of the same size. -/
lemma exists_matching_of_padMatchingLE {K : Finset (Finset X)} (hne : ∀ T ∈ K, T.Nonempty)
    {M : Finset (Finset (PadV X r m))} (hM : IsMatching (padFamLE r m K) M) :
    ∃ M' : Finset (Finset X), IsMatching K M' ∧ (M'.card : ℝ) = (M.card : ℝ) := by
  classical
  have hmem : ∀ U ∈ M, U.toLeft ∈ K ∧ (U.toLeft).Nonempty := by
    intro U hU
    obtain ⟨T, hT, i, rfl⟩ := mem_padFamLE (hM.subset hU)
    rw [padEdgeD_toLeft]
    exact ⟨hT, hne T hT⟩
  have hdisjL : ∀ U ∈ M, ∀ V ∈ M, U ≠ V → Disjoint U.toLeft V.toLeft := by
    intro U hU V hV hUV
    have hdisj := hM.disjoint U hU V hV hUV
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_toLeft] at hx hx'
    exact (Finset.disjoint_left.mp hdisj hx) hx'
  have hinj : Set.InjOn (Finset.toLeft : Finset (PadV X r m) → Finset X) ↑M := by
    intro U hU V hV h
    by_contra hUV
    obtain ⟨x, hx⟩ := (hmem U hU).2
    have hx' : x ∈ V.toLeft := by rw [← h]; exact hx
    exact (Finset.disjoint_left.mp (hdisjL U hU V hV hUV) hx) hx'
  refine ⟨M.image Finset.toLeft, ⟨?_, ?_⟩, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact (hmem U hU).1
  · intro T hT T' hT' hTT
    rw [Finset.mem_image] at hT hT'
    obtain ⟨U, hU, rfl⟩ := hT
    obtain ⟨V, hV, rfl⟩ := hT'
    exact hdisjL U hU V hV (fun h => hTT (by rw [h]))
  · rw [Finset.card_image_of_injOn hinj]

end LEUnif

/-- **The weighted nibble for hypergraphs with edges of size at most `r`.**  For every accuracy `β`
and every bound `r` on the edge size there are a codegree threshold `γ` and a constant `C`,
depending on `β` and `r` alone, such that every weighting of a family of nonempty edges of size at
most `r` with loads at most `1` and weighted codegrees at most `γ` admits a matching of size at
least `(1-β)·∑w − β·|X| − C`. -/
theorem fracNibble_leUniform (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
        (∀ T ∈ K, T.Nonempty ∧ #T ≤ r) →
        (∀ T, 0 ≤ w T) →
        (∀ v : X, Slack.wLoad K w v ≤ 1) →
        (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset X), IsMatching K M ∧
          (1 - β) * (∑ T ∈ K, w T) - β * (Fintype.card X : ℝ) - C ≤ (M.card : ℝ) := by
  classical
  have hrpos : (0 : ℝ) < 1 + (r : ℝ) := by positivity
  set b : ℝ := β / (1 + (r : ℝ)) with hbdef
  have hb : 0 < b := by positivity
  have hbβ : b ≤ β := by
    rw [hbdef, div_le_iff₀ hrpos]
    nlinarith
  obtain ⟨γ₂, hγ₂, hmain⟩ := fracNibbleR_withSlack (r - 1) (by omega) b hb
  refine ⟨min γ₂ 1, lt_min hγ₂ one_pos, b * (r : ℝ) * (1 / γ₂ + 3) + 1, by positivity, ?_⟩
  intro X _ _ K w hsize hw hload hcod
  set W : ℝ := ∑ T ∈ K, w T with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun T _ => hw T
  set m : ℕ := ⌈W⌉₊ + ⌈1 / γ₂⌉₊ + 1 with hmdef
  have hm : 0 < m := by omega
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmW : W + 1 / γ₂ ≤ (m : ℝ) := by
    have h1 : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil W
    have h2 : 1 / γ₂ ≤ (⌈1 / γ₂⌉₊ : ℝ) := Nat.le_ceil _
    rw [hmdef]
    push_cast
    linarith
  have hmub : (m : ℝ) ≤ W + 1 / γ₂ + 3 := by
    have h1 : (⌈W⌉₊ : ℝ) < W + 1 := Nat.ceil_lt_add_one hW0
    have h2 : (⌈1 / γ₂⌉₊ : ℝ) < 1 / γ₂ + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [hmdef]
    push_cast
    linarith
  have hWm : W ≤ (m : ℝ) := by
    have : (0 : ℝ) < 1 / γ₂ := by positivity
    linarith
  have hinvm : 1 / (m : ℝ) ≤ γ₂ := by
    rw [div_le_iff₀ hm']
    have : 1 / γ₂ ≤ (m : ℝ) := by linarith
    rw [div_le_iff₀ hγ₂] at this
    linarith
  -- the padded system
  set K' := LEUnif.padFamLE r m K with hK'
  set w' := LEUnif.padWtLE r m w with hw'
  have hunif : IsUniform K' (r - 1 + 1) := by
    have hrr : r - 1 + 1 = r := by omega
    rw [hrr]
    exact LEUnif.padFamLE_uniform (fun T hT => (hsize T hT).2)
  have hnn : ∀ U, 0 ≤ w' U := fun U => LEUnif.padWtLE_nonneg w hw U
  have hfilW : ∀ p : Finset X → Prop, ∀ _ : DecidablePred p,
      ∑ T ∈ K.filter p, w T ≤ W := by
    intro p _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun T _ _ => hw T)
  have hloadPad : ∀ v : LEUnif.PadV X r m, Slack.wLoad K' w' v ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [hK', hw', LEUnif.padLoad_inl hm K w a]; exact hload a
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [hK', hw', LEUnif.padLoad_inr hm K w j e, div_le_one hm']
        exact le_trans (hfilW _ _) hWm
  have hloadX : ∀ v : X, 0 ≤ Slack.wLoad K w v :=
    fun v => Finset.sum_nonneg fun T _ => hw T
  have hcodPad : ∀ x z : LEUnif.PadV X r m, x ≠ z →
      ∑ U ∈ K'.filter (fun U => x ∈ U ∧ z ∈ U), w' U ≤ γ₂ := by
    intro x z hxz
    have hmix : ∀ a : X, Slack.wLoad K w a / (m : ℝ) ≤ γ₂ := by
      intro a
      have h1 : Slack.wLoad K w a / (m : ℝ) ≤ 1 / (m : ℝ) := by
        gcongr
        exact hload a
      linarith [hinvm]
    cases x with
    | inl a =>
        cases z with
        | inl c =>
            have hac : a ≠ c := fun h => hxz (by rw [h])
            rw [hK', hw', LEUnif.padCodeg_inl_inl K w hm]
            exact le_trans (hcod a c hac) (le_trans (min_le_left _ _) (le_refl _))
        | inr d =>
            obtain ⟨j, e⟩ := d
            exact le_trans (LEUnif.padCodeg_inl_inr hm K w hw a j e) (hmix a)
    | inr d =>
        obtain ⟨j, e⟩ := d
        cases z with
        | inl c =>
            rw [hK', hw', LEUnif.padCodegLE_comm]
            exact le_trans (LEUnif.padCodeg_inl_inr hm K w hw c j e) (hmix c)
        | inr d' =>
            obtain ⟨j', e'⟩ := d'
            have hne : (j, e) ≠ (j', e') := fun h => hxz (by rw [h])
            refine le_trans (LEUnif.padCodeg_inr_inr hm K w hw hne) ?_
            have h1 : W / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hm']
              nlinarith
            linarith [hinvm]
  -- the slack of the padded system
  have hslackEq : Slack.slackTotal K' w'
      = (∑ v : X, (1 - Slack.wLoad K' w' (Sum.inl v)))
        + ∑ d : Fin r × Fin m, (1 - Slack.wLoad K' w' (Sum.inr d)) := by
    rw [Slack.slackTotal]
    exact Fintype.sum_sum_type _
  have hdummy : ∀ d : Fin r × Fin m, Slack.wLoad K' w' (Sum.inr d) ≤ W / (m : ℝ) := by
    rintro ⟨j, e⟩
    rw [hK', hw', LEUnif.padLoad_inr hm K w j e]
    gcongr
    exact hfilW _ _
  have hslackLB : 1 / γ₂ ≤ Slack.slackTotal K' w' := by
    have hreal : 0 ≤ ∑ v : X, (1 - Slack.wLoad K' w' (Sum.inl v)) := by
      refine Finset.sum_nonneg fun v _ => ?_
      have := hloadPad (Sum.inl v)
      linarith
    have hdum : (Fintype.card (Fin r × Fin m) : ℝ) * (1 - W / (m : ℝ))
        ≤ ∑ d : Fin r × Fin m, (1 - Slack.wLoad K' w' (Sum.inr d)) := by
      have hconst : (Fintype.card (Fin r × Fin m) : ℝ) * (1 - W / (m : ℝ))
          = ∑ _d : Fin r × Fin m, (1 - W / (m : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hconst]
      refine Finset.sum_le_sum fun d _ => ?_
      have := hdummy d
      linarith
    have hcardrm : (Fintype.card (Fin r × Fin m) : ℝ) = (r : ℝ) * (m : ℝ) := by
      simp
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    have hmWpos : 1 / γ₂ ≤ (m : ℝ) - W := by linarith
    have hkey : (r : ℝ) * (m : ℝ) * (1 - W / (m : ℝ)) = (r : ℝ) * ((m : ℝ) - W) := by
      field_simp
    rw [hslackEq]
    rw [hcardrm, hkey] at hdum
    nlinarith [hmWpos]
  obtain ⟨M, hM, hMcard⟩ :=
    hmain K' w' hunif hnn hloadPad hcodPad hslackLB
  -- the total weight and the size of the slack
  have hsumw' : ∑ U ∈ K', w' U = W := LEUnif.sum_padWtLE hm K w
  have hslackUB : Slack.slackTotal K' w'
      ≤ (Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ) := by
    have hbound : ∀ v : LEUnif.PadV X r m, 1 - Slack.wLoad K' w' v ≤ 1 := by
      intro v
      have : 0 ≤ Slack.wLoad K' w' v := Finset.sum_nonneg fun U _ => hnn U
      linarith
    have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset (LEUnif.PadV X r m))) => hbound v)
    rw [Slack.slackTotal]
    refine le_trans this ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : (Fintype.card (LEUnif.PadV X r m) : ℝ)
        = (Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ) := by simp
    rw [this]
  have hWX : W ≤ (Fintype.card X : ℝ) := by
    have h1 : W ≤ ∑ T ∈ K, (#T : ℝ) * w T := by
      refine Finset.sum_le_sum fun T hT => ?_
      have h2 : (1 : ℝ) ≤ (#T : ℝ) := by
        have := (hsize T hT).1
        have : 1 ≤ #T := Finset.card_pos.mpr this
        exact_mod_cast this
      nlinarith [hw T]
    have h3 : ∑ v : X, Slack.wLoad K w v ≤ (Fintype.card X : ℝ) := by
      have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset X)) => hload v)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
      exact this
    rw [LEUnif.sum_wLoad_eq K w] at h3
    linarith
  obtain ⟨M', hM', hM'card⟩ :=
    LEUnif.exists_matching_of_padMatchingLE (fun T hT => (hsize T hT).1) hM
  refine ⟨M', hM', ?_⟩
  rw [hM'card]
  rw [hsumw'] at hMcard
  have hslackbound : b * Slack.slackTotal K' w'
      ≤ β * (Fintype.card X : ℝ) + b * (r : ℝ) * (1 / γ₂ + 3) := by
    have h1 : b * Slack.slackTotal K' w'
        ≤ b * ((Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hslackUB hb.le
    have h2 : (r : ℝ) * (m : ℝ) ≤ (r : ℝ) * (W + 1 / γ₂ + 3) := by
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hmub hr0
    have hbr : b * (1 + (r : ℝ)) = β := by
      rw [hbdef]
      field_simp
    nlinarith [hb.le, hWX, hW0]
  have hbw : b * W ≤ β * W := mul_le_mul_of_nonneg_right hbβ hW0
  linarith only [hMcard, hslackbound, hbw]

-- Axiom check: `[propext, Classical.choice, Quot.sound]`.

/-- The proved theorem meets the independently stated bounded-edge interface. -/
theorem boundedEdgeWeightedRounding_holds : Hypergraph.BoundedEdgeWeightedRounding := by
  intro r hr β hβ
  exact fracNibble_leUniform r hr β hβ

end Nibble
