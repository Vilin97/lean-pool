/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Product
import LeanPool.DomainTheory.Neighborhood.Exercise319Sum

/-!
# Example 6.1 (Scott 1981, PRG-19, §6) — the tree algebra `D^§` and the domain
equation
`D^§ ≅ D + (D^§ × D^§)`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19
(1981), Lecture VI,
*Introduction to domain equations*. Starting from a fixed domain `D` (a
neighbourhood system over `Δ`)
Scott iterates the product `D × D` *indefinitely* and collects all the iterates
into a **single**
domain `D^§`, the *tree algebra* over `D`. The construction:

* the tokens of `D^§` live in `Γ = {1,2}* 0 Δ` — a finite `{1,2}`-path (here a
`List Bool`, `true = 1`,
  `false = 2`) followed by a separator `0` and a `D`-token in `Δ`. We model this
  as `List Bool × α`
  with the master neighbourhood `Γ = {t | t.2 ∈ Δ}`;
* the neighbourhoods of `D^§` are the **least** family containing (i) `Γ`, (ii)
`0X = {([], a) ∣ a ∈ X}`
  for `X ∈ 𝒟`, and (iii) `1P ∪ 2Q` for `P, Q ∈ 𝒟^§`. This is the inductive
  predicate `MemS`.

The heart of the example is Scott's verification that `D^§` is a neighbourhood
system: closure under
consistent intersection, proved by induction on the way `X` was put into `D^§`,
using the standing
assumption `∅ ∉ 𝒟` (passed as `hD : ∀ X, 𝒟.mem X → X.Nonempty`). The pay-off is
the **domain
equation**

`D^§ ≅ D + (D^§ × D^§)`,

formalized as the order-isomorphism `dsharpEquiv : (Dsharp D hD).Element ≃o (sum D
(prod …) …).Element`,
i.e. `Dsharp D hD ≅ᴰ sum D (prod (Dsharp D hD) (Dsharp D hD)) …`.

We use the project's `+` (`sum`, Exercise 3.18) and `×` (`prod`, Definition 3.1).
All *data* is
choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-! ### Token embeddings `0X`, `1P`, `2Q` and the master `Γ`. -/

/-- `0X = {([], a) ∣ a ∈ X}`: the `0`-tagged copy of a `D`-neighbourhood `X`
(empty
`{1,2}`-path). -/
def embZero (X : Set α) : Set (List Bool × α) := {t | t.1 = [] ∧ t.2 ∈ X}

/-- `1P = {(1::p, a) ∣ (p, a) ∈ P}`: the `1`-prefixed copy of a
`D^§`-neighbourhood `P`. -/
def embL (P : Set (List Bool × α)) : Set (List Bool × α) :=
  {t | ∃ p', t.1 = true :: p' ∧ (p', t.2) ∈ P}

/-- `2Q = {(2::q, a) ∣ (q, a) ∈ Q}`: the `2`-prefixed copy of a
`D^§`-neighbourhood `Q`. -/
def embR (Q : Set (List Bool × α)) : Set (List Bool × α) :=
  {t | ∃ q', t.1 = false :: q' ∧ (q', t.2) ∈ Q}

/-- `1P ∪ 2Q`: the product-style neighbourhood of `D^§`. -/
def embPair (P Q : Set (List Bool × α)) : Set (List Bool × α) := embL P ∪ embR Q

/-- The master neighbourhood `Γ = {1,2}* 0 Δ` of `D^§`: any path, `D`-token in
`Δ`. -/
def Gamma (D : NeighborhoodSystem α) : Set (List Bool × α) := {t | t.2 ∈ D.master}

@[simp] theorem mem_embZero {X : Set α} {p : List Bool} {a : α} :
    (p, a) ∈ embZero X ↔ p = [] ∧ a ∈ X := Iff.rfl

@[simp] theorem mem_embL {P : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embL P ↔ ∃ p', p = true :: p' ∧ (p', a) ∈ P := Iff.rfl

@[simp] theorem mem_embR {Q : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embR Q ↔ ∃ q', p = false :: q' ∧ (q', a) ∈ Q := Iff.rfl

@[simp] theorem mem_embPair {P Q : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embPair P Q ↔
      (∃ p', p = true :: p' ∧ (p', a) ∈ P) ∨ (∃ q', p = false :: q' ∧ (q', a) ∈ Q) := Iff.rfl

@[simp] theorem mem_Gamma {D : NeighborhoodSystem α} {p : List Bool} {a : α} :
    (p, a) ∈ Gamma D ↔ a ∈ D.master := Iff.rfl

/-! ### Intersection identities. -/

theorem embZero_inter (X X' : Set α) :
    embZero X ∩ embZero X' = embZero (X ∩ X' : Set α) := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embZero]
  tauto

theorem embPair_inter (P Q P' Q' : Set (List Bool × α)) :
    embPair P Q ∩ embPair P' Q' = embPair (P ∩ P') (Q ∩ Q') := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embPair]
  rcases p with _ | ⟨b, ps⟩
  · simp
  · cases b <;> simp [List.cons.injEq]

theorem embZero_inter_embPair (X : Set α) (P Q : Set (List Bool × α)) :
    embZero X ∩ embPair P Q = ∅ := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embZero, mem_embPair, Set.mem_empty_iff_false, iff_false,
    not_and, not_or]
  rintro ⟨rfl, -⟩
  exact ⟨by rintro ⟨p', hp', -⟩; exact absurd hp' (by simp), by
    rintro ⟨q', hq', -⟩; exact absurd hq' (by simp)⟩

/-! ### Subset / injectivity. -/

theorem embZero_subset {X X' : Set α} : embZero X ⊆ embZero X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha
    have : (([], a) : List Bool × α) ∈ embZero X' := h ⟨rfl, ha⟩
    exact this.2
  · intro h t ht; exact ⟨ht.1, h ht.2⟩

theorem embPair_subset {P Q P' Q' : Set (List Bool × α)} :
    embPair P Q ⊆ embPair P' Q' ↔ P ⊆ P' ∧ Q ⊆ Q' := by
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨p', a⟩ := t
      have hmem : ((true :: p', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inl ⟨p', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', hP'⟩ | ⟨q'', hq'', -⟩
      · simp only [List.cons.injEq, true_and] at hp''; exact hp'' ▸ hP'
      · exact absurd hq'' (by simp)
    · obtain ⟨q', a⟩ := t
      have hmem : ((false :: q', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inr ⟨q', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', -⟩ | ⟨q'', hq'', hQ'⟩
      · exact absurd hp'' (by simp)
      · simp only [List.cons.injEq, true_and] at hq''; exact hq'' ▸ hQ'
  · rintro ⟨hP, hQ⟩ t ht
    rcases ht with ⟨p', hp', hPmem⟩ | ⟨q', hq', hQmem⟩
    · exact Or.inl ⟨p', hp', hP hPmem⟩
    · exact Or.inr ⟨q', hq', hQ hQmem⟩

theorem embZero_injective {X X' : Set α} (h : embZero X = embZero X') : X = X' :=
  Set.Subset.antisymm (embZero_subset.mp h.subset) (embZero_subset.mp h.symm.subset)

theorem embPair_injective {P Q P' Q' : Set (List Bool × α)}
    (h : embPair P Q = embPair P' Q') : P = P' ∧ Q = Q' := by
  obtain ⟨hP, hQ⟩ := embPair_subset.mp h.subset
  obtain ⟨hP', hQ'⟩ := embPair_subset.mp h.symm.subset
  exact ⟨Set.Subset.antisymm hP hP', Set.Subset.antisymm hQ hQ'⟩

/-! ### Nonemptiness and `⊆ Γ`. -/

theorem embZero_nonempty {X : Set α} (hX : X.Nonempty) : (embZero X).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨([], a), rfl, ha⟩

theorem embPair_nonempty {P Q : Set (List Bool × α)} (hP : P.Nonempty) :
    (embPair P Q).Nonempty := by
  obtain ⟨⟨p', a⟩, hP⟩ := hP; exact ⟨(true :: p', a), Or.inl ⟨p', rfl, hP⟩⟩

theorem embZero_subset_Gamma {D : NeighborhoodSystem α} {X : Set α} (hX : D.mem X) :
    embZero X ⊆ Gamma D := by
  rintro ⟨p, a⟩ ⟨-, ha⟩; exact D.sub_master hX ha

theorem embPair_subset_Gamma {D : NeighborhoodSystem α} {P Q : Set (List Bool × α)}
    (hP : P ⊆ Gamma D) (hQ : Q ⊆ Gamma D) : embPair P Q ⊆ Gamma D := by
  rintro ⟨p, a⟩ (⟨p', -, hPmem⟩ | ⟨q', -, hQmem⟩)
  · have h := hP hPmem; exact h
  · have h := hQ hQmem; exact h

theorem Gamma_nonempty {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) :
    (Gamma D).Nonempty := by
  obtain ⟨a, ha⟩ := hD D.master D.master_mem; exact ⟨([], a), ha⟩

/-! ### The neighbourhood system `D^§`. -/

/-- **Example 6.1 (Scott 1981, PRG-19).** The neighbourhoods of `D^§`, defined
inductively as the
*least* family of subsets of `Γ` containing (i) `Γ`, (ii) `0X` for `X ∈ 𝒟`, and
(iii) `1P ∪ 2Q`
whenever it already contains `P` and `Q`. This is Scott's fixed-point family
`𝒟^§ = {Γ} ∪ {0X ∣ X ∈ 𝒟} ∪ {1P ∪ 2Q ∣ P, Q ∈ 𝒟^§}`. -/
inductive MemS (D : NeighborhoodSystem α) : Set (List Bool × α) → Prop
  | gamma : MemS D (Gamma D)
  | zero {X : Set α} : D.mem X → MemS D (embZero X)
  | pair {P Q : Set (List Bool × α)} : MemS D P → MemS D Q → MemS D (embPair P Q)

/-- Every neighbourhood of `D^§` is a subset of the master `Γ` (Scott's `𝒟^§ ⊆
𝒫(Γ)`). -/
theorem memS_subset_gamma {D : NeighborhoodSystem α} {W : Set (List Bool × α)}
    (hW : MemS D W) : W ⊆ Gamma D := by
  induction hW with
  | gamma => exact subset_rfl
  | zero hX => exact embZero_subset_Gamma hX
  | pair _ _ ihP ihQ => exact embPair_subset_Gamma ihP ihQ

/-- Under Scott's standing assumption `∅ ∉ 𝒟`, no neighbourhood of `D^§` is empty. -/
theorem memS_nonempty {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {W : Set (List Bool × α)} (hW : MemS D W) : W.Nonempty := by
  induction hW with
  | gamma => exact Gamma_nonempty hD
  | zero hX => exact embZero_nonempty (hD _ hX)
  | pair _ _ ihP _ => exact embPair_nonempty ihP

/-- **Example 6.1 — closure under consistent intersection.** Scott's central
verification, "by
induction on the number of steps required to put `X` and `Y` into `𝒟^§`". The
cross cases
(`0A ∩ (1P∪2Q) = ∅`, etc.) are discharged because the consistency witness `Z` is
non-empty
(`memS_nonempty`); the `0A ∩ 0B` case uses `𝒟`'s own closure; the `(1P∪2Q) ∩
(1P'∪2Q')` case recurses
on `P, P'` and `Q, Q'`. -/
theorem memS_inter {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ {X : Set (List Bool × α)}, MemS D X → ∀ {Y : Set (List Bool × α)}, MemS D Y →
      ∀ {Z : Set (List Bool × α)}, MemS D Z → Z ⊆ X ∩ Y → MemS D (X ∩ Y) := by
  intro X hX
  induction hX with
  | gamma =>
    intro Y hY Z _ _
    rw [Set.inter_eq_right.mpr (memS_subset_gamma hY)]; exact hY
  | @zero A hA =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hA)]; exact MemS.zero hA
    | @zero B hB =>
      rw [embZero_inter]
      -- the witness `Z` must be a `0C`; read off `C ⊆ A ∩ B`, then `D`'s closure
      -- gives `A ∩ B ∈ 𝒟`.
      rw [embZero_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show ((true :: [], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        exact MemS.zero (D.inter_mem hA hB hC (embZero_subset.mp hsub))
      | @pair P Q hP hQ =>
        obtain ⟨t, hmem⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hempty : t.1 = [] := (hsub hmem).1
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · rw [hp'] at hempty; exact absurd hempty (by simp)
        · rw [hq'] at hempty; exact absurd hempty (by simp)
    | @pair P Q _ _ =>
      rw [embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
  | @pair P Q hP hQ ihP ihQ =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma hP) (
        memS_subset_gamma hQ))]
      exact MemS.pair hP hQ
    | @zero B hB =>
      rw [Set.inter_comm, embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
    | @pair P' Q' hP' hQ' =>
      rw [embPair_inter]
      rw [embPair_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        obtain ⟨a, ha⟩ := hD C hC
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ embZero C from ⟨rfl, ha⟩)) (by simp)
      | @pair Z₀ Z₁ hZ₀ hZ₁ =>
        obtain ⟨hsub₀, hsub₁⟩ := embPair_subset.mp hsub
        exact MemS.pair (ihP hP' hZ₀ hsub₀) (ihQ hQ' hZ₁ hsub₁)

/-- **Example 6.1 (Scott 1981, PRG-19).** The *tree algebra* `D^§`: a
neighbourhood system over
`Γ = {1,2}* 0 Δ`, under the standing assumption `∅ ∉ 𝒟` (`hD`). -/
def Dsharp (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem (List Bool × α) where
  mem := MemS D
  master := Gamma D
  master_mem := MemS.gamma
  inter_mem := fun hX hY hZ hsub => memS_inter hD hX hY hZ hsub
  sub_master := memS_subset_gamma

@[simp] theorem Dsharp_mem {D : NeighborhoodSystem α} {hD : ∀ X, D.mem X → X.Nonempty}
    {W : Set (List Bool × α)} : (Dsharp D hD).mem W ↔ MemS D W := Iff.rfl

@[simp] theorem Dsharp_master {D : NeighborhoodSystem α} {hD : ∀ X, D.mem X → X.Nonempty} :
    (Dsharp D hD).master = Gamma D := rfl

/-! ### Inversion lemmas for `D^§`-neighbourhoods.

Because the three neighbourhood shapes `Γ`, `0X`, `1P ∪ 2Q` are mutually
distinguishable (by the
shape of their `{1,2}`-paths, using non-emptiness), a `D^§`-neighbourhood of a
given shape can only
have arisen from the matching constructor. -/

theorem memS_embZero_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) {X : Set α}
    (h : MemS D (embZero X)) : D.mem X := by
  generalize hW : embZero X = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : ((true :: [], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1; exact absurd h1.1 (by simp)
  | @zero X' hX' => rw [embZero_injective hW]; exact hX'
  | @pair P Q hP hQ =>
    exfalso
    obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
    have hcons : t.1 ≠ [] := by
      rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp [hp']
      · simp [hq']
    have hz : t ∈ embZero X := by rw [← hW] at ht; exact ht
    exact hcons hz.1

theorem memS_embPair_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {P Q : Set (List Bool × α)} (h : MemS D (embPair P Q)) : MemS D P ∧ MemS D Q := by
  generalize hW : embPair P Q = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : (([], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1
    rcases h1 with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · simp at hp'
    · simp at hq'
  | @zero X hX =>
    exfalso
    obtain ⟨t, ht⟩ := embZero_nonempty (hD X hX)
    have hempty : t.1 = [] := ht.1
    rw [← hW] at ht
    rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · rw [hp'] at hempty; simp at hempty
    · rw [hq'] at hempty; simp at hempty
  | @pair P' Q' hP' hQ' =>
    obtain ⟨hPP, hQQ⟩ := embPair_injective hW
    rw [hPP, hQQ]; exact ⟨hP', hQ'⟩

/-! ### The domain equation `D^§ ≅ D + (D^§ × D^§)`. -/

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- No neighbourhood of `D^§ × D^§` is empty (needed to form the sum `D + (D^§ ×
D^§)`). -/
theorem prod_dsharp_nonempty :
    ∀ V, (prod (Dsharp D hD) (Dsharp D hD)).mem V → V.Nonempty := by
  rintro V ⟨P, Q, hP, hQ, rfl⟩
  obtain ⟨t, ht⟩ := memS_nonempty hD hP
  exact ⟨Sum.inl t, mem_prodNbhd_inl.mpr ht⟩

/-- The right-hand side of Scott's domain equation: the sum system `D + (D^§ ×
D^§)`. -/
def sumSys : NeighborhoodSystem (Option (α ⊕ ((List Bool × α) ⊕ (List Bool × α)))) :=
  sum D (prod (Dsharp D hD) (Dsharp D hD)) hD (prod_dsharp_nonempty D hD)

/-- A sum-neighbourhood of the form `0X` arises only from the left factor, so `X ∈
𝒟`. -/
theorem sum_mem_inj₀_inv {X : Set α} (h : (sumSys D hD).mem (inj₀ X)) : D.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := prod_dsharp_nonempty D hD Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

/-- A sum-neighbourhood of the form `1V` arises only from the right factor, so `V
∈ 𝒟^§ × 𝒟^§`. -/
theorem sum_mem_inj₁_inv {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    (h : (sumSys D hD).mem (inj₁ V)) : (prod (Dsharp D hD) (Dsharp D hD)).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := hD X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

/-- No neighbourhood of the sum `D + (D^§ × D^§)` is empty. -/
theorem sumSys_mem_nonempty {W : Set (Option (α ⊕ ((List Bool × α) ⊕ (List Bool × α))))}
    (h : (sumSys D hD).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (hD X hX)
  · exact inj₁_nonempty (prod_dsharp_nonempty D hD Y hY)

/-- **Example 6.1 — the forward half of the domain equation.** Sends an element
`z` of `D^§` to an
element of `D + (D^§ × D^§)`, recording for each branch which `0X`/`1V`
neighbourhoods `z` reaches:
`0X ∈ toS z ↔ embZero X ∈ z` and `1(P∪Q) ∈ toS z ↔ (1P∪2Q) ∈ z`. -/
def toS (z : (Dsharp D hD).Element) : (sumSys D hD).Element where
  mem W := W = sumMaster D (prod (Dsharp D hD) (Dsharp D hD))
    ∨ (∃ X, D.mem X ∧ W = inj₀ X ∧ z.mem (embZero X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = inj₁ (prodNbhd P Q) ∧ z.mem (embPair P Q))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨prodNbhd P Q, prod_mem_prodNbhd hP hQ, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨P', Q', hP', hQ', rfl, hzPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [sumMaster_inter_inj₁ (prod_mem_prodNbhd hP' hQ')], hzPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embZero_inter] at hz
        exact memS_embZero_inv hD (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embZero_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzPQ'; rw [embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (prod_mem_prodNbhd hP hQ)], hzPQ⟩)
    · exfalso
      have hz := z.inter_mem hzPQ hzX'; rw [Set.inter_comm, embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [inj₁_inter, prodNbhd_inter], ?_⟩)
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).1
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).2
      · have hz := z.inter_mem hzPQ hzPQ'; rwa [embPair_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩) hW' hsub
    · left
      exact eq_sumMaster_of_subset hW' hsub
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemS.zero hX') (embZero_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · obtain ⟨a, ha⟩ := hD X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := prod_dsharp_nonempty D hD (prodNbhd P Q) (prod_mem_prodNbhd hP hQ)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨P', Q', hP', hQ', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := prodNbhd_subset_iff.mp (inj₁_subset_inj₁.mp hsub)
        exact z.up_mem hzPQ (MemS.pair hP' hQ') (embPair_subset.mpr ⟨hPP, hQQ⟩)

@[simp] theorem toS_mem_inj₀ {z : (Dsharp D hD).Element} {X : Set α} (hX : D.mem X) :
    (toS D hD z).mem (inj₀ X) ↔ z.mem (embZero X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨P, Q, hP, hQ, heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := hD X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toS_mem_inj₁ {z : (Dsharp D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (toS D hD z).mem (inj₁ (prodNbhd P Q)) ↔ z.mem (embPair P Q) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨P', Q', hP', hQ', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := hD X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · obtain ⟨hPP, hQQ⟩ := prodNbhd_injective (inj₁_injective heq)
      rw [hPP, hQQ]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hz⟩)

/-- **Example 6.1 — the inverse half of the domain equation.** Sends an element
`s` of
`D + (D^§ × D^§)` back to an element of `D^§`. -/
def fromS (s : (sumSys D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D
    ∨ (∃ X, D.mem X ∧ W = embZero X ∧ s.mem (inj₀ X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = embPair P Q ∧ s.mem (inj₁ (prodNbhd P Q)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact MemS.gamma
    · exact MemS.zero hX
    · exact MemS.pair hP hQ
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨P', Q', hP', hQ', rfl, hsPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX',
        by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma hX')], hsX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [Set.inter_eq_right.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP') (memS_subset_gamma hQ'))], hsPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hX)], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embZero_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv D hD (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsPQ'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_eq_left.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP) (memS_subset_gamma hQ))], hsPQ⟩)
    · exfalso
      have hs := s.inter_mem hsPQ hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [embPair_inter], ?_⟩)
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).1
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).2
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embZero_subset.mp hsub))
      | @pair P' Q' hP' hQ' =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        have hmem : (([], a) : List Bool × α) ∈ embPair P' Q' := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        have hz : t ∈ embZero X' := hsub ht
        exact hcons hz.1
      | @pair P' Q' hP' hQ' =>
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact s.up_mem hsPQ (Or.inr (Or.inr ⟨prodNbhd P' Q', prod_mem_prodNbhd hP' hQ', rfl⟩))
          (inj₁_subset_inj₁.mpr (prodNbhd_subset_iff.mpr ⟨hPP, hQQ⟩))

theorem embZero_ne_Gamma (X : Set α) : embZero X ≠ Gamma D := by
  intro h
  obtain ⟨a, ha⟩ := hD D.master D.master_mem
  have hmem : ((true :: [], a) : List Bool × α) ∈ Gamma D := ha
  rw [← h] at hmem; exact absurd hmem.1 (by simp)

theorem embPair_ne_Gamma (P Q : Set (List Bool × α)) : embPair P Q ≠ Gamma D := by
  intro h
  obtain ⟨a, ha⟩ := hD D.master D.master_mem
  have hmem : (([], a) : List Bool × α) ∈ Gamma D := ha
  rw [← h] at hmem
  rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · simp at hp'
  · simp at hq'

theorem embZero_ne_embPair {X : Set α} (hX : D.mem X) (P Q : Set (List Bool × α)) :
    embZero X ≠ embPair P Q := by
  intro h
  obtain ⟨a, ha⟩ := hD X hX
  have hmem : (([], a) : List Bool × α) ∈ embPair P Q := h ▸ (⟨rfl, ha⟩ : ([], a) ∈ embZero X)
  rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · simp at hp'
  · simp at hq'

@[simp] theorem fromS_mem_embZero {s : (sumSys D hD).Element} {X : Set α} (hX : D.mem X) :
    (fromS D hD s).mem (embZero X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P, Q, hP, hQ, heq, hs⟩)
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rwa [embZero_injective heq]
    · exact absurd heq (embZero_ne_embPair D hD hX P Q)
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromS_mem_embPair {s : (sumSys D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (fromS D hD s).mem (embPair P Q) ↔ s.mem (inj₁ (prodNbhd P Q)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P', Q', hP', hQ', heq, hs⟩)
    · exact absurd h0 (embPair_ne_Gamma D hD P Q)
    · exact absurd heq.symm (embZero_ne_embPair D hD hX' P Q)
    · obtain ⟨hPP, hQQ⟩ := embPair_injective heq
      rw [hPP, hQQ]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hs⟩)

/-- `fromS ∘ toS = id`. -/
theorem fromS_toS (z : (Dsharp D hD).Element) : fromS D hD (toS D hD z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact z.master_mem
    · exact (toS_mem_inj₀ D hD hX).mp hs
    · exact (toS_mem_inj₁ D hD hP hQ).mp hs
  · intro hW
    cases z.sub hW with
    | gamma => exact Or.inl rfl
    | @zero X hX => exact Or.inr (Or.inl ⟨X, hX, rfl, (toS_mem_inj₀ D hD hX).mpr hW⟩)
    | @pair P Q hP hQ => exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (toS_mem_inj₁ D hD hP hQ).mpr hW⟩)

/-- `toS ∘ fromS = id`. -/
theorem toS_fromS (s : (sumSys D hD).Element) : toS D hD (fromS D hD s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromS_mem_embZero D hD hX).mp hs
    · exact (fromS_mem_embPair D hD hP hQ).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromS_mem_embZero D hD hX).mpr hW⟩)
    · obtain ⟨P, Q, hP, hQ, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (fromS_mem_embPair D hD hP hQ).mpr hW⟩)

/-- **Example 6.1 (Scott 1981, PRG-19) — the domain equation, as an
order-isomorphism.**
`|D^§| ≃o |D + (D^§ × D^§)|`. -/
def dsharpEquiv : (Dsharp D hD).Element ≃o (sumSys D hD).Element where
  toFun := toS D hD
  invFun := fromS D hD
  left_inv := fromS_toS D hD
  right_inv := toS_fromS D hD
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h X hX
      cases z.sub hX with
      | gamma => exact z'.master_mem
      | @zero A hA =>
        exact (toS_mem_inj₀ D hD hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      | @pair P Q hP hQ =>
        exact (toS_mem_inj₁ D hD hP hQ).mp (h _ (Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, h _ hzPQ⟩)

/-- **Example 6.1 (Scott 1981, PRG-19) — the domain equation `D^§ ≅ D + (D^§ ×
D^§)`.** The tree
algebra `D^§` is, as a domain, isomorphic to `D + (D^§ × D^§)` — Scott's defining
isomorphism, "as can
be seen by reference to the equation for `D^§` and the definitions of `+` and
`×`". -/
theorem dsharp_domain_equation :
    Dsharp D hD ≅ᴰ sum D (prod (Dsharp D hD) (Dsharp D hD)) hD (prod_dsharp_nonempty D hD) :=
  ⟨dsharpEquiv D hD⟩

/-! ### The isomorphic injections `x ↦ x^§` and `x, y ↦ ⟨x, y⟩`.

Scott exhibits the *finite-element* structure of `|D^§|` through two one-one
(information-preserving)
injections: `λx. x^§ : D → D^§` and `λx, y. ⟨x, y⟩ : D^§ × D^§ → D^§`, with bottom
`⊥ = {Γ}`
(the system's own `bot`). -/

/-- Scott's injection `x^§ = {Γ} ∪ {0X ∣ X ∈ x}` of a `D`-element into `D^§`. -/
def inSharp (x : D.Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ X, x.mem X ∧ W = embZero X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact MemS.gamma
    · exact MemS.zero (x.sub hX)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma (x.sub hX'))]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma (x.sub hX))]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embZero_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' => exact Or.inr ⟨X', x.up_mem hX hX' (embZero_subset.mp hsub), rfl⟩
      | @pair P Q hP hQ =>
        exfalso
        obtain ⟨a, ha⟩ := hD X (x.sub hX)
        have hmem : (([], a) : List Bool × α) ∈ embPair P Q := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'

/-- **Example 6.1 (Scott 1981, PRG-19).** `λx. x^§` is an *isomorphic injection*:
`x^§ ⊑ x'^§ ↔
x ⊑ x'`
(in particular one-one). -/
theorem inSharp_le_iff {x x' : D.Element} : inSharp D hD x ≤ inSharp D hD x' ↔ x ≤ x' := by
  constructor
  · intro h X hX
    rcases h (embZero X) (Or.inr ⟨X, hX, rfl⟩) with h0 | ⟨X', hX', heq⟩
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rw [← embZero_injective heq] at hX'; exact hX'
  · intro h W hW
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h _ hX, rfl⟩

/-- Scott's pairing `⟨x, y⟩ = {Γ} ∪ {1P ∪ 2Q ∣ P ∈ x, Q ∈ y}` of two
`D^§`-elements. -/
def pairSharp (x y : (Dsharp D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ P Q, x.mem P ∧ y.mem Q ∧ W = embPair P Q
  sub := by
    rintro W (rfl | ⟨P, Q, hP, hQ, rfl⟩)
    · exact MemS.gamma
    · exact MemS.pair (x.sub hP) (y.sub hQ)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) (rfl | ⟨P', Q', hP', hQ', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨P', Q', hP', hQ', by
        rw [Set.inter_eq_right.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP'))
          (memS_subset_gamma (y.sub hQ')))]⟩
    · exact Or.inr ⟨P, Q, hP, hQ, by
        rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP))
          (memS_subset_gamma (y.sub hQ)))]⟩
    · exact Or.inr ⟨P ∩ P', Q ∩ Q', x.inter_mem hP hP', y.inter_mem hQ hQ', by rw [embPair_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD (x.sub hP)) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        exact hcons (hsub ht).1
      | @pair P' Q' hP' hQ' =>
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact Or.inr ⟨P', Q', x.up_mem hP hP' hPP, y.up_mem hQ hQ' hQQ, rfl⟩

/-- **Example 6.1 (Scott 1981, PRG-19).** `λx, y. ⟨x, y⟩` is an *isomorphic
injection*:
`⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑ y'`. -/
theorem pairSharp_le_iff {x x' y y' : (Dsharp D hD).Element} :
    pairSharp D hD x y ≤ pairSharp D hD x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun P hP => ?_, fun Q hQ => ?_⟩
    · rcases h (embPair P (Gamma D)) (Or.inr ⟨P, Gamma D, hP, y.master_mem, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD P (Gamma D))
      · obtain ⟨hPP, -⟩ := embPair_injective heq; rw [← hPP] at hP'; exact hP'
    · rcases h (embPair (Gamma D) Q) (Or.inr ⟨Gamma D, Q, x.master_mem, hQ, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD (Gamma D) Q)
      · obtain ⟨-, hQQ⟩ := embPair_injective heq; rw [← hQQ] at hQ'; exact hQ'
  · rintro ⟨hx, hy⟩ W hW
    rcases hW with rfl | ⟨P, Q, hP, hQ, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨P, Q, hx _ hP, hy _ hQ, rfl⟩

end Equation

end Example61

end Domain.Neighborhood
