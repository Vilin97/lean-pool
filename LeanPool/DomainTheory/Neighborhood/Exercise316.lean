/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise315

/-!
# Exercise 3.16 (Scott 1981, PRG-19, §3) — the infinite iterate `𝒟^∞`

Scott: for a neighbourhood system `𝒟` over `Δ`, let `Δ^∞ = ⋃ₙ 1ⁿ0Δ` be infinitely
many disjoint
copies of `Δ`, and let `𝒟^∞` be the *least* family of subsets with

1. `Δ^∞ ∈ 𝒟^∞`, and
2. `X ∈ 𝒟`, `Y ∈ 𝒟^∞` ⟹ `0X ∪ 1Y ∈ 𝒟^∞`.

He asks to show `𝒟^∞` is a neighbourhood system over `Δ^∞`, that `𝒟^∞ ≅ 𝒟 × 𝒟^∞`,
and that the
elements of `|𝒟^∞|` are in one-one correspondence with arbitrary infinite
sequences `⟨xₙ⟩` of
elements `xₙ ∈ |𝒟|`, via the combinations of neighbourhoods

`0X₀ ∪ 10X₁ ∪ ⋯ ∪ 1ⁿ0Xₙ ∪ ⋯`   (with all but finitely many `Xₘ = Δ`).

**Model.** We take the token type to be `ℕ × α`, where `(n, a)` is "the token `a ∈
Δ` sitting in
the `n`-th copy" (i.e. Scott's `1ⁿ0a`). A neighbourhood `0X₀ ∪ 1ⁿ0Xₙ ∪ ⋯` is then
exactly the set
`{(i, a) ∣ a ∈ Xᵢ}`, recovered from `W` by its **fibers** `fiber W i = {a ∣ (i, a)
∈ W}`. The
"least family" description is equivalent to: `W ∈ 𝒟^∞` iff every fiber is a
neighbourhood and all
but finitely many fibers equal `Δ`. (Closure under (2) and the base (1) generate
exactly these, and
no fewer, because (2) is the one-step "cons" and the cofinite-`Δ` condition is its
iterate.)

The element-level payoff is the clean order-isomorphism

`iterSeqEquiv : |𝒟^∞| ≃o (ℕ → |𝒟|)`

(Scott's "one-one correspondence with infinite sequences"), from which `𝒟^∞ ≅ 𝒟 ×
𝒟^∞` falls out by
the shift `(ℕ → E) ≃o E × (ℕ → E)`.

Everything is **choice-free in spirit**; the classical content is only what is
inherited from the
project's `Element.ext`/`prodEquiv` machinery, as elsewhere in §3.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

/-! ### Fibers of a set of `(copy index, token)` pairs. -/

/-- The `i`-th *fiber* of a set `W ⊆ ℕ × α`: the tokens appearing in copy `i`. -/
def fiber (W : Set (ℕ × α)) (i : ℕ) : Set α := {a | (i, a) ∈ W}

@[simp] theorem mem_fiber {W : Set (ℕ × α)} {i : ℕ} {a : α} : a ∈ fiber W i ↔ (i, a) ∈ W := Iff.rfl

theorem fiber_mono {W W' : Set (ℕ × α)} (h : W ⊆ W') (i : ℕ) : fiber W i ⊆ fiber W' i :=
  fun _ ha => h ha

theorem fiber_inter (W W' : Set (ℕ × α)) (i : ℕ) :
    fiber (W ∩ W') i = fiber W i ∩ fiber W' i := rfl

theorem eq_of_fiber_eq {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i = fiber W' i) : W = W' := by
  ext ⟨i, a⟩
  exact Set.ext_iff.mp (h i) a

theorem subset_of_fiber_subset {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i ⊆ fiber W' i) :
    W ⊆ W' := fun ⟨i, _⟩ ha => h i ha

/-! ### The pinning neighbourhood `single n X` (Scott's `1ⁿ0X`, rest `Δ`). -/

variable (V : NeighborhoodSystem α)

/-- The `𝒟^∞`-neighbourhood pinning copy `n` to `X` and leaving all other copies
at `Δ`: Scott's
`Δ^∞ ∩ (1ⁿ0X)`, i.e. the combination with `Xₙ = X` and `Xₘ = Δ` for `m ≠ n`. -/
def single (n : ℕ) (X : Set α) : Set (ℕ × α) :=
  {p | if p.1 = n then p.2 ∈ X else p.2 ∈ V.master}

variable {V}

@[simp] theorem fiber_single_self (n : ℕ) (X : Set α) : fiber (single V n X) n = X := by
  ext a; simp [fiber, single]

theorem fiber_single_ne {n i : ℕ} (h : i ≠ n) (X : Set α) : fiber (single V n X) i = V.master := by
  ext a; simp [fiber, single, h]

theorem single_mono {n : ℕ} {X X' : Set α} (h : X ⊆ X') : single V n X ⊆ single V n X' := by
  intro p hp
  simp only [single, Set.mem_setOf_eq] at hp ⊢
  by_cases hc : p.1 = n
  · rw [if_pos hc] at hp ⊢; exact h hp
  · rw [if_neg hc] at hp ⊢; exact hp

theorem single_inter {n : ℕ} (X X' : Set α) :
    single V n X ∩ single V n X' = single V n (X ∩ X') := by
  apply eq_of_fiber_eq
  intro i
  by_cases h : i = n
  · subst h; rw [fiber_inter, fiber_single_self, fiber_single_self, fiber_single_self]
  · rw [fiber_inter, fiber_single_ne h, fiber_single_ne h, fiber_single_ne h, Set.inter_self]

/-! ### The system `𝒟^∞`. -/

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The infinite iterate `𝒟^∞` over `Δ^∞ =
ℕ × Δ`:
`W ∈ 𝒟^∞` iff every fiber is a neighbourhood of `𝒟` and all but finitely many
fibers equal `Δ`. -/
def iterSys (V : NeighborhoodSystem α) : NeighborhoodSystem (ℕ × α) where
  mem W := (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master
  master := {p | p.2 ∈ V.master}
  master_mem := ⟨fun _ => V.master_mem, 0, fun _ _ => rfl⟩
  inter_mem := by
    rintro W W' Z ⟨hWf, NW, hNW⟩ ⟨hW'f, NW', hNW'⟩ ⟨hZf, _⟩ hsub
    refine ⟨fun i => ?_, max NW NW', fun i hi => ?_⟩
    · rw [fiber_inter]
      exact V.inter_mem (hWf i) (hW'f i) (hZf i) (fiber_mono hsub i)
    · rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
  sub_master := by
    rintro W ⟨hWf, _⟩ ⟨i, a⟩ ha
    exact V.sub_master (hWf i) ha

@[simp] theorem iterSys_master : (iterSys V).master = {p : ℕ × α | p.2 ∈ V.master} := rfl

theorem fiber_iterSys_master (i : ℕ) : fiber ((iterSys V).master) i = V.master := rfl

@[simp] theorem mem_iterSys {W : Set (ℕ × α)} :
    (iterSys V).mem W ↔ (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master := Iff.rfl

/-- `single V n X` is a `𝒟^∞`-neighbourhood whenever `X ∈ 𝒟`. -/
theorem single_mem {n : ℕ} {X : Set α} (hX : V.mem X) : (iterSys V).mem (single V n X) := by
  refine ⟨fun i => ?_, n + 1, fun i hi => ?_⟩
  · by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact V.master_mem
  · exact fiber_single_ne (by omega : i ≠ n) X

theorem single_master (n : ℕ) : single V n V.master = (iterSys V).master := by
  apply eq_of_fiber_eq
  intro i
  rw [fiber_iterSys_master]
  by_cases h : i = n
  · subst h; rw [fiber_single_self]
  · rw [fiber_single_ne h]

/-- Every `𝒟^∞`-neighbourhood is contained in the pinning of its own `i`-th fiber. -/
theorem subset_single {W : Set (ℕ × α)} (hW : (iterSys V).mem W) (i : ℕ) :
    W ⊆ single V i (fiber W i) := by
  rintro ⟨j, a⟩ ha
  simp only [single, Set.mem_setOf_eq]
  by_cases h : j = i
  · rw [if_pos h]; subst h; exact ha
  · rw [if_neg h]; exact V.sub_master (hW.1 j) ha

theorem interUpTo_subset_master (F : ℕ → Set (ℕ × α)) (N : ℕ) :
    (iterSys V).interUpTo F N ⊆ (iterSys V).master := by
  induction N with
  | zero => exact subset_rfl
  | succ n ih => rw [NeighborhoodSystem.interUpTo_succ]; exact Set.inter_subset_left.trans ih

/-- The finite intersection `⋂_{i<N} single i (fiber W i)` reconstructs `W` from
below, once `N`
exceeds the cofinite-`Δ` bound of `W`. -/
theorem reconstruct_subset {W : Set (ℕ × α)} (_hW : (iterSys V).mem W) {N : ℕ}
    (hN : ∀ i, N ≤ i → fiber W i = V.master) :
    (iterSys V).interUpTo (fun i => single V i (fiber W i)) N ⊆ W := by
  rintro ⟨j, a⟩ ha
  by_cases h : j < N
  · have hsub := (iterSys V).interUpTo_subset (fun i => single V i (fiber W i)) h
    have hmem : (j, a) ∈ single V j (fiber W j) := hsub ha
    simpa [single] using hmem
  · have haM : a ∈ V.master := interUpTo_subset_master (fun i => single V i (fiber W i)) N ha
    have : a ∈ fiber W j := by rw [hN j (not_lt.mp h)]; exact haM
    exact this

/-! ### Components and sequences. -/

/-- The `n`-th component `xₙ ∈ |𝒟|` of a `𝒟^∞`-element `z` (Scott's coordinate at
copy `n`). -/
def component (z : (iterSys V).Element) (n : ℕ) : V.Element where
  mem X := V.mem X ∧ z.mem (single V n X)
  sub h := h.1
  master_mem := ⟨V.master_mem, by rw [single_master]; exact z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz : z.mem (single V n (X ∩ X')) := by rw [← single_inter]; exact z.inter_mem hzX hzX'
    have hmem : V.mem (X ∩ X') := by
      have := (z.sub hz).1 n; rwa [fiber_single_self] at this
    exact ⟨hmem, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    exact ⟨hX', z.up_mem hzX (single_mem hX') (single_mono hXX')⟩

@[simp] theorem mem_component {z : (iterSys V).Element} {n : ℕ} {X : Set α} :
    (component z n).mem X ↔ V.mem X ∧ z.mem (single V n X) := Iff.rfl

/-- The `𝒟^∞`-element determined by an infinite sequence `⟨xₙ⟩` of `𝒟`-elements:
the neighbourhoods
`W` whose every fiber lies in the corresponding `xᵢ`. -/
def ofSeq (seq : ℕ → V.Element) : (iterSys V).Element where
  mem W := (iterSys V).mem W ∧ ∀ i, (seq i).mem (fiber W i)
  sub h := h.1
  master_mem := ⟨(iterSys V).master_mem, fun i => by
    rw [fiber_iterSys_master]; exact (seq i).master_mem⟩
  inter_mem := by
    rintro W W' ⟨hW, hWf⟩ ⟨hW', hW'f⟩
    refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [fiber_inter]; exact (seq i).sub ((seq i).inter_mem (hWf i) (hW'f i))
    · obtain ⟨NW, hNW⟩ := hW.2
      obtain ⟨NW', hNW'⟩ := hW'.2
      refine ⟨max NW NW', fun i hi => ?_⟩
      rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
    · rw [fiber_inter]; exact (seq i).inter_mem (hWf i) (hW'f i)
  up_mem := by
    rintro W W' ⟨_, hWf⟩ hW' hWW'
    exact ⟨hW', fun i => (seq i).up_mem (hWf i) (hW'.1 i) (fiber_mono hWW' i)⟩

@[simp] theorem mem_ofSeq {seq : ℕ → V.Element} {W : Set (ℕ × α)} :
    (ofSeq seq).mem W ↔ (iterSys V).mem W ∧ ∀ i, (seq i).mem (fiber W i) := Iff.rfl

theorem ofSeq_mono {seq seq' : ℕ → V.Element} (h : ∀ n, seq n ≤ seq' n) :
    ofSeq seq ≤ ofSeq seq' := by
  rintro W ⟨hW, hf⟩
  exact ⟨hW, fun i => h i _ (hf i)⟩

/-! ### The two round-trips. -/

@[simp] theorem component_ofSeq (seq : ℕ → V.Element) (n : ℕ) :
    component (ofSeq seq) n = seq n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨_, _, hfib⟩
    have := hfib n; rwa [fiber_single_self] at this
  · intro hX
    refine ⟨(seq n).sub hX, single_mem ((seq n).sub hX), fun i => ?_⟩
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact (seq i).master_mem

@[simp] theorem ofSeq_component (z : (iterSys V).Element) :
    ofSeq (fun n => component z n) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hW, hfib⟩
    obtain ⟨N, hN⟩ := hW.2
    exact z.up_mem (z.mem_interUpTo _ (n := N) (fun i _ => (hfib i).2)) hW
      (reconstruct_subset hW hN)
  · intro hzW
    refine ⟨z.sub hzW, fun i => ?_⟩
    exact ⟨(z.sub hzW).1 i, z.up_mem hzW (single_mem ((z.sub hzW).1 i)) (
      subset_single (z.sub hzW) i)⟩

/-- `z ⊑ z'` is detected component-wise. -/
theorem le_of_component_le {z z' : (iterSys V).Element}
    (h : ∀ n, component z n ≤ component z' n) : z ≤ z' := by
  have hmono := ofSeq_mono h
  rwa [ofSeq_component, ofSeq_component] at hmono

/-! ### Scott's two conclusions. -/

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The elements of `|𝒟^∞|` are in
one-one,
order-preserving correspondence with infinite sequences `⟨xₙ⟩` of elements of
`|𝒟|`. -/
def iterSeqEquiv (V : NeighborhoodSystem α) : (iterSys V).Element ≃o (∀ _ : ℕ, V.Element) where
  toFun z := fun n => component z n
  invFun seq := ofSeq seq
  left_inv z := ofSeq_component z
  right_inv seq := by funext n; exact component_ofSeq seq n
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h
      exact le_of_component_le (fun n => h n)
    · intro h n X hX
      exact ⟨hX.1, h (single V n X) hX.2⟩

/-- The shift order-isomorphism `(ℕ → E) ≃o E × (ℕ → E)`, `f ↦ (f 0, f ∘ succ)`. -/
def natShiftEquiv (E : Type*) [Preorder E] : (ℕ → E) ≃o E × (ℕ → E) where
  toFun f := (f 0, fun n => f (n + 1))
  invFun p := fun n => Nat.casesOn n p.1 (fun m => p.2 m)
  left_inv f := by funext n; cases n <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h0, hs⟩
      intro n
      cases n with
      | zero => exact h0
      | succ m => exact hs m
    · intro h
      exact ⟨h 0, fun m => h (m + 1)⟩

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The isomorphism `|𝒟^∞| ≃o |𝒟 × 𝒟^∞|`,
obtained from the
sequence correspondence and the shift. -/
def iterProdIso (V : NeighborhoodSystem α) :
    (iterSys V).Element ≃o (prod V (iterSys V)).Element :=
  (iterSeqEquiv V).trans <|
    (natShiftEquiv V.Element).trans <|
      (prodCongrOrderIso (OrderIso.refl V.Element) (iterSeqEquiv V).symm).trans
        (prodEquiv V (iterSys V)).symm

/-- **Exercise 3.16 (Scott 1981, PRG-19).** `𝒟^∞ ≅ 𝒟 × 𝒟^∞`. -/
theorem iter_isomorphic (V : NeighborhoodSystem α) : iterSys V ≅ᴰ prod V (iterSys V) :=
  ⟨iterProdIso V⟩

/-! ### The coordinate projections `𝒟^∞ → 𝒟` (used in Exercise 3.24(ii)). -/

open ApproximableMap

/-- The `n`-th coordinate projection `projN n : 𝒟^∞ → 𝒟`, `W (projN n) X ↔ fiber W
n ⊆ X`. -/
def projN (V : NeighborhoodSystem α) (n : ℕ) : ApproximableMap (iterSys V) V where
  rel W X := (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, V.master_mem, by rw [fiber_iterSys_master]⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    exact ⟨hW, V.inter_mem hX hX' (hW.1 n) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, _, hsub⟩ hW₂W hXX₂ hW₂ hX₂
    exact ⟨hW₂, hX₂, (fiber_mono hW₂W n).trans (hsub.trans hXX₂)⟩

@[simp] theorem projN_rel {n : ℕ} {W : Set (ℕ × α)} {X : Set α} :
    (projN V n).rel W X ↔ (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X := Iff.rfl

/-- `projN n` extracts the `n`-th component: `projN n (z) = component z n`. -/
@[simp] theorem toElementMap_projN (z : (iterSys V).Element) (n : ℕ) :
    (projN V n).toElementMap z = component z n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨W, hzW, hW, hX, hsub⟩
    refine ⟨hX, z.up_mem hzW (single_mem hX) ?_⟩
    refine subset_of_fiber_subset (fun i => ?_)
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hsub
    · rw [fiber_single_ne h]; exact V.sub_master (hW.1 i)
  · rintro ⟨hX, hz⟩
    exact ⟨single V n X, hz, single_mem hX, hX, by rw [fiber_single_self]⟩

end Domain.Neighborhood
