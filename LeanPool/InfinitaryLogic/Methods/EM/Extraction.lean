/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.EM.Indiscernible
/-!
# Extraction Scaffolding for Indiscernible Sequences

This file provides the model-theoretic scaffolding that reduces the task
"extract a pairwise-distinct ℕ-indexed restricted-indiscernible sequence
from a large model" (`MorleyHanfExtraction`) to a smaller combinatorial-
model-theoretic residual (a per-formula partition step).

## Main definitions

- `IsIndiscernibleOnSet a Γ S` : `a : I → M` is indiscernible on the subset
  `S : Set I` for the family of formulas `Γ`. Equivalently, for every
  `⟨n, φ⟩ ∈ Γ` and every two strictly-increasing tuples `t, t' : Fin n → I`
  with all entries in `S`, the truth values of `φ` on `a ∘ t` and `a ∘ t'`
  agree.

## Main results

- `IsIndiscernibleOnSet.toLomega1omegaIndiscernibleOn` (sequence-level
  reduction): if `f : ℕ → I` is strictly monotone and `Set.range f` is
  `IsIndiscernibleOnSet` for the range of a formula sequence `s`, then the
  assembled `a ∘ f : ℕ → M` is `IsLomega1omegaIndiscernibleOn (Set.range s)`.

## Scope

This file does NOT prove any combinatorial extraction theorem — the goal is
to provide the model-theoretic bridge that turns an already-extracted
indiscernible subset into the restricted-indiscernible sequence consumed
by the Phase-2 bridge `hasArbLargeModels_of_restricted_extraction`. The
existence of the indiscernible subset (Erdős–Rado-style partition content)
remains a separate hypothesis for a future tranche.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-! ### Indiscernibility on a subset -/

section IndiscernibleOnSet

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

/-- `IsIndiscernibleOnSet a Γ S` expresses that `a : I → M` is indiscernible
on the subset `S ⊆ I` for the family of formulas `Γ ⊆ Σ n, L.BoundedFormulaω Empty n`:
for every `⟨n, φ⟩ ∈ Γ` and every two strictly-increasing `n`-tuples drawn
from `S`, the truth values of `φ` on the corresponding `a`-tuples agree.

This is the natural "homogeneous subset" notion used in Erdős–Rado-style
extraction arguments: a set `S` is `IsIndiscernibleOnSet` for `Γ` iff all
`Γ`-formulas have constant truth on strictly-increasing tuples in `S`. -/
def IsIndiscernibleOnSet (a : I → M)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) (S : Set I) : Prop :=
  ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty n}, ⟨n, φ⟩ ∈ Γ →
    ∀ (t t' : Fin n → I),
      StrictMono t → StrictMono t' →
      (∀ k, t k ∈ S) → (∀ k, t' k ∈ S) →
      (φ.Realize (Empty.elim : Empty → M) (a ∘ t) ↔
       φ.Realize (Empty.elim : Empty → M) (a ∘ t'))

/-- Monotonicity: shrinking either the formula family or the subset
preserves indiscernibility. -/
theorem IsIndiscernibleOnSet.mono {a : I → M}
    {Γ Γ' : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ ⊆ Γ')
    {S S' : Set I} (hS : S ⊆ S')
    (h : IsIndiscernibleOnSet a Γ' S') :
    IsIndiscernibleOnSet a Γ S := by
  unfold IsIndiscernibleOnSet
  intro n φ hφ t t' ht ht' htS ht'S
  exact h (hΓ hφ) t t' ht ht' (fun k => hS (htS k)) (fun k => hS (ht'S k))

end IndiscernibleOnSet

/-! ### Sequence-level reduction to `IsLomega1omegaIndiscernibleOn` -/

section Reduction

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

/-- **Sequence-level reduction**: if `f : ℕ → I` is strictly monotone and
its range is `IsIndiscernibleOnSet` for the range of a formula sequence `s`,
then the composed sequence `a ∘ f : ℕ → M` is
`IsLomega1omegaIndiscernibleOn (Set.range s)`.

This is the bridge from "extracted indiscernible subset" to "restricted-
indiscernible ℕ-sequence" consumed by `MorleyHanfExtraction`. -/
theorem IsIndiscernibleOnSet.toLomega1omegaIndiscernibleOn
    (a : I → M) (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (f : ℕ → I) (hf : StrictMono f)
    (hInd : IsIndiscernibleOnSet a (Set.range s) (Set.range f)) :
    IsLomega1omegaIndiscernibleOn (a ∘ f) (Set.range s) := by
  intro n φ hmem u t hu ht
  -- `f ∘ u` and `f ∘ t` are strictly-monotone `n`-tuples in `Set.range f`.
  have hfu : StrictMono (f ∘ u) := hf.comp hu
  have hft : StrictMono (f ∘ t) := hf.comp ht
  have huS : ∀ k, (f ∘ u) k ∈ Set.range f := fun k => ⟨u k, rfl⟩
  have htS : ∀ k, (f ∘ t) k ∈ Set.range f := fun k => ⟨t k, rfl⟩
  have hkey := hInd hmem (f ∘ u) (f ∘ t) hfu hft huS htS
  -- `(a ∘ f) ∘ u = a ∘ (f ∘ u)` and similarly for `t`, by function composition.
  show φ.Realize (Empty.elim : Empty → M) ((a ∘ f) ∘ u) ↔
       φ.Realize (Empty.elim : Empty → M) ((a ∘ f) ∘ t)
  have hcompU : ((a ∘ f) ∘ u : Fin n → M) = a ∘ (f ∘ u) := rfl
  have hcompT : ((a ∘ f) ∘ t : Fin n → M) = a ∘ (f ∘ t) := rfl
  rw [hcompU, hcompT]
  exact hkey

end Reduction

end FirstOrder.Language
