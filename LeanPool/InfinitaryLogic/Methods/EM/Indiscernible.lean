/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
/-!
# Indiscernible Sequences for Lω₁ω

A sequence `(aᵢ)_{i ∈ I}` in a model M is Lω₁ω-indiscernible if for every
n-variable formula and every two strictly increasing n-tuples from I, the
formula holds on one iff it holds on the other.

Standalone API — does not advance the Hanf boundary.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

section Indiscernible

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

/-- A sequence `a : I → M` is Lω₁ω-indiscernible if for every n-variable
formula φ (no free variables) and every two strictly increasing maps
`s t : Fin n → I`, the formula holds on `a ∘ s` iff on `a ∘ t`. -/
def IsLomega1omegaIndiscernible (a : I → M) : Prop :=
  ∀ (n : ℕ) (φ : L.BoundedFormulaω Empty n)
    (s : Fin n → I) (_ : StrictMono s)
    (t : Fin n → I) (_ : StrictMono t),
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
    φ.Realize (Empty.elim : Empty → M) (a ∘ t)

/-- `IsLomega1omegaIndiscernibleOn a Γ` is the `Γ`-restricted form: the
indiscernibility equivalence is required only for formulas whose sigma-pair
lies in `Γ ⊆ Σ n, L.BoundedFormulaω Empty n`. Strictly weaker than
`IsLomega1omegaIndiscernible a` (which is the `Γ = Set.univ` case).

Motivation: the EM pipeline only uses indiscernibility on the countable
family `Set.range s` for a chosen formula enumeration `s`, not on all
Lω₁ω formulas. Weakening to the restricted form lets callers supply the
genuinely-needed hypothesis rather than the stronger full indiscernibility. -/
def IsLomega1omegaIndiscernibleOn (a : I → M)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) : Prop :=
  ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty n}, ⟨n, φ⟩ ∈ Γ →
    ∀ (s t : Fin n → I), StrictMono s → StrictMono t →
      letI := ‹L.Structure M›
      φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
      φ.Realize (Empty.elim : Empty → M) (a ∘ t)

/-- Full indiscernibility implies restricted indiscernibility on any family. -/
theorem IsLomega1omegaIndiscernible.toOn {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    IsLomega1omegaIndiscernibleOn (L := L) a Γ := by
  intro n φ _ s t hs ht
  exact h n φ s hs t ht

/-- Restricting an `On`-indiscernible sequence to a sub-order preserves
restricted indiscernibility on the same family. -/
theorem IsLomega1omegaIndiscernibleOn.restrict {a : I → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOn (L := L) a Γ)
    {J : Type*} [LinearOrder J] (e : J ↪o I) :
    IsLomega1omegaIndiscernibleOn (L := L) (a ∘ e) Γ := by
  intro n φ hφ s t hs ht
  exact h hφ (e ∘ s) (e ∘ t) (e.strictMono.comp hs) (e.strictMono.comp ht)

/-- Reindexing an `On`-indiscernible sequence by an order isomorphism
preserves restricted indiscernibility on the same family. -/
theorem IsLomega1omegaIndiscernibleOn.reindex {a : I → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOn (L := L) a Γ)
    {J : Type*} [LinearOrder J] (e : J ≃o I) :
    IsLomega1omegaIndiscernibleOn (L := L) (a ∘ e) Γ :=
  h.restrict e.toOrderEmbedding

/-- Monotonicity: shrinking the formula family preserves restricted
indiscernibility. -/
theorem IsLomega1omegaIndiscernibleOn.mono {a : I → M}
    {Γ Γ' : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ ⊆ Γ')
    (h : IsLomega1omegaIndiscernibleOn (L := L) a Γ') :
    IsLomega1omegaIndiscernibleOn (L := L) a Γ := by
  intro n φ hφ s t hs ht
  exact h (hΓ hφ) s t hs ht

/-- Restricted form of the calling-convention lemma: the restricted
indiscernibility hypothesis restated with the formula preceding the tuples. -/
theorem IsLomega1omegaIndiscernibleOn.iff_realize {a : I → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOn (L := L) a Γ)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hφ : ⟨n, φ⟩ ∈ Γ)
    {s t : Fin n → I} (hs : StrictMono s) (ht : StrictMono t) :
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
    φ.Realize (Empty.elim : Empty → M) (a ∘ t) :=
  h hφ s t hs ht

/-- Restricting an indiscernible sequence to a sub-order. -/
theorem IsLomega1omegaIndiscernible.restrict {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type*} [LinearOrder J] (e : J ↪o I) :
    IsLomega1omegaIndiscernible (L := L) (a ∘ e) :=
  fun n φ s hs t ht => h n φ (e ∘ s) (e.strictMono.comp hs) (e ∘ t) (e.strictMono.comp ht)

/-- For a 1-variable formula, truth is the same at any two indices. -/
theorem IsLomega1omegaIndiscernible.unary_const {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (φ : L.BoundedFormulaω Empty 1) (i j : I) :
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (fun _ => a i) ↔
    φ.Realize (Empty.elim : Empty → M) (fun _ => a j) :=
  h 1 φ (fun _ => i) (fun x y h => absurd h (by omega))
       (fun _ => j) (fun x y h => absurd h (by omega))

/-- The indiscernibility hypothesis, restated with the formula `φ` preceding the
tuples (a more natural calling convention than the universal form used by the
underlying definition). -/
theorem IsLomega1omegaIndiscernible.iff_realize {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n)
    {s t : Fin n → I} (hs : StrictMono s) (ht : StrictMono t) :
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
    φ.Realize (Empty.elim : Empty → M) (a ∘ t) :=
  h n φ s hs t ht

/-- The indiscernibility hypothesis, stated for bundled increasing tuples
`s t : Fin n ↪o I`. This is the natural form for working with order embeddings
of `Fin n` into the index set. -/
theorem IsLomega1omegaIndiscernible.iff_realize_of_orderEmbedding {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (s t : Fin n ↪o I) :
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
    φ.Realize (Empty.elim : Empty → M) (a ∘ t) :=
  h n φ s s.strictMono t t.strictMono

/-- Pre-composing an indiscernible sequence by an order isomorphism yields an
indiscernible sequence. A direct corollary of `restrict` via
`OrderIso.toOrderEmbedding`. -/
theorem IsLomega1omegaIndiscernible.reindex {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type*} [LinearOrder J] (e : J ≃o I) :
    IsLomega1omegaIndiscernible (L := L) (a ∘ e) :=
  h.restrict e.toOrderEmbedding

/-- For a 2-variable formula, truth is the same on any two strictly increasing
pairs from the indiscernible sequence. The binary analogue of `unary_const`. -/
theorem IsLomega1omegaIndiscernible.pair_const {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (φ : L.BoundedFormulaω Empty 2) {i₁ i₂ j₁ j₂ : I}
    (hi : i₁ < i₂) (hj : j₁ < j₂) :
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (a ∘ ![i₁, i₂]) ↔
    φ.Realize (Empty.elim : Empty → M) (a ∘ ![j₁, j₂]) := by
  have aux : ∀ {p q : I}, p < q → StrictMono (![p, q] : Fin 2 → I) := by
    intro p q hpq x y hxy
    match x, y with
    | 0, 0 => exact absurd hxy (by decide)
    | 0, 1 => simpa using hpq
    | 1, 0 => exact absurd hxy (by decide)
    | 1, 1 => exact absurd hxy (by decide)
  exact h 2 φ ![i₁, i₂] (aux hi) ![j₁, j₂] (aux hj)

end Indiscernible

end FirstOrder.Language
