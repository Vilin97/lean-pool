/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
/-!
# Tail-restricted `L_{ω₁ω}` indiscernibility (neutral definition)

The bare definition of tail-restricted indiscernibility, factored out so both the EM stretching
pipeline (`Methods/EM/TailAdapter.lean`, which keeps every EM-dependent downstream lemma) and the
deliberately EM-free local `EMContext` re-base (`Methods/LocalEMContext.lean`) can refer to it
without either importing the other.

The definition depends only on `BoundedFormulaω.Realize`, `StrictMono`, and `ℕ`/`Fin` — nothing
from the EM/Admissible stack — so this file sits low in the import graph. It is on the default
surface (imported by `TailAdapter.lean` → `Admissible.lean`); being neutral and tiny, that is
harmless, unlike routing the def through the WIP-excluded `LocalEMSupport.lean`.
-/

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type*} [L.Structure M]

/-- **Tail-restricted indiscernibility**: for every formula of the family there is a cutoff
beyond which all strictly monotone tuples of the sequence agree. Weaker than
`IsLomega1omegaIndiscernibleOn` (which is the cutoff-`0` case), and the form actually
produced by Erdős–Rado extraction arguments. -/
def IsLomega1omegaIndiscernibleOnTail (a : ℕ → M)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) : Prop :=
  ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty n}, ⟨n, φ⟩ ∈ Γ →
    ∃ N : ℕ, ∀ s t : Fin n → ℕ, StrictMono s → StrictMono t →
      (∀ k, N ≤ s k) → (∀ k, N ≤ t k) →
      (φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
       φ.Realize (Empty.elim : Empty → M) (a ∘ t))

end FirstOrder.Language
