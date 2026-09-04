/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
/-!
# Iterated Skolemization: the staged language tower and its colimit `L^Sk`

The bespoke Ehrenfeucht–Mostowski term model needs a language in which *every* formula's
existential has a Skolem function (so the term-model truth lemma can witness nested `∃`'s). One
layer (`skolem₁ω`) is not closed under its own witness formulas, so we iterate:

* `L₀ = L`, `L_{k+1} = L_k.sum (skolem₁ω L_k)` (`skolemStage`);
* the colimit `L^Sk = colim_k L_k` (next) is **Skolem-complete**: an `L^Sk`-formula lives at some
  finite stage `k`, and its existential's Skolem function appears at stage `k+1`.

This is *ambient* infrastructure: the family `Γ*` consumed by the truth lemma is a **countable**
staged closure inside `L^Sk`. Caveat: the EM term model's `EMContext` also needs the **full atom
diagram** over `L^Sk`, which *does* enumerate its continuum-many symbols — the reason for the
countable family-restricted re-base (`localSkolem` and the `Llocal`/`Γlocal` tower in
`LocalSkolem.lean`/`LocalTower.lean`); `skolemColim` is retained as exploratory infrastructure.

For `L : Language.{0,0}` every stage stays in `Type 0` (`BoundedFormulaω Empty n` over a `{0,0}`
language is `Type 0`), so the tower has no universe blowup.
-/

namespace FirstOrder.Language

variable (L : Language.{0, 0})

/-! ### Sequential colimit of types -/

/-- The sequential colimit of a tower of types `F 0 → F 1 → …` along maps `φ`, as the quotient of
`Σ k, F k` identifying `⟨k, x⟩` with `⟨k+1, φ k x⟩`. -/
def DirectedColim (F : ℕ → Type) (φ : ∀ k, F k → F (k + 1)) : Type :=
  Quot (fun a b : Σ k, F k => b = ⟨a.1 + 1, φ a.1 a.2⟩)

/-- The canonical inclusion of stage `k` into the colimit. -/
def DirectedColim.incl {F : ℕ → Type} {φ : ∀ k, F k → F (k + 1)} (k : ℕ) (x : F k) :
    DirectedColim F φ :=
  Quot.mk _ ⟨k, x⟩

/-- Inclusions commute with the tower maps: a stage-`k` element and its image at stage `k+1` have
the same colimit class. -/
theorem DirectedColim.incl_step {F : ℕ → Type} {φ : ∀ k, F k → F (k + 1)} (k : ℕ) (x : F k) :
    DirectedColim.incl (φ := φ) (k + 1) (φ k x) = DirectedColim.incl (φ := φ) k x := by
  symm
  exact Quot.sound rfl

/-! ### The colimit language `L^Sk` and the stage cocone -/

/-! ### Stage structures on a fixed model -/

section Structures

variable {M : Type} [L.Structure M] [Nonempty M]

end Structures

end FirstOrder.Language
