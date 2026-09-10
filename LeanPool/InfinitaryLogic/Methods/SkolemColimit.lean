/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Basic
/-!
# Sequential colimits

`DirectedColim` is the quotient of a sequence of types by its transition maps. The local Skolem
tower uses this generic construction for its function and relation symbols.
-/

namespace FirstOrder.Language

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

end FirstOrder.Language
