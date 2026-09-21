/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixDegenerate
import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixWhisker

/-!
# The whiskered mixed sum at arbitrary counts

The two generalisations of the nonvanishing of the mixed sum
combine: the letter systems built on the indexed biproduct work at
every pair of counts, and the extraction of the colour sums
survives whiskering by an auxiliary object, so the block
idempotent acts nontrivially on the whiskered tensor power at
every pair of counts and every diagram avoiding the corresponding
cell.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **Nonvanishing of the whiskered mixed sum at arbitrary
counts**: no positivity of either count is needed, and the
nontriviality hypothesis is carried by the whiskering object. -/
theorem OddLine.whisker_permAlg_mix_ne_zero'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D]
    (P : SchurPackage.{v})
    (P₀ : SchurPackage.{0}) (W : D) (L : OddLine D) (r s : ℕ)
    {lam : YoungDiagram}
    (hW : ∀ k : ℕ, 𝟙 (W ⊗ tensorPow D L.obj k) ≠ 0)
    (hcell : ((r, s) : ℕ × ℕ) ∉ lam) :
    W ◁ permAlg (L.mix r s) lam.card (P.e lam) ≠ 0 := by
  intro hkill
  have he : P.e lam = P₀.e lam := by
    rw [P.e_eq_nProjector lam, P₀.e_eq_nProjector lam]
  have hcs : ∀ c d : Fin lam.card → Fin r ⊕ Fin s,
      colourSum (mixParity r s) (P₀.e lam) c d = 0 := by
    intro c d
    have h := (L.mixLetters r s).colourSum_eq_zero_whisker
      L.braid_neg W hW hkill c d
    rwa [he] at h
  exact not_schurKilled_stdSuper P₀ hcell
    ((superLetters r s).permAlg_eq_zero stdSuper_braiding_neg hcs)

end RS
