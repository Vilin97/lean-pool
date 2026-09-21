/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.Strata

/-!
# Top Fox--Neuwirth cells

Top dual cells are exactly one-block barred permutations.  Consequently their finite type is
canonically equivalent to the full permutation group.  The prime symmetry action is the
restriction of relabelling on this permutation torsor.
-/

namespace NRR

variable {p : ℕ}

namespace BarredPermutation

/-- Top-dimensional dual Fox--Neuwirth symbols. -/
def TopCell (p : ℕ) := {c : BarredPermutation p // c.IsTop}

namespace TopCell

/-- A permutation determines the unique top symbol with that vertical order. -/
def ofPerm (σ : Equiv.Perm (Fin p)) : TopCell p :=
  ⟨⟨σ, ∅⟩, rfl⟩

@[simp] theorem ofPerm_rank (σ : Equiv.Perm (Fin p)) :
    (ofPerm σ).1.rank = σ :=
  rfl

@[simp] theorem ofPerm_bars (σ : Equiv.Perm (Fin p)) :
    (ofPerm σ).1.bars = ∅ :=
  rfl

/-- Top symbols are canonically the permutation torsor. -/
def equivPerm : TopCell p ≃ Equiv.Perm (Fin p) where
  toFun c := c.1.rank
  invFun := ofPerm
  left_inv := by
    intro c
    apply Subtype.ext
    apply BarredPermutation.ext
    · rfl
    · simpa [IsTop] using c.2.symm
  right_inv := by
    intro σ
    rfl

noncomputable instance : Fintype (TopCell p) :=
  Fintype.ofEquiv (Equiv.Perm (Fin p)) equivPerm.symm

noncomputable instance : DecidableEq (TopCell p) :=
  Classical.decEq _

/-- A top cell is in particular a barred permutation. -/
instance : Coe (TopCell p) (BarredPermutation p) :=
  ⟨Subtype.val⟩

/-- Prime symmetry preserves top cells. -/
instance primeSymmetryAction (hp : Nat.Prime p) :
    MulAction (PrimeSymmetry hp) (TopCell p) where
  smul g c :=
    ⟨g • c.1,
      (BarredPermutation.isTop_relabel
        (PrimeSymmetry.toPerm hp g) c.1).2 c.2⟩
  one_smul c := by
    apply Subtype.ext
    exact one_smul _ _
  mul_smul g h c := by
    apply Subtype.ext
    exact mul_smul _ _ _

@[simp] theorem smul_coe
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (c : TopCell p) :
    (g • c : TopCell p).1 = g • c.1 :=
  rfl

/-- Distinguished even top-cell representative. -/
def evenRepresentative : TopCell p :=
  ofPerm 1

/-- Distinguished transposition representative used for the second odd-prime orbit. -/
def transpositionRepresentative
    (i j : Fin p) : TopCell p :=
  ofPerm (Equiv.swap i j)

 theorem dimension
    (hp : Nat.Prime p) (c : TopCell p) :
    c.1.dualDimension = p - 1 :=
  BarredPermutation.dualDimension_top c.1 hp.pos c.2

end TopCell

end BarredPermutation

end NRR
