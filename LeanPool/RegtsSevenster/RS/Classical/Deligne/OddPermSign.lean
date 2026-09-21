/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29

/-!
# The sign action on tensor powers of an odd line

The permutation action on a tensor power of an odd line is the sign
character.  The line's self-braiding is `−1`, so the top braiding of
any tensor power is the negated identity; every adjacent
transposition therefore acts by `−1`, and functoriality of the
action, together with generation of the symmetric group by the
adjacent transpositions, forces a general permutation to act by its
sign.  The linear extension evaluates the group algebra's action on
a single group element accordingly.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

/-- **The top braiding of an odd line's tensor power is `−1`**: the
braiding of the top two factors is the line's self-braiding,
whiskered by the factors below, and negation passes through the
whiskering. -/
theorem oddLine_swapTop
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D]
    (L : OddLine D) (n : ℕ) :
    swapTop L.obj n = -𝟙 (tensorPow D L.obj (n + 2)) := by
  unfold swapTop
  rw [L.braid_neg, whiskerLeft_neg, MonoidalCategory.whiskerLeft_id,
    Preadditive.neg_comp, Category.id_comp, Preadditive.comp_neg,
    Iso.hom_inv_id]

/-- **Every adjacent transposition acts by `−1`** on a tensor power
of an odd line: the top one is the top braiding, and the lower ones
are whiskered copies of the same evaluation one arity down. -/
theorem oddLine_permMor_adjSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D]
    (L : OddLine D) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      permMor L.obj (n + 2) (Equiv.swap i.castSucc i.succ) =
        -𝟙 (tensorPow D L.obj (n + 2)) := by
  intro n
  induction n with
  | zero =>
    intro i
    refine Fin.lastCases ?_ (fun j => j.elim0) i
    rw [show Equiv.swap (Fin.castSucc (Fin.last 0)) (Fin.last 0).succ
        = (topSwap : Equiv.Perm (Fin 2)) from by
          rw [topSwap, Fin.succ_last],
      permMor_topSwap_eq]
    exact oddLine_swapTop L 0
  | succ n ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show Equiv.swap (Fin.castSucc (Fin.last (n + 1)))
          (Fin.last (n + 1)).succ
          = (topSwap : Equiv.Perm (Fin (n + 3))) from by
            rw [topSwap, Fin.succ_last],
        permMor_topSwap_eq]
      exact oddLine_swapTop L (n + 1)
    · rw [swap_castSucc_succ_castSucc j, permMor_extPerm, ih j,
        neg_whiskerRight, MonoidalCategory.id_whiskerRight]
      rfl

/-- **The permutation action on a tensor power of an odd line is the
sign character.**  Both the action and the sign are multiplicative,
and every adjacent transposition acts by `−1`, so generation of the
symmetric group by the adjacent transpositions gives the general
permutation. -/
theorem oddLine_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    (L : OddLine D) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    permMor L.obj n σ =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) • 𝟙 (tensorPow D L.obj n) := by
  match n, σ with
  | 0, σ =>
    have hσ : σ = 1 := Equiv.ext fun x => x.elim0
    rw [hσ, permMor_one, Equiv.Perm.sign_one]
    simp
  | 1, σ =>
    have hσ : σ = 1 := Equiv.ext fun x => Fin.ext (by omega)
    rw [hσ, permMor_one, Equiv.Perm.sign_one]
    simp
  | n + 2, σ =>
    have key : ∀ τ : Equiv.Perm (Fin (n + 2)),
        τ ∈ Submonoid.closure (Set.range fun i : Fin (n + 1) =>
          Equiv.swap i.castSucc i.succ) →
        permMor L.obj (n + 2) τ =
          ((Equiv.Perm.sign τ : ℤ) : ℂ) •
            𝟙 (tensorPow D L.obj (n + 2)) := by
      intro τ hτ
      induction hτ using Submonoid.closure_induction_left with
      | one =>
        rw [permMor_one, Equiv.Perm.sign_one]
        simp
      | mul_left g hg τ' hτ' ihτ' =>
        obtain ⟨i, rfl⟩ := hg
        rw [permMor_mul, ihτ', oddLine_permMor_adjSwap L n i,
          Equiv.Perm.sign_mul,
          Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
        simp [neg_smul]
    exact key σ (by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)

end RS
