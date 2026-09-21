/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Nilpotency from a shifted finite filtration

The abstract engine of a filtration argument, in a preadditive
category with a zero object.  Given a finite chain of subobjects
`F : ℕ → Subobject X` with `F 0 = ⊤` and `F N = ⊥`, an
endomorphism `f` that moves each stage into the next — in the
sense that `(F k).arrow ≫ f` factors through `F (k + 1)` for every
`k < N` — satisfies `f ^ N = 0` (`RS.comp_eq_zero_of_chain`); if
`f` is moreover idempotent it vanishes outright
(`RS.eq_zero_of_idem_of_chain`).  Convenience forms taking the
chain as a `Fin (N + 1)`-indexed family are also provided
(`RS.comp_eq_zero_of_finChain`, `RS.eq_zero_of_idem_of_finChain`).

No monotonicity of the chain is assumed: only the endpoints and
the shift hypothesis enter the argument.

## Composition-order convention

Multiplication in `End X` is reversed composition:
`g * h = h ≫ g` (`CategoryTheory.End.mul_def`).  Read as a
morphism via `CategoryTheory.End.asHom`, the power `f ^ (n + 1)`
is therefore `End.asHom (f ^ n) ≫ End.asHom f`; the lemma
`RS.pow_end_eq` records exactly this unfolding.  (For powers of a
single endomorphism all bracketings agree, but consumers matching
syntactically against `f ^ N` should unfold via `pow_end_eq`.)
The shift hypothesis is phrased with `End.asHom f`, so consumers
supply factorisations of the morphism `(F k).arrow ≫ End.asHom f`.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u}

/-- Powers in `End X` unfold through the reversed multiplication
of `End`: read as a morphism, `f ^ (n + 1)` is `f ^ n ≫ f`. -/
lemma pow_end_eq [Category.{v} C]
    {X : C} (f : End X) (n : ℕ) :
    End.asHom (f ^ (n + 1)) = End.asHom (f ^ n) ≫ End.asHom f := by
  rw [pow_succ']
  rfl

section Chain

/-- An idempotent has all its positive powers equal to itself. -/
private lemma pow_succ_of_idem [Category.{v} C] {X : C}
    {f : End X} (h : f * f = f) :
    ∀ n : ℕ, f ^ (n + 1) = f
  | 0 => pow_one f
  | n + 1 => by rw [pow_succ, pow_succ_of_idem h n, h]

/-- An idempotent endomorphism with a vanishing power is zero.  At
exponent zero the hypothesis reads `1 = 0`, which kills `f` as
well. -/
private lemma eq_zero_of_idem_of_pow [Category.{v} C] [Preadditive C] {X : C}
    {f : End X} {N : ℕ}
    (hidem : f * f = f) (hpow : f ^ N = 0) : f = 0 := by
  rcases N with _ | M
  · rw [pow_zero] at hpow
    calc f = f * 1 := (mul_one f).symm
      _ = f * 0 := by rw [hpow]
      _ = 0 := mul_zero f
  · rw [pow_succ_of_idem hidem M] at hpow
    exact hpow

/-- **Shifting a finite chain forces nilpotency.**  If the chain
`F` runs from `F 0 = ⊤` to `F N = ⊥` and the endomorphism `f`
moves each stage into the next — `(F k).arrow ≫ f` factors
through `F (k + 1)` for every `k < N` — then `f ^ N = 0`.

The proof shows by induction that `(⊤ : Subobject X).arrow`
composed with `f ^ k` factors through `F k`; at `k = N` the
factorisation runs through `⊥`, whose arrow is zero, and the top
arrow is an isomorphism, hence an epimorphism. -/
theorem comp_eq_zero_of_chain
    [Category.{v} C] [Preadditive C] [HasZeroObject C] {X : C}
    {N : ℕ} (F : ℕ → Subobject X)
    (htop : F 0 = ⊤) (hbot : F N = ⊥) (f : End X)
    (hshift : ∀ k, k < N →
      (F (k + 1)).Factors ((F k).arrow ≫ End.asHom f)) :
    f ^ N = 0 := by
  have key : ∀ k, k ≤ N →
      (F k).Factors
        ((⊤ : Subobject X).arrow ≫ End.asHom (f ^ k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [htop]
      exact Subobject.top_factors _
    | succ k ih =>
      intro hk
      have h := ih (Nat.le_of_succ_le hk)
      have h' := hshift k hk
      have heq : (⊤ : Subobject X).arrow ≫ End.asHom (f ^ (k + 1))
          = ((F k).factorThru _ h ≫ (F (k + 1)).factorThru _ h') ≫
              (F (k + 1)).arrow := by
        rw [pow_end_eq]
        calc (⊤ : Subobject X).arrow ≫
              End.asHom (f ^ k) ≫ End.asHom f
            = ((⊤ : Subobject X).arrow ≫ End.asHom (f ^ k)) ≫
                End.asHom f := (Category.assoc _ _ _).symm
          _ = ((F k).factorThru _ h ≫ (F k).arrow) ≫
                End.asHom f := by rw [Subobject.factorThru_arrow]
          _ = (F k).factorThru _ h ≫ (F k).arrow ≫ End.asHom f :=
              Category.assoc _ _ _
          _ = (F k).factorThru _ h ≫ (F (k + 1)).factorThru _ h' ≫
                (F (k + 1)).arrow := by
              rw [Subobject.factorThru_arrow]
          _ = ((F k).factorThru _ h ≫
                (F (k + 1)).factorThru _ h') ≫ (F (k + 1)).arrow :=
              (Category.assoc _ _ _).symm
      rw [heq]
      exact Subobject.factors_comp_arrow _
  have hN := key N le_rfl
  rw [hbot, Subobject.bot_factors_iff_zero] at hN
  have hz : End.asHom (f ^ N) = 0 :=
    (cancel_epi ((⊤ : Subobject X).arrow)).mp
      (by rw [hN, comp_zero])
  exact hz

/-- **A shifted idempotent is zero.**  Under the hypotheses of
`comp_eq_zero_of_chain`, an idempotent `f` (with respect to the
`End` multiplication `f * f = f`) vanishes outright: `f ^ N = 0`
and `f = f ^ N` for `N ≥ 1`, while `N = 0` makes `X` a zero
object. -/
theorem eq_zero_of_idem_of_chain
    [Category.{v} C] [Preadditive C] [HasZeroObject C] {X : C}
    {N : ℕ} (F : ℕ → Subobject X)
    (htop : F 0 = ⊤) (hbot : F N = ⊥) (f : End X)
    (hshift : ∀ k, k < N →
      (F (k + 1)).Factors ((F k).arrow ≫ End.asHom f))
    (hidem : f * f = f) : f = 0 :=
  eq_zero_of_idem_of_pow hidem
    (comp_eq_zero_of_chain F htop hbot f hshift)

/-- Convenience form of `comp_eq_zero_of_chain` with the chain
indexed by `Fin (N + 1)`: it runs from `F 0 = ⊤` to
`F (Fin.last N) = ⊥`, and the shift hypothesis is stated over
`k : Fin N` via `Fin.castSucc` and `Fin.succ`. -/
theorem comp_eq_zero_of_finChain
    [Category.{v} C] [Preadditive C] [HasZeroObject C] {X : C}
    {N : ℕ}
    (F : Fin (N + 1) → Subobject X) (htop : F 0 = ⊤)
    (hbot : F (Fin.last N) = ⊥) (f : End X)
    (hshift : ∀ k : Fin N,
      (F k.succ).Factors ((F k.castSucc).arrow ≫ End.asHom f)) :
    f ^ N = 0 := by
  refine comp_eq_zero_of_chain
    (fun k => if h : k ≤ N then F ⟨k, Nat.lt_succ_of_le h⟩ else ⊥)
    ?_ ?_ f ?_
  · rw [dif_pos (Nat.zero_le N)]
    exact htop
  · rw [dif_pos (le_refl N)]
    exact hbot
  · intro k hk
    have h1 : k ≤ N := Nat.le_of_lt hk
    have h2 : k + 1 ≤ N := hk
    rw [dif_pos h2, dif_pos h1]
    exact hshift ⟨k, hk⟩

/-- Convenience form of `eq_zero_of_idem_of_chain` with the chain
indexed by `Fin (N + 1)`. -/
theorem eq_zero_of_idem_of_finChain
    [Category.{v} C] [Preadditive C] [HasZeroObject C] {X : C}
    {N : ℕ}
    (F : Fin (N + 1) → Subobject X) (htop : F 0 = ⊤)
    (hbot : F (Fin.last N) = ⊥) (f : End X)
    (hshift : ∀ k : Fin N,
      (F k.succ).Factors ((F k.castSucc).arrow ≫ End.asHom f))
    (hidem : f * f = f) : f = 0 :=
  eq_zero_of_idem_of_pow hidem
    (comp_eq_zero_of_finChain F htop hbot f hshift)

end Chain

end RS
