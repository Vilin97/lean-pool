/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowPairing

/-!
# Permutations across the power pairing

The nested power pairing consumes the `M'`-power from the top and
the `M`-power from the bottom, so it pairs slot `j` of the
`M'`-power against slot `n - 1 - j` of the `M`-power.  Moving a
permutation of the `M`-slots across the pairing therefore turns it
into the *order-reversing adjoint* permutation of the `M'`-slots.

* `adjPerm`: the adjoint `σ ↦ rev ∘ σ⁻¹ ∘ rev`.  The convention is
  chosen so that the exchange law holds verbatim; it is an
  anti-homomorphism (`adjPerm_mul`) and an involution
  (`adjPerm_adjPerm`), and on transpositions it reverses the two
  slots (`adjPerm_swap`).
* `swapTop_powPeel`, `powPeel_permMor_swap`, `powPeel_permMor_low`:
  the head peel intertwines an adjacent braiding away from the
  bottom slot with the braiding one slot down, and resolves the
  bottom braiding into the braiding of the two exposed factors.
* `pairStep_dbl_braid`: the doubled generic step absorbs the
  braiding of its two consumed `M'`-factors as the braiding of its
  two consumed `M`-factors — the boundary of the exchange law.
* `rawPair_perm`: **the exchange law** — a permutation of the
  `M`-power slots crosses the raw pairing as the adjoint
  permutation of the `M'`-power slots.
* `pairPow_perm`, `symPowIdem_pairPow`: the exchange law descended
  to the module powers, and its average over the group — the
  symmetriser on either side of the descended pairing agree, the
  self-adjointness that transfers the power-level duality to the
  symmetric powers.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## The order-reversing adjoint of a permutation -/

section AdjPerm

variable {n : ℕ}

/-- **The order-reversing adjoint** of a permutation: conjugate
the inverse by the order reversal of the slots.  The inverse makes
it an anti-homomorphism, which is the direction in which
permutations cross the power pairing. -/
def adjPerm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm * σ⁻¹ * Fin.revPerm

@[simp]
theorem adjPerm_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    adjPerm σ i = (σ⁻¹ i.rev).rev := by
  simp [adjPerm]

/-- The adjoint of the identity is the identity. -/
@[simp]
theorem adjPerm_one : adjPerm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i
  simp

/-- **The adjoint is an anti-homomorphism.** -/
theorem adjPerm_mul (σ τ : Equiv.Perm (Fin n)) :
    adjPerm (σ * τ) = adjPerm τ * adjPerm σ := by
  ext i
  simp

/-- **The adjoint is an involution.** -/
@[simp]
theorem adjPerm_adjPerm (σ : Equiv.Perm (Fin n)) :
    adjPerm (adjPerm σ) = σ := by
  ext i
  simp [adjPerm]

/-- The adjoint of a transposition reverses its two slots. -/
theorem adjPerm_swap (u v : Fin n) :
    adjPerm (Equiv.swap u v) = Equiv.swap u.rev v.rev := by
  ext i
  simp only [adjPerm_apply, Equiv.swap_inv]
  rcases eq_or_ne i u.rev with rfl | hu
  · rw [Fin.rev_rev, Equiv.swap_apply_left, Equiv.swap_apply_left]
  rcases eq_or_ne i v.rev with rfl | hv
  · rw [Fin.rev_rev, Equiv.swap_apply_right, Equiv.swap_apply_right]
  have hu' : i.rev ≠ u := fun h => hu (by rw [← h, Fin.rev_rev])
  have hv' : i.rev ≠ v := fun h => hv (by rw [← h, Fin.rev_rev])
  rw [Equiv.swap_apply_of_ne_of_ne hu' hv', Fin.rev_rev,
    Equiv.swap_apply_of_ne_of_ne hu hv]

/-- The adjoint of an adjacent transposition is the adjacent
transposition at the reversed position. -/
theorem adjPerm_swap_castSucc_succ {m : ℕ} (i : Fin (m + 1)) :
    adjPerm (Equiv.swap i.castSucc i.succ) =
      Equiv.swap i.rev.castSucc i.rev.succ := by
  rw [adjPerm_swap, Fin.rev_castSucc, Fin.rev_succ,
    Equiv.swap_comm]

end AdjPerm

variable {D : Type u}

/-! ## Adjacent braidings across the head peel

The permutation action of `Envelope/SymPerm.lean` is built from the
top of the power, while the pairing peels the bottom.  The bridge
is the head peel: an adjacent braiding that avoids the bottom slot
passes the peel, dropping one slot; the braiding of the bottom two
slots resolves, under the double peel, into the braiding of the two
exposed factors.
-/

section PermPeel

/-- The top braiding word over an arbitrary base. -/
private noncomputable def braidTopM
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (P : D) :
    (P ⊗ X) ⊗ X ⟶ (P ⊗ X) ⊗ X :=
  (α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv

/-- Naturality of the top braiding word in its base. -/
private theorem braidTopM_natural
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {P Q : D} (f : P ⟶ Q) :
    braidTopM X P ≫ ((f ▷ X) ▷ X) =
      ((f ▷ X) ▷ X) ≫ braidTopM X Q := by
  rw [braidTopM, braidTopM, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left]
  simp only [Category.assoc]

/-- The top braiding word migrates below an exposed head factor. -/
private theorem braidTop_shift
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (P : D) :
    braidTopM X (X ⊗ P) ≫
      ((α_ X P X).hom ▷ X) ≫ (α_ X (P ⊗ X) X).hom =
    ((α_ X P X).hom ▷ X) ≫ (α_ X (P ⊗ X) X).hom ≫
      (X ◁ braidTopM X P) := by
  rw [braidTopM, braidTopM]
  monoidal

/-- The top braiding passes a peeled step, at general objects. -/
private theorem braidTop_peel_gen
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {W P : D} (p : W ⟶ X ⊗ P) :
    braidTopM X W ≫
        (((p ▷ X) ≫ (α_ X P X).hom) ▷ X) ≫
        (α_ X (P ⊗ X) X).hom =
      ((((p ▷ X) ≫ (α_ X P X).hom) ▷ X) ≫
        (α_ X (P ⊗ X) X).hom) ≫
        (X ◁ braidTopM X P) := by
  rw [MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [reassoc_of% (braidTopM_natural X p)]
  exact congrArg (CategoryStruct.comp _) (braidTop_shift X P)

/-- **The top braiding passes the head peel**, dropping to the top
braiding one arity down. -/
theorem swapTop_powPeel
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (k : ℕ) :
    swapTop X (k + 1) ≫ (powPeel X (k + 2)).hom =
      (powPeel X (k + 2)).hom ≫ (X ◁ swapTop X k) :=
  braidTop_peel_gen X (P := tensorPow D X k) (powPeel X k).hom

/-- An endomorphism intertwined with a lower one by a peel is
intertwined with its whisker by the peeled step; at general
objects. -/
private theorem peel_step_gen [Category.{v} D] [MonoidalCategory D] (X : D)
    {W P : D} (p : W ⟶ X ⊗ P)
    (s : W ⟶ W) (t : P ⟶ P) (hst : s ≫ p = p ≫ (X ◁ t)) :
    (s ▷ X) ≫ ((p ▷ X) ≫ (α_ X P X).hom) =
      ((p ▷ X) ≫ (α_ X P X).hom) ≫ (X ◁ (t ▷ X)) := by
  rw [← MonoidalCategory.comp_whiskerRight_assoc, hst,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    associator_naturality_middle]
  simp only [Category.assoc]

/-- **An adjacent braiding above the bottom slot passes the head
peel**, dropping one slot. -/
theorem powPeel_permMor_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D) :
    ∀ (q a b : ℕ) (_ : a + 2 + b = q),
      permMor X (q + 1)
          (Equiv.swap ⟨a + 1, by omega⟩ ⟨a + 2, by omega⟩) ≫
        (powPeel X q).hom =
      (powPeel X q).hom ≫
        (X ◁ permMor X q
          (Equiv.swap ⟨a, by omega⟩ ⟨a + 1, by omega⟩))
  | q, a, 0, h => by
    subst h
    change permMor X (a + 1 + 2) topSwap ≫
        (powPeel X (a + 2)).hom =
      (powPeel X (a + 2)).hom ≫
        (X ◁ permMor X (a + 2) topSwap)
    rw [permMor_topSwap_eq, permMor_topSwap_eq]
    exact swapTop_powPeel X a
  | q, a, b + 1, h => by
    subst h
    change permMor X (a + 2 + b + 1 + 1)
        (Equiv.swap ⟨a + 1, by omega⟩ ⟨a + 2, by omega⟩) ≫
        (powPeel X (a + 2 + b + 1)).hom =
      (powPeel X (a + 2 + b + 1)).hom ≫
        (X ◁ permMor X (a + 2 + b + 1)
          (Equiv.swap ⟨a, by omega⟩ ⟨a + 1, by omega⟩))
    have hswL : (Equiv.swap
          (⟨a + 1, by omega⟩ : Fin (a + 2 + b + 1 + 1))
          ⟨a + 2, by omega⟩) =
        extPerm (Equiv.swap
          (⟨a + 1, by omega⟩ : Fin (a + 2 + b + 1))
          ⟨a + 2, by omega⟩) := by
      rw [extPerm_swap]
      rfl
    have hswR : (Equiv.swap
          (⟨a, by omega⟩ : Fin (a + 2 + b + 1))
          ⟨a + 1, by omega⟩) =
        extPerm (Equiv.swap
          (⟨a, by omega⟩ : Fin (a + 2 + b))
          ⟨a + 1, by omega⟩) := by
      rw [extPerm_swap]
      rfl
    rw [hswL, hswR, permMor_extPerm, permMor_extPerm]
    exact peel_step_gen X (powPeel X (a + 2 + b)).hom _ _
      (powPeel_permMor_swap X (a + 2 + b) a b rfl)

/-- The bottom braiding word migrates below one more exposed head
factor, as the bottom braiding of the extended tail. -/
private theorem braidLow_shift
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (P : D) :
    ((α_ X X P).inv ▷ X) ≫ (((β_ X X).hom ▷ P) ▷ X) ≫
      ((α_ X X P).hom ▷ X) ≫ (α_ X (X ⊗ P) X).hom ≫
      (X ◁ (α_ X P X).hom) =
    (α_ X (X ⊗ P) X).hom ≫ (X ◁ (α_ X P X).hom) ≫
      (α_ X X (P ⊗ X)).inv ≫ ((β_ X X).hom ▷ (P ⊗ X)) ≫
      (α_ X X (P ⊗ X)).hom := by
  monoidal

/-- An endomorphism intertwined with the bottom braiding by a
double peel is intertwined with the extended bottom braiding by
the doubled peel; at general objects. -/
private theorem peel_low_gen
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {W W₀ P : D} (f : W ⟶ X ⊗ W₀)
    (g : W₀ ⟶ X ⊗ P) (s : W ⟶ W)
    (hs : s ≫ f ≫ (X ◁ g) =
      f ≫ (X ◁ g) ≫ (α_ X X P).inv ≫
        ((β_ X X).hom ▷ P) ≫ (α_ X X P).hom) :
    (s ▷ X) ≫ ((f ▷ X) ≫ (α_ X W₀ X).hom) ≫
        (X ◁ ((g ▷ X) ≫ (α_ X P X).hom)) =
      ((f ▷ X) ≫ (α_ X W₀ X).hom) ≫
        (X ◁ ((g ▷ X) ≫ (α_ X P X).hom)) ≫
        (α_ X X (P ⊗ X)).inv ≫
        ((β_ X X).hom ▷ (P ⊗ X)) ≫ (α_ X X (P ⊗ X)).hom := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_lhs => rw [← associator_naturality_middle_assoc]
  conv_rhs => rw [← associator_naturality_middle_assoc]
  conv_lhs => rw [← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, Category.assoc]
  rw [hs]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  refine congrArg (CategoryStruct.comp _) ?_
  refine congrArg (CategoryStruct.comp _) ?_
  exact braidLow_shift X P

/-- **The bottom braiding resolves under the double peel** into
the braiding of the two exposed head factors. -/
theorem powPeel_permMor_low
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D) :
    ∀ n : ℕ,
      permMor X (n + 2)
          (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) ≫
        (powPeel X (n + 1)).hom ≫ (X ◁ (powPeel X n).hom) =
      (powPeel X (n + 1)).hom ≫ (X ◁ (powPeel X n).hom) ≫
        (α_ X X (tensorPow D X n)).inv ≫
        ((β_ X X).hom ▷ tensorPow D X n) ≫
        (α_ X X (tensorPow D X n)).hom
  | 0 => by
    change permMor X (0 + 2) topSwap ≫
        (powPeel X 1).hom ≫ (X ◁ (powPeel X 0).hom) =
      (powPeel X 1).hom ≫ (X ◁ (powPeel X 0).hom) ≫
        (α_ X X (𝟙_ D)).inv ≫ ((β_ X X).hom ▷ 𝟙_ D) ≫
        (α_ X X (𝟙_ D)).hom
    rw [permMor_topSwap_eq]
    change ((α_ (𝟙_ D) X X).hom ≫ (𝟙_ D ◁ (β_ X X).hom) ≫
        (α_ (𝟙_ D) X X).inv) ≫
        ((((λ_ X).hom ≫ (ρ_ X).inv) ▷ X) ≫
          (α_ X (𝟙_ D) X).hom) ≫
        (X ◁ ((λ_ X).hom ≫ (ρ_ X).inv)) =
      ((((λ_ X).hom ≫ (ρ_ X).inv) ▷ X) ≫
          (α_ X (𝟙_ D) X).hom) ≫
        (X ◁ ((λ_ X).hom ≫ (ρ_ X).inv)) ≫
        (α_ X X (𝟙_ D)).inv ≫ ((β_ X X).hom ▷ 𝟙_ D) ≫
        (α_ X X (𝟙_ D)).hom
    monoidal
  | n + 1 => by
    change permMor X (n + 2 + 1)
        (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) ≫
        (powPeel X (n + 1 + 1)).hom ≫
        (X ◁ (powPeel X (n + 1)).hom) =
      (powPeel X (n + 1 + 1)).hom ≫
        (X ◁ (powPeel X (n + 1)).hom) ≫
        (α_ X X (tensorPow D X (n + 1))).inv ≫
        ((β_ X X).hom ▷ tensorPow D X (n + 1)) ≫
        (α_ X X (tensorPow D X (n + 1))).hom
    have hsw : (Equiv.swap (⟨0, by omega⟩ : Fin (n + 2 + 1))
          ⟨1, by omega⟩) =
        extPerm (Equiv.swap (⟨0, by omega⟩ : Fin (n + 2))
          ⟨1, by omega⟩) := by
      rw [extPerm_swap]
      rfl
    rw [hsw, permMor_extPerm]
    exact peel_low_gen X (powPeel X (n + 1)).hom
      (powPeel X n).hom _ (powPeel_permMor_low X n)

end PermPeel

/-! ## The doubled step absorbs the boundary braiding

The recursion of the power pairing consumes the top `M'`-factor
against the bottom `M`-factor; two consecutive steps consume the
top two `M'`-factors against the bottom two `M`-factors.  The
boundary of the exchange law is that braiding the two consumed
`M'`-factors equals braiding the two consumed `M`-factors, across
the doubled step.  Everything here is at general objects, over an
opaque pairing `u` and continuation `r`; commutativity of the
monoid enters exactly once, to exchange the two emitted scalars.
-/

section DblCore

/-- The single pairing window over an opaque pairing: evaluate on
the head pair and braid the scalar out past the tail. -/
private noncomputable def winU
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) (R : D) :
    V' ⊗ (V ⊗ R) ⟶ R ⊗ A :=
  (α_ V' V R).inv ≫ (u ▷ R) ≫ (β_ A R).hom

/-- The generic step over an opaque pairing, shaped exactly as
`pairStep` over `pairRaw`. -/
private noncomputable def stepU
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) {Q R : D}
    (r : Q ⊗ R ⟶ A) : (Q ⊗ V') ⊗ (V ⊗ R) ⟶ A :=
  (α_ Q V' (V ⊗ R)).hom ≫ (Q ◁ winU A V' V u R) ≫
    (α_ Q R A).inv ≫ (r ▷ A) ≫ μ[A]

/-- The doubled window: both consumed pairs fire, the two scalars
collected at the tail. -/
private noncomputable def dblWin
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) (R : D) :
    V' ⊗ (V' ⊗ (V ⊗ (V ⊗ R))) ⟶ R ⊗ (A ⊗ A) :=
  (V' ◁ winU A V' V u (V ⊗ R)) ≫ (α_ V' (V ⊗ R) A).inv ≫
    (winU A V' V u R ▷ A) ≫ (α_ R A A).hom

/-- **The doubled step in window form**: two steps are the doubled
window on the consumed factors, the continuation, and the fold of
the two scalars. -/
private theorem stepU_stepU
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) {Q R : D}
    (r : Q ⊗ R ⟶ A) :
    stepU A V' V u (stepU A V' V u r) =
      (α_ (Q ⊗ V') V' (V ⊗ (V ⊗ R))).hom ≫
        (α_ Q V' (V' ⊗ (V ⊗ (V ⊗ R)))).hom ≫
        (Q ◁ dblWin A V' V u R) ≫
        (α_ Q R (A ⊗ A)).inv ≫ (r ▷ (A ⊗ A)) ≫
        (A ◁ μ[A]) ≫ μ[A] := by
  rw [stepU, stepU, dblWin]
  simp only [winU, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [MonObj.mul_assoc]
  monoidal

/-- The pre-braiding of the two consumed `M'`-factors migrates
into the spine. -/
private theorem braid_spine
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (V' : D)
    (Q T : D) :
    (((α_ Q V' V').hom ≫ (Q ◁ (β_ V' V').hom) ≫
        (α_ Q V' V').inv) ▷ T) ≫
      (α_ (Q ⊗ V') V' T).hom ≫ (α_ Q V' (V' ⊗ T)).hom =
    (α_ (Q ⊗ V') V' T).hom ≫ (α_ Q V' (V' ⊗ T)).hom ≫
      (Q ◁ ((α_ V' V' T).inv ≫ ((β_ V' V').hom ▷ T) ≫
        (α_ V' V' T).hom)) := by
  monoidal

/-- A whiskering of the consumed tail migrates into the spine. -/
private theorem whisk_spine [Category.{v} D] [MonoidalCategory D] (V' : D)
    {Q T T' : D} (f : T ⟶ T') :
    (((Q ⊗ V') ⊗ V') ◁ f) ≫
      (α_ (Q ⊗ V') V' T').hom ≫ (α_ Q V' (V' ⊗ T')).hom =
    (α_ (Q ⊗ V') V' T).hom ≫ (α_ Q V' (V' ⊗ T)).hom ≫
      (Q ◁ (V' ◁ (V' ◁ f))) := by
  rw [associator_naturality_right_assoc,
    associator_naturality_right]

/-- The scalar flip is absorbed by the commutative fold. -/
private theorem flip_absorb
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A]
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    (Q ◁ (R ◁ (β_ A A).hom)) ≫ (α_ Q R (A ⊗ A)).inv ≫
      (r ▷ (A ⊗ A)) ≫ (A ◁ μ[A]) ≫ μ[A] =
    (α_ Q R (A ⊗ A)).inv ≫ (r ▷ (A ⊗ A)) ≫
      (A ◁ μ[A]) ≫ μ[A] := by
  rw [associator_inv_naturality_right_assoc,
    whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    IsCommMonObj.mul_comm]

/-- **The doubled window in parallel form**: both pairs are routed
side by side, fire in parallel, and the scalars collect at the
tail. -/
private theorem dblWin_par
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) (R : D) :
    dblWin A V' V u R =
      (V' ◁ (α_ V' V (V ⊗ R)).inv) ≫
        (α_ V' (V' ⊗ V) (V ⊗ R)).inv ≫
        ((β_ V' (V' ⊗ V)).hom ▷ (V ⊗ R)) ≫
        (α_ (V' ⊗ V) V' (V ⊗ R)).hom ≫
        ((V' ⊗ V) ◁ (α_ V' V R).inv) ≫
        (u ▷ ((V' ⊗ V) ⊗ R)) ≫ (A ◁ (u ▷ R)) ≫
        (A ◁ (β_ A R).hom) ≫ (β_ A (R ⊗ A)).hom ≫
        (α_ R A A).hom := by
  have hb := braid_cross_pair (S := V') (T := V ⊗ R) A
    (winU A V' V u R)
  have hkey : (V' ◁ (β_ A (V ⊗ R)).hom) ≫
      (α_ V' (V ⊗ R) A).inv ≫ (winU A V' V u R ▷ A) =
      (α_ V' A (V ⊗ R)).inv ≫ ((β_ V' A).hom ▷ (V ⊗ R)) ≫
        (α_ A V' (V ⊗ R)).hom ≫ (A ◁ winU A V' V u R) ≫
        (β_ A (R ⊗ A)).hom := by
    rw [reassoc_of% hb]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← Category.assoc, Category.assoc,
      SymmetricCategory.symmetry, Category.comp_id]
    simp only [Category.assoc]
  rw [dblWin]
  conv_lhs => rw [winU]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hkey]
  rw [associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    associator_naturality_left_assoc,
    ← whisker_exchange_assoc]
  conv_lhs => rw [winU]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]

/-- The block braiding passes the parallel firing, becoming the
scalar braiding. -/
private theorem fire_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) (R : D) :
    ((α_ (V' ⊗ V) (V' ⊗ V) R).inv ≫
        ((β_ (V' ⊗ V) (V' ⊗ V)).hom ▷ R) ≫
        (α_ (V' ⊗ V) (V' ⊗ V) R).hom) ≫
      (u ▷ ((V' ⊗ V) ⊗ R)) ≫ (A ◁ (u ▷ R)) =
    (u ▷ ((V' ⊗ V) ⊗ R)) ≫ (A ◁ (u ▷ R)) ≫
      ((α_ A A R).inv ≫ ((β_ A A).hom ▷ R) ≫
        (α_ A A R).hom) := by
  rw [← MonoidalCategory.tensorHom_def_assoc,
    ← MonoidalCategory.tensorHom_def]
  rw [show (u ▷ R : (V' ⊗ V) ⊗ R ⟶ A ⊗ R) = u ⊗ₘ 𝟙 R from
    (MonoidalCategory.tensorHom_id u R).symm]
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_naturality,
    MonoidalCategory.associator_inv_naturality_assoc]
  simp only [← Category.assoc]
  refine congrArg (fun t => t ≫ (α_ A A R).hom) ?_
  simp only [Category.assoc]
  refine congrArg (CategoryStruct.comp _) ?_
  rw [MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_whiskerRight,
    ← MonoidalCategory.comp_whiskerRight,
    ← BraidedCategory.braiding_naturality]

/-- The scalar braiding passes the collecting tail, becoming the
flip of the collected pair. -/
private theorem tail_flip
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (R : D) :
    (α_ A A R).inv ≫ ((β_ A A).hom ▷ R) ≫ (α_ A A R).hom ≫
      (A ◁ (β_ A R).hom) ≫ (β_ A (R ⊗ A)).hom ≫
      (α_ R A A).hom =
    (A ◁ (β_ A R).hom) ≫ (β_ A (R ⊗ A)).hom ≫
      (α_ R A A).hom ≫ (R ◁ (β_ A A).hom) := by
  rw [BraidedCategory.braiding_tensor_right_hom A R A]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [BraidedCategory.yang_baxter_assoc]
  simp only [Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp,
    SymmetricCategory.symmetry,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- **The first pure routing law**: the braiding of the two
`M'`-factors before the parallel routing is the single interleave
crossing. -/
private theorem route_fst
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (V' : D)
    (V : D)
    (R : D) :
    ((α_ V' V' (V ⊗ (V ⊗ R))).inv ≫
        ((β_ V' V').hom ▷ (V ⊗ (V ⊗ R))) ≫
        (α_ V' V' (V ⊗ (V ⊗ R))).hom) ≫
      (V' ◁ (α_ V' V (V ⊗ R)).inv) ≫
      (α_ V' (V' ⊗ V) (V ⊗ R)).inv ≫
      ((β_ V' (V' ⊗ V)).hom ▷ (V ⊗ R)) ≫
      (α_ (V' ⊗ V) V' (V ⊗ R)).hom ≫
      ((V' ⊗ V) ◁ (α_ V' V R).inv) =
    (V' ◁ ((α_ V' V (V ⊗ R)).inv ≫
        ((β_ V' V).hom ▷ (V ⊗ R)) ≫
        (α_ V V' (V ⊗ R)).hom ≫ (V ◁ (α_ V' V R).inv))) ≫
      (α_ V' V ((V' ⊗ V) ⊗ R)).inv := by
  have hnat : ((β_ V' V').hom ▷ (V ⊗ (V ⊗ R))) ≫
      (α_ V' V' (V ⊗ (V ⊗ R))).hom ≫
      (V' ◁ (α_ V' V (V ⊗ R)).inv) ≫
      (α_ V' (V' ⊗ V) (V ⊗ R)).inv ≫
      ((α_ V' V' V).inv ▷ (V ⊗ R)) =
      (α_ V' V' (V ⊗ (V ⊗ R))).hom ≫
      (V' ◁ (α_ V' V (V ⊗ R)).inv) ≫
      (α_ V' (V' ⊗ V) (V ⊗ R)).inv ≫
      ((α_ V' V' V).inv ▷ (V ⊗ R)) ≫
      (((β_ V' V').hom ▷ V) ▷ (V ⊗ R)) := by
    monoidal
  have hcancel : (((β_ V' V').hom ▷ V) ▷ (V ⊗ R)) ≫
      (((β_ V' V').hom ▷ V) ▷ (V ⊗ R)) =
      𝟙 (((V' ⊗ V') ⊗ V) ⊗ (V ⊗ R)) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight,
      SymmetricCategory.symmetry]
    simp
  rw [BraidedCategory.braiding_tensor_right_hom V' V' V]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hcancel]
  simp only [Iso.inv_hom_id_assoc]
  monoidal

/-- **The second pure routing law**: the braiding of the two
`M`-factors before the parallel routing, followed by the block
braiding, is the same single interleave crossing. -/
private theorem route_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (V' : D)
    (V : D)
    (R : D) :
    (V' ◁ (V' ◁ ((α_ V V R).inv ≫ ((β_ V V).hom ▷ R) ≫
        (α_ V V R).hom))) ≫
      (V' ◁ (α_ V' V (V ⊗ R)).inv) ≫
      (α_ V' (V' ⊗ V) (V ⊗ R)).inv ≫
      ((β_ V' (V' ⊗ V)).hom ▷ (V ⊗ R)) ≫
      (α_ (V' ⊗ V) V' (V ⊗ R)).hom ≫
      ((V' ⊗ V) ◁ (α_ V' V R).inv) ≫
      (α_ (V' ⊗ V) (V' ⊗ V) R).inv ≫
      ((β_ (V' ⊗ V) (V' ⊗ V)).hom ▷ R) ≫
      (α_ (V' ⊗ V) (V' ⊗ V) R).hom =
    (V' ◁ ((α_ V' V (V ⊗ R)).inv ≫
        ((β_ V' V).hom ▷ (V ⊗ R)) ≫
        (α_ V V' (V ⊗ R)).hom ≫ (V ◁ (α_ V' V R).inv))) ≫
      (α_ V' V ((V' ⊗ V) ⊗ R)).inv := by
  rw [BraidedCategory.braiding_tensor_right_hom V' V' V,
    BraidedCategory.braiding_tensor_right_hom
      (V' ⊗ V) V' V,
    BraidedCategory.braiding_tensor_left_hom V' V V',
    BraidedCategory.braiding_tensor_left_hom V' V V]
  simp only [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have hw1 : ((α_ V' V V').inv ▷ (V ⊗ R)) ≫
      (α_ (V' ⊗ V) V' (V ⊗ R)).hom ≫
      ((V' ⊗ V) ◁ (α_ V' V R).inv) ≫
      (α_ (V' ⊗ V) (V' ⊗ V) R).inv ≫
      ((α_ (V' ⊗ V) V' V).inv ▷ R) ≫
      (((α_ V' V V').hom ▷ V) ▷ R) =
      (α_ (V' ⊗ (V ⊗ V')) V R).inv := by
    monoidal
  have hc1 : ((V' ◁ (β_ V' V).hom) ▷ (V ⊗ R)) ≫
      ((V' ◁ (β_ V V').hom) ▷ (V ⊗ R)) =
      𝟙 ((V' ⊗ (V' ⊗ V)) ⊗ (V ⊗ R)) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.whiskerLeft_comp,
      SymmetricCategory.symmetry]
    simp
  rw [reassoc_of% hw1, ← associator_inv_naturality_left_assoc,
    reassoc_of% hc1]
  have hw2 : ((α_ V' V' V).hom ▷ (V ⊗ R)) ≫
      (α_ (V' ⊗ (V' ⊗ V)) V R).inv ≫
      ((α_ V' V' V).inv ▷ V ▷ R) =
      (α_ ((V' ⊗ V') ⊗ V) V R).inv := by
    monoidal
  have hc2 : ((β_ V' V').hom ▷ V ▷ (V ⊗ R)) ≫
      ((β_ V' V').hom ▷ V ▷ (V ⊗ R)) =
      𝟙 (((V' ⊗ V') ⊗ V) ⊗ (V ⊗ R)) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight,
      SymmetricCategory.symmetry]
    simp
  rw [reassoc_of% hw2, ← associator_inv_naturality_left_assoc,
    reassoc_of% hc2]
  have hw3 : (V' ◁ V' ◁ (α_ V V R).hom) ≫
      (V' ◁ (α_ V' V (V ⊗ R)).inv) ≫
      (α_ V' (V' ⊗ V) (V ⊗ R)).inv ≫
      ((α_ V' V' V).inv ▷ (V ⊗ R)) ≫
      (α_ ((V' ⊗ V') ⊗ V) V R).inv ≫
      ((α_ V' V' V).hom ▷ V ▷ R) ≫
      ((α_ V' (V' ⊗ V) V).hom ▷ R) ≫
      ((V' ◁ (α_ V' V V).hom) ▷ R) =
      (V' ◁ (α_ V' (V ⊗ V) R).inv) ≫
      (α_ V' (V' ⊗ (V ⊗ V)) R).inv := by
    monoidal
  have hc3 : (V' ◁ ((β_ V V).hom ▷ R)) ≫
      (V' ◁ ((β_ V V).hom ▷ R)) =
      𝟙 (V' ⊗ ((V ⊗ V) ⊗ R)) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.comp_whiskerRight,
      SymmetricCategory.symmetry]
    simp
  rw [reassoc_of% hw3, ← associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [← associator_inv_naturality_middle, reassoc_of% hc3]
  monoidal

/-- **The window braid exchange**: braiding the two consumed
`M'`-factors before the doubled window equals braiding the two
consumed `M`-factors and flipping the two emitted scalars. -/
private theorem dblWin_braid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) (R : D) :
    ((α_ V' V' (V ⊗ (V ⊗ R))).inv ≫
        ((β_ V' V').hom ▷ (V ⊗ (V ⊗ R))) ≫
        (α_ V' V' (V ⊗ (V ⊗ R))).hom) ≫ dblWin A V' V u R =
      (V' ◁ (V' ◁ ((α_ V V R).inv ≫ ((β_ V V).hom ▷ R) ≫
          (α_ V V R).hom))) ≫ dblWin A V' V u R ≫
        (R ◁ (β_ A A).hom) := by
  rw [dblWin_par]
  simp only [Category.assoc]
  trans (V' ◁ ((α_ V' V (V ⊗ R)).inv ≫
      ((β_ V' V).hom ▷ (V ⊗ R)) ≫
      (α_ V V' (V ⊗ R)).hom ≫ (V ◁ (α_ V' V R).inv))) ≫
    (α_ V' V ((V' ⊗ V) ⊗ R)).inv ≫
    (u ▷ ((V' ⊗ V) ⊗ R)) ≫ (A ◁ (u ▷ R)) ≫
    (A ◁ (β_ A R).hom) ≫ (β_ A (R ⊗ A)).hom ≫
    (α_ R A A).hom
  · rw [reassoc_of% (route_fst V' V R)]
  · rw [← reassoc_of% (route_snd V' V R),
      reassoc_of% (fire_swap A V' V u R),
      tail_flip A R]

/-- **The doubled step absorbs the boundary braiding**: braiding
the two consumed `M'`-factors before the doubled step equals
braiding the two consumed `M`-factors.  The two emitted scalars
exchange, which the commutative fold absorbs. -/
private theorem stepU_dbl_braid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A] (V' : D) (V : D)
    (u : V' ⊗ V ⟶ A) {Q R : D}
    (r : Q ⊗ R ⟶ A) :
    (((α_ Q V' V').hom ≫ (Q ◁ (β_ V' V').hom) ≫
        (α_ Q V' V').inv) ▷ (V ⊗ (V ⊗ R))) ≫
      stepU A V' V u (stepU A V' V u r) =
    (((Q ⊗ V') ⊗ V') ◁ ((α_ V V R).inv ≫
        ((β_ V V).hom ▷ R) ≫ (α_ V V R).hom)) ≫
      stepU A V' V u (stepU A V' V u r) := by
  rw [stepU_stepU]
  rw [reassoc_of% (braid_spine V' Q (V ⊗ (V ⊗ R)))]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    dblWin_braid]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% (whisk_spine V' (α_ V V R).hom),
    reassoc_of% (whisk_spine V' ((β_ V V).hom ▷ R)),
    reassoc_of% (whisk_spine V' (α_ V V R).inv)]
  rw [flip_absorb]

end DblCore

/-! ## The exchange law -/

section Exchange

/-- The doubled pairing step absorbs the boundary braiding. -/
private theorem pairStep_dbl_braid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    (((α_ Q M'.X M'.X).hom ≫ (Q ◁ (β_ M'.X M'.X).hom) ≫
        (α_ Q M'.X M'.X).inv) ▷ (M.X ⊗ (M.X ⊗ R))) ≫
      pairStep A M M' d (pairStep A M M' d r) =
    (((Q ⊗ M'.X) ⊗ M'.X) ◁ ((α_ M.X M.X R).inv ≫
        ((β_ M.X M.X).hom ▷ R) ≫ (α_ M.X M.X R).hom)) ≫
      pairStep A M M' d (pairStep A M M' d r) :=
  stepU_dbl_braid A M'.X M.X (pairRaw A M M' d) r

/-- **The boundary of the exchange law**: the top transposition of
the `M'`-power crosses the pairing as the bottom transposition of
the `M`-power. -/
private theorem rawPair_topSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    (permMor M'.X (n + 1 + 1) topSwap ▷
        tensorPow D M.X (n + 1 + 1)) ≫
      rawPair A M M' d (n + 1 + 1) =
    (tensorPow D M'.X (n + 1 + 1) ◁
        permMor M.X (n + 1 + 1)
          (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)) ≫
      rawPair A M M' d (n + 1 + 1) := by
  have hpair : rawPair A M M' d (n + 1 + 1) =
      (tensorPow D M'.X (n + 1 + 1) ◁
          ((powPeel M.X (n + 1)).hom ≫
            (M.X ◁ (powPeel M.X n).hom))) ≫
        pairStep A M M' d
          (pairStep A M M' d (rawPair A M M' d n)) := by
    erw [rawPair_succ_step, rawPair_succ_step,
      ← pairStep_postcomp]
    conv_rhs => erw [MonoidalCategory.whiskerLeft_comp]
    erw [Category.assoc]
    rfl
  have hts : permMor M'.X (n + 1 + 1) topSwap =
      swapTop M'.X n :=
    permMor_topSwap_eq M'.X n
  have hlow : permMor M.X (n + 1 + 1)
        (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) ≫
        ((powPeel M.X (n + 1)).hom ≫
          (M.X ◁ (powPeel M.X n).hom)) =
      ((powPeel M.X (n + 1)).hom ≫
          (M.X ◁ (powPeel M.X n).hom)) ≫
        ((α_ M.X M.X (tensorPow D M.X n)).inv ≫
          ((β_ M.X M.X).hom ▷ tensorPow D M.X n) ≫
          (α_ M.X M.X (tensorPow D M.X n)).hom) := by
    have h := powPeel_permMor_low M.X n
    simp only [Category.assoc] at h ⊢
    exact h
  have hdbl : (tensorPow D M'.X (n + 1 + 1) ◁
        ((α_ M.X M.X (tensorPow D M.X n)).inv ≫
          ((β_ M.X M.X).hom ▷ tensorPow D M.X n) ≫
          (α_ M.X M.X (tensorPow D M.X n)).hom)) ≫
      pairStep A M M' d
        (pairStep A M M' d (rawPair A M M' d n)) =
      (swapTop M'.X n ▷
          (M.X ⊗ (M.X ⊗ tensorPow D M.X n))) ≫
        pairStep A M M' d
          (pairStep A M M' d (rawPair A M M' d n)) :=
    (pairStep_dbl_braid A M M' d (rawPair A M M' d n)).symm
  erw [hpair, hts, ← whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hlow]
  conv_rhs => erw [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact congrArg (CategoryStruct.comp _) hdbl.symm

/-- **The exchange law on adjacent transpositions**: the adjacent
braiding of `M`-slots `a, a + 1` crosses the raw pairing as the
adjacent braiding of `M'`-slots `b, b + 1`, mirrored across the
arity. -/
private theorem rawPair_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    ∀ (a b m : ℕ) (_ : a + 2 + b = m),
      (permMor M'.X m
          (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) ▷
          tensorPow D M.X m) ≫ rawPair A M M' d m =
      (tensorPow D M'.X m ◁
          permMor M.X m
            (Equiv.swap ⟨a, by omega⟩ ⟨a + 1, by omega⟩)) ≫
        rawPair A M M' d m
  | 0, b, m, h => by
    subst h
    have hc : (0 : ℕ) + 2 + b = b + 1 + 1 := by omega
    have hL : permMor M'.X (0 + 2 + b)
          (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) ≫
          powCast M'.X hc =
        powCast M'.X hc ≫ permMor M'.X (b + 1 + 1)
          (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) :=
      (powCast_permMor_swap M'.X hc ⟨b, by omega⟩
        ⟨b + 1, by omega⟩).symm
    have hR : permMor M.X (0 + 2 + b)
          (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) ≫
          powCast M.X hc =
        powCast M.X hc ≫ permMor M.X (b + 1 + 1)
          (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) :=
      (powCast_permMor_swap M.X hc ⟨0, by omega⟩
        ⟨1, by omega⟩).symm
    rw [rawPair_cast A M M' d hc]
    conv_lhs => rw [← MonoidalCategory.comp_whiskerRight_assoc,
      hL, MonoidalCategory.comp_whiskerRight, Category.assoc,
      ← whisker_exchange_assoc]
    conv_rhs => rw [whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, hR,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    refine congrArg (CategoryStruct.comp _) ?_
    refine congrArg (CategoryStruct.comp _) ?_
    exact rawPair_topSwap A M M' d b
  | a + 1, b, m, h => by
    subst h
    have hc : a + 1 + 2 + b = a + 2 + b + 1 := by omega
    have hL : permMor M'.X (a + 1 + 2 + b)
          (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) ≫
          powCast M'.X hc =
        powCast M'.X hc ≫ permMor M'.X (a + 2 + b + 1)
          (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) :=
      (powCast_permMor_swap M'.X hc ⟨b, by omega⟩
        ⟨b + 1, by omega⟩).symm
    have hR : permMor M.X (a + 1 + 2 + b)
          (Equiv.swap ⟨a + 1, by omega⟩ ⟨a + 2, by omega⟩) ≫
          powCast M.X hc =
        powCast M.X hc ≫ permMor M.X (a + 2 + b + 1)
          (Equiv.swap ⟨a + 1, by omega⟩ ⟨a + 2, by omega⟩) :=
      (powCast_permMor_swap M.X hc ⟨a + 1, by omega⟩
        ⟨a + 2, by omega⟩).symm
    have hcontent : (permMor M'.X (a + 2 + b + 1)
          (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) ▷
          tensorPow D M.X (a + 2 + b + 1)) ≫
          rawPair A M M' d (a + 2 + b + 1) =
        (tensorPow D M'.X (a + 2 + b + 1) ◁
            permMor M.X (a + 2 + b + 1)
              (Equiv.swap ⟨a + 1, by omega⟩
                ⟨a + 2, by omega⟩)) ≫
          rawPair A M M' d (a + 2 + b + 1) := by
      have hswL : (Equiv.swap
            (⟨b, by omega⟩ : Fin (a + 2 + b + 1))
            ⟨b + 1, by omega⟩) =
          extPerm (Equiv.swap
            (⟨b, by omega⟩ : Fin (a + 2 + b))
            ⟨b + 1, by omega⟩) := by
        rw [extPerm_swap]
        rfl
      have hpost : (tensorPow D M'.X (a + 2 + b + 1) ◁
            (M.X ◁ permMor M.X (a + 2 + b)
              (Equiv.swap ⟨a, by omega⟩ ⟨a + 1, by omega⟩))) ≫
            pairStep A M M' d (rawPair A M M' d (a + 2 + b)) =
          pairStep A M M' d
            ((tensorPow D M'.X (a + 2 + b) ◁
              permMor M.X (a + 2 + b)
                (Equiv.swap ⟨a, by omega⟩ ⟨a + 1, by omega⟩)) ≫
              rawPair A M M' d (a + 2 + b)) :=
        pairStep_postcomp A M M' d _ _
      have hstep : (permMor M'.X (a + 2 + b + 1)
            (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) ▷
            (M.X ⊗ tensorPow D M.X (a + 2 + b))) ≫
            pairStep A M M' d (rawPair A M M' d (a + 2 + b)) =
          pairStep A M M' d
            ((permMor M'.X (a + 2 + b)
              (Equiv.swap ⟨b, by omega⟩ ⟨b + 1, by omega⟩) ▷
              tensorPow D M.X (a + 2 + b)) ≫
              rawPair A M M' d (a + 2 + b)) := by
        rw [hswL, permMor_extPerm]
        exact pairStep_precomp A M M' d _ _
      rw [rawPair_succ_step]
      erw [← whisker_exchange_assoc, hstep]
      erw [← MonoidalCategory.whiskerLeft_comp_assoc,
        powPeel_permMor_swap M.X (a + 2 + b) a b rfl,
        MonoidalCategory.whiskerLeft_comp, Category.assoc,
        hpost]
      exact congrArg (CategoryStruct.comp _)
        (congrArg (pairStep A M M' d)
          (rawPair_swap A M M' d a b (a + 2 + b) rfl))
    rw [rawPair_cast A M M' d hc]
    conv_lhs => rw [← MonoidalCategory.comp_whiskerRight_assoc,
      hL, MonoidalCategory.comp_whiskerRight, Category.assoc,
      ← whisker_exchange_assoc]
    conv_rhs => rw [whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, hR,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    refine congrArg (CategoryStruct.comp _) ?_
    refine congrArg (CategoryStruct.comp _) ?_
    exact hcontent

/-- **The exchange law**: a permutation of the `M`-power slots
crosses the raw power pairing as the order-reversing adjoint
permutation of the `M'`-power slots. -/
theorem rawPair_perm [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      (permMor M'.X n (adjPerm σ) ▷ tensorPow D M.X n) ≫
          rawPair A M M' d n =
        (tensorPow D M'.X n ◁ permMor M.X n σ) ≫
          rawPair A M M' d n
  | 0, σ => by
    have hσ : σ = 1 := Equiv.ext fun i => i.elim0
    rw [hσ, adjPerm_one, permMor_one, permMor_one]
    simp
  | 1, σ => by
    have hσ : σ = 1 := Equiv.ext fun i => Subsingleton.elim _ _
    rw [hσ, adjPerm_one, permMor_one, permMor_one]
    simp
  | m + 2, σ => by
    have hgen : ∀ i : Fin (m + 1),
        (permMor M'.X (m + 2)
            (adjPerm (Equiv.swap i.castSucc i.succ)) ▷
            tensorPow D M.X (m + 2)) ≫
          rawPair A M M' d (m + 2) =
        (tensorPow D M'.X (m + 2) ◁
            permMor M.X (m + 2)
              (Equiv.swap i.castSucc i.succ)) ≫
          rawPair A M M' d (m + 2) := by
      intro i
      have hlt := i.isLt
      have h1 : (i.rev.castSucc : Fin (m + 2)) =
          ⟨m - i.val, by omega⟩ := by
        refine Fin.ext ?_
        simp only [Fin.val_castSucc, Fin.val_rev]
        omega
      have h2 : (i.rev.succ : Fin (m + 2)) =
          ⟨m - i.val + 1, by omega⟩ := by
        refine Fin.ext ?_
        simp only [Fin.val_succ, Fin.val_rev]
        omega
      have h3 : (i.castSucc : Fin (m + 2)) =
          ⟨i.val, by omega⟩ :=
        Fin.ext rfl
      have h4 : (i.succ : Fin (m + 2)) =
          ⟨i.val + 1, by omega⟩ :=
        Fin.ext rfl
      rw [adjPerm_swap_castSucc_succ, h1, h2, h3, h4]
      exact rawPair_swap A M M' d i.val (m - i.val) (m + 2)
        (by omega)
    have key : ∀ τ : Equiv.Perm (Fin (m + 2)),
        τ ∈ Submonoid.closure
          (Set.range fun i : Fin (m + 1) =>
            Equiv.swap i.castSucc i.succ) →
        (permMor M'.X (m + 2) (adjPerm τ) ▷
            tensorPow D M.X (m + 2)) ≫
          rawPair A M M' d (m + 2) =
        (tensorPow D M'.X (m + 2) ◁
            permMor M.X (m + 2) τ) ≫
          rawPair A M M' d (m + 2) := by
      intro τ hτ
      induction hτ using Submonoid.closure_induction_left with
      | one =>
        rw [adjPerm_one, permMor_one, permMor_one]
        simp
      | mul_left g hg τ' hτ' ih =>
        obtain ⟨i, rfl⟩ := hg
        rw [adjPerm_mul, permMor_mul, permMor_mul]
        simp only [MonoidalCategory.comp_whiskerRight,
          MonoidalCategory.whiskerLeft_comp, Category.assoc]
        rw [ih, ← whisker_exchange_assoc, hgen i]
    exact key σ (by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)

/-! ## The descended exchange law and self-adjointness -/

section Descended

/-- **The descended exchange law**: a permutation of the module
power crosses the descended pairing as its order-reversing
adjoint. -/
theorem pairPow_perm [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M') (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (modPowPerm (A := A) (X := M'.X) n (adjPerm σ) ▷
        modPow A M.X n) ≫ pairPow A M M' d n =
      (modPow A M'.X n ◁
          modPowPerm (A := A) (X := M.X) n σ) ≫
        pairPow A M M' d n := by
  have hππ : (modPowπ A M'.X n ▷ tensorPow D M.X n) ≫
      (modPow A M'.X n ◁ modPowπ A M.X n) ≫
      pairPow A M M' d n = rawPair A M M' d n := by
    rw [← MonoidalCategory.tensorHom_def_assoc,
      modPowπ_tensor_pairPow]
  apply modPow_whiskerLeft_hom_ext A M.X (modPow A M'.X n) n
  apply modPow_whiskerRight_hom_ext A M'.X n
    (tensorPow D M.X n)
  conv_lhs => rw [whisker_exchange_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, modPowπ_perm,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    modPowπ_perm, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, ← whisker_exchange_assoc]
  rw [hππ]
  exact rawPair_perm A M M' d n σ

/-- **Self-adjointness of the symmetriser across the pairing**:
the symmetriser acting on either module power pairs equally.  The
adjoint is a bijection of the group, so the average over all
permutations is invariant under the exchange law. -/
theorem symPowIdem_pairPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    (symPowIdem A M'.X n ▷ modPow A M.X n) ≫
        pairPow A M M' d n =
      (modPow A M'.X n ◁ symPowIdem A M.X n) ≫
        pairPow A M M' d n := by
  have hexpL : symPowIdem A M'.X n =
      ((n.factorial : ℂ))⁻¹ • ∑ σ : Equiv.Perm (Fin n),
        modPowPerm (A := A) (X := M'.X) n σ := by
    rw [symPowIdem, symmetriser, map_smul, map_sum]
    simp only [modPowAlg_single]
  have hexpR : symPowIdem A M.X n =
      ((n.factorial : ℂ))⁻¹ • ∑ σ : Equiv.Perm (Fin n),
        modPowPerm (A := A) (X := M.X) n σ := by
    rw [symPowIdem, symmetriser, map_smul, map_sum]
    simp only [modPowAlg_single]
  rw [hexpL, hexpR, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp,
    Linear.smul_comp]
  refine congrArg (HSMul.hSMul (((n.factorial : ℂ))⁻¹)) ?_
  rw [sum_whiskerRight, whiskerLeft_sum,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Fintype.sum_equiv
    ⟨adjPerm, adjPerm, adjPerm_adjPerm, adjPerm_adjPerm⟩
    _ _ fun σ => ?_
  have h := pairPow_perm A M M' d n (adjPerm σ)
  rw [adjPerm_adjPerm] at h
  exact h

/-- Self-adjointness of the symmetriser, in tensor form. -/
theorem symPowIdem_pairPow_tensor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    (symPowIdem A M'.X n ⊗ₘ 𝟙 (modPow A M.X n)) ≫
        pairPow A M M' d n =
      (𝟙 (modPow A M'.X n) ⊗ₘ symPowIdem A M.X n) ≫
        pairPow A M M' d n := by
  rw [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom]
  exact symPowIdem_pairPow A M M' d n

end Descended

end Exchange

end RS
