/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Interfaces.KoszulAction
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.TensorNonvanishing
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelPermCoord

/-!
# Sector intertwining for the standard model

The even and odd sector trace functionals for the standard model
`stdSuperPair k ℓ`, and their character formulas: the intertwining that
carries the abstract `superPermAction` kernel containment of
`KoszulAction.lean` to concrete characters.

## Main definitions

* `evenSectorTr k ℓ n` — the partial trace on the all-even colour
  block of `(superPow (stdSuperPair k ℓ) n).even`
* `oddSectorTr k ℓ n` — the partial trace on the all-odd colour
  block (in the even component when `n` is even)

## Main results

* `evenSectorTr_perm` — the character formula:
  `evenSectorTr k ℓ n (modelPermMap σ).evenMap = cycleProd (const k) σ`
* `oddSectorTr_perm` — the signed character formula:
  `oddSectorTr k ℓ n (modelPermMap σ).evenMap =
    sign(σ) · cycleProd (const (2ℓ)) σ`
  (for even `n`)

## The transport to an abstract package

The transport from `stdSuperPair k ℓ` to `strandImage f P` (for an
abstract Deligne package with `strandImage ≅ stdSuperPair k ℓ`) requires
conjugating `evenSectorTr` / `oddSectorTr` by the induced
`LinearEquiv` on `(superPow V n).even`.  Concretely: given a super
iso pair `(e, e')` with `e' ∘ e = id` and `e ∘ e' = id`, the
functoriality of `superPow` (tensorHom iterated) gives
  `superPowIso : superPow (stdSuperPair k ℓ) n ≅ superPow (strandImage f P) n`
and
  `evenSectorTr k ℓ n ∘ (conjugate by superPowIso.even) = evenSectorTr' f P n`
intertwines `modelPermMap` with `evenPermRep`.  The kernel containment
  `superPermAction f P n x = 0 → evenSectorTr' (evenPermRep f P n x) = 0`
follows from `superPermAction_zero_imp_evenPermRep_zero` in
`KoszulAction.lean`.
-/

noncomputable section

namespace RS

open Finset MonoidAlgebra

open scoped Classical

/-! ## All-even colourings -/

/-- The all-even colouring: every position gets an even colour. -/
def allEvenEmb (k ℓ n : ℕ) (f : Fin n → Fin k) : MixedColouring k ℓ n :=
  fun i => Sum.inl (f i)

/-- All-even colourings have empty odd support, hence even parity. -/
theorem allEvenEmb_isEven (k ℓ n : ℕ) (f : Fin n → Fin k) :
    (allEvenEmb k ℓ n f).IsEven := by
  unfold MixedColouring.IsEven MixedColouring.oddSet allEvenEmb
  have : Finset.univ.filter
      (fun i : Fin n =>
        (Sum.inl (f i) : Fin k ⊕ Fin (2 * ℓ)).isRight) = ∅ := by
    rw [Finset.filter_false_of_mem]
    intro i _
    simp [Sum.isRight]
  rw [this]; exact ⟨0, by simp⟩

/-- Composing an all-even colouring with a permutation. -/
theorem allEvenEmb_comp (k ℓ n : ℕ) (f : Fin n → Fin k)
    (σ : Equiv.Perm (Fin n)) :
    allEvenEmb k ℓ n f ∘ σ = allEvenEmb k ℓ n (f ∘ σ) := rfl

/-- The all-even embedding is injective. -/
theorem allEvenEmb_injective (k ℓ n : ℕ) :
    Function.Injective (allEvenEmb k ℓ n) := by
  intro f g h
  exact funext fun i => Sum.inl.inj (congrFun h i)

/-- `oddInversions` vanishes on all-even colourings: no position
is odd-coloured, so the inversion filter is empty. -/
theorem oddInversions_allEvenEmb (k ℓ n : ℕ)
    (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin k) :
    oddInversions σ (allEvenEmb k ℓ n f) = 0 := by
  unfold oddInversions allEvenEmb
  rw [show Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ σ p.1 > σ p.2 ∧
      (Sum.inl (f (σ p.1)) : Fin k ⊕ Fin (2 * ℓ)).isRight ∧
      (Sum.inl (f (σ p.2)) : Fin k ⊕ Fin (2 * ℓ)).isRight) =
    ∅ from by
    rw [Finset.filter_false_of_mem]
    intro ⟨a, b⟩ _
    simp [Sum.isRight]]
  exact Finset.card_empty

/-! ## Colour-model basis vectors -/

/-- A basis vector of the even colour model at an even colouring. -/
private noncomputable def evenBasis (k ℓ n : ℕ)
    (c : {c : MixedColouring k ℓ n // c.IsEven}) :
    (superPow (stdSuperPair k ℓ) n).even :=
  (colourPowerEquiv k ℓ n).evenEquiv.symm
    (show (colourPower k ℓ n).even from Pi.single c 1)

/-- The colour-model coordinate at an even colouring,
evaluated on a basis vector. -/
private theorem evenCoord_basis (k ℓ n : ℕ)
    (c₁ c₂ : {c : MixedColouring k ℓ n // c.IsEven}) :
    (colourPowerEquiv k ℓ n).evenEquiv (evenBasis k ℓ n c₂) c₁ =
      if c₁ = c₂ then 1 else 0 := by
  unfold evenBasis
  have hrw : (colourPowerEquiv k ℓ n).evenEquiv
      ((colourPowerEquiv k ℓ n).evenEquiv.symm
        (show (colourPower k ℓ n).even from Pi.single c₂ 1)) =
      (show (colourPower k ℓ n).even from Pi.single c₂ 1) :=
    (colourPowerEquiv k ℓ n).evenEquiv.apply_symm_apply _
  -- Apply function extensionality to extract the c₁ component
  have happ := congrFun hrw c₁
  simp only at happ
  rw [happ]
  -- Goal is now about Pi.single c₂ 1 applied to c₁
  by_cases h : c₁ = c₂ <;> simp [h]

/-- Specialisation: the coordinate at `allEvenEmb f` of
the basis vector at `allEvenEmb g`. -/
private theorem coordOf_basis_allEven (k ℓ n : ℕ)
    (f g : Fin n → Fin k) :
    coordOf (evenBasis k ℓ n
        ⟨allEvenEmb k ℓ n g, allEvenEmb_isEven k ℓ n g⟩)
      (allEvenEmb k ℓ n f) =
    if f = g then 1 else 0 := by
  unfold coordOf
  rw [dif_pos (allEvenEmb_isEven k ℓ n f)]
  rw [evenCoord_basis]
  by_cases h : f = g
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (fun hh => h
      (allEvenEmb_injective k ℓ n (congrArg Subtype.val hh)))]

/-! ## The even sector trace -/

/-- The even sector trace functional: the partial trace of an
endomorphism of `(superPow (stdSuperPair k ℓ) n).even` restricted to
the all-even colour block. -/
noncomputable def evenSectorTr (k ℓ n : ℕ) :
    Module.End ℂ (superPow (stdSuperPair k ℓ) n).even →ₗ[ℂ] ℂ where
  toFun T := ∑ f : Fin n → Fin k,
    (colourPowerEquiv k ℓ n).evenEquiv
      (T (evenBasis k ℓ n
        ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
      ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩
  map_add' T₁ T₂ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [LinearMap.add_apply]
    exact congrFun (map_add (colourPowerEquiv k ℓ n).evenEquiv
      (T₁ (evenBasis k ℓ n _)) (T₂ (evenBasis k ℓ n _))) _
  map_smul' r T := by
    simp only [RingHom.id_apply]
    have hterm : ∀ f : Fin n → Fin k,
        (colourPowerEquiv k ℓ n).evenEquiv
          ((r • T) (evenBasis k ℓ n
            ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
          ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩ =
        r • (colourPowerEquiv k ℓ n).evenEquiv
          (T (evenBasis k ℓ n
            ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
          ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩ := by
      intro f
      rw [LinearMap.smul_apply]
      exact congrFun (map_smul (colourPowerEquiv k ℓ n).evenEquiv r _) _
    rw [show (∑ f, (colourPowerEquiv k ℓ n).evenEquiv
          ((r • T) (evenBasis k ℓ n
            ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
          ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩) =
      ∑ f, r • (colourPowerEquiv k ℓ n).evenEquiv
          (T (evenBasis k ℓ n
            ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
          ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩ from
      Finset.sum_congr rfl fun f _ => hterm f]
    exact (Finset.smul_sum).symm

/-! ## Fixed-point count -/

/-- The sum over `if f ∘ σ = f then 1 else 0` equals `cycleProd (const m)`. -/
theorem fixedCount_eq_cycleProd (n m : ℕ) (σ : Equiv.Perm (Fin n)) :
    (∑ f : Fin n → Fin m,
      if f ∘ σ = f then (1 : ℂ) else 0) =
    cycleProd (fun _ => (m : ℂ)) σ := by
  -- Step 1: sum = card of fixed-point subtype
  rw [Finset.sum_boole]
  -- Step 2: card of filter = card of subtype
  rw [show #{f ∈ Finset.univ | f ∘ σ = f} =
    Fintype.card {f : Fin n → Fin m // f ∘ σ = f} from by
    rw [Fintype.card_subtype]]
  -- Step 3: fixed functions ≃ OrbitSpace → Fin m
  rw [Fintype.card_congr (fixedFunEquiv σ (Fin m)),
    Fintype.card_fun, Fintype.card_fin]
  -- Step 4: cycleProd (const m) = m ^ #orbits
  rw [cycleProd_const, card_orbitSpace]
  push_cast; ring

/-! ## The even character formula -/

/-- **Even character formula**: the even sector trace of
`modelPermMap σ` equals `cycleProd (fun _ => k) σ`. -/
theorem evenSectorTr_perm (k ℓ n : ℕ) (σ : Equiv.Perm (Fin n)) :
    evenSectorTr k ℓ n
      ((modelPermMap σ :
        SuperVect.Hom (superPow (stdSuperPair k ℓ) n)
          (superPow (stdSuperPair k ℓ) n)).evenMap) =
      cycleProd (fun _ => (k : ℂ)) σ := by
  -- Unfold evenSectorTr
  show ∑ f : Fin n → Fin k,
    (colourPowerEquiv k ℓ n).evenEquiv
      (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
        (evenBasis k ℓ n
          ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
      ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩ = _
  -- Each summand = coordOf of the modelPermMap image
  have hstep : ∀ f : Fin n → Fin k,
      (colourPowerEquiv k ℓ n).evenEquiv
        (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
          (evenBasis k ℓ n
            ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
        ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩ =
      coordOf (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
        (evenBasis k ℓ n
          ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
        (allEvenEmb k ℓ n f) := fun f => by
    unfold coordOf
    rw [dif_pos (allEvenEmb_isEven k ℓ n f)]
  rw [Finset.sum_congr rfl (fun f _ => hstep f)]
  -- Apply coordOf_modelPermMap'
  have hcoord : ∀ f : Fin n → Fin k,
      coordOf (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
        (evenBasis k ℓ n
          ⟨allEvenEmb k ℓ n f, allEvenEmb_isEven k ℓ n f⟩))
        (allEvenEmb k ℓ n f) =
      if f ∘ σ = f then 1 else 0 := fun f => by
    rw [coordOf_modelPermMap' σ]
    rw [oddInversions_allEvenEmb, pow_zero, one_mul, allEvenEmb_comp]
    exact coordOf_basis_allEven k ℓ n (f ∘ σ) f
  rw [Finset.sum_congr rfl (fun f _ => hcoord f)]
  exact fixedCount_eq_cycleProd n k σ

/-! ## All-odd colourings (even-n case) -/

/-- The all-odd colouring: every position gets an odd colour. -/
def allOddEmb (k ℓ n : ℕ) (g : Fin n → Fin (2 * ℓ)) :
    MixedColouring k ℓ n :=
  fun i => Sum.inr (g i)

/-- An all-odd colouring has `oddSet = univ`. -/
theorem allOddEmb_oddSet_card (k ℓ n : ℕ)
    (g : Fin n → Fin (2 * ℓ)) :
    (allOddEmb k ℓ n g).oddSet.card = n := by
  unfold MixedColouring.oddSet allOddEmb
  have : Finset.univ.filter
      (fun i : Fin n =>
        (Sum.inr (g i) : Fin k ⊕ Fin (2 * ℓ)).isRight) =
      Finset.univ := by
    rw [Finset.filter_true_of_mem]
    intro i _; simp [Sum.isRight]
  rw [this]; exact Finset.card_fin n

/-- All-odd colourings are even-parity iff `n` is even. -/
theorem allOddEmb_isEven_iff (k ℓ n : ℕ)
    (g : Fin n → Fin (2 * ℓ)) :
    (allOddEmb k ℓ n g).IsEven ↔ Even n := by
  unfold MixedColouring.IsEven
  rw [allOddEmb_oddSet_card]

/-- For even `n`, all-odd colourings are even-parity. -/
theorem allOddEmb_isEven (k ℓ n : ℕ) (hn : Even n)
    (g : Fin n → Fin (2 * ℓ)) :
    (allOddEmb k ℓ n g).IsEven :=
  (allOddEmb_isEven_iff k ℓ n g).mpr hn

/-- Composing an all-odd colouring with a permutation. -/
theorem allOddEmb_comp (k ℓ n : ℕ) (g : Fin n → Fin (2 * ℓ))
    (σ : Equiv.Perm (Fin n)) :
    allOddEmb k ℓ n g ∘ σ = allOddEmb k ℓ n (g ∘ σ) := rfl

/-- The all-odd embedding is injective. -/
theorem allOddEmb_injective (k ℓ n : ℕ) :
    Function.Injective (allOddEmb k ℓ n) := by
  intro f g h
  exact funext fun i => Sum.inr.inj (congrFun h i)

/-! ## Sign equals `(-1)^inversions` -/

/-- `adjTrans i` is a swap of two distinct elements. -/
private theorem adjTrans_isSwap {n : ℕ} (i : Fin n) :
    (adjTrans i).IsSwap := by
  exact ⟨i.castSucc, i.succ, by
    intro h; exact absurd (Fin.ext_iff.mp h) (by simp [Fin.val_succ]),
    rfl⟩

/-- The sign of a permutation equals `(-1)` raised to the
length of its adjacent-transposition word. -/
private theorem sign_eq_neg_one_pow_adjWord_length
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign σ : ℤˣ) =
      (-1 : ℤˣ) ^ (adjWord σ).length := by
  conv_lhs => rw [← adjWord_spec σ]
  rw [Equiv.Perm.sign_prod_list_swap
    (fun g hg => by
      rw [List.mem_map] at hg
      obtain ⟨i, _, rfl⟩ := hg
      exact adjTrans_isSwap i)]
  congr 1; exact List.length_map ..

/-- `wordSign w c = (-1)^(length w)` when `c` is all-odd. -/
private theorem wordSign_allOdd {n : ℕ} (w : List (Fin n))
    (g : Fin (n + 1) → Fin (2 * ℓ)) :
    wordSign w (allOddEmb k ℓ (n + 1) g) =
      (-1 : ℂ) ^ w.length := by
  induction w generalizing g with
  | nil => simp [wordSign]
  | cons i w ih =>
    show adjSign (allOddEmb k ℓ (n + 1) g)
        ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ *
      wordSign w (allOddEmb k ℓ (n + 1) g ∘
        Equiv.swap ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩) =
      (-1 : ℂ) ^ (i :: w).length
    have hadj : adjSign (allOddEmb k ℓ (n + 1) g)
        ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ = -1 := by
      unfold adjSign allOddEmb
      rw [if_pos ⟨by simp [Sum.isRight], by simp [Sum.isRight]⟩]
    rw [hadj]
    have hswap : allOddEmb k ℓ (n + 1) g ∘
        Equiv.swap (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩ =
        allOddEmb k ℓ (n + 1) (g ∘
          Equiv.swap (⟨i.val, by omega⟩ : Fin (n + 1))
            ⟨i.val + 1, by omega⟩) := rfl
    rw [hswap, ih, List.length_cons, pow_succ]; ring

/-- `(-1)^oddInversions σ c = sign σ` when `c` is all-odd, at
positive arity. -/
theorem neg_one_pow_oddInversions_allOdd {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1)))
    (g : Fin (n + 1) → Fin (2 * ℓ)) :
    (-1 : ℂ) ^ oddInversions σ (allOddEmb k ℓ (n + 1) g) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  have hw := wordSign_eq_oddInversions (k := k) (ℓ := ℓ)
    (adjWord σ) (allOddEmb k ℓ (n + 1) g)
  rw [wordPerm_adjWord] at hw
  rw [← hw, wordSign_allOdd (adjWord σ) g]
  -- Goal: (-1 : ℂ) ^ |w| = ((sign σ : ℤ) : ℂ)
  have hsign := sign_eq_neg_one_pow_adjWord_length σ
  have hval : (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ (adjWord σ).length := by
    calc (Equiv.Perm.sign σ : ℤ)
        = ↑((Equiv.Perm.sign σ : ℤˣ)) := rfl
      _ = ↑((-1 : ℤˣ) ^ (adjWord σ).length) := by rw [hsign]
      _ = (↑(-1 : ℤˣ)) ^ (adjWord σ).length :=
            (Units.val_pow_eq_pow_val _ _).symm
      _ = (-1 : ℤ) ^ (adjWord σ).length := rfl
  rw [hval]; push_cast; ring

/-- The sign-inversion identity at all arities. -/
theorem neg_one_pow_oddInversions_allOdd' (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (g : Fin n → Fin (2 * ℓ)) :
    (-1 : ℂ) ^ oddInversions σ (allOddEmb k ℓ n g) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  match n with
  | 0 =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst hσ
    suffices oddInversions (1 : Equiv.Perm (Fin 0))
        (allOddEmb k ℓ 0 g) = 0 by
      rw [this]; norm_num [Equiv.Perm.sign_one]
    unfold oddInversions
    convert Finset.card_empty (α := Fin 0 × Fin 0)
    exact Finset.eq_empty_of_forall_notMem
      fun ⟨a, _⟩ => Fin.elim0 a
  | n + 1 => exact neg_one_pow_oddInversions_allOdd σ g

/-! ## The odd sector trace (even-n case) -/

/-- The odd sector trace functional (for even `n`): the partial
trace on the all-odd colour block of
`(superPow (stdSuperPair k ℓ) n).even`. -/
noncomputable def oddSectorTr (k ℓ n : ℕ) (hn : Even n) :
    Module.End ℂ (superPow (stdSuperPair k ℓ) n).even →ₗ[ℂ] ℂ where
  toFun T := ∑ g : Fin n → Fin (2 * ℓ),
    (colourPowerEquiv k ℓ n).evenEquiv
      (T (evenBasis k ℓ n
        ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
      ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩
  map_add' T₁ T₂ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.add_apply]
    exact congrFun (map_add (colourPowerEquiv k ℓ n).evenEquiv
      (T₁ (evenBasis k ℓ n _)) (T₂ (evenBasis k ℓ n _))) _
  map_smul' r T := by
    simp only [RingHom.id_apply]
    have hterm : ∀ g : Fin n → Fin (2 * ℓ),
        (colourPowerEquiv k ℓ n).evenEquiv
          ((r • T) (evenBasis k ℓ n
            ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
          ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩ =
        r • (colourPowerEquiv k ℓ n).evenEquiv
          (T (evenBasis k ℓ n
            ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
          ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩ := by
      intro g
      rw [LinearMap.smul_apply]
      exact congrFun (map_smul (colourPowerEquiv k ℓ n).evenEquiv r _) _
    rw [show (∑ g, (colourPowerEquiv k ℓ n).evenEquiv
          ((r • T) (evenBasis k ℓ n
            ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
          ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩) =
      ∑ g, r • (colourPowerEquiv k ℓ n).evenEquiv
          (T (evenBasis k ℓ n
            ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
          ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩ from
      Finset.sum_congr rfl fun g _ => hterm g]
    exact (Finset.smul_sum).symm

/-- Specialisation: the coordinate at `allOddEmb g₁` of
the basis vector at `allOddEmb g₂`. -/
private theorem coordOf_basis_allOdd (k ℓ n : ℕ) (hn : Even n)
    (g₁ g₂ : Fin n → Fin (2 * ℓ)) :
    coordOf (evenBasis k ℓ n
        ⟨allOddEmb k ℓ n g₂, allOddEmb_isEven k ℓ n hn g₂⟩)
      (allOddEmb k ℓ n g₁) =
    if g₁ = g₂ then 1 else 0 := by
  unfold coordOf
  rw [dif_pos (allOddEmb_isEven k ℓ n hn g₁)]
  rw [evenCoord_basis]
  by_cases h : g₁ = g₂
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (fun hh => h
      (allOddEmb_injective k ℓ n (congrArg Subtype.val hh)))]

/-- **Odd character formula (even-n case)**: the odd sector trace
of `modelPermMap σ` equals `sign(σ) · cycleProd (const (2ℓ)) σ`. -/
theorem oddSectorTr_perm (k ℓ n : ℕ) (hn : Even n)
    (σ : Equiv.Perm (Fin n)) :
    oddSectorTr k ℓ n hn
      ((modelPermMap σ :
        SuperVect.Hom (superPow (stdSuperPair k ℓ) n)
          (superPow (stdSuperPair k ℓ) n)).evenMap) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        cycleProd (fun _ => ((2 * ℓ : ℕ) : ℂ)) σ := by
  -- Unfold
  show ∑ g : Fin n → Fin (2 * ℓ),
    (colourPowerEquiv k ℓ n).evenEquiv
      (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
        (evenBasis k ℓ n
          ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
      ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩ = _
  -- Rewrite via coordOf
  have hstep : ∀ g : Fin n → Fin (2 * ℓ),
      (colourPowerEquiv k ℓ n).evenEquiv
        (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
          (evenBasis k ℓ n
            ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
        ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩ =
      coordOf (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
        (evenBasis k ℓ n
          ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
        (allOddEmb k ℓ n g) := fun g => by
    unfold coordOf
    rw [dif_pos (allOddEmb_isEven k ℓ n hn g)]
  rw [Finset.sum_congr rfl (fun g _ => hstep g)]
  -- Apply coordOf_modelPermMap'
  have hcoord : ∀ g : Fin n → Fin (2 * ℓ),
      coordOf (((modelPermMap σ : SuperVect.Hom _ _).evenMap)
        (evenBasis k ℓ n
          ⟨allOddEmb k ℓ n g, allOddEmb_isEven k ℓ n hn g⟩))
        (allOddEmb k ℓ n g) =
      (-1 : ℂ) ^ oddInversions σ (allOddEmb k ℓ n g) *
        (if g ∘ σ = g then 1 else 0) := fun g => by
    rw [coordOf_modelPermMap' σ, allOddEmb_comp]
    exact congrArg
      ((-1 : ℂ) ^ oddInversions σ (allOddEmb k ℓ n g) * ·)
      (coordOf_basis_allOdd k ℓ n hn (g ∘ σ) g)
  rw [Finset.sum_congr rfl (fun g _ => hcoord g)]
  -- Factor out the sign (oddInversions is constant)
  have hsign : ∀ g : Fin n → Fin (2 * ℓ),
      (-1 : ℂ) ^ oddInversions σ (allOddEmb k ℓ n g) =
        ((Equiv.Perm.sign σ : ℤ) : ℂ) :=
    neg_one_pow_oddInversions_allOdd' n σ
  rw [show (∑ g : Fin n → Fin (2 * ℓ),
      (-1 : ℂ) ^ oddInversions σ (allOddEmb k ℓ n g) *
        (if g ∘ σ = g then 1 else 0)) =
    ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ∑ g : Fin n → Fin (2 * ℓ),
        (if g ∘ σ = g then (1 : ℂ) else 0) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [hsign g]]
  rw [fixedCount_eq_cycleProd]

end RS

end
