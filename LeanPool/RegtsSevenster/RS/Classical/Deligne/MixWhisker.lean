/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixSumPow

/-!
# Whiskered nonvanishing of the mixed sum

The nonvanishing of `MixSumPow.lean` says that the block
idempotent of a diagram avoiding the cell `(p + 1, q + 1)` acts
nonzero on the tensor power of the mixed sum.  For the dévissage
one needs the same statement after whiskering by an auxiliary
object `W`: the action stays nonzero inside `W ⊗ −`.

Whiskering is a `ℂ`-linear functor, so the whole extraction of
`SuperEmbed.lean` survives it verbatim.  The colour sums are the
model-independent middle of that argument: the entry formula
`nIn_permAlg_nOut` pins the normalised matrix entry of a
group-algebra element to a scalar times a transport, and applying
`W ◁ −` to it leaves the scalar alone.  Once every colour sum
vanishes the ambient endgame — reconstruction in `SuperVect` and
the super trace computation — is reused unchanged.

The hypothesis feeding the whiskered form is that no power of the
odd line is killed by `W ⊗ −`; for `W` a monoid object with
nonzero unit this is automatic, since the odd line is invertible.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Whiskered extraction of the colour sums -/

section WhiskerLetters

variable {A : Type u}

namespace MixedLetters

/-- **Whiskered extraction**: if a group-algebra element acts as
zero on the tensor power of the mixed object *after whiskering by
`W`*, all its colour sums vanish — provided no power of the odd
line is annihilated by `W ⊗ −`.  The proof is the unwhiskered one
run through the `ℂ`-linear functor `W ◁ −`. -/
theorem colourSum_eq_zero_whisker
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] [DecidableEq K]
    {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) (W : A)
    (hW : ∀ k : ℕ, 𝟙 (W ⊗ tensorPow A U k) ≠
      (0 : W ⊗ tensorPow A U k ⟶ W ⊗ tensorPow A U k))
    {n : ℕ} {x : SymGroupAlgebra n}
    (hx : W ◁ permAlg M n x = 0) (c d : Fin n → K) :
    colourSum par x c d = 0 := by
  by_cases hpop : popCount (par ∘ c) = popCount (par ∘ d)
  · have h1 : W ◁ (S.nIn n c ≫ permAlg M n x ≫ S.nOut n d) = 0 := by
      rw [MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.whiskerLeft_comp, hx, Limits.zero_comp,
        Limits.comp_zero]
    rw [S.nIn_permAlg_nOut hβ x c d, dite_eq_left hpop,
      MonoidalLinear.whiskerLeft_smul] at h1
    by_contra hne
    have h2 : W ◁ eqToHom (congrArg (tensorPow A U) hpop) = 0 := by
      have h3 := congrArg
        (fun t => (colourSum par x c d)⁻¹ • t) h1
      simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul,
        smul_zero] using h3
    refine hW (popCount (par ∘ c)) ?_
    have h4 := congrArg (fun t => t ≫
      W ◁ eqToHom (congrArg (tensorPow A U) hpop).symm) h2
    simpa only [← MonoidalCategory.whiskerLeft_comp, eqToHom_trans,
      eqToHom_refl, MonoidalCategory.whiskerLeft_id,
      Limits.zero_comp] using h4
  · exact colourSum_eq_zero_of_ne par x hpop

end MixedLetters

end WhiskerLetters

/-! ## The whiskered ambient extraction and endgame -/

section AmbientWhisker

variable {A : Type u}

/-- **Whiskered extraction in the ambient category**: if the block
idempotent acts as zero on the whiskered tensor power of the mixed
sum, every colour sum of the idempotent vanishes. -/
theorem colourSum_eq_zero_of_whisker_sum
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v})
    (W : A) {U : A}
    (hW : ∀ k : ℕ, 𝟙 (W ⊗ tensorPow A U k) ≠
      (0 : W ⊗ tensorPow A U k ⟶ W ⊗ tensorPow A U k))
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) (p q : ℕ)
    {lam : YoungDiagram}
    (hkill : W ◁ permAlg (sumPow (𝟙_ A) p ⊞ sumPow U q) lam.card
      (P.e lam) = 0) :
    ∀ c d : Fin lam.card → Fin (p + 1) ⊕ Fin (q + 1),
      colourSum mixedPar (P.e lam) c d = 0 :=
  fun c d => (mixedSumLetters p q U).colourSum_eq_zero_whisker hβ W
    hW hkill c d

/-- **The whiskered nonvanishing half of Deligne 1.9**: whiskering
by `W` does not destroy the action of the block idempotent on a
direct sum of `p + 1` unit copies and `q + 1` odd-line copies, at
any diagram avoiding the cell `(p + 1, q + 1)`.  The nontriviality
of the ambient category is replaced by the sharper hypothesis that
`W ⊗ −` kills no power of the line. -/
theorem whisker_permAlg_sum_ne_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v})
    (P₀ : SchurPackage.{0}) (W : A) {U : A}
    (hW : ∀ k : ℕ, 𝟙 (W ⊗ tensorPow A U k) ≠
      (0 : W ⊗ tensorPow A U k ⟶ W ⊗ tensorPow A U k))
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) (p q : ℕ)
    {lam : YoungDiagram}
    (hcell : ((p + 1, q + 1) : ℕ × ℕ) ∉ lam) :
    W ◁ permAlg (sumPow (𝟙_ A) p ⊞ sumPow U q) lam.card (P.e lam)
      ≠ 0 := by
  intro hkill
  have he : P.e lam = P₀.e lam := by
    rw [P.e_eq_nProjector lam, P₀.e_eq_nProjector lam]
  have hcs := colourSum_eq_zero_of_whisker_sum P W hW hβ p q hkill
  rw [he] at hcs
  exact not_schurKilled_stdSuper P₀ hcell
    (schurKilled_stdSuper_of_colourSum P₀ p q hcs)

end AmbientWhisker

/-! ## Transport of the whiskered action along an isomorphism -/

section Transport

variable {A : Type u}

/-- **The whiskered action is an isomorphism invariant**: the
tensor power of the inverse splits the tensor power of the
isomorphism, and `W ◁ −` is a functor, so the naturality square of
`permAlg` transports the vanishing. -/
theorem whisker_permAlg_eq_zero_of_iso
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (W : A) {X Y : A} (e : X ≅ Y)
    {n : ℕ} (x : SymGroupAlgebra n) (h : W ◁ permAlg X n x = 0) :
    W ◁ permAlg Y n x = 0 := by
  have hST : (W ◁ tensorPowMap e.inv n) ≫
      (W ◁ tensorPowMap e.hom n) = 𝟙 (W ⊗ tensorPow A Y n) := by
    rw [← MonoidalCategory.whiskerLeft_comp, ← tensorPowMap_comp,
      e.inv_hom_id, tensorPowMap_id,
      MonoidalCategory.whiskerLeft_id]
  have hnat : (W ◁ permAlg X n x) ≫ (W ◁ tensorPowMap e.hom n) =
      (W ◁ tensorPowMap e.hom n) ≫ (W ◁ permAlg Y n x) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, permAlg_natural]
  calc W ◁ permAlg Y n x
      = ((W ◁ tensorPowMap e.inv n) ≫
          (W ◁ tensorPowMap e.hom n)) ≫ (W ◁ permAlg Y n x) := by
        rw [hST, Category.id_comp]
    _ = (W ◁ tensorPowMap e.inv n) ≫ (W ◁ permAlg X n x) ≫
        (W ◁ tensorPowMap e.hom n) := by
        rw [Category.assoc, ← hnat]
    _ = 0 := by rw [h, Limits.zero_comp, Limits.comp_zero]

end Transport

/-! ## Whiskered powers of an odd line -/

section LinePowers

variable {A : Type u}

/-- A zero identity transfers along an isomorphism.  Stated at
general objects. -/
private theorem id_zero_of_iso [Category.{v} A] [Preadditive A]
    {X Y : A} (e : X ≅ Y) (h : 𝟙 X = 0) :
    𝟙 Y = 0 := by
  calc 𝟙 Y = e.inv ≫ 𝟙 X ≫ e.hom := by
        rw [Category.id_comp, e.inv_hom_id]
    _ = 0 := by rw [h, Limits.zero_comp, Limits.comp_zero]

/-- **Whiskered powers of an odd line are nonzero** when the unit
of the whiskering monoid is: one more copy of the line is undone
through the line's self-pairing, and the empty power leaves `W`
itself, whose identity carries the unit. -/
theorem OddLine.whisker_tensorPow_id_ne_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [MonoidalPreadditive A]
    (L : OddLine A)
    {W : A} [MonObj W] (hW : η[W] ≠ 0) (k : ℕ) :
    𝟙 (W ⊗ tensorPow A L.obj k) ≠
      (0 : W ⊗ tensorPow A L.obj k ⟶ W ⊗ tensorPow A L.obj k) := by
  induction k with
  | zero =>
    intro h
    refine hW ?_
    have h1 : 𝟙 W = 0 :=
      id_zero_of_iso (ρ_ W) (show 𝟙 (W ⊗ 𝟙_ A) = 0 from h)
    calc η[W] = η[W] ≫ 𝟙 W := (Category.comp_id _).symm
      _ = 0 := by rw [h1, Limits.comp_zero]
  | succ k ih =>
    intro h
    have h1 : 𝟙 ((W ⊗ tensorPow A L.obj (k + 1)) ⊗ L.obj) = 0 := by
      rw [← MonoidalCategory.id_whiskerRight, h,
        MonoidalPreadditive.zero_whiskerRight]
    exact ih (id_zero_of_iso
      (α_ W (tensorPow A L.obj k ⊗ L.obj) L.obj ≪≫
        whiskerLeftIso W
          (α_ (tensorPow A L.obj k) L.obj L.obj ≪≫
            whiskerLeftIso (tensorPow A L.obj k) L.sq ≪≫
            ρ_ (tensorPow A L.obj k))) h1)

end LinePowers

/-! ## The whiskered mixed sum -/

section MixWhisker

variable {A : Type u}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

end MixWhisker

end RS
