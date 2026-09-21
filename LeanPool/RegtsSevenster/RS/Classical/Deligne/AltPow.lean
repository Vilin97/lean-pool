/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymAlg

/-!
# Alternating powers over an internal monoid

The antisymmetric counterpart of the symmetric-power interface of
`SymAlg.lean`: the sign-character central idempotent of the group
algebra `ℂ[Sₙ]` — the antisymmetriser — and the alternating power
of a module over an internal monoid, presented as the coequalizer
of the antisymmetriser's action on the module power against the
identity.

* `antisymmetriser n`: the sign-character central idempotent
  `(1/n!) • ∑ σ, sign σ • σ` of the group algebra, with signed
  absorption and idempotency.
* `altPow A X n`: the alternating power, presented as the
  coequalizer of `modPowAlg (antisymmetriser n)` against the
  identity — which the idempotent splits into a direct summand:
  `altPowσ ≫ altPowπ = 𝟙` and `altPowπ ≫ altPowσ` is the
  antisymmetriser's action.  Morphisms out of the alternating power
  descend along `altPowπ`; morphisms in arrive through the section
  `altPowσ`.

The `A`-module structure on the alternating power is outside this
module's scope, exactly as its symmetric counterpart lives in
`PowAct.lean` rather than in `SymAlg.lean`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The antisymmetriser

The sign-character central idempotent of the group algebra
`ℂ[Sₙ]` — the `charIdempotent 1 sign` of the Schur interface,
written directly.
-/

section Antisymmetriser

/-- **The antisymmetriser** `(1/n!) • ∑ σ, sign σ • σ` of the
symmetric-group algebra. -/
noncomputable def antisymmetriser (n : ℕ) : SymGroupAlgebra n :=
  ((n.factorial : ℂ))⁻¹ •
    ∑ σ : Equiv.Perm (Fin n),
      MonoidAlgebra.single σ ((Equiv.Perm.sign σ : ℤ) : ℂ)

/-- The square of a sign, cast to `ℂ`, is one. -/
theorem sign_coe_mul_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) =
      1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, Int.cast_one]

/-- The antisymmetriser absorbs every group element on the right,
up to its sign. -/
@[simp]
theorem antisymmetriser_mul_single (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    antisymmetriser n * MonoidAlgebra.single τ (1 : ℂ) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • antisymmetriser n := by
  unfold antisymmetriser
  rw [smul_mul_assoc, Finset.sum_mul,
    smul_comm ((Equiv.Perm.sign τ : ℤ) : ℂ)]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulRight]
  rw [MonoidAlgebra.single_mul_single, mul_one,
    MonoidAlgebra.smul_single', Equiv.Perm.sign_mul, Units.val_mul,
    Int.cast_mul, mul_comm ((Equiv.Perm.sign σ : ℤ) : ℂ),
    ← mul_assoc, sign_coe_mul_self, one_mul]

/-- The antisymmetriser absorbs every group element on the left,
up to its sign. -/
@[simp]
theorem single_mul_antisymmetriser (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.single τ (1 : ℂ) * antisymmetriser n =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • antisymmetriser n := by
  unfold antisymmetriser
  rw [mul_smul_comm, smul_comm ((Equiv.Perm.sign τ : ℤ) : ℂ)]
  congr 1
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [MonoidAlgebra.single_mul_single, one_mul,
    MonoidAlgebra.smul_single', Equiv.Perm.sign_mul, Units.val_mul,
    Int.cast_mul, ← mul_assoc, sign_coe_mul_self, one_mul]

/-- The antisymmetriser absorbs a sign-weighted group element on
the right, exactly. -/
theorem antisymmetriser_mul_sign_single (n : ℕ)
    (τ : Equiv.Perm (Fin n)) :
    antisymmetriser n *
        MonoidAlgebra.single τ ((Equiv.Perm.sign τ : ℤ) : ℂ) =
      antisymmetriser n := by
  have h : MonoidAlgebra.single τ ((Equiv.Perm.sign τ : ℤ) : ℂ) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) •
        MonoidAlgebra.single τ (1 : ℂ) := by
    rw [MonoidAlgebra.smul_single', mul_one]
  rw [h, mul_smul_comm, antisymmetriser_mul_single, smul_smul,
    sign_coe_mul_self, one_smul]

/-- **The antisymmetriser is idempotent.** -/
theorem antisymmetriser_idem (n : ℕ) :
    antisymmetriser n * antisymmetriser n = antisymmetriser n := by
  nth_rewrite 2 [antisymmetriser]
  rw [mul_smul_comm, Finset.mul_sum]
  simp only [antisymmetriser_mul_sign_single, Finset.sum_const,
    Finset.card_univ]
  rw [Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by
      exact_mod_cast n.factorial_ne_zero), one_smul]

end Antisymmetriser

/-! ## The alternating power -/

section AltPow

/-- The antisymmetriser acting on the module power. -/
noncomputable def altPowIdem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : modPow A X n ⟶ modPow A X n :=
  modPowAlg A X n (antisymmetriser n)

/-- The antisymmetriser's action is idempotent. -/
theorem altPowIdem_idem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    altPowIdem A X n ≫ altPowIdem A X n = altPowIdem A X n := by
  have h := congrArg (modPowAlg A X n) (antisymmetriser_idem n)
  rw [map_mul] at h
  exact h

/-- **The alternating power**: the coinvariants of the
antisymmetriser's action — the coequalizer of the action against
the identity.  The idempotency splits it off as a direct summand of
the module power, with section `altPowσ`; this presentation is
chosen because consumers build morphisms out of the alternating
power by descent along `altPowπ` and morphisms into it through the
section. -/
noncomputable def altPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : D :=
  coequalizer (altPowIdem A X n) (𝟙 (modPow A X n))

/-- The projection onto the alternating power. -/
noncomputable def altPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : modPow A X n ⟶ altPow A X n :=
  coequalizer.π _ _

instance [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : Epi (altPowπ A X n) :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- The antisymmetriser is absorbed by the projection. -/
@[reassoc (attr := simp)]
theorem altPowIdem_π
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    altPowIdem A X n ≫ altPowπ A X n = altPowπ A X n := by
  have h := coequalizer.condition (altPowIdem A X n)
    (𝟙 (modPow A X n))
  rwa [Category.id_comp] at h

/-- The section of the alternating power, from idempotency. -/
noncomputable def altPowσ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : altPow A X n ⟶ modPow A X n :=
  coequalizer.desc (altPowIdem A X n)
    (by rw [Category.id_comp, altPowIdem_idem])

/-- The section realises the antisymmetriser as projection followed
by inclusion. -/
@[reassoc (attr := simp)]
theorem altPowπ_altPowσ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    altPowπ A X n ≫ altPowσ A X n = altPowIdem A X n :=
  coequalizer.π_desc _ _

/-- Morphisms out of the alternating power are determined by their
composite with the projection. -/
theorem altPow_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {W : D} {k l : altPow A X n ⟶ W}
    (h : altPowπ A X n ≫ k = altPowπ A X n ≫ l) : k = l :=
  coequalizer.hom_ext h

/-- **The alternating power is a direct summand**: the section
followed by the projection is the identity. -/
@[reassoc (attr := simp)]
theorem altPowσ_altPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    altPowσ A X n ≫ altPowπ A X n = 𝟙 (altPow A X n) := by
  apply altPow_hom_ext A X
  rw [← Category.assoc, altPowπ_altPowσ, altPowIdem_π,
    Category.comp_id]

/-- Descend a morphism absorbed by the antisymmetriser to the
alternating power. -/
noncomputable def altPowDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {W : D} (k : modPow A X n ⟶ W)
    (h : altPowIdem A X n ≫ k = k) : altPow A X n ⟶ W :=
  coequalizer.desc k (by rw [Category.id_comp, h])

/-- The descent factors the given morphism through the
projection. -/
@[reassoc (attr := simp)]
theorem altPowπ_desc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {W : D} (k : modPow A X n ⟶ W)
    (h : altPowIdem A X n ≫ k = k) :
    altPowπ A X n ≫ altPowDesc A X k h = k :=
  coequalizer.π_desc _ _

end AltPow

end RS
