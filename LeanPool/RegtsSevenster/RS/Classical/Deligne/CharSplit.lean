/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.RegularSum
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.Package

/-!
# Character splitting of the completed cycle product

The completed cycle product `cycleFun` is multiplicative in the
scalar sequence and expands over the Jacobi–Trudi characters with
Schur coefficients — the inverse Frobenius formula.  Pairing the
expansion against a third character produces the Kronecker
multiplicities, which are nonnegative integers by the equivariant
Hom-space count, and yields the splitting of the Schur
specialisation at a pointwise product of scalar sequences over
pairs of shapes.
-/

namespace RS

open Finset Equiv

universe u

/-! ### The completed cycle product -/

/-- The completed cycle product of a prospective power-sum
sequence: the product of `t` over the cycle type, completed by
`t 1` over the fixed points. -/
noncomputable def cycleFun {n : ℕ} (t : ℕ → ℂ)
    (π : Equiv.Perm (Fin n)) : ℂ :=
  (π.cycleType.map t).prod * (t 1) ^ (n - π.cycleType.sum)

/-- `cycleFun` is the completed cycle-type product of the
orbit-factorization development. -/
theorem cycleFun_eq_cycleProd {n : ℕ} (t : ℕ → ℂ)
    (π : Equiv.Perm (Fin n)) :
    cycleFun t π = cycleProd t π :=
  rfl

/-- **Multiplicativity of the completed cycle product** in the
scalar sequence. -/
theorem cycleFun_mul {n : ℕ} (t t' : ℕ → ℂ)
    (π : Equiv.Perm (Fin n)) :
    cycleFun (fun c => t c * t' c) π =
      cycleFun t π * cycleFun t' π := by
  rw [cycleFun, cycleFun, cycleFun, Multiset.prod_map_mul, mul_pow]
  ring

/-- The completed cycle product is a class function. -/
theorem cycleFun_conj {n : ℕ} (t : ℕ → ℂ)
    (σ π : Equiv.Perm (Fin n)) :
    cycleFun t (σ * π * σ⁻¹) = cycleFun t π := by
  rw [cycleFun, cycleFun, Equiv.Perm.cycleType_conj]

/-- The completed cycle product is invariant under relabelling
along an equality of sizes. -/
theorem cycleFun_permCast {m n : ℕ} (h : m = n) (t : ℕ → ℂ)
    (π : Equiv.Perm (Fin m)) :
    cycleFun t (permCast h π) = cycleFun t π := by
  subst h
  rw [permCast_rfl, Equiv.refl_apply]

/-! ### Shape-level Frobenius and orthonormality

The Frobenius formula and the orthonormality of the Jacobi–Trudi
characters, reindexed along `permCast` to the group `S_n` shared by
all shapes of size `n`. -/

/-- **The Frobenius formula at a shape**: the normalized pairing of
the recast Jacobi–Trudi character with the completed cycle product
is the Schur specialisation. -/
theorem jtChar_shape_frobenius {n : ℕ} (μ : Shape n) (t : ℕ → ℂ) :
    ((n.factorial : ℂ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
      jtChar μ.val (permCast μ.prop.symm π) * cycleFun t π =
    diagramSchur μ.val t := by
  rw [show ((n.factorial : ℂ)) = (μ.val.card.factorial : ℂ) from by
    rw [μ.prop]]
  rw [← jtChar_frobenius' μ.val t,
    ← Equiv.sum_comp (permCast μ.prop.symm)
      (fun g => jtChar μ.val g * cycleProd t g)]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← cycleFun_eq_cycleProd, cycleFun_permCast]

/-- **Orthonormality at a shape**: the recast Jacobi–Trudi
character has unit norm for the class pairing of `S_n`. -/
theorem jtChar_shape_orthonormal {n : ℕ} (μ : Shape n) :
    ((n.factorial : ℂ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
      jtChar μ.val (permCast μ.prop.symm π) *
        jtChar μ.val (permCast μ.prop.symm π) = 1 := by
  rw [show ((n.factorial : ℂ)) = (μ.val.card.factorial : ℂ) from by
    rw [μ.prop]]
  rw [Equiv.sum_comp (permCast μ.prop.symm)
    (fun g => jtChar μ.val g * jtChar μ.val g)]
  exact jtChar_orthonormal μ.val

/-! ### Cross-shape orthogonality

Distinct shapes of one size have orthogonal recast characters: a
common irreducible constituent would force the two Schur
specialisations to agree, contradicting the separation theorem. -/

/-- **Orthogonality of the recast characters**: the class pairing
of the Jacobi–Trudi characters of distinct shapes of size `n`
vanishes. -/
theorem jtChar_orthogonal {n : ℕ} (μ ν : Shape n) (hne : μ ≠ ν) :
    ((n.factorial : ℂ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
      jtChar μ.val (permCast μ.prop.symm π) *
        jtChar ν.val (permCast ν.prop.symm π) = 0 := by
  classical
  set ρμ : Representation ℂ (Equiv.Perm (Fin n))
      (subCarrier (jtSimple μ.val)) :=
    (rhoS (jtSimple μ.val)).comp (permCastHom μ.prop.symm) with hρμ
  set ρν : Representation ℂ (Equiv.Perm (Fin n))
      (subCarrier (jtSimple ν.val)) :=
    (rhoS (jtSimple ν.val)).comp (permCastHom ν.prop.symm) with hρν
  haveI : ρμ.IsIrreducible :=
    isIrreducible_comp_permCastHom μ.prop.symm _
      (rhoS_isIrreducible _ (jtSimple_simple μ.val))
  haveI : ρν.IsIrreducible :=
    isIrreducible_comp_permCastHom ν.prop.symm _
      (rhoS_isIrreducible _ (jtSimple_simple ν.val))
  have hcard0 : ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) :=
    invertibleOfNonzero hcard0
  -- the recast characters are the characters of the pullbacks
  have hchμ : ∀ g : Equiv.Perm (Fin n),
      ρμ.character g = jtChar μ.val (permCast μ.prop.symm g) := by
    intro g
    rw [jtSimple_char μ.val]
    rfl
  have hchν : ∀ g : Equiv.Perm (Fin n),
      ρν.character g = jtChar ν.val (permCast ν.prop.symm g) := by
    intro g
    rw [jtSimple_char ν.val]
    rfl
  -- no equivalence: else the Schur specialisations agree
  have hnoiso : ¬ Nonempty (ρν.Equiv ρμ) := by
    rintro ⟨φ⟩
    have hchar := Representation.char_iso φ
    have hds : ∀ s : ℕ → ℂ,
        diagramSchur ν.val s = diagramSchur μ.val s := by
      intro s
      rw [← jtChar_shape_frobenius μ s, ← jtChar_shape_frobenius ν s]
      congr 1
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← hchμ g, ← hchν g, hchar]
    exact hne (Shape.ext (diagramSchur_injective hds)).symm
  have horth := Representation.char_orthonormal ρμ ρν
  rw [if_neg hnoiso] at horth
  rw [show ((n.factorial : ℂ))⁻¹ =
      ((Nat.card (Equiv.Perm (Fin n)) : ℂ))⁻¹ from by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]]
  rw [show (∑ π : Equiv.Perm (Fin n),
      jtChar μ.val (permCast μ.prop.symm π) *
        jtChar ν.val (permCast ν.prop.symm π)) =
      ∑ π : Equiv.Perm (Fin n),
        ρμ.character π * ρν.character π⁻¹ from by
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [hchμ π, show ρν.character π⁻¹ =
      nChar (jtSimple ν.val) (permCast ν.prop.symm π⁻¹) from rfl,
      permCast_inv, ← jtSimple_char ν.val, jtChar_inv]]
  rw [horth]

/-! ### The character expansion of the completed cycle product

The recast idempotents of a Schur package span the class elements
of `ℂ[S_n]`; expanding the class element of the completed cycle
product over them and pairing against each character determines the
coefficients as Schur specialisations — the inverse Frobenius
formula. -/

/-- The coefficients of a recast idempotent: the normalized recast
Jacobi–Trudi character. -/
theorem shape_e_coeff (P : SchurPackage.{u}) {n : ℕ} (μ : Shape n)
    (π : Equiv.Perm (Fin n)) :
    (Shape.e P μ).coeff π =
      ((P.dim μ.val : ℂ) / (n.factorial : ℂ)) *
        jtChar μ.val (permCast μ.prop.symm π) := by
  have h1 : (Shape.e P μ).coeff π =
      (P.e μ.val).coeff ((permCast μ.prop).symm π) := by
    change (symCast (le_of_eq μ.prop) (P.e μ.val)).coeff π =
      (P.e μ.val).coeff ((permCast μ.prop).symm π)
    rw [symCast_apply_of_eq μ.prop (P.e μ.val) π]
  rw [h1, P.e_coeff, P.char_eq_jtChar, permCast_symm]
  rw [show ((μ.val.card.factorial : ℂ)) = (n.factorial : ℂ) from by
    rw [μ.prop]]

/-- **The recast idempotents span the class elements**: every
conjugation-invariant coefficient function's class element is a
linear combination of the `Shape.e P μ`. -/
theorem classElem_eq_sum_shape_e (P : SchurPackage.{u}) {n : ℕ}
    (c : Equiv.Perm (Fin n) → ℂ)
    (hc : ∀ g k : Equiv.Perm (Fin n), c (k * g * k⁻¹) = c g) :
    ∃ a : Shape n → ℂ,
      classElem c = ∑ μ : Shape n, a μ • Shape.e P μ := by
  obtain ⟨a, ha⟩ := eq_sum_shape_e_of_mem_span P
    (classElem_mem_span_classSum c hc)
  exact ⟨a, ha.symm⟩

/-- **The character expansion of the completed cycle product** —
the inverse Frobenius formula: the completed cycle product expands
over the recast Jacobi–Trudi characters with the Schur
specialisations as coefficients. -/
theorem cycleFun_expand {n : ℕ} (t : ℕ → ℂ)
    (π : Equiv.Perm (Fin n)) :
    cycleFun t π = ∑ μ : Shape n,
      diagramSchur μ.val t * jtChar μ.val (permCast μ.prop.symm π) := by
  classical
  set P : SchurPackage.{0} := schurPackage.{0} with hP
  obtain ⟨a, ha⟩ := classElem_eq_sum_shape_e P
    (fun g => cycleFun t g) (fun g k => cycleFun_conj t k g)
  set b : Shape n → ℂ :=
    fun μ => a μ * ((P.dim μ.val : ℂ) / (n.factorial : ℂ)) with hb
  -- the coefficient identity at every permutation
  have hcoeff : ∀ g : Equiv.Perm (Fin n), cycleFun t g =
      ∑ μ : Shape n, b μ * jtChar μ.val (permCast μ.prop.symm g) := by
    intro g
    have h := congrArg (fun z : SymGroupAlgebra n => z.coeff g) ha
    rw [show (classElem (fun g => cycleFun t g)).coeff g =
      cycleFun t g from classElem_coeff _ g] at h
    rw [show (∑ μ : Shape n, a μ • Shape.e P μ).coeff g =
        ∑ μ : Shape n, (a μ • Shape.e P μ).coeff g from by
      rw [MonoidAlgebra.coeff_sum]
      exact Finsupp.finsetSum_apply _ _ _] at h
    rw [Finset.sum_congr rfl (fun μ _ => show
        (a μ • Shape.e P μ).coeff g =
          a μ * (Shape.e P μ).coeff g from
        MonoidAlgebra.smul_apply _ _ _)] at h
    rw [Finset.sum_congr rfl (fun μ _ => by
      rw [shape_e_coeff P μ g, ← mul_assoc])] at h
    exact h
  -- the coefficients are the Schur specialisations
  have hbs : ∀ ν : Shape n, b ν = diagramSchur ν.val t := by
    intro ν
    rw [← jtChar_shape_frobenius ν t]
    rw [Finset.sum_congr rfl fun g _ => by rw [hcoeff g]]
    rw [Finset.sum_congr rfl fun g _ => Finset.mul_sum
      (f := fun μ : Shape n =>
        b μ * jtChar μ.val (permCast μ.prop.symm g))
      (a := jtChar ν.val (permCast ν.prop.symm g)) Finset.univ]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun μ _ => show
        (∑ g : Equiv.Perm (Fin n),
          jtChar ν.val (permCast ν.prop.symm g) *
            (b μ * jtChar μ.val (permCast μ.prop.symm g))) =
        b μ * ∑ g : Equiv.Perm (Fin n),
          jtChar ν.val (permCast ν.prop.symm g) *
            jtChar μ.val (permCast μ.prop.symm g) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring]
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun μ _ =>
      (mul_left_comm ((n.factorial : ℂ))⁻¹ (b μ) _)]
    rw [Finset.sum_eq_single ν
      (fun μ _ hμν => by
        rw [jtChar_orthogonal ν μ (Ne.symm hμν), mul_zero])
      (fun h => absurd (Finset.mem_univ ν) h)]
    rw [jtChar_shape_orthonormal ν, mul_one]
  rw [hcoeff π]
  exact Finset.sum_congr rfl fun μ _ => by rw [hbs μ]

/-! ### Kronecker multiplicities

The triple class pairing of three recast characters counts, by the
equivariant Hom-space dimension against a tensor product of
pullback representations, a nonnegative integer. -/

/-- The Kronecker multiplicity of three shapes of one size: the
normalized triple class pairing of their recast Jacobi–Trudi
characters. -/
noncomputable def kronMult {n : ℕ} (lam μ ν : Shape n) : ℂ :=
  ((n.factorial : ℂ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
    jtChar lam.val (permCast lam.prop.symm π) *
      jtChar μ.val (permCast μ.prop.symm π) *
      jtChar ν.val (permCast ν.prop.symm π)

/-- **Kronecker multiplicities are nonnegative integers**: the
triple pairing is the dimension of an equivariant Hom space. -/
theorem kronMult_exists_nat {n : ℕ} (lam μ ν : Shape n) :
    ∃ m : ℕ, kronMult lam μ ν = m := by
  classical
  set ρl : Representation ℂ (Equiv.Perm (Fin n))
      (subCarrier (jtSimple lam.val)) :=
    (rhoS (jtSimple lam.val)).comp (permCastHom lam.prop.symm)
    with hρl
  set ρμ : Representation ℂ (Equiv.Perm (Fin n))
      (subCarrier (jtSimple μ.val)) :=
    (rhoS (jtSimple μ.val)).comp (permCastHom μ.prop.symm) with hρμ
  set ρν : Representation ℂ (Equiv.Perm (Fin n))
      (subCarrier (jtSimple ν.val)) :=
    (rhoS (jtSimple ν.val)).comp (permCastHom ν.prop.symm) with hρν
  have hcard0 : ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) :=
    invertibleOfNonzero hcard0
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (W := TensorProduct ℂ (subCarrier (jtSimple μ.val))
      (subCarrier (jtSimple ν.val)))
    ρl (Representation.tprod ρμ ρν)
  refine ⟨Module.finrank ℂ
    (Representation.IntertwiningMap ρl
      (Representation.tprod ρμ ρν)), ?_⟩
  rw [← h, kronMult]
  rw [show ((n.factorial : ℂ))⁻¹ =
      ((Nat.card (Equiv.Perm (Fin n)) : ℂ))⁻¹ from by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Representation.char_tensor, Pi.mul_apply]
  rw [show ρμ.character π =
    jtChar μ.val (permCast μ.prop.symm π) from by
      rw [jtSimple_char μ.val]; rfl]
  rw [show ρν.character π =
    jtChar ν.val (permCast ν.prop.symm π) from by
      rw [jtSimple_char ν.val]; rfl]
  rw [show ρl.character π⁻¹ =
    jtChar lam.val (permCast lam.prop.symm π) from by
      rw [show ρl.character π⁻¹ =
        nChar (jtSimple lam.val) (permCast lam.prop.symm π⁻¹) from
          rfl,
        permCast_inv, ← jtSimple_char lam.val, jtChar_inv]]
  ring

/-! ### The Kronecker splitting identity

The Schur specialisation at a pointwise product of scalar
sequences splits over pairs of shapes with Kronecker
multiplicities: Frobenius at the product, multiplicativity of the
completed cycle product, and the character expansion of each
factor. -/

/-- **The Kronecker splitting identity**: the Schur specialisation
at a pointwise product of scalar sequences is the
Kronecker-weighted sum of products of Schur specialisations. -/
theorem diagramSchur_pointwise_mul (lam : YoungDiagram)
    (t t' : ℕ → ℂ) :
    diagramSchur lam (fun c => t c * t' c) =
      ∑ μ : Shape lam.card, ∑ ν : Shape lam.card,
        kronMult ⟨lam, rfl⟩ μ ν * diagramSchur μ.val t *
          diagramSchur ν.val t' := by
  classical
  set L : Shape lam.card := ⟨lam, rfl⟩ with hL
  rw [show diagramSchur lam (fun c => t c * t' c) =
    diagramSchur L.val (fun c => t c * t' c) from rfl]
  rw [← jtChar_shape_frobenius L (fun c => t c * t' c)]
  rw [Finset.sum_congr rfl fun π _ => by
    rw [cycleFun_mul t t' π, cycleFun_expand t π,
      cycleFun_expand t' π]]
  -- expand the product of the two shape sums
  rw [Finset.sum_congr rfl fun π _ => by
    rw [Finset.sum_mul_sum Finset.univ Finset.univ
      (fun μ : Shape lam.card => diagramSchur μ.val t *
        jtChar μ.val (permCast μ.prop.symm π))
      (fun ν : Shape lam.card => diagramSchur ν.val t' *
        jtChar ν.val (permCast ν.prop.symm π))]]
  -- push the character of `L` inside and swap the summations
  rw [Finset.sum_congr rfl fun π _ => Finset.mul_sum
    (f := fun μ : Shape lam.card => ∑ ν : Shape lam.card,
      (diagramSchur μ.val t * jtChar μ.val (permCast μ.prop.symm π)) *
        (diagramSchur ν.val t' *
          jtChar ν.val (permCast ν.prop.symm π)))
    (a := jtChar L.val (permCast L.prop.symm π)) Finset.univ]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl
    fun π _ => Finset.mul_sum
      (f := fun ν : Shape lam.card =>
        (diagramSchur μ.val t *
          jtChar μ.val (permCast μ.prop.symm π)) *
          (diagramSchur ν.val t' *
            jtChar ν.val (permCast ν.prop.symm π)))
      (a := jtChar L.val (permCast L.prop.symm π)) Finset.univ]
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    (s := (Finset.univ : Finset (Equiv.Perm (Fin lam.card))))
    (t := (Finset.univ : Finset (Shape lam.card)))]
  -- identify each inner permutation sum as a Kronecker multiplicity
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [kronMult]
  rw [show (∑ π : Equiv.Perm (Fin lam.card),
      jtChar L.val (permCast L.prop.symm π) *
        ((diagramSchur μ.val t *
          jtChar μ.val (permCast μ.prop.symm π)) *
          (diagramSchur ν.val t' *
            jtChar ν.val (permCast ν.prop.symm π)))) =
      diagramSchur μ.val t * diagramSchur ν.val t' *
        ∑ π : Equiv.Perm (Fin lam.card),
          jtChar L.val (permCast L.prop.symm π) *
            jtChar μ.val (permCast μ.prop.symm π) *
            jtChar ν.val (permCast ν.prop.symm π) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun π _ => by ring]
  ring

end RS
