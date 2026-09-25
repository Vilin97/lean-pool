/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BiprodTransfer
import LeanPool.RegtsSevenster.RS.Classical.Deligne.KronKill
import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixedDiag

/-!
# The tensor-product transfer of Schur vanishing

Deligne 1.13, second half: if a Schur functor kills `X` and one
kills `Y`, a product-hook Schur functor kills `X ⊗ Y`.  The
distribution isomorphism carries the diagonal action on
`(X ⊗ Y)^⊗n` to the double action on `X^⊗n ⊗ Y^⊗n`, which extends
to the group algebra of `S_n × S_n`; there the diagonal image of
the central idempotent of `λ` meets the complete family of external
products of block idempotents, where every term dies — by the
Kronecker kill when the multiplicity vanishes, and through the
killed whiskered factor when it does not, since a nonzero
multiplicity pushes a bounding-box cell into `μ'` or `ν'`
(Deligne 1.12).
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u}

/-- **Left whiskering by a fixed object is an algebra map** on
endomorphisms, the mirror of `whiskerAlg`.  Multiplicativity is
functoriality of `◁` — note that `End` multiplies in the order
opposite to composition, which is why no reversal appears. -/
noncomputable def whiskerLeftAlg
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    (P X : A) :
    End X →ₐ[ℂ] End (P ⊗ X) where
  toFun f := P ◁ f
  map_one' := MonoidalCategory.whiskerLeft_id P X
  map_mul' f g := MonoidalCategory.whiskerLeft_comp P g f
  map_zero' := MonoidalPreadditive.whiskerLeft_zero
  map_add' f g := MonoidalPreadditive.whiskerLeft_add f g
  commutes' c := by
    change P ◁ (c • 𝟙 X) = c • 𝟙 (P ⊗ X)
    rw [MonoidalLinear.whiskerLeft_smul,
      MonoidalCategory.whiskerLeft_id]

/-- **The double action of a pair of permutations** on
`X ^ ⊗ n ⊗ Y ^ ⊗ n`, as a monoid homomorphism on the product
group: `(σ, τ)` acts by the two actions tensored together. -/
@[simps]
noncomputable def pairPermHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A]
    (X Y : A) (n : ℕ) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) →*
      End (tensorPow A X n ⊗ tensorPow A Y n) where
  toFun g := permMor X n g.1 ⊗ₘ permMor Y n g.2
  map_one' := by
    change permMor X n 1 ⊗ₘ permMor Y n 1 =
      𝟙 (tensorPow A X n ⊗ tensorPow A Y n)
    rw [permMor_one, permMor_one, MonoidalCategory.id_tensorHom_id]
  map_mul' g h := by
    change permMor X n (g.1 * h.1) ⊗ₘ permMor Y n (g.2 * h.2) =
      (permMor X n h.1 ⊗ₘ permMor Y n h.2) ≫
        (permMor X n g.1 ⊗ₘ permMor Y n g.2)
    rw [permMor_mul, permMor_mul,
      MonoidalCategory.tensorHom_comp_tensorHom]

/-- **The double action of the product group algebra** on
`X ^ ⊗ n ⊗ Y ^ ⊗ n`: the linear extension of
`(σ, τ) ↦ permMor X n σ ⊗ₘ permMor Y n τ`.  Since `End` multiplies
in the order opposite to composition, `pairAlg (a * b)` is
`pairAlg b ≫ pairAlg a` as a morphism. -/
noncomputable def pairAlg
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X Y : A) (n : ℕ) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) →ₐ[ℂ]
      End (tensorPow A X n ⊗ tensorPow A Y n) :=
  MonoidAlgebra.lift ℂ (End (tensorPow A X n ⊗ tensorPow A Y n))
    (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) (pairPermHom X Y n)

/-- The pair algebra map sends a pair of group elements to the
tensor product of their two actions. -/
@[simp]
theorem pairAlg_single
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X Y : A) (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) :
    pairAlg X Y n (MonoidAlgebra.single (σ, τ) (1 : ℂ)) =
      permMor X n σ ⊗ₘ permMor Y n τ := by
  rw [pairAlg, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- **The double action restricted to the diagonal** is the
diagonal double action: `pairAlg` extends `diagAlg` along
`diagEmbed`. -/
theorem pairAlg_diagEmbed
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X Y : A) (n : ℕ)
    (x : SymGroupAlgebra n) :
    pairAlg X Y n (diagEmbed x) = diagAlg X Y n x := by
  have hext : (pairAlg X Y n).comp diagEmbed = diagAlg X Y n := by
    refine MonoidAlgebra.algHom_ext (fun σ => ?_) (Subsingleton.elim _ _)
    change pairAlg X Y n (diagEmbed (MonoidAlgebra.single σ 1)) =
      diagAlg X Y n (MonoidAlgebra.single σ 1)
    have hd : diagEmbed (MonoidAlgebra.single σ (1 : ℂ)) =
        MonoidAlgebra.single
          ((σ, σ) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n))
          (1 : ℂ) := by
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single σ 1) = _
      exact MonoidAlgebra.mapDomain_single
    rw [hd, pairAlg_single, diagAlg_single]
  exact DFunLike.congr_fun hext x

/-- **The double action on the first external image** is the right
whiskering of the one-sided action: `pairAlg` extends
`permAlg X n · ▷ Y ^ ⊗ n` along the first-factor embedding. -/
theorem pairAlg_extFst
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (X Y : A) (n : ℕ) (x : SymGroupAlgebra n) :
    pairAlg X Y n
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x) =
      permAlg X n x ▷ tensorPow A Y n := by
  have hext : (pairAlg X Y n).comp
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n)) =
      (whiskerAlg (tensorPow A X n) (tensorPow A Y n)).comp
        (permAlg X n) := by
    refine MonoidAlgebra.algHom_ext (fun σ => ?_) (Subsingleton.elim _ _)
    change pairAlg X Y n (MonoidAlgebra.mapDomainAlgHom ℂ ℂ
        (extFstHom n) (MonoidAlgebra.single σ 1)) =
      whiskerAlg (tensorPow A X n) (tensorPow A Y n)
        (permAlg X n (MonoidAlgebra.single σ 1))
    have hf : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n)
        (MonoidAlgebra.single σ (1 : ℂ)) =
        MonoidAlgebra.single
          ((σ, 1) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n))
          (1 : ℂ) := by
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single σ 1) = _
      exact MonoidAlgebra.mapDomain_single
    rw [hf, pairAlg_single, permAlg_single, permMor_one,
      MonoidalCategory.tensorHom_id]
    rfl
  exact DFunLike.congr_fun hext x

/-- **The double action on the second external image** is the left
whiskering of the one-sided action: `pairAlg` extends
`X ^ ⊗ n ◁ permAlg Y n ·` along the second-factor embedding. -/
theorem pairAlg_extSnd
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (X Y : A) (n : ℕ) (y : SymGroupAlgebra n) :
    pairAlg X Y n
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y) =
      tensorPow A X n ◁ permAlg Y n y := by
  have hext : (pairAlg X Y n).comp
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n)) =
      (whiskerLeftAlg (tensorPow A X n) (tensorPow A Y n)).comp
        (permAlg Y n) := by
    refine MonoidAlgebra.algHom_ext (fun τ => ?_) (Subsingleton.elim _ _)
    change pairAlg X Y n (MonoidAlgebra.mapDomainAlgHom ℂ ℂ
        (extSndHom n) (MonoidAlgebra.single τ 1)) =
      whiskerLeftAlg (tensorPow A X n) (tensorPow A Y n)
        (permAlg Y n (MonoidAlgebra.single τ 1))
    have hs : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n)
        (MonoidAlgebra.single τ (1 : ℂ)) =
        MonoidAlgebra.single
          ((1, τ) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n))
          (1 : ℂ) := by
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single τ 1) = _
      exact MonoidAlgebra.mapDomain_single
    rw [hs, pairAlg_single, permAlg_single, permMor_one,
      MonoidalCategory.id_tensorHom]
    rfl
  exact DFunLike.congr_fun hext y

/-- **The double action on an external product**, as a morphism:
the left whiskering of the second factor's action followed by the
right whiskering of the first's.  This composite order is `End`'s
`pairAlg (extProd x y) = pairAlg (sndImage y) ≫ pairAlg
(fstImage x)`, the form the per-term kill composes with. -/
theorem pairAlg_extProd
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (X Y : A) (n : ℕ)
    (x y : SymGroupAlgebra n) :
    pairAlg X Y n (extProd x y) =
      (tensorPow A X n ◁ permAlg Y n y) ≫
        (permAlg X n x ▷ tensorPow A Y n) := by
  unfold extProd
  rw [map_mul, pairAlg_extFst, pairAlg_extSnd]
  rfl

/-- The external products of the recast block idempotents are a
complete family in the product group algebra. -/
theorem sum_extProd_shape_e (P : SchurPackage.{v}) (n : ℕ) :
    ∑ μ' : Shape n, ∑ ν' : Shape n,
      extProd (Shape.e P μ') (Shape.e P ν') =
      (1 : MonoidAlgebra ℂ
        (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))) := by
  classical
  calc ∑ μ' : Shape n, ∑ ν' : Shape n,
      extProd (Shape.e P μ') (Shape.e P ν')
      = (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n)
          (∑ μ' : Shape n, Shape.e P μ')) *
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n)
          (∑ ν' : Shape n, Shape.e P ν')) := by
        rw [map_sum, map_sum, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun μ' _ =>
          Finset.sum_congr rfl fun ν' _ => rfl
    _ = 1 := by
        rw [P.sum_shape_e_eq_one, map_one, map_one, one_mul]

/-- **The tensor-product transfer** (Deligne 1.13, ⊗ half): Schur
vanishing for `X` at `μ` and `Y` at `ν` forces Schur vanishing for
`X ⊗ Y` at every diagram containing the product-hook cell of the
two bounding boxes. -/
theorem SchurKilled.tensorObj
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) {X Y : A}
    {μ ν lam : YoungDiagram} {p q r s : ℕ}
    (hμc : μ.colLen 0 ≤ p + 1) (hμr : μ.rowLen 0 ≤ q + 1)
    (hνc : ν.colLen 0 ≤ r + 1) (hνr : ν.rowLen 0 ≤ s + 1)
    (hX : SchurKilled P X μ) (hY : SchurKilled P Y ν)
    (hcell : (p * r + q * s, p * s + q * r) ∈ lam) :
    SchurKilled P (X ⊗ Y) lam := by
  classical
  rw [SchurKilled]
  -- The recast idempotent at size `lam.card` is the idempotent.
  have heS : Shape.e P (⟨lam, rfl⟩ : Shape lam.card) = P.e lam := by
    unfold Shape.e
    erw [symCast_le_refl]
  -- Each external term of the double action dies.
  have hterm : ∀ μ' ν' : Shape lam.card,
      (pairAlg X Y lam.card
          (extProd (Shape.e P μ') (Shape.e P ν') *
            diagEmbed (P.e lam)) :
        tensorPow A X lam.card ⊗ tensorPow A Y lam.card ⟶
          tensorPow A X lam.card ⊗ tensorPow A Y lam.card) =
      0 := by
    intro μ' ν'
    by_cases hk : kronMult (⟨lam, rfl⟩ : Shape lam.card) μ' ν' = 0
    · -- The Kronecker kill.
      have hz0 : extProd (Shape.e P μ') (Shape.e P ν') *
          diagEmbed (P.e lam) = 0 := by
        rw [show P.e lam =
            Shape.e P (⟨lam, rfl⟩ : Shape lam.card) from heS.symm]
        exact extProd_mul_diagEmbed_eq_zero P ⟨lam, rfl⟩ μ' ν' hk
      rw [hz0]
      exact map_zero _
    · -- A bounding-box cell lands in `μ'` or `ν'`; that factor is
      -- killed and its whiskering propagates the zero.
      have hcell' := cell_of_kronMult_ne_zero
        (⟨lam, rfl⟩ : Shape lam.card) μ' ν'
        (p := p) (q := q) (r := r) (s := s) hk hcell
      have hsplit : pairAlg X Y lam.card
          (extProd (Shape.e P μ') (Shape.e P ν') *
            diagEmbed (P.e lam)) =
          pairAlg X Y lam.card (diagEmbed (P.e lam)) ≫
            pairAlg X Y lam.card
              (extProd (Shape.e P μ') (Shape.e P ν')) := by
        rw [map_mul]
        rfl
      rw [hsplit, pairAlg_extProd]
      rcases hcell' with hcμ | hcν
      · have hkilled : SchurKilled P X μ'.val :=
          hX.mono P (le_of_box_of_cell hμc hμr hcμ)
        have hz : permAlg X lam.card (Shape.e P μ') =
            (0 : tensorPow A X lam.card ⟶
              tensorPow A X lam.card) := by
          rw [Shape.e]
          exact permAlg_compat X _ _ hkilled
        rw [hz, MonoidalPreadditive.zero_whiskerRight,
          Limits.comp_zero, Limits.comp_zero]
      · have hkilled : SchurKilled P Y ν'.val :=
          hY.mono P (le_of_box_of_cell hνc hνr hcν)
        have hz : permAlg Y lam.card (Shape.e P ν') =
            (0 : tensorPow A Y lam.card ⟶
              tensorPow A Y lam.card) := by
          rw [Shape.e]
          exact permAlg_compat Y _ _ hkilled
        rw [hz, MonoidalPreadditive.whiskerLeft_zero,
          Limits.zero_comp, Limits.comp_zero]
  -- The diagonal double action of the idempotent vanishes: expand
  -- the diagonal image over the complete external family.
  have hdiag : (diagAlg X Y lam.card (P.e lam) :
      tensorPow A X lam.card ⊗ tensorPow A Y lam.card ⟶
        tensorPow A X lam.card ⊗ tensorPow A Y lam.card) = 0 := by
    rw [← pairAlg_diagEmbed]
    have hexp : diagEmbed (P.e lam) =
        ∑ μ' : Shape lam.card, ∑ ν' : Shape lam.card,
          extProd (Shape.e P μ') (Shape.e P ν') *
            diagEmbed (P.e lam) := by
      conv_lhs => rw [show diagEmbed (P.e lam) =
          1 * diagEmbed (P.e lam) from (one_mul _).symm,
        ← sum_extProd_shape_e P lam.card]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun μ' _ => Finset.sum_mul _ _ _
    have hdist : (pairAlg X Y lam.card (diagEmbed (P.e lam)) :
        tensorPow A X lam.card ⊗ tensorPow A Y lam.card ⟶
          tensorPow A X lam.card ⊗ tensorPow A Y lam.card) =
        ∑ μ' : Shape lam.card, ∑ ν' : Shape lam.card,
          pairAlg X Y lam.card
            (extProd (Shape.e P μ') (Shape.e P ν') *
              diagEmbed (P.e lam)) := by
      conv_lhs => rw [hexp]
      rw [map_sum]
      exact Finset.sum_congr rfl fun μ' _ => map_sum _ _ _
    rw [hdist]
    refine Finset.sum_eq_zero fun μ' _ => ?_
    refine Finset.sum_eq_zero fun ν' _ => ?_
    exact hterm μ' ν'
  -- Transport back through the distribution isomorphism.
  have hcomp : permAlg (X ⊗ Y) lam.card (P.e lam) ≫
      (tensorPowDistrib X Y lam.card).hom = 0 := by
    rw [tensorPowDistrib_permAlg, hdiag]
    exact Limits.comp_zero
  calc permAlg (X ⊗ Y) lam.card (P.e lam)
      = (permAlg (X ⊗ Y) lam.card (P.e lam) ≫
          (tensorPowDistrib X Y lam.card).hom) ≫
          (tensorPowDistrib X Y lam.card).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = 0 := by rw [hcomp, Limits.zero_comp]

end RS
