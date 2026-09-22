/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BiprodPow
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndKill
import LeanPool.RegtsSevenster.RS.Classical.Deligne.HookMult

/-!
# The direct-sum transfer of Schur vanishing

Deligne 1.13, first half: if a Schur functor kills `X` and one
kills `Y`, a fat-hook Schur functor kills `X ⊞ Y`.  The identity
of `(X ⊞ Y)^⊗n` expands over mixed words; each mixed inclusion
sorts to the standard block inclusion; the central idempotent of
`λ` then meets the complete family of embedded block idempotents,
where every term dies — by the induction kill when the multiplicity
vanishes, and through the killed factor and naturality when it does
not, since a nonzero multiplicity pushes a bounding-box cell into
`μ'` or `ν'` (Deligne 1.10).
-/

namespace RS

open CategoryTheory MonoidalCategory Limits Finset

universe v u

variable {A : Type u}

/-- Transport of the group-algebra action along an arity
equality. -/
theorem permAlg_eqToHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (Z : A) {m n : ℕ} (h : m = n)
    (x : SymGroupAlgebra n) :
    eqToHom (congrArg (tensorPow A Z) h) ≫ permAlg Z n x =
      permAlg Z m (symCast (le_of_eq h.symm) x) ≫
        eqToHom (congrArg (tensorPow A Z) h) := by
  subst h
  rw [symCast_le_refl]
  simp

/-- The embedded block idempotents are a complete family. -/
theorem sum_blockAlgEmbed_shape_e (P : SchurPackage.{v})
    (a b : ℕ) :
    ∑ μ' : Shape a, ∑ ν' : Shape b,
      blockAlgEmbed (Shape.e P μ') (Shape.e P ν') =
      (1 : SymGroupAlgebra (a + b)) := by
  classical
  calc ∑ μ' : Shape a, ∑ ν' : Shape b,
      blockAlgEmbed (Shape.e P μ') (Shape.e P ν')
      = (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b)
          (∑ μ' : Shape a, Shape.e P μ')) *
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b)
          (∑ ν' : Shape b, Shape.e P ν')) := by
        rw [map_sum, map_sum, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun μ' _ =>
          Finset.sum_congr rfl fun ν' _ => rfl
    _ = 1 := by
        rw [P.sum_shape_e_eq_one, P.sum_shape_e_eq_one,
          map_one, map_one, one_mul]

/-- A diagram inside the `(p+1) × (q+1)` bounding box is contained
in any diagram holding the cell `(p, q)`. -/
theorem le_of_box_of_cell {μ μ' : YoungDiagram} {p q : ℕ}
    (hc : μ.colLen 0 ≤ p + 1) (hr : μ.rowLen 0 ≤ q + 1)
    (hcell : (p, q) ∈ μ') : μ ≤ μ' := by
  intro c hcmem
  obtain ⟨i, j⟩ := c
  have hi : i < μ.colLen 0 := by
    rw [← YoungDiagram.mem_iff_lt_colLen]
    exact μ.up_left_mem le_rfl (Nat.zero_le _) hcmem
  have hj : j < μ.rowLen 0 := by
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    exact μ.up_left_mem (Nat.zero_le _) le_rfl hcmem
  exact μ'.up_left_mem (by omega) (by omega) hcell

/-- A central element commutes with every permutation action. -/
theorem permMor_comp_permAlg
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (Z : A) {n : ℕ}
    (g : Equiv.Perm (Fin n)) {x : SymGroupAlgebra n}
    (hcen : ∀ y, x * y = y * x) :
    permMor Z n g ≫ permAlg Z n x =
      permAlg Z n x ≫ permMor Z n g := by
  have h1 : permMor Z n g ≫ permAlg Z n x =
      permAlg Z n (x * MonoidAlgebra.single g 1) := by
    rw [map_mul, permAlg_single]
    rfl
  have h2 : permAlg Z n x ≫ permMor Z n g =
      permAlg Z n (MonoidAlgebra.single g 1 * x) := by
    rw [map_mul, permAlg_single]
    rfl
  rw [h1, h2, hcen]

/-- **The direct-sum transfer** (Deligne 1.13, ⊕ half): Schur
vanishing for `X` at `μ` and `Y` at `ν` forces Schur vanishing for
`X ⊞ Y` at every diagram containing the fat-hook cell of the two
bounding boxes. -/
theorem SchurKilled.biprod
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v}) {X Y : A}
    {μ ν lam : YoungDiagram} {p q r s : ℕ}
    (hμc : μ.colLen 0 ≤ p + 1) (hμr : μ.rowLen 0 ≤ q + 1)
    (hνc : ν.colLen 0 ≤ r + 1) (hνr : ν.rowLen 0 ≤ s + 1)
    (hX : SchurKilled P X μ) (hY : SchurKilled P Y ν)
    (hcell : (p + r, q + s) ∈ lam) :
    SchurKilled P (X ⊞ Y) lam := by
  classical
  rw [SchurKilled]
  set n := lam.card with hn
  -- Expand the identity over mixed words.
  have hexp : permAlg (X ⊞ Y) n (P.e lam) =
      ∑ w : Fin n → Bool, mixedFrom X Y n w ≫
        (mixedInto X Y n w ≫ permAlg (X ⊞ Y) n (P.e lam)) := by
    conv_lhs => rw [show permAlg (X ⊞ Y) n (P.e lam) =
      𝟙 (tensorPow A (X ⊞ Y) n) ≫ permAlg (X ⊞ Y) n (P.e lam) from
        (Category.id_comp _).symm]
    rw [← sum_mixedFrom_mixedInto, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun w _ => Category.assoc _ _ _
  rw [hexp]
  refine Finset.sum_eq_zero fun w _ => ?_
  suffices hzero : mixedInto X Y n w ≫
      permAlg (X ⊞ Y) n (P.e lam) = 0 by
    rw [hzero]
    exact Limits.comp_zero
  -- Sort the inclusion to the standard block.
  set a := popCount w with ha
  set b := n - popCount w with hb
  have hab : a + b = n := Nat.add_sub_cancel' (popCount_le w)
  have hsorted := sortIso_spec X Y n w
  -- `mixedInto ≫ permMor (sortPerm w)` is the standard inclusion.
  -- Post-compose the goal with the invertible sorting action.
  have hperm : permMor (X ⊞ Y) n (sortPerm w) ≫
      permMor (X ⊞ Y) n (sortPerm w)⁻¹ = 𝟙 _ := by
    rw [show permMor (X ⊞ Y) n (sortPerm w) ≫
        permMor (X ⊞ Y) n (sortPerm w)⁻¹ =
      permAlg (X ⊞ Y) n (MonoidAlgebra.single ((sortPerm w)⁻¹ *
        sortPerm w) 1) from by
      rw [show MonoidAlgebra.single ((sortPerm w)⁻¹ *
          sortPerm w) (1 : ℂ) =
        MonoidAlgebra.single (sortPerm w)⁻¹ 1 *
          MonoidAlgebra.single (sortPerm w) 1 from by
        rw [MonoidAlgebra.single_mul_single, one_mul],
        map_mul, permAlg_single, permAlg_single]
      rfl]
    rw [inv_mul_cancel]
    rw [show MonoidAlgebra.single (1 : Equiv.Perm (Fin n))
      (1 : ℂ) = 1 from rfl, map_one]
    rfl
  have hcen : ∀ y, P.e lam * y = y * P.e lam := fun y => by
    have := shape_e_central P (⟨lam, rfl⟩ : Shape lam.card) y
    rwa [show Shape.e P (⟨lam, rfl⟩ : Shape lam.card) =
      P.e lam from by
        unfold Shape.e
        erw [symCast_le_refl]] at this
  have hfactor : mixedInto X Y n w ≫ permAlg (X ⊞ Y) n (P.e lam) =
      (sortIso X Y n w).hom ≫
        ((tensorPowMap biprod.inl a ⊗ₘ tensorPowMap biprod.inr b) ≫
          (tensorPowConcat (X ⊞ Y) a b).hom ≫
          eqToHom (congrArg (tensorPow A (X ⊞ Y)) hab) ≫
          permAlg (X ⊞ Y) n (P.e lam)) ≫
        permMor (X ⊞ Y) n (sortPerm w)⁻¹ := by
    have h1 : mixedInto X Y n w =
        ((sortIso X Y n w).hom ≫
          ((tensorPowMap biprod.inl a ⊗ₘ
              tensorPowMap biprod.inr b) ≫
            (tensorPowConcat (X ⊞ Y) a b).hom ≫
            eqToHom (congrArg (tensorPow A (X ⊞ Y)) hab))) ≫
          permMor (X ⊞ Y) n (sortPerm w)⁻¹ := by
      rw [← hsorted]
      rw [Category.assoc, hperm, Category.comp_id]
    rw [h1]
    rw [Category.assoc]
    rw [show permMor (X ⊞ Y) n (sortPerm w)⁻¹ ≫
        permAlg (X ⊞ Y) n (P.e lam) =
      permAlg (X ⊞ Y) n (P.e lam) ≫ permMor (X ⊞ Y) n (sortPerm w)⁻¹ from
      permMor_comp_permAlg (X ⊞ Y) _ hcen]
    simp only [Category.assoc]
  rw [hfactor]
  suffices hcore :
      (tensorPowMap biprod.inl a ⊗ₘ tensorPowMap biprod.inr b) ≫
        (tensorPowConcat (X ⊞ Y) a b).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hab) ≫
        permAlg (X ⊞ Y) n (P.e lam) = 0 by
    rw [show (tensorPowMap biprod.inl a ⊗ₘ
        tensorPowMap biprod.inr b) ≫
        (tensorPowConcat (X ⊞ Y) a b).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hab) ≫
        permAlg (X ⊞ Y) n (P.e lam) = 0 from hcore]
    rw [Limits.zero_comp, Limits.comp_zero]
  -- Transport the idempotent to the split arity.
  rw [permAlg_eqToHom (X ⊞ Y) hab]
  set eS : SymGroupAlgebra (a + b) :=
    symCast (le_of_eq hab.symm) (P.e lam) with heS
  have heSshape : eS = Shape.e P (⟨lam, hab.symm⟩ :
      Shape (a + b)) := rfl
  -- Each embedded block term dies.
  have hterm : ∀ (μ' : Shape a) (ν' : Shape b),
      (tensorPowMap biprod.inl a ⊗ₘ tensorPowMap biprod.inr b) ≫
        (tensorPowConcat (X ⊞ Y) a b).hom ≫
        permAlg (X ⊞ Y) (a + b)
          (eS * blockAlgEmbed (Shape.e P μ') (Shape.e P ν')) =
      0 := by
    intro μ' ν'
    by_cases hind : indMult (⟨lam, hab.symm⟩ : Shape (a + b))
      μ' ν' = 0
    · -- The induction kill.
      have hz0 : permAlg (X ⊞ Y) (a + b)
          (eS * blockAlgEmbed (Shape.e P μ') (Shape.e P ν')) =
          (0 : tensorPow A (X ⊞ Y) (a + b) ⟶
            tensorPow A (X ⊞ Y) (a + b)) := by
        rw [show eS * blockAlgEmbed (Shape.e P μ') (Shape.e P ν') =
          0 from by
            rw [heSshape]
            exact shape_e_mul_blockAlgEmbed_eq_zero P _ μ' ν' hind]
        exact map_zero _
      rw [hz0, Limits.comp_zero, Limits.comp_zero]
    · -- A bounding-box cell lands in `μ'` or `ν'`; that factor
      -- is killed and naturality propagates the zero.
      have hcell' := cell_of_indMult_ne_zero
        (⟨lam, hab.symm⟩ : Shape (a + b)) μ' ν'
        (p := p) (q := q) (r := r) (s := s) hind hcell
      have hsplit : permAlg (X ⊞ Y) (a + b)
          (eS * blockAlgEmbed (Shape.e P μ') (Shape.e P ν')) =
          permAlg (X ⊞ Y) (a + b)
            (blockAlgEmbed (Shape.e P μ') (Shape.e P ν')) ≫
          permAlg (X ⊞ Y) (a + b) eS := by
        rw [map_mul]
        rfl
      rw [hsplit]
      rw [show (tensorPowConcat (X ⊞ Y) a b).hom ≫
          permAlg (X ⊞ Y) (a + b)
            (blockAlgEmbed (Shape.e P μ') (Shape.e P ν')) ≫
          permAlg (X ⊞ Y) (a + b) eS =
        ((permAlg (X ⊞ Y) a (Shape.e P μ') ⊗ₘ
            permAlg (X ⊞ Y) b (Shape.e P ν')) ≫
          (tensorPowConcat (X ⊞ Y) a b).hom) ≫
          permAlg (X ⊞ Y) (a + b) eS from by
        rw [← Category.assoc, tensorPowConcat_permAlg]]
      rw [show (tensorPowMap biprod.inl a ⊗ₘ
          tensorPowMap biprod.inr b) ≫
          ((permAlg (X ⊞ Y) a (Shape.e P μ') ⊗ₘ
              permAlg (X ⊞ Y) b (Shape.e P ν')) ≫
            (tensorPowConcat (X ⊞ Y) a b).hom) ≫
          permAlg (X ⊞ Y) (a + b) eS =
        ((tensorPowMap biprod.inl a ≫ permAlg (X ⊞ Y) a (Shape.e P μ')) ⊗ₘ
          (tensorPowMap biprod.inr b ≫
            permAlg (X ⊞ Y) b (Shape.e P ν'))) ≫
          (tensorPowConcat (X ⊞ Y) a b).hom ≫
          permAlg (X ⊞ Y) (a + b) eS from by
        rw [← Category.assoc, ← Category.assoc,
          tensorHom_comp_tensorHom]
        simp only [Category.assoc]]
      rcases hcell' with hcμ | hcν
      · have hkilled : SchurKilled P X μ'.val :=
          hX.mono P (le_of_box_of_cell hμc hμr hcμ)
        have hz : permAlg X a (Shape.e P μ') =
            (0 : tensorPow A X a ⟶ tensorPow A X a) := by
          rw [Shape.e]
          exact permAlg_compat X _ _ hkilled
        rw [show tensorPowMap biprod.inl a ≫
            permAlg (X ⊞ Y) a (Shape.e P μ') =
          permAlg X a (Shape.e P μ') ≫
            tensorPowMap biprod.inl a from
          (permAlg_natural biprod.inl a _).symm, hz,
          Limits.zero_comp]
        rw [show ((0 : tensorPow A X a ⟶ tensorPow A (X ⊞ Y) a) ⊗ₘ
            (tensorPowMap biprod.inr b ≫
              permAlg (X ⊞ Y) b (Shape.e P ν'))) =
          0 from by
          rw [tensorHom_def, MonoidalPreadditive.zero_whiskerRight,
            Limits.zero_comp]]
        rw [Limits.zero_comp]
      · have hkilled : SchurKilled P Y ν'.val :=
          hY.mono P (le_of_box_of_cell hνc hνr hcν)
        have hz : permAlg Y b (Shape.e P ν') =
            (0 : tensorPow A Y b ⟶ tensorPow A Y b) := by
          rw [Shape.e]
          exact permAlg_compat Y _ _ hkilled
        rw [show tensorPowMap biprod.inr b ≫
            permAlg (X ⊞ Y) b (Shape.e P ν') =
          permAlg Y b (Shape.e P ν') ≫
            tensorPowMap biprod.inr b from
          (permAlg_natural biprod.inr b _).symm, hz,
          Limits.zero_comp]
        rw [show ((tensorPowMap biprod.inl a ≫
              permAlg (X ⊞ Y) a (Shape.e P μ')) ⊗ₘ
            (0 : tensorPow A Y b ⟶ tensorPow A (X ⊞ Y) b)) =
          0 from by
          rw [tensorHom_def, MonoidalPreadditive.whiskerLeft_zero,
            Limits.comp_zero]]
        rw [Limits.zero_comp]
  -- Assemble: the complete family expands the idempotent.
  have hone : eS = ∑ μ' : Shape a, ∑ ν' : Shape b,
      eS * blockAlgEmbed (Shape.e P μ') (Shape.e P ν') := by
    conv_lhs => rw [show eS = eS * 1 from (mul_one eS).symm,
      ← sum_blockAlgEmbed_shape_e P a b]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ' _ => Finset.mul_sum _ _ _
  set F : Shape a → Shape b →
      (tensorPow A (X ⊞ Y) (a + b) ⟶
        tensorPow A (X ⊞ Y) (a + b)) :=
    fun μ' ν' => permAlg (X ⊞ Y) (a + b)
      (eS * blockAlgEmbed (Shape.e P μ') (Shape.e P ν')) with hF
  have hdist : (permAlg (X ⊞ Y) (a + b) eS :
      tensorPow A (X ⊞ Y) (a + b) ⟶
        tensorPow A (X ⊞ Y) (a + b)) =
      ∑ μ' : Shape a, ∑ ν' : Shape b, F μ' ν' := by
    conv_lhs => rw [hone]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ' _ => map_sum _ _ _
  rw [hdist]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun μ' _ => ?_
  refine Finset.sum_eq_zero fun ν' _ => ?_
  calc (tensorPowMap biprod.inl a ⊗ₘ tensorPowMap biprod.inr b) ≫
      (tensorPowConcat (X ⊞ Y) a b).hom ≫ F μ' ν' ≫
      eqToHom (congrArg (tensorPow A (X ⊞ Y)) hab)
      = ((tensorPowMap biprod.inl a ⊗ₘ tensorPowMap biprod.inr b) ≫
        (tensorPowConcat (X ⊞ Y) a b).hom ≫
        permAlg (X ⊞ Y) (a + b)
          (eS * blockAlgEmbed (Shape.e P μ') (Shape.e P ν'))) ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hab) := by
        simp only [Category.assoc]
        rfl
    _ = 0 ≫ eqToHom (congrArg (tensorPow A (X ⊞ Y)) hab) := by
        rw [hterm μ' ν']
    _ = 0 := Limits.zero_comp

end RS
