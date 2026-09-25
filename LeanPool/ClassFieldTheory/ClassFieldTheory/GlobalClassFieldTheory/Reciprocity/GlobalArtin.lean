/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CofinitelySplitFiniteExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
/-!
# The preliminary global Artin homomorphism

For a finite abelian extension `L / K`, the global norm-residue symbol
on ideles is the product of its archimedean and finite-place local
Artin factors.
-/

@[expose] public section

open scoped BigOperators IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

open scoped Classical in
/-- The preliminary global Artin homomorphism
`[·, L / K] : I_K → Gal(L / K)`, defined as the product of all local
Artin homomorphisms. -/
noncomputable def globalArtinMonoidHom :
    IdeleGroup K →* (L ≃ₐ[K] L) :=
  infinitePlaceGlobalArtinMonoidHom
      (K := K) (L := L) *
    finitePlaceGlobalArtinMonoidHom
      (K := K) (L := L)

open scoped Classical in
/-- The preliminary global Artin homomorphism is continuous. -/
theorem globalArtinMonoidHom_continuous :
    Continuous
      (globalArtinMonoidHom
        (K := K) (L := L)) :=
  (infinitePlaceGlobalArtinMonoidHom_continuous
    (K := K) (L := L)).mul
      (finitePlaceGlobalArtinMonoidHom_continuous
        (K := K) (L := L))

open scoped Classical in
/-- The preliminary global Artin symbol is the product of its actual
archimedean and finite local factors. -/
theorem globalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    globalArtinMonoidHom (K := K) (L := L) a =
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v a)) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v a) := by
  change
    infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) a *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) a = _
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  rfl

open scoped Classical in
/-- The preliminary global Artin homomorphism of `L / K` kills every
actual relative-idele norm from `L`.  At each finite and infinite place
this is exactly the corresponding local reciprocity kernel theorem. -/
@[simp]
theorem globalArtinMonoidHom_relativeIdeleNorm_eq_one
    (z : RelativeIdeleGroup K L) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (RelativeIdeleGroup.norm K L z) =
      1 := by
  rw [globalArtinMonoidHom_apply]
  have hnorm :
      RelativeIdeleGroup.norm K L z ∈
        (RelativeIdeleGroup.norm K L).range :=
    ⟨z, rfl⟩
  have hinfinite :
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (RelativeIdeleGroup.norm K L z))) =
        1 := by
    apply Finset.prod_eq_one
    intro v _
    apply MonoidHom.mem_ker.mp
    rw [chosenInfinitePlaceArtinMonoidHom_ker
      (K := K) (L := L) v]
    exact
      _root_.infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
          (K := K) (L := L)
          (RelativeIdeleGroup.norm K L z) hnorm v
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v
            (RelativeIdeleGroup.norm K L z))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    apply MonoidHom.mem_ker.mp
    rw [chosenFinitePlaceArtinMonoidHom_ker
      (K := K) (L := L) v]
    exact
      _root_.relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup
          (K := K) (L := L) v z
  rw [hinfinite, hfinite, mul_one]

open scoped Classical in
/-- The preliminary global Artin homomorphism kills the ordinary idele
norm `N_{L/K} : I_L → I_K`.  This is the relative-idele kernel theorem
above, transported by the canonical scalar-extension equivalence used in
the definition of `IdeleGroup.norm`. -/
@[simp]
theorem globalArtinMonoidHom_ideleNorm_eq_one
    (a : IdeleGroup L) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K L a) =
      1 := by
  change
    globalArtinMonoidHom
        (K := K) (L := L)
        (RelativeIdeleGroup.norm K L
          ((relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L)).symm a)) =
      1
  exact
    globalArtinMonoidHom_relativeIdeleNorm_eq_one
      (K := K) (L := L)
      ((relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).symm a)

open scoped Classical in
/-- The actual global Artin symbol after an ordinary idele norm, expanded
simultaneously at all archimedean and finite places.  The factors are
indexed by the genuine places upstairs, and use the ordinary LCFT field
norm on the corresponding completions. -/
theorem globalArtinMonoidHom_norm_eq_place_products
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    letI : ∀ W : InfinitePlace M,
        W.1.LiesOver
      (infinitePlaceBelow (K := K) W).1 :=
      fun _ => ⟨rfl⟩
    letI : ∀ W : HeightOneSpectrum (𝓞 M),
        Algebra
          ((finitePlaceBelow
            (K := K) W).adicCompletion K)
          (W.adicCompletion M) :=
      fun W =>
        (finitePlaceAdicCompletionMap
          K M
          (finitePlaceBelow (K := K) W)
          ⟨W, rfl⟩).toAlgebra
    globalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
      (∏ W : InfinitePlace M,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          (LocalFieldTheory.normUnits
            (infinitePlaceBelow
              (K := K) W).Completion
            W.Completion
            (IdeleGroup.infiniteComponent W a))) *
      ∏ᶠ W : HeightOneSpectrum (𝓞 M),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          (LocalFieldTheory.normUnits
            ((finitePlaceBelow
              (K := K) W).adicCompletion K)
            (W.adicCompletion M)
            (IdeleGroup.finiteComponent W a)) := by
  classical
  let : ∀ W : InfinitePlace M,
      W.1.LiesOver
        (infinitePlaceBelow (K := K) W).1 :=
    fun _ => ⟨rfl⟩
  let : ∀ W : HeightOneSpectrum (𝓞 M),
      Algebra
        ((finitePlaceBelow
          (K := K) W).adicCompletion K)
        (W.adicCompletion M) :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K M
        (finitePlaceBelow (K := K) W)
        ⟨W, rfl⟩).toAlgebra
  change
    infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) *
      finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) = _
  rw [infinitePlaceGlobalArtinMonoidHom_norm_eq_prod,
    finitePlaceGlobalArtinMonoidHom_norm_eq_finprod]

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- In an actual field diamond `K ⊂ K'`, `L ⊂ L'`, the standard
restriction map distributes over every local factor of the upper global
Artin symbol.  The vertical Galois map is exactly the composite supplied
by mathlib: first restrict scalars from `K'` to `K`, then restrict the
automorphism of `L'` to the normal subextension `L`. -/
theorem restrict_globalArtinMonoidHom_apply
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (a : IdeleGroup K') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (globalArtinMonoidHom
          (K := K') (L := L') a) =
      (∏ v : InfinitePlace K',
        ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K))
          (chosenInfinitePlaceArtinMonoidHom
            (K := K') (L := L') v
            (IdeleGroup.infiniteComponent v a))) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K'),
        ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K))
          (chosenFinitePlaceArtinMonoidHom
            (K := K') (L := L') v
            (IdeleGroup.finiteComponent v a)) := by
  rw [globalArtinMonoidHom_apply, map_mul, map_prod]
  rw [MonoidHom.map_finprod
    ((AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K))
    (finitePlaceArtinFactors_hasFiniteMulSupport
      (K := K') (L := L') a)]

open scoped Classical in
/-- Norm--restriction for the actual global Artin homomorphism.  In a number-field
diamond `K ⊂ K'`, `L ⊂ L'`, the ordinary idele norm and mathlib's standard
restriction composite form a commuting square. -/
theorem globalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalArtinMonoidHom
          (K := K') (L := L')) =
      (globalArtinMonoidHom
        (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  apply MonoidHom.ext
  intro a
  change
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (infinitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a *
          finitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a) =
      infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a) *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a)
  rw [map_mul]
  have hinfinite :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (infinitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a) =
        infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a) := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (infinitePlaceGlobalArtinMonoidHom_norm_restriction
          (K := K) (L := L))
        a
  have hfinite :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (finitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a) =
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a) := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (finitePlaceGlobalArtinMonoidHom_norm_restriction
          (K := K) (L := L))
        a
  rw [hinfinite, hfinite]

open scoped Classical in
/-- For an abelian tower with fixed base field, the global Artin map
commutes with the genuine restriction homomorphism. -/
theorem globalArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [NumberField E]
    [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [IsAbelianGalois K E] :
    (AlgEquiv.restrictNormalHom E).comp
        (globalArtinMonoidHom
          (K := K) (L := L)) =
      globalArtinMonoidHom
        (K := K) (L := E) := by
  apply MonoidHom.ext
  intro a
  change
    AlgEquiv.restrictNormalHom E
        (infinitePlaceGlobalArtinMonoidHom
            (K := K) (L := L) a *
          finitePlaceGlobalArtinMonoidHom
            (K := K) (L := L) a) =
      infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := E) a *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := E) a
  rw [map_mul]
  congr 1
  · simp only [infinitePlaceGlobalArtinMonoidHom,
      MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    exact DFunLike.congr_fun
      (chosenInfinitePlaceArtinMonoidHom_restrict_tower
        (K := K) (L := L) (E := E) v)
      (IdeleGroup.infiniteComponent v a)
  · change
      AlgEquiv.restrictNormalHom E
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (IdeleGroup.finiteComponent v a)) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          chosenFinitePlaceArtinMonoidHom
            (K := K) (L := E) v
            (IdeleGroup.finiteComponent v a)
    rw [MonoidHom.map_finprod
      (AlgEquiv.restrictNormalHom E)
      (finitePlaceArtinFactors_hasFiniteMulSupport
        (K := K) (L := L) a)]
    apply finprod_congr
    intro v
    exact DFunLike.congr_fun
      (chosenFinitePlaceArtinMonoidHom_restrict_tower
        (K := K) (L := L) (E := E) v)
      (IdeleGroup.finiteComponent v a)

open scoped Classical in
/-- The global Artin symbol of an archimedean one-place idele is its
local infinite-place Artin symbol. -/
@[simp]
theorem globalArtinMonoidHom_infinitePlaceIdele
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (infinitePlaceIdele v x) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x := by
  classical
  change
    infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x
  have hinfinite :
      infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v x := by
    unfold infinitePlaceGlobalArtinMonoidHom
    rw [MonoidHom.finsetProd_apply, Finset.prod_eq_single v]
    · rw [MonoidHom.comp_apply,
        infinitePlaceIdele_infiniteComponent_same]
    · intro w _ hwv
      rw [MonoidHom.comp_apply,
        infinitePlaceIdele_infiniteComponent_of_ne v w x hwv,
        map_one]
    · intro hv
      exact (hv (Finset.mem_univ v)).elim
  have hfinite :
      finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) =
        1 := by
    change
      (∏ᶠ w : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) w
          (IdeleGroup.finiteComponent w
            (infinitePlaceIdele v x))) = 1
    apply finprod_eq_one_of_forall_eq_one
    intro w
    rw [infinitePlaceIdele_finiteComponent, map_one]
  rw [hinfinite, hfinite, mul_one]

open scoped Classical in
/-- The global Artin symbol of a finite one-place idele is its local
finite-place Artin symbol. -/
@[simp]
theorem globalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x := by
  change
    infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (finitePlaceIdele v x) *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x
  rw [infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele,
    finitePlaceGlobalArtinMonoidHom_finitePlaceIdele, one_mul]

open scoped Classical in
/-- Every chosen finite-place decomposition group is contained in the
image of the global Artin homomorphism. -/
theorem finitePlaceDecompositionGroup_le_globalArtinMonoidHom_range
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePlaceDecompositionGroup
        (K := K) (L := L) v ≤
      (globalArtinMonoidHom
        (K := K) (L := L)).range := by
  rw [← chosenFinitePlaceArtinMonoidHom_range
    (K := K) (L := L) v]
  intro σ hσ
  rcases hσ with ⟨x, rfl⟩
  exact
    ⟨finitePlaceIdele v x,
      globalArtinMonoidHom_finitePlaceIdele
        (K := K) (L := L) v x⟩

open scoped Classical in
/-- The actual global Artin homomorphism of a finite abelian extension
of number fields is surjective. -/
theorem globalArtinMonoidHom_surjective :
    Function.Surjective
      (globalArtinMonoidHom
        (K := K) (L := L)) := by
  let H : Subgroup (L ≃ₐ[K] L) :=
    (globalArtinMonoidHom
      (K := K) (L := L)).range
  let : H.Normal :=
    H.normal_of_isMulCommutative
  let E : IntermediateField K L :=
    IntermediateField.fixedField H
  let : IsGalois K E := by
    dsimp only [E]
    infer_instance
  have hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K),
        FinitePlaceSplitsCompletely
          (K := K) (L := E) v := by
    intro v
    apply
      _root_.finitePlaceSplitsCompletely_of_decompositionGroup_le_restrictNormalHom_ker
          (K := K) (E := E) (N := L) v
    rw [IntermediateField.restrictNormalHom_ker]
    change
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤
        (IntermediateField.fixedField H).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField]
    simpa only [H] using
      finitePlaceDecompositionGroup_le_globalArtinMonoidHom_range
        (K := K) (L := L) v
  have hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := E) v}.Finite := by
    apply Set.finite_empty.subset
    intro v hv
    exact
      (hv
        ((_root_.finitePlaceSplitsCompletely_iff_inExtension
          (K := K) (E := E) v).mp
            (hsplit v))).elim
  have hdegree :
      Module.finrank K E = 1 :=
    Cohomology.finrank_eq_one_of_finite_nonSplittingPlaces
      K E hfinite
  have hEbot :
      E = (⊥ : IntermediateField K L) :=
    IntermediateField.finrank_eq_one_iff.mp hdegree
  have hHtop :
      H = (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    calc
      H =
          (IntermediateField.fixedField H).fixingSubgroup :=
        (IntermediateField.fixingSubgroup_fixedField H).symm
      _ = E.fixingSubgroup := rfl
      _ = (⊥ : IntermediateField K L).fixingSubgroup :=
        congrArg
          (fun F : IntermediateField K L =>
            F.fixingSubgroup)
          hEbot
      _ = ⊤ := by
        rw [IntermediateField.fixingSubgroup_bot]
  apply MonoidHom.range_eq_top.mp
  simpa only [H] using hHtop

end Reciprocity
end GlobalClassFieldTheory
