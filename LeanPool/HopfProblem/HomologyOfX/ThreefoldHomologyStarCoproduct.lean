/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.MainTheorem.SixSphereCube1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube1

/-!
# Hopf problem: homology of x · threefold homology star coproduct

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts :
    CategoryTheory.Limits.HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.sigmaInclusion {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (i : ι) : C(X i, Σ i, X i) :=
  ⟨Sigma.mk i, continuous_sigmaMk⟩

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.singularSimplex_sigma_split {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) (σ : FirstHurewicz.SingularSimplex (Σ i, X i) n) :
    ∃ (i : ι) (τ : FirstHurewicz.SingularSimplex (X i) n), σ = (sigmaInclusion X i).comp τ := by
  obtain ⟨i, g, hg, heq⟩ := σ.continuous.exists_lift_sigma
  exact ⟨i, ⟨g, hg⟩, ContinuousMap.ext (congrFun heq)⟩

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.sigmaSimplexMap {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) :
    (Σ i, FirstHurewicz.SingularSimplex (X i) n) → FirstHurewicz.SingularSimplex (Σ i, X i) n :=
  fun σ => (sigmaInclusion X σ.1).comp σ.2

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.sigmaSimplexMap_injective {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) : Function.Injective (sigmaSimplexMap X n) := by
  classical
  let z : stdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  rintro ⟨i, σ⟩ ⟨j, τ⟩ h
  have hij : i = j := congrArg (fun f => (f z).1) h
  subst j
  congr 1
  exact ContinuousMap.ext fun t => sigma_mk_injective (congrArg (fun f => f t) h)

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.sigmaSimplexMap_surjective {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) : Function.Surjective (sigmaSimplexMap X n) := by
  intro σ
  obtain ⟨i, τ, hτ⟩ := singularSimplex_sigma_split X n σ
  exact ⟨⟨i, τ⟩, hτ.symm⟩

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.sigmaSimplexEquiv {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) :
    (Σ i, FirstHurewicz.SingularSimplex (X i) n) ≃ FirstHurewicz.SingularSimplex (Σ i, X i) n :=
  Equiv.ofBijective (sigmaSimplexMap X n)
    ⟨sigmaSimplexMap_injective X n, sigmaSimplexMap_surjective X n⟩

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
@[simp]
private theorem
    ThreefoldHomologyStarCoproduct.sigmaSimplexEquiv_symm_inclusion {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) (i : ι) (σ : FirstHurewicz.SingularSimplex (X i) n) :
    (sigmaSimplexEquiv X n).symm ((sigmaInclusion X i).comp σ) = ⟨i, σ⟩ :=
  (sigmaSimplexEquiv X n).symm_apply_apply ⟨i, σ⟩

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.sigmaChains_hom_ext {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) {M : ModuleCat ℤ}
    (f g : FirstHurewicz.Chains (Σ i, X i) n ⟶ M)
    (h :
      ∀ i,
        (FirstHurewicz.singularChainMap (sigmaInclusion X i)).f n ≫ f =
          (FirstHurewicz.singularChainMap (sigmaInclusion X i)).f n ≫ g) :
    f = g := by
  apply ModuleCat.hom_ext
  apply FirstHurewicz.chainMap_ext (Σ i, X i) n
  intro σ
  obtain ⟨i, τ, rfl⟩ := singularSimplex_sigma_split X n σ
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, FirstHurewicz.inducedChain_simplex] using
    congrArg (fun k => k.hom (FirstHurewicz.simplexChain (X i) n τ)) (h i)

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.sigmaChainComplexMap {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    (⨁ fun i => FirstHurewicz.singularComplex (X i)) ⟶ FirstHurewicz.singularComplex (Σ i, X i) :=
  CategoryTheory.Limits.biproduct.desc fun i =>
    FirstHurewicz.singularChainMap (sigmaInclusion X i)

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
@[simp]
private theorem
    ThreefoldHomologyStarCoproduct.sigmaChainComplexMap_inclusion {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] (i : ι) :
    CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) i ≫
        sigmaChainComplexMap X =
      FirstHurewicz.singularChainMap (sigmaInclusion X i) :=
  CategoryTheory.Limits.biproduct.ι_desc _ i

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.sigmaChainInverseDegree_mo1973_5500 {ι : Type}
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (n : ℕ) :
    FirstHurewicz.Chains (Σ i, X i) n →ₗ[ℤ]
      (⨁ fun i => FirstHurewicz.singularComplex (X i)).X n :=
  FirstHurewicz.chainLift (Σ i, X i) n fun σ =>
    let τ := (sigmaSimplexEquiv X n).symm σ
    ((CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) τ.1).f
          n).hom
      (FirstHurewicz.simplexChain (X τ.1) n τ.2)

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.sigmaChainInverseDegree_inclusion_mo1973_5501
    {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (n : ℕ) (i : ι)
    (σ : FirstHurewicz.SingularSimplex (X i) n) :
    sigmaChainInverseDegree_mo1973_5500 X n
        (FirstHurewicz.simplexChain (Σ i, X i) n ((sigmaInclusion X i).comp σ)) =
      ((CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) i).f
            n).hom
        (FirstHurewicz.simplexChain (X i) n σ) := by
  simpa only [sigmaChainInverseDegree_mo1973_5500, FirstHurewicz.chainLift_simplex] using
    congrArg
      (fun τ : Σ i, FirstHurewicz.SingularSimplex (X i) n =>
        ((CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) τ.1).f
              n).hom
          (FirstHurewicz.simplexChain (X τ.1) n τ.2))
      (sigmaSimplexEquiv_symm_inclusion X n i σ)

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.sigmaChainInverseDegree_comp_inclusion_mo1973_5502
    {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (n : ℕ) (i : ι) :
    (FirstHurewicz.singularChainMap (sigmaInclusion X i)).f n ≫
        ModuleCat.ofHom (sigmaChainInverseDegree_mo1973_5500 X n) =
      (CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) i).f n := by
  apply ModuleCat.hom_ext
  apply FirstHurewicz.chainMap_ext (X i) n
  intro σ
  change
    sigmaChainInverseDegree_mo1973_5500 X n
        (FirstHurewicz.inducedChain (sigmaInclusion X i) n
          (FirstHurewicz.simplexChain (X i) n σ)) =
      _
  rw [FirstHurewicz.inducedChain_simplex, sigmaChainInverseDegree_inclusion_mo1973_5501]

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.sigmaChainComplexInverse {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    FirstHurewicz.singularComplex (Σ i, X i) ⟶ (⨁ fun i => FirstHurewicz.singularComplex (X i))
    where
  f n := ModuleCat.ofHom (sigmaChainInverseDegree_mo1973_5500 X n)
  comm' n m
    _ := by
    apply sigmaChains_hom_ext X n
    intro i
    calc
      _ =
          ((FirstHurewicz.singularChainMap (sigmaInclusion X i)).f n ≫
              ModuleCat.ofHom (sigmaChainInverseDegree_mo1973_5500 X n)) ≫
            (⨁ fun i => FirstHurewicz.singularComplex (X i)).d n m :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          (CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) i).f
              n ≫
            (⨁ fun i => FirstHurewicz.singularComplex (X i)).d n m :=
        (congrArg
          (fun f :
              FirstHurewicz.Chains (X i) n ⟶
                (⨁ fun i => FirstHurewicz.singularComplex (X i)).X n =>
            f ≫ (⨁ fun i => FirstHurewicz.singularComplex (X i)).d n m)
          (sigmaChainInverseDegree_comp_inclusion_mo1973_5502 X n i))
      _ =
          (FirstHurewicz.singularComplex (X i)).d n m ≫
            (CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) i).f
              m :=
        ((CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) i).comm
          n m)
      _ =
          (FirstHurewicz.singularComplex (X i)).d n m ≫
            ((FirstHurewicz.singularChainMap (sigmaInclusion X i)).f m ≫
              ModuleCat.ofHom (sigmaChainInverseDegree_mo1973_5500 X m)) :=
        (congrArg
            (fun f :
                FirstHurewicz.Chains (X i) m ⟶
                  (⨁ fun i => FirstHurewicz.singularComplex (X i)).X m =>
              (FirstHurewicz.singularComplex (X i)).d n m ≫ f)
            (sigmaChainInverseDegree_comp_inclusion_mo1973_5502 X m i)).symm
      _ =
          ((FirstHurewicz.singularComplex (X i)).d n m ≫
              (FirstHurewicz.singularChainMap (sigmaInclusion X i)).f m) ≫
            ModuleCat.ofHom (sigmaChainInverseDegree_mo1973_5500 X m) :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          ((FirstHurewicz.singularChainMap (sigmaInclusion X i)).f n ≫
              (FirstHurewicz.singularComplex (Σ i, X i)).d n m) ≫
            ModuleCat.ofHom (sigmaChainInverseDegree_mo1973_5500 X m) :=
        (congrArg
          (fun f : FirstHurewicz.Chains (X i) n ⟶ FirstHurewicz.Chains (Σ i, X i) m =>
            f ≫ ModuleCat.ofHom (sigmaChainInverseDegree_mo1973_5500 X m))
          ((FirstHurewicz.singularChainMap (sigmaInclusion X i)).comm n m).symm)
      _ = _ := CategoryTheory.Category.assoc _ _ _

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
@[simp]
private theorem ThreefoldHomologyStarCoproduct.sigmaChainComplexInverse_inclusion {ι : Type}
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] [Fintype ι] (i : ι) :
    FirstHurewicz.singularChainMap (sigmaInclusion X i) ≫ sigmaChainComplexInverse X =
      CategoryTheory.Limits.biproduct.ι (fun i => FirstHurewicz.singularComplex (X i)) i := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sigmaChainInverseDegree_comp_inclusion_mo1973_5502 X n i

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem
    ThreefoldHomologyStarCoproduct.sigmaChainComplexMap_comp_inverse {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    sigmaChainComplexMap X ≫ sigmaChainComplexInverse X =
      𝟙 (⨁ fun i => FirstHurewicz.singularComplex (X i)) := by
  apply CategoryTheory.Limits.biproduct.hom_ext'
  intro i
  rw [← CategoryTheory.Category.assoc, sigmaChainComplexMap_inclusion,
    sigmaChainComplexInverse_inclusion, CategoryTheory.Category.comp_id]

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private theorem
    ThreefoldHomologyStarCoproduct.sigmaChainComplexInverse_comp_map {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    sigmaChainComplexInverse X ≫ sigmaChainComplexMap X =
      𝟙 (FirstHurewicz.singularComplex (Σ i, X i)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply sigmaChains_hom_ext X n
  intro i
  have h :
    FirstHurewicz.singularChainMap (sigmaInclusion X i) ≫
        (sigmaChainComplexInverse X ≫ sigmaChainComplexMap X) =
      FirstHurewicz.singularChainMap (sigmaInclusion X i) := by
    rw [← CategoryTheory.Category.assoc, sigmaChainComplexInverse_inclusion,
      sigmaChainComplexMap_inclusion]
  exact (congrArg (fun f => f.f n) h).trans (CategoryTheory.Category.comp_id _).symm

attribute [local instance] ThreefoldHomologyStarCoproduct.singularChainsFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.sigmaChainComplexIso {ι : Type} (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] [Fintype ι] :
    (⨁ fun i => FirstHurewicz.singularComplex (X i)) ≅ FirstHurewicz.singularComplex (Σ i, X i)
    where
  hom := sigmaChainComplexMap X
  inv := sigmaChainComplexInverse X
  hom_inv_id := sigmaChainComplexMap_comp_inverse X
  inv_hom_id := sigmaChainComplexInverse_comp_map X

public
theorem ThreefoldHomologyStarCoproduct.homologyFiniteBiproducts :
    CategoryTheory.Limits.HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] ThreefoldHomologyStarCoproduct.homologyFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.homology_π_ι_self_mo1973_5511 {ι : Type} [Finite ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (i : ι) (a : (K i).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom a) =
      a := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biproduct.ι K i)
      (CategoryTheory.Limits.biproduct.π K i) n
  rw [CategoryTheory.Limits.biproduct.ι_π_self, HomologicalComplex.homologyMap_id] at h
  exact (congrArg (fun f => f.hom a) h).symm

attribute [local instance] ThreefoldHomologyStarCoproduct.homologyFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.homology_π_ι_ne_mo1973_5512 {ι : Type} [Finite ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) {i j : ι} (hij : i ≠ j)
    (a : (K i).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K j) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom a) =
      0 := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biproduct.ι K i)
      (CategoryTheory.Limits.biproduct.π K j) n
  rw [CategoryTheory.Limits.biproduct.ι_π_ne K hij, HomologicalComplex.homologyMap_zero] at h
  exact (congrArg (fun f => f.hom a) h).symm

attribute [local instance] ThreefoldHomologyStarCoproduct.homologyFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.homology_biproduct_total_mo1973_5513 {ι : Type}
    [Fintype ι] (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : (⨁ K).homology n) :
    ∑ i,
        (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom a) =
      a := by
  have h :
    HomologicalComplex.homologyMap
        (∑ i, CategoryTheory.Limits.biproduct.π K i ≫ CategoryTheory.Limits.biproduct.ι K i) n =
      𝟙 ((⨁ K).homology n) := by
    rw [CategoryTheory.Limits.biproduct.total, HomologicalComplex.homologyMap_id]
  change
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
        (∑ i, CategoryTheory.Limits.biproduct.π K i ≫ CategoryTheory.Limits.biproduct.ι K i) =
      _ at h
  rw [CategoryTheory.Functor.map_sum] at h
  change
    (∑ i,
        HomologicalComplex.homologyMap
          (CategoryTheory.Limits.biproduct.π K i ≫ CategoryTheory.Limits.biproduct.ι K i) n) =
      _ at h
  simpa only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using
    congrArg (fun f => f.hom a) h

attribute [local instance] ThreefoldHomologyStarCoproduct.homologyFiniteBiproducts in
private def ThreefoldHomologyStarCoproduct.homologyBiproductEquiv {ι : Type} [Fintype ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (⨁ K).homology n ≃ₗ[ℤ] (∀ i, (K i).homology n) := by
  classical
    exact
    ({    toFun a
            i := (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom a
          invFun
            a :=
            ∑ i,
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom (a i)
          left_inv := homology_biproduct_total_mo1973_5513 K n
          right_inv
            a := by
            funext i
            change
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom
                  (∑ j,
                    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K j) n).hom
                      (a j)) =
                a i
            rw [map_sum, Finset.sum_eq_single i]
            · exact homology_π_ι_self_mo1973_5511 K n i (a i)
            · intro j _ hji
              exact homology_π_ι_ne_mo1973_5512 K n hji (a j)
            · simp
          map_add' a
            b := by
            funext i
            exact
              map_add
                (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.π K i) n).hom a
                b } :
        (⨁ K).homology n ≃+ (∀ i, (K i).homology n)).toIntLinearEquiv

attribute [local instance] ThreefoldHomologyStarCoproduct.homologyFiniteBiproducts in
private theorem
    ThreefoldHomologyStarCoproduct.homologyBiproductEquiv_symm_apply {ι : Type} [Fintype ι]
    (K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : ∀ i, (K i).homology n) :
    (homologyBiproductEquiv K n).symm a =
      ∑ i, (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.ι K i) n).hom (a i) :=
  rfl

attribute [local instance] ThreefoldHomologyStarCoproduct.homologyFiniteBiproducts in
private theorem ThreefoldHomologyStarCoproduct.homologyBiproductEquiv_desc {ι : Type} [Fintype ι]
    {K : ι → ChainComplex (ModuleCat.{0} ℤ) ℕ} (n : ℕ) {L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : ∀ i, K i ⟶ L) (a : ∀ i, (K i).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biproduct.desc f) n).hom
        ((homologyBiproductEquiv K n).symm a) =
      ∑ i, (HomologicalComplex.homologyMap (f i) n).hom (a i) := by
  rw [homologyBiproductEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biproduct.ι K i)
      (CategoryTheory.Limits.biproduct.desc f) n
  rw [CategoryTheory.Limits.biproduct.ι_desc] at h
  exact (congrArg (fun k => k.hom (a i)) h).symm

private def ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv {ι : Type} [Fintype ι] (X : ι → Type)
    [∀ i, TopologicalSpace (X i)] (n : ℕ) :
    SingularMayerVietoris.SingularHomology (Σ i, X i) n ≃ₗ[ℤ]
      (∀ i, SingularMayerVietoris.SingularHomology (X i) n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (sigmaChainComplexIso X)).symm.toLinearEquiv.trans
    (homologyBiproductEquiv (fun i => FirstHurewicz.singularComplex (X i)) n)

private theorem ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv_symm_apply {ι : Type} [Fintype ι]
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] (n : ℕ)
    (a : ∀ i, SingularMayerVietoris.SingularHomology (X i) n) :
    (sigmaHomologyEquiv X n).symm a =
      ∑ i, SingularMayerVietoris.singularHomologyMap (sigmaInclusion X i) n (a i) := by
  change
    (HomologicalComplex.homologyMap (sigmaChainComplexMap X) n).hom
        ((homologyBiproductEquiv (fun i => FirstHurewicz.singularComplex (X i)) n).symm a) =
      _
  exact
    homologyBiproductEquiv_desc n (fun i => FirstHurewicz.singularChainMap (sigmaInclusion X i)) a

@[simp]
private theorem ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv_symm_single {ι : Type} [Fintype ι]
    (X : ι → Type) [∀ i, TopologicalSpace (X i)] [DecidableEq ι] (n : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (X i) n) :
    (sigmaHomologyEquiv X n).symm (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (sigmaInclusion X i) n a := by
  rw [sigmaHomologyEquiv_symm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

end Mathoverflow1973

end
