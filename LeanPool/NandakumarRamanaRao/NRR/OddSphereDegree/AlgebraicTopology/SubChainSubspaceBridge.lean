/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.MayerVietoris
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyFormula
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.BallBoundaryLES

/-! # Sub Chain Subspace Bridge -/

@[expose] public section
open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section

namespace SphereOddDegree

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The continuous inclusion of a subspace into the ambient space. -/
def sInclusion (S : Set X) : TopCat.of S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem sInclusion_hom_apply (S : Set X) (x : S) :
    (ConcreteCategory.hom (sInclusion S)) x = (x : X) := rfl

theorem isSubordinate_pushSimplex_sInclusion (S : Set X) (n : ℕ)
    (τ : singularSimplices (TopCat.of S) n) :
    IsSubordinate S (pushSimplex (sInclusion S) n τ) := by
  rintro _ ⟨x, rfl⟩
  exact (singularSimplexAsContinuousMap (TopCat.of S) n τ x).2

theorem pushSimplex_sInclusion_injective (S : Set X) (n : ℕ) :
    Function.Injective (pushSimplex (sInclusion S) n) := by
  intro τ₁ τ₂ h_eq
  apply ((TopCat.of S).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  ext x
  have h := congrArg (fun σ => (X.toSSetObjEquiv (Opposite.op ⦋n⦌) σ) x) h_eq
  exact h

theorem exists_pushSimplex_of_subordinate (S : Set X) (n : ℕ)
    {σ : singularSimplices X n} (hσ : IsSubordinate S σ) :
    ∃ τ, pushSimplex (sInclusion S) n τ = σ := by
  have h_range : Set.range (singularSimplexAsContinuousMap X n σ) ⊆ S := hσ
  let g : C(Delta n, S) :=
    ContinuousMap.mk (fun x => ⟨singularSimplexAsContinuousMap X n σ x, h_range ⟨x, rfl⟩⟩)
  use continuousMapAsSingularSimplex (TopCat.of S) n g
  apply singularSimplices_ext
  rw [pushSimplex_continuousMap, singularSimplexAsContinuousMap_continuousMapAsSingularSimplex]
  ext x
  rfl

theorem singularChainMap_sInclusion_mem (S : Set X) (n : ℕ)
    (c : singularChainGroup R (TopCat.of S) n) :
    (singularChainMap R (sInclusion S) n).hom c ∈ subChainSubmodule R X S n := by
  let f : singularChainGroup R (TopCat.of S) n ⟶ ModuleCat.of R (singularChainGroup R X n ⧸
    subChainSubmodule R X S n) :=
    singularChainMap R (sInclusion S) n ≫ ModuleCat.ofHom (Submodule.mkQ (subChainSubmodule R X
      S n))
  have hf : f = 0 := by
    apply Limits.colimit.hom_ext
    intro τ
    have h1 : (Sigma.ι (fun _ : singularSimplices (TopCat.of S) n => ModuleCat.of R R) τ.as ≫
      f).hom (1 : R) = 0 := by
      change Submodule.mkQ _ ((singularChainMap R (sInclusion S) n).hom (chainGenerator R
        (TopCat.of S) n τ.as)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, singularChainMap_generator]
      exact chainGenerator_mem_subChainSubmodule (isSubordinate_pushSimplex_sInclusion S n τ.as)
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h1
  have hc := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hf) c
  change (Submodule.mkQ (subChainSubmodule R X S n)) ((singularChainMap R (sInclusion S) n).hom
    c) = 0 at hc
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
  exact hc

/-- Corestrict the subspace singular-chain map to the subcomplex of supported chains. -/
def subChainCorestrict (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X) :
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj (TopCat.of S) ⟶
      subChainComplex R X S where
  f n := ModuleCat.ofHom
    (LinearMap.codRestrict (subChainSubmodule R X S n)
      (singularChainMap R (sInclusion S) n).hom (singularChainMap_sInclusion_mem S n))
  comm' i j hij := by
    obtain ⟨k, hk⟩ := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    have := singularChainMap_boundary_apply R (sInclusion S) j (c : singularChainGroup R
      (TopCat.of S) (j + 1))
    simp_all only [singularBoundary, subChainComplex_X, colimit.cocone_x, subChainComplex_d,
      SetLike.coe_eq_coe]
    change (subBoundary R X S j).hom ((LinearMap.codRestrict (subChainSubmodule R X S (j + 1))
      (singularChainMap R (sInclusion S) (j + 1)).hom (singularChainMap_sInclusion_mem S (j +
      1))) c) =
         ⟨(singularChainMap R (sInclusion S) j).hom ((singularBoundary R (TopCat.of S) j).hom c), _⟩
    apply Subtype.ext
    exact this

/-- The linear chain map obtained by reindexing singular-simplex generators in one degree. -/
noncomputable def reindexChainMap (R : Type) [CommRing R] {X Y : TopCat.{0}} (n : ℕ)
    (g : singularSimplices Y n → singularSimplices X n) :
    singularChainGroup R Y n ⟶ singularChainGroup R X n :=
  Limits.Sigma.desc (fun s => Limits.Sigma.ι (fun _ : singularSimplices X n => ModuleCat.of R R)
    (g s))

@[simp] theorem reindexChainMap_generator {X Y : TopCat.{0}} (n : ℕ)
    (g : singularSimplices Y n → singularSimplices X n) (σ : singularSimplices Y n) :
    (reindexChainMap R n g).hom (chainGenerator R Y n σ) = chainGenerator R X n (g σ) := by
  have key : (Sigma.ι (fun _ : singularSimplices Y n => ModuleCat.of R R) σ) ≫
      (reindexChainMap R n g) = Sigma.ι (fun _ : singularSimplices X n => ModuleCat.of R R) (g σ) :=
    Sigma.ι_comp_desc _ _
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) (1 : R)
  erw [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

theorem reindexChainMap_comp_singularChainMap {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (g : singularSimplices Y n → singularSimplices X n)
    (hg : Function.LeftInverse g (pushSimplex f n)) :
    singularChainMap R f n ≫ reindexChainMap R n g = 𝟙 _ := by
  apply Limits.colimit.hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (reindexChainMap R n g).hom ((singularChainMap R f n).hom (chainGenerator R X n τ.as)) =
       chainGenerator R X n τ.as
  rw [singularChainMap_generator, reindexChainMap_generator, hg τ.as]

theorem singularChainMap_injective_of_pushSimplex_injective {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (hf : Function.Injective (pushSimplex f n)) :
    Function.Injective (singularChainMap R f n).hom := by
  have : Mono (singularChainMap R f n) :=
    @MonoCoprod.mono_of_injective' (ModuleCat.{0} R) _ _ (singularSimplices Y n)
      (singularSimplices X n)
      (fun _ => ModuleCat.of R R) (pushSimplex f n) hf _ _ _
  exact (ModuleCat.mono_iff_injective _).mp this

theorem subChainCorestrict_bijective (S : Set X) (n : ℕ) :
    Function.Bijective ((subChainCorestrict R X S).f n).hom := by
  constructor
  · intro x y hxy
    have h_inj := @singularChainMap_injective_of_pushSimplex_injective R _ (TopCat.of S) X
      (sInclusion S) n
      (pushSimplex_sInclusion_injective S n)
    apply h_inj
    apply Subtype.ext_iff.mp at hxy
    exact hxy
  · rintro ⟨x, hx⟩
    induction hx using Submodule.span_induction with
    | mem _ h =>
      rcases h with ⟨σ, hσ, rfl⟩
      obtain ⟨τ, rfl⟩ := exists_pushSimplex_of_subordinate S n hσ
      refine ⟨chainGenerator R (TopCat.of S) n τ, ?_⟩
      apply Subtype.ext
      exact singularChainMap_generator R (sInclusion S) n τ
    | zero =>
      refine ⟨0, ?_⟩
      apply Subtype.ext
      exact map_zero _
    | add u v hu hv hx hy =>
      rcases hx with ⟨u', hu'⟩
      rcases hy with ⟨v', hv'⟩
      refine ⟨u' + v', ?_⟩
      rw [map_add, hu', hv']
      rfl
    | smul a u hu hx =>
      rcases hx with ⟨u', hu'⟩
      refine ⟨a • u', ?_⟩
      rw [map_smul, hu']
      rfl

instance subChainCorestrict_component_isIso (S : Set X) (n : ℕ) :
    IsIso ((subChainCorestrict R X S).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (subChainCorestrict_bijective S n)

instance subChainCorestrict_isIso (S : Set X) :
    IsIso (subChainCorestrict R X S) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- Identify homology of supported chains with singular homology of the subspace. -/
def subspaceHomologyIso (S : Set X) (n : ℕ) :
    (subChainComplex R X S).homology n ≅
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).obj (TopCat.of S)).homology n :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso (asIso (subChainCorestrict R X S))).symm

/-- The subspace homology identification with integer coefficients. -/
def subspaceHomologyIsoℤ (X : TopCat.{0}) (S : Set X) (n : ℕ) :
    (subChainComplex ℤ X S).homology n ≅ (singularHomologyℤ n).obj (TopCat.of S) :=
  subspaceHomologyIso S n

theorem isZero_subChainComplex_homology_of_contractible
    (X : TopCat.{0}) (S : Set X) [ContractibleSpace S] (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((subChainComplex ℤ X S).homology n) :=
  IsZero.of_iso (isZero_singularHomologyℤ_of_contractibleSpace n hn S)
    (subspaceHomologyIsoℤ X S n)

end SphereOddDegree
