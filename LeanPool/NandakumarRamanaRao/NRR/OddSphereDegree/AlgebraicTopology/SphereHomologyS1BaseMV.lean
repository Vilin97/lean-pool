/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SphereHomologyMVStep
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularH0PathConnected
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.MayerVietoris
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Topology.Separation.Lemmas
/-!
# Mayer–Vietoris base case: `H₁(S¹; ℤ) ≅ ℤ`

We compute the integral first homology of the circle `S¹` by the singular
Mayer–Vietoris sequence applied to the two-punctured cover specialized from the
recursive step file (`SphereHomologyMVStep.lean`), with `n = 0`:

* `U = S¹ \ {north}`, `V = S¹ \ {south}` are contractible;
* `U ∩ V` (the equatorial band) is homotopy equivalent to `S⁰`.

Around degree `1` the sequence reads
`H₁(U) ⊕ H₁(V) → H₁(S¹) → H₀(U ∩ V) → H₀(U) ⊕ H₀(V)`.
The left term vanishes (contractibility), so the connecting map identifies
`H₁(S¹) ≅ ker(H₀(U ∩ V) → H₀(U) ⊕ H₀(V))`. Using the augmentation isomorphism
`H₀(contractible) ≅ ℤ` (`SingularH0PathConnected.lean`), that kernel coincides
with the kernel of the augmentation `H₀(U ∩ V) → ℤ`, i.e. with the reduced
zeroth homology `H̃₀(S⁰) ≅ ℤ`.

The result `sphereTopHomologyIso_one : SphereTopHomologyIso 1` supplies the
`base` field of `SphereSuspensionTower`.
-/

open CategoryTheory AlgebraicTopology Limits TopologicalSpace
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

/-! ## Setup for the circle cover (the `n = 0` specialization) -/

/-- The circle `S¹` as a `TopCat` (the `n = 0` instance of `sphereSpace`). -/
abbrev circleTop : TopCat.{0} := sphereSpace 0

/-- The upper-punctured open cover member. -/
abbrev circU : Opens circleTop := upperOpens 0

/-- The lower-punctured open cover member. -/
abbrev circV : Opens circleTop := lowerOpens 0

theorem circUV_top : circU ⊔ circV = ⊤ := upperOpens_sup_lowerOpens 0

/-- The equatorial band `S¹ \ {north, south}` as a subset. -/
abbrev circBand : Set circleTop := (circU : Set circleTop) ∩ (circV : Set circleTop)

/-- The Mayer–Vietoris left map on `H₀`, `H₀(U ∩ V) → H₀(U) ⊕ H₀(V)`. -/
abbrev circF0 :
    (subChainComplex ℤ circleTop circBand).homology 0 ⟶
      (subChainComplex ℤ circleTop (circU : Set circleTop) ⊞
        subChainComplex ℤ circleTop (circV : Set circleTop)).homology 0 :=
  HomologicalComplex.homologyMap (mvShortComplex ℤ circU circV circUV_top).f 0

/-! ## Reduced `H₀(S⁰) ≅ ℤ` -/

/-- A point of `S⁰`. -/
instance instNonemptySphere0 : Nonempty (Sphere 0) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp [EuclideanSpace.norm_eq]⟩⟩

/-
**Algebra helper.** A finite free `ℤ`-module of rank `1` is isomorphic to `ℤ`.
-/
theorem linearEquiv_int_of_finrank_one {N : Type} [AddCommGroup N] [Module ℤ N]
    [Module.Free ℤ N] [Module.Finite ℤ N] (h : Module.finrank ℤ N = 1) :
    Nonempty (N ≃ₗ[ℤ] ℤ) := by
  have := ( Module.finBasis ℤ N );
  rw [ h ] at this; exact ⟨ this.equivFun.trans ( LinearEquiv.ofFinrankEq _ _ <| by simp +decide [ h ] ) ⟩ ;

/-- **Algebra helper.** The kernel of a surjection from a rank-`2` finite free
`ℤ`-module onto `ℤ` is isomorphic to `ℤ`. -/
theorem ker_linearEquiv_int_of_finrank_two {M : Type} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (hM : Module.finrank ℤ M = 2)
    (g : M →ₗ[ℤ] ℤ) (hg : Function.Surjective g) :
    Nonempty (↥(LinearMap.ker g) ≃ₗ[ℤ] ℤ) := by
  -- There is a ℤ-module instance diamond on `↥(ker g)` (`Submodule.module` vs
  -- `AddCommGroup.toIntModule`); we work with `Submodule.module` and bridge with
  -- `Subsingleton.elim` at the end.
  have key : @Module.finrank ℤ ↥(LinearMap.ker g) _ _ (LinearMap.ker g).module = 1 := by
    letI : Module ℤ ↥(LinearMap.ker g) := (LinearMap.ker g).module
    letI : Module ℤ (M ⧸ LinearMap.ker g) := Submodule.Quotient.module _
    haveI hfin : Module.Finite ℤ ↥(LinearMap.ker g) :=
      Module.Finite.of_fg (IsNoetherian.noetherian (LinearMap.ker g))
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
    have hq := (g.quotKerEquivOfSurjective hg).finrank_eq
    rw [Module.finrank_self] at hq
    rw [hq, hM] at h1
    omega
  letI : Module ℤ ↥(LinearMap.ker g) := (LinearMap.ker g).module
  haveI hfin : Module.Finite ℤ ↥(LinearMap.ker g) :=
    Module.Finite.of_fg (IsNoetherian.noetherian (LinearMap.ker g))
  haveI hfree : Module.Free ℤ ↥(LinearMap.ker g) :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨e⟩ := linearEquiv_int_of_finrank_one key
  exact ⟨(Subsingleton.elim (LinearMap.ker g).module
    (AddCommGroup.toIntModule ↥(LinearMap.ker g))) ▸ e⟩

/-
`S⁰` has exactly two points.
-/
theorem sphere0_equiv_fin2 : Nonempty (Sphere 0 ≃ Fin 2) := by
  refine' ⟨ _ ⟩;
  refine' Equiv.ofBijective ( fun x => if x = ⟨ EuclideanSpace.single 0 1, by norm_num [ EuclideanSpace.norm_eq ] ⟩ then 0 else 1 ) ⟨ _, _ ⟩;
  · intro x y hxy;
    cases sphere_zero_eq_or_neg x ⟨ EuclideanSpace.single 0 1, by norm_num [ EuclideanSpace.norm_eq ] ⟩ <;> cases sphere_zero_eq_or_neg y ⟨ EuclideanSpace.single 0 1, by norm_num [ EuclideanSpace.norm_eq ] ⟩ <;> aesop;
  · intro x;
    fin_cases x <;> simp +decide;
    refine' ⟨ EuclideanSpace.single 0 ( -1 ), _, _ ⟩ <;> norm_num;
    exact ne_of_apply_ne ( fun x => x 0 ) ( by norm_num )

/-
**Topology helper.** `H₀(S⁰; ℤ)` is a finite free `ℤ`-module of rank `2`.
-/
theorem h0_sphere0_free_finrank :
    Module.Free ℤ ((singularChainComplex ℤ (TopCat.of (Sphere 0))).homology 0) ∧
    Module.Finite ℤ ((singularChainComplex ℤ (TopCat.of (Sphere 0))).homology 0) ∧
    Module.finrank ℤ ((singularChainComplex ℤ (TopCat.of (Sphere 0))).homology 0) = 2 := by
  refine' ⟨ _, _, _ ⟩;
  · have := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace ( ModuleCat ℤ ) ( ModuleCat.of ℤ ℤ ) ( TopCat.of ( Sphere 0 ) );
    have := this.toLinearEquiv;
    exact Module.Free.of_equiv this.symm;
  · have := singularHomologyFunctorZeroOfTotallyDisconnectedSpace ( ModuleCat ℤ ) ( ModuleCat.of ℤ ℤ ) ( TopCat.of ( Sphere 0 ) );
    have := this.toLinearEquiv;
    exact Module.Finite.of_surjective this.symm.toLinearMap this.symm.surjective;
  · obtain ⟨ e ⟩ := sphere0_equiv_fin2;
    have h_iso : (singularChainComplex ℤ (TopCat.of (Sphere 0))).homology 0 ≅ ModuleCat.of ℤ (DirectSum (Sphere 0) (fun _ => ℤ)) := by
      have hi := singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of (Sphere 0))
      change (singularChainComplex ℤ (TopCat.of (Sphere 0))).homology 0 ≅ _ at hi
      exact hi ≪≫ ModuleCat.coprodIsoDirectSum _
    convert LinearEquiv.finrank_eq ( h_iso.toLinearEquiv ) using 1;
    simp +decide [ Module.finrank ];
    rw [ Cardinal.mk_congr e ] ; norm_num

/-
**Reduced zeroth homology of `S⁰`.** The kernel of the augmentation
`H₀(S⁰; ℤ) → ℤ` is isomorphic to `ℤ`.
-/
theorem reducedH0_sphere0_iso :
    Nonempty (kernel (H0aug (TopCat.of (Sphere 0))) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨hFree, hFin, hrank⟩ := h0_sphere0_free_finrank
  haveI := hFree
  haveI := hFin
  obtain ⟨e⟩ := ker_linearEquiv_int_of_finrank_two hrank
    (ModuleCat.Hom.hom (H0aug (TopCat.of (Sphere 0)))) (surjective_H0aug _)
  -- Use the isomorphism from the kernel to the integers to construct the desired isomorphism.
  apply Nonempty.intro;
  refine' CategoryTheory.Iso.trans _ ( LinearEquiv.toModuleIso e );
  convert ModuleCat.kernelIsoKer _;
  exact Subsingleton.elim _ _

/-! ## The kernel of the band augmentation is `ℤ` -/

/-- The kernel of the band augmentation `H₀(U ∩ V) → ℤ` is isomorphic to `ℤ`,
using the homotopy equivalence `U ∩ V ≃ S⁰` and `reducedH0_sphere0_iso`. -/
theorem kerBand_iso :
    Nonempty (kernel (subH0aug circleTop circBand) ≅ ModuleCat.of ℤ ℤ) := by
  have hnat : (singularHomologyℤ_isoOfHomotopyEquivSpace 0 (sphereBandHomotopyEquiv 0)).hom
      ≫ H0aug (TopCat.of (Sphere 0)) = H0aug (TopCat.of ↑(sphereBand 0)) :=
    H0aug_natural (TopCat.ofHom (sphereBandHomotopyEquiv 0).toFun)
  refine ⟨?_⟩
  refine kernelIsIsoComp (subspaceHomologyIsoℤ circleTop circBand 0).hom
    (H0aug (TopCat.of circBand)) ≪≫ ?_
  refine kernelIsoOfEq hnat.symm ≪≫ ?_
  exact kernelIsIsoComp (singularHomologyℤ_isoOfHomotopyEquivSpace 0 (sphereBandHomotopyEquiv 0)).hom
    (H0aug (TopCat.of (Sphere 0))) ≪≫ reducedH0_sphere0_iso.some

/-! ## The Mayer–Vietoris kernel identity -/

/-
The MV left map's first component is the inclusion `U ∩ V ↪ U`.
-/
theorem circF_comp_fst :
    (mvShortComplex ℤ circU circV circUV_top).f ≫ biprod.fst
      = mvInclUV_U ℤ circU circV := by
  simp [mvShortComplex, mvLeftChainMap]

/-
The MV left map's second component is minus the inclusion `U ∩ V ↪ V`.
-/
theorem circF_comp_snd :
    (mvShortComplex ℤ circU circV circUV_top).f ≫ biprod.snd
      = -(mvInclUV_V ℤ circU circV) := by
  simp [mvShortComplex, mvLeftChainMap]

/-- **Joint monomorphism of the homology biproduct projections.** An element of
`H₀(X₂)` is zero iff both of its biproduct components vanish. -/
theorem biprod_homology_zero_iff
    (y : (subChainComplex ℤ circleTop (circU : Set circleTop) ⊞
      subChainComplex ℤ circleTop (circV : Set circleTop)).homology 0) :
    y = 0 ↔
      (HomologicalComplex.homologyMap (biprod.fst :
          (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0) y = 0
        ∧ (HomologicalComplex.homologyMap (biprod.snd :
          (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0) y = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩
  · rintro ⟨h1, h2⟩
    have htot :
        (biprod.fst : (subChainComplex ℤ circleTop (circU : Set circleTop)
            ⊞ subChainComplex ℤ circleTop (circV : Set circleTop)) ⟶ _) ≫ biprod.inl
          + (biprod.snd : _ ⟶ _) ≫ biprod.inr
          = 𝟙 (subChainComplex ℤ circleTop (circU : Set circleTop)
            ⊞ subChainComplex ℤ circleTop (circV : Set circleTop)) := biprod.total
    have hmap := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) htot
    simp only [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_id] at hmap
    have hy := congrArg (fun ψ => ψ y) hmap
    change
      ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inl :
          subChainComplex ℤ circleTop (circU : Set circleTop) ⟶ _) 0)
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.fst :
            (subChainComplex ℤ circleTop (circU : Set circleTop) ⊞
              subChainComplex ℤ circleTop (circV : Set circleTop)) ⟶ _) 0) y) +
        ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inr :
          subChainComplex ℤ circleTop (circV : Set circleTop) ⟶ _) 0)
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.snd :
            (subChainComplex ℤ circleTop (circU : Set circleTop) ⊞
              subChainComplex ℤ circleTop (circV : Set circleTop)) ⟶ _) 0) y) = y at hy
    rw [h1, h2, map_zero, map_zero] at hy
    exact hy.symm.trans (add_zero _)

/-- **The Mayer–Vietoris kernel coincides with the reduced-`H₀` kernel.**
`ker(H₀(U ∩ V) → H₀(U) ⊕ H₀(V)) ≅ ker(H₀(U ∩ V) → ℤ)`. -/
theorem kerF0_iso_kerBand :
    Nonempty (kernel circF0 ≅ kernel (subH0aug circleTop circBand)) := by
  haveI := isIso_subH0aug circleTop (circU : Set circleTop)
  haveI := isIso_subH0aug circleTop (circV : Set circleTop)
  have hUeq : HomologicalComplex.homologyMap (mvInclUV_U ℤ circU circV) 0
      ≫ subH0aug circleTop (circU : Set circleTop) = subH0aug circleTop circBand :=
    subH0aug_natural_inclusion circleTop circBand (circU : Set circleTop) Set.inter_subset_left
  have hVeq : HomologicalComplex.homologyMap (mvInclUV_V ℤ circU circV) 0
      ≫ subH0aug circleTop (circV : Set circleTop) = subH0aug circleTop circBand :=
    subH0aug_natural_inclusion circleTop circBand (circV : Set circleTop) Set.inter_subset_right
  have hfst : circF0 ≫ HomologicalComplex.homologyMap
      (biprod.fst : (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0
      = HomologicalComplex.homologyMap (mvInclUV_U ℤ circU circV) 0 := by
    change HomologicalComplex.homologyMap (mvLeftChainMap ℤ circU circV circUV_top) 0 ≫ _ = _
    rw [← HomologicalComplex.homologyMap_comp]
    simp [mvLeftChainMap]
  have hsnd : circF0 ≫ HomologicalComplex.homologyMap
      (biprod.snd : (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0
      = -(HomologicalComplex.homologyMap (mvInclUV_V ℤ circU circV) 0) := by
    change HomologicalComplex.homologyMap (mvLeftChainMap ℤ circU circV circUV_top) 0 ≫ _ = _
    rw [← HomologicalComplex.homologyMap_comp]
    simp [mvLeftChainMap, HomologicalComplex.homologyMap_neg]
  have hinjU : Function.Injective (ModuleCat.Hom.hom (subH0aug circleTop (circU : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hinjV : Function.Injective (ModuleCat.Hom.hom (subH0aug circleTop (circV : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hUx : ∀ z, (subH0aug circleTop (circU : Set circleTop))
      ((HomologicalComplex.homologyMap (mvInclUV_U ℤ circU circV) 0) z)
      = subH0aug circleTop circBand z := by
    intro z
    have h : (HomologicalComplex.homologyMap (mvInclUV_U ℤ circU circV) 0
        ≫ subH0aug circleTop (circU : Set circleTop)) z = subH0aug circleTop circBand z :=
      congrArg (fun ψ => ψ z) hUeq
    rwa [CategoryTheory.comp_apply] at h
  have hVx : ∀ z, (subH0aug circleTop (circV : Set circleTop))
      ((HomologicalComplex.homologyMap (mvInclUV_V ℤ circU circV) 0) z)
      = subH0aug circleTop circBand z := by
    intro z
    have h : (HomologicalComplex.homologyMap (mvInclUV_V ℤ circU circV) 0
        ≫ subH0aug circleTop (circV : Set circleTop)) z = subH0aug circleTop circBand z :=
      congrArg (fun ψ => ψ z) hVeq
    rwa [CategoryTheory.comp_apply] at h
  have hfx : ∀ z, (HomologicalComplex.homologyMap (biprod.fst :
      (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0)
      (circF0 z) = (HomologicalComplex.homologyMap (mvInclUV_U ℤ circU circV) 0) z := by
    intro z
    have h : (circF0 ≫ HomologicalComplex.homologyMap (biprod.fst :
        (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0) z
        = (HomologicalComplex.homologyMap (mvInclUV_U ℤ circU circV) 0) z :=
      congrArg (fun ψ => ψ z) hfst
    rwa [CategoryTheory.comp_apply] at h
  have hsx : ∀ z, (HomologicalComplex.homologyMap (biprod.snd :
      (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0)
      (circF0 z) = -((HomologicalComplex.homologyMap (mvInclUV_V ℤ circU circV) 0) z) := by
    intro z
    have h : (circF0 ≫ HomologicalComplex.homologyMap (biprod.snd :
        (subChainComplex ℤ circleTop ↑circU ⊞ subChainComplex ℤ circleTop ↑circV) ⟶ _) 0) z
        = (-(HomologicalComplex.homologyMap (mvInclUV_V ℤ circU circV) 0)) z :=
      congrArg (fun ψ => ψ z) hsnd
    rw [CategoryTheory.comp_apply] at h
    refine h.trans ?_
    simp
  have hker : LinearMap.ker (ModuleCat.Hom.hom circF0)
      = LinearMap.ker (ModuleCat.Hom.hom (subH0aug circleTop circBand)) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hcx : circF0 x = 0 := hx
      show subH0aug circleTop circBand x = 0
      rw [← hUx x, ← hfx x, hcx, map_zero, map_zero]
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hbandx : subH0aug circleTop circBand x = 0 := hx
      have hax : (HomologicalComplex.homologyMap (mvInclUV_U ℤ circU circV) 0) x = 0 := by
        apply hinjU; rw [map_zero, hUx x, hbandx]
      have hbx : (HomologicalComplex.homologyMap (mvInclUV_V ℤ circU circV) 0) x = 0 := by
        apply hinjV; rw [map_zero, hVx x, hbandx]
      show circF0 x = 0
      refine (biprod_homology_zero_iff (circF0 x)).mpr ⟨?_, ?_⟩
      · rw [hfx x, hax]
      · rw [hsx x, hbx, neg_zero]
  exact ⟨ModuleCat.kernelIsoKer circF0 ≪≫ eqToIso (by rw [hker]) ≪≫
    (ModuleCat.kernelIsoKer (subH0aug circleTop circBand)).symm⟩

/-! ## Assembling the Mayer–Vietoris connecting isomorphism -/

/-
`H₁(S¹) ≅ ker(H₀(U ∩ V) → H₀(U) ⊕ H₀(V))`, the connecting isomorphism onto the
kernel (the connecting map is mono since `H₁(U) ⊕ H₁(V) = 0`, and its image is the
kernel by exactness).
-/
theorem sphereH1_iso_kerF0 :
    Nonempty (sphereTopHomologyℤ 1 ≅ kernel circF0) := by
  refine ⟨(sphereModelHomologyIso 1 1).trans
    ((smallChains_homologyIso ℤ (TopCat.of (Sphere 1))
      (twoSetCover circU circV circUV_top) 1).symm.trans ?_)⟩
  have hδ_mono : Mono ( (mvShortExact ℤ circU circV circUV_top).δ 1 0 (by simp [ComplexShape.down_Rel]) ) := by
    have hδ_mono : IsZero ( (mvShortComplex ℤ circU circV circUV_top).X₂.homology 1 ) := by
      apply isZero_mvX₂_homology;
      · convert isZero_subChainComplex_homology_of_contractible circleTop ( ↑circU ) 1 ( by norm_num ) using 1;
      · apply isZero_subChainComplex_homology_of_contractible circleTop (lowerOpens 0) 1 (by norm_num);
    have := ( mvShortExact ℤ circU circV circUV_top ).homology_exact₃ 1 0 ( by simp [ ComplexShape.down_Rel ] );
    convert this.mono_g;
    simp +decide [ hδ_mono.eq_of_src ];
    exact Or.inl ( hδ_mono.eq_of_src _ _ );
  have hexact := (mvShortExact ℤ circU circV circUV_top).homology_exact₁ 1 0
    (by simp [ComplexShape.down_Rel])
  exact hexact.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)

/-! ## The base case -/

/-- **`H₁(S¹; ℤ) ≅ ℤ`** (as a `Nonempty` package). -/
theorem sphereTopHomology_one_iso_nonempty :
    Nonempty (sphereTopHomologyℤ 1 ≅ ModuleCat.of ℤ ℤ) :=
  ⟨(sphereH1_iso_kerF0).some ≪≫ (kerF0_iso_kerBand).some ≪≫ (kerBand_iso).some⟩

/-- **The base case of the sphere suspension tower:** `H₁(S¹; ℤ) ≅ ℤ`. -/
def sphereTopHomologyIso_one : SphereTopHomologyIso 1 :=
  (sphereTopHomology_one_iso_nonempty).some

end SphereOddDegree
