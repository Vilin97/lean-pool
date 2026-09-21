/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.H1ClassifierZMod2

/-!
# Naturality and bijectivity of the Kronecker classifier over `F₂`

This file upgrades the evaluation classifier
`kroneckerMap X n : Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)`
(`H1ClassifierZMod2.lean`) to:

* its **naturality** in the space `X` — the Kronecker pairing is natural,
 `⟨f^* a, z⟩ = ⟨a, f_* z⟩` (`kroneckerMap_naturality`,
 `kroneckerMap_naturality_apply`);
* its **injectivity** over the field `F₂` (`kroneckerMap_injective`) — the second,
 "uniqueness" half of the universal coefficient theorem over a field;
* hence its **bijectivity** and the bundled **universal coefficient isomorphism**
 `kroneckerEquiv X n : Hⁿ(X; F₂) ≅ Hom_{F₂}(Hₙ(X; F₂), F₂)`.

Together with the already-proved `kroneckerMap_surjective` this completes the
degree-`n` universal coefficient theorem over `F₂` for the library's own singular
(co)homology, as a *natural isomorphism*.

## Main declarations

* `chainMapZMod2 f` / `homologyPushZMod2 f n` — the covariant chain map and the
 pushforward `f_* : Hₙ(X; F₂) ⟶ Hₙ(Y; F₂)` of a continuous map `f`.
* `homologyDualMap f n` — the dual (precomposition) map
 `Hom(Hₙ(Y; F₂), F₂) ⟶ Hom(Hₙ(X; F₂), F₂)`.
* `kroneckerMap_naturality` — the naturality square
 `cohPullback f n ≫ kroneckerMap X n = kroneckerMap Y n ≫ homologyDualMap f n`.
* `kroneckerMap_injective`, `kroneckerMap_bijective`.
* `kroneckerEquiv X n` — the universal coefficient isomorphism over `F₂`.
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace SphereOddDegree

variable {X Y : TopCat.{0}}

/-- The covariant `F₂` singular chain map induced by a continuous map `f`. -/
abbrev chainMapZMod2 (f : X ⟶ Y) : chainCxZMod2 X ⟶ chainCxZMod2 Y :=
  ((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).map f

/-- The pushforward `f_* : Hₙ(X; F₂) ⟶ Hₙ(Y; F₂)` on singular homology. -/
noncomputable def homologyPushZMod2 (f : X ⟶ Y) (n : ℕ) :
    homologyZMod2 X n ⟶ homologyZMod2 Y n :=
  HomologicalComplex.homologyMap (chainMapZMod2 f) n

/-- The dual / precomposition map
`Hom(Hₙ(Y; F₂), F₂) ⟶ Hom(Hₙ(X; F₂), F₂)` of the homology pushforward. -/
noncomputable def homologyDualMap (f : X ⟶ Y) (n : ℕ) :
    homologyDualZMod2 Y n ⟶ homologyDualZMod2 X n :=
  ModuleCat.ofHom (LinearMap.lcomp (ZMod 2) (ZMod 2) (homologyPushZMod2 f n).hom)

@[simp] theorem homologyDualMap_hom_apply (f : X ⟶ Y) (n : ℕ)
    (g : homologyZMod2 Y n →ₗ[ZMod 2] ZMod 2) :
    (homologyDualMap f n).hom g = g.comp (homologyPushZMod2 f n).hom := rfl

/-- The cochain pullback is precomposition with the chain map (definitional). -/
theorem cochainPullback_eq_comp (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) :
    cochainPullback f n φ = (chainMapZMod2 f).f n ≫ φ := rfl

/-
**Naturality of the Kronecker classifier.** The square
```text
Hⁿ(Y; F₂) --kroneckerMap Y n--> Hom(Hₙ(Y; F₂), F₂)
 | cohPullback f n | homologyDualMap f n
 v v
Hⁿ(X; F₂) --kroneckerMap X n--> Hom(Hₙ(X; F₂), F₂)
```
commutes: `cohPullback f n ≫ kroneckerMap X n = kroneckerMap Y n ≫ homologyDualMap f n`.
-/
theorem kroneckerMap_naturality (f : X ⟶ Y) (n : ℕ) :
    cohPullback f n ≫ kroneckerMap X n = kroneckerMap Y n ≫ homologyDualMap f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective Y n a
  show (kroneckerMap X n).hom ((cohPullback f n).hom (cocycleClass Y n φ hφ))
    = (homologyDualMap f n).hom ((kroneckerMap Y n).hom (cocycleClass Y n φ hφ))
  rw [cohPullback_cocycleClass, kroneckerMap_cocycleClass, kroneckerMap_cocycleClass, homologyDualMap_hom_apply]
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective ((chainCxZMod2 X).homologyπ n)).1 inferInstance z
  have h_lhs := kroneckerFunctional_apply X n (cochainPullback f n φ) (cochainPullback_cocycle f n φ hφ) c
  have h_push : (homologyPushZMod2 f n).hom (((chainCxZMod2 X).homologyπ n).hom c)
      = ((chainCxZMod2 Y).homologyπ n).hom ((HomologicalComplex.cyclesMap (chainMapZMod2 f) n).hom c) := by
    have h_nat := HomologicalComplex.homologyπ_naturality (chainMapZMod2 f) n
    have := congrArg (fun (m : (chainCxZMod2 X).cycles n ⟶ homologyZMod2 Y n) => m.hom c) h_nat
    exact this
  have h_rhs := kroneckerFunctional_apply Y n φ hφ ((HomologicalComplex.cyclesMap (chainMapZMod2 f) n).hom c)
  rw [LinearMap.comp_apply, h_push, h_rhs, h_lhs]
  have h_cyc : ((chainCxZMod2 Y).iCycles n).hom ((HomologicalComplex.cyclesMap (chainMapZMod2 f) n).hom c)
      = ((chainMapZMod2 f).f n).hom (((chainCxZMod2 X).iCycles n).hom c) := by
    have h_i := HomologicalComplex.cyclesMap_i (chainMapZMod2 f) n
    have := congrArg (fun (m : (chainCxZMod2 X).cycles n ⟶ (chainCxZMod2 Y).X n) => m.hom c) h_i
    exact this
  rw [h_cyc]
  rfl

/-- Element form of `kroneckerMap_naturality`: `⟨f^* a, z⟩ = ⟨a, f_* z⟩`. -/
theorem kroneckerMap_naturality_apply (f : X ⟶ Y) (n : ℕ) (a : cohomologyZMod2 Y n) :
    (kroneckerMap X n).hom ((cohPullback f n).hom a)
      = ((kroneckerMap Y n).hom a).comp (homologyPushZMod2 f n).hom := by
  have h := kroneckerMap_naturality f n
  have happ := congrArg (fun m : cohomologyZMod2 Y n ⟶ homologyDualZMod2 X n => m.hom a) h
  have hcomp : (cohPullback f n ≫ kroneckerMap X n).hom a
      = (kroneckerMap X n).hom ((cohPullback f n).hom a) := rfl
  have hcomp2 : (kroneckerMap Y n ≫ homologyDualMap f n).hom a
      = ((kroneckerMap Y n).hom a).comp (homologyPushZMod2 f n).hom := rfl
  exact hcomp.symm.trans (happ.trans hcomp2)

/-- **Extension of functionals over the field `F₂`.** Every linear functional on a
submodule `W` of an `F₂`-module `M` extends to a functional on all of `M`. This
is the injectivity of the `F₂`-module `ZMod 2`. -/
theorem zmod2_extend_functional {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (W : Submodule (ZMod 2) M) (f : W →ₗ[ZMod 2] ZMod 2) :
    ∃ g : M →ₗ[ZMod 2] ZMod 2, ∀ w : W, g (w : M) = f w := by
  obtain ⟨g, hg⟩ := (moduleInjective_ZMod2 (ZMod 2)).out W.subtype W.injective_subtype f
  exact ⟨g, fun w => hg w⟩

/-- **A functional vanishing on `ker d` factors through `d`.** If `φ : M → F₂`
vanishes on the kernel of a linear map `d : M → N`, then `φ = η ∘ d` for some
functional `η : N → F₂`. (Over a field: first isomorphism theorem plus the
extension `zmod2_extend_functional`.) -/
theorem zmod2_factor_of_ker_le {M N : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (d : M →ₗ[ZMod 2] N) (φ : M →ₗ[ZMod 2] ZMod 2)
    (h : LinearMap.ker d ≤ LinearMap.ker φ) :
    ∃ η : N →ₗ[ZMod 2] ZMod 2, η.comp d = φ := by
  -- φ descends to M ⧸ ker d, then transports to range d via the first iso theorem,
  -- then extends to all of N by injectivity of F₂.
  set φbar : (M ⧸ LinearMap.ker d) →ₗ[ZMod 2] ZMod 2 := (LinearMap.ker d).liftQ φ h with hφbar
  set e : (M ⧸ LinearMap.ker d) ≃ₗ[ZMod 2] LinearMap.range d := d.quotKerEquivRange with he
  set f0 : (LinearMap.range d) →ₗ[ZMod 2] ZMod 2 := φbar.comp e.symm.toLinearMap with hf0
  obtain ⟨η, hη⟩ := zmod2_extend_functional (LinearMap.range d) f0
  refine ⟨η, ?_⟩
  ext x
  have hmem : d x ∈ LinearMap.range d := ⟨x, rfl⟩
  have h1 : η (d x) = f0 ⟨d x, hmem⟩ := hη ⟨d x, hmem⟩
  have h2 : e.symm ⟨d x, hmem⟩ = Submodule.Quotient.mk x := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [he, LinearMap.quotKerEquivRange_apply_mk]
  simp only [LinearMap.comp_apply, h1, hf0, LinearEquiv.coe_coe, h2, hφbar,
    Submodule.liftQ_apply]

/-- **The cycle inclusion realises the kernel of the differential.** Any chain
element killed by the differential out of degree `n+1` is the image of a cycle. -/
theorem mem_range_iCycles_of_d {X : TopCat.{0}} (n : ℕ)
    (x : (chainCxZMod2 X).X (n + 1))
    (hx : ((chainCxZMod2 X).d (n + 1) n).hom x = 0) :
    ∃ c : (chainCxZMod2 X).cycles (n + 1), ((chainCxZMod2 X).iCycles (n + 1)).hom c = x :=
  ⟨(chainCxZMod2 X).cyclesMk x n (by simp [ComplexShape.next_eq']) hx,
    (chainCxZMod2 X).i_cyclesMk x n (by simp [ComplexShape.next_eq']) hx⟩

/-- **Injectivity of the Kronecker classifier over `F₂`** (the "uniqueness" half
of the universal coefficient theorem over a field): a cohomology class whose
Kronecker functional vanishes is zero. -/
theorem kroneckerMap_injective (X : TopCat.{0}) (n : ℕ) :
    Function.Injective (kroneckerMap X n).hom := by
  rw [(ModuleCat.mono_iff_injective (kroneckerMap X n)).symm, ModuleCat.mono_iff_injective]
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X n a
  have hkf : (kroneckerFunctional X n φ hφ).hom = 0 := by
    rw [← kroneckerMap_cocycleClass X n φ hφ]; exact ha
  have hkf0 : kroneckerFunctional X n φ hφ = 0 := by
    apply ModuleCat.hom_ext; rw [hkf]; rfl
  have hiφ : (chainCxZMod2 X).iCycles n ≫ φ = 0 := by
    rw [← kroneckerFunctional_homologyπ X n φ hφ, hkf0, comp_zero]
  rcases n with _ | m
  · have : Epi ((chainCxZMod2 X).iCycles 0) := by
      have : IsIso ((chainCxZMod2 X).iCycles 0) :=
        (chainCxZMod2 X).isIso_iCycles 0 0 (by simp [ComplexShape.next])
          ((chainCxZMod2 X).shape 0 0 (by simp [ComplexShape.down]))
      infer_instance
    have hφ0 : φ = 0 := by
      rw [← cancel_epi ((chainCxZMod2 X).iCycles 0), hiφ, comp_zero]
    rw [cocycleClass_congr X 0 hφ0 hφ (hφ0 ▸ hφ), cocycleClass_zero]
  · have hkerle : LinearMap.ker ((chainCxZMod2 X).d (m + 1) m).hom
        ≤ LinearMap.ker φ.hom := by
      intro x hx
      simp only [LinearMap.mem_ker] at hx ⊢
      obtain ⟨c, rfl⟩ := mem_range_iCycles_of_d m x hx
      have := congrArg (fun (t : (chainCxZMod2 X).cycles (m + 1) ⟶ _) => t.hom c) hiφ
      simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using this
    obtain ⟨ηlin, hη⟩ := zmod2_factor_of_ker_le
      ((chainCxZMod2 X).d (m + 1) m).hom φ.hom hkerle
    set η : singularCochainGroup (ZMod 2) X m := ModuleCat.ofHom ηlin with hηdef
    have hcob : φ = cochainCoboundary (ZMod 2) X m η := by
      have hstep : cochainCoboundary (ZMod 2) X m η
          = (chainCxZMod2 X).d (m + 1) m ≫ η := rfl
      rw [hstep]
      apply ModuleCat.hom_ext
      show φ.hom = ((chainCxZMod2 X).d (m + 1) m ≫ η).hom
      rw [ModuleCat.hom_comp]
      exact hη.symm
    rw [cocycleClass_congr X (m + 1) hcob hφ
        (cochainCoboundary_cochainCoboundary X m η),
      cocycleClass_coboundary_zero]

/-- The Kronecker classifier is bijective over `F₂`. -/
theorem kroneckerMap_bijective (X : TopCat.{0}) (n : ℕ) :
    Function.Bijective (kroneckerMap X n).hom :=
  ⟨kroneckerMap_injective X n, kroneckerMap_surjective X n⟩

/-- **The universal coefficient isomorphism over `F₂`**:
`Hⁿ(X; F₂) ≅ Hom_{F₂}(Hₙ(X; F₂), F₂)`, the Kronecker classifier as an
isomorphism of `ModuleCat (ZMod 2)`. -/
noncomputable def kroneckerEquiv (X : TopCat.{0}) (n : ℕ) :
    cohomologyZMod2 X n ≅ homologyDualZMod2 X n :=
  (LinearEquiv.ofBijective (kroneckerMap X n).hom (kroneckerMap_bijective X n)).toModuleIso

end SphereOddDegree
