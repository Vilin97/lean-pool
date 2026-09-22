/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.MayerVietorisSES
import Mathlib.Tactic

/-!
# The singular Mayer–Vietoris long exact sequence and connecting isomorphism

Building on the chain-level short exact sequence
`mvShortComplex_shortExact` (file `MayerVietorisSES.lean`)

```text
0 → C_*(U ∩ V) → C_*(U) ⊕ C_*(V) → C_*^{U,V}(X) → 0
```

and Mathlib's homology long exact sequence for a short exact sequence of
homological complexes (`ShortComplex.ShortExact.homology_exact₁/₂/₃` and the
connecting map `ShortComplex.ShortExact.δ`), this file packages the **singular
Mayer–Vietoris exact sequence**.

The key consequence used downstream (sphere homology, the project) is the
**connecting isomorphism**: whenever the homology of `C_*(U)` and `C_*(V)`
vanishes in the two relevant degrees (e.g. when `U` and `V` are contractible and
the degrees are positive), the Mayer–Vietoris connecting map is an isomorphism

```text
H_i(X) ≅ H_{i-1}(U ∩ V)
```

after using the small-simplices quasi-isomorphism of the project to replace the
small-chain homology `H_*(C_*^{U,V}(X))` by the singular homology `H_*(X)`.

## Main results

* `SphereOddDegree.isIso_shortExact_δ` — abstract homological-algebra input: for a
 short exact sequence of chain complexes, the connecting map `δ : H_i(X₃) →
 H_j(X₁)` is an isomorphism as soon as `H_i(X₂)` and `H_j(X₂)` both vanish.
* `SphereOddDegree.mvHomology_exact_inter`, `mvHomology_exact_sum`,
 `mvHomology_exact_X` — the three exactness statements of the Mayer–Vietoris
 sequence (re-exported from Mathlib for the two-set cover).
* `SphereOddDegree.mvConnectingIso` — the connecting isomorphism
 `H_i(C_*^{U,V}(X)) ≅ H_j(U ∩ V)` under the two vanishing hypotheses.
* `SphereOddDegree.mvHomologyIso` — the singular Mayer–Vietoris connecting
 isomorphism `H_i(X) ≅ H_j(U ∩ V)` (with `i = j + 1`), obtained by composing the
 small-simplices quasi-isomorphism with `mvConnectingIso`.
* `SphereOddDegree.mvHomologyIsoSucc` — the special case `H_{n+1}(X) ≅
 H_n(U ∩ V)`, the sphere-ready corollary.
-/

open CategoryTheory Limits TopologicalSpace ShortComplex
open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree

open Classical

variable (R : Type) [CommRing R] {X : TopCat.{0}}

/-! ## Abstract homological-algebra inputs -/

/-- A binary biproduct of two zero objects is a zero object. -/
theorem isZero_biprod_of_isZero {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {A B : C} (hA : IsZero A) (hB : IsZero B) :
    IsZero (A ⊞ B) := by
  have h : 𝟙 (A ⊞ B) = 0 := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      first
        | (simp; done)
        | exact hA.eq_of_src _ _
        | exact hB.eq_of_src _ _
  exact (Limits.IsZero.iff_id_eq_zero _).mpr h

/-- **Connecting map is an isomorphism when the middle homology vanishes.**

For a short exact sequence `S` of chain complexes (over `ModuleCat R`) and a
relation `c.Rel i j` in the chain-complex shape, if the homology of the middle
term `S.X₂` vanishes in degrees `i` and `j`, then the Mayer–Vietoris-type
connecting morphism `S.δ i j : H_i(X₃) → H_j(X₁)` is an isomorphism.

This is pure homological algebra: vanishing of `H_i(X₂)` forces `δ` to be a
monomorphism (by exactness at `H_i(X₃)`), and vanishing of `H_j(X₂)` forces `δ`
to be an epimorphism (by exactness at `H_j(X₁)`); `ModuleCat R` is balanced. -/
theorem isIso_shortExact_δ
    {S : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ)} (hS : S.ShortExact)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (h2i : IsZero (S.X₂.homology i)) (h2j : IsZero (S.X₂.homology j)) :
    IsIso (hS.δ i j hij) := by
  have hmono : Mono (hS.δ i j hij) :=
    (hS.homology_exact₃ i j hij).mono_g (h2i.eq_of_src _ _)
  have hepi : Epi (hS.δ i j hij) :=
    (hS.homology_exact₁ i j hij).epi_f (h2j.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-! ## The Mayer–Vietoris short exact sequence and its homology -/

/-- The Mayer–Vietoris short exact sequence of chain complexes for the cover
`{U, V}` (re-export of `mvShortComplex_shortExact`). -/
theorem mvShortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvShortComplex R U V hUV).ShortExact :=
  mvShortComplex_shortExact R U V hUV

/-- **Exactness at `H_n(U ∩ V)`** in the Mayer–Vietoris sequence:
`H_n(C_*^{U,V}(X)) →(δ) H_{n-1}(U ∩ V) →(incl) H_{n-1}(U) ⊕ H_{n-1}(V)`. -/
theorem mvHomology_exact_inter (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (ShortComplex.mk ((mvShortExact R U V hUV).δ i j hij)
      (HomologicalComplex.homologyMap (mvShortComplex R U V hUV).f j)
      ((mvShortExact R U V hUV).δ_comp i j hij)).Exact :=
  (mvShortExact R U V hUV).homology_exact₁ i j hij

/-- **Exactness at `H_n(U) ⊕ H_n(V)`** in the Mayer–Vietoris sequence:
`H_n(U ∩ V) → H_n(U) ⊕ H_n(V) → H_n(C_*^{U,V}(X))`. -/
theorem mvHomology_exact_sum (U V : Opens X) (hUV : U ⊔ V = ⊤) (i : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (mvShortComplex R U V hUV).f i)
      (HomologicalComplex.homologyMap (mvShortComplex R U V hUV).g i)
      (by rw [← HomologicalComplex.homologyMap_comp, (mvShortComplex R U V hUV).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (mvShortExact R U V hUV).homology_exact₂ i

/-- **Exactness at `H_n(C_*^{U,V}(X))`** in the Mayer–Vietoris sequence:
`H_n(U) ⊕ H_n(V) → H_n(C_*^{U,V}(X)) →(δ) H_{n-1}(U ∩ V)`. -/
theorem mvHomology_exact_X (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (mvShortComplex R U V hUV).g i)
      ((mvShortExact R U V hUV).δ i j hij)
      ((mvShortExact R U V hUV).comp_δ i j hij)).Exact :=
  (mvShortExact R U V hUV).homology_exact₃ i j hij

/-- Vanishing of `H_i(C_*(U))` and `H_i(C_*(V))` implies vanishing of the middle
homology `H_i(C_*(U) ⊕ C_*(V))` of the Mayer–Vietoris sequence. -/
theorem isZero_mvX₂_homology (U V : Opens X) (hUV : U ⊔ V = ⊤) (i : ℕ)
    (hU : IsZero ((subChainComplex R X (U : Set X)).homology i))
    (hV : IsZero ((subChainComplex R X (V : Set X)).homology i)) :
    IsZero ((mvShortComplex R U V hUV).X₂.homology i) := by
  let : Limits.PreservesBinaryBiproduct
      (subChainComplex R X (U : Set X)) (subChainComplex R X (V : Set X))
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) i) :=
    Limits.preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  have e : (mvShortComplex R U V hUV).X₂.homology i ≅
      (subChainComplex R X (U : Set X)).homology i
        ⊞ (subChainComplex R X (V : Set X)).homology i :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) i).mapBiprod
      (subChainComplex R X (U : Set X)) (subChainComplex R X (V : Set X))
  exact IsZero.of_iso (isZero_biprod_of_isZero hU hV) e

/-! ## The connecting isomorphism -/

/-- **The Mayer–Vietoris connecting isomorphism on small-chain homology.**

If the homology of `C_*(U)` and `C_*(V)` vanishes in degrees `i` and `j` (with
`c.Rel i j`), the connecting map gives an isomorphism
`H_i(C_*^{U,V}(X)) ≅ H_j(U ∩ V)`. -/
noncomputable def mvConnectingIso (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hUi : IsZero ((subChainComplex R X (U : Set X)).homology i))
    (hVi : IsZero ((subChainComplex R X (V : Set X)).homology i))
    (hUj : IsZero ((subChainComplex R X (U : Set X)).homology j))
    (hVj : IsZero ((subChainComplex R X (V : Set X)).homology j)) :
    (twoOpenCoverSmallChains R U V hUV).homology i
      ≅ (subChainComplex R X ((U : Set X) ∩ (V : Set X))).homology j :=
  have hIso : IsIso ((mvShortExact R U V hUV).δ i j hij) :=
    isIso_shortExact_δ R (mvShortExact R U V hUV) i j hij
      (isZero_mvX₂_homology R U V hUV i hUi hVi)
      (isZero_mvX₂_homology R U V hUV j hUj hVj)
  @asIso _ _ _ _ ((mvShortExact R U V hUV).δ i j hij) hIso

/-- **The singular Mayer–Vietoris connecting isomorphism.**

Using the small-simplices quasi-isomorphism to replace the homology
of the small-chain complex `C_*^{U,V}(X)` by the singular homology of `X`, the
connecting map yields an isomorphism `H_i(X) ≅ H_j(U ∩ V)` whenever the homology
of `C_*(U)` and `C_*(V)` vanishes in degrees `i` and `j`. -/
noncomputable def mvHomologyIso (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hUi : IsZero ((subChainComplex R X (U : Set X)).homology i))
    (hVi : IsZero ((subChainComplex R X (V : Set X)).homology i))
    (hUj : IsZero ((subChainComplex R X (U : Set X)).homology j))
    (hVj : IsZero ((subChainComplex R X (V : Set X)).homology j)) :
    (singularChainComplex R X).homology i
      ≅ (subChainComplex R X ((U : Set X) ∩ (V : Set X))).homology j :=
  (smallChainsHomologyIso R X (twoSetCover U V hUV) i).symm
    ≪≫ mvConnectingIso R U V hUV i j hij hUi hVi hUj hVj

/-- **Sphere-ready corollary.** `H_{n+1}(X) ≅ H_n(U ∩ V)` whenever the homology of
`C_*(U)` and `C_*(V)` vanishes in degrees `n + 1` and `n` (which holds, for
instance, when `U` and `V` are contractible and `1 ≤ n`). This is the form used
in the inductive computation of sphere homology. -/
noncomputable def mvHomologyIsoSucc (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hUi : IsZero ((subChainComplex R X (U : Set X)).homology (n + 1)))
    (hVi : IsZero ((subChainComplex R X (V : Set X)).homology (n + 1)))
    (hUj : IsZero ((subChainComplex R X (U : Set X)).homology n))
    (hVj : IsZero ((subChainComplex R X (V : Set X)).homology n)) :
    (singularChainComplex R X).homology (n + 1)
      ≅ (subChainComplex R X ((U : Set X) ∩ (V : Set X))).homology n :=
  mvHomologyIso R U V hUV (n + 1) n (by simp [ComplexShape.down_Rel]) hUi hVi hUj hVj

end SphereOddDegree
