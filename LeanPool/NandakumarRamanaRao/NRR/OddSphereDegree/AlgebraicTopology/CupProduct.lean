/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AlexanderWhitney

/-!
# Cochain-level singular cup product (Alexander–Whitney formula)

This file builds a **genuine, formalized** cochain-level singular cup product
from the Alexander–Whitney front/back faces of `AlexanderWhitney.lean`. There are

## What is and is not here

Pinned Mathlib (`v4.28.0`, commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`) has **no** cup product. The genuine
*topological* input — the Alexander–Whitney front/back faces — is supplied by
`AlexanderWhitney.lean`. Using the definitional facts

* a singular chain group in degree `n` is the coproduct
 `C_n(X) = ∐_{σ : n-simplex} R` (`rfl`), so an `R`-linear map out of it is
 determined by its values on the generators (`cochain_ext`);
* a singular cochain in degree `p` is exactly a morphism `C_p(X) ⟶ R` (`rfl`);
* the pullback of a cochain is precomposition with the singular chain map (`rfl`),

we define the **cochain cup product** by the classical Alexander–Whitney formula

```text
(φ ⌣ ψ)(σ) = φ(front_p σ) · ψ(back_q σ) (σ a (p+q)-simplex)
```

with coefficients in the ring `R` itself (`M = R`, which covers the downstream
`R = ZMod 2` case). The operation is genuine, `R`-bilinear, natural in the space,
strictly unital on the right, and assembled into degree-`n` powers of a
degree-one cochain.

**What is NOT here (the exact required input).** The descent to *cohomology*
(`H^p × H^q → H^{p+q}`) requires the Leibniz / coboundary identity

```text
δ(φ ⌣ ψ) = (δφ) ⌣ ψ + (-1)^p φ ⌣ (δψ),
```

equivalently that the assembled cochain map `C^•(X) ⊗ C^•(X) → C^•(X)` is a
morphism of cochain complexes. That identity is the standard telescoping argument
over the front/back simplicial identities
(`frontFace_last_eq_backFace_zero`, `frontFace_succ`, `backFace_succ_square`); it
is **not** proved here, so no cohomology-level `cup` is introduced (per the
project's no-unsupported-declarations policy). See the module footer and

## Coefficients

Everything is stated for a general `CommRing R`, with coefficients in `R` itself
(`ModuleCat.of R R`). The `ZMod 2` specializations (`cochainCupZMod2`, …) are thin
abbreviations; over `ZMod 2` the Koszul sign in the Leibniz rule is trivial.
-/

open CategoryTheory AlgebraicTopology Limits SphereOddDegree.AlexanderWhitney

namespace SphereOddDegree

/-! ## 0. Singular simplices and cochains as concrete objects -/

/-- The set of singular `n`-simplices of a space `Z` (an element of the singular
simplicial set in degree `n`). -/
abbrev singularSimplices (Z : TopCat.{0}) (n : ℕ) :=
  (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk n))

/-- A singular `p`-cochain of `Z` with coefficients in the ring `R`: an `R`-linear
map from the singular chain group `C_p(Z) = ∐_{σ} R` to `R`. This is
definitionally the degree-`p` object of the singular cochain complex with
coefficients in `ModuleCat.of R R`. -/
abbrev singularCochainGroup (R : Type) [CommRing R] (Z : TopCat.{0}) (p : ℕ) :=
  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj Z).X p
    ⟶ ModuleCat.of R R

/-! ## 1. Evaluation of a cochain on a simplex -/

/-- Evaluate a singular `p`-cochain `φ` on a singular `p`-simplex `τ`, i.e. on the
basis chain `τ` (the image of `1 ∈ R` under the coproduct inclusion at `τ`). -/
noncomputable def cochainEval {R : Type} [CommRing R] {Z : TopCat.{0}} (p : ℕ)
    (φ : singularCochainGroup R Z p) (τ : singularSimplices Z p) : R :=
  φ.hom ((Sigma.ι (fun (_ : singularSimplices Z p) => ModuleCat.of R R) τ).hom (1 : R))

/-- **Cochain extensionality.** Two `p`-cochains are equal iff they agree on every
singular `p`-simplex. (The chain group is a coproduct of copies of `R`, so a map
out of it is determined by its values on the generators.) -/
theorem cochain_ext {R : Type} [CommRing R] {Z : TopCat.{0}} {p : ℕ}
    {φ ψ : singularCochainGroup R Z p}
    (h : ∀ τ, cochainEval p φ τ = cochainEval p ψ τ) : φ = ψ := by
  apply Sigma.hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have ht := h τ
  dsimp [cochainEval] at ht
  exact ht

@[simp] theorem cochainEval_add {R : Type} [CommRing R] {Z : TopCat.{0}} (p : ℕ)
    (φ ψ : singularCochainGroup R Z p) (τ : singularSimplices Z p) :
    cochainEval p (φ + ψ) τ = cochainEval p φ τ + cochainEval p ψ τ := rfl

@[simp] theorem cochainEval_smul {R : Type} [CommRing R] {Z : TopCat.{0}} (p : ℕ)
    (s : R) (φ : singularCochainGroup R Z p) (τ : singularSimplices Z p) :
    cochainEval p (s • φ) τ = s * cochainEval p φ τ := rfl

@[simp] theorem cochainEval_zero {R : Type} [CommRing R] {Z : TopCat.{0}} (p : ℕ)
    (τ : singularSimplices Z p) :
    cochainEval p (0 : singularCochainGroup R Z p) τ = 0 := rfl

/-! ## 2. The cochain cup product -/

/-- The **cochain-level cup product** `⌣ : C^p(Z; R) → C^q(Z; R) → C^{p+q}(Z; R)`,
defined by the Alexander–Whitney formula `(φ ⌣ ψ)(σ) = φ(front_p σ)·ψ(back_q σ)`.
Built degree-wise out of the singular-chain coproduct via `Limits.Sigma.desc`. -/
noncomputable def cochainCup {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R Z p) (ψ : singularCochainGroup R Z q) :
    singularCochainGroup R Z (p + q) :=
  Sigma.desc (fun (σ : singularSimplices Z (p + q)) =>
    ModuleCat.ofHom ((cochainEval p φ (frontSimplex Z p q σ)
      * cochainEval q ψ (backSimplex Z p q σ)) • (LinearMap.id : R →ₗ[R] R)))

/-- **Defining formula of the cup product.** The value of `φ ⌣ ψ` on a singular
`(p+q)`-simplex `σ` is `φ(front_p σ) · ψ(back_q σ)`. -/
@[simp] theorem cochainCup_eval {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R Z p) (ψ : singularCochainGroup R Z q)
    (σ : singularSimplices Z (p + q)) :
    cochainEval (p + q) (cochainCup p q φ ψ) σ
      = cochainEval p φ (frontSimplex Z p q σ) * cochainEval q ψ (backSimplex Z p q σ) := by
  dsimp [cochainEval, cochainCup]
  have h := congrArg (fun (f : ModuleCat.of R R ⟶ ModuleCat.of R R) => f.hom (1 : R))
    (Sigma.ι_desc (fun (σ : singularSimplices Z (p + q)) =>
      ModuleCat.ofHom ((cochainEval p φ (frontSimplex Z p q σ)
        * cochainEval q ψ (backSimplex Z p q σ)) • (LinearMap.id : R →ₗ[R] R))) σ)
  dsimp at h
  have hone : cochainEval p φ (frontSimplex Z p q σ) * cochainEval q ψ (backSimplex Z p q σ) * (1 : R)
      = cochainEval p φ (frontSimplex Z p q σ) * cochainEval q ψ (backSimplex Z p q σ) := mul_one _
  exact hone ▸ h

/-! ### Bilinearity -/

/-- The cup product is additive in its left argument. -/
theorem cochainCup_add_left {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (φ φ' : singularCochainGroup R Z p) (ψ : singularCochainGroup R Z q) :
    cochainCup p q (φ + φ') ψ = cochainCup p q φ ψ + cochainCup p q φ' ψ := by
  apply cochain_ext; intro σ
  simp only [cochainCup_eval, cochainEval_add]
  ring

/-- The cup product is additive in its right argument. -/
theorem cochainCup_add_right {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R Z p) (ψ ψ' : singularCochainGroup R Z q) :
    cochainCup p q φ (ψ + ψ') = cochainCup p q φ ψ + cochainCup p q φ ψ' := by
  apply cochain_ext; intro σ
  simp only [cochainCup_eval, cochainEval_add]
  ring

/-- The cup product is `R`-linear in its left argument. -/
theorem cochainCup_smul_left {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (s : R) (φ : singularCochainGroup R Z p) (ψ : singularCochainGroup R Z q) :
    cochainCup p q (s • φ) ψ = s • cochainCup p q φ ψ := by
  apply cochain_ext; intro σ
  simp only [cochainCup_eval, cochainEval_smul]
  ring

/-- The cup product is `R`-linear in its right argument. -/
theorem cochainCup_smul_right {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (s : R) (φ : singularCochainGroup R Z p) (ψ : singularCochainGroup R Z q) :
    cochainCup p q φ (s • ψ) = s • cochainCup p q φ ψ := by
  apply cochain_ext; intro σ
  simp only [cochainCup_eval, cochainEval_smul]
  ring

@[simp] theorem cochainCup_zero_left {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (ψ : singularCochainGroup R Z q) :
    cochainCup p q (0 : singularCochainGroup R Z p) ψ = 0 := by
  apply cochain_ext; intro σ
  simp [cochainCup_eval, cochainEval_zero]

@[simp] theorem cochainCup_zero_right {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R Z p) :
    cochainCup p q φ (0 : singularCochainGroup R Z q) = 0 := by
  apply cochain_ext; intro σ
  simp [cochainCup_eval, cochainEval_zero]

/-! ## 3. Pullback of cochains and naturality of the cup product -/

/-- The pullback `f^*` of a singular `p`-cochain along a continuous map
`f : X ⟶ Y`, i.e. precomposition with the induced singular chain map. -/
noncomputable def cochainPullback {R : Type} [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (p : ℕ) (φ : singularCochainGroup R Y p) : singularCochainGroup R X p :=
  (((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).f p).hom φ

/-- The singular chain map sends the generator at a simplex `τ` to the generator at
its pushforward `f ∘ τ`. -/
theorem chainmap_generator {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (τ : singularSimplices X n) :
    (Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) τ)
      ≫ ((((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f n)
      = Sigma.ι (fun (_ : singularSimplices Y n) => ModuleCat.of R R)
          ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) τ) :=
  @SSet.ι_chainComplexMap_f (ModuleCat R) _ _ _ (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f) (ModuleCat.of R R) n τ

/-- **Pullback evaluation.** `(f^* φ)(τ) = φ(f ∘ τ)`. -/
theorem cochainPullback_eval {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (p : ℕ) (φ : singularCochainGroup R Y p) (τ : singularSimplices X p) :
    cochainEval p (cochainPullback f p φ) τ
      = cochainEval p φ ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk p)) τ) := by
  dsimp [cochainEval, cochainPullback]
  have h1 := chainmap_generator f p τ (R := R)
  have h2 := congrArg (· ≫ φ) h1
  have h3 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom (1 : R)) h2
  dsimp at h3
  exact h3

/-- **Naturality of the cup product (cochain level).**
`f^*(φ ⌣ ψ) = (f^* φ) ⌣ (f^* ψ)`. This is the cochain-level substrate for the
eventual cohomology-level `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem cochainCup_naturality {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (p q : ℕ) (φ : singularCochainGroup R Y p) (ψ : singularCochainGroup R Y q) :
    cochainPullback f (p + q) (cochainCup p q φ ψ)
      = cochainCup p q (cochainPullback f p φ) (cochainPullback f q ψ) := by
  apply cochain_ext; intro σ
  rw [cochainCup_eval, cochainPullback_eval, cochainCup_eval,
    cochainPullback_eval, cochainPullback_eval,
    frontSimplex_naturality f p q σ, backSimplex_naturality f p q σ]

/-! ## 4. The unit cochain and right unitality -/

/-- The **unit cochain** `1 ∈ C^0(Z; R)`: the augmentation cochain taking the
value `1` on every singular `0`-simplex. -/
noncomputable def cochainOne {R : Type} [CommRing R] {Z : TopCat.{0}} :
    singularCochainGroup R Z 0 :=
  Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R))

@[simp] theorem cochainOne_eval {R : Type} [CommRing R] {Z : TopCat.{0}}
    (τ : singularSimplices Z 0) : cochainEval 0 (cochainOne (R := R) (Z := Z)) τ = 1 := by
  unfold cochainEval cochainOne
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (Sigma.ι_desc (fun (_ : singularSimplices Z 0) => 𝟙 (ModuleCat.of R R)) τ)) (1 : R)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans (by simp)

/-- The front `p`-face inclusion with empty back part is the identity, so the front
`p`-face of a `p`-simplex is the simplex itself. -/
@[simp] theorem frontSimplex_q_zero {Z : TopCat.{0}} (p : ℕ)
    (σ : singularSimplices Z (p + 0)) :
    frontSimplex Z p 0 σ = σ := by
  have hf : frontFace p 0 = 𝟙 (SimplexCategory.mk p) := by
    ext x : 3
    apply Fin.ext
    rfl
  unfold frontSimplex
  rw [hf]
  simp

/-- **Right unitality.** `φ ⌣ 1 = φ`. -/
@[simp] theorem cochainCup_one {R : Type} [CommRing R] {Z : TopCat.{0}} (p : ℕ)
    (φ : singularCochainGroup R Z p) :
    cochainCup p 0 φ (cochainOne (R := R) (Z := Z)) = φ := by
  apply cochain_ext; intro σ
  rw [cochainCup_eval, cochainOne_eval, mul_one, frontSimplex_q_zero]
  rfl

/-! ## 5. Powers of a degree-one cochain -/

/-- The `n`-th cup power `φ^{⌣ n} ∈ C^n(Z; R)` of a degree-one cochain
`φ ∈ C^1(Z; R)`, defined by `φ^0 = 1` and `φ^{n+1} = φ^n ⌣ φ`. This is the
cochain-level scaffolding for the powers `αⁿ` of a degree-one cohomology class. -/
noncomputable def cochainPow {R : Type} [CommRing R] {Z : TopCat.{0}}
    (φ : singularCochainGroup R Z 1) : (n : ℕ) → singularCochainGroup R Z n
  | 0 => cochainOne
  | (n + 1) => cochainCup n 1 (cochainPow φ n) φ

@[simp] theorem cochainPow_zero {R : Type} [CommRing R] {Z : TopCat.{0}}
    (φ : singularCochainGroup R Z 1) :
    cochainPow φ 0 = cochainOne := rfl

@[simp] theorem cochainPow_succ {R : Type} [CommRing R] {Z : TopCat.{0}}
    (φ : singularCochainGroup R Z 1) (n : ℕ) :
    cochainPow φ (n + 1) = cochainCup n 1 (cochainPow φ n) φ := rfl

/-- **Naturality of powers (cochain level).** `f^*(φ^n) = (f^* φ)^n`. -/
theorem cochainPow_naturality {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (φ : singularCochainGroup R Y 1) (n : ℕ) :
    cochainPullback f n (cochainPow φ n) = cochainPow (cochainPullback f 1 φ) n := by
  induction n with
  | zero =>
      apply cochain_ext; intro σ
      simp [cochainPullback_eval]
  | succ n ih =>
      rw [cochainPow_succ, cochainPow_succ, cochainCup_naturality, ih]

/-! ## 6. `ZMod 2` specializations

The downstream `RPⁿ` cohomology computation uses `ZMod 2` coefficients. These are
thin abbreviations of the general definitions. -/

/-- The cochain cup product with `ZMod 2` coefficients. -/
noncomputable abbrev cochainCupZMod2 {Z : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Z p) (ψ : singularCochainGroup (ZMod 2) Z q) :
    singularCochainGroup (ZMod 2) Z (p + q) :=
  cochainCup p q φ ψ

/-- The unit cochain with `ZMod 2` coefficients. -/
noncomputable abbrev cochainOneZMod2 {Z : TopCat.{0}} :
    singularCochainGroup (ZMod 2) Z 0 :=
  cochainOne

/-- Cup powers of a degree-one cochain with `ZMod 2` coefficients. -/
noncomputable abbrev cochainPowZMod2 {Z : TopCat.{0}}
    (φ : singularCochainGroup (ZMod 2) Z 1) (n : ℕ) :
    singularCochainGroup (ZMod 2) Z n :=
  cochainPow φ n

/-- Naturality of the `ZMod 2` cochain cup product. -/
theorem cochainCupZMod2_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y p) (ψ : singularCochainGroup (ZMod 2) Y q) :
    cochainPullback f (p + q) (cochainCupZMod2 p q φ ψ)
      = cochainCupZMod2 p q (cochainPullback f p φ) (cochainPullback f q ψ) :=
  cochainCup_naturality f p q φ ψ

end SphereOddDegree

/-!
## Cohomology-level descent

This file supplies the Alexander--Whitney cochain product, bilinearity, naturality, unit, and
powers. The Leibniz identity and the induced cohomology product are implemented in
`CohomologyCupProduct.lean`, which exports `cupZMod2`, its naturality, and cup powers.
-/
