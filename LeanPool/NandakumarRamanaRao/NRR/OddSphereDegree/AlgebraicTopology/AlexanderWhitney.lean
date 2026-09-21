/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CupProductScaffolding
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Alexander–Whitney diagonal — combinatorial and simplex-level layer

This file develops the combinatorial and simplex-level groundwork for the Alexander–Whitney
(AW) chain diagonal

```text
Δ : C_•(X) → C_•(X) ⊗ C_•(X),
```

the chain-level ingredient underlying the singular cochain cup product. It uses the simplex
category, standard face maps, the singular simplicial set `TopCat.toSSet`, the singular chain
complex functor, and the monoidal structure supplied by `CupProductScaffolding.lean`.
The tensor-valued linearization and chain-map identity are developed in the related
Alexander–Whitney modules.

## Mathematical content

For a singular `n`-simplex `σ` (with `n = p + q`), the AW diagonal is

```text
Δ(σ) = Σ_{p+q=n} (front_p σ) ⊗ (back_q σ),
```

where:

* the **front `p`-face** `front_p σ` is the restriction of `σ` to the first
 `p+1` vertices `{0,…,p}`;
* the **back `q`-face** `back_q σ` is the restriction of `σ` to the last
 `q+1` vertices `{p,…,p+q}`.

These restrictions are induced by the order-preserving maps

```text
frontFace p q : ⦋p⦌ ⟶ ⦋p+q⦌ , i ↦ i (inclusion of an initial segment)
backFace p q : ⦋q⦌ ⟶ ⦋p+q⦌ , i ↦ i + p (inclusion of a final segment)
```

in `SimplexCategory`. The two faces **overlap in the single vertex `p`**
(`front`'s last vertex `=` `back`'s first vertex), which is the geometric content
of the diagonal.

## What this file supplies

1. **Front/back combinatorial face maps** `frontFace`, `backFace` in
 `SimplexCategory`, with their value lemmas, the overlap/matching identity
 `frontFace_last_eq_backFace_zero`, injectivity, and the two structural
 recursion identities
 `frontFace_succ` (adding a top vertex via `δ (last)`) and
 `backFace_succ_square` (the front-of-`δ₀` commuting square) that drive the
 eventual chain-map identity.
2. **Singular-simplex front/back restrictions** `frontSimplex`, `backSimplex`
 of a singular `(p+q)`-simplex, with their **naturality in the space**
 (`frontSimplex_naturality`, `backSimplex_naturality`).
3. **Degree bookkeeping** for `p + q = n` via `Finset.antidiagonal`
 (`awIndex`, `mem_awIndex`, `awIndex_add`).
4. **Tensor-complex target objects** `singularChainTensorSquare` (the chain-level
 `C_•(X) ⊗ C_•(X)`, the *codomain* of the AW diagonal) with its functorial
 pullback and `map_id`/`map_comp` laws — the chain-level analogue of the
 cochain tensor square already in `CupProductScaffolding.lean`.
5. **Object-level diagonal shape** `awPair` — the `(p,q)`-component
 `σ ↦ (front_p σ, back_q σ)` of the (un-linearized) AW diagonal, natural in the
 space (`awPair_naturality`).
-/

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial SimplexCategory

namespace SphereOddDegree.AlexanderWhitney

/-! ## 1. Front and back combinatorial face maps -/

/-- The **front `p`-face inclusion** `⦋p⦌ ⟶ ⦋p+q⦌` in `SimplexCategory`,
sending vertex `i` to `i` — the inclusion of the initial segment `{0,…,p}`
of `{0,…,p+q}`. -/
def frontFace (p q : ℕ) : (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => Fin.castLE (by lia) i, fun a b h => by
    simpa [Fin.castLE] using h⟩

/-- The **back `q`-face inclusion** `⦋q⦌ ⟶ ⦋p+q⦌` in `SimplexCategory`,
sending vertex `i` to `i + p` — the inclusion of the final segment `{p,…,p+q}`
of `{0,…,p+q}`. -/
def backFace (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨i.val + p, by have := i.isLt; lia⟩, fun a b h => by
    simp only [Fin.mk_le_mk]; exact Nat.add_le_add_right h p⟩

@[simp] lemma frontFace_apply (p q : ℕ) (i : Fin (p + 1)) :
    ((frontFace p q).toOrderHom i : ℕ) = i.val := rfl

@[simp] lemma backFace_apply (p q : ℕ) (i : Fin (q + 1)) :
    ((backFace p q).toOrderHom i : ℕ) = i.val + p := rfl

/-- The last vertex of the front `p`-face is `p`. -/
lemma frontFace_last (p q : ℕ) : ((frontFace p q).toOrderHom (Fin.last p) : ℕ) = p := rfl

/-- The first vertex of the front `p`-face is `0`. -/
lemma frontFace_zero (p q : ℕ) : ((frontFace p q).toOrderHom 0 : ℕ) = 0 := rfl

/-- The first vertex of the back `q`-face is `p`. -/
lemma backFace_zero (p q : ℕ) : ((backFace p q).toOrderHom 0 : ℕ) = p := by
  rw [backFace_apply]; simp

/-- The last vertex of the back `q`-face is `p + q`. -/
lemma backFace_last (p q : ℕ) : ((backFace p q).toOrderHom (Fin.last q) : ℕ) = p + q := by
  rw [backFace_apply, Fin.val_last]; lia

/-- **Overlap / matching identity.** The last vertex of the front `p`-face and
the first vertex of the back `q`-face are the *same* vertex `p` of `⦋p+q⦌`. This
single shared vertex is the geometric content of the Alexander–Whitney diagonal. -/
lemma frontFace_last_eq_backFace_zero (p q : ℕ) :
    (frontFace p q).toOrderHom (Fin.last p) = (backFace p q).toOrderHom 0 := by
  apply Fin.ext
  rw [frontFace_last, backFace_zero]

/-- The front face map is injective on vertices. -/
lemma frontFace_injective (p q : ℕ) :
    Function.Injective (frontFace p q).toOrderHom := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (Fin.val) h
  simp only [frontFace_apply] at hv
  exact hv

/-- The back face map is injective on vertices. -/
lemma backFace_injective (p q : ℕ) :
    Function.Injective (backFace p q).toOrderHom := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (Fin.val) h
  simp only [backFace_apply] at hv
  omega

/-- **Front recursion.** Extending the back length by one is the same as
post-composing the front face with the top face map `δ (last)`, i.e. adding the
new top vertex `p+q+1` that the front face never reaches. -/
lemma frontFace_succ (p q : ℕ) :
    frontFace p (q + 1) = frontFace p q ≫ SimplexCategory.δ (Fin.last (p + q + 1)) := by
  ext x : 3
  apply Fin.ext
  have hR : ((frontFace p q ≫ SimplexCategory.δ (Fin.last (p + q + 1))).toOrderHom x : ℕ)
      = x.val := by
    show ((Fin.last (p + q + 1)).succAbove ((frontFace p q).toOrderHom x) : ℕ) = x.val
    rw [Fin.succAbove_last]; rfl
  have hL : ((frontFace p (q + 1)).toOrderHom x : ℕ) = x.val := rfl
  omega

/-- **Back commuting square.** The bottom face map `δ 0` intertwines the back
faces `backFace p q` and `backFace p (q+1)`: both routes `⦋q⦌ ⟶ ⦋p+q+1⦌` send
`i ↦ i + p + 1`. This is the first-face simplicial identity for the back faces
that enters the chain-map identity of the AW diagonal. -/
lemma backFace_succ_square (p q : ℕ) :
    SimplexCategory.δ 0 ≫ backFace p (q + 1) = backFace p q ≫ SimplexCategory.δ 0 := by
  ext x : 3
  apply Fin.ext
  have hL : ((SimplexCategory.δ (0 : Fin (q + 2)) ≫ backFace p (q + 1)).toOrderHom x : ℕ)
      = x.val + 1 + p := by
    show ((backFace p (q + 1)).toOrderHom ((0 : Fin (q + 2)).succAbove x) : ℕ) = x.val + 1 + p
    rw [Fin.succAbove_zero, backFace_apply, Fin.val_succ]
  have hR : ((backFace p q ≫ SimplexCategory.δ (0 : Fin (p + q + 2))).toOrderHom x : ℕ)
      = x.val + p + 1 := by
    show ((0 : Fin (p + q + 2)).succAbove ((backFace p q).toOrderHom x) : ℕ) = x.val + p + 1
    rw [Fin.succAbove_zero, Fin.val_succ, backFace_apply]
  omega

/-! ## 2. Singular-simplex front/back restrictions

A singular `(p+q)`-simplex of a space `X` is an element of
`(TopCat.toSSet.obj X).obj (op ⦋p+q⦌)`. Restricting it along the front/back face
maps yields its front `p`-face and back `q`-face, the two tensor factors of the
`(p,q)`-component of the Alexander–Whitney diagonal. -/

/-- The **front `p`-face of a singular `(p+q)`-simplex** `σ`, obtained by
restricting `σ` along `frontFace p q`. -/
noncomputable def frontSimplex (X : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋p⦌ : SimplexCategory)) :=
  (TopCat.toSSet.obj X).map (frontFace p q).op σ

/-- The **back `q`-face of a singular `(p+q)`-simplex** `σ`, obtained by
restricting `σ` along `backFace p q`. -/
noncomputable def backSimplex (X : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋q⦌ : SimplexCategory)) :=
  (TopCat.toSSet.obj X).map (backFace p q).op σ

/-- **Naturality of the front face in the space.** A continuous map `f : X ⟶ Y`
commutes with taking front faces of singular simplices. This is naturality of the
singular simplicial set functor `TopCat.toSSet`. -/
lemma frontSimplex_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q⦌ : SimplexCategory))) :
    (TopCat.toSSet.map f).app (Opposite.op (⦋p⦌ : SimplexCategory)) (frontSimplex X p q σ)
      = frontSimplex Y p q
          ((TopCat.toSSet.map f).app (Opposite.op (⦋p + q⦌ : SimplexCategory)) σ) := by
  dsimp [frontSimplex]
  exact (NatTrans.naturality_apply (TopCat.toSSet.map f) (frontFace p q).op σ).symm

/-- **Naturality of the back face in the space.** A continuous map `f : X ⟶ Y`
commutes with taking back faces of singular simplices. -/
lemma backSimplex_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q⦌ : SimplexCategory))) :
    (TopCat.toSSet.map f).app (Opposite.op (⦋q⦌ : SimplexCategory)) (backSimplex X p q σ)
      = backSimplex Y p q
          ((TopCat.toSSet.map f).app (Opposite.op (⦋p + q⦌ : SimplexCategory)) σ) := by
  dsimp [backSimplex]
  exact (NatTrans.naturality_apply (TopCat.toSSet.map f) (backFace p q).op σ).symm

/-! ## 3. Degree bookkeeping for `p + q = n`

The Alexander–Whitney diagonal of an `n`-simplex is a sum over all splittings
`p + q = n`, i.e. over `Finset.antidiagonal n`. -/

/-- The **index set of the degree-`n` Alexander–Whitney diagonal**: all pairs
`(p, q)` with `p + q = n`, the bidegrees of the tensor summands. -/
def awIndex (n : ℕ) : Finset (ℕ × ℕ) := Finset.antidiagonal n

@[simp] lemma mem_awIndex {n : ℕ} {pq : ℕ × ℕ} : pq ∈ awIndex n ↔ pq.1 + pq.2 = n :=
  Finset.mem_antidiagonal

/-- Each summand bidegree `(p, q)` of the degree-`n` AW diagonal satisfies
`p + q = n`. -/
lemma awIndex_add {n : ℕ} {pq : ℕ × ℕ} (h : pq ∈ awIndex n) : pq.1 + pq.2 = n :=
  mem_awIndex.mp h

/-! ## 4. Tensor-complex target objects `C_•(X) ⊗ C_•(X)`

With the monoidal wiring of `CupProductScaffolding.lean` in place, the tensor
product of the singular *chain* complex with itself is a genuine
`ChainComplex (ModuleCat R) ℕ`. This is the **codomain** of the Alexander–Whitney
diagonal `Δ : C_•(X) → C_•(X) ⊗ C_•(X)`. -/

/-- The **tensor square of the singular chain complex** with coefficients in
`M : ModuleCat R`, i.e. `C_•(X; M) ⊗ C_•(X; M)` as a `ChainComplex (ModuleCat R) ℕ`.
This is the chain-level codomain of the Alexander–Whitney diagonal. -/
noncomputable def singularChainTensorSquare (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  MonoidalCategory.tensorObj
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj X)
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj X)

/-- The functorial pushforward on the chain tensor square: a continuous map
`f : X ⟶ Y` induces `f_# ⊗ f_#` on the tensor squares. -/
noncomputable def singularChainTensorSquareMap (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularChainTensorSquare R M X ⟶ singularChainTensorSquare R M Y :=
  MonoidalCategory.tensorHom (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map f)
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map f)

/-- Functoriality: the chain tensor-square pushforward preserves identities. -/
@[simp]
theorem singularChainTensorSquareMap_id (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    singularChainTensorSquareMap R M (𝟙 X) = 𝟙 _ := by
  rw [singularChainTensorSquareMap, (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M)).map_id]
  exact MonoidalCategory.id_tensorHom_id _ _

/-- Functoriality: the chain tensor-square pushforward preserves composition. -/
theorem singularChainTensorSquareMap_comp (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularChainTensorSquareMap R M (f ≫ g)
      = singularChainTensorSquareMap R M f ≫ singularChainTensorSquareMap R M g := by
  dsimp [singularChainTensorSquareMap]
  rw [Functor.map_comp]
  exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

/-- The tensor square of the singular `F₂`-chain complex, `C_•(X; F₂) ⊗ C_•(X; F₂)`. -/
noncomputable abbrev singularChainTensorSquareZMod2 (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  singularChainTensorSquare (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) X

/-! ## 5. Object-level Alexander–Whitney diagonal shape

The `(p, q)`-component of the (un-linearized) Alexander–Whitney diagonal sends a
singular `(p+q)`-simplex `σ` to the pair `(front_p σ, back_q σ)`. Summing the
linearizations of these pairs over `awIndex n` is the AW diagonal; the
linearization itself is the required input (see the module footer). -/

/-- The **`(p, q)`-component of the Alexander–Whitney diagonal**, at the level of
sets of simplices: a singular `(p+q)`-simplex `σ` maps to the pair of its front
`p`-face and back `q`-face. The genuine chain diagonal is the `R`-linearization
of the sum of these pairs over `awIndex (p+q)`. -/
noncomputable def awPair (X : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋p⦌ : SimplexCategory)) ×
      (TopCat.toSSet.obj X).obj (Opposite.op (⦋q⦌ : SimplexCategory)) :=
  (frontSimplex X p q σ, backSimplex X p q σ)

/-- **Naturality of the object-level AW diagonal component in the space.** -/
lemma awPair_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q⦌ : SimplexCategory))) :
    awPair Y p q ((TopCat.toSSet.map f).app (Opposite.op (⦋p + q⦌ : SimplexCategory)) σ)
      = (((TopCat.toSSet.map f).app (Opposite.op (⦋p⦌ : SimplexCategory))) (awPair X p q σ).1,
         ((TopCat.toSSet.map f).app (Opposite.op (⦋q⦌ : SimplexCategory))) (awPair X p q σ).2) := by
  ext
  · exact (frontSimplex_naturality f p q σ).symm
  · exact (backSimplex_naturality f p q σ).symm

end SphereOddDegree.AlexanderWhitney
