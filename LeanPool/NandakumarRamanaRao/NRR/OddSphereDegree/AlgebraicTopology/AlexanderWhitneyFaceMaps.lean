/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CupProduct

/-!
# Alexander–Whitney face maps and degree bookkeeping

This file finishes the **formalized** combinatorial / simplex-level setup needed
for the Alexander–Whitney chain-map (Leibniz) identity

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ (over ZMod 2 : δ(φ⌣ψ) = δφ⌣ψ + φ⌣δψ)
```

to be proved in the following modules. It builds directly on the front/back face
maps `frontFace`, `backFace` of `AlexanderWhitney.lean`, and on the cochain cup
product `cochainCup` of `CupProduct.lean`. Every statement below is proved.

## What this file supplies

The Leibniz proof telescopes the singular coboundary `(δφ)(σ) = Σ_i (-1)^i
φ(d_i σ)` over the front/back faces. The combinatorial heart is the interaction
of the simplicial face maps `SimplexCategory.δ k` with the front/back inclusions,
split by whether the deleted vertex index `k` is `≤ p` (an *internal front* face)
or `> p` (an *internal back* face), together with the two *endpoint* faces whose
contributions cancel. This file proves every such identity.

1. **Value lemmas** `succAbove_val'`, `δ_toOrderHom_val`, `awCastLeft_val`:
 pointwise (vertex-value) descriptions of `Fin.succAbove`, the face map
 `SimplexCategory.δ`, and the degree-cast isomorphism.

2. **Degree bookkeeping** `aw_degree_left_succ`, `aw_degree_right_succ`,
 `cochainCup_degree`, and the object-level cast `awDegLeft` / `awCastLeft`
 bridging `⦋p+1+q⦌` and `⦋p+q+1⦌` (these are propositionally but **not**
 definitionally equal, while `⦋p+(q+1)⦌ = ⦋p+q+1⦌` *is* definitional).

3. **Internal face-composition identities**
 `frontFace_comp_δ_of_le`, `frontFace_comp_δ_of_gt`,
 `backFace_comp_δ_of_le`, `backFace_comp_δ_of_gt`:
 for a deleted vertex `k : Fin (p+q+2)` of a `(p+q+1)`-simplex, how the front
 `p`-face / back `q`-face of the `k`-th boundary face is expressed via a
 front/back face of `σ` itself, with the `k ≤ p` vs `p < k` split.

4. **Endpoint identities** `aw_endpoint_front`, `aw_endpoint_back` and their
 combination `aw_internal_face_cancel_pair`: the two boundary faces (the top
 face of the front, and the bottom face of the back) that produce the *same*
 front/back restriction pair `(frontFace p (q+1), backFace (p+1) q)`, hence
 cancel in the Leibniz sum.

5. **Simplex-level corollaries** `faceSimplex`, `frontSimplex_faceSimplex_of_gt`,
 `backSimplex_faceSimplex_of_le`: the cast-free restriction identities on
 singular simplices that the project plugs directly into the cochain computation.

## Sign convention

The combinatorial identities here are sign-free; the Koszul signs `(-1)^i` enter
only at the cochain coboundary level. Over `ZMod 2` all signs are
`1`, so the same identities give the characteristic-two Leibniz rule with no
extra work.
-/

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial SimplexCategory

namespace SphereOddDegree.AlexanderWhitney

/-! ## 1. Value lemmas for `Fin.succAbove` and the face map -/

/-- The vertex value of `Fin.succAbove k i`: it is `i` if `i < k` and `i + 1`
otherwise. This is the arithmetic content of "delete the `k`-th vertex". -/
theorem succAbove_val' (n : ℕ) (k : Fin (n + 1)) (i : Fin n) :
    (k.succAbove i : ℕ) = if i.val < k.val then i.val else i.val + 1 := by
  rcases lt_or_ge i.castSucc k with h | h
  · rw [Fin.succAbove_of_castSucc_lt k i h, Fin.val_castSucc, ite_eq_left]; exact h
  · rw [Fin.succAbove_of_le_castSucc k i h, Fin.val_succ, ite_eq_right]
    simp only [Fin.le_def, Fin.val_castSucc] at h; omega

/-- The vertex value of the face map `SimplexCategory.δ k` applied to a vertex `x`:
it deletes the `k`-th vertex, sending `x` to `x` if `x < k` and to `x + 1`
otherwise. -/
@[simp] lemma δ_toOrderHom_val {n : ℕ} (k : Fin (n + 2)) (x : Fin (n + 1)) :
    ((SimplexCategory.δ k).toOrderHom x : ℕ) = if x.val < k.val then x.val else x.val + 1 := by
  change (k.succAbove x : ℕ) = _; rw [succAbove_val']

/-! ## 2. Degree bookkeeping -/

/-- Degree arithmetic for the *left* (front) coboundary term: incrementing the
front degree `p` raises the total `(p+q)`-degree by one. Stated as `p+1+q`
(the degree of `δφ ⌣ ψ`) equals `(p+q)+1` (the degree of `δ(φ ⌣ ψ)`). -/
theorem aw_degree_left_succ (p q : ℕ) : p + 1 + q = p + q + 1 := by omega

/-- Degree arithmetic for the *right* (back) coboundary term: incrementing the
back degree `q` raises the total `(p+q)`-degree by one. Here `p+(q+1)` (the
degree of `φ ⌣ δψ`) is **definitionally** `(p+q)+1`. -/
theorem aw_degree_right_succ (p q : ℕ) : p + (q + 1) = p + q + 1 := rfl

/-- **Output / coboundary degree bookkeeping for the cup product.** The cup
product `cochainCup p q φ ψ` has output degree `p + q`, and the coboundary
`δ(φ ⌣ ψ)` lives in degree `(p+q)+1`, which equals both `(p+1)+q` (the degree of
`δφ ⌣ ψ`) and `p+(q+1)` (the degree of `φ ⌣ δψ`). This is the degree
compatibility that the Leibniz identity needs. -/
theorem cochainCup_degree (p q : ℕ) :
    (p + q) + 1 = (p + 1) + q ∧ (p + q) + 1 = p + (q + 1) :=
  ⟨(aw_degree_left_succ p q).symm, (aw_degree_right_succ p q).symm⟩

/-- The object-level degree equality `⦋p+1+q⦌ = ⦋p+q+1⦌` in `SimplexCategory`
(propositional, not definitional). -/
theorem awDegLeft (p q : ℕ) : (⦋p + 1 + q⦌ : SimplexCategory) = ⦋p + q + 1⦌ := by
  rw [Nat.succ_add]

/-- The degree-cast isomorphism `⦋p+1+q⦌ ⟶ ⦋p+q+1⦌`, used to bridge the
`δφ ⌣ ψ` summand (degree `(p+1)+q`) with the `δ(φ ⌣ ψ)` summand (degree
`(p+q)+1`). -/
def awCastLeft (p q : ℕ) : (⦋p + 1 + q⦌ : SimplexCategory) ⟶ ⦋p + q + 1⦌ :=
  eqToHom (awDegLeft p q)

/-- The degree cast `awCastLeft` is a relabelling: it preserves vertex values. -/
@[simp] lemma awCastLeft_val (p q : ℕ) (x : Fin (p + 1 + q + 1)) :
    (((awCastLeft p q).toOrderHom x : Fin (p + q + 1 + 1)) : ℕ) = x.val := by
  rw [awCastLeft, SimplexCategory.eqToHom_toOrderHom (awDegLeft p q)]; rfl

/-! ## 3. Internal face-composition identities

For a `(p+q+1)`-simplex `σ`, deleting its `k`-th vertex (`k : Fin (p+q+2)`)
gives a `(p+q)`-simplex `d_k σ`. The front `p`-face and back `q`-face of `d_k σ`
are computed below by composing `frontFace`/`backFace` with `SimplexCategory.δ k`
in `SimplexCategory`, split according to whether `k ≤ p` (deleted vertex lies in
the front block) or `p < k` (deleted vertex lies in the back block). -/

/-- **Internal front face, `k ≤ p`.** Deleting a vertex `k ≤ p` from `σ` and then
taking the front `p`-face is the same as taking the front `(p+1)`-face of `σ` and
then deleting vertex `k` (reindexed into `⦋p⦌ ⟶ ⦋p+1⦌`), up to the degree cast. -/
theorem frontFace_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2)) (hk : k.val ≤ p) :
    frontFace p q ≫ SimplexCategory.δ k
      = SimplexCategory.δ (⟨k.val, by omega⟩ : Fin (p + 2)) ≫ frontFace (p + 1) q
        ≫ awCastLeft p q := by
  ext x : 3; apply Fin.ext
  change ((SimplexCategory.δ k).toOrderHom ((frontFace p q).toOrderHom x) : ℕ)
     = (((awCastLeft p q).toOrderHom
          ((frontFace (p + 1) q).toOrderHom
            ((SimplexCategory.δ (⟨k.val, by omega⟩ : Fin (p + 2))).toOrderHom x))) : ℕ)
  rw [awCastLeft_val, δ_toOrderHom_val, frontFace_apply, frontFace_apply, δ_toOrderHom_val]

/-- **Internal front face, `p < k`.** Deleting a vertex `k > p` from `σ` does not
disturb the front `p`-block, so the front `p`-face of `d_k σ` equals the front
`p`-face of `σ` (now viewed inside the `(p+(q+1))`-simplex `σ`). -/
theorem frontFace_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2)) (hk : p < k.val) :
    frontFace p q ≫ SimplexCategory.δ k = frontFace p (q + 1) := by
  ext x : 3; apply Fin.ext
  change ((SimplexCategory.δ k).toOrderHom ((frontFace p q).toOrderHom x) : ℕ)
     = ((frontFace p (q + 1)).toOrderHom x : ℕ)
  rw [δ_toOrderHom_val, frontFace_apply, frontFace_apply]
  have hx : x.val < p + 1 := x.isLt
  split_ifs with h
  · rfl
  · exfalso; omega

/-- **Internal back face, `k ≤ p`.** Deleting a vertex `k ≤ p` from `σ` does not
disturb the back `q`-block (its vertices are `≥ p`), so the back `q`-face of
`d_k σ` equals the back `q`-face of `σ` with the block shifted by one
(`backFace (p+1) q`), up to the degree cast. -/
theorem backFace_comp_δ_of_le (p q : ℕ) (k : Fin (p + q + 2)) (hk : k.val ≤ p) :
    backFace p q ≫ SimplexCategory.δ k
      = backFace (p + 1) q ≫ awCastLeft p q := by
  ext x : 3; apply Fin.ext
  change ((SimplexCategory.δ k).toOrderHom ((backFace p q).toOrderHom x) : ℕ)
     = (((awCastLeft p q).toOrderHom ((backFace (p + 1) q).toOrderHom x)) : ℕ)
  rw [awCastLeft_val, δ_toOrderHom_val, backFace_apply, backFace_apply]
  rw [ite_eq_right (by have := x.isLt; omega)]; omega

/-- **Internal back face, `p < k`.** Deleting a vertex `k > p` from `σ` and then
taking the back `q`-face is the same as taking the back `q`-face of the
`(p+(q+1))`-simplex `σ` and then deleting vertex `k - p` (reindexed into
`⦋q⦌ ⟶ ⦋q+1⦌`). -/
theorem backFace_comp_δ_of_gt (p q : ℕ) (k : Fin (p + q + 2)) (hk : p < k.val) :
    backFace p q ≫ SimplexCategory.δ k
      = SimplexCategory.δ (⟨k.val - p, by have := k.isLt; omega⟩ : Fin (q + 2))
          ≫ backFace p (q + 1) := by
  ext x : 3; apply Fin.ext
  change ((SimplexCategory.δ k).toOrderHom ((backFace p q).toOrderHom x) : ℕ)
     = ((backFace p (q + 1)).toOrderHom
          ((SimplexCategory.δ (⟨k.val - p, by have := k.isLt; omega⟩ : Fin (q + 2))).toOrderHom x) : ℕ)
  rw [δ_toOrderHom_val, backFace_apply, backFace_apply, δ_toOrderHom_val]
  have hf : (⟨k.val - p, by have := k.isLt; omega⟩ : Fin (q + 2)).val = k.val - p := rfl
  rw [hf]
  have hx : x.val < q + 1 := x.isLt
  by_cases hc : x.val + p < k.val
  · rw [ite_eq_left hc, ite_eq_left (by omega)]
  · rw [ite_eq_right hc, ite_eq_right (by omega)]; omega

/-! ## 4. Endpoint identities and their cancellation

In the Leibniz sum the term `i = p+1` of `δφ ⌣ ψ` and the term `j = 0` of
`φ ⌣ δψ` both produce the restriction pair `(frontFace p (q+1), backFace (p+1) q)`
(up to the degree cast), with opposite Koszul signs, and so cancel. The two
identities below witness exactly this matching. -/

/-- **Front endpoint.** Deleting the *top* vertex of the front `(p+1)`-face
recovers the front `p`-face: `δ (last) ≫ frontFace (p+1) q ≫ cast = frontFace p
(q+1)`. -/
theorem aw_endpoint_front (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ frontFace (p + 1) q ≫ awCastLeft p q
      = frontFace p (q + 1) := by
  ext x : 3; apply Fin.ext
  change (((awCastLeft p q).toOrderHom
          ((frontFace (p + 1) q).toOrderHom
            ((SimplexCategory.δ (Fin.last (p + 1))).toOrderHom x))) : ℕ)
     = ((frontFace p (q + 1)).toOrderHom x : ℕ)
  rw [awCastLeft_val, frontFace_apply, δ_toOrderHom_val, frontFace_apply]
  rw [Fin.val_last]
  split_ifs <;> omega

/-- **Back endpoint.** Deleting the *bottom* vertex of the back `(q+1)`-face
recovers the back `q`-face (block shifted by one): `δ 0 ≫ backFace p (q+1) =
backFace (p+1) q ≫ cast`. -/
theorem aw_endpoint_back (p q : ℕ) :
    SimplexCategory.δ 0 ≫ backFace p (q + 1)
      = backFace (p + 1) q ≫ awCastLeft p q := by
  ext x : 3; apply Fin.ext
  change ((backFace p (q + 1)).toOrderHom ((SimplexCategory.δ (0 : Fin (q + 2))).toOrderHom x) : ℕ)
     = (((awCastLeft p q).toOrderHom ((backFace (p + 1) q).toOrderHom x)) : ℕ)
  rw [awCastLeft_val, backFace_apply, backFace_apply, δ_toOrderHom_val]
  split_ifs with h
  · exfalso; simp only [Fin.val_zero] at h; omega
  · omega

/-- **Endpoint cancellation pair.** The front endpoint (top face of the front
`(p+1)`-block) and the back endpoint (bottom face of the back `(q+1)`-block)
produce the *same* front/back restriction pair `(frontFace p (q+1), backFace
(p+1) q)`. In the signed Leibniz sum these two contributions carry opposite signs
and cancel; over `ZMod 2` they coincide and cancel mod 2. -/
theorem aw_internal_face_cancel_pair (p q : ℕ) :
    (SimplexCategory.δ (Fin.last (p + 1)) ≫ frontFace (p + 1) q ≫ awCastLeft p q
        = frontFace p (q + 1))
      ∧ (SimplexCategory.δ 0 ≫ backFace p (q + 1)
          = backFace (p + 1) q ≫ awCastLeft p q) :=
  ⟨aw_endpoint_front p q, aw_endpoint_back p q⟩

/-! ## 5. Simplex-level restriction corollaries

Applying `(TopCat.toSSet.obj X).map` to the cast-free face-composition identities
gives the restriction identities on singular simplices that the cochain
computation of the project uses directly. The two `k > p` cases (front
and back) are cast-free (no degree relabelling), so they are recorded here in
their cleanest form. The cast-involving (`k ≤ p`, endpoint) cases are obtained in
the project by applying `(TopCat.toSSet.obj X).map` to the morphism identities of
§3–§4. -/

/-- The **`k`-th boundary face** of a singular `(n+1)`-simplex `σ`, obtained by
restricting `σ` along `SimplexCategory.δ k`. -/
noncomputable def faceSimplex (X : TopCat.{0}) (n : ℕ) (k : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n + 1⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌ : SimplexCategory)) :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ k).op σ

/-- **Simplex-level internal front face, `p < k`.** The front `p`-face of the
`k`-th boundary face of `σ` (for `k > p`) equals the front `p`-face of `σ`. -/
theorem frontSimplex_faceSimplex_of_gt (X : TopCat.{0}) (p q : ℕ) (k : Fin (p + q + 2))
    (hk : p < k.val)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + 1⦌ : SimplexCategory))) :
    frontSimplex X p q (faceSimplex X (p + q) k σ) = frontSimplex X p (q + 1) σ := by
  unfold frontSimplex faceSimplex
  rw [← Functor.map_comp_apply, ← op_comp, frontFace_comp_δ_of_gt p q k hk]

/-- **Simplex-level internal back face, `p < k`.** The back `q`-face of the `k`-th
boundary face of `σ` (for `k > p`) equals the `(k-p)`-th boundary face of the
back `(q+1)`-face of `σ`. -/
theorem backSimplex_faceSimplex_of_gt (X : TopCat.{0}) (p q : ℕ) (k : Fin (p + q + 2))
    (hk : p < k.val)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋p + q + 1⦌ : SimplexCategory))) :
    backSimplex X p q (faceSimplex X (p + q) k σ)
      = faceSimplex X q (⟨k.val - p, by have := k.isLt; omega⟩ : Fin (q + 2))
          (backSimplex X p (q + 1) σ) := by
  unfold backSimplex faceSimplex
  rw [← Functor.map_comp_apply, ← op_comp, backFace_comp_δ_of_gt p q k hk,
    op_comp, Functor.map_comp_apply]

end SphereOddDegree.AlexanderWhitney
