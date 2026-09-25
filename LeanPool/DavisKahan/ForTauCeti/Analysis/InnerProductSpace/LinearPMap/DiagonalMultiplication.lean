/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The maximal diagonal multiplication operator on `ℓ²`

For a multiplier `d : ι → 𝕜` the map `x ↦ (dᵢ xᵢ)` is the archetypal *unbounded*
operator on `ℓ²(ι)`: it is everywhere defined as a formal expression, but the
result is square summable only on the subspace

`{x | (dᵢ xᵢ) ∈ ℓ²}`,

which is the largest domain on which it can be read as an operator at all.  This
module builds that operator as a Mathlib `LinearPMap` — the canonical carrier for
unbounded operators — and proves the two facts that make it usable:

* `lpDiagonal_isSymmetric`, coordinatewise, when every `dᵢ` is real; and
* `lpDiagonal_isSelfAdjoint`, the statement that the maximal domain is *exactly*
  right — no larger domain carries a symmetric extension.

## Why maximality is the content

Symmetry is a one-line computation.  The work is the reverse domain inclusion
`A† ≤ A`, and the standard argument is coordinate extraction: test a putative
adjoint vector `y` against the standard basis vector `lp.single 2 i 1`, which is
finitely supported and therefore always in the domain.  The defining identity
`⟪A† y, x⟫ = ⟪y, A x⟫` then reads off the `i`-th coordinate of `A† y` as `dᵢ yᵢ`.
Since `A† y` is by construction a vector of `ℓ²`, the sequence `(dᵢ yᵢ)` is square
summable, which is precisely membership in the maximal domain.  So the domain was
never a modelling choice; it is forced.

Density of the domain comes from the same finitely supported vectors:
`lp.hasSum_single` writes every `f : ℓ²` as the limit of its coordinate partial
sums, each of which lies in the domain because it has finite support.

## Provenance

*New.*  Mathlib has `LinearPMap.adjoint` and the `lp` inner-product API, but no
diagonal or multiplication operator presented as a `LinearPMap`, and no
self-adjointness criterion for one.  The bounded companion in this library is
`TauCeti.diagOpLp` (`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/
DiagonalSequence.lean`), which requires a uniformly bounded multiplier; nothing
there survives the unbounded case, where the domain is the whole point.

Written for the Davis--Kahan 1970 Section 9 example, whose trial vector is in the
form domain of such an operator but not in its operator domain.
-/

@[expose] public section

open scoped InnerProductSpace ENNReal

namespace TauCeti
namespace LinearPMap

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]

-- `@[expose]`: `lpDiagonal_domain` and `lpDiagonal_apply` below are the whole API
-- of these two definitions, and both are definitional.  A consumer that wants the
-- domain of the operator to *be* the maximal domain — which is the point of the
-- construction — has to see through the `Submodule` and the `LinearPMap` bundle.
/-- **The maximal domain of the diagonal multiplication operator** with multiplier
`d`: the vectors whose coordinatewise product with `d` is still square summable. -/
@[expose]
def lpDiagonalDomain (d : ι → 𝕜) : Submodule 𝕜 (lp (fun _ : ι => 𝕜) 2) where
  carrier := {x | Memℓp (fun i => d i * (x : ι → 𝕜) i) 2}
  add_mem' {x y} hx hy := by
    have h : (fun i => d i * ((x + y : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i)
        = fun i => d i * (x : ι → 𝕜) i + d i * (y : ι → 𝕜) i := by
      funext i
      change d i * ((x : ι → 𝕜) i + (y : ι → 𝕜) i) = _
      ring
    rw [Set.mem_ofPred_eq, h]
    exact hx.add hy
  zero_mem' := by
    have h : (fun i => d i * ((0 : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i) = fun _ => (0 : 𝕜) := by
      funext i
      change d i * (0 : 𝕜) = 0
      ring
    rw [Set.mem_ofPred_eq, h]
    exact zero_memℓp
  smul_mem' c {x} hx := by
    have h : (fun i => d i * ((c • x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i)
        = fun i => c • (d i * (x : ι → 𝕜) i) := by
      funext i
      change d i * (c * (x : ι → 𝕜) i) = c * (d i * (x : ι → 𝕜) i)
      ring
    rw [Set.mem_ofPred_eq, h]
    exact hx.const_smul c

/-- Characteristic form of membership in the maximal diagonal domain.  This is the
public unfolding interface for `lpDiagonalDomain`. -/
theorem mem_lpDiagonalDomain_iff (d : ι → 𝕜) (x : lp (fun _ : ι => 𝕜) 2) :
    x ∈ lpDiagonalDomain d ↔ Memℓp (fun i => d i * (x : ι → 𝕜) i) 2 := Iff.rfl

/-- **The unbounded diagonal multiplication operator**, on its maximal domain. -/
@[expose]
noncomputable def lpDiagonal (d : ι → 𝕜) :
    lp (fun _ : ι => 𝕜) 2 →ₗ.[𝕜] lp (fun _ : ι => 𝕜) 2 where
  domain := lpDiagonalDomain d
  toFun :=
    { toFun := fun x => ⟨fun i => d i * ((x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i, x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        funext i
        change d i * (((x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i
            + ((y : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i)
          = d i * ((x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i
            + d i * ((y : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i
        ring
      map_smul' := fun c x => by
        apply Subtype.ext
        funext i
        change d i * (c * ((x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i)
          = c * (d i * ((x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i)
        ring }

/-- The operator's domain is the maximal domain, by construction. -/
@[simp]
theorem lpDiagonal_domain (d : ι → 𝕜) : (lpDiagonal d).domain = lpDiagonalDomain d := rfl

/-- The operator acts coordinatewise by the multiplier. -/
@[simp]
theorem lpDiagonal_apply (d : ι → 𝕜) (x : (lpDiagonal d).domain) (i : ι) :
    ((lpDiagonal d x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i
      = d i * ((x : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) i := rfl

section Single

variable [DecidableEq ι]

/-- Finitely supported vectors always lie in the maximal domain: the multiplier
cannot destroy square summability of a vector with one nonzero coordinate. -/
theorem single_mem_lpDiagonal_domain (d : ι → 𝕜) (i : ι) (a : 𝕜) :
    lp.single 2 i a ∈ (lpDiagonal d).domain := by
  rw [lpDiagonal_domain, mem_lpDiagonalDomain_iff]
  have h : (fun j => d j * ((lp.single 2 i a : lp (fun _ : ι => 𝕜) 2) : ι → 𝕜) j)
      = ⇑(lp.single 2 i (d i * a) : lp (fun _ : ι => 𝕜) 2) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [lp.single_apply_self, lp.single_apply_self]
    · rw [lp.single_apply_ne _ _ _ hj, lp.single_apply_ne _ _ _ hj, mul_zero]
  rw [h]
  exact lp.memℓp _

/-- The operator acts on a standard basis vector by scaling it. -/
theorem lpDiagonal_single (d : ι → 𝕜) (i : ι) (a : 𝕜) :
    lpDiagonal d ⟨lp.single 2 i a, single_mem_lpDiagonal_domain d i a⟩
      = lp.single 2 i (d i * a) := by
  apply lp.ext
  funext j
  rw [lpDiagonal_apply]
  by_cases hj : j = i
  · subst hj
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ hj, lp.single_apply_ne _ _ _ hj, mul_zero]

end Single

/-- **The maximal domain is dense.**  Every `ℓ²` vector is the limit of its
coordinate partial sums, and each partial sum has finite support. -/
theorem dense_lpDiagonal_domain (d : ι → 𝕜) :
    Dense (((lpDiagonal d).domain : Submodule 𝕜 (lp (fun _ : ι => 𝕜) 2)) :
      Set (lp (fun _ : ι => 𝕜) 2)) := by
  classical
  intro f
  have hsum : HasSum (fun i => lp.single 2 i ((f : ι → 𝕜) i)) f :=
    lp.hasSum_single (by norm_num) f
  refine mem_closure_of_tendsto hsum ?_
  filter_upwards with s
  exact Submodule.sum_mem _ fun i _ => single_mem_lpDiagonal_domain d i _

/-- **A real diagonal multiplier gives a symmetric operator.**  The identity is
coordinatewise: conjugating `dᵢ xᵢ` moves `dᵢ` across the inner product unchanged. -/
theorem lpDiagonal_isSymmetric (d : ι → 𝕜) (hd : ∀ i, (starRingEnd 𝕜) (d i) = d i) :
    IsSymmetric (lpDiagonal d) := by
  rw [isSymmetric_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [RCLike.inner_apply', RCLike.inner_apply', lpDiagonal_apply, lpDiagonal_apply,
    map_mul, hd i]
  ring

/-- **The adjoint domain is no larger than the maximal domain.**  Testing against
`lp.single 2 i 1` identifies the `i`-th coordinate of the adjoint image as
`dᵢ yᵢ`, and that image is an `ℓ²` vector by construction. -/
theorem adjoint_domain_le_lpDiagonal_domain (d : ι → 𝕜)
    (hd : ∀ i, (starRingEnd 𝕜) (d i) = d i) :
    (lpDiagonal d).adjoint.domain ≤ (lpDiagonal d).domain := by
  classical
  intro y hy
  have hdense := dense_lpDiagonal_domain d
  have hform := _root_.LinearPMap.adjoint_isFormalAdjoint (T := lpDiagonal d) hdense
  set z : lp (fun _ : ι => 𝕜) 2 := (lpDiagonal d).adjoint ⟨y, hy⟩ with hzdef
  have hcoord : ∀ i, (z : ι → 𝕜) i = d i * (y : ι → 𝕜) i := by
    intro i
    have hx := hform ⟨y, hy⟩ ⟨lp.single 2 i 1, single_mem_lpDiagonal_domain d i 1⟩
    rw [lpDiagonal_single, mul_one, lp.inner_single_right, lp.inner_single_right] at hx
    rw [RCLike.inner_apply', RCLike.inner_apply'] at hx
    have hx' := congrArg (starRingEnd 𝕜) hx
    rw [map_mul, map_mul, RCLike.conj_conj, RCLike.conj_conj, map_one, hd i] at hx'
    rw [← hzdef] at hx'
    rw [mul_one] at hx'
    rw [hx', mul_comm]
  have himage : (fun i => d i * (y : ι → 𝕜) i) = ⇑z := by
    funext i
    exact (hcoord i).symm
  rw [lpDiagonal_domain, mem_lpDiagonalDomain_iff, himage]
  exact lp.memℓp _

/-- **The maximal real diagonal operator is self-adjoint.**

Symmetry gives `A ≤ A†`; maximality of the domain gives the reverse inclusion of
domains; a partial map contained in another with the same domain is that other
map. -/
theorem lpDiagonal_isSelfAdjoint (d : ι → 𝕜) (hd : ∀ i, (starRingEnd 𝕜) (d i) = d i) :
    _root_.IsSelfAdjoint (lpDiagonal d) := by
  classical
  have hdense := dense_lpDiagonal_domain d
  have hsym : (lpDiagonal d).IsFormalAdjoint (lpDiagonal d) :=
    (isSymmetric_iff _).mp (lpDiagonal_isSymmetric d hd)
  have hle : lpDiagonal d ≤ (lpDiagonal d).adjoint :=
    _root_.LinearPMap.IsFormalAdjoint.le_adjoint (T := lpDiagonal d) (S := lpDiagonal d)
      hdense hsym
  have hdom : (lpDiagonal d).domain = (lpDiagonal d).adjoint.domain :=
    le_antisymm hle.1 (adjoint_domain_le_lpDiagonal_domain d hd)
  rw [_root_.LinearPMap.isSelfAdjoint_def]
  exact (_root_.LinearPMap.eq_of_le_of_domain_eq hle hdom).symm

end LinearPMap
end TauCeti
