/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Spectral.OpNorm
public import LeanPool.BlockSpectralSensitivity.Composition

/-!
# `lambda (f ∘ g) = lambda f * lambda g`

Write an input of `comp f g` as a `W`-indexed family of blocks, `blk x w : Input V`, and let
`topBits g x : Input W` be the string of block values `w ↦ g (blk x w)`, so that
`comp f g x = f (topBits g x)`.

Two inputs of `comp f g` are adjacent in the sensitivity graph exactly when they differ in one
coordinate `(w, v)`, that flip is sensitive for `g` inside the block `w`, and the resulting
flip of the `w`-th top bit is sensitive for `f`; this is `BSLambda.adj_comp_flip`, and summing
it over the coordinates gives the master identity `BSLambda.adj_comp_mulVec_apply`

```
(A_{f∘g} *ᵥ ψ) x = ∑ w, A_f (topBits g x) ((topBits g x)^w) * (A_g *ᵥ ψ^{x,w}) (blk x w)
```

where `ψ^{x,w} z = ψ (setBlk x w z)` is the restriction of `ψ` to the `w`-th block through `x`.

*Upper bound.*  Group the inputs into the fibres of `topBits g` (`BSLambda.sum_sq_fibres`).  On
the fibre over `b` the identity above expresses `A_{f∘g} ψ` as a sum of at most `deg_f(b)`
terms, each of which is a copy of `A_g` acting inside one block and the identity elsewhere, so
each has norm at most `lambda(g)` times the norm of `ψ` on the fibre over `b^w`
(`BSLambda.sum_sq_block_le`).  Minkowski's inequality bounds the fibre
(`BSLambda.sum_sq_fibre_adj_comp_mulVec_le`), and the operator bound for `A_f` applied to the
vector of fibre norms `BSLambda.fibreNorm` then gives `‖A_{f∘g}‖ ≤ lambda(f) * lambda(g)`.

*Lower bound.*  If `A_g u = lambda(g) u` and `A_f v = lambda(f) v`, then
`φ x = v (topBits g x) * ∏ w, u (blk x w)` satisfies `A_{f∘g} φ = lambda(f) lambda(g) φ`
exactly.  It is nonzero because the support of an eigenvector for a nonzero eigenvalue of a
bipartite graph meets both sides.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

/-! ### Minkowski's inequality

The lemma below mentions nothing from this development.  Mathlib has the two-summand
Minkowski inequality `Real.Lp_add_le` and the abstract triangle inequality `norm_sum_le`, but
not the coordinate form for a finite *family* of vectors at `p = 2`; the proof is the standard
reduction to `norm_sum_le` in `EuclideanSpace ℝ X`.  It is stated in the root namespace
because it is Mathlib-shaped, not `BSLambda`-shaped.
-/

/-- **Minkowski's inequality** for a finite family of vectors, in sum-of-squares form: if the
`ℓ²`-norm of each `F y` is at most `t y`, then the `ℓ²`-norm of `∑ y, F y` is at most
`∑ y, t y`. -/
theorem sum_sq_sum_le_sq_sum {X Y : Type*} [Fintype X] [Fintype Y] (F : Y → X → ℝ) (t : Y → ℝ)
    (ht0 : ∀ y, 0 ≤ t y) (ht : ∀ y, ∑ x, F y x ^ 2 ≤ t y ^ 2) :
    ∑ x, (∑ y, F y x) ^ 2 ≤ (∑ y, t y) ^ 2 := by
  have hn (y : Y) : ‖(WithLp.toLp 2 (F y) : EuclideanSpace ℝ X)‖ ≤ t y := by
    refine (sq_le_sq₀ (norm_nonneg _) (ht0 y)).mp ?_
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Real.norm_eq_abs, sq_abs] using ht y
  have key : ‖∑ y, (WithLp.toLp 2 (F y) : EuclideanSpace ℝ X)‖ ≤ ∑ y, t y :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ ↦ hn y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [EuclideanSpace.norm_sq_eq] at hsq
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ ↦ ?_)) hsq
  simp [Real.norm_eq_abs, sq_abs, Finset.sum_apply]

namespace BSLambda

open scoped Matrix

/-! ### Blocks of a composed input

An input of `comp f g` is a `W`-indexed family of `V`-blocks.  Passing to that view is
`Function.curry`, and overwriting one block is `Function.update` read through it, so the
rewriting API below is Mathlib's `Function.update` API transported along `blk_setBlk`.
-/

section Blocks

variable {W V : Type*}

/-- The `w`-th block of an input of `comp f g`, i.e. `x` viewed as a `W`-indexed family. -/
@[expose]
def blk (x : Input (W × V)) : W → Input V := Function.curry x

/-- The string of block values `w ↦ g (blk x w)`, which `comp f g` feeds into `f`. -/
@[expose]
def topBits (g : Input V → Bool) (x : Input (W × V)) : Input W := fun w ↦ g (blk x w)

/-- `comp f g` is `f` applied to the top bits. -/
theorem comp_apply_topBits (f : Input W → Bool) (g : Input V → Bool) (x : Input (W × V)) :
    comp f g x = f (topBits g x) := rfl

/-- An input is determined by its blocks. -/
theorem blk_injective : Function.Injective (blk : Input (W × V) → W → Input V) :=
  Function.curry_injective

variable [DecidableEq W]

/-- `setBlk x w z` replaces the `w`-th block of `x` by `z`. -/
@[expose]
def setBlk (x : Input (W × V)) (w : W) (z : Input V) : Input (W × V) :=
  Function.uncurry (Function.update (blk x) w z)

/-- The blocks of `setBlk x w z` are the blocks of `x` with the `w`-th one updated.  Every
other `setBlk` lemma below is this together with Mathlib's `Function.update` API. -/
@[simp] theorem blk_setBlk (x : Input (W × V)) (w : W) (z : Input V) :
    blk (setBlk x w z) = Function.update (blk x) w z := rfl

/-- Writing back the block that is already there does nothing. -/
@[simp] theorem setBlk_blk_self (x : Input (W × V)) (w : W) : setBlk x w (blk x w) = x :=
  blk_injective (by simp)

/-- Only the last value written to the `w`-th block survives. -/
@[simp] theorem setBlk_setBlk (x : Input (W × V)) (w : W) (z z' : Input V) :
    setBlk (setBlk x w z) w z' = setBlk x w z' :=
  blk_injective (by simp)

/-- Overwriting the `w`-th block changes exactly one factor of a product over the blocks. -/
theorem prod_blk_setBlk {M : Type*} [Fintype W] [CommMonoid M]
    (u : Input V → M) (x : Input (W × V)) (w : W) (z : Input V) :
    ∏ w' : W, u (blk (setBlk x w z) w') = u z * ∏ w' ∈ Finset.univ.erase w, u (blk x w') := by
  rw [blk_setBlk, ← Finset.mul_prod_erase Finset.univ (fun w' ↦ u (Function.update (blk x) w z w'))
    (Finset.mem_univ w), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun w' hw' ↦
    congrArg u (Function.update_of_ne (Finset.ne_of_mem_erase hw') z (blk x))

/-- Flipping the coordinate `(w, v)` flips the coordinate `v` inside the `w`-th block. -/
theorem flipSet_prod_singleton [DecidableEq V] (x : Input (W × V)) (w : W) (v : V) :
    flipSet x {(w, v)} = setBlk x w (flipSet (blk x w) {v}) := by
  refine blk_injective (funext fun w' ↦ ?_)
  rw [blk_setBlk]
  rcases eq_or_ne w' w with rfl | hw
  · rw [Function.update_self]
    funext v'
    rcases eq_or_ne v' v with rfl | hv
    · simp [blk, flipSet]
    · simp [blk, flipSet, hv, Prod.ext_iff]
  · rw [Function.update_of_ne hw]
    funext v'
    simp [blk, flipSet, hw, Prod.ext_iff]

/-- The `w`-th top bit of `setBlk x w z` is the value of `g` on the new block. -/
theorem topBits_setBlk_apply_self (g : Input V → Bool) (x : Input (W × V)) (w : W)
    (z : Input V) : topBits g (setBlk x w z) w = g z := by
  simp [topBits]

/-- Away from `w`, the top bits of `setBlk x w z` are those of `x`. -/
theorem topBits_setBlk_apply_of_ne (g : Input V → Bool) (x : Input (W × V)) (w : W)
    (z : Input V) {w' : W} (h : w' ≠ w) :
    topBits g (setBlk x w z) w' = topBits g x w' := by
  simp [topBits, Function.update_of_ne h]

/-- Rewriting the `w`-th block without changing its `g`-value leaves the top bits alone. -/
theorem topBits_setBlk_of_eq (g : Input V → Bool) (x : Input (W × V)) (w : W) (z : Input V)
    (h : g z = g (blk x w)) :
    topBits g (setBlk x w z) = topBits g x := by
  refine funext fun w' ↦ ?_
  rcases eq_or_ne w' w with rfl | hw
  exacts [(topBits_setBlk_apply_self g x w' z).trans h, topBits_setBlk_apply_of_ne g x w z hw]

/-- Rewriting the `w`-th block so as to change its `g`-value flips the `w`-th top bit. -/
theorem topBits_setBlk_of_ne (g : Input V → Bool) (x : Input (W × V)) (w : W) (z : Input V)
    (h : g z ≠ g (blk x w)) :
    topBits g (setBlk x w z) = flipSet (topBits g x) {w} := by
  funext w'
  rcases eq_or_ne w' w with rfl | hw
  · rw [topBits_setBlk_apply_self, flipSet_apply_of_mem (Finset.mem_singleton_self w')]
    exact Bool.eq_not_of_ne h
  · rw [topBits_setBlk_apply_of_ne g x w z hw,
      flipSet_apply_of_notMem (Finset.notMem_singleton.mpr hw)]

/-- If the top bits of `x` disagree with `c` at some coordinate other than `w`, then no
rewriting of the `w`-th block lands in the fibre of `topBits g` over `c`. -/
theorem topBits_setBlk_ne (g : Input V → Bool) (x : Input (W × V)) (w : W) {c : Input W}
    {w' : W} (hw' : w' ≠ w) (h : topBits g x w' ≠ c w') (z : Input V) :
    topBits g (setBlk x w z) ≠ c := by
  refine fun hcon ↦ h ?_
  rw [← topBits_setBlk_apply_of_ne g x w z hw', hcon]

/-- If the top bits of `x` already agree with `c` away from `w`, then `setBlk x w z` lies in the
fibre of `topBits g` over `c` exactly when `g z` is the `w`-th bit of `c`. -/
theorem topBits_setBlk_eq_iff (g : Input V → Bool) (x : Input (W × V)) (w : W) {c : Input W}
    (hc : ∀ w' : W, w' ≠ w → topBits g x w' = c w') (z : Input V) :
    topBits g (setBlk x w z) = c ↔ g z = c w := by
  refine ⟨fun h ↦ by rw [← topBits_setBlk_apply_self g x w z, h], fun h ↦ funext fun w' ↦ ?_⟩
  rcases eq_or_ne w' w with rfl | hw'
  · rw [topBits_setBlk_apply_self, h]
  · rw [topBits_setBlk_apply_of_ne g x w z hw', hc w' hw']

end Blocks

section Composition

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

/-! ### The adjacency matrix of a composition -/

/-- An edge of the sensitivity graph of `comp f g` is a `g`-sensitive flip inside one block
whose effect on the top bits is an `f`-sensitive flip. -/
theorem adj_comp_flip (f : Input W → Bool) (g : Input V → Bool) (x : Input (W × V)) (w : W)
    (v : V) :
    adj (comp f g) x (flipSet x {(w, v)})
      = adj f (topBits g x) (flipSet (topBits g x) {w})
        * adj g (blk x w) (flipSet (blk x w) {v}) := by
  by_cases hg : g (flipSet (blk x w) {v}) = g (blk x w)
  · -- The flip is invisible to `g`, hence to `comp f g`: both sides vanish.
    have h1 : topBits g (flipSet x {(w, v)}) = topBits g x :=
      (flipSet_prod_singleton x w v) ▸ topBits_setBlk_of_eq g x w _ hg
    rw [adj_eq_zero_of_apply_eq g hg.symm, mul_zero]
    exact adj_eq_zero_of_apply_eq (comp f g) (congrArg f h1.symm)
  · -- The flip changes the `w`-th top bit, so the two edges match up.
    have h1 : topBits g (flipSet x {(w, v)}) = flipSet (topBits g x) {w} :=
      (flipSet_prod_singleton x w v) ▸ topBits_setBlk_of_ne g x w _ hg
    have h2 : adj g (blk x w) (flipSet (blk x w) {v}) = 1 :=
      adj_apply_eq_one_iff.2 ⟨hammingDist_flipSet_singleton _ _, fun hne ↦ hg hne.symm⟩
    rw [h2, mul_one, adj_apply, adj_apply, comp_apply_topBits, comp_apply_topBits, h1,
      hammingDist_flipSet_singleton, hammingDist_flipSet_singleton]

/-- **Master identity.**  `A_{f∘g}` acts on a vector by applying `A_g` inside each block and
weighting the blocks by the entries of `A_f` at the top bits. -/
theorem adj_comp_mulVec_apply (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (x : Input (W × V)) :
    (adj (comp f g) *ᵥ ψ) x
      = ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
          * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) := by
  rw [adj_mulVec_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [adj_mulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [adj_comp_flip, flipSet_prod_singleton, mul_assoc]

/-! ### The upper bound -/

/-- The fibres of `topBits g` partition the inputs, so the squares of the fibrewise truncations
of `F` sum to `∑ x, F x ^ 2`. -/
theorem sum_sq_fibres (g : Input V → Bool) (F : Input (W × V) → ℝ) :
    ∑ b : Input W, ∑ x : Input (W × V), (if topBits g x = b then F x else 0) ^ 2
      = ∑ x : Input (W × V), F x ^ 2 := by
  rw [← Finset.sum_fiberwise Finset.univ (topBits g) fun x ↦ F x ^ 2]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun _ _ ↦ by split <;> simp

/-- The `ℓ²`-norm of `ψ` on the fibre of `topBits g` over `b`. -/
noncomputable def fibreNorm (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) : ℝ :=
  Real.sqrt (∑ x : Input (W × V), (if topBits g x = b then ψ x else 0) ^ 2)

/-- Fibre norms are nonnegative. -/
theorem fibreNorm_nonneg (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) :
    0 ≤ fibreNorm g ψ b :=
  Real.sqrt_nonneg _

/-- The defining property of the fibre norm, with the square root cleared. -/
theorem sq_fibreNorm (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) :
    fibreNorm g ψ b ^ 2 = ∑ x : Input (W × V), (if topBits g x = b then ψ x else 0) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The fibre norms of `ψ` recombine into its `ℓ²`-norm. -/
theorem sum_sq_fibreNorm (g : Input V → Bool) (ψ : Input (W × V) → ℝ) :
    ∑ b : Input W, fibreNorm g ψ b ^ 2 = ∑ x : Input (W × V), ψ x ^ 2 :=
  (Finset.sum_congr rfl fun b _ ↦ sq_fibreNorm g ψ b).trans (sum_sq_fibres g ψ)

/-- Splitting an input of `comp f g` into its `w`-th block and everything else. -/
def blockEquiv (w : W) :
    Input V × {x : Input (W × V) // blk x w = zeroInput V} ≃ Input (W × V) where
  toFun p := setBlk p.2.1 w p.1
  invFun x := ⟨blk x w, setBlk x w (zeroInput V), Function.update_self w _ (blk x)⟩
  left_inv := by
    rintro ⟨z, x, hx⟩
    simp [← hx]
  right_inv x := by simp

/-- Every input decomposes as a value for the `w`-th block together with an input whose `w`-th
block is zero, so a sum over all inputs splits accordingly. -/
theorem sum_setBlk (w : W) (F : Input (W × V) → ℝ) :
    ∑ y : {x : Input (W × V) // blk x w = zeroInput V}, ∑ a : Input V, F (setBlk y.1 w a)
      = ∑ x : Input (W × V), F x := by
  rw [← Fintype.sum_prod_type_right (f := fun p : Input V ×
    {x : Input (W × V) // blk x w = zeroInput V} ↦ F (setBlk p.2.1 w p.1))]
  exact Equiv.sum_comp (blockEquiv (V := V) w) F

/-- Applying `A_g` inside the block `w` and the identity elsewhere is an operator of norm at
most `lambda(g)` from the fibre of `topBits g` over `b^w` to the fibre over `b`. -/
theorem sum_sq_block_le (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) (w : W) :
    ∑ x : Input (W × V),
        (if topBits g x = b then (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
      ≤ lam g ^ 2 * fibreNorm g ψ (flipSet b {w}) ^ 2 := by
  have hflip : ∀ w' : W, w' ≠ w → flipSet b {w} w' = b w' :=
    fun w' hw' ↦ flipSet_apply_of_notMem (Finset.notMem_singleton.mpr hw')
  rw [sq_fibreNorm, ← sum_setBlk w, ← sum_setBlk w, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  by_cases hP : ∀ w' : W, w' ≠ w → topBits g y.1 w' = b w'
  · -- Off `w` the input `setBlk y.1 w a` already agrees with `b`, so lying in the fibre over
    -- any such `c` is a condition on the single bit `g a`.
    have hL : ∀ a : Input V, (topBits g (setBlk y.1 w a) = b) ↔ (g a = b w) :=
      topBits_setBlk_eq_iff g y.1 w hP
    have hR (a : Input V) : (topBits g (setBlk y.1 w a) = flipSet b {w}) ↔ ¬ (g a = b w) := by
      rw [topBits_setBlk_eq_iff g y.1 w (fun w' hw' ↦ (hP w' hw').trans (hflip w' hw').symm) a,
        flipSet_apply_of_mem (Finset.mem_singleton_self w)]
      cases b w <;> simp
    have hLsum (a : Input V) :
        (if topBits g (setBlk y.1 w a) = b then
            (adj g *ᵥ fun z ↦ ψ (setBlk (setBlk y.1 w a) w z)) (blk (setBlk y.1 w a) w)
          else 0) ^ 2
          = (if g a = b w then (adj g *ᵥ fun z ↦ ψ (setBlk y.1 w z)) a else 0) ^ 2 := by
      simp only [setBlk_setBlk, blk_setBlk, Function.update_self]
      by_cases hga : g a = b w
      · rw [ite_eq_left ((hL a).2 hga), ite_eq_left hga]
      · rw [ite_eq_right fun h ↦ hga ((hL a).1 h), ite_eq_right hga]
    have hRsum (a : Input V) :
        (if topBits g (setBlk y.1 w a) = flipSet b {w} then ψ (setBlk y.1 w a) else 0) ^ 2
          = (if g a = b w then 0 else ψ (setBlk y.1 w a)) ^ 2 := by
      by_cases hga : g a = b w
      · rw [ite_eq_right fun h ↦ (hR a).1 h hga, ite_eq_left hga]
      · rw [ite_eq_left ((hR a).2 hga), ite_eq_right hga]
    rw [Finset.sum_congr rfl fun a _ ↦ hLsum a, Finset.sum_congr rfl fun a _ ↦ hRsum a]
    exact sum_sq_adj_mulVec_side_le g (fun z ↦ ψ (setBlk y.1 w z)) (b w)
  · -- Off `w` the input `setBlk y.1 w a` disagrees with `b`, so both sides vanish.
    push Not at hP
    obtain ⟨w', hw'ne, hw'⟩ := hP
    have hw'flip : topBits g y.1 w' ≠ flipSet b {w} w' := by
      rw [hflip w' hw'ne]
      exact hw'
    simp [topBits_setBlk_ne g y.1 w hw'ne hw', topBits_setBlk_ne g y.1 w hw'ne hw'flip]

/-- The `w`-th summand of the master identity, restricted to the fibre of `topBits g` over `b`.
This is `sum_sq_block_le` with the constant `A_f b b^w` pulled out of the sum. -/
theorem sum_sq_fibre_summand_le (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (b : Input W) (w : W) :
    ∑ x : Input (W × V), (if topBits g x = b then
        adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
      ≤ (adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w}))) ^ 2 := by
  have hfactor (x : Input (W × V)) :
      (if topBits g x = b then
          adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
        = adj f b (flipSet b {w}) ^ 2
          * (if topBits g x = b then (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2 := by
    split <;> ring
  rw [Finset.sum_congr rfl fun x _ ↦ hfactor x, ← Finset.mul_sum, mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (sum_sq_block_le g ψ b w) (sq_nonneg _)

/-- **The fibrewise bound.**  On the fibre of `topBits g` over `b`, the master identity writes
`A_{f∘g} ψ` as a sum of `#W` vectors whose norms `sum_sq_fibre_summand_le` controls; Minkowski's
inequality then bounds the fibre by `lambda(g)` times the value at `b` of `A_f` applied to the
vector of fibre norms of `ψ`. -/
theorem sum_sq_fibre_adj_comp_mulVec_le (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (b : Input W) :
    ∑ x : Input (W × V), (if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0) ^ 2
      ≤ lam g ^ 2 * ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 := by
  have hmaster (x : Input (W × V)) : ∑ w : W, (if topBits g x = b then
      adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0)
        = if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0 := by
    by_cases hx : topBits g x = b
    · subst hx
      simp only [reduceIte]
      exact (adj_comp_mulVec_apply f g ψ x).symm
    · simp [hx]
  have ht0 (w : W) : 0 ≤ adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w})) :=
    mul_nonneg (adj_nonneg f _ _) (mul_nonneg (lam_nonneg g) (fibreNorm_nonneg g ψ _))
  have htsum : ∑ w : W, adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w}))
      = lam g * (adj f *ᵥ fibreNorm g ψ) b := by
    rw [adj_mulVec_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  calc ∑ x : Input (W × V), (if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0) ^ 2
      = ∑ x : Input (W × V), (∑ w : W, (if topBits g x = b then
          adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0)) ^ 2 :=
        Finset.sum_congr rfl fun x _ ↦ by rw [hmaster x]
    _ ≤ (∑ w : W, adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w}))) ^ 2 :=
        sum_sq_sum_le_sq_sum _ _ ht0 (sum_sq_fibre_summand_le f g ψ b)
    _ = lam g ^ 2 * ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 := by rw [htsum, mul_pow]

/-- The operator bound for `A_{f∘g}`, in sum-of-squares form. -/
theorem sum_sq_adj_comp_mulVec_le (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) :
    ∑ x, (adj (comp f g) *ᵥ ψ) x ^ 2 ≤ (lam f * lam g) ^ 2 * ∑ x, ψ x ^ 2 :=
  calc ∑ x, (adj (comp f g) *ᵥ ψ) x ^ 2
      = ∑ b : Input W, ∑ x : Input (W × V),
          (if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0) ^ 2 :=
        (sum_sq_fibres g (adj (comp f g) *ᵥ ψ)).symm
    _ ≤ ∑ b : Input W, lam g ^ 2 * ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 :=
        Finset.sum_le_sum fun b _ ↦ sum_sq_fibre_adj_comp_mulVec_le f g ψ b
    _ = lam g ^ 2 * ∑ b : Input W, ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ lam g ^ 2 * (lam f ^ 2 * ∑ b : Input W, fibreNorm g ψ b ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_sq_adj_mulVec_le f (fibreNorm g ψ)) (sq_nonneg _)
    _ = (lam f * lam g) ^ 2 * ∑ x, ψ x ^ 2 := by
        rw [sum_sq_fibreNorm]
        ring

/-- **Submultiplicativity of `lambda`.** -/
theorem lam_comp_le (f : Input W → Bool) (g : Input V → Bool) :
    lam (comp f g) ≤ lam f * lam g :=
  (lam_le_l2_opNorm_adj (comp f g)).trans
    (Matrix.l2_opNorm_le_of_sum_sq_mulVec_le (adj (comp f g))
      (mul_nonneg (lam_nonneg f) (lam_nonneg g)) (sum_sq_adj_comp_mulVec_le f g))

/-! ### The lower bound -/

/-- The support of an eigenvector for a nonzero eigenvalue meets both sides of the
bipartition. -/
theorem exists_apply_eq_and_ne_zero (g : Input V → Bool) {μ : ℝ} (hμ : μ ≠ 0)
    {u : Input V → ℝ} (hu : u ≠ 0) (hev : adj g *ᵥ u = μ • u) (β : Bool) :
    ∃ a : Input V, g a = β ∧ u a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hu (funext fun a ↦ show u a = (0 : ℝ) from ?_)
  by_cases hga : g a = β
  · exact hcon a hga
  · -- Every neighbour `y` of `a` has `g y ≠ g a`, hence `g y = β`, hence `u y = 0`.
    have hβ : (!g a) = β := (Bool.eq_not_of_ne (Ne.symm hga)).symm
    have hzero : ∑ y : Input V, adj g a y * u y = 0 :=
      Finset.sum_eq_zero fun y _ ↦ by
        rcases eq_or_ne (adj g a y) 0 with hy | hy
        · rw [hy, zero_mul]
        · rw [hcon y ((Bool.eq_not_of_ne (apply_ne_of_adj_ne_zero g hy).symm).trans hβ), mul_zero]
    exact (mul_eq_zero.mp ((congrFun hev a).symm.trans hzero)).resolve_left hμ

/-- **The block step of the product eigenvector computation.**  Applying `A_g` inside the
`w`-th block to `x ↦ v (topBits g x) * ∏ w, u (blk x w)` multiplies it by `lambda(g)` and
flips the `w`-th top bit: only blocks `z` adjacent to `blk x w` contribute, and for those the
top bits change exactly at `w`. -/
theorem adj_mulVec_block_prod (g : Input V → Bool) {u : Input V → ℝ} (v : Input W → ℝ)
    (hu : adj g *ᵥ u = lam g • u) (x : Input (W × V)) (w : W) :
    (adj g *ᵥ fun z : Input V ↦
        v (topBits g (setBlk x w z)) * ∏ w' : W, u (blk (setBlk x w z) w')) (blk x w)
      = lam g * v (flipSet (topBits g x) {w}) * ∏ w' : W, u (blk x w') := by
  have hstep : (adj g *ᵥ fun z : Input V ↦
        v (topBits g (setBlk x w z)) * ∏ w' : W, u (blk (setBlk x w z) w')) (blk x w)
      = ∑ z : Input V, adj g (blk x w) z
          * (v (flipSet (topBits g x) {w})
            * (u z * ∏ w' ∈ Finset.univ.erase w, u (blk x w'))) := by
    change ∑ z : Input V, adj g (blk x w) z
        * (v (topBits g (setBlk x w z)) * ∏ w' : W, u (blk (setBlk x w z) w')) = _
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hz : adj g (blk x w) z = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [topBits_setBlk_of_ne g x w z (apply_ne_of_adj_ne_zero g hz).symm,
        prod_blk_setBlk u x w z]
  have hpull : ∑ z : Input V, adj g (blk x w) z
        * (v (flipSet (topBits g x) {w})
          * (u z * ∏ w' ∈ Finset.univ.erase w, u (blk x w')))
      = (v (flipSet (topBits g x) {w}) * ∏ w' ∈ Finset.univ.erase w, u (blk x w'))
        * ∑ z : Input V, adj g (blk x w) z * u z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  have hev : ∑ z : Input V, adj g (blk x w) z * u z = lam g * u (blk x w) :=
    congrFun hu (blk x w)
  rw [hstep, hpull, hev,
    ← Finset.mul_prod_erase Finset.univ (fun w' ↦ u (blk x w')) (Finset.mem_univ w)]
  ring

/-- The product eigenvector: if `u` and `v` are eigenvectors of `A_g` and `A_f` then
`x ↦ v (topBits g x) * ∏ w, u (blk x w)` is an eigenvector of `A_{f∘g}`. -/
theorem adj_comp_mulVec_prod (f : Input W → Bool) (g : Input V → Bool) {u : Input V → ℝ}
    {v : Input W → ℝ} (hu : adj g *ᵥ u = lam g • u) (hv : adj f *ᵥ v = lam f • v) :
    adj (comp f g) *ᵥ (fun x ↦ v (topBits g x) * ∏ w, u (blk x w))
      = (lam f * lam g) • fun x ↦ v (topBits g x) * ∏ w, u (blk x w) := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [adj_comp_mulVec_apply]
  have hfin : ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
        * (lam g * v (flipSet (topBits g x) {w}) * ∏ w' : W, u (blk x w'))
      = lam f * lam g * (v (topBits g x) * ∏ w' : W, u (blk x w')) := by
    have h1 : ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
          * (lam g * v (flipSet (topBits g x) {w}) * ∏ w' : W, u (blk x w'))
        = (lam g * ∏ w' : W, u (blk x w'))
          * ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
            * v (flipSet (topBits g x) {w}) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    have h2 : (adj f *ᵥ v) (topBits g x) = lam f * v (topBits g x) := congrFun hv (topBits g x)
    rw [h1, ← adj_mulVec_apply f v (topBits g x), h2]
    ring
  rw [← hfin]
  exact Finset.sum_congr rfl fun w _ ↦ by rw [adj_mulVec_block_prod g v hu x w]

omit [DecidableEq W] [Fintype V] [DecidableEq V] in
/-- The product eigenvector is nonzero. -/
theorem prod_eigenvector_ne_zero (g : Input V → Bool) {u : Input V → ℝ} {v : Input W → ℝ}
    (hboth : ∀ β : Bool, ∃ a : Input V, g a = β ∧ u a ≠ 0) (hv : v ≠ 0) :
    (fun x : Input (W × V) ↦ v (topBits g x) * ∏ w, u (blk x w)) ≠ 0 := by
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hb
  choose a ha hua using hboth
  refine Function.ne_iff.mpr ⟨fun p ↦ a (b p.1) p.2, ?_⟩
  simp only [Pi.zero_apply]
  have hbt : topBits g (fun p : W × V ↦ a (b p.1) p.2) = b := funext fun w ↦ ha (b w)
  rw [hbt]
  apply mul_ne_zero hb
  rw [Finset.prod_ne_zero_iff]
  exact fun w _ ↦ hua (b w)

/-- **Supermultiplicativity of `lambda`.** -/
theorem le_lam_comp (f : Input W → Bool) (g : Input V → Bool) :
    lam f * lam g ≤ lam (comp f g) := by
  rcases eq_or_lt_of_le (lam_nonneg g) with hg | hg
  · rw [← hg, mul_zero]
    exact lam_nonneg _
  obtain ⟨u, hu0, hu⟩ := exists_top_eigenvector g
  obtain ⟨v, hv0, hv⟩ := exists_top_eigenvector f
  exact le_lam_of_eigenvector (comp f g)
    (prod_eigenvector_ne_zero g (exists_apply_eq_and_ne_zero g hg.ne' hu0 hu) hv0)
    (adj_comp_mulVec_prod f g hu hv)

/-- **The composition theorem** (Section 14 of `bs_lambda.txt`, imported there from ABKRT):
`lambda` is multiplicative under block composition. -/
theorem lam_comp (f : Input W → Bool) (g : Input V → Bool) :
    lam (comp f g) = lam f * lam g :=
  le_antisymm (lam_comp_le f g) (le_lam_comp f g)

/-! ### Self-composition -/

/-- The one-bit identity function has `lambda = 1`. -/
theorem lam_iterFun_zero (f : Input V → Bool) : lam (iterFun f 0) = 1 := by
  let : Unique (IterCoord V 0) := inferInstanceAs (Unique PUnit)
  refine lam_eq_of_sensAt_eq zero_le_one fun x ↦ ?_
  have hsc (v : IterCoord V 0) : SensitiveCoord (iterFun f 0) x v := by
    change flipSet x {v} v ≠ x v
    rw [flipSet_singleton_self]
    exact Bool.not_ne_self _
  rw [sensAt_eq_card_univ hsc, Fintype.card_unique, Nat.cast_one]

/-- `lambda(F_m) = lambda(f)^m` for the `m`-fold self-composition (Section 14). -/
theorem lam_iterFun_eq (f : Input V → Bool) : ∀ m, lam (iterFun f m) = lam f ^ m
  | 0 => (lam_iterFun_zero f).trans (pow_zero _).symm
  | m + 1 => by
      change lam (comp f (iterFun f m)) = _
      rw [lam_comp, lam_iterFun_eq f m, pow_succ']

end Composition

end BSLambda
