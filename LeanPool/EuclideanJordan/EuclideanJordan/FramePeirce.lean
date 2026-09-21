/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import LeanPool.EuclideanJordan.EuclideanJordan.FrameExists


/-!
# The frame Peirce decomposition: `J = ⨁_{i ≤ j} V_{ij}`

For a Jordan frame `F = (p₁, …, pₙ)` this file builds the blocks

* `V_{ii} := J₂(p i) = {x | p i ∘ x = x}`,
* `V_{ij} := {x | p i ∘ x = ½ • x ∧ p j ∘ x = ½ • x}` for `i ≠ j`,

as a family `frameBlock F : Sym2 (Fin n) → Submodule ℝ J` (`Sym2` because `V_{ij} = V_{ji}`),
and proves `frameBlock_isInternal : DirectSum.IsInternal (frameBlock F)` — independence
(`frameBlock_iSupIndep`) plus spanning (`frameBlock_iSup_eq_top`).

`frameBlockRaw_self` records that the diagonal block really is
    `EuclideanJordan/PeirceSubalgebra.lean`'s
`peirceOneSub`, so the two definitions of `J₂(p i)` in the tree do not drift apart.

## ★ The reprice held in direction and was wrong about the mechanism

The build plan and the task brief both priced this module as risk #2, with the diagnosis: the
eigenvalue combinatorics is *already done* in `EuclideanJordan/Pattern.lean`, what is missing is (a)
simultaneous diagonalisation / spanning and (b) the `DirectSum.IsInternal` packaging, and the
mechanism for (a) is to expand

    id = ∏ᵢ (P₁(pᵢ) + P½(pᵢ) + P₀(pᵢ)) = ∑_{μ : Fin n → Fin 3} ∏ᵢ P_{μ i}(pᵢ)

and let the `Pattern` lemmas annihilate every `μ` outside the allowed set — the cost driver
being that "expand a `Finset.prod` of sums of commuting idempotent projections over a `Fintype`
and package it as `DirectSum.IsInternal`" is the archetypal Lean chore.

(a) and (b) were indeed the missing parts.  **The mechanism was not used, and neither was
`EuclideanJordan/Pattern.lean`.**  `Pattern` is in scope here — it arrives through
`EuclideanJordan/Class.lean`'s import — and no declaration in this file mentions `sum_eigen_eq_one`,
`eigen_pattern_mem` or `eigen_pattern_card_le_two`.  There is no `Finset.prod` of projections
below, and no sum over `Fin n → Fin 3`; neither string occurs in this file outside this
docstring.

★ What replaced it is a *residual* argument, `frame_peirce_span`.  Set

    z := x − ∑ᵢ P₁(pᵢ) x − ½ • ∑ᵢ P½(pᵢ) x.

The eight composition rules of the `Compose` section below, together with
`sum_peirceHalf_erase` in the one place where `P½(p k) P½(p k) x` has to be matched against the
rest of the half-component, kill `P₁(p k) z` and `P½(p k) z` for every `k`; so `peirce_add_add`
at `p k` collapses to `z = P₀(p k) z`, whence `p k ∘ z = 0` for every `k`, whence
`z = 1 ∘ z = (∑ₖ p k) ∘ z = 0`.  Nothing is expanded, because the *identity* is never expanded —
only its residual is tested, one idempotent at a time.

★ The `½` in that identity is not a normalisation choice.  `P½(pᵢ) x` is the whole
`i`-th half-eigencomponent, which is the sum of the `V_{ij}` parts over all `j ≠ i`; so an
off-diagonal block is counted once by `P½(pᵢ)` and again by `P½(pⱼ)`, and the sum over `i`
double-counts exactly.  Breaking `P½(pᵢ) x` into its blocks is `sum_peirceHalf_erase`, which is
one of exactly two places `F.complete` is used; the other is the final `z = 1 ∘ z`.

## What is *not* needed, and what is still missing

★ **No proof below uses primitivity.**  The string `primitive` does not occur in this file
outside this docstring: every proof runs on `F.orthIdem` and `F.complete` alone, so primitivity
enters the *statements* only through the `JordanFrame` hypothesis they carry, never through an
argument.  (That is an observation about these proofs, not a claim that the results have been
restated at the weaker hypothesis — they have not.)  Primitivity is what will collapse `V_{ii}`
to `ℝ ∙ pᵢ`: that is the next module's `dim V_{ii} = 1`, and it is not proved here.

★ **`rank J = n` is still not available** and nothing here is a step towards it; the frame is
carried as data.  See `EuclideanJordan/Rank.lean`'s module docstring.  Do not read
`frameBlock_isInternal` as a statement about the rank.

★ That guard got easier to trip once `EuclideanJordan/HermitianCarrier.lean` named a frame.
`diagJordanFrame : JordanFrame (HermitianMat n ℂ) (Fintype.card n)` puts a frame of cardinality
`Fintype.card n` on `H_n(ℂ)`, which reads like "`rank (H_n(ℂ)) = Fintype.card n`".  It is not:
`EuclideanJordan/Rank.lean` supplies `JordanFrame.card_le_rank`, an inequality in one direction
    only, and
`rank` is a supremum over *every* orthogonal family of nonzero idempotents.  A named frame of
cardinality `k` is a lower bound on the rank and nothing more.

★ **The carrier arrived after this file — this paragraph used to say the opposite.**  As
written on 2026-08-23 it recorded that the only `EuclideanJordanAlgebra` instances in the tree
were `EuclideanJordan/PeirceSubalgebra.lean`'s two, both *conditional* on an ambient
`[EuclideanJordanAlgebra J]`, so that nothing exhibited a base model and the results below
applied to no concrete algebra.  That was true when written and is **false now**:
`EuclideanJordan/HermitianCarrier.lean`'s `instEuclideanJordanAlgebraHermitianMat` makes
`HermitianMat n 𝕜` an instance for every `RCLike 𝕜`, and its `hermitian_exists_jordanFrame`
and `hermitian_frameBlock_isInternal` (both under `[Nonempty n]`, which is what `1 ≠ 0` needs)
are `exists_jordanFrame` and `frameBlock_isInternal` read on that carrier.  So the theorems
below are statements about a live object, not only about an unwitnessed class.  Since
`1ad66d2` the carrier module goes past existence and *names* a frame — `diagJordanFrame`, the
diagonal matrix units, over ℂ — so `frameBlock_isInternal` has an instance with nothing left
existentially quantified.  Note what that does and does not settle: see the rank guard above.

## Scope

-/

noncomputable section

namespace EuclideanJordan

open EuclideanJordanAlgebra

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

/-! ## Eigenspaces of left multiplication -/

/-- The `r`-eigenspace of `L_a`. -/
def eigSub (a : J) (r : ℝ) : Submodule ℝ J where
  carrier := {x : J | a * x = r • x}
  add_mem' := fun {u v} hu hv => by
    change a * (u + v) = r • (u + v)
    rw [mul_add, hu, hv, smul_add]
  zero_mem' := by change a * 0 = r • (0 : J); rw [mul_zero, smul_zero]
  smul_mem' := fun t x hx => by
    change a * (t • x) = r • (t • x)
    rw [mul_smul_comm, hx, smul_comm]

@[simp] theorem mem_eigSub {a : J} {r : ℝ} {x : J} : x ∈ eigSub a r ↔ a * x = r • x := Iff.rfl

/-! ## The blocks -/

variable {n : ℕ}

/-- The eigenvalue attached to the pair `(i, j)`: `1` on the diagonal, `1/2` off it. -/
def blockCoef (i j : Fin n) : ℝ := if i = j then 1 else (2 : ℝ)⁻¹

theorem blockCoef_comm (i j : Fin n) : blockCoef i j = blockCoef j i := by
  unfold blockCoef
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- `V_{ij}` before it is pushed through `Sym2`. -/
def frameBlockRaw (F : JordanFrame J n) (i j : Fin n) : Submodule ℝ J :=
  eigSub (F.p i) (blockCoef i j) ⊓ eigSub (F.p j) (blockCoef i j)

theorem frameBlockRaw_comm (F : JordanFrame J n) (i j : Fin n) :
    frameBlockRaw F i j = frameBlockRaw F j i := by
  unfold frameBlockRaw
  rw [blockCoef_comm i j, inf_comm]

/-- **`V_{ij}`.**  For `i ≠ j` the joint `1/2`-eigenspace of `L_{p i}` and `L_{p j}`; on the
diagonal, `J₂(p i)`. -/
def frameBlock (F : JordanFrame J n) : Sym2 (Fin n) → Submodule ℝ J :=
  Sym2.lift ⟨frameBlockRaw F, frameBlockRaw_comm F⟩

@[simp] theorem frameBlock_mk (F : JordanFrame J n) (i j : Fin n) :
    frameBlock F s(i, j) = frameBlockRaw F i j := rfl

theorem mem_frameBlockRaw_diag {F : JordanFrame J n} {i : Fin n} {x : J} :
    x ∈ frameBlockRaw F i i ↔ F.p i * x = x := by
  simp [frameBlockRaw, blockCoef]

theorem mem_frameBlockRaw_off {F : JordanFrame J n} {i j : Fin n} (hij : i ≠ j) {x : J} :
    x ∈ frameBlockRaw F i j ↔ F.p i * x = (2 : ℝ)⁻¹ • x ∧ F.p j * x = (2 : ℝ)⁻¹ • x := by
  simp [frameBlockRaw, blockCoef, hij]

/-- The diagonal block is `EuclideanJordan/PeirceSubalgebra.lean`'s `J₂(p i)` on the nose. -/
theorem frameBlockRaw_self (F : JordanFrame J n) (i : Fin n) :
    frameBlockRaw F i i = peirceOneSub (F.orthIdem.idem i) :=
  Submodule.ext fun _ => mem_frameBlockRaw_diag

/-! ## What the frame does to a block element -/

/-- An element of `J₂(p i)` is annihilated by every other member of the frame. -/
theorem frame_mul_eq_zero_of_eigen_one (F : JordanFrame J n) {i k : Fin n} (hik : k ≠ i)
    {x : J} (hx : F.p i * x = x) : F.p k * x = 0 := by
  have h := eigen_one_mul_zero (F.orthIdem.idem i) hx (F.orthIdem.orth i k (Ne.symm hik))
  rw [_root_.mul_comm]; exact h

/-- An element halved by `p i` and by `p j` is annihilated by every other member of the frame:
it lies in `J₂(p i + p j)`, and every other `p k` lies in `J₀(p i + p j)`. -/
theorem frame_mul_eq_zero_of_eigen_half (F : JordanFrame J n) {i j k : Fin n} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) {x : J} (hi : F.p i * x = (2 : ℝ)⁻¹ • x)
    (hj : F.p j * x = (2 : ℝ)⁻¹ • x) : F.p k * x = 0 := by
  have hq : (F.p i + F.p j) * (F.p i + F.p j) = F.p i + F.p j :=
    add_idem_of_orthogonal (F.orthIdem.idem i) (F.orthIdem.idem j) (F.orthIdem.orth i j hij)
  have hqx : (F.p i + F.p j) * x = x := mem_J2_of_half_half hi hj
  have hqk : (F.p i + F.p j) * F.p k = 0 := pair_mul_of_ne F.orthIdem hki hkj
  have h := eigen_one_mul_zero hq hqx hqk
  rw [_root_.mul_comm]; exact h

/-- **The eigenvalue of `L_{p k}` on `V_{ij}` is `0` for every `k` outside `{i, j}`.** -/
theorem frameBlockRaw_mul_eq_zero (F : JordanFrame J n) {i j k : Fin n} (hki : k ≠ i)
    (hkj : k ≠ j) {x : J} (hx : x ∈ frameBlockRaw F i j) : F.p k * x = 0 := by
  by_cases hij : i = j
  · subst hij
    exact frame_mul_eq_zero_of_eigen_one F hki (mem_frameBlockRaw_diag.mp hx)
  · obtain ⟨hi, hj⟩ := (mem_frameBlockRaw_off hij).mp hx
    exact frame_mul_eq_zero_of_eigen_half F hij hki hkj hi hj

/-! ## How the frame's Peirce projections compose

The eight ways two of the projections `peirceOne (p i)`, `peirceHalf (p i)` can be applied in
succession.  Every one is `EuclideanJordan/Block.lean`'s commutation plus a single-idempotent
    rule from
`EuclideanJordan/Peirce.lean`. -/

section Compose

variable (F : JordanFrame J n) (x : J) {i k : Fin n}

theorem peirceOne_peirceOne_self : peirceOne (F.p k) (peirceOne (F.p k) x) =
    peirceOne (F.p k) x := peirceOne_of_eigen (mul_peirceOne (F.orthIdem.idem k) x)

theorem peirceOne_peirceOne_of_ne (h : i ≠ k) :
    peirceOne (F.p k) (peirceOne (F.p i) x) = 0 :=
  peirceOne_of_eigen_zero
    (frame_mul_eq_zero_of_eigen_one F (Ne.symm h) (mul_peirceOne (F.orthIdem.idem i) x))

theorem peirceOne_peirceHalf_self : peirceOne (F.p k) (peirceHalf (F.p k) x) = 0 :=
  peirceOne_of_eigen_half (mul_peirceHalf (F.orthIdem.idem k) x)

theorem peirceOne_peirceHalf_of_ne (h : i ≠ k) :
    peirceOne (F.p k) (peirceHalf (F.p i) x) = 0 := by
  have hcomm : peirceOne (F.p k) (peirceHalf (F.p i) x)
      = peirceHalf (F.p i) (peirceOne (F.p k) x) :=
    peirceOne_comm_of_mul_comm (F := peirceHalf (F.p i))
      (mul_peirceHalf_comm_orth (F.orthIdem.idem k) (F.orthIdem.orth i k h)) x
  rw [hcomm]
  exact peirceHalf_of_eigen_zero
    (frame_mul_eq_zero_of_eigen_one F h (mul_peirceOne (F.orthIdem.idem k) x))

theorem peirceHalf_peirceOne_self : peirceHalf (F.p k) (peirceOne (F.p k) x) = 0 :=
  peirceHalf_of_eigen (mul_peirceOne (F.orthIdem.idem k) x)

theorem peirceHalf_peirceOne_of_ne (h : i ≠ k) :
    peirceHalf (F.p k) (peirceOne (F.p i) x) = 0 :=
  peirceHalf_of_eigen_zero
    (frame_mul_eq_zero_of_eigen_one F (Ne.symm h) (mul_peirceOne (F.orthIdem.idem i) x))

theorem peirceHalf_peirceHalf_self : peirceHalf (F.p k) (peirceHalf (F.p k) x) =
    peirceHalf (F.p k) x := peirceHalf_of_eigen_half (mul_peirceHalf (F.orthIdem.idem k) x)

theorem peirceHalf_peirceHalf_comm (h : i ≠ k) :
    peirceHalf (F.p k) (peirceHalf (F.p i) x) = peirceHalf (F.p i) (peirceHalf (F.p k) x) :=
  peirceHalf_comm_peirceHalf (F.orthIdem.idem k) (F.orthIdem.orth i k h) x

end Compose

/-! ## The half-eigenspace of one frame member splits over the others -/

/-- **`J½(p k) = ∑_{m ≠ k} V_{km}`, in the form the spanning argument needs.**

For `y` halved by `p k` and `m ≠ k`, `peirceOne (p m) y` lies in `J₂(p m)` — hence in `J₀(p k)`
— and simultaneously in `J½(p k)`, because `peirceOne (p m)` commutes with `L_{p k}`; so it
vanishes.  Then `p m ∘ y = ½ • peirceHalf (p m) y`, and completeness turns
`∑ₘ p m ∘ y = y` into the claim. -/
theorem sum_peirceHalf_erase (F : JordanFrame J n) {k : Fin n} {y : J}
    (hy : F.p k * y = (2 : ℝ)⁻¹ • y) :
    ∑ m ∈ Finset.univ.erase k, peirceHalf (F.p m) y = y := by
  classical
  have hone : ∀ m, m ≠ k → peirceOne (F.p m) y = 0 := by
    intro m hm
    have hcomm : F.p k * peirceOne (F.p m) y = peirceOne (F.p m) (F.p k * y) :=
      mul_peirceOne_comm_orth (F.orthIdem.idem k) (F.orthIdem.orth m k hm) y
    have h1 : F.p k * peirceOne (F.p m) y = (2 : ℝ)⁻¹ • peirceOne (F.p m) y := by
      rw [hcomm, hy, map_smul]
    have h0 : F.p k * peirceOne (F.p m) y = 0 :=
      frame_mul_eq_zero_of_eigen_one F (Ne.symm hm) (mul_peirceOne (F.orthIdem.idem m) y)
    have : (2 : ℝ)⁻¹ • peirceOne (F.p m) y = 0 := by rw [← h1, h0]
    simpa using this
  have hmul : ∀ m, m ≠ k → F.p m * y = (2 : ℝ)⁻¹ • peirceHalf (F.p m) y := by
    intro m hm
    calc F.p m * y = F.p m * (peirceOne (F.p m) y + peirceHalf (F.p m) y + peirceZero (F.p m) y)
        := by
          rw [peirce_add_add]
      _ = (2 : ℝ)⁻¹ • peirceHalf (F.p m) y := by
          rw [mul_add, mul_add, mul_peirceOne (F.orthIdem.idem m),
            mul_peirceHalf (F.orthIdem.idem m), mul_peirceZero (F.orthIdem.idem m), hone m hm]
          module
  have hsum : ∑ m, F.p m * y = y := by
    rw [← Finset.sum_mul, F.complete, EuclideanJordanAlgebra.one_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hy] at hsum
  have hstep : ∑ m ∈ Finset.univ.erase k, F.p m * y
      = (2 : ℝ)⁻¹ • ∑ m ∈ Finset.univ.erase k, peirceHalf (F.p m) y := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun m hm => hmul m (Finset.ne_of_mem_erase hm)
  rw [hstep] at hsum
  have : (2 : ℝ)⁻¹ • ∑ m ∈ Finset.univ.erase k, peirceHalf (F.p m) y = (2 : ℝ)⁻¹ • y := by
    linear_combination (norm := module) hsum
  exact smul_right_injective J (by norm_num : (2 : ℝ)⁻¹ ≠ 0) this

/-! ## Spanning -/

/-- **The frame Peirce decomposition, spanning half.**

The proof is not an expansion of `∏ᵢ (P₁(pᵢ) + P½(pᵢ) + P₀(pᵢ))`.  Set
`z := x - ∑ᵢ P₁(pᵢ) x - ½ ∑ᵢ P½(pᵢ) x`; the composition lemmas above kill `P₁(p k) z` and
`P½(p k) z` for every `k`, so `z = P₀(p k) z` and hence `p k ∘ z = 0` for every `k`, and
completeness gives `z = 1 ∘ z = 0`. -/
theorem frame_peirce_span (F : JordanFrame J n) (x : J) :
    x = ∑ i, peirceOne (F.p i) x + (2 : ℝ)⁻¹ • ∑ i, peirceHalf (F.p i) x := by
  classical
  have e1 : ∀ k, ∑ i, peirceOne (F.p k) (peirceOne (F.p i) x) = peirceOne (F.p k) x := by
    intro k
    rw [Finset.sum_eq_single k (fun b _ hb => peirceOne_peirceOne_of_ne F x hb)
      (fun h => absurd (Finset.mem_univ k) h)]
    exact peirceOne_peirceOne_self F x
  have e2 : ∀ k, ∑ i, peirceOne (F.p k) (peirceHalf (F.p i) x) = 0 := fun k =>
    Finset.sum_eq_zero fun i _ => by
      by_cases h : i = k
      · subst h; exact peirceOne_peirceHalf_self F x
      · exact peirceOne_peirceHalf_of_ne F x h
  have e3 : ∀ k, ∑ i, peirceHalf (F.p k) (peirceOne (F.p i) x) = 0 := fun k =>
    Finset.sum_eq_zero fun i _ => by
      by_cases h : i = k
      · subst h; exact peirceHalf_peirceOne_self F x
      · exact peirceHalf_peirceOne_of_ne F x h
  have e4 : ∀ k, ∑ i, peirceHalf (F.p k) (peirceHalf (F.p i) x)
      = peirceHalf (F.p k) x + peirceHalf (F.p k) x := by
    intro k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    congr 1
    · exact peirceHalf_peirceHalf_self F x
    · rw [Finset.sum_congr rfl fun i hi => peirceHalf_peirceHalf_comm F x
        (Finset.ne_of_mem_erase hi)]
      exact sum_peirceHalf_erase F (mul_peirceHalf (F.orthIdem.idem k) x)
  obtain ⟨z, hzdef⟩ : ∃ z : J,
      z = x - ∑ i, peirceOne (F.p i) x - (2 : ℝ)⁻¹ • ∑ i, peirceHalf (F.p i) x := ⟨_, rfl⟩
  have hA : ∀ k, peirceOne (F.p k) z = 0 := by
    intro k
    rw [hzdef]
    simp only [map_sub, map_smul, map_sum]
    rw [e1 k, e2 k]
    module
  have hB : ∀ k, peirceHalf (F.p k) z = 0 := by
    intro k
    rw [hzdef]
    simp only [map_sub, map_smul, map_sum]
    rw [e3 k, e4 k]
    module
  have hzero : ∀ k, F.p k * z = 0 := by
    intro k
    have hsplit := peirce_add_add (F.p k) z
    rw [hA k, hB k, zero_add, zero_add] at hsplit
    rw [← hsplit]
    exact mul_peirceZero (F.orthIdem.idem k) z
  have hz0 : z = 0 := by
    have : (∑ i, F.p i) * z = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => hzero i
    rwa [F.complete, EuclideanJordanAlgebra.one_mul] at this
  rw [hzdef, sub_sub, sub_eq_zero] at hz0
  exact hz0

/-! ## The block projections -/

open scoped Classical in
/-- The projection onto `V_{ij}`: `P₁(p i)` on the diagonal, `P½(p i) ∘ P½(p j)` off it. -/
def blockProj (F : JordanFrame J n) (i j : Fin n) : J →ₗ[ℝ] J :=
  if i = j then peirceOne (F.p i) else (peirceHalf (F.p i)).comp (peirceHalf (F.p j))

theorem blockProj_diag (F : JordanFrame J n) (i : Fin n) :
    blockProj F i i = peirceOne (F.p i) := by
  unfold blockProj; simp

theorem blockProj_off (F : JordanFrame J n) {i j : Fin n} (h : i ≠ j) :
    blockProj F i j = (peirceHalf (F.p i)).comp (peirceHalf (F.p j)) := by
  unfold blockProj; simp [h]

/-- `blockProj F i j` is the identity on `V_{ij}`. -/
theorem blockProj_apply_eq_self (F : JordanFrame J n) {i j : Fin n} {x : J}
    (hx : x ∈ frameBlockRaw F i j) : blockProj F i j x = x := by
  by_cases hij : i = j
  · subst hij
    rw [blockProj_diag]
    exact peirceOne_of_eigen (mem_frameBlockRaw_diag.mp hx)
  · obtain ⟨hi, hj⟩ := (mem_frameBlockRaw_off hij).mp hx
    rw [blockProj_off F hij, LinearMap.comp_apply, peirceHalf_of_eigen_half hj,
      peirceHalf_of_eigen_half hi]

/-- `blockProj F a b` annihilates every *other* block. -/
theorem blockProj_apply_eq_zero (F : JordanFrame J n) {a b c d : Fin n} {x : J}
    (hne : s(c, d) ≠ s(a, b)) (hx : x ∈ frameBlockRaw F c d) : blockProj F a b x = 0 := by
  have hne' : ¬((c = a ∧ d = b) ∨ (c = b ∧ d = a)) := fun h => hne (Sym2.eq_iff.mpr h)
  have hL : ¬(a = c ∧ b = d) := fun h => hne' (Or.inl ⟨h.1.symm, h.2.symm⟩)
  have hR : ¬(a = d ∧ b = c) := fun h => hne' (Or.inr ⟨h.2.symm, h.1.symm⟩)
  by_cases hab : a = b
  · subst hab
    rw [blockProj_diag]
    by_cases hac : a = c
    · have had : a ≠ d := fun h => hL ⟨hac, h⟩
      have hcd : c ≠ d := hac ▸ had
      have := ((mem_frameBlockRaw_off hcd).mp hx).1
      rw [← hac] at this
      exact peirceOne_of_eigen_half this
    · by_cases had : a = d
      · have hbc : a ≠ c := hac
        have hcd : c ≠ d := fun h => hac (had.trans h.symm)
        have := ((mem_frameBlockRaw_off hcd).mp hx).2
        rw [← had] at this
        exact peirceOne_of_eigen_half this
      · exact peirceOne_of_eigen_zero (frameBlockRaw_mul_eq_zero F hac had hx)
  · rw [blockProj_off F hab, LinearMap.comp_apply]
    by_cases hac : a = c
    · have hbd : b ≠ d := fun h => hL ⟨hac, h⟩
      have hbc : b ≠ c := fun h => hab (hac.trans h.symm)
      rw [peirceHalf_of_eigen_zero (frameBlockRaw_mul_eq_zero F hbc hbd hx), map_zero]
    · by_cases had : a = d
      · have hbc : b ≠ c := fun h => hR ⟨had, h⟩
        have hbd : b ≠ d := fun h => hab (had.trans h.symm)
        rw [peirceHalf_of_eigen_zero (frameBlockRaw_mul_eq_zero F hbc hbd hx), map_zero]
      · have hax : F.p a * x = 0 := frameBlockRaw_mul_eq_zero F hac had hx
        refine peirceHalf_of_eigen_zero ?_
        rw [mul_peirceHalf_comm_orth (F.orthIdem.idem a) (F.orthIdem.orth b a (Ne.symm hab)),
          hax, map_zero]

/-! ## `DirectSum.IsInternal` -/

/-- For `i ≠ m`, `P½(p m) P½(p i) x` lies in `V_{im}`. -/
theorem peirceHalf_peirceHalf_mem (F : JordanFrame J n) {i m : Fin n} (him : i ≠ m) (x : J) :
    peirceHalf (F.p m) (peirceHalf (F.p i) x) ∈ frameBlockRaw F i m := by
  refine (mem_frameBlockRaw_off him).mpr ⟨?_, mul_peirceHalf (F.orthIdem.idem m) _⟩
  rw [mul_peirceHalf_comm_orth (F.orthIdem.idem i) (F.orthIdem.orth m i (Ne.symm him)),
    mul_peirceHalf (F.orthIdem.idem i), map_smul]

theorem peirceOne_mem_frameBlock (F : JordanFrame J n) (i : Fin n) (x : J) :
    peirceOne (F.p i) x ∈ frameBlock F s(i, i) :=
  mem_frameBlockRaw_diag.mpr (mul_peirceOne (F.orthIdem.idem i) x)

/-- **The blocks span.** -/
theorem frameBlock_iSup_eq_top (F : JordanFrame J n) : ⨆ s, frameBlock F s = ⊤ := by
  classical
  refine eq_top_iff.mpr fun x _ => ?_
  have hhalf : ∀ i, peirceHalf (F.p i) x ∈ ⨆ s, frameBlock F s := by
    intro i
    rw [← sum_peirceHalf_erase F (mul_peirceHalf (F.orthIdem.idem i) x)]
    refine Submodule.sum_mem _ fun m hm => Submodule.mem_iSup_of_mem s(i, m) ?_
    exact peirceHalf_peirceHalf_mem F (Ne.symm (Finset.ne_of_mem_erase hm)) x
  rw [frame_peirce_span F x]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_)
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => hhalf i))
  exact Submodule.mem_iSup_of_mem s(i, i) (peirceOne_mem_frameBlock F i x)

/-- **The blocks are independent.** -/
theorem frameBlock_iSupIndep (F : JordanFrame J n) : iSupIndep (frameBlock F) := by
  classical
  intro s
  induction s using Sym2.ind with
  | _ a b =>
    have hker : (⨆ t, ⨆ (_ : t ≠ s(a, b)), frameBlock F t)
        ≤ LinearMap.ker (blockProj F a b) := by
      refine iSup_le fun t => ?_
      induction t using Sym2.ind with
      | _ c d =>
        refine iSup_le fun ht => fun y hy => ?_
        simp only [LinearMap.mem_ker]
        exact blockProj_apply_eq_zero F ht hy
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 : blockProj F a b x = x := blockProj_apply_eq_self F hx
    have h0 : blockProj F a b x = 0 := hker hx'
    rw [← h1, h0]

/-- **The frame Peirce decomposition.**  `J = ⨁_{i ≤ j} V_{ij}`. -/
theorem frameBlock_isInternal (F : JordanFrame J n) : DirectSum.IsInternal (frameBlock F) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨frameBlock_iSupIndep F, frameBlock_iSup_eq_top F⟩

end EuclideanJordan
