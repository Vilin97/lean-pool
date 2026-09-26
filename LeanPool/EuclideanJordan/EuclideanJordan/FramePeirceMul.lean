/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.FramePeirce



/-!
# The Faraut–Korányi multiplication table relative to a Jordan frame

`EuclideanJordan/FramePeirce.lean` builds the blocks `V_{ij}` of a Jordan frame `F = (p₁, …,
    pₙ)` and proves
`J = ⨁_{i ≤ j} V_{ij}`.  This file multiplies them.  The table:

* `V_{ii} ∘ V_{ii} ⊆ V_{ii}` (`frameBlockRaw_diag_mul_diag`),
* `V_{ii} ∘ V_{ij} ⊆ V_{ij}` (`frameBlockRaw_diag_mul_off`),
* `V_{ij} ∘ V_{jk} ⊆ V_{ik}` for `i, j, k` distinct (`frameBlockRaw_mul_middle`),
* `V_{ij} ∘ V_{kl} = 0` when `{i,j} ∩ {k,l} = ∅` (`frameBlockRaw_mul_disjoint`),
* `V_{ij} ∘ V_{ij} ⊆ ℝ∙pᵢ + ℝ∙pⱼ` (`frameBlockRaw_mul_self_eq`),

together with `dim V_{ii} = 1` (`finrank_frameBlockRaw_self`) and the eigenvalue rule
`pᵢ ∘ x = ½ • x` on `V_{ij}` (`frameBlockRaw_mul_left_half`).  The last three lines of the table
are also stated as literal submodule inclusions through `EuclideanJordan/Class.lean`'s bundled
    `jmulₗ` and
`Submodule.map₂`, in the `Map₂` section; there is no `Mul` on `Submodule ℝ J` to state them with,
because Mathlib's `Submodule.mul` instance is declared for `[Semiring A] [Module R A]
[IsScalarTower R A A]` — an associative unital ring — which a Jordan algebra is not.

## ★ Where the coefficients come from — the plan's one unpriced step

The build plan priced every rule here as a short consequence of `EuclideanJordan/PeirceMul.lean`'s
single-idempotent rules **except** `V_{ij} ∘ V_{ij} ⊆ ℝ∙pᵢ + ℝ∙pⱼ`, which it left explicitly
unpriced: `eigen_half_mul_half` gives the projection identity, but *pinning the two coefficients*
was expected to need the trace form, and no in-tree lemma had been matched to that step.

**The trace form is not used.**  The step is the frame's completeness.  For `x, y ∈ V_{ij}` put
`z := x ∘ y`.  Every `p_k` with `k ∉ {i,j}` kills both factors, so `eigen_zero_mul_zero` kills
`z`; hence

    z = 1 ∘ z = (∑ₖ p_k) ∘ z = p_i ∘ z + p_j ∘ z,

which is `frameBlockRaw_mul_self_split`.  And `eigen_half_mul_half` at `p_i` says exactly
`p_i ∘ (p_i ∘ z) = p_i ∘ z`, i.e. `p_i ∘ z ∈ J₂(p_i) = V_{ii}` — so the two summands are already
in the two diagonal blocks (`frameBlockRaw_mul_self_left_mem`).  That much is the *decomposition*,
and it needs neither primitivity nor finite-dimensionality.

The **coefficients** then come from `V_{ii}` being a line, not from an inner-product computation:
`p_i ∘ z = a • p_i` because `dim V_{ii} = 1`.  So the sub-item the plan could not price is really
two independent facts, and the trace form is in neither.  What *is* load-bearing is the
completeness of the frame, used once, in `frameBlockRaw_mul_self_split`.

## ★ Primitivity is spent here

`EuclideanJordan/FramePeirce.lean` records that no proof in it uses primitivity at all.  This
    file is not,
however, the first in the tree to *touch* the `IsPrimitive` clauses, and an earlier draft of this
docstring said so wrongly: `EuclideanJordan/Rank.lean`'s `JordanFrame.p_ne_zero` consumes the
    `ne_zero` clause,
and `EuclideanJordan/FrameExists.lean`'s `isPrimitive_coe_of_peirceOne` /
    `isPrimitive_coe_of_peirceZero`
consume the splitting clause `∀ d, d ∘ d = d → c ∘ d = d → d = 0 ∨ d = c` in full.  What those two
do with it is *transport* it across the coercion `↥(J₂(c)) → J`; they extract no structural
consequence from it.

This file is the first to spend it.  Within this file the splitting clause is used at exactly one
theorem, `peirceOneSub_eq_span_of_isPrimitive`, which runs `EuclideanJordan/Class.lean`'s
`spectral_resolution_complete'` **inside** `J₂(c)` — legitimate because
`EuclideanJordan/PeirceSubalgebra.lean` gives `J₂(c)` its own `EuclideanJordanAlgebra` instance
    with unit `c`
— and reads off that every idempotent appearing in the resolution is `0` or `1`, by
`EuclideanJordan/Rank.lean`'s `isPrimitive_iff_of_idem`.  A resolution all of whose idempotents
    are `0` or `1`
has every term a real multiple of `1 = c`.

Orthogonality of the resolution is *not* used in that argument, only the two-valuedness; that is
why the proof does not have to rule out two indices both landing on `1`.

The rest of the `Primitive` section is downstream of that one theorem, except that
`finrank_frameBlockRaw_self` also uses the `ne_zero` clause, through `JordanFrame.p_ne_zero`.
Everything *before* the `Primitive` section runs on `F.orthIdem` and `F.complete` alone.

## Scope


★ `rank J = n` is **not** available and nothing here is a step towards it — `dim V_{ii} = 1` is a
statement about one block of a frame carried as data, not about the rank of `J`.

★ **There is a carrier and a named frame**, so the theorems below are not statements about an
empty class: `EuclideanJordan/HermitianCarrier.lean` supplies
    `instEuclideanJordanAlgebraHermitianMat` and
`diagJordanFrame : JordanFrame (HermitianMat n ℂ) (Fintype.card n)`.  `frameBlockRaw_mul_self_eq` is
consumed at `F = diagJordanFrame` through `EuclideanJordan/Connection.lean`'s `exists_sq_smul`.

★ Do not quote this paragraph for the carrier's state; read
`EuclideanJordan/HermitianCarrier.lean`.
The durable part is the one below.

★ `rank J = n` is not proved for **any** frame, `diagJordanFrame` included:
    `EuclideanJordan/Rank.lean`
bounds a frame's cardinality by the rank and by the dimension, and nothing anywhere converts
`dim V_{ii} = 1` into a statement about `rank J`.
-/

@[expose] public section

noncomputable section

namespace EuclideanJordan

open EuclideanJordanAlgebra

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]
variable {n : ℕ}

/-! ## The eigenvalue rule on a block -/

/-- **`pᵢ ∘ x = ½ • x` for `x ∈ V_{ij}`, `i ≠ j`.**  Definitional at
`EuclideanJordan/FramePeirce.lean`'s
`frameBlockRaw`; named because the multiplication rules below take it as an argument constantly. -/
theorem frameBlockRaw_mul_left_half (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) : F.p i * x = (2 : ℝ)⁻¹ • x :=
  ((mem_frameBlockRaw_off hij).mp hx).1

/-- The same at the second index. -/
theorem frameBlockRaw_mul_right_half (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x : J}
    (hx : x ∈ frameBlockRaw F i j) : F.p j * x = (2 : ℝ)⁻¹ • x :=
  ((mem_frameBlockRaw_off hij).mp hx).2

/-! ## The table

Each rule is read off the single-idempotent Faraut–Korányi rules of
    `EuclideanJordan/PeirceMul.lean`, applied
at one frame member at a time.  `frameBlockRaw_mul_eq_zero` (in
    `EuclideanJordan/FramePeirce.lean`) supplies
the `0`-eigenvalue of every frame member outside a block's index pair. -/

/-- **`V_{ii} ∘ V_{ii} ⊆ V_{ii}`** — the diagonal block is a subalgebra.  This is
`eigen_one_mul_one` verbatim; `EuclideanJordan/PeirceSubalgebra.lean` already uses it as the
    `Mul` field of
`J₂(pᵢ)`. -/
theorem frameBlockRaw_diag_mul_diag (F : JordanFrame J n) {i : Fin n} {x y : J}
    (hx : x ∈ frameBlockRaw F i i) (hy : y ∈ frameBlockRaw F i i) :
    x * y ∈ frameBlockRaw F i i :=
  mem_frameBlockRaw_diag.mpr
    (eigen_one_mul_one (F.orthIdem.idem i) (mem_frameBlockRaw_diag.mp hx)
      (mem_frameBlockRaw_diag.mp hy))

/-- **`V_{ii} ∘ V_{ij} ⊆ V_{ij}`.**  At `pᵢ` this is `eigen_one_mul_half`; at `pⱼ` it is
`eigen_zero_mul_half`, because `pⱼ` annihilates `J₂(pᵢ)`. -/
theorem frameBlockRaw_diag_mul_off (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x y : J}
    (hx : x ∈ frameBlockRaw F i i) (hy : y ∈ frameBlockRaw F i j) :
    x * y ∈ frameBlockRaw F i j := by
  have hxi : F.p i * x = x := mem_frameBlockRaw_diag.mp hx
  have hxj : F.p j * x = 0 :=
    frameBlockRaw_mul_eq_zero F (Ne.symm hij) (Ne.symm hij) hx
  refine (mem_frameBlockRaw_off hij).mpr ⟨?_, ?_⟩
  · exact eigen_one_mul_half (F.orthIdem.idem i) hxi (frameBlockRaw_mul_left_half F hij hy)
  · exact eigen_zero_mul_half (F.orthIdem.idem j) hxj (frameBlockRaw_mul_right_half F hij hy)

/-- **`V_{ij} ∘ V_{jk} ⊆ V_{ik}` for `i, j, k` distinct.**

`pᵢ` halves `x` and kills `y`, `p_k` kills `x` and halves `y`; `eigen_zero_mul_half` at each of
them is the whole proof.  The middle index enters only through the eigenvalue hypotheses on `x`
and `y`: nothing has to be shown about `pⱼ ∘ (x ∘ y)`, because membership in `V_{ik}` is a
condition at `pᵢ` and `p_k` only. -/
theorem frameBlockRaw_mul_middle (F : JordanFrame J n) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) {x y : J} (hx : x ∈ frameBlockRaw F i j)
    (hy : y ∈ frameBlockRaw F j k) : x * y ∈ frameBlockRaw F i k := by
  have hyi : F.p i * y = 0 := frameBlockRaw_mul_eq_zero F hij hik hy
  have hxk : F.p k * x = 0 := frameBlockRaw_mul_eq_zero F (Ne.symm hik) (Ne.symm hjk) hx
  refine (mem_frameBlockRaw_off hik).mpr ⟨?_, ?_⟩
  · have h := eigen_zero_mul_half (F.orthIdem.idem i) hyi (frameBlockRaw_mul_left_half F hij hx)
    rwa [_root_.mul_comm y x] at h
  · exact eigen_zero_mul_half (F.orthIdem.idem k) hxk (frameBlockRaw_mul_right_half F hjk hy)

/-- **`V_{ij} ∘ V_{kl} = 0` when `{i,j}` and `{k,l}` are disjoint** — the two blocks annihilate
each other, not merely land in a common block.

Both index pairs are allowed to be diagonal.  If `i = j` then `x ∈ J₂(pᵢ)` and `y ∈ J₀(pᵢ)`, and
`eigen_one_mul_zero` finishes; otherwise the same argument runs at the rank-two idempotent
`q = pᵢ + pⱼ`, with `x ∈ J₂(q)` by `mem_J2_of_half_half` and `y ∈ J₀(q)` because `pᵢ` and `pⱼ`
each kill `y`. -/
theorem frameBlockRaw_mul_disjoint (F : JordanFrame J n) {i j k l : Fin n} (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) {x y : J} (hx : x ∈ frameBlockRaw F i j)
    (hy : y ∈ frameBlockRaw F k l) : x * y = 0 := by
  have hyi : F.p i * y = 0 := frameBlockRaw_mul_eq_zero F hik hil hy
  have hyj : F.p j * y = 0 := frameBlockRaw_mul_eq_zero F hjk hjl hy
  by_cases hij : i = j
  · subst hij
    exact eigen_one_mul_zero (F.orthIdem.idem i) (mem_frameBlockRaw_diag.mp hx) hyi
  · have hq : (F.p i + F.p j) * (F.p i + F.p j) = F.p i + F.p j :=
      add_idem_of_orthogonal (F.orthIdem.idem i) (F.orthIdem.idem j) (F.orthIdem.orth i j hij)
    have hqx : (F.p i + F.p j) * x = x :=
      mem_J2_of_half_half (frameBlockRaw_mul_left_half F hij hx)
        (frameBlockRaw_mul_right_half F hij hx)
    have hqy : (F.p i + F.p j) * y = 0 := by rw [_root_.add_mul, hyi, hyj, add_zero]
    exact eigen_one_mul_zero hq hqx hqy

/-! ## `V_{ij} ∘ V_{ij}`: the decomposition, before any coefficients

★ These three are the plan's unpriced step, and they use no trace form, no primitivity and no
finite-dimensionality — only `F.complete` and `EuclideanJordan/PeirceMul.lean`. -/

/-- **`x ∘ y = pᵢ ∘ (x ∘ y) + pⱼ ∘ (x ∘ y)` for `x, y ∈ V_{ij}`.**

The one place completeness is used: every frame member outside `{i,j}` kills both factors, hence
their product by `eigen_zero_mul_zero`, so `∑ₖ p_k ∘ z` collapses to two terms and `∑ₖ p_k = 1`
says that sum is `z`. -/
theorem frameBlockRaw_mul_self_split (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x y : J}
    (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F i j) :
    x * y = F.p i * (x * y) + F.p j * (x * y) := by
  classical
  have hsum : ∑ k, F.p k * (x * y) = x * y := by
    rw [← Finset.sum_mul, F.complete, EuclideanJordanAlgebra.one_mul]
  have hpair : ∑ k ∈ ({i, j} : Finset (Fin n)), F.p k * (x * y) = ∑ k, F.p k * (x * y) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro k _ hk
    have hki : k ≠ i := fun h => hk (by simp [h])
    have hkj : k ≠ j := fun h => hk (by simp [h])
    exact eigen_zero_mul_zero (F.orthIdem.idem k)
      (frameBlockRaw_mul_eq_zero F hki hkj hx) (frameBlockRaw_mul_eq_zero F hki hkj hy)
  rw [Finset.sum_pair hij] at hpair
  exact (hpair.trans hsum).symm

/-- The first summand of `frameBlockRaw_mul_self_split` lies in the diagonal block `V_{ii}`.
This is `eigen_half_mul_half` read as a membership: `L_{pᵢ}² = L_{pᵢ}` on `x ∘ y` says precisely
that `pᵢ ∘ (x ∘ y)` is fixed by `L_{pᵢ}`. -/
theorem frameBlockRaw_mul_self_left_mem (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j)
    {x y : J} (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F i j) :
    F.p i * (x * y) ∈ frameBlockRaw F i i :=
  mem_frameBlockRaw_diag.mpr
    (eigen_half_mul_half (F.orthIdem.idem i) (frameBlockRaw_mul_left_half F hij hx)
      (frameBlockRaw_mul_left_half F hij hy))

/-- The second summand lies in `V_{jj}`. -/
theorem frameBlockRaw_mul_self_right_mem (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j)
    {x y : J} (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F i j) :
    F.p j * (x * y) ∈ frameBlockRaw F j j :=
  mem_frameBlockRaw_diag.mpr
    (eigen_half_mul_half (F.orthIdem.idem j) (frameBlockRaw_mul_right_half F hij hx)
      (frameBlockRaw_mul_right_half F hij hy))

/-- **`V_{ij} ∘ V_{ij} ⊆ V_{ii} ⊔ V_{jj}`**, the coefficient-free form. -/
theorem frameBlockRaw_mul_self_mem_sup (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j)
    {x y : J} (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F i j) :
    x * y ∈ frameBlockRaw F i i ⊔ frameBlockRaw F j j := by
  rw [frameBlockRaw_mul_self_split F hij hx hy]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (frameBlockRaw_mul_self_left_mem F hij hx hy))
    (Submodule.mem_sup_right (frameBlockRaw_mul_self_right_mem F hij hx hy))

/-! ## Primitivity: the diagonal block is a line

★ The `JordanFrame.primitive` field is consumed here and nowhere else in the frame Peirce
layer. -/

section Primitive

variable [FiniteDimensional ℝ J]

/-- **`J₂(c) = ℝ ∙ c` for a primitive idempotent `c`.**

`EuclideanJordan/PeirceSubalgebra.lean` makes `J₂(c)` a Euclidean Jordan algebra with unit `c`, so
`EuclideanJordan/Class.lean`'s `spectral_resolution_complete'` applies *inside* it: every element is
`∑ₖ λ_k • e_k` with each `e_k` idempotent in `J₂(c)`.  `EuclideanJordan/Rank.lean`'s
`isPrimitive_iff_of_idem` says each `e_k` is `0` or `1`, and `1 = c`; so every term is a real
multiple of `c`.

Orthogonality of the `e_k` is not used — only that each is `0` or `1`. -/
theorem peirceOneSub_eq_span_of_isPrimitive {c : J} (hp : IsPrimitive c) :
    peirceOneSub hp.idem = Submodule.span ℝ {c} := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨m, e, lam, hfam, -, hrep⟩ :=
      spectral_resolution_complete' (J := ↥(peirceOneSub hp.idem)) ⟨x, hx⟩
    have hcoe : x = ∑ k, lam k • ((e k : ↥(peirceOneSub hp.idem)) : J) := by
      have := congrArg (fun z : ↥(peirceOneSub hp.idem) => (z : J)) hrep
      simpa using this
    rw [hcoe]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rcases (isPrimitive_iff_of_idem hp.idem hp.ne_zero).mp hp (e k) (hfam.idem k) with h | h
    · rw [h]; simp
    · rw [h]; exact Submodule.mem_span_singleton_self c
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hp.idem

/-- `dim J₂(c) = 1` for a primitive idempotent — the definition of primitivity, cashed out as a
dimension. -/
theorem finrank_peirceOneSub_of_isPrimitive {c : J} (hp : IsPrimitive c) :
    Module.finrank ℝ ↥(peirceOneSub hp.idem) = 1 := by
  rw [peirceOneSub_eq_span_of_isPrimitive hp]
  exact finrank_span_singleton hp.ne_zero

/-- **`V_{ii} = ℝ ∙ pᵢ`.** -/
theorem frameBlockRaw_self_eq_span (F : JordanFrame J n) (i : Fin n) :
    frameBlockRaw F i i = Submodule.span ℝ {F.p i} := by
  rw [frameBlockRaw_self F i]
  exact peirceOneSub_eq_span_of_isPrimitive (F.primitive i)

/-- **`dim V_{ii} = 1`.**  The statement the coordinatization rests on. -/
theorem finrank_frameBlockRaw_self (F : JordanFrame J n) (i : Fin n) :
    Module.finrank ℝ ↥(frameBlockRaw F i i) = 1 := by
  rw [frameBlockRaw_self_eq_span F i]
  exact finrank_span_singleton (F.p_ne_zero i)

/-- `dim V_{ii} = 1`, in the `Sym2`-indexed vocabulary `frameBlock` uses. -/
theorem finrank_frameBlock_diag (F : JordanFrame J n) (i : Fin n) :
    Module.finrank ℝ ↥(frameBlock F s(i, i)) = 1 :=
  finrank_frameBlockRaw_self F i

/-- An element of `V_{ii}` is a real multiple of `pᵢ` — `frameBlockRaw_self_eq_span` read
pointwise. -/
theorem exists_smul_of_mem_frameBlockRaw_self (F : JordanFrame J n) {i : Fin n} {x : J}
    (hx : x ∈ frameBlockRaw F i i) : ∃ a : ℝ, x = a • F.p i := by
  rw [frameBlockRaw_self_eq_span F i, Submodule.mem_span_singleton] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

/-- **`V_{ij} ∘ V_{ij} ⊆ ℝ∙pᵢ + ℝ∙pⱼ`**, with the coefficients exhibited.

`frameBlockRaw_mul_self_split` puts the product in `V_{ii} ⊕ V_{jj}`; `dim V_{ii} = 1` turns each
summand into a scalar multiple of a frame member. -/
theorem frameBlockRaw_mul_self_eq (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) {x y : J}
    (hx : x ∈ frameBlockRaw F i j) (hy : y ∈ frameBlockRaw F i j) :
    ∃ a b : ℝ, x * y = a • F.p i + b • F.p j := by
  obtain ⟨a, ha⟩ :=
    exists_smul_of_mem_frameBlockRaw_self F (frameBlockRaw_mul_self_left_mem F hij hx hy)
  obtain ⟨b, hb⟩ :=
    exists_smul_of_mem_frameBlockRaw_self F (frameBlockRaw_mul_self_right_mem F hij hx hy)
  exact ⟨a, b, by rw [frameBlockRaw_mul_self_split F hij hx hy, ha, hb]⟩

end Primitive

/-! ## The table as submodule inclusions

`Submodule.map₂ (jmulₗ J) P Q` is the submodule generated by the products, so these are the
literal `⊆` statements of the module docstring.  `EuclideanJordan/Class.lean`'s `jmulₗ` is the
    bundled form of
the same product (`jmulₗ_apply` is `rfl`). -/

section Map₂

/-- `V_{ij} ∘ V_{jk} ⊆ V_{ik}`. -/
theorem map₂_frameBlockRaw_middle_le (F : JordanFrame J n) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    Submodule.map₂ (jmulₗ J) (frameBlockRaw F i j) (frameBlockRaw F j k)
      ≤ frameBlockRaw F i k :=
  Submodule.map₂_le.mpr fun _ hx _ hy => frameBlockRaw_mul_middle F hij hjk hik hx hy

/-- `V_{ij} ∘ V_{kl} = 0` for disjoint index pairs. -/
theorem map₂_frameBlockRaw_disjoint (F : JordanFrame J n) {i j k l : Fin n} (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Submodule.map₂ (jmulₗ J) (frameBlockRaw F i j) (frameBlockRaw F k l) = ⊥ :=
  le_bot_iff.mp <| Submodule.map₂_le.mpr fun _ hx _ hy =>
    (Submodule.mem_bot ℝ).mpr (frameBlockRaw_mul_disjoint F hik hil hjk hjl hx hy)

/-- `V_{ij} ∘ V_{ij} ⊆ V_{ii} ⊔ V_{jj}`. -/
theorem map₂_frameBlockRaw_self_le (F : JordanFrame J n) {i j : Fin n} (hij : i ≠ j) :
    Submodule.map₂ (jmulₗ J) (frameBlockRaw F i j) (frameBlockRaw F i j)
      ≤ frameBlockRaw F i i ⊔ frameBlockRaw F j j :=
  Submodule.map₂_le.mpr fun _ hx _ hy => frameBlockRaw_mul_self_mem_sup F hij hx hy

/-- `V_{ij} ∘ V_{ij} ⊆ ℝ∙pᵢ + ℝ∙pⱼ`. -/
theorem map₂_frameBlockRaw_self_le_span [FiniteDimensional ℝ J] (F : JordanFrame J n)
    {i j : Fin n} (hij : i ≠ j) :
    Submodule.map₂ (jmulₗ J) (frameBlockRaw F i j) (frameBlockRaw F i j)
      ≤ Submodule.span ℝ {F.p i} ⊔ Submodule.span ℝ {F.p j} := by
  rw [← frameBlockRaw_self_eq_span F i, ← frameBlockRaw_self_eq_span F j]
  exact map₂_frameBlockRaw_self_le F hij

end Map₂

end EuclideanJordan
