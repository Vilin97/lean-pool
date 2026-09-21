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
import LeanPool.EuclideanJordan.EuclideanJordan.PeirceSubalgebra


/-!
# Primitive idempotents, Jordan frames, and rank

`EuclideanJordan/Frame.lean` carries `IsOrthIdemFamily`: a family of pairwise-orthogonal idempotents, with
completeness deliberately left out.  This file adds the two conditions that turn such a family
into a *Jordan frame* — every member primitive, and the family complete — and defines the rank.

## What the rank is here, and the chapter that is not needed

★ **Frame conjugacy is not proved and is not needed.**  "All Jordan frames have the same
cardinality" looks like a prerequisite — "rank `n ≥ 3`" seems meaningless before it — and its
classical proof (Faraut–Korányi Thm IV.2.5, conjugacy of frames under `Aut(J)`) is a chapter of
its own.  The direction saves it.  The rank is *defined* as the size of a Jordan frame — a complete
system of orthogonal primitive idempotents `F = {p₁, …, pₙ}` with `∑ᵢ pᵢ = e` (FK IV.2) — so a
hypothesis "rank `= n`" **implies** "there exists a Jordan frame of cardinality `n`".  Taking
the latter as the Lean hypothesis makes the Lean theorem weaker or equal, which is the correct
direction for an import; and well-definedness falls out downstream, since once `J ≅ H_n(K)` the
dimension pins `n`.

★ So this file's `rank` is deliberately **not** the load-bearing object, and downstream modules
should carry a `JordanFrame J n` as *data* rather than reason about the number `rank J`.  What
is proved about `rank J` is exactly two inequalities: `JordanFrame.card_le_rank` (a frame's
cardinality is at most the rank) and `rank_le_finrank`.  The reverse of the first —
`rank J = n` for a frame of cardinality `n` — is **not** proved here, and nothing in this file
is a step towards it: `rank J` is a supremum over *all* orthogonal families of nonzero
idempotents, primitive or not, and bounding such a family by `n` needs either the frame Peirce
decomposition or frame conjugacy, neither of which is available yet.  Do not quote `rank J = n`
off this file.

## The linear-independence argument is already in the tree

Orthogonal nonzero idempotents are linearly independent, and the argument is
`EuclideanJordan/Order.lean`'s `inner_left_coeff` verbatim: idempotency and then associativity of the inner
product give `⟪pₖ, pᵢ⟫ = ⟪pₖ ∘ pₖ, pᵢ⟫ = ⟪pₖ, pₖ ∘ pᵢ⟫ = 0` for `i ≠ k`, so pairing a vanishing
combination against `pₖ` reads off `gₖ ‖pₖ‖² = 0`.  That lemma is stated in `EuclideanJordan/Order.lean`'s bilinear-map vocabulary;
`EuclideanJordan/Class.lean`'s `jmulₗ` and `jmulₗ_inner_assoc` are what let it be applied at the class
without restating it.

## Scope

-/

noncomputable section

namespace EuclideanJordan

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

/-! ## Primitivity -/

/-- A **primitive idempotent**: a nonzero idempotent that cannot be split, i.e. the only
idempotents of the Peirce subalgebra `J₂(c)` are `0` and `c` itself.

The third clause is stated in the ambient algebra — `d` idempotent with `c ∘ d = d`, which is
membership in `peirceOneSub` — rather than over the subtype, so that it can be checked without
first producing the subalgebra.  `isPrimitive_iff_of_idem` below is the two readings'
equivalence. -/
def IsPrimitive (c : J) : Prop :=
  c * c = c ∧ c ≠ 0 ∧ ∀ d : J, d * d = d → c * d = d → d = 0 ∨ d = c

theorem IsPrimitive.idem {c : J} (h : IsPrimitive c) : c * c = c := h.1

theorem IsPrimitive.ne_zero {c : J} (h : IsPrimitive c) : c ≠ 0 := h.2.1

theorem IsPrimitive.eq_zero_or_eq {c : J} (h : IsPrimitive c) {d : J} (hd : d * d = d)
    (hcd : c * d = d) : d = 0 ∨ d = c := h.2.2 d hd hcd

/-- Primitivity of `c`, read *inside* `J₂(c)`: `c` is primitive exactly when the only
idempotents of the Peirce subalgebra are its zero and its unit.  The intended consumer is the
`dim V_ii = 1` step of the frame Peirce decomposition, which runs the spectral theorem inside
`J₂(pᵢ)`; that step is `EuclideanJordan/FramePeirceMul.lean`'s `peirceOneSub_eq_span_of_isPrimitive`, and it
consumes this lemma in the `→` direction. -/
theorem isPrimitive_iff_of_idem {c : J} (hc : c * c = c) (hc0 : c ≠ 0) :
    IsPrimitive c ↔ ∀ d : ↥(peirceOneSub hc), d * d = d → d = 0 ∨ d = 1 := by
  constructor
  · rintro ⟨-, -, h⟩ d hd
    rcases h (d : J) (congrArg Subtype.val hd) d.2 with h0 | h1
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h1)
  · intro h
    refine ⟨hc, hc0, fun d hd hcd => ?_⟩
    rcases h ⟨d, hcd⟩ (Subtype.ext hd) with h0 | h1
    · exact Or.inl (congrArg Subtype.val h0)
    · exact Or.inr (congrArg Subtype.val h1)

/-! ## Jordan frames -/

/-- A **Jordan frame**: a complete family of pairwise-orthogonal primitive idempotents.
Carried as data, indexed by `Fin n`, so that its cardinality is available without any
well-definedness theorem — see the module docstring. -/
structure JordanFrame (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] (n : ℕ) where
  /-- The idempotents. -/
  p : Fin n → J
  /-- They are idempotent and pairwise orthogonal. -/
  orthIdem : IsOrthIdemFamily p
  /-- Each is primitive. -/
  primitive : ∀ i, IsPrimitive (p i)
  /-- They sum to the unit. -/
  complete : ∑ i, p i = 1

namespace JordanFrame

variable {n : ℕ} (F : JordanFrame J n)

theorem p_ne_zero (i : Fin n) : F.p i ≠ 0 := (F.primitive i).ne_zero

/-- **A Jordan frame cannot be extended.**  Anything orthogonal to every member of a complete
family is annihilated by the unit, hence zero — so there is no nonzero idempotent to adjoin.
Idempotency of `q` is not used. -/
theorem eq_zero_of_orth {q : J} (hq : ∀ i, F.p i * q = 0) : q = 0 := by
  have h : (1 : J) * q = 0 := by
    rw [← F.complete, Finset.sum_mul, Finset.sum_eq_zero (fun i _ => hq i)]
  rwa [EuclideanJordanAlgebra.one_mul] at h

include F in
/-- A frame of a nontrivial algebra is nonempty. -/
theorem card_pos (h1 : (1 : J) ≠ 0) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exact absurd (by simpa using F.complete.symm) h1
  · exact h

end JordanFrame

/-! ## Linear independence and the dimension bound -/

/-- **Orthogonal nonzero idempotents are linearly independent.**  `EuclideanJordan/Order.lean`'s
`inner_left_coeff`, applied through `EuclideanJordan/Class.lean`'s `jmulₗ`. -/
theorem linearIndependent_of_orthIdem {n : ℕ} {p : Fin n → J} (hp : IsOrthIdemFamily p)
    (hne : ∀ i, p i ≠ 0) : LinearIndependent ℝ p := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have key := inner_left_coeff (m := jmulₗ J) (q := p) (lam := g) jmulₗ_inner_assoc
    (fun i => hp.idem i) (fun i j hij => hp.orth i j hij) (x := 0) hg.symm k
  rw [inner_zero_right] at key
  have hpos : (0 : ℝ) < inner ℝ (p k) (p k) := real_inner_self_pos.mpr (hne k)
  nlinarith [key, hpos]

theorem card_le_finrank_of_orthIdem [FiniteDimensional ℝ J] {n : ℕ} {p : Fin n → J}
    (hp : IsOrthIdemFamily p) (hne : ∀ i, p i ≠ 0) : n ≤ Module.finrank ℝ J := by
  simpa using (linearIndependent_of_orthIdem hp hne).fintype_card_le_finrank

/-! ## Rank -/

/-- The cardinalities realised by orthogonal families of **nonzero** idempotents.  Primitivity
is not required — see the module docstring on what that costs. -/
def orthIdemCards (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : Set ℕ :=
  {n | ∃ p : Fin n → J, IsOrthIdemFamily p ∧ ∀ i, p i ≠ 0}

theorem zero_mem_orthIdemCards : 0 ∈ orthIdemCards J :=
  ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩

theorem bddAbove_orthIdemCards [FiniteDimensional ℝ J] : BddAbove (orthIdemCards J) :=
  ⟨Module.finrank ℝ J, fun _ ⟨_p, hp, hne⟩ => card_le_finrank_of_orthIdem hp hne⟩

/-- The **rank** of a Euclidean Jordan algebra: the greatest cardinality of a family of
pairwise-orthogonal nonzero idempotents. -/
def rank (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] : ℕ := sSup (orthIdemCards J)

theorem le_rank [FiniteDimensional ℝ J] {n : ℕ} (hn : n ∈ orthIdemCards J) : n ≤ rank J :=
  le_csSup bddAbove_orthIdemCards hn

theorem rank_le_finrank [FiniteDimensional ℝ J] : rank J ≤ Module.finrank ℝ J :=
  csSup_le ⟨0, zero_mem_orthIdemCards⟩ (fun _ ⟨_p, hp, hne⟩ => card_le_finrank_of_orthIdem hp hne)

theorem JordanFrame.mem_orthIdemCards {n : ℕ} (F : JordanFrame J n) : n ∈ orthIdemCards J :=
  ⟨F.p, F.orthIdem, F.p_ne_zero⟩

theorem JordanFrame.card_le_rank [FiniteDimensional ℝ J] {n : ℕ} (F : JordanFrame J n) :
    n ≤ rank J := le_rank F.mem_orthIdemCards

theorem JordanFrame.card_le_finrank [FiniteDimensional ℝ J] {n : ℕ} (F : JordanFrame J n) :
    n ≤ Module.finrank ℝ J :=
  card_le_finrank_of_orthIdem F.orthIdem F.p_ne_zero

end EuclideanJordan
