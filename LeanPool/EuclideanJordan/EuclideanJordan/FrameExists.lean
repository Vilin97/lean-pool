/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.Rank



/-!
# Every nontrivial finite-dimensional Euclidean Jordan algebra carries a Jordan frame

`EuclideanJordan/Rank.lean` defines `JordanFrame J n` — a complete family of `n` pairwise-orthogonal
primitive idempotents — and carries it as *data*, because a rank hypothesis supplies one.  This
    file proves such data always exists: `exists_jordanFrame`, by strong
induction on `Module.finrank ℝ J` down the Peirce decomposition of a nontrivial idempotent.

The induction itself is the expected one.  If `1` is primitive the one-element family
`fun _ : Fin 1 => (1 : J)` is a frame.  Otherwise primitivity fails at its third clause, which
    hands over an idempotent `c` with
`c ≠ 0` and `c ≠ 1`; `EuclideanJordan/PeirceSubalgebra.lean` makes `J₂(c)` and `J₀(c)` Euclidean
    Jordan
algebras with units `c` and `1 - c` and drops the dimension at both; and the two frames obtained
from the induction hypothesis concatenate along `Fin.append`.

## ★ The step the build plan missed

The plan priced this module as "mostly `Fin n ⊕ Fin m ≃ Fin (n + m)` re-indexing, not
mathematics".  The re-indexing is indeed routine — it is `exists_frame_of_split` below, five
`Fin.addCases` splits and a `Fin.sum_univ_add`, and it compiled on the first attempt.  The
prediction is wrong about where the content is.  Concatenating the two frames requires each
member to be primitive **in `J`**, and what the induction hypothesis supplies is primitivity
*inside* the subalgebra.  Those differ: the ambient statement quantifies over every idempotent
`y` of `J` with `d ∘ y = y`, the subalgebra statement only over those that additionally lie in
`J₂(c)`.  Closing the gap is exactly

> `J₂(d) ⊆ J₂(c)` for `d` an idempotent of `J₂(c)`,

which is `eigen_one_of_eigen_one` below, and which is in neither
`EuclideanJordan/PeirceSubalgebra.lean` nor `EuclideanJordan/Rank.lean`.

★ **What makes it work is changing which idempotent one decomposes at.**  Attacking it at `c` —
rewriting `c ∘ x` as `c ∘ (d ∘ x)` and trying to move `c` inwards — is circular, because moving
`c` past `d` is what needs the conclusion; `EuclideanJordan/PeirceMul.lean`'s
    `mul_comm_of_eigen_one` only
relocates that difficulty: `mul_comm_of_eigen_one` at `(c, d, x)` yields
`c ∘ x = d ∘ (c ∘ x)`, which puts `c ∘ x` back inside `J₂(d)` rather than identifying it with
`x`.  Decomposing at **`d`** instead makes it immediate: `d` annihilates `c - d`
(`mul_sub_eq_zero_of_eigen_one`, one line), so `c - d` lies in `J₀(d)` while `x` lies in
`J₂(d)`, and `EuclideanJordan/PeirceMul.lean`'s `eigen_one_mul_zero` — the rule that the two
    *extreme*
Peirce components of a single idempotent annihilate each other — kills `(c - d) ∘ x` outright.
Then `c ∘ x = d ∘ x + (c - d) ∘ x = x`.  (`c - d` is also idempotent, but that is neither
proved nor used here.)

★ `eigen_one_of_eigen_one` does **not** need `c` to be idempotent.  The hypothesis was written
into the first draft, the unused-variable linter flagged it, and it was deleted rather than
underscored.  Nothing is claimed about the remaining three: `hd`, `hcd` and `hx` are each used
by the proof, but whether any of them could be dropped was not tested.  `peirceOneSub_le`
restates the lemma as the submodule inequality, and *there* `hc` reappears — not because the
mathematics needs it but because `peirceOneSub` is indexed by an idempotency proof, so the
ambient carrier cannot be named without one.

## Scope


★ The frame produced here carries **no claim about its cardinality**.  `exists_jordanFrame`
existentially quantifies `n`, and `EuclideanJordan/Rank.lean`'s module docstring records why
    `rank J = n`
is not available: `rank J` is a supremum over *all* orthogonal families of nonzero idempotents,
and bounding such a family by a frame's cardinality needs the frame Peirce decomposition or
frame conjugacy.  Nothing here is a step towards it.  Do not read `exists_jordanFrame` as
"`J` has rank `n`".
-/

@[expose] public section

noncomputable section

namespace EuclideanJordan

universe u

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

/-! ## `J₂(d) ⊆ J₂(c)`, the step the induction turns on -/

/-- For an idempotent `d` of `J₂(c)`, the complement `c - d` lies in `J₀(d)`: two rewrites and
`d ∘ d = d`.  Idempotency of `c` is not used. -/
theorem mul_sub_eq_zero_of_eigen_one {c d : J} (hd : d * d = d) (hcd : c * d = d) :
    d * (c - d) = 0 := by
  rw [mul_sub, _root_.mul_comm d c, hcd, hd, sub_self]

/-- ★ **`J₂(d) ⊆ J₂(c)` for `d` an idempotent of `J₂(c)`.**  An element fixed by `d` is fixed by
`c`.

The proof decomposes at `d`, not at `c` — see the module docstring.  `c - d` sits in `J₀(d)` by
`mul_sub_eq_zero_of_eigen_one` and `x` sits in `J₂(d)` by hypothesis, so `eigen_one_mul_zero`
at `d` gives
`x ∘ (c - d) = 0`, and `c ∘ x = d ∘ x + (c - d) ∘ x = x + 0`.

Idempotency of `c` is not required. -/
theorem eigen_one_of_eigen_one {c d x : J} (hd : d * d = d) (hcd : c * d = d)
    (hx : d * x = x) : c * x = x := by
  have h0 : (c - d) * x = 0 := by
    rw [_root_.mul_comm, eigen_one_mul_zero hd hx (mul_sub_eq_zero_of_eigen_one hd hcd)]
  have h : c * x = d * x + (c - d) * x := by rw [← add_mul, add_sub_cancel]
  rw [h, h0, hx, add_zero]

/-- The submodule form of `eigen_one_of_eigen_one`.  `hc` is present only because
`peirceOneSub` is indexed by an idempotency proof. -/
theorem peirceOneSub_le {c d : J} (hc : c * c = c) (hd : d * d = d) (hcd : c * d = d) :
    peirceOneSub hd ≤ peirceOneSub hc :=
  fun _x hx => eigen_one_of_eigen_one hd hcd hx

/-! ## Primitivity transfers out of a Peirce subalgebra

Primitivity inside `J₂(c)` (resp. `J₀(c)`) implies primitivity in `J`.  Apart from the
restatement `peirceOneSub_le`, which nothing downstream consumes, this is where
`eigen_one_of_eigen_one` is used, and it is the reason the induction closes. -/

/-- Primitivity from a weakened third clause: an idempotent `d` fixed by `u` is primitive as
soon as its splitting condition is checked on those idempotents that `u` also fixes, because
`eigen_one_of_eigen_one` supplies that side condition for free. -/
theorem isPrimitive_of_unit {u d : J} (hd : d * d = d) (hd0 : d ≠ 0) (hud : u * d = d)
    (h : ∀ y : J, y * y = y → d * y = y → u * y = y → y = 0 ∨ y = d) : IsPrimitive d :=
  ⟨hd, hd0, fun y hy hdy => h y hy hdy (eigen_one_of_eigen_one hd hud hdy)⟩

/-- A primitive idempotent of `J₂(c)` is primitive in `J`. -/
theorem isPrimitive_coe_of_peirceOne {c : J} (hc : c * c = c) {d : ↥(peirceOneSub hc)}
    (hd : IsPrimitive d) : IsPrimitive (d : J) := by
  refine isPrimitive_of_unit (congrArg Subtype.val hd.idem)
    (fun h => hd.ne_zero (Subtype.ext (h.trans (ZeroMemClass.coe_zero _).symm))) d.2 ?_
  intro y hy hdy hcy
  rcases hd.eq_zero_or_eq (d := ⟨y, hcy⟩) (Subtype.ext hy) (Subtype.ext hdy) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

/-- A primitive idempotent of `J₀(c)` is primitive in `J`.  The unit fed to
`isPrimitive_of_unit` is `1 - c`, and the side condition `(1 - c) ∘ y = y` is membership in
`J₀(c)` read backwards. -/
theorem isPrimitive_coe_of_peirceZero {c : J} (hc : c * c = c) {d : ↥(peirceZeroSub hc)}
    (hd : IsPrimitive d) : IsPrimitive (d : J) := by
  have hd2 : c * (d : J) = 0 := d.2
  have hud : ((1 : J) - c) * (d : J) = (d : J) := by
    rw [sub_mul, EuclideanJordanAlgebra.one_mul, hd2, sub_zero]
  refine isPrimitive_of_unit (congrArg Subtype.val hd.idem)
    (fun h => hd.ne_zero (Subtype.ext (h.trans (ZeroMemClass.coe_zero _).symm))) hud ?_
  intro y hy hdy hcy
  have hmem : y ∈ peirceZeroSub hc := by
    rw [sub_mul, EuclideanJordanAlgebra.one_mul] at hcy
    exact sub_eq_self.mp hcy
  rcases hd.eq_zero_or_eq (d := ⟨y, hmem⟩) (Subtype.ext hy) (Subtype.ext hdy) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

/-! ## Concatenating the two frames -/

/-- **The frames of `J₂(c)` and `J₀(c)` concatenate to a frame of `J`.**  Along `Fin.append`;
the four orthogonality cases are the two blocks' own orthogonality and, across the blocks,
`eigen_one_mul_zero` at `c`.  Completeness adds the two units `c` and `1 - c`. -/
theorem exists_frame_of_split {c : J} (hc : c * c = c) {n₁ n₀ : ℕ}
    (F₁ : JordanFrame ↥(peirceOneSub hc) n₁) (F₀ : JordanFrame ↥(peirceZeroSub hc) n₀) :
    Nonempty (JordanFrame J (n₁ + n₀)) := by
  classical
  set a : Fin n₁ → J := fun i => (F₁.p i : J) with ha
  set b : Fin n₀ → J := fun i => (F₀.p i : J) with hb
  have haidem : ∀ i, a i * a i = a i := fun i => congrArg Subtype.val (F₁.orthIdem.idem i)
  have hbidem : ∀ i, b i * b i = b i := fun i => congrArg Subtype.val (F₀.orthIdem.idem i)
  have haorth : ∀ i j, i ≠ j → a i * a j = 0 := fun i j hij =>
    congrArg Subtype.val (F₁.orthIdem.orth i j hij)
  have hborth : ∀ i j, i ≠ j → b i * b j = 0 := fun i j hij =>
    congrArg Subtype.val (F₀.orthIdem.orth i j hij)
  have hcross : ∀ i j, a i * b j = 0 := fun i j => eigen_one_mul_zero hc (F₁.p i).2 (F₀.p j).2
  refine ⟨{ p := Fin.append a b, orthIdem := ⟨?_, ?_⟩, primitive := ?_, complete := ?_ }⟩
  · refine Fin.addCases ?_ ?_
    · intro i; simp only [Fin.append_left]; exact haidem i
    · intro i; simp only [Fin.append_right]; exact hbidem i
  · refine Fin.addCases ?_ ?_
    · intro i
      refine Fin.addCases ?_ ?_
      · intro j hij
        simp only [Fin.append_left]
        exact haorth i j (fun h => hij (by rw [h]))
      · intro j _
        simp only [Fin.append_left, Fin.append_right]
        exact hcross i j
    · intro i
      refine Fin.addCases ?_ ?_
      · intro j _
        simp only [Fin.append_left, Fin.append_right]
        rw [_root_.mul_comm]; exact hcross j i
      · intro j hij
        simp only [Fin.append_right]
        exact hborth i j (fun h => hij (by rw [h]))
  · refine Fin.addCases ?_ ?_
    · intro i; simp only [Fin.append_left]
      exact isPrimitive_coe_of_peirceOne hc (F₁.primitive i)
    · intro i; simp only [Fin.append_right]
      exact isPrimitive_coe_of_peirceZero hc (F₀.primitive i)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h1 : ∑ i, a i = c := by
      rw [ha, ← AddSubmonoidClass.coe_finsetSum, F₁.complete]
      exact coe_one_peirceOneSub hc
    have h0 : ∑ i, b i = 1 - c := by
      rw [hb, ← AddSubmonoidClass.coe_finsetSum, F₀.complete]
      exact coe_one_peirceZeroSub hc
    rw [h1, h0]; abel

/-! ## The induction -/

/-- The induction carrier: quantified over the *type*, because the recursive calls land on the
two Peirce subalgebras rather than on `J`.  The dimension bound is a `≤`, so the outer
induction is the ordinary one on `ℕ` rather than a well-founded recursion. -/
theorem exists_jordanFrame_of_finrank_le (N : ℕ) : ∀ (J : Type u) [NormedAddCommGroup J]
    [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J],
    Module.finrank ℝ J ≤ N → (1 : J) ≠ 0 → ∃ n, Nonempty (JordanFrame J n) := by
  induction N with
  | zero =>
    intro J _ _ _ _ hle h1
    exact absurd (finrank_zero_iff_forall_zero.mp (Nat.le_zero.mp hle) 1) h1
  | succ N ih =>
    intro J _ _ _ _ hle h1
    by_cases hprim : IsPrimitive (1 : J)
    · have horth : IsOrthIdemFamily (fun _ : Fin 1 => (1 : J)) := by
        refine ⟨fun _ => EuclideanJordanAlgebra.one_mul 1, fun i j hij => ?_⟩
        exact absurd (Subsingleton.elim i j) hij
      exact ⟨1, ⟨⟨fun _ => 1, horth, fun _ => hprim, by simp⟩⟩⟩
    · obtain ⟨c, hcidem, hc0, hc1⟩ : ∃ c : J, c * c = c ∧ c ≠ 0 ∧ c ≠ 1 := by
        by_contra hno
        refine hprim ⟨EuclideanJordanAlgebra.one_mul 1, h1, fun d hd _ => ?_⟩
        by_cases h : d = 0
        · exact Or.inl h
        · by_cases h' : d = 1
          · exact Or.inr h'
          · exact absurd ⟨d, hd, h, h'⟩ hno
      have hlt1 : Module.finrank ℝ ↥(peirceOneSub hcidem) ≤ N :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (finrank_peirceOneSub_lt hcidem hc1) hle)
      have hlt0 : Module.finrank ℝ ↥(peirceZeroSub hcidem) ≤ N :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (finrank_peirceZeroSub_lt hcidem hc0) hle)
      have hu1 : (1 : ↥(peirceOneSub hcidem)) ≠ 0 := fun h => hc0 (by
        have hco := congrArg Subtype.val h
        rwa [coe_one_peirceOneSub, ZeroMemClass.coe_zero] at hco)
      have hu0 : (1 : ↥(peirceZeroSub hcidem)) ≠ 0 := fun h => hc1 (by
        have hco := congrArg Subtype.val h
        rw [coe_one_peirceZeroSub, ZeroMemClass.coe_zero] at hco
        linear_combination (norm := module) -hco)
      obtain ⟨n₁, ⟨F₁⟩⟩ := ih _ hlt1 hu1
      obtain ⟨n₀, ⟨F₀⟩⟩ := ih _ hlt0 hu0
      exact ⟨n₁ + n₀, exists_frame_of_split hcidem F₁ F₀⟩

/-- **M3.**  Every finite-dimensional Euclidean Jordan algebra with `1 ≠ 0` carries a Jordan
frame.  The cardinality is existentially quantified and is *not* claimed to be the rank — see
the module docstring. -/
theorem exists_jordanFrame (J : Type u) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] (h1 : (1 : J) ≠ 0) :
    ∃ n, Nonempty (JordanFrame J n) :=
  exists_jordanFrame_of_finrank_le (Module.finrank ℝ J) J le_rfl h1

/-- `1 ≠ 0` is exactly nontriviality: if `1 = 0` then `x = 1 ∘ x = 0` for every `x`. -/
theorem one_ne_zero_of_nontrivial [Nontrivial J] : (1 : J) ≠ 0 := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne J
  refine hxy ?_
  have hz : ∀ z : J, z = 0 := fun z => by
    rw [← EuclideanJordanAlgebra.one_mul z, h, EuclideanJordanAlgebra.zero_mul']
  rw [hz x, hz y]

/-- **M3, stated over `Nontrivial`.** -/
theorem exists_jordanFrame' (J : Type u) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [EuclideanJordanAlgebra J] [FiniteDimensional ℝ J] [Nontrivial J] :
    ∃ n, Nonempty (JordanFrame J n) :=
  exists_jordanFrame J one_ne_zero_of_nontrivial

end EuclideanJordan
