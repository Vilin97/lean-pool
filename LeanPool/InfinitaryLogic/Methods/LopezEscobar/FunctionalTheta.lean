/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.WitnessLang
import LeanPool.InfinitaryLogic.Descriptive.QueryCode
import LeanPool.InfinitaryLogic.Lomega1omega.FiniteQuantification
/-!
# The functional Θ: syntax and semantics (issue #10, Unit 2a)

Marker's Lemma-4.23 sentence over the two-sorted mid-language `MidLang L = L.sum WitnessLang`
(one witness copy; Unit 2b maps it into the tagged `KLang` per side), with the audit's
Unit-2 revision: a **default-coordinate clause** absent from Marker's bijective-pairing
presentation.  Without it the `f`-sequence could carry arbitrary bits at coordinates
outside `range queryEmbedding` while Unit 0's `queryCode` fixes those coordinates to
`false`, and a path through `T` would not correspond to the base reduct's query code.

The six clauses:

1. `omegaAxioms` — `(c, s)` enumerate the carrier as `(ℕ, 0, succ)`: `s` injective, `c` not
   a successor, and every element is a numeral (countable disjunction);
2. `bitAxiom` — every `f(x)` equals `c` or `s(c)`;
3. `codeAxiom` — for every query `q`, `R(numerals of q) ↔ f(numeral (queryEmbedding q)) = s(c)`;
4. `defaultAxiom` — `f(numeral n) = c` for every `n ∉ range queryEmbedding`;
5. `treeDiagram T` — every `tree n` pinned at all numeral tuples according to `T n`
   (classically: atom if the node is in `T`, its negation otherwise), including `n = 0`;
6. `pathAxiom` — every prefix formed from `f` and `g` satisfies `tree n`, including `tree 0`.

Exports: per-clause realization lemmas; `numMap_bijective` (clause 1 gives a bijective
numeral map); `fBit_eq_queryCode` (clauses 1–4 identify the `f`-bit sequence **exactly**
with `queryCode` of the base-reduct code `pulledCode`); the tree pinning as an **iff**
(`realize_treeDiagram`); and the bundled `functionalTheta T`.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

/-- The two-sorted mid-language: the base plus one witness copy. -/
abbrev MidLang (L : Language.{0, 0}) : Language.{0, 0} := L.sum WitnessLang

variable {L : Language.{0, 0}}

/-! ## Terms -/

variable (L) in
/-- Numeral terms in the mid-language: `c`, `s c`, `s (s c)`, …. -/
def mNum (α : Type) : ℕ → (MidLang L).Term α
  | 0 => Term.func (Sum.inr WitnessFun.c) Fin.elim0
  | n + 1 => Term.func (Sum.inr WitnessFun.s) ![mNum α n]

variable (L) in
/-- `f` applied to a term. -/
def mF {α : Type} (t : (MidLang L).Term α) : (MidLang L).Term α :=
  Term.func (Sum.inr WitnessFun.f) ![t]

variable (L) in
/-- `g` applied to a term. -/
def mG {α : Type} (t : (MidLang L).Term α) : (MidLang L).Term α :=
  Term.func (Sum.inr WitnessFun.g) ![t]

/-! ## Semantic shorthands (the language argument is explicit throughout — it is not
inferable from the carrier) -/

section Maps

variable (L) (M : Type) [inst : (MidLang L).Structure M]

/-- The interpreted successor. -/
def sMap (x : M) : M := @Structure.funMap (MidLang L) M inst 1 (Sum.inr WitnessFun.s) ![x]

/-- The interpreted `f`. -/
def fMap (x : M) : M := @Structure.funMap (MidLang L) M inst 1 (Sum.inr WitnessFun.f) ![x]

/-- The interpreted `g`. -/
def gMap (x : M) : M := @Structure.funMap (MidLang L) M inst 1 (Sum.inr WitnessFun.g) ![x]

/-- The numeral map `ℕ → M`. -/
def numMap : ℕ → M
  | 0 => @Structure.funMap (MidLang L) M inst 0 (Sum.inr WitnessFun.c) Fin.elim0
  | n + 1 => sMap L M (numMap n)

end Maps

section Semantics

variable {M : Type} [inst : (MidLang L).Structure M]

/-- One-argument application terms realize through `![·]`. -/
private theorem realize_app1 {α : Type} (f : (MidLang L).Functions 1)
    (t : (MidLang L).Term α) (v : α → M) :
    (Term.func f ![t]).realize v = Structure.funMap f ![t.realize v] := by
  show Structure.funMap f _ = _
  congr 1
  funext i
  rw [Fin.eq_zero i]
  simp only [Matrix.cons_val_zero]

/-- Successor applications realize to `sMap`.

Stated with the symbol `Sum.inr WitnessFun.s` baked in rather than via the generic
`realize_app1`: the goal's copy of that symbol carries the type `L.Functions 1 ⊕
WitnessLang.Functions 1`, which `rw`/`simp` cannot assign to `realize_app1`'s
`?f : (MidLang L).Functions 1` at `implicit` transparency. Spelling it the same way here makes
the match syntactic. -/
private theorem realize_s_app {α : Type} (t : (MidLang L).Term α) (v : α → M) :
    (Term.func (Sum.inr WitnessFun.s) ![t]).realize v = sMap L M (t.realize v) :=
  realize_app1 _ t v

/-- Numeral terms realize to the numeral map, under any assignment. -/
@[simp] theorem realize_mNum {α : Type} (v : α → M) (n : ℕ) :
    (mNum L α n).realize v = numMap L M n := by
  induction n with
  | zero =>
    show Structure.funMap _ _ = _
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    exact (realize_app1 _ _ _).trans (congrArg (fun x => sMap L M x) ih)

@[simp] theorem realize_mF {α : Type} (t : (MidLang L).Term α) (v : α → M) :
    (mF L t).realize v = fMap L M (t.realize v) :=
  realize_app1 _ t v

@[simp] theorem realize_mG {α : Type} (t : (MidLang L).Term α) (v : α → M) :
    (mG L t).realize v = gMap L M (t.realize v) :=
  realize_app1 _ t v

private theorem realize_var_block {k : ℕ} (ws : Fin k → M) (j : Fin k) :
    Term.realize (Sum.elim (Empty.elim : Empty → M) (Fin.append Fin.elim0 ws))
      (Term.var (Sum.inr (Fin.natAdd 0 j)) : (MidLang L).Term (Empty ⊕ Fin (0 + k))) =
      ws j := by
  show Fin.append Fin.elim0 ws (Fin.natAdd 0 j) = ws j
  exact Fin.append_right _ _ j

end Semantics

/-! ## Clause 1: the ω-axioms -/

variable (L) in
/-- **Clause 1** (`omegaAxioms`): `s` is injective, `c` is not a successor, and every
element is a numeral.  Together: the numeral map is a bijection `ℕ ≃ carrier`. -/
noncomputable def omegaAxioms : (MidLang L).Sentenceω :=
  (BoundedFormulaω.forallBlock (k := 2)
    ((BoundedFormulaω.equal
        (Term.func (Sum.inr WitnessFun.s) ![Term.var (Sum.inr (Fin.natAdd 0 0))])
        (Term.func (Sum.inr WitnessFun.s) ![Term.var (Sum.inr (Fin.natAdd 0 1))])).imp
      (BoundedFormulaω.equal (Term.var (Sum.inr (Fin.natAdd 0 0)))
        (Term.var (Sum.inr (Fin.natAdd 0 1)))))).and
  ((BoundedFormulaω.forallBlock (k := 1)
    ((BoundedFormulaω.equal
        (Term.func (Sum.inr WitnessFun.s) ![Term.var (Sum.inr (Fin.natAdd 0 0))])
        (mNum L _ 0)).not)).and
  (BoundedFormulaω.forallBlock (k := 1)
    (BoundedFormulaω.iSup fun i =>
      BoundedFormulaω.equal (mNum L _ i) (Term.var (Sum.inr (Fin.natAdd 0 0))))))

section Semantics

variable {M : Type} [inst : (MidLang L).Structure M]

/-- Clause-1 realization: injectivity, non-successorhood of `c`, numeral surjectivity. -/
theorem realize_omegaAxioms :
    Sentenceω.Realize (omegaAxioms L) M ↔
      (Function.Injective (sMap L M) ∧
        (∀ x : M, sMap L M x ≠ numMap L M 0) ∧
        Function.Surjective (numMap L M)) := by
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [omegaAxioms, BoundedFormulaω.realize_and, BoundedFormulaω.realize_and,
    BoundedFormulaω.realize_forallBlock, BoundedFormulaω.realize_forallBlock,
    BoundedFormulaω.realize_forallBlock]
  constructor
  · rintro ⟨hinj, hne, hsurj⟩
    refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x => ?_⟩
    · have h := hinj ![x, y]
      rw [BoundedFormulaω.realize_imp, BoundedFormulaω.realize_equal,
        BoundedFormulaω.realize_equal] at h
      simp only [realize_s_app, 
        ] at h
      exact h hxy
    · have h := hne ![x]
      rw [BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal] at h
      simp only [realize_s_app, realize_mNum] at h
      exact h hx
    · have h := hsurj ![x]
      rw [BoundedFormulaω.realize_iSup] at h
      obtain ⟨i, hi⟩ := h
      rw [BoundedFormulaω.realize_equal] at hi
      simp only [realize_mNum] at hi
      exact ⟨i, hi⟩
  · rintro ⟨hinj, hne, hsurj⟩
    refine ⟨fun ws => ?_, fun ws => ?_, fun ws => ?_⟩
    · rw [BoundedFormulaω.realize_imp, BoundedFormulaω.realize_equal,
        BoundedFormulaω.realize_equal]
      simp only [realize_s_app]
      exact fun h => hinj h
    · rw [BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal]
      simp only [realize_s_app, realize_mNum]
      exact hne (ws 0)
    · rw [BoundedFormulaω.realize_iSup]
      obtain ⟨i, hi⟩ := hsurj (ws 0)
      refine ⟨i, ?_⟩
      rw [BoundedFormulaω.realize_equal]
      simp only [realize_mNum]
      exact hi

/-- **Clause 1 export**: the numeral map of a model of `omegaAxioms` is bijective. -/
theorem numMap_bijective (h : Sentenceω.Realize (omegaAxioms L) M) :
    Function.Bijective (numMap L M) := by
  rw [realize_omegaAxioms] at h
  obtain ⟨hinj, hne, hsurj⟩ := h
  refine ⟨?_, hsurj⟩
  have key : ∀ i j : ℕ, numMap L M i = numMap L M j → i = j := by
    intro i
    induction i with
    | zero =>
      intro j hj
      cases j with
      | zero => rfl
      | succ j => exact absurd hj.symm (hne _)
    | succ i ih =>
      intro j hj
      cases j with
      | zero => exact absurd hj (hne _)
      | succ j => exact congrArg Nat.succ (ih j (hinj hj))
  exact fun i j => key i j

end Semantics

/-! ## Clause 2: the bit axiom -/

variable (L) in
/-- **Clause 2** (`bitAxiom`): every `f`-value is `c` or `s(c)`. -/
noncomputable def bitAxiom : (MidLang L).Sentenceω :=
  BoundedFormulaω.forallBlock (k := 1)
    ((BoundedFormulaω.equal (mF L (Term.var (Sum.inr (Fin.natAdd 0 0)))) (mNum L _ 0)) ⊔
      (BoundedFormulaω.equal (mF L (Term.var (Sum.inr (Fin.natAdd 0 0)))) (mNum L _ 1)))

theorem realize_bitAxiom {M : Type} [inst : (MidLang L).Structure M] :
    Sentenceω.Realize (bitAxiom L) M ↔
      ∀ x : M, fMap L M x = numMap L M 0 ∨ fMap L M x = numMap L M 1 := by
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [bitAxiom, BoundedFormulaω.realize_forallBlock]
  -- the sentence semantics supplies the empty tuple as `default` rather than `Fin.elim0`; the two
  -- are definitionally equal, so `realize_var_block` still proves the evaluation, but only after
  -- the equality is stated in the shape the goal actually has
  have hvar : ∀ ws : Fin 1 → M,
      Term.realize (Sum.elim (Empty.elim : Empty → M) (Fin.append default ws))
        (Term.var (Sum.inr (Fin.natAdd 0 0)) : (MidLang L).Term (Empty ⊕ Fin (0 + 1))) = ws 0 :=
    fun ws => realize_var_block ws 0
  constructor
  · intro h x
    have hx := h ![x]
    rw [BoundedFormulaω.realize_sup, BoundedFormulaω.realize_equal,
      BoundedFormulaω.realize_equal] at hx
    simpa only [realize_mF, hvar, realize_mNum, Matrix.cons_val_zero] using hx
  · intro h ws
    rw [BoundedFormulaω.realize_sup, BoundedFormulaω.realize_equal,
      BoundedFormulaω.realize_equal]
    simpa only [realize_mF, hvar, realize_mNum] using h (ws 0)

/-! ## Clauses 3 and 4: code and default -/

variable (L) in
/-- **Clause 3** (`codeAxiom`): for every query `q = (R, v)`,
`R(numerals of v) ↔ f(numeral (queryEmbedding q)) = s(c)`. -/
noncomputable def codeAxiom [Countable (Σ l, L.Relations l)] : (MidLang L).Sentenceω :=
  letI : Encodable (RelQuery L) := queryEncodable
  BoundedFormulaω.einf fun q : RelQuery L =>
    (BoundedFormulaω.rel (Sum.inl q.1.2 : (MidLang L).Relations q.1.1)
        (fun i => mNum L _ (q.2 i))).iff
      (BoundedFormulaω.equal (mF L (mNum L _ (queryEmbedding (L := L) q))) (mNum L _ 1))

theorem realize_codeAxiom [Countable (Σ l, L.Relations l)]
    {M : Type} [inst : (MidLang L).Structure M] :
    Sentenceω.Realize (codeAxiom L) M ↔
      ∀ q : RelQuery L,
        (@Structure.RelMap (MidLang L) M inst q.1.1 (Sum.inl q.1.2)
            (fun i => numMap L M (q.2 i)) ↔
          fMap L M (numMap L M (queryEmbedding (L := L) q)) = numMap L M 1) := by
  let : Encodable (RelQuery L) := queryEncodable
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [codeAxiom, BoundedFormulaω.realize_einf]
  refine forall_congr' fun q => ?_
  rw [BoundedFormulaω.realize_iff]
  refine iff_congr (Iff.of_eq (congrArg
    (@Structure.RelMap (MidLang L) M inst q.1.1 (Sum.inl q.1.2)) ?_)) ?_
  · funext i
    exact realize_mNum _ _
  · rw [BoundedFormulaω.realize_equal]
    simp only [realize_mNum, realize_mF]

variable (L) in
/-- **Clause 4** (`defaultAxiom`, the audit's Unit-2 addition): `f(numeral n) = c` at every
coordinate outside the query embedding's range — matching Unit 0's `queryCode` default. -/
noncomputable def defaultAxiom [Countable (Σ l, L.Relations l)] : (MidLang L).Sentenceω :=
  letI : Encodable {n : ℕ // n ∉ Set.range (queryEmbedding (L := L))} :=
    Encodable.ofCountable _
  BoundedFormulaω.einf fun p : {n : ℕ // n ∉ Set.range (queryEmbedding (L := L))} =>
    BoundedFormulaω.equal (mF L (mNum L _ p.1)) (mNum L _ 0)

theorem realize_defaultAxiom [Countable (Σ l, L.Relations l)]
    {M : Type} [inst : (MidLang L).Structure M] :
    Sentenceω.Realize (defaultAxiom L) M ↔
      ∀ n ∉ Set.range (queryEmbedding (L := L)),
        fMap L M (numMap L M n) = numMap L M 0 := by
  let : Encodable {n : ℕ // n ∉ Set.range (queryEmbedding (L := L))} :=
    Encodable.ofCountable _
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [defaultAxiom, BoundedFormulaω.realize_einf]
  constructor
  · intro h n hn
    have hp := h ⟨n, hn⟩
    rw [BoundedFormulaω.realize_equal] at hp
    simpa only [realize_mF, realize_mNum] using hp
  · intro h p
    rw [BoundedFormulaω.realize_equal]
    simpa only [realize_mF, realize_mNum] using h p.1 p.2

/-! ## Clause 5: the tree diagram -/

variable (L) in
/-- The tree atom at level `n`: `tree n` applied to the bit-numerals of `σ` followed by the
numerals of `τ`. -/
private def treeAtom (n : ℕ) (σ : Fin n → Bool) (τ : Fin n → ℕ) : (MidLang L).Sentenceω :=
  BoundedFormulaω.rel (Sum.inr (WitnessRel.tree n) : (MidLang L).Relations (2 * n))
    (fun i : Fin (2 * n) =>
      if h : (i : ℕ) < n then mNum L _ (cond (σ ⟨i, h⟩) 1 0)
      else mNum L _ (τ ⟨(i : ℕ) - n, by omega⟩))

variable (L) in
/-- The semantic tuple of a tree atom. -/
def treeTuple (M : Type) [inst : (MidLang L).Structure M] (n : ℕ)
    (σ : Fin n → Bool) (τ : Fin n → ℕ) : Fin (2 * n) → M :=
  fun i =>
    if h : (i : ℕ) < n then numMap L M (cond (σ ⟨i, h⟩) 1 0)
    else numMap L M (τ ⟨(i : ℕ) - n, by omega⟩)

private theorem realize_treeAtom {M : Type} [inst : (MidLang L).Structure M] (n : ℕ)
    (σ : Fin n → Bool) (τ : Fin n → ℕ) :
    Sentenceω.Realize (treeAtom L n σ τ) M ↔
      @Structure.RelMap (MidLang L) M inst (2 * n) (Sum.inr (WitnessRel.tree n))
        (treeTuple L M n σ τ) := by
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [treeAtom]
  refine Iff.of_eq (congrArg
    (@Structure.RelMap (MidLang L) M inst (2 * n) (Sum.inr (WitnessRel.tree n))) ?_)
  funext i
  by_cases h : (i : ℕ) < n
  · simp only [treeTuple, dite_eq_left h, realize_mNum]
  · simp only [treeTuple, dite_eq_right h, realize_mNum]

variable (L) in
open Classical in
/-- **Clause 5** (`treeDiagram`): every `tree n` pinned at all numeral tuples according to
`T n` — the atom when the node is in `T n`, its negation otherwise — including `n = 0`. -/
noncomputable def treeDiagram (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    (MidLang L).Sentenceω :=
  letI : Encodable (Σ n, (Fin n → Bool) × (Fin n → ℕ)) := Encodable.ofCountable _
  BoundedFormulaω.einf fun p : Σ n, (Fin n → Bool) × (Fin n → ℕ) =>
    if (p.2.1, p.2.2) ∈ T p.1 then treeAtom L p.1 p.2.1 p.2.2
    else (treeAtom L p.1 p.2.1 p.2.2).not

/-- Clause-5 realization — **an iff, not merely preservation**: the interpreted `tree n`
holds at a numeral tuple exactly when the node is in `T n`. -/
theorem realize_treeDiagram {M : Type} [inst : (MidLang L).Structure M]
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    Sentenceω.Realize (treeDiagram L T) M ↔
      ∀ (n : ℕ) (σ : Fin n → Bool) (τ : Fin n → ℕ),
        (@Structure.RelMap (MidLang L) M inst (2 * n) (Sum.inr (WitnessRel.tree n))
            (treeTuple L M n σ τ) ↔ (σ, τ) ∈ T n) := by
  classical
  let : Encodable (Σ n, (Fin n → Bool) × (Fin n → ℕ)) := Encodable.ofCountable _
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [treeDiagram, BoundedFormulaω.realize_einf]
  constructor
  · intro h n σ τ
    have hp := h ⟨n, σ, τ⟩
    by_cases hmem : (σ, τ) ∈ T n
    · rw [ite_eq_left hmem] at hp
      exact ⟨fun _ => hmem, fun _ => (realize_treeAtom (L := L) n σ τ).mp hp⟩
    · rw [ite_eq_right hmem, BoundedFormulaω.realize_not] at hp
      exact ⟨fun hR => absurd ((realize_treeAtom (L := L) n σ τ).mpr hR) hp,
        fun hmem' => absurd hmem' hmem⟩
  · intro h p
    by_cases hmem : (p.2.1, p.2.2) ∈ T p.1
    · rw [ite_eq_left hmem]
      exact (realize_treeAtom (L := L) p.1 p.2.1 p.2.2).mpr ((h p.1 p.2.1 p.2.2).mpr hmem)
    · rw [ite_eq_right hmem, BoundedFormulaω.realize_not]
      exact fun hreal =>
        hmem ((h p.1 p.2.1 p.2.2).mp ((realize_treeAtom (L := L) p.1 p.2.1 p.2.2).mp hreal))

/-! ## Clause 6: the path axiom -/

variable (L) in
/-- **Clause 6** (`pathAxiom`): for every `n` — including `0` — the length-`n` prefixes of
`f` and `g` along the numerals satisfy `tree n`. -/
def pathAxiom : (MidLang L).Sentenceω :=
  BoundedFormulaω.iInf fun n =>
    BoundedFormulaω.rel (Sum.inr (WitnessRel.tree n) : (MidLang L).Relations (2 * n))
      (fun i : Fin (2 * n) =>
        if (i : ℕ) < n then mF L (mNum L _ (i : ℕ))
        else mG L (mNum L _ ((i : ℕ) - n)))

variable (L) in
/-- The semantic path tuple at level `n`. -/
def pathTuple (M : Type) [inst : (MidLang L).Structure M] (n : ℕ) : Fin (2 * n) → M :=
  fun i =>
    if (i : ℕ) < n then fMap L M (numMap L M (i : ℕ))
    else gMap L M (numMap L M ((i : ℕ) - n))

theorem realize_pathAxiom {M : Type} [inst : (MidLang L).Structure M] :
    Sentenceω.Realize (pathAxiom L) M ↔
      ∀ n : ℕ, @Structure.RelMap (MidLang L) M inst (2 * n) (Sum.inr (WitnessRel.tree n))
        (pathTuple L M n) := by
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [pathAxiom, BoundedFormulaω.realize_iInf]
  refine forall_congr' fun n => ?_
  refine Iff.of_eq (congrArg
    (@Structure.RelMap (MidLang L) M inst (2 * n) (Sum.inr (WitnessRel.tree n))) ?_)
  funext i
  by_cases h : (i : ℕ) < n
  · simp only [pathTuple, ite_eq_left h, realize_mF, realize_mNum]
  · simp only [pathTuple, ite_eq_right h, realize_mG, realize_mNum]

/-! ## The pulled-back code and the bit-sequence identification -/

variable (L) in
open Classical in
/-- The base-reduct code of a mid-language structure, pulled back along the numeral map:
the query `q` holds iff the base relation holds at the corresponding numerals. -/
noncomputable def pulledCode (M : Type) [inst : (MidLang L).Structure M] :
    StructureSpace L :=
  fun q =>
    if @Structure.RelMap (MidLang L) M inst q.1.1 (Sum.inl q.1.2)
        (fun i => numMap L M (q.2 i)) then true else false

theorem pulledCode_eq_true (M : Type) [inst : (MidLang L).Structure M] (q : RelQuery L) :
    pulledCode L M q = true ↔
      @Structure.RelMap (MidLang L) M inst q.1.1 (Sum.inl q.1.2)
        (fun i => numMap L M (q.2 i)) := by
  classical
  simp only [pulledCode]
  by_cases h : @Structure.RelMap (MidLang L) M inst q.1.1 (Sum.inl q.1.2)
      (fun i => numMap L M (q.2 i)) <;> simp [h]

/-- **The bit-sequence identification** (clauses 1, 3, 4): the `f`-bit at numeral `n` is
`1` exactly when `queryCode` of the pulled-back base code is `true` at `n`. -/
theorem fBit_eq_queryCode [Countable (Σ l, L.Relations l)]
    {M : Type} [inst : (MidLang L).Structure M]
    (homega : Sentenceω.Realize (omegaAxioms L) M)
    (hcode : Sentenceω.Realize (codeAxiom L) M)
    (hdefault : Sentenceω.Realize (defaultAxiom L) M) (n : ℕ) :
    fMap L M (numMap L M n) = numMap L M 1 ↔
      queryCode (pulledCode L M) n = true := by
  classical
  by_cases hn : ∃ q, queryEmbedding (L := L) q = n
  · obtain ⟨q, rfl⟩ := hn
    rw [queryCode_embedding]
    have hq := (realize_codeAxiom.mp hcode) q
    rw [← hq]
    simp only [pulledCode]
    by_cases hR : @Structure.RelMap (MidLang L) M inst q.1.1 (Sum.inl q.1.2)
        (fun i => numMap L M (q.2 i))
    · simp [hR]
    · simp [hR]
  · have hout : n ∉ Set.range (queryEmbedding (L := L)) := hn
    rw [queryCode_of_notMem_range _ hout]
    rw [(realize_defaultAxiom.mp hdefault) n hout]
    have hinj := (numMap_bijective homega).1
    simp only [Bool.false_eq_true, iff_false]
    intro h01
    exact absurd (hinj h01) (by omega)

/-! ## The bundle -/

variable (L) in
/-- **The functional Θ** over the mid-language: all six clauses. -/
noncomputable def functionalTheta [Countable (Σ l, L.Relations l)]
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) : (MidLang L).Sentenceω :=
  (omegaAxioms L).and ((bitAxiom L).and ((codeAxiom L).and ((defaultAxiom L).and
    ((treeDiagram L T).and (pathAxiom L)))))

/-- Realization of the bundle: all six clause-level semantics. -/
theorem realize_functionalTheta [Countable (Σ l, L.Relations l)]
    {M : Type} [inst : (MidLang L).Structure M]
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    Sentenceω.Realize (functionalTheta L T) M ↔
      (Sentenceω.Realize (omegaAxioms L) M ∧ Sentenceω.Realize (bitAxiom L) M ∧
        Sentenceω.Realize (codeAxiom L) M ∧ Sentenceω.Realize (defaultAxiom L) M ∧
        Sentenceω.Realize (treeDiagram L T) M ∧ Sentenceω.Realize (pathAxiom L) M) := by
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [functionalTheta]
  simp only [BoundedFormulaω.realize_and]
  rfl

end FirstOrder.Language
