/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.CountableIndex
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# The beth-ladder syntax (Marker, Exercise 5.3)

The common sentence of the bounded-spectrum ladder: for an ordinal `α`, the language
`ladderLang α` has constants `cₙ` (`n : ℕ`), unary level predicates `U_i` indexed by
`Index α := (α + 2).ToType` (the canonical `Type 0` well order of the levels `β ≤ α + 1`), and
one binary relation `E`. The sentence `ladderSentence α` asserts, per the audit
(`docs/hanf-ladder-audit.md`):

* base: `U_⊥ x ↔ ⋁ₙ x = cₙ`;
* top: every element is in `U_⊤`;
* nesting: `U_i ⊆ U_j` for `i < j`;
* limit covering: at an order-limit level `j`, `U_j x → ⋁_{i<j} U_i x`;
* predecessor descent: for adjacent levels `i ⋖ j`, `U_j x → E y x → U_i y`;
* extensionality: equal `E`-predecessor sets imply equality.

All clause indexing is INTERNAL to the order on `Index α` (`<`, `⋖`, `Order.IsSuccLimit`,
`⊥`/`⊤` from the order instances); `typein`/`enum` translation is deferred to the semantic
files. Only formation of the countably-indexed sentence needs `[Countable (Index α)]`
(supplied by `α < ω₁` downstream); the language itself is `Language.{0,0}` for every `α`.

The acceptance interface is the semantic packaging `realize_ladderSentence_iff`: realization is
equivalent to the six named clause predicates bundled in `IsLadderModel` — downstream files
(the `α = 0` powerset model, the general upper-bound induction) work with those predicates and
never unfold binders, `ciInf`/`ciSup`, or valuation bookkeeping again.
-/

namespace FirstOrder

namespace Language

namespace HanfLadder

open Ordinal

/-- The level-index order: the canonical `Type 0` well order of type `α + 2` — the levels
`β ≤ α + 1`. Carries `LinearOrder`, `WellFoundedLT`, and (noncomputably) `SuccOrder`
instances. -/
abbrev Index (α : Ordinal.{0}) : Type := (α + 2).ToType

instance (α : Ordinal.{0}) : Nonempty (Index α) :=
  Ordinal.nonempty_toType_iff.mpr fun h => by
    have h2 := (Ordinal.add_eq_zero_iff.mp h).2
    rw [show (2 : Ordinal) = 1 + 1 from one_add_one_eq_two.symm,
      Ordinal.add_eq_zero_iff] at h2
    exact one_ne_zero h2.1

noncomputable instance (α : Ordinal.{0}) : OrderBot (Index α) :=
  WellFoundedLT.toOrderBot (Index α)

noncomputable instance (α : Ordinal.{0}) : OrderTop (Index α) where
  top := ToType.mk ⟨α + 1, by
    rw [Set.mem_Iio, (show (α + 2 : Ordinal) = Order.succ (α + 1) by
      rw [Order.succ_eq_add_one, add_assoc, one_add_one_eq_two])]
    exact Order.lt_succ _⟩
  le_top x := by
    rw [← ToType.mk.symm.le_iff_le, OrderIso.symm_apply_apply]
    change ((ToType.mk.symm x : Set.Iio (α + 2)) : Ordinal) ≤ α + 1
    have hx : ((ToType.mk.symm x : Set.Iio (α + 2)) : Ordinal) < α + 2 :=
      (ToType.mk.symm x).2
    have heq : (α + 2 : Ordinal) = Order.succ (α + 1) := by
      rw [Order.succ_eq_add_one, add_assoc, one_add_one_eq_two]
    exact Order.lt_succ_iff.mp (lt_of_lt_of_eq hx heq)

/-- The ladder language: `ℕ` constants, `Index α`-indexed unary level predicates, one binary
relation. `Language.{0,0}` for every `α`. -/
def ladderLang (α : Ordinal.{0}) : Language.{0, 0} :=
  ⟨fun n => match n with
    | 0 => ℕ
    | _ => Empty,
   fun n => match n with
    | 1 => Index α
    | 2 => Unit
    | _ => Empty⟩

variable {α : Ordinal.{0}}

/-- The `n`-th constant, as a term over any variable type. -/
private def const (n : ℕ) {γ : Type} : (ladderLang α).Term γ :=
  Term.func (show (ladderLang α).Functions 0 from n) Fin.elim0

/-- The level atom `U_i t`. -/
private def levelAtom (i : Index α) {γ : Type} {n : ℕ} (t : (ladderLang α).Term (γ ⊕ Fin n)) :
    (ladderLang α).BoundedFormulaω γ n :=
  BoundedFormulaω.rel (show (ladderLang α).Relations 1 from i) (fun _ => t)

/-- The edge atom `E t u`. -/
private def eAtom {γ : Type} {n : ℕ} (t u : (ladderLang α).Term (γ ⊕ Fin n)) :
    (ladderLang α).BoundedFormulaω γ n :=
  BoundedFormulaω.rel (show (ladderLang α).Relations 2 from ()) ![t, u]

/-- Variable `i` at arity `n`, over `Empty` free variables. -/
private abbrev bvar {n : ℕ} (i : Fin n) : (ladderLang α).Term (Empty ⊕ Fin n) :=
  Term.var (Sum.inr i)

section Clauses

variable (α)
variable [Countable (Index α)]

/-- Base, `⊇`: every constant is in the bottom level. -/
private noncomputable def baseInC : (ladderLang α).Sentenceω :=
  BoundedFormulaω.iInf fun n => levelAtom ⊥ (const n)

/-- Base, `⊆`: every bottom-level element is a constant. -/
private noncomputable def baseOutC : (ladderLang α).Sentenceω :=
  BoundedFormulaω.all ((levelAtom ⊥ (bvar 0)).imp
    (BoundedFormulaω.iSup fun n => BoundedFormulaω.equal (bvar 0) (const n)))

/-- Top: every element is in the top level. -/
private noncomputable def topC : (ladderLang α).Sentenceω :=
  BoundedFormulaω.all (levelAtom ⊤ (bvar 0))

/-- Nesting: `U_i ⊆ U_j` for `i < j`. -/
private noncomputable def nestedC : (ladderLang α).Sentenceω :=
  BoundedFormulaω.ciInf fun p : {p : Index α × Index α // p.1 < p.2} =>
    BoundedFormulaω.all ((levelAtom p.1.1 (bvar 0)).imp (levelAtom p.1.2 (bvar 0)))

/-- Limit covering: at an order-limit level `j`, `U_j x → ⋁_{i<j} U_i x`. -/
private noncomputable def limitC : (ladderLang α).Sentenceω :=
  BoundedFormulaω.ciInf fun j : {j : Index α // Order.IsSuccLimit j} =>
    BoundedFormulaω.all ((levelAtom j.1 (bvar 0)).imp
      (BoundedFormulaω.ciSup fun i : {i : Index α // i < j.1} => levelAtom i.1 (bvar 0)))

/-- Predecessor descent: for adjacent `i ⋖ j`, `U_j x → E y x → U_i y`
(`x` = bound variable `0`, `y` = bound variable `1`). -/
private noncomputable def predC : (ladderLang α).Sentenceω :=
  BoundedFormulaω.ciInf fun p : {p : Index α × Index α // p.1 ⋖ p.2} =>
    BoundedFormulaω.all (BoundedFormulaω.all
      ((levelAtom p.1.2 (bvar 0)).imp
        ((eAtom (bvar 1) (bvar 0)).imp (levelAtom p.1.1 (bvar 1)))))

/-- Extensionality, curried: `(∀x, E x y → E x z) → (∀x, E x z → E x y) → y = z`
(`y` = bound variable `0`, `z` = bound variable `1`, `x` = bound variable `2`). -/
private def extC : (ladderLang α).Sentenceω :=
  BoundedFormulaω.all (BoundedFormulaω.all
    ((BoundedFormulaω.all ((eAtom (bvar 2) (bvar 0)).imp (eAtom (bvar 2) (bvar 1)))).imp
      ((BoundedFormulaω.all ((eAtom (bvar 2) (bvar 1)).imp (eAtom (bvar 2) (bvar 0)))).imp
        (BoundedFormulaω.equal (bvar 0) (bvar 1)))))

/-- **The ladder sentence** (Marker, Exercise 5.3). -/
noncomputable def ladderSentence : (ladderLang α).Sentenceω :=
  BoundedFormulaω.iInf fun k =>
    match k with
    | 0 => baseInC α
    | 1 => baseOutC α
    | 2 => topC α
    | 3 => nestedC α
    | 4 => limitC α
    | 5 => predC α
    | _ => extC α

end Clauses

/-! ## The semantic packaging -/

section Semantics

variable (α) {M : Type} [(ladderLang α).Structure M]

/-- The value of the `n`-th constant. -/
def constVal (n : ℕ) : M :=
  Structure.funMap (L := ladderLang α) (show (ladderLang α).Functions 0 from n) Fin.elim0

/-- The level predicate `U_i`. -/
def Level (i : Index α) (x : M) : Prop :=
  Structure.RelMap (L := ladderLang α) (show (ladderLang α).Relations 1 from i) (fun _ => x)

/-- The edge relation `E`. -/
def Edge (x y : M) : Prop :=
  Structure.RelMap (L := ladderLang α) (show (ladderLang α).Relations 2 from ()) ![x, y]

/-- **The six clauses of a ladder model** — the interface every semantic file works with. -/
structure IsLadderModel : Prop where
  base : ∀ x : M, Level α ⊥ x ↔ ∃ n, x = constVal α n
  top : ∀ x : M, Level α ⊤ x
  nested : ∀ {i j : Index α}, i < j → ∀ x : M, Level α i x → Level α j x
  limit_covered : ∀ {j : Index α}, Order.IsSuccLimit j → ∀ x : M,
    Level α j x → ∃ i < j, Level α i x
  pred_down : ∀ {i j : Index α}, i ⋖ j → ∀ x y : M,
    Level α j x → Edge α y x → Level α i y
  ext : ∀ y z : M, (∀ x : M, Edge α x y ↔ Edge α x z) → y = z

variable {α}

section RealizeHelpers

/-- Constant terms realize to their values, at any valuation. -/
private theorem realize_const {γ : Type} (v : γ → M) (n : ℕ) :
    (const n : (ladderLang α).Term γ).realize v = constVal α n := by
  change Structure.funMap _ _ = _
  congr 1
  exact funext fun i => i.elim0

private theorem realize_levelAtom {γ : Type} {n : ℕ} (i : Index α)
    (t : (ladderLang α).Term (γ ⊕ Fin n)) (v : γ → M) (xs : Fin n → M) :
    (levelAtom i t).Realize v xs ↔ Level α i (t.realize (Sum.elim v xs)) := by
  rw [levelAtom, BoundedFormulaω.realize_rel, Level]

private theorem realize_eAtom {γ : Type} {n : ℕ}
    (t u : (ladderLang α).Term (γ ⊕ Fin n)) (v : γ → M) (xs : Fin n → M) :
    (eAtom t u).Realize v xs ↔
      Edge α (t.realize (Sum.elim v xs)) (u.realize (Sum.elim v xs)) := by
  rw [eAtom, BoundedFormulaω.realize_rel, Edge]
  refine Iff.of_eq (congrArg _ ?_)
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl

/-- The bound variable at arity `1` realizes to the snoc value. -/
private theorem realize_bvar1 (x : M) :
    (bvar 0 : (ladderLang α).Term (Empty ⊕ Fin 1)).realize
      (Sum.elim (Empty.elim : Empty → M) (Fin.snoc Fin.elim0 x)) = x := by
  change (Fin.snoc (Fin.elim0 : Fin 0 → M) x : Fin 1 → M) (Fin.last 0) = x
  exact Fin.snoc_last _ _

end RealizeHelpers

variable [Countable (Index α)]

/-- **The acceptance gate: realization of the ladder sentence is exactly the six clauses.** -/
theorem realize_ladderSentence_iff :
    Sentenceω.Realize (ladderSentence α) M ↔ IsLadderModel α (M := M) := by
  have hmaster : Sentenceω.Realize (ladderSentence α) M ↔
      (Sentenceω.Realize (baseInC α) M ∧ Sentenceω.Realize (baseOutC α) M ∧
        Sentenceω.Realize (topC α) M ∧ Sentenceω.Realize (nestedC α) M ∧
        Sentenceω.Realize (limitC α) M ∧ Sentenceω.Realize (predC α) M ∧
        Sentenceω.Realize (extC α) M) := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [ladderSentence, BoundedFormulaω.realize_iInf]
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
    · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ k
      match k with
      | 0 => exact h0
      | 1 => exact h1
      | 2 => exact h2
      | 3 => exact h3
      | 4 => exact h4
      | 5 => exact h5
      | (n + 6) => exact h6
  rw [hmaster]
  -- per-group semantic characterizations
  have hbaseIn : Sentenceω.Realize (baseInC α) M ↔
      ∀ n : ℕ, Level α ⊥ (constVal α n : M) := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [baseInC, BoundedFormulaω.realize_iInf]
    refine forall_congr' fun n => ?_
    rw [realize_levelAtom, realize_const]
  have hbaseOut : Sentenceω.Realize (baseOutC α) M ↔
      ∀ x : M, Level α ⊥ x → ∃ n, x = constVal α n := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [baseOutC, BoundedFormulaω.realize_all]
    refine forall_congr' fun x => ?_
    rw [BoundedFormulaω.realize_imp, realize_levelAtom, BoundedFormulaω.realize_iSup]
    refine imp_congr ?_ (exists_congr fun n => ?_)
    · rw [realize_bvar1 x]
    · rw [BoundedFormulaω.realize_equal, realize_const,
        realize_bvar1 x]
  have htop : Sentenceω.Realize (topC α) M ↔ ∀ x : M, Level α ⊤ x := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [topC, BoundedFormulaω.realize_all]
    refine forall_congr' fun x => ?_
    rw [realize_levelAtom,
      realize_bvar1 x]
  have hnested : Sentenceω.Realize (nestedC α) M ↔
      ∀ {i j : Index α}, i < j → ∀ x : M, Level α i x → Level α j x := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [nestedC, BoundedFormulaω.realize_ciInf]
    constructor
    · intro h i j hij x
      have hx := (BoundedFormulaω.realize_all _).mp (h ⟨(i, j), hij⟩) x
      rw [BoundedFormulaω.realize_imp, realize_levelAtom, realize_levelAtom,
        realize_bvar1 x] at hx
      exact hx
    · intro h p
      rw [BoundedFormulaω.realize_all]
      intro x
      rw [BoundedFormulaω.realize_imp, realize_levelAtom, realize_levelAtom,
        realize_bvar1 x]
      exact h p.2 x
  have hlimit : Sentenceω.Realize (limitC α) M ↔
      ∀ {j : Index α}, Order.IsSuccLimit j → ∀ x : M,
        Level α j x → ∃ i < j, Level α i x := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [limitC, BoundedFormulaω.realize_ciInf]
    constructor
    · intro h j hj x
      have hx := (BoundedFormulaω.realize_all _).mp (h ⟨j, hj⟩) x
      rw [BoundedFormulaω.realize_imp, realize_levelAtom, BoundedFormulaω.realize_ciSup,
        realize_bvar1 x] at hx
      intro hlev
      obtain ⟨i, hi⟩ := hx hlev
      rw [realize_levelAtom,
        realize_bvar1 x] at hi
      exact ⟨i.1, i.2, hi⟩
    · intro h j
      rw [BoundedFormulaω.realize_all]
      intro x
      rw [BoundedFormulaω.realize_imp, realize_levelAtom, BoundedFormulaω.realize_ciSup,
        realize_bvar1 x]
      intro hlev
      obtain ⟨i, hi, hlevi⟩ := h j.2 x hlev
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [realize_levelAtom,
        realize_bvar1 x]
      exact hlevi
  have hval2 : ∀ (x y : M) (i : Fin 2),
      (bvar i : (ladderLang α).Term (Empty ⊕ Fin 2)).realize
        (Sum.elim Empty.elim (Fin.snoc (Fin.snoc Fin.elim0 x) y)) =
      (Fin.snoc (Fin.snoc Fin.elim0 x) y : Fin 2 → M) i := fun _ _ _ => rfl
  have hsn20 : ∀ x y : M, (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → M) x) y : Fin 2 → M) 0
      = x := by
    intro x y
    change (Fin.snoc (Fin.snoc Fin.elim0 x) y : Fin 2 → M) (Fin.castSucc (Fin.last 0)) = x
    rw [Fin.snoc_castSucc]
    exact Fin.snoc_last _ _
  have hsn21 : ∀ x y : M, (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → M) x) y : Fin 2 → M) 1
      = y := by
    intro x y
    change (Fin.snoc (Fin.snoc Fin.elim0 x) y : Fin 2 → M) (Fin.last 1) = y
    exact Fin.snoc_last _ _
  have hpred : Sentenceω.Realize (predC α) M ↔
      ∀ {i j : Index α}, i ⋖ j → ∀ x y : M,
        Level α j x → Edge α y x → Level α i y := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [predC, BoundedFormulaω.realize_ciInf]
    have hstep : ∀ (p : {p : Index α × Index α // p.1 ⋖ p.2}),
        (BoundedFormulaω.all (BoundedFormulaω.all
          ((levelAtom p.1.2 (bvar 0)).imp
            ((eAtom (bvar 1) (bvar 0)).imp (levelAtom p.1.1 (bvar 1))))) :
          (ladderLang α).Sentenceω).Realize
          (Empty.elim : Empty → M) Fin.elim0 ↔
        ∀ x y : M, Level α p.1.2 x → Edge α y x → Level α p.1.1 y := by
      intro p
      rw [BoundedFormulaω.realize_all]
      refine forall_congr' fun x => ?_
      rw [BoundedFormulaω.realize_all]
      refine forall_congr' fun y => ?_
      rw [BoundedFormulaω.realize_imp, BoundedFormulaω.realize_imp,
        realize_levelAtom, realize_eAtom, realize_levelAtom]
      simp only [hval2, hsn20, hsn21]
    constructor
    · intro h i j hij
      exact (hstep ⟨(i, j), hij⟩).mp (h ⟨(i, j), hij⟩)
    · intro h p
      exact (hstep p).mpr (h p.2)
  have hext : Sentenceω.Realize (extC α) M ↔
      ∀ y z : M, (∀ x : M, Edge α x y ↔ Edge α x z) → y = z := by
    change BoundedFormulaω.Realize _ (Empty.elim : Empty → M) Fin.elim0 ↔ _
    rw [extC, BoundedFormulaω.realize_all]
    refine forall_congr' fun y => ?_
    rw [BoundedFormulaω.realize_all]
    refine forall_congr' fun z => ?_
    have hval3 : ∀ (x : M) (i : Fin 3),
        (bvar i : (ladderLang α).Term (Empty ⊕ Fin 3)).realize
          (Sum.elim Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 y) z) x)) =
        (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 y) z) x : Fin 3 → M) i := fun _ _ => rfl
    have hsn30 : ∀ x : M,
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → M) y) z) x : Fin 3 → M) 0 = y := by
      intro x
      change (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 y) z) x : Fin 3 → M)
        (Fin.castSucc (Fin.castSucc (Fin.last 0))) = y
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact Fin.snoc_last _ _
    have hsn31 : ∀ x : M,
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → M) y) z) x : Fin 3 → M) 1 = z := by
      intro x
      change (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 y) z) x : Fin 3 → M)
        (Fin.castSucc (Fin.last 1)) = z
      rw [Fin.snoc_castSucc]
      exact Fin.snoc_last _ _
    have hsn32 : ∀ x : M,
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → M) y) z) x : Fin 3 → M) 2 = x := by
      intro x
      change (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 y) z) x : Fin 3 → M) (Fin.last 2) = x
      exact Fin.snoc_last _ _
    rw [BoundedFormulaω.realize_imp, BoundedFormulaω.realize_imp,
      BoundedFormulaω.realize_equal]
    have hinner1 : (BoundedFormulaω.all
        ((eAtom (bvar 2) (bvar 0)).imp (eAtom (bvar 2) (bvar 1)) :
          (ladderLang α).BoundedFormulaω Empty 3)).Realize
        (Empty.elim : Empty → M) (Fin.snoc (Fin.snoc Fin.elim0 y) z) ↔
        ∀ x : M, Edge α x y → Edge α x z := by
      rw [BoundedFormulaω.realize_all]
      refine forall_congr' fun x => ?_
      rw [BoundedFormulaω.realize_imp, realize_eAtom, realize_eAtom]
      simp only [hval3, hsn30, hsn31, hsn32]
    have hinner2 : (BoundedFormulaω.all
        ((eAtom (bvar 2) (bvar 1)).imp (eAtom (bvar 2) (bvar 0)) :
          (ladderLang α).BoundedFormulaω Empty 3)).Realize
        (Empty.elim : Empty → M) (Fin.snoc (Fin.snoc Fin.elim0 y) z) ↔
        ∀ x : M, Edge α x z → Edge α x y := by
      rw [BoundedFormulaω.realize_all]
      refine forall_congr' fun x => ?_
      rw [BoundedFormulaω.realize_imp, realize_eAtom, realize_eAtom]
      simp only [hval3, hsn30, hsn31, hsn32]
    rw [hinner1, hinner2, hval2 y z 0, hval2 y z 1, hsn20 y z, hsn21 y z]
    constructor
    · intro h hiff
      exact h (fun x => (hiff x).mp) (fun x => (hiff x).mpr)
    · intro h h1 h2
      exact h fun x => ⟨h1 x, h2 x⟩
  rw [hbaseIn, hbaseOut, htop, hnested, hlimit, hpred, hext]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨fun x => ⟨h1 x, fun ⟨n, hn⟩ => by rw [hn]; exact h0 n⟩, h2,
      fun {i j} => h3, fun {j} => h4, fun {i j} => h5, h6⟩
  · rintro ⟨hb, ht, hn, hl, hp, he⟩
    exact ⟨fun n => (hb _).mpr ⟨n, rfl⟩, fun x hx => (hb x).mp hx, ht,
      fun {i j} => hn, fun {j} => hl, fun {i j} => hp, he⟩

end Semantics

end HanfLadder

end Language

end FirstOrder
