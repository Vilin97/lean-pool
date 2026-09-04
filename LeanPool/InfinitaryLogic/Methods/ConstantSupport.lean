/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.FiniteQuantification
import LeanPool.InfinitaryLogic.Lomega1omega.QuantifierClass
import LeanPool.InfinitaryLogic.Methods.LanguageMapOccurrence
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
import Mathlib.Data.Set.Finite.Lattice

/-!
# The constant-support calculus for a constant expansion `L[[J]]` (issue #8 kernel step 2)

The neutral home of the syntactic constant-support machinery, moved and generalized from
`Methods/MarkerStage.lean` (its Layers 2/5 discovered the finite-support problem: an `L_{ω₁ω}`
formula can mention infinitely many constants — `⋁ₙ (dₙ = dₙ)` has support all of `ℕ` — so
freshness arguments must CARRY a finite support rather than compute one). Craig interpolation
(#8) consumes the same calculus for its `InsepAt`-parameterized separators.

* the generic `functionsIn` structural lemmas (relabel / castLE / subst / openBounds /
  finiteness), verbatim from MarkerStage;
* `sentenceJConsts` — the constant support of an `L'[[J]]`-formula — with its monotonicity
  calculus, verbatim from MarkerStage;
* NEW: term-level support (`Term.jConsts`), the constant closed term (`constTerm`),
  instantiation support bounds, the base-symbol projections (`baseFunctionsIn` /
  `baseRelationsIn`), and `stripConsts` — a constant-free expansion formula restricts to the
  base language, with `mapLanguage (lhomWithConstants)` as left inverse and occurrence
  transport (the `A = ∅` root gate of the interpolation argument).
-/

namespace FirstOrder.Language

/-! ## Structural lemmas for `functionsIn` (relabel / castLE / subst / openBounds)

The mentioned function symbols are stable under variable renamings and grow only by the
substituted terms' symbols under substitution. Generic over the language. -/

section FunctionsIn

variable {L : Language.{0, 0}} {α β : Type}

theorem Term.functionsIn_relabel (g : α → β) (t : L.Term α) :
    (t.relabel g).functionsIn = t.functionsIn := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.relabel, Term.functionsIn, ih]

theorem Term.functionsIn_subst (tf : α → L.Term β) (t : L.Term α) :
    (t.subst tf).functionsIn ⊆ t.functionsIn ∪ ⋃ a, (tf a).functionsIn := by
  induction t with
  | var x =>
    simp only [Term.subst, Term.functionsIn, Set.empty_union]
    exact Set.subset_iUnion (fun a => (tf a).functionsIn) x
  | func f ts ih =>
    simp only [Term.subst, Term.functionsIn]
    rw [Set.insert_subset_iff]
    refine ⟨Set.mem_union_left _ (Set.mem_insert _ _), Set.iUnion_subset fun i => ?_⟩
    exact (ih i).trans (Set.union_subset_union
      ((Set.subset_iUnion (fun i => (ts i).functionsIn) i).trans (Set.subset_insert _ _)) subset_rfl)

private theorem BoundedFormulaω.functionsIn_castLE {m n : ℕ} (h : m ≤ n)
    (φ : L.BoundedFormulaω α m) : (φ.castLE h).functionsIn = φ.functionsIn := by
  induction φ generalizing n with
  | falsum => rfl
  | equal t₁ t₂ => simp only [BoundedFormulaω.castLE, BoundedFormulaω.functionsIn,
      Term.functionsIn_relabel]
  | rel R ts => simp only [BoundedFormulaω.castLE, BoundedFormulaω.functionsIn,
      Term.functionsIn_relabel]
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.castLE, BoundedFormulaω.functionsIn, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.castLE, BoundedFormulaω.functionsIn, ih]
  | iSup φs ih => simp only [BoundedFormulaω.castLE, BoundedFormulaω.functionsIn, ih]
  | iInf φs ih => simp only [BoundedFormulaω.castLE, BoundedFormulaω.functionsIn, ih]

theorem BoundedFormulaω.functionsIn_relabel {n : ℕ} (g : α → β ⊕ Fin n) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k), (φ.relabel g).functionsIn = φ.functionsIn := by
  intro k φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp only [BoundedFormulaω.relabel, BoundedFormulaω.functionsIn,
      Term.functionsIn_relabel]
  | rel R ts => simp only [BoundedFormulaω.relabel, BoundedFormulaω.functionsIn,
      Term.functionsIn_relabel]
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.relabel, BoundedFormulaω.functionsIn, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.relabel, BoundedFormulaω.functionsIn,
      BoundedFormulaω.functionsIn_castLE, ih]
  | iSup φs ih => simp only [BoundedFormulaω.relabel, BoundedFormulaω.functionsIn, ih]
  | iInf φs ih => simp only [BoundedFormulaω.relabel, BoundedFormulaω.functionsIn, ih]

private theorem BoundedFormulaω.relationsIn_castLE {m n : ℕ} (h : m ≤ n)
    (φ : L.BoundedFormulaω α m) : (φ.castLE h).relationsIn = φ.relationsIn := by
  induction φ generalizing n with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.castLE, BoundedFormulaω.relationsIn, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.castLE, BoundedFormulaω.relationsIn, ih]
  | iSup φs ih => simp only [BoundedFormulaω.castLE, BoundedFormulaω.relationsIn, ih]
  | iInf φs ih => simp only [BoundedFormulaω.castLE, BoundedFormulaω.relationsIn, ih]

theorem BoundedFormulaω.relationsIn_relabel {n : ℕ} (g : α → β ⊕ Fin n) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k), (φ.relabel g).relationsIn = φ.relationsIn := by
  intro k φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.relabel, BoundedFormulaω.relationsIn, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.relabel, BoundedFormulaω.relationsIn,
      BoundedFormulaω.relationsIn_castLE, ih]
  | iSup φs ih => simp only [BoundedFormulaω.relabel, BoundedFormulaω.relationsIn, ih]
  | iInf φs ih => simp only [BoundedFormulaω.relabel, BoundedFormulaω.relationsIn, ih]

theorem BoundedFormulaω.functionsIn_subst (tf : α → L.Term β) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      (φ.subst tf).functionsIn ⊆ φ.functionsIn ∪ ⋃ a, (tf a).functionsIn := by
  intro k φ
  induction φ with
  | falsum => simp only [BoundedFormulaω.subst, BoundedFormulaω.functionsIn]; exact Set.empty_subset _
  | equal t₁ t₂ =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.functionsIn]
    refine Set.union_subset ?_ ?_ <;>
      · refine (Term.functionsIn_subst _ _).trans (Set.union_subset_union ?_ ?_)
        · first
          | exact Set.subset_union_left
          | exact Set.subset_union_right
        · refine Set.iUnion_subset fun x => ?_
          rcases x with a | i
          · simpa only [Sum.elim_inl, Function.comp_apply, Term.functionsIn_relabel] using
              Set.subset_iUnion (fun a => (tf a).functionsIn) a
          · simp only [Sum.elim_inr, Function.comp_apply, Term.functionsIn]
            exact Set.empty_subset _
  | rel R ts =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.functionsIn]
    refine Set.iUnion_subset fun i => (Term.functionsIn_subst _ _).trans
      (Set.union_subset_union (Set.subset_iUnion (fun i => (ts i).functionsIn) i)
        (Set.iUnion_subset fun x => ?_))
    rcases x with a | j
    · simpa only [Sum.elim_inl, Function.comp_apply, Term.functionsIn_relabel] using
        Set.subset_iUnion (fun a => (tf a).functionsIn) a
    · simp only [Sum.elim_inr, Function.comp_apply, Term.functionsIn]
      exact Set.empty_subset _
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.functionsIn]
    exact Set.union_subset
      (ihφ.trans (Set.union_subset_union_left _ Set.subset_union_left))
      (ihψ.trans (Set.union_subset_union_left _ Set.subset_union_right))
  | all φ ih => simpa only [BoundedFormulaω.subst, BoundedFormulaω.functionsIn] using ih
  | iSup φs ih =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.functionsIn]
    exact Set.iUnion_subset fun i => (ih i).trans
      (Set.union_subset_union_left _ (Set.subset_iUnion (fun i => BoundedFormulaω.functionsIn (φs i)) i))
  | iInf φs ih =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.functionsIn]
    exact Set.iUnion_subset fun i => (ih i).trans
      (Set.union_subset_union_left _ (Set.subset_iUnion (fun i => BoundedFormulaω.functionsIn (φs i)) i))

theorem BoundedFormulaω.functionsIn_openBounds :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
      (φ.openBounds).functionsIn = φ.functionsIn := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp only [BoundedFormulaω.openBounds, BoundedFormulaω.functionsIn,
      Term.functionsIn_relabel]
  | rel R ts => simp only [BoundedFormulaω.openBounds, BoundedFormulaω.functionsIn,
      Term.functionsIn_relabel]
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.openBounds, BoundedFormulaω.functionsIn,
      ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.openBounds, BoundedFormulaω.functionsIn,
      BoundedFormulaω.functionsIn_relabel, ih]
  | iSup φs ih => simp only [BoundedFormulaω.openBounds, BoundedFormulaω.functionsIn, ih]
  | iInf φs ih => simp only [BoundedFormulaω.openBounds, BoundedFormulaω.functionsIn, ih]

/-- A term mentions only finitely many function symbols (it is a finite tree). -/
theorem Term.functionsIn_finite (t : L.Term α) : t.functionsIn.Finite := by
  induction t with
  | var x => simp [Term.functionsIn]
  | func f ts ih => exact (Set.finite_iUnion ih).insert _





/-- Negation does not change the mentioned function symbols (`not` is `imp · ⊥`). -/
theorem BoundedFormulaω.functionsIn_not {n : ℕ} (φ : L.BoundedFormulaω α n) :
    (φ.not).functionsIn = φ.functionsIn := by
  show φ.functionsIn ∪ (BoundedFormulaω.falsum : L.BoundedFormulaω α n).functionsIn = _
  simp only [BoundedFormulaω.functionsIn, Set.union_empty]

/-- Existential quantification (`¬∀¬`) does not change the mentioned function symbols. -/
theorem BoundedFormulaω.functionsIn_ex {n : ℕ} (φ : L.BoundedFormulaω α (n + 1)) :
    (φ.ex).functionsIn = φ.functionsIn := by
  show (φ.not.all.not).functionsIn = _
  rw [BoundedFormulaω.functionsIn_not]
  show (φ.not).functionsIn = _
  rw [BoundedFormulaω.functionsIn_not]

/-- Negation does not change the mentioned relation symbols. -/
theorem BoundedFormulaω.relationsIn_not {n : ℕ} (φ : L.BoundedFormulaω α n) :
    (φ.not).relationsIn = φ.relationsIn := by
  show φ.relationsIn ∪ (BoundedFormulaω.falsum : L.BoundedFormulaω α n).relationsIn = _
  simp only [BoundedFormulaω.relationsIn, Set.union_empty]

/-- Existential quantification does not change the mentioned relation symbols. -/
theorem BoundedFormulaω.relationsIn_ex {n : ℕ} (φ : L.BoundedFormulaω α (n + 1)) :
    (φ.ex).relationsIn = φ.relationsIn := by
  show (φ.not.all.not).relationsIn = _
  rw [BoundedFormulaω.relationsIn_not]
  show (φ.not).relationsIn = _
  rw [BoundedFormulaω.relationsIn_not]



/-- A finite existential block does not change the mentioned relation symbols. -/
theorem BoundedFormulaω.relationsIn_existsBlock {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α (n + k)),
      (φ.existsBlock).relationsIn = φ.relationsIn
  | 0, _ => rfl
  | _ + 1, φ => (relationsIn_existsBlock φ.ex).trans (BoundedFormulaω.relationsIn_ex φ)



/-- A finite universal block does not change the mentioned relation symbols. -/
theorem BoundedFormulaω.relationsIn_forallBlock {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α (n + k)),
      (φ.forallBlock).relationsIn = φ.relationsIn
  | 0, _ => rfl
  | _ + 1, φ => relationsIn_forallBlock φ.all



/-- The true formula mentions no relation symbols. -/
private theorem BoundedFormulaω.relationsIn_top {n : ℕ} :
    (⊤ : L.BoundedFormulaω α n).relationsIn = ∅ :=
  Set.union_empty ∅



/-- Binary conjunction collects both sides' relation symbols. -/
theorem BoundedFormulaω.relationsIn_and {n : ℕ} (φ ψ : L.BoundedFormulaω α n) :
    (φ.and ψ).relationsIn = φ.relationsIn ∪ ψ.relationsIn := by
  show ((φ.imp ψ.not).not).relationsIn = _
  rw [BoundedFormulaω.relationsIn_not]
  show φ.relationsIn ∪ (ψ.not).relationsIn = _
  rw [BoundedFormulaω.relationsIn_not]



/-- An `Encodable`-indexed conjunction collects the branches' relation symbols. -/
theorem BoundedFormulaω.relationsIn_einf {ι : Type*} [Encodable ι] {n : ℕ}
    (φs : ι → L.BoundedFormulaω α n) :
    (BoundedFormulaω.einf φs).relationsIn = ⋃ i, (φs i).relationsIn := by
  ext x
  simp only [BoundedFormulaω.einf, BoundedFormulaω.relationsIn, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := ι) k with
    | none => rw [hd, BoundedFormulaω.relationsIn_top] at hk; exact absurd hk (Set.notMem_empty x)
    | some i => rw [hd] at hk; exact ⟨i, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨Encodable.encode i, by rw [Encodable.encodek]; exact hi⟩

/-- In a relational language no formula mentions a function symbol. -/
theorem BoundedFormulaω.functionsIn_of_isRelational {L' : Language.{0, 0}} [L'.IsRelational]
    {α : Type} {n : ℕ} (φ : L'.BoundedFormulaω α n) : φ.functionsIn = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  exact fun p _ => IsEmpty.false p.2

/-- **Occurrence-aware term-realization congruence**: two structure instances agreeing on the
function symbols occurring in `t` realize `t` identically. -/
private theorem Term.realize_congr_functionsIn {M : Type} (S S' : L.Structure M) {γ : Type} :
    ∀ (t : L.Term γ)
      (_ : ∀ p ∈ t.functionsIn, ∀ x : Fin p.1 → M,
        @Structure.funMap L M S p.1 p.2 x = @Structure.funMap L M S' p.1 p.2 x)
      (v : γ → M),
      @Term.realize L M S γ v t = @Term.realize L M S' γ v t
  | .var _, _, _ => rfl
  | .func f ts, hf, v => by
    show @Structure.funMap L M S _ f _ = @Structure.funMap L M S' _ f _
    rw [hf ⟨_, f⟩ (Set.mem_insert _ _)]
    exact congrArg _ (funext fun i => Term.realize_congr_functionsIn S S' (ts i)
      (fun p hp x => hf p (Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨i, hp⟩)) x) v)

/-- **Occurrence-aware realization congruence**: two structure instances agreeing on the
symbols occurring in `φ` realize `φ` identically. The tool that localizes semantic transport
to a formula's own vocabulary. -/
theorem BoundedFormulaω.realize_congr_symbolsIn {M : Type} (S S' : L.Structure M) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n)
      (_ : ∀ p ∈ φ.functionsIn, ∀ x : Fin p.1 → M,
        @Structure.funMap L M S p.1 p.2 x = @Structure.funMap L M S' p.1 p.2 x)
      (_ : ∀ p ∈ φ.relationsIn, ∀ x : Fin p.1 → M,
        (@Structure.RelMap L M S p.1 p.2 x ↔ @Structure.RelMap L M S' p.1 p.2 x))
      (v : α → M) (xs : Fin n → M),
      @BoundedFormulaω.Realize L M S α n φ v xs ↔ @BoundedFormulaω.Realize L M S' α n φ v xs
  | _, .falsum, _, _, _, _ => Iff.rfl
  | _, .equal t₁ t₂, hf, _, v, xs => by
    show @Term.realize L M S _ _ t₁ = @Term.realize L M S _ _ t₂
      ↔ @Term.realize L M S' _ _ t₁ = @Term.realize L M S' _ _ t₂
    rw [Term.realize_congr_functionsIn S S' t₁ (fun p hp => hf p (Set.mem_union_left _ hp)),
      Term.realize_congr_functionsIn S S' t₂ (fun p hp => hf p (Set.mem_union_right _ hp))]
  | _, .rel R ts, hf, hr, v, xs => by
    show @Structure.RelMap L M S _ R _ ↔ @Structure.RelMap L M S' _ R _
    rw [show (fun i => @Term.realize L M S _ _ (ts i))
        = (fun i => @Term.realize L M S' _ _ (ts i)) from funext fun i =>
          Term.realize_congr_functionsIn S S' (ts i)
            (fun p hp => hf p (Set.mem_iUnion.mpr ⟨i, hp⟩)) _]
    exact hr ⟨_, R⟩ rfl _
  | _, .imp φ ψ, hf, hr, v, xs =>
    -- term mode: the lemma is stated through the reducible `BoundedFormulaω.Realize` alias,
    -- so `rw` cannot key on it against a goal in `BoundedFormulaInf.Realize`
    Iff.imp
      (BoundedFormulaω.realize_congr_symbolsIn S S' φ
        (fun p hp => hf p (Set.mem_union_left _ hp))
        (fun p hp => hr p (Set.mem_union_left _ hp)) v xs)
      (BoundedFormulaω.realize_congr_symbolsIn S S' ψ
        (fun p hp => hf p (Set.mem_union_right _ hp))
        (fun p hp => hr p (Set.mem_union_right _ hp)) v xs)
  | _, .all φ, hf, hr, v, xs =>
    forall_congr' fun x =>
      BoundedFormulaω.realize_congr_symbolsIn S S' φ hf hr v (Fin.snoc xs x)
  | _, .iSup φs, hf, hr, v, xs =>
    exists_congr fun i => BoundedFormulaω.realize_congr_symbolsIn S S' (φs i)
      (fun p hp => hf p (Set.mem_iUnion.mpr ⟨i, hp⟩))
      (fun p hp => hr p (Set.mem_iUnion.mpr ⟨i, hp⟩)) v xs
  | _, .iInf φs, hf, hr, v, xs =>
    forall_congr' fun i => BoundedFormulaω.realize_congr_symbolsIn S S' (φs i)
      (fun p hp => hf p (Set.mem_iUnion.mpr ⟨i, hp⟩))
      (fun p hp => hr p (Set.mem_iUnion.mpr ⟨i, hp⟩)) v xs

end FunctionsIn

/-! ## Constant support of a constant-expansion formula -/

section ConstSupport

variable {L' : Language.{0, 0}} {J : Type}

/-- The syntactic constant support of an `L'[[J]]`-formula: the added constants (arity-0
`Sum.inr` function symbols) among its mentioned symbols. Only countable in general
(`functionsIn_countable` — countably-branching connectives); freshness arguments *demand*
containment in a finite set rather than computing one. Generic in the base language, so it
also serves iterated expansion layers (`L := L'[[J]]`, constants `ℕ`). -/
def sentenceJConsts {α : Type} {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) : Set J :=
  {j | (⟨0, (Sum.inr j : L'[[J]].Functions 0)⟩ : Σ n, L'[[J]].Functions n) ∈
    BoundedFormulaω.functionsIn φ}

/-- Negation does not change the constant support (`not` is `imp · falsum`). -/
theorem sentenceJConsts_not {α : Type} {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) :
    sentenceJConsts (L' := L') φ.not = sentenceJConsts (L' := L') φ := by
  ext j
  simp [sentenceJConsts, BoundedFormulaω.functionsIn]

/-- A conjunction component's constant support is contained in the conjunction's. -/
theorem sentenceJConsts_component_iInf {α : Type} {n : ℕ}
    (φs : ℕ → L'[[J]].BoundedFormulaω α n) (k : ℕ) :
    sentenceJConsts (L' := L') (φs k) ⊆
      sentenceJConsts (L' := L') (BoundedFormulaω.iInf φs) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_iUnion.mpr ⟨k, hj⟩

/-- A disjunction component's constant support is contained in the disjunction's. -/
theorem sentenceJConsts_component_iSup {α : Type} {n : ℕ}
    (φs : ℕ → L'[[J]].BoundedFormulaω α n) (k : ℕ) :
    sentenceJConsts (L' := L') (φs k) ⊆
      sentenceJConsts (L' := L') (BoundedFormulaω.iSup φs) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_iUnion.mpr ⟨k, hj⟩

/-- An implication's antecedent support is contained in the implication's. -/
theorem sentenceJConsts_imp_left {α : Type} {n : ℕ} (φ ψ : L'[[J]].BoundedFormulaω α n) :
    sentenceJConsts (L' := L') φ ⊆ sentenceJConsts (L' := L') (φ.imp ψ) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_union_left _ hj

/-- An implication's consequent support is contained in the implication's. -/
theorem sentenceJConsts_imp_right {α : Type} {n : ℕ} (φ ψ : L'[[J]].BoundedFormulaω α n) :
    sentenceJConsts (L' := L') ψ ⊆ sentenceJConsts (L' := L') (φ.imp ψ) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
  exact Set.mem_union_right _ hj

/-- The constant support of an expansion term. -/
def Term.jConsts {β : Type} (t : L'[[J]].Term β) : Set J :=
  {j | (⟨0, (Sum.inr j : L'[[J]].Functions 0)⟩ : Σ n, L'[[J]].Functions n) ∈
    Term.functionsIn t}

/-- The `j`-th constant of the expansion, as a closed term. -/
def constTerm (j : J) : L'[[J]].Term Empty :=
  Term.func (Sum.inr j : L'[[J]].Functions 0) Fin.elim0

theorem constTerm_functionsIn (j : J) :
    (constTerm (L' := L') j).functionsIn =
      {(⟨0, (Sum.inr j : L'[[J]].Functions 0)⟩ : Σ n, L'[[J]].Functions n)} := by
  simp [constTerm, Term.functionsIn, Set.iUnion_of_empty]

/-- `openBounds` does not change the constant support. -/
theorem sentenceJConsts_openBounds {n : ℕ} (φ : L'[[J]].BoundedFormulaω Empty n) :
    sentenceJConsts (L' := L') φ.openBounds = sentenceJConsts (L' := L') φ := by
  unfold sentenceJConsts
  rw [BoundedFormulaω.functionsIn_openBounds]

/-- Existential quantification does not change the constant support. -/
theorem sentenceJConsts_ex {α : Type} {n : ℕ} (φ : L'[[J]].BoundedFormulaω α (n + 1)) :
    sentenceJConsts (L' := L') φ.ex = sentenceJConsts (L' := L') φ := by
  unfold sentenceJConsts
  rw [BoundedFormulaω.functionsIn_ex]

/-- **Instantiation support bound**: substituting the constant `j` into a one-variable
formula adds at most `j` to the constant support. -/
theorem sentenceJConsts_subst_constTerm (φ : L'[[J]].Formulaω (Fin 1)) (j : J) :
    sentenceJConsts (L' := L') (φ.subst fun _ => constTerm j) ⊆
      sentenceJConsts (L' := L') φ ∪ {j} := by
  intro j' hj'
  have h := BoundedFormulaω.functionsIn_subst (fun _ : Fin 1 => constTerm (L' := L') j) φ hj'
  rcases h with h | h
  · exact Set.mem_union_left _ h
  · right
    obtain ⟨_, ⟨a, rfl⟩, hmem⟩ := h
    rw [constTerm_functionsIn] at hmem
    have := Set.mem_singleton_iff.mp hmem
    have hinj : (Sum.inr j' : L'[[J]].Functions 0) = Sum.inr j := by
      have h0 := (Sigma.mk.injEq _ _ _ _).mp this
      exact eq_of_heq h0.2
    exact Set.mem_singleton_iff.mpr (Sum.inr.injEq j' j ▸ hinj)

/-- The base function symbols of an expansion formula (the `Sum.inl` layer). -/
def BoundedFormulaω.baseFunctionsIn {α : Type} {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) :
    Set (Σ n, L'.Functions n) :=
  {s | (⟨s.1, Sum.inl s.2⟩ : Σ n, L'[[J]].Functions n) ∈ φ.functionsIn}

/-- The base relation symbols of an expansion formula (the constant layer adds none). -/
def BoundedFormulaω.baseRelationsIn {α : Type} {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) :
    Set (Σ n, L'.Relations n) :=
  {s | (⟨s.1, Sum.inl s.2⟩ : Σ n, L'[[J]].Relations n) ∈ φ.relationsIn}

end ConstSupport

/-! ## Stripping constant-free formulas to the base language

A constant-free `L'[[J]]`-formula is (the `mapLanguage`-image of) a base formula. This is the
`A = ∅` root gate of the interpolation argument: a separator with empty allowed support
strips to an interpolant of the base language. -/

section Strip

variable {L' : Language.{0, 0}} {J : Type}

/-- Strip a constant-free expansion term to the base language. -/
def Term.stripConsts {β : Type} :
    ∀ t : L'[[J]].Term β, Term.jConsts (L' := L') t ⊆ ∅ → L'.Term β
  | .var x, _ => .var x
  | .func (Sum.inl f) ts, h =>
    .func f fun i => (ts i).stripConsts fun _ hj =>
      h (Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨i, hj⟩))
  | @Term.func _ _ 0 (Sum.inr c) _, h =>
    absurd (h (Set.mem_insert _ _)) (Set.notMem_empty c)
  | @Term.func _ _ (_ + 1) (Sum.inr c) _, _ => nomatch c

/-- The `withConstants` inclusion is a left inverse of term stripping. -/
private theorem Term.onTerm_stripConsts {β : Type} :
    ∀ (t : L'[[J]].Term β) (h : Term.jConsts (L' := L') t ⊆ ∅),
      (L'.lhomWithConstants J).onTerm (t.stripConsts h) = t := by
  intro t
  induction t with
  | var x => intro h; rfl
  | @func l f ts ih =>
    rcases f with f | c
    · intro h
      simp only [Term.stripConsts, LHom.onTerm]
      exact congrArg _ (funext fun i => ih i _)
    · cases l with
      | zero => intro h; exact absurd (h (Set.mem_insert _ _)) (Set.notMem_empty c)
      | succ l => exact nomatch c

/-- Occurrence transport for term stripping: the stripped term's symbols are the base
symbols of the original. -/
theorem Term.functionsIn_stripConsts {β : Type} :
    ∀ (t : L'[[J]].Term β) (h : Term.jConsts (L' := L') t ⊆ ∅),
      (t.stripConsts h).functionsIn ⊆
        {s : Σ n, L'.Functions n | (⟨s.1, Sum.inl s.2⟩ : Σ n, L'[[J]].Functions n) ∈
          Term.functionsIn t} := by
  intro t
  induction t with
  | var x => intro h s hs; exact absurd hs (Set.notMem_empty s)
  | @func l f ts ih =>
    rcases f with f | c
    · intro h s hs
      simp only [Term.stripConsts, Term.functionsIn] at hs
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact Set.mem_insert _ _
      · obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
        exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨i, ih i _ hmem⟩)
    · cases l with
      | zero => intro h; exact absurd (h (Set.mem_insert _ _)) (Set.notMem_empty c)
      | succ l => exact nomatch c

/-- Strip a constant-free expansion formula to the base language. -/
def BoundedFormulaω.stripConsts {α : Type} :
    ∀ {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n),
      sentenceJConsts (L' := L') φ ⊆ ∅ → L'.BoundedFormulaω α n
  | _, .falsum, _ => .falsum
  | _, .equal t u, h =>
    .equal (t.stripConsts fun _ hj => h (Set.mem_union_left _ hj))
      (u.stripConsts fun _ hj => h (Set.mem_union_right _ hj))
  | _, .rel (Sum.inl R) ts, h =>
    .rel R fun i => (ts i).stripConsts fun _ hj => h (Set.mem_iUnion.mpr ⟨i, hj⟩)
  | _, .rel (Sum.inr R) _, _ => nomatch R
  | _, .imp φ ψ, h =>
    .imp (φ.stripConsts fun _ hj => h (Set.mem_union_left _ hj))
      (ψ.stripConsts fun _ hj => h (Set.mem_union_right _ hj))
  | _, .all φ, h => .all (φ.stripConsts h)
  | _, .iSup φs, h =>
    .iSup fun i => (φs i).stripConsts fun _ hj => h (Set.mem_iUnion.mpr ⟨i, hj⟩)
  | _, .iInf φs, h =>
    .iInf fun i => (φs i).stripConsts fun _ hj => h (Set.mem_iUnion.mpr ⟨i, hj⟩)

/-- **Quantifier class is invariant under stripping constants.**  `stripConsts` rewrites only terms
and the relation tag; it touches no quantifier node, so the signed universal class is exact. -/
theorem BoundedFormulaω.universalSigned_stripConsts {α : Type} (s : Bool) :
    ∀ {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n)
      (h : sentenceJConsts (L' := L') φ ⊆ ∅),
      universalSigned s (φ.stripConsts h) ↔ universalSigned s φ := by
  intro n φ
  induction φ generalizing s with
  | falsum => intro _; exact Iff.rfl
  | equal t u => intro _; exact Iff.rfl
  | rel R ts =>
    intro h
    match R with
    | Sum.inl _ => exact Iff.rfl
    | Sum.inr R => exact nomatch R
  | imp φ ψ ihφ ihψ =>
    intro h
    show universalSigned (!s) _ ∧ universalSigned s _ ↔ _
    exact and_congr (ihφ (!s) _) (ihψ s _)
  | all φ ih =>
    intro h
    show s = true ∧ universalSigned s _ ↔ _
    exact and_congr_right fun _ => ih s _
  | iSup φs ih =>
    intro h
    show (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s _
  | iInf φs ih =>
    intro h
    show (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s _

/-- The `withConstants` inclusion is a left inverse of formula stripping. -/
theorem BoundedFormulaω.mapLanguage_stripConsts {α : Type} :
    ∀ {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) (h : sentenceJConsts (L' := L') φ ⊆ ∅),
      (φ.stripConsts h).mapLanguage (L'.lhomWithConstants J) = φ := by
  intro n φ
  induction φ with
  | falsum => intro h; rfl
  | equal t u =>
    intro h
    simp only [BoundedFormulaω.stripConsts, BoundedFormulaω.mapLanguage]
    exact congrArg₂ _ (Term.onTerm_stripConsts _ _) (Term.onTerm_stripConsts _ _)
  | rel R ts =>
    rcases R with R | R
    · intro h
      simp only [BoundedFormulaω.stripConsts, BoundedFormulaω.mapLanguage]
      exact congrArg _ (funext fun i => Term.onTerm_stripConsts (ts i) _)
    · exact nomatch R
  | imp φ ψ ihφ ihψ =>
    intro h
    simp only [BoundedFormulaω.stripConsts, BoundedFormulaω.mapLanguage]
    exact congrArg₂ _ (ihφ _) (ihψ _)
  | all φ ih =>
    intro h
    simp only [BoundedFormulaω.stripConsts, BoundedFormulaω.mapLanguage]
    exact congrArg _ (ih _)
  | iSup φs ih =>
    intro h
    simp only [BoundedFormulaω.stripConsts, BoundedFormulaω.mapLanguage]
    exact congrArg _ (funext fun i => ih i _)
  | iInf φs ih =>
    intro h
    simp only [BoundedFormulaω.stripConsts, BoundedFormulaω.mapLanguage]
    exact congrArg _ (funext fun i => ih i _)

/-- Occurrence transport for formula stripping (function symbols). -/
theorem BoundedFormulaω.functionsIn_stripConsts {α : Type} :
    ∀ {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) (h : sentenceJConsts (L' := L') φ ⊆ ∅),
      (φ.stripConsts h).functionsIn ⊆ φ.baseFunctionsIn := by
  intro n φ
  induction φ with
  | falsum => intro h s hs; exact absurd hs (Set.notMem_empty s)
  | equal t u =>
    intro h s hs
    rcases hs with hs | hs
    · exact Set.mem_union_left _ (Term.functionsIn_stripConsts t _ hs)
    · exact Set.mem_union_right _ (Term.functionsIn_stripConsts u _ hs)
  | rel R ts =>
    rcases R with R | R
    · intro h s hs
      obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
      exact Set.mem_iUnion.mpr ⟨i, Term.functionsIn_stripConsts (ts i) _ hmem⟩
    · exact nomatch R
  | imp φ ψ ihφ ihψ =>
    intro h s hs
    rcases hs with hs | hs
    · exact Set.mem_union_left _ (ihφ _ hs)
    · exact Set.mem_union_right _ (ihψ _ hs)
  | all φ ih => intro h s hs; exact ih _ hs
  | iSup φs ih =>
    intro h s hs
    obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
    exact Set.mem_iUnion.mpr ⟨i, ih i _ hmem⟩
  | iInf φs ih =>
    intro h s hs
    obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
    exact Set.mem_iUnion.mpr ⟨i, ih i _ hmem⟩

/-- Occurrence transport for formula stripping (relation symbols). -/
theorem BoundedFormulaω.relationsIn_stripConsts {α : Type} :
    ∀ {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) (h : sentenceJConsts (L' := L') φ ⊆ ∅),
      (φ.stripConsts h).relationsIn ⊆ φ.baseRelationsIn := by
  intro n φ
  induction φ with
  | falsum => intro h s hs; exact absurd hs (Set.notMem_empty s)
  | equal t u => intro h s hs; exact absurd hs (Set.notMem_empty s)
  | rel R ts =>
    rcases R with R | R
    · intro h s hs
      rcases Set.mem_singleton_iff.mp hs with rfl
      exact Set.mem_singleton _
    · exact nomatch R
  | imp φ ψ ihφ ihψ =>
    intro h s hs
    rcases hs with hs | hs
    · exact Set.mem_union_left _ (ihφ _ hs)
    · exact Set.mem_union_right _ (ihψ _ hs)
  | all φ ih => intro h s hs; exact ih _ hs
  | iSup φs ih =>
    intro h s hs
    obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
    exact Set.mem_iUnion.mpr ⟨i, ih i _ hmem⟩
  | iInf φs ih =>
    intro h s hs
    obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
    exact Set.mem_iUnion.mpr ⟨i, ih i _ hmem⟩

end Strip

/-- **A constant-expansion image carries no constants**: its constant support is empty. -/
theorem sentenceJConsts_mapLanguage_withConstants (r : L.Sentenceω) :
    sentenceJConsts (L' := L) (J := ℕ)
      (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r) = ∅ := by
  ext j
  simp only [sentenceJConsts, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn_mapLanguage,
    Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  rintro ⟨p1, p2⟩ - hpe
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hpe
  exact absurd (show (Sum.inl p2 : L[[ℕ]].Functions 0) = Sum.inr j from eq_of_heq h2) (by simp)

end FirstOrder.Language
