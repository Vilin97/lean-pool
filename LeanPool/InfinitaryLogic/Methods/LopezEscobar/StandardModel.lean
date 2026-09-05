/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.PCSentence
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorel
/-!
# The standard functional model and the forward presentation (issue #10, Unit 3a)

The graph-language **code reduct** along the base embedding, and the **standard functional
expansion** on `ℕ` built from a base code `c` and a branch `g`:

* `c^M = 0`, `s^M = succ` (so `numMap = id`);
* `f^M n = 1` exactly when `queryCode c n = true`;
* `g^M = g`;
* base relations read off `c`;
* `tree n` interpreted by `T n`, with `false` outside bit-coded first halves.

Forward acceptance gate (`subset_pcClass`): `c ∈ B → ∃ d, codeReduct d = c ∧
d ∈ ModelsOf (pcSentence side T)` — **without** `IsomorphismInvariant`.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ## The code reduct -/

/-- The base-language code reduct of a `graphLanguage (KLang L)`-code: read each base query
through the graph-language image `G_base(Sum.inl R)` of the base relation. -/
def codeReduct (d : StructureSpace (graphLanguage (KLang L))) : StructureSpace L :=
  fun q => d ⟨⟨q.1.1, GraphRelation.base (Sum.inl q.1.2)⟩, q.2⟩

omit [Countable (Σ l, L.Relations l)] in
/-- Compatibility with decoded structures: the reduct code's relations are the base graph
relations of the decoded structure. -/
theorem codeReduct_toStructure {d : StructureSpace (graphLanguage (KLang L))} {l : ℕ}
    (R : L.Relations l) (v : Fin l → ℕ) :
    @Structure.RelMap L ℕ (codeReduct d).toStructure l R v ↔
      @Structure.RelMap (graphLanguage (KLang L)) ℕ d.toStructure l
        (GraphRelation.base (Sum.inl R)) v :=
  Iff.rfl

/-! ## The standard functional structure -/

namespace LopezStd

/-- Decode a `{0,1}`-valued numeral back to a bit. -/
def decodeBit (m : ℕ) : Bool := decide (m = 1)

theorem decodeBit_cond (b : Bool) : decodeBit (cond b 1 0) = b := by
  cases b <;> rfl

/-- The first-half `Fin (2n)` index of `i : Fin n`. -/
private def firstIdx (n : ℕ) (i : Fin n) : Fin (2 * n) := ⟨(i : ℕ), by omega⟩

/-- The second-half `Fin (2n)` index of `i : Fin n`. -/
private def secondIdx (n : ℕ) (i : Fin n) : Fin (2 * n) := ⟨n + (i : ℕ), by omega⟩

variable (c : StructureSpace L) (g : ℕ → ℕ)
  (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))

/-- The witness function interpretation on `ℕ`: `c ↦ 0`, `s ↦ succ`, `f ↦` the query bit,
`g ↦` the branch. -/
private noncomputable def wFun : {k : ℕ} → WitnessFun k → (Fin k → ℕ) → ℕ
  | _, .c, _ => 0
  | _, .s, a => a 0 + 1
  | _, .f, a => cond (queryCode c (a 0)) 1 0
  | _, .g, a => g (a 0)

/-- The witness (tree) relation interpretation on `ℕ`: `tree n` decodes the first half as
bits, the second half as `τ`, and asks membership in `T n`. -/
private def wRel : {k : ℕ} → WitnessRel k → (Fin k → ℕ) → Prop
  | _, .tree n, u =>
      ((fun i : Fin n => decodeBit (u (firstIdx n i))), (fun i : Fin n => u (secondIdx n i)))
        ∈ T n

/-- **The standard `MidLang L`-structure** on `ℕ` from a code `c`, branch `g`, tree `T`. -/
@[reducible] noncomputable def standardMid : (MidLang L).Structure ℕ where
  funMap {_} f a :=
    match f with
    | Sum.inl f' => isEmptyElim f'
    | Sum.inr w => wFun c g w a
  RelMap {k} r a :=
    match r with
    | Sum.inl R => c ⟨⟨k, R⟩, a⟩ = true
    | Sum.inr w => wRel T w a

/-- **The standard `KLang L`-structure** on `ℕ`: both witness copies interpreted identically,
so its reduct along either side's embedding is `standardMid`. -/
@[reducible] noncomputable def standardK : (KLang L).Structure ℕ where
  funMap {_} f a :=
    match f with
    | Sum.inl f' => isEmptyElim f'
    | Sum.inr (Sum.inl w) => wFun c g w a
    | Sum.inr (Sum.inr w) => wFun c g w a
  RelMap {k} r a :=
    match r with
    | Sum.inl R => c ⟨⟨k, R⟩, a⟩ = true
    | Sum.inr (Sum.inl w) => wRel T w a
    | Sum.inr (Sum.inr w) => wRel T w a

/-! ### Reductions of the semantic maps in the standard model -/

private theorem sMap_std (x : ℕ) : @sMap L ℕ (standardMid c g T) x = x + 1 := rfl

private theorem numMap_std (m : ℕ) : @numMap L ℕ (standardMid c g T) m = m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (· + 1) ih

private theorem fMap_std (x : ℕ) :
    @fMap L ℕ (standardMid c g T) x = cond (queryCode c x) 1 0 := rfl

private theorem gMap_std (x : ℕ) : @gMap L ℕ (standardMid c g T) x = g x := rfl

/-! ### The tree tuple / path tuple extractions -/

private theorem treeTuple_firstIdx (n : ℕ) (σ : Fin n → Bool) (τ : Fin n → ℕ) (i : Fin n) :
    @treeTuple L ℕ (standardMid c g T) n σ τ (firstIdx n i) = cond (σ i) 1 0 := by
  have h : ((firstIdx n i : Fin (2 * n)) : ℕ) < n := i.2
  change (if h : ((firstIdx n i : Fin (2 * n)) : ℕ) < n
      then @numMap L ℕ (standardMid c g T) (cond (σ ⟨_, h⟩) 1 0)
      else @numMap L ℕ (standardMid c g T) (τ ⟨_, _⟩)) = _
  rw [dite_eq_left h, numMap_std]
  congr 1

private theorem treeTuple_secondIdx (n : ℕ) (σ : Fin n → Bool) (τ : Fin n → ℕ) (i : Fin n) :
    @treeTuple L ℕ (standardMid c g T) n σ τ (secondIdx n i) = τ i := by
  have h : ¬ ((secondIdx n i : Fin (2 * n)) : ℕ) < n := by
    change ¬ n + (i : ℕ) < n; omega
  change (if h : ((secondIdx n i : Fin (2 * n)) : ℕ) < n
      then @numMap L ℕ (standardMid c g T) (cond (σ ⟨_, h⟩) 1 0)
      else @numMap L ℕ (standardMid c g T) (τ ⟨((secondIdx n i : Fin (2 * n)) : ℕ) - n, _⟩)) = _
  rw [dite_eq_right h, numMap_std]
  congr 1
  apply Fin.ext
  change n + (i : ℕ) - n = (i : ℕ)
  omega

private theorem pathTuple_firstIdx (n : ℕ) (i : Fin n) :
    @pathTuple L ℕ (standardMid c g T) n (firstIdx n i) = cond (queryCode c (i : ℕ)) 1 0 := by
  have h : ((firstIdx n i : Fin (2 * n)) : ℕ) < n := i.2
  change (if ((firstIdx n i : Fin (2 * n)) : ℕ) < n
      then @fMap L ℕ (standardMid c g T) (@numMap L ℕ (standardMid c g T) _)
      else _) = _
  rw [ite_eq_left h, numMap_std, fMap_std]
  rfl

private theorem pathTuple_secondIdx (n : ℕ) (i : Fin n) :
    @pathTuple L ℕ (standardMid c g T) n (secondIdx n i) = g (i : ℕ) := by
  have h : ¬ ((secondIdx n i : Fin (2 * n)) : ℕ) < n := by
    change ¬ n + (i : ℕ) < n; omega
  change (if ((secondIdx n i : Fin (2 * n)) : ℕ) < n then _
      else @gMap L ℕ (standardMid c g T)
        (@numMap L ℕ (standardMid c g T) (((secondIdx n i : Fin (2 * n)) : ℕ) - n))) = _
  rw [ite_eq_right h, numMap_std, gMap_std]
  congr 1
  change n + (i : ℕ) - n = (i : ℕ)
  omega

/-! ### The standard model satisfies Θ -/

private theorem standardMid_models
    (hbranch : ∀ n : ℕ,
      ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g (i : ℕ))) ∈ T n) :
    @Sentenceω.Realize (MidLang L) (functionalTheta L T) ℕ (standardMid c g T) := by
  let := standardMid c g T
  rw [realize_functionalTheta]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- omegaAxioms
    rw [realize_omegaAxioms]
    refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x => ⟨x, ?_⟩⟩
    · rw [sMap_std, sMap_std] at hxy; omega
    · rw [sMap_std, numMap_std] at hx; omega
    · rw [numMap_std]
  · -- bitAxiom
    rw [realize_bitAxiom]
    intro x
    simp only [fMap_std, numMap_std]
    cases queryCode c x <;> simp
  · -- codeAxiom
    rw [realize_codeAxiom]
    intro q
    simp only [fMap_std, numMap_std]
    change (c q = true) ↔ cond (queryCode c (queryEmbedding q)) 1 0 = 1
    rw [queryCode_embedding]
    cases c q <;> simp
  · -- defaultAxiom
    rw [realize_defaultAxiom]
    intro n hn
    simp only [fMap_std, numMap_std, queryCode_of_notMem_range _ hn]
    rfl
  · -- treeDiagram
    rw [realize_treeDiagram]
    intro n σ τ
    change wRel T (WitnessRel.tree n) (treeTuple L ℕ n σ τ) ↔ _
    change ((fun i : Fin n => decodeBit (treeTuple L ℕ n σ τ (firstIdx n i))),
      (fun i : Fin n => treeTuple L ℕ n σ τ (secondIdx n i))) ∈ T n ↔ _
    rw [show (fun i : Fin n => decodeBit (treeTuple L ℕ n σ τ (firstIdx n i))) = σ from
        funext fun i => by rw [treeTuple_firstIdx, decodeBit_cond],
      show (fun i : Fin n => treeTuple L ℕ n σ τ (secondIdx n i)) = τ from
        funext fun i => treeTuple_secondIdx c g T n σ τ i]
  · -- pathAxiom
    rw [realize_pathAxiom]
    intro n
    change wRel T (WitnessRel.tree n) (pathTuple L ℕ n)
    change ((fun i : Fin n => decodeBit (pathTuple L ℕ n (firstIdx n i))),
      (fun i : Fin n => pathTuple L ℕ n (secondIdx n i))) ∈ T n
    rw [show (fun i : Fin n => decodeBit (pathTuple L ℕ n (firstIdx n i)))
          = (fun i : Fin n => queryCode c (i : ℕ)) from
        funext fun i => by rw [pathTuple_firstIdx, decodeBit_cond],
      show (fun i : Fin n => pathTuple L ℕ n (secondIdx n i))
          = (fun i : Fin n => g (i : ℕ)) from
        funext fun i => pathTuple_secondIdx c g T n i]
    exact hbranch n

/-! ### Lifting to `KLang` and graph-expanding -/

/-- `sideEmb` is an expansion of `standardK` onto `standardMid`. -/
private theorem sideEmb_isExpansionOn (side : PCSide) :
    @LHom.IsExpansionOn (MidLang L) (KLang L) (sideEmb L side) ℕ (standardMid c g T)
      (standardK c g T) := by
  let := standardMid c g T
  let := standardK c g T
  constructor
  · intro k f a
    cases side <;> cases f with
    | inl f' => exact isEmptyElim f'
    | inr w => rfl
  · intro k r a
    cases side <;> cases r with
    | inl R => rfl
    | inr w => rfl

private theorem standardK_models_pc (side : PCSide)
    (hbranch : ∀ n : ℕ,
      ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g (i : ℕ))) ∈ T n) :
    @Sentenceω.Realize (KLang L) (functionalPCSentence L side T) ℕ (standardK c g T) := by
  let := standardMid c g T
  let := standardK c g T
  have := sideEmb_isExpansionOn c g T side
  rw [functionalPCSentence]
  exact (BoundedFormulaω.realize_mapLanguage (sideEmb L side) (functionalTheta L T)
    (Empty.elim : Empty → ℕ) Fin.elim0).mpr (standardMid_models c g T hbranch)

/-! ### The forward code and its two properties -/

/-- The forward code: the encoded graph expansion of the standard `KLang` model (independent
of the side). -/
private noncomputable def forwardCode : StructureSpace (graphLanguage (KLang L)) :=
  letI := standardK c g T
  StructureSpaceOn.ofStructure (graphExpansion (KLang L) ℕ)

private theorem forwardCode_toStructure :
    (forwardCode c g T).toStructure = @graphExpansion (KLang L) ℕ (standardK c g T) := by
  apply Structure.ext
  · funext k f a; exact isEmptyElim f
  · funext k r a
    exact propext (StructureSpaceOn.toStructure_ofStructure
      (@graphExpansion (KLang L) ℕ (standardK c g T)) r a)

private theorem forwardCode_mem_modelsOf (side : PCSide)
    (hbranch : ∀ n : ℕ,
      ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g (i : ℕ))) ∈ T n) :
    forwardCode c g T ∈ ModelsOf (pcSentence L side T) := by
  let := standardK c g T
  change @Sentenceω.Realize (graphLanguage (KLang L)) (pcSentence L side T) ℕ
    (forwardCode c g T).toStructure
  rw [forwardCode_toStructure]
  exact graphExpansion_realizes_pcSentence side T (standardK_models_pc c g T side hbranch)

private theorem codeReduct_forwardCode :
    codeReduct (forwardCode c g T) = c := by
  let := standardK c g T
  funext q
  rw [Bool.eq_iff_iff]
  change (forwardCode c g T) ⟨⟨q.1.1, GraphRelation.base (Sum.inl q.1.2)⟩, q.2⟩ = true ↔ c q = true
  rw [← StructureSpace.relMap_toStructure (forwardCode c g T)
      (GraphRelation.base (Sum.inl q.1.2)) q.2,
    forwardCode_toStructure]
  -- `graphExpansion_relMap_base` is itself `Iff.rfl` and its structure instance no longer matches
  -- the one left by `forwardCode_toStructure`; the closing `Iff.rfl` covers it.
  exact Iff.rfl

end LopezStd

/-! ## The forward presentation -/

open LopezStd in
/-- **Forward gate** (`subset_pcClass`): if `T` characterizes `B` by branches (Unit 0), then
every code of `B` is the base reduct of a model of the PC sentence.  No `IsomorphismInvariant`. -/
theorem subset_pcClass {B : Set (StructureSpace L)} (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hT : ∀ c : StructureSpace L, c ∈ B ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T n) :
    B ⊆ codeReduct '' ModelsOf (pcSentence L side T) := by
  intro c hc
  obtain ⟨g, hbranch⟩ := (hT c).mp hc
  exact ⟨forwardCode c g T, forwardCode_mem_modelsOf c g T side hbranch,
    codeReduct_forwardCode c g T⟩

end FirstOrder.Language
