/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalTower
/-!
# The countable local colimit language `L_Γ` (`localColim`) and its cocone

The hinge of the L_Γ pivot. `LocalTower.lean` builds the mutually recursive tower
`Llocal s₀ k` / `Γlocal s₀ k` and proves every *stage* countable; this file assembles the tower
into an actual colimit language and shows countability **survives to the colimit** — the object
the EM term model must be re-based over (the full `skolemColim` is uncountable, so its atom
diagram cannot fit inside the countable family the tail extraction delivers).

Mirrors the `skolemColim` layer of `SkolemColimit.lean` exactly (same `DirectedColim` quotient,
same `Quot.lift` colimit structure, same definitional stage coherence), plus what `skolemColim`
cannot have: countability of the colimit symbol types and of the colimit image `ΓlocalColim` of
the staged families.

* `localColim s₀` — the colimit language `L_Γ = colim_k (Llocal s₀ k)`.
* `LlocalInclusion s₀ k` — the cocone `Llocal s₀ k →ᴸ localColim s₀`, with symbol-level
  cocone-compatibility (`LlocalInclusion_onFunction_step`/`_onRelation_step`).
* `localColim_fun_countable` / `localColim_rel_countable` — **the payoff**: the colimit language
  is countable (via `DirectedColim.countable`, a sequential colimit of countable types).
* `localStageStructure` / `localColimStructure` / `LlocalInclusion_isExpansionOn` /
  `realize_map_LlocalInclusion` — the semantic-transport API on a fixed `s₀.Lang`-model `M`.
* `toLocalColimFormula` / `ΓlocalColim` / `ΓlocalColim_countable` — the (countable) colimit image
  of the staged families, the family the truth lemma will consume.
* Formula-level cocone coherence for the EM rebase: `LlocalInclusion_comp_LlocalHom`,
  `toLocalColimFormula_step`, `toLocalColimFormula_lift_mem_ΓlocalColim`, and
  `localSkolemWitnessFormula_mem_ΓlocalColim` (the `skolemNeed` witness body of every family
  universal lands in `ΓlocalColim`).

Next chunks (not here): the local atom/deForm seed and its countability, then the `EMContext`
re-base over `localColim`.
-/

namespace FirstOrder.Language

/-- A sequential colimit of countable types is countable: the colimit is a quotient of the
countable total space `Σ k, F k`. (Generic companion to `DirectedColim`; the reason the *local*
colimit stays countable while `skolemColim` does not.) -/
theorem DirectedColim.countable {F : ℕ → Type} {φ : ∀ k, F k → F (k + 1)}
    (h : ∀ k, Countable (F k)) : Countable (DirectedColim F φ) := by
  have : ∀ k, Countable (F k) := h
  exact inferInstanceAs (Countable (Quot _))

/-- `mapLanguage` composes: transporting along `g` then `h` is transporting along `h.comp g`.
(A Mathlib-gap-style generic lemma; belongs in `Lomega1omega/Operations.lean` eventually —
localized here, where the cocone coherence needs it, to keep the default build path untouched.) -/
theorem BoundedFormulaω.mapLanguage_mapLanguage {L₁ L₂ L₃ : Language} (g : L₁ →ᴸ L₂)
    (h : L₂ →ᴸ L₃) {α : Type*} {n : ℕ} (φ : L₁.BoundedFormulaω α n) :
    (φ.mapLanguage g).mapLanguage h = φ.mapLanguage (h.comp g) := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormulaω.mapLanguage, LHom.comp_onTerm, Function.comp_apply]
  | rel R ts =>
    simp only [BoundedFormulaω.mapLanguage, LHom.comp_onTerm, Function.comp_apply]
    rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.mapLanguage, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.mapLanguage, ih]
  | iSup φs ih => simp only [BoundedFormulaω.mapLanguage]; exact congrArg _ (funext ih)
  | iInf φs ih => simp only [BoundedFormulaω.mapLanguage]; exact congrArg _ (funext ih)

variable (s₀ : LocalStage)

/-- Per-arity function-symbol countability at each stage (the fibre of the stagewise all-arity
certificate `Llocal_fun_countable`). -/
private theorem Llocal_functions_countable (k m : ℕ) : Countable ((Llocal s₀ k).Functions m) := by
  have := Llocal_fun_countable s₀ k
  exact (sigma_mk_injective (i := m)).countable

/-- Per-arity relation-symbol countability at each stage. -/
private theorem Llocal_relations_countable (k m : ℕ) : Countable ((Llocal s₀ k).Relations m) := by
  have := Llocal_rel_countable s₀ k
  exact (sigma_mk_injective (i := m)).countable

/-! ### The colimit language `L_Γ` and the stage cocone -/

/-- The **local colimit language** `L_Γ = colim_k (Llocal s₀ k)`: function/relation symbols at
each arity are the sequential colimits of the staged symbol types along `LlocalHom`. Every
`L_Γ`-symbol lives at a finite stage; in particular every family formula's existential acquires
its local Skolem function at the next stage, so `L_Γ` is Skolem-complete *for the family*. -/
def localColim : Language.{0, 0} where
  Functions m :=
    DirectedColim (fun k => (Llocal s₀ k).Functions m)
      (fun k x => (LlocalHom s₀ k).onFunction x)
  Relations m :=
    DirectedColim (fun k => (Llocal s₀ k).Relations m)
      (fun k x => (LlocalHom s₀ k).onRelation x)

/-- The cocone: the inclusion of stage `k` into the local colimit language `L_Γ`. On symbols it
is the colimit inclusion `DirectedColim.incl k`. -/
def LlocalInclusion (k : ℕ) : Llocal s₀ k →ᴸ localColim s₀ where
  onFunction {m} f :=
    DirectedColim.incl (F := fun j => (Llocal s₀ j).Functions m)
      (φ := fun j x => (LlocalHom s₀ j).onFunction x) k f
  onRelation {m} r :=
    DirectedColim.incl (F := fun j => (Llocal s₀ j).Relations m)
      (φ := fun j x => (LlocalHom s₀ j).onRelation x) k r

/-- Cocone compatibility on function symbols: pushing a stage-`k` symbol one stage up and then
into the colimit is the same as including it directly. -/
private theorem LlocalInclusion_onFunction_step {k m : ℕ} (f : (Llocal s₀ k).Functions m) :
    (LlocalInclusion s₀ (k + 1)).onFunction ((LlocalHom s₀ k).onFunction f)
      = (LlocalInclusion s₀ k).onFunction f :=
  DirectedColim.incl_step (F := fun j => (Llocal s₀ j).Functions m)
    (φ := fun j x => (LlocalHom s₀ j).onFunction x) k f

/-- Cocone compatibility on relation symbols. -/
private theorem LlocalInclusion_onRelation_step {k m : ℕ} (r : (Llocal s₀ k).Relations m) :
    (LlocalInclusion s₀ (k + 1)).onRelation ((LlocalHom s₀ k).onRelation r)
      = (LlocalInclusion s₀ k).onRelation r :=
  DirectedColim.incl_step (F := fun j => (Llocal s₀ j).Relations m)
    (φ := fun j x => (LlocalHom s₀ j).onRelation x) k r

/-- **Cocone compatibility as an `LHom` equation**: including stage `k` via stage `k+1` is the
direct inclusion. The formula-level coherence (`toLocalColimFormula_step`) is this plus
`mapLanguage` composition. -/
theorem LlocalInclusion_comp_LlocalHom (k : ℕ) :
    (LlocalInclusion s₀ (k + 1)).comp (LlocalHom s₀ k) = LlocalInclusion s₀ k :=
  LHom.funext
    (funext fun _m => funext fun f => LlocalInclusion_onFunction_step s₀ f)
    (funext fun _m => funext fun r => LlocalInclusion_onRelation_step s₀ r)

/-! ### Countability of the colimit language — the payoff of the pivot -/

/-- Per-arity: the colimit function symbols are countable. -/
private theorem localColim_functions_countable (m : ℕ) : Countable ((localColim s₀).Functions m) :=
  DirectedColim.countable (F := fun k => (Llocal s₀ k).Functions m)
    (φ := fun k x => (LlocalHom s₀ k).onFunction x)
    (fun k => Llocal_functions_countable s₀ k m)

/-- Per-arity: the colimit relation symbols are countable. -/
private theorem localColim_relations_countable (m : ℕ) : Countable ((localColim s₀).Relations m) :=
  DirectedColim.countable (F := fun k => (Llocal s₀ k).Relations m)
    (φ := fun k x => (LlocalHom s₀ k).onRelation x)
    (fun k => Llocal_relations_countable s₀ k m)

/-- **The local colimit language has countably many function symbols** — in contrast to
`skolemColim`, whose function-symbol type has the cardinality of the continuum. -/
theorem localColim_fun_countable : Countable (Σ n, (localColim s₀).Functions n) := by
  have : ∀ n, Countable ((localColim s₀).Functions n) := localColim_functions_countable s₀
  infer_instance

/-- **The local colimit language has countably many relation symbols.** -/
theorem localColim_rel_countable : Countable (Σ n, (localColim s₀).Relations n) := by
  have : ∀ n, Countable ((localColim s₀).Relations n) := localColim_relations_countable s₀
  infer_instance

/-! ### Stage structures on a fixed model and the colimit structure -/

section Structures

variable {M : Type} [s₀.Lang.Structure M] [Nonempty M]

/-- The **stage-`k` structure** on a fixed `s₀.Lang`-model `M`: stage `0` is `M`'s own structure,
and each successor stage adds the Hilbert-choice interpretation of the new *local* Skolem symbols
(`localSkolemStructure`) on top of the previous stage, via the sum structure. -/
@[implicit_reducible] noncomputable def localStageStructure :
    (k : ℕ) → (Llocal s₀ k).Structure M
  | 0 => ‹s₀.Lang.Structure M›
  | k + 1 =>
      letI := localStageStructure k
      inferInstanceAs
        (((Llocal s₀ k).sum
          (localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))).Structure M)

/-- Stage coherence (functions): a stage-`k` symbol pushed to stage `k+1` interprets the same
way. This is the cocone-compatibility witnessing the colimit interpretation is well-defined. -/
private theorem localStageStructure_funMap_succ {k m : ℕ}
    (f : (Llocal s₀ k).Functions m) (x : Fin m → M) :
    @Structure.funMap (Llocal s₀ (k + 1)) M (localStageStructure s₀ (k + 1)) m
        ((LlocalHom s₀ k).onFunction f) x
      = @Structure.funMap (Llocal s₀ k) M (localStageStructure s₀ k) m f x :=
  rfl

/-- Stage coherence (relations). -/
private theorem localStageStructure_relMap_succ {k m : ℕ}
    (r : (Llocal s₀ k).Relations m) (x : Fin m → M) :
    @Structure.RelMap (Llocal s₀ (k + 1)) M (localStageStructure s₀ (k + 1)) m
        ((LlocalHom s₀ k).onRelation r) x
      = @Structure.RelMap (Llocal s₀ k) M (localStageStructure s₀ k) m r x :=
  rfl

/-- The **colimit structure**: an `L_Γ`-symbol is interpreted through any stage representative,
well-defined by the (definitional) stage coherence above. -/
@[implicit_reducible] noncomputable def localColimStructure : (localColim s₀).Structure M where
  funMap {m} f x :=
    Quot.lift
      (fun p => @Structure.funMap (Llocal s₀ p.1) M (localStageStructure s₀ p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (localStageStructure_funMap_succ s₀ a.2 x).symm) f
  RelMap {m} r x :=
    Quot.lift
      (fun p => @Structure.RelMap (Llocal s₀ p.1) M (localStageStructure s₀ p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (localStageStructure_relMap_succ s₀ a.2 x).symm) r

/-- The stage inclusion is an **expansion**: the colimit structure restricts to the stage
structure along `LlocalInclusion` (the colimit `funMap`/`RelMap` on an included symbol computes —
by `rfl` — to the stage interpretation). -/
private theorem LlocalInclusion_isExpansionOn (k : ℕ) :
    letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
    letI : (localColim s₀).Structure M := localColimStructure s₀
    (LlocalInclusion s₀ k).IsExpansionOn M :=
  letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  letI : (localColim s₀).Structure M := localColimStructure s₀
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Semantic preservation by stage inclusion**: transporting a stage-`k` formula into `L_Γ`
along `LlocalInclusion` preserves its realization in `M`. Immediate from `realize_mapLanguage`
and the expansion property above. -/
theorem realize_map_LlocalInclusion (k : ℕ) {n : ℕ}
    (φ : (Llocal s₀ k).BoundedFormulaω Empty n) (v : Empty → M) (xs : Fin n → M) :
    letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
    letI : (localColim s₀).Structure M := localColimStructure s₀
    (φ.mapLanguage (LlocalInclusion s₀ k)).Realize v xs ↔ φ.Realize v xs := by
  let : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  let : (localColim s₀).Structure M := localColimStructure s₀
  have := LlocalInclusion_isExpansionOn (s₀ := s₀) (M := M) k
  exact BoundedFormulaω.realize_mapLanguage (LlocalInclusion s₀ k) φ v xs

end Structures

/-! ### The colimit image of the staged families -/

/-- Transport an arity-tagged stage-`k` formula into the local colimit language along the
cocone inclusion. -/
def toLocalColimFormula (k : ℕ) (p : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) :
    Σ n, (localColim s₀).BoundedFormulaω Empty n :=
  ⟨p.1, p.2.mapLanguage (LlocalInclusion s₀ k)⟩

/-- The **colimit family** `Γ_Γ ⊆ L_Γ`-formulas: the union over all stages of the colimit images
of the staged families `Γlocal s₀ k`. This is the family over which the re-based EM term model's
truth lemma will run. -/
def ΓlocalColim : Set (Σ n, (localColim s₀).BoundedFormulaω Empty n) :=
  ⋃ k, toLocalColimFormula s₀ k '' Γlocal s₀ k

/-- Stage membership transports into the colimit family. -/
theorem toLocalColimFormula_mem_ΓlocalColim {k : ℕ}
    {p : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n} (hp : p ∈ Γlocal s₀ k) :
    toLocalColimFormula s₀ k p ∈ ΓlocalColim s₀ :=
  Set.mem_iUnion.mpr ⟨k, Set.mem_image_of_mem _ hp⟩

/-- **The colimit family is countable**: a countable union of images of the (stagewise countable)
families. Together with `localColim_fun_countable`/`_rel_countable`, this says the local Skolem
construction really does produce a countable language *and* family in the colimit — the exact
size interface the tail extraction (`MorleyHanfExtractionTail`) can serve. -/
theorem ΓlocalColim_countable : (ΓlocalColim s₀).Countable :=
  Set.countable_iUnion fun k => (Γlocal_countable s₀ k).image _

/-! ### Formula-level cocone coherence

The wrappers the EM rebase will consume, so its proofs never touch raw `mapLanguage` equalities. -/

end FirstOrder.Language
