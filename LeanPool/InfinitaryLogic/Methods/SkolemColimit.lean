/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Skolem
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
/-!
# Iterated Skolemization: the staged language tower and its colimit `L^Sk`

The bespoke Ehrenfeucht–Mostowski term model needs a language in which *every* formula's
existential has a Skolem function (so the term-model truth lemma can witness nested `∃`'s). One
layer (`skolem₁ω`) is not closed under its own witness formulas, so we iterate:

* `L₀ = L`, `L_{k+1} = L_k.sum (skolem₁ω L_k)` (`skolemStage`);
* the colimit `L^Sk = colim_k L_k` (next) is **Skolem-complete**: an `L^Sk`-formula lives at some
  finite stage `k`, and its existential's Skolem function appears at stage `k+1`.

This is *ambient* infrastructure: the family `Γ*` consumed by the truth lemma is a **countable**
staged closure inside `L^Sk`. Caveat: the EM term model's `EMContext` also needs the **full atom
diagram** over `L^Sk`, which *does* enumerate its continuum-many symbols — the reason for the
countable family-restricted re-base (`localSkolem` and the `Llocal`/`Γlocal` tower in
`LocalSkolem.lean`/`LocalTower.lean`); `skolemColim` is retained as exploratory infrastructure.

For `L : Language.{0,0}` every stage stays in `Type 0` (`BoundedFormulaω Empty n` over a `{0,0}`
language is `Type 0`), so the tower has no universe blowup.
-/

namespace FirstOrder.Language

variable (L : Language.{0, 0})

/-- The **staged Skolem language tower**: `skolemStage L 0 = L` and
`skolemStage L (k+1) = (skolemStage L k).sum (skolem₁ω (skolemStage L k))`. Each step adjoins a
Skolem function symbol for every formula of the previous stage. -/
def skolemStage : ℕ → Language.{0, 0}
  | 0 => L
  | k + 1 => (skolemStage k).sum (skolem₁ω (skolemStage k))





/-- The stage-`k` → stage-`(k+1)` language embedding: the left injection of the sum. Its
`onFunction`/`onRelation` carry stage-`k` symbols into stage-`(k+1)`. -/
def skolemStageHom (k : ℕ) : skolemStage L k →ᴸ skolemStage L (k + 1) :=
  LHom.sumInl

/-! ### Sequential colimit of types -/

/-- The sequential colimit of a tower of types `F 0 → F 1 → …` along maps `φ`, as the quotient of
`Σ k, F k` identifying `⟨k, x⟩` with `⟨k+1, φ k x⟩`. -/
def DirectedColim (F : ℕ → Type) (φ : ∀ k, F k → F (k + 1)) : Type :=
  Quot (fun a b : Σ k, F k => b = ⟨a.1 + 1, φ a.1 a.2⟩)

/-- The canonical inclusion of stage `k` into the colimit. -/
def DirectedColim.incl {F : ℕ → Type} {φ : ∀ k, F k → F (k + 1)} (k : ℕ) (x : F k) :
    DirectedColim F φ :=
  Quot.mk _ ⟨k, x⟩

/-- Inclusions commute with the tower maps: a stage-`k` element and its image at stage `k+1` have
the same colimit class. -/
theorem DirectedColim.incl_step {F : ℕ → Type} {φ : ∀ k, F k → F (k + 1)} (k : ℕ) (x : F k) :
    DirectedColim.incl (φ := φ) (k + 1) (φ k x) = DirectedColim.incl (φ := φ) k x := by
  symm
  exact Quot.sound rfl

/-! ### The colimit language `L^Sk` and the stage cocone -/

/-- The **iterated-Skolemization colimit language** `L^Sk = colim_k (skolemStage L k)`. Its
function/relation symbols at each arity are the sequential colimits of the staged symbol types. An
`L^Sk`-symbol lives at a finite stage; in particular every `L^Sk`-formula's existential acquires a
Skolem function at the next stage, so `L^Sk` is Skolem-complete. -/
def skolemColim : Language.{0, 0} where
  Functions m :=
    DirectedColim (fun k => (skolemStage L k).Functions m) (fun k x => (skolemStageHom L k).onFunction x)
  Relations m :=
    DirectedColim (fun k => (skolemStage L k).Relations m) (fun k x => (skolemStageHom L k).onRelation x)

/-- The cocone: the inclusion of stage `k` into the colimit language `L^Sk`. On symbols it is the
colimit inclusion `DirectedColim.incl k`. -/
def skolemStageInclusion (k : ℕ) : skolemStage L k →ᴸ skolemColim L where
  onFunction {m} f :=
    DirectedColim.incl (F := fun j => (skolemStage L j).Functions m)
      (φ := fun j x => (skolemStageHom L j).onFunction x) k f
  onRelation {m} r :=
    DirectedColim.incl (F := fun j => (skolemStage L j).Relations m)
      (φ := fun j x => (skolemStageHom L j).onRelation x) k r

/-! ### Stage structures on a fixed model -/

section Structures

variable {M : Type} [L.Structure M] [Nonempty M]

/-- The **stage-`k` structure** on a fixed `L`-model `M`: stage `0` is `M`'s own `L`-structure, and
each successor stage adds the Hilbert-choice interpretation of the new Skolem symbols
(`skolem₁ωStructure`) on top of the previous stage, via the sum structure. -/
@[implicit_reducible] noncomputable def skolemStageStructure : (k : ℕ) → (skolemStage L k).Structure M
  | 0 => ‹L.Structure M›
  | k + 1 =>
      letI := skolemStageStructure k
      inferInstanceAs (((skolemStage L k).sum (skolem₁ω (skolemStage L k))).Structure M)

/-- Stage coherence (functions): a stage-`k` symbol pushed to stage `k+1` interprets the same way.
This is the cocone-compatibility witnessing the colimit interpretation is well-defined. -/
private theorem skolemStageStructure_funMap_succ {k m : ℕ}
    (f : (skolemStage L k).Functions m) (x : Fin m → M) :
    @Structure.funMap (skolemStage L (k + 1)) M (skolemStageStructure L (k + 1)) m
        ((skolemStageHom L k).onFunction f) x
      = @Structure.funMap (skolemStage L k) M (skolemStageStructure L k) m f x :=
  rfl

/-- Stage coherence (relations). -/
private theorem skolemStageStructure_relMap_succ {k m : ℕ}
    (r : (skolemStage L k).Relations m) (x : Fin m → M) :
    @Structure.RelMap (skolemStage L (k + 1)) M (skolemStageStructure L (k + 1)) m
        ((skolemStageHom L k).onRelation r) x
      = @Structure.RelMap (skolemStage L k) M (skolemStageStructure L k) m r x :=
  rfl

/-- The **colimit structure** `L^Sk`-structure on `M`: a colimit symbol is interpreted through any
stage representative, well-defined by the (definitional) stage coherence above. -/
@[implicit_reducible] noncomputable def skolemColimStructure : (skolemColim L).Structure M where
  funMap {m} f x :=
    Quot.lift
      (fun p => @Structure.funMap (skolemStage L p.1) M (skolemStageStructure L p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (skolemStageStructure_funMap_succ L a.2 x).symm) f
  RelMap {m} r x :=
    Quot.lift
      (fun p => @Structure.RelMap (skolemStage L p.1) M (skolemStageStructure L p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (skolemStageStructure_relMap_succ L a.2 x).symm) r





end Structures

end FirstOrder.Language
