/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.Hanf
import LeanPool.InfinitaryLogic.Methods.EM.FragmentAdapter
import LeanPool.InfinitaryLogic.Methods.EM.TailAdapter
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Aleph
/-!
# Morley-Hanf Transfer Hypothesis (Conditional)

This file isolates the deep combinatorial transfer hypothesis needed for the
Morley-Hanf theorem. The hypothesis encapsulates Erdős-Rado extraction +
Ehrenfeucht-Mostowski stretching, which require infrastructure not currently
formalized in Lean or Mathlib.

## Conditional Status

`MorleyHanfTransfer` is a `Prop`-valued definition, not a theorem. The
conditional theorem `morley_hanf_of_transfer` takes it as a hypothesis.
Both are placed in `Conditional/` to make the external dependency visible.

## References

- [Mar16], §5
- [KK04], §1.6
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-! ### Residual extraction hypothesis + proved bridge

Phase 2 refactor: split `MorleyHanfTransfer` into a source-side extraction
hypothesis (still conditional) plus a compactness oracle, joined by a proved
bridge theorem. The extraction is the genuine combinatorial residual
(Erdős–Rado + pairwise-distinct stable-type extraction); the stretching
side is now fully formalized in `Methods/EM/FragmentAdapter.lean`.

Universe note: the bridge uses `L : Language.{0, 0}` so that the target
linear order `J : Type` (produced via `(Cardinal.ord κ).ToType` at
`Cardinal.{0}`) matches the universe expected by the stretching theorems
(which take `{J : Type u}` tied to `L`'s first universe). -/

section RestrictedBridge

variable {L' : Language.{0, 0}} [Countable (Σ l, L'.Relations l)]

/-! ### Tail-weakened residual

The interface-refinement audit (2026-06-10) showed that the EM stretching pipeline consumes
source-side indiscernibility only through the finite-satisfiability lemma, where the
interpreting tuple is freely chosen — so per-formula **tail** indiscernibility suffices
(see `Methods/EM/TailAdapter.lean`). The tail residual below matches what classical
Erdős–Rado extraction actually produces in the source model (per-arity cutoffs, no full
simultaneity across arities), and is implied by the original `MorleyHanfExtraction`. -/

/-- **The honest residual consumed by the tail Morley–Hanf bridge**: realizability of the
tail-template theory of the **Morley seed** `{φ, x₀ ≠ x₁}` only, carrying the source facts the
bridge actually has — `φ` holds in the source model `M` of size `≥ ℶ_{ω₁}`, and the extracted
sequence is pairwise distinct and tail-indiscernible on the seed.

The `|M| ≥ ℶ_ω₁` premise is essential for the statement to be true-shaped: the seed's template
theory is `{φ} ∪ {distinct constants}`, so realizability over a size-`κ` order is "`φ` has a
model of size `≥ κ`" — without the cardinality premise this would assert that every `φ` with an
infinite model has arbitrarily large models, false for Scott sentences of bounded Hanf number.
Unlike the broad `TailTemplateRealizable` (false-shaped: see its docstring), the seed family has
no countable connectives beyond those inside `φ` itself, and the classical proof is the
Ehrenfeucht–Mostowski / Skolem-hull construction over `J`.

**Now PROVED** (`morleySeedTailTemplateRealizable_holds`,
`Conditional/MorleyHanfSchemaDischarge.lean`) via the schema-completion construction — in fact
without consuming the sequence's tail indiscernibility. Kept as a named `Prop` because the
bridge theorems below are stated against it. -/
def MorleySeedTailTemplateRealizable : Prop :=
  ∀ (φ : L'.Sentenceω) (M : Type) [L'.Structure M] (a : ℕ → M) (J : Type) [LinearOrder J],
    Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    Sentenceω.Realize φ M →
    (∀ i j : ℕ, i ≠ j → a i ≠ a j) →
    IsLomega1omegaIndiscernibleOnTail a (Set.range (morleySeed φ)) →
    ∃ (N : Type) (_ : L'[[J]].Structure N),
      Theoryω.Model
        ((tailTemplateOfSeq a : Lomega1omegaTemplate L').templateTheoryOfSeq (morleySeed φ) J) N

omit [Countable (Σ l, L'.Relations l)] in
/-- **Morley–Hanf via seed-template realizability alone — no extraction** (the definitive
bridge). `morleySeed_indiscernibleOn` makes any extraction hypothesis unnecessary: an injective
`ℕ`-sequence of the (infinite) source is already FULLY indiscernible on the Morley seed — the
arity-`0` members ignore their tuples and the disequality is absolute for injective sequences —
so `Infinite.natEmbedding` supplies the sequence directly. No countable Ramsey, no Erdős–Rado.
The EM template theory of the seed is realized via `MorleySeedTailTemplateRealizable`, and the
model-form stretching of `Methods/EM/TailAdapter.lean` reads off `φ`-preservation and size. -/
private theorem hasArbLargeModels_of_seed_realizability
    (hRealize : MorleySeedTailTemplateRealizable (L' := L'))
    (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ := by
  classical
  obtain ⟨M, instM, hRealizeM, hSizeM⟩ := hφ
  let s : ℕ → Σ n, L'.BoundedFormulaω Empty n := morleySeed φ
  have hs0 : s 0 = ⟨0, φ⟩ := rfl
  have hs1 : s 1 = ⟨2, disEqFormula⟩ := rfl
  have : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSizeM
  set a : ℕ → M := fun n => (Infinite.natEmbedding M) n with ha_def
  have hPairwise : ∀ i j : ℕ, i ≠ j → a i ≠ a j :=
    fun i j hij h => hij ((Infinite.natEmbedding M).injective h)
  have hIndisc : IsLomega1omegaIndiscernibleOnTail (L := L') a (Set.range s) :=
    IsLomega1omegaIndiscernibleOn.isLomega1omegaIndiscernibleOnTail
      (morleySeed_indiscernibleOn φ hPairwise)
  intro κ
  let J : Type := (Cardinal.ord κ).ToType
  have : LinearOrder J := linearOrder_toType _
  have hJ_card : Cardinal.mk J = κ := Cardinal.mk_ord_toType κ
  obtain ⟨N, instN, b, hSeq⟩ :=
    IsLomega1omegaIndiscernibleOnTail.stretch_restricted_sequence_of_model (J := J)
      s (hRealize φ M a J hSizeM hRealizeM hPairwise hIndisc)
  let : L'.Structure N := (L'.lhomWithConstants J).reduct N
  refine ⟨N, inferInstance, ?_, ?_⟩
  · -- Sentence preservation
    have hSeq_at_0 := hSeq 0
    rw [hs0] at hSeq_at_0
    dsimp only at hSeq_at_0
    let t0 : Fin 0 ↪o J :=
      ⟨⟨Fin.elim0, fun ⟨_, hk⟩ => absurd hk (Nat.not_lt_zero _)⟩, fun {x} => x.elim0⟩
    have hkey := hSeq_at_0 t0
    have hbt0 : (b ∘ t0 : Fin 0 → N) = Fin.elim0 := funext fun k => k.elim0
    rw [hbt0] at hkey
    have hTmpl : (tailTemplateOfSeq a : Lomega1omegaTemplate L').truth φ := by
      refine ⟨0, fun u _ _ => ?_⟩
      have hu0 : (a ∘ u : Fin 0 → M) = Fin.elim0 := funext fun k => k.elim0
      rw [hu0]
      exact hRealizeM
    change Sentenceω.Realize φ N
    exact hkey.mpr hTmpl
  · -- Injectivity ⇒ #N ≥ #J = κ
    have hDisTruth : (tailTemplateOfSeq a : Lomega1omegaTemplate L').truth disEqFormula := by
      refine ⟨0, fun u hu _ => ?_⟩
      simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
        Term.realize_var]
      intro heq
      have h01 : u 0 ≠ u 1 := ne_of_lt (hu (show (0 : Fin 2) < 1 by decide))
      exact hPairwise (u 0) (u 1) h01 (by simpa using heq)
    have hSeq_at_1 := hSeq 1
    rw [hs1] at hSeq_at_1
    dsimp only at hSeq_at_1
    have hbInj : Function.Injective b := by
      have helper : ∀ {j₀ j₁ : J}, j₀ < j₁ → b j₀ = b j₁ → False := by
        intro j₀ j₁ hlt heq
        have hmono : StrictMono (![j₀, j₁] : Fin 2 → J) := by
          intro p q hpq
          match p, q, hpq with
          | ⟨0, _⟩, ⟨1, _⟩, _ => exact hlt
          | ⟨0, _⟩, ⟨0, _⟩, h => exact absurd h (lt_irrefl _)
          | ⟨1, _⟩, ⟨1, _⟩, h => exact absurd h (lt_irrefl _)
          | ⟨1, _⟩, ⟨0, _⟩, h =>
            have hval : (1 : ℕ) < 0 := h
            exact absurd hval (by omega)
        set t : Fin 2 ↪o J := OrderEmbedding.ofStrictMono ![j₀, j₁] hmono with ht_def
        have hrealize := (hSeq_at_1 t).mpr hDisTruth
        simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
          Term.realize_var] at hrealize
        apply hrealize
        change b (t 0) = b (t 1)
        have h0 : t 0 = j₀ := by simp [ht_def, OrderEmbedding.coe_ofStrictMono]
        have h1 : t 1 = j₁ := by simp [ht_def, OrderEmbedding.coe_ofStrictMono]
        rw [h0, h1]
        exact heq
      intro j j' hbjj'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact helper hlt hbjj'
      · exact helper hlt hbjj'.symm
    calc Cardinal.mk N ≥ Cardinal.mk J := Cardinal.mk_le_of_injective hbInj
      _ = κ := hJ_card

/-! ### Combinatorial residual via `IsIndiscernibleOnSet` -/

end RestrictedBridge

/-! ### Pure partition-calculus residual -/

/-! ### Compact-only Morley–Hanf headlines (LEGACY)

These wrappers collapse the proved reduction chain
(`hasArbLargeModels_of_restricted_extraction` ∘
`morleyHanfExtraction_of_indiscernibleSequence` ∘
`indiscernibleSequence_of_pureColoring`) into a single theorem parameterized
by the pure combinatorial hypothesis and a compactness oracle.

**Legacy-shaped**: the compactness oracle is no longer needed — the local EM
route discharges the model-existence side, so `morley_hanf_of_pureColoring`
(`Methods/LocalEMOmegaResidual.lean`) derives the Hanf bound from
`PureColoringHypothesis` alone, and `morley_hanf_of_finiteArityErdosRado`
from the ER-facing residual `FiniteArityErdosRadoOmega1 ℶ_1` (via
`pureColoringHypothesis_of_finiteArityErdosRadoOmega1` above). Prefer those
endpoints; the wrappers below are retained for compatibility. -/

/-! ### Realizability-only Morley–Hanf via the proved tail extraction

The tail-weakened source extraction is now **formalized** (`morleyHanfExtractionTail_holds`,
proved from `infinite_ramsey_nat_family` — countable Ramsey on `ℕ`, not an `ℶ_{ω₁}` Erdős–Rado
schedule). Composing it with `hasArbLargeModels_of_tail_realizability` discharges the
combinatorial hypothesis entirely: the theorems below take **only** the honest residual
`MorleySeedTailTemplateRealizable` (realizability of the EM tail-template theory of the Morley
seed `{φ, x₀ ≠ x₁}`, with the source facts).

**That residual is itself now PROVED** (`morleySeedTailTemplateRealizable_holds`,
`Conditional/MorleyHanfSchemaDischarge.lean` — the schema-completion construction), so the
unconditional endpoint `morley_hanf` there has no hypotheses at all. The `hRealize`-relative
forms below remain the transparent intermediates; the `*_compact` wrappers are retained as
legacy — their oracle is strictly stronger than needed. -/

/-- **Morley–Hanf bound (realizability-only)**: `ℶ_ω₁` is a Hanf bound for every Lω₁ω sentence,
assuming only `MorleySeedTailTemplateRealizable` — which is itself proved
(`morleySeedTailTemplateRealizable_holds`); see `morley_hanf` in
`Conditional/MorleyHanfSchemaDischarge.lean` for the hypothesis-free endpoint. Consumes no
extraction: the route is `hasArbLargeModels_of_seed_realizability`. -/
theorem morley_hanf_of_seed_realizable
    {L' : Language.{0, 0}}
    (hRealize : MorleySeedTailTemplateRealizable (L' := L'))
    (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  intro ⟨M, hStr, hRealizeφ, hSize⟩
  exact hasArbLargeModels_of_seed_realizability hRealize φ ⟨M, hStr, hRealizeφ, hSize⟩

end Language

end FirstOrder

-- lean4:disprove-begin txn=e12264ecbafc cycle=1 role=artifact decl=T_counterexample
namespace FirstOrder.Language

namespace HeightCex

/-- The counterexample language: unary predicates `Pᵢ` indexed by `i : ℕ`, nothing else. -/
def Lang : Language.{0, 0} where
  Functions _ := Empty
  Relations n := match n with
    | 1 => ℕ
    | _ => Empty

/-- The carrier: a set of size exactly `ℶ_{ω₁}`. -/
def Carrier : Type := (Cardinal.beth (Ordinal.omega 1)).ord.ToType

private theorem mk_Carrier : Cardinal.mk Carrier = Cardinal.beth (Ordinal.omega 1) :=
  Cardinal.mk_ord_toType _

instance : Infinite Carrier :=
  Cardinal.infinite_iff.mpr (mk_Carrier ▸ Cardinal.aleph0_le_beth _)

/-- A copy of `ℕ` inside the carrier, along which heights are unbounded. -/
private noncomputable def emb : ℕ ↪ Carrier := Infinite.natEmbedding Carrier

/-- The height of a carrier element: the inverse of `emb` on its range, arbitrary elsewhere. -/
noncomputable def hgt (x : Carrier) : ℕ := Function.invFun emb x

/-- The unary atom `Pᵢ x₀`. -/
def P (i : ℕ) : Lang.BoundedFormulaω Empty 1 :=
  BoundedFormulaω.rel (n := 1) (show Lang.Relations 1 from i)
    (fun _ => Term.var (Sum.inr (0 : Fin 1)))

/-- The countable conjunction `⋀ᵢ Pᵢ x₀`. -/
private def conj : Lang.BoundedFormulaω Empty 1 := BoundedFormulaω.iInf P

/-- The seed: `⋀ᵢ Pᵢ` first, then every `Pᵢ`. -/
def seed : ℕ → Σ n, Lang.BoundedFormulaω Empty n := fun k =>
  match k with
  | 0 => ⟨1, conj⟩
  | i + 1 => ⟨1, P i⟩

/-- The sequence of unboundedly growing height. -/
noncomputable def a : ℕ → Carrier := fun n => emb n

end HeightCex

end FirstOrder.Language
-- lean4:disprove-end txn=e12264ecbafc
