/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMTruth
/-!
# The local Skolem-universality mixin

The `all` case of the local EM truth lemma (`LocalEMContext.truthLemmaStage`) consumes ONE special
property of the canonical source structure: every staged local-Skolem symbol has the universal
witness property (body true at the Skolem value ⟹ body true everywhere). Today that property is
discharged inline from `localColimStructure`'s Hilbert-choice interpretations — which pins the
truth lemma's source to the canonical structure. The schema route needs the same truth lemma over
`schemaTermStructure`, which is NOT definitionally canonical.

This file isolates the property as the assignment-level mixin `LocalSkolemUniversalForColim` —
independent of `J` and of terms, quantifying over a raw value tuple `xs` — and proves:

* `localSkolemUniversalForColim_canonical`: the canonical `localColimStructure` satisfies it
  (the current inline argument, via `localSkolem_funMap_spec`);
* `locSkWitness_universal_of_mixin`: the deep-term transport `locSkWitness_universal` consumed by
  the truth lemma's `all` case follows from the mixin alone — term evaluation supplies `xs`.

The follow-up refactor threads the mixin through `truthLemmaStage` (keeping the current theorems
as wrappers supplying the canonical proof) and discharges it for `schemaTermStructure` from the
restricted schema truth lemma.
-/

namespace FirstOrder.Language

/-- **The Skolem-universality mixin**: in a given `localColim` structure, every staged
local-Skolem symbol (keyed by a family universal `∀ψ ∈ Γlocal s₀ k`) has the universal witness
property at every value assignment: if the body holds at the symbol's value on `xs`, it holds at
every element. Independent of `J` and of terms — the truth lemma supplies `xs` by term
evaluation. -/
structure LocalSkolemUniversalForColim (s₀ : LocalStage) {M : Type}
    [(localColim s₀).Structure M] : Prop where
  universal : ∀ {k n : ℕ} {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
      (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
      (xs : Fin n → M),
    (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
        (Fin.snoc xs
          (Structure.funMap
            ((LlocalInclusion s₀ (k + 1)).onFunction
              (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)) xs)) →
      ∀ x : M,
        (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M) (Fin.snoc xs x)

/-- **The canonical structure satisfies the mixin**: `localColimStructure`'s Skolem symbols are
Hilbert-choice values, so `localSkolem_funMap_spec` supplies the universal property — the exact
inline argument of the current truth lemma, factored out. -/
theorem localSkolemUniversalForColim_canonical (s₀ : LocalStage) {M : Type}
    [s₀.Lang.Structure M] [Nonempty M] :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    LocalSkolemUniversalForColim s₀ (M := M) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  refine ⟨?_⟩
  intro k n ψ h xs
  let : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  simp only [realize_map_LlocalInclusion]
  intro hψw x
  by_contra hcon
  have hex : ∃ b, (ψ.not).Realize (Empty.elim : Empty → M) (Fin.snoc xs b) :=
    ⟨x, by rw [BoundedFormulaω.realize_not]; exact hcon⟩
  have hspec : (ψ.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc xs
        (Structure.funMap (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
          (skolemNeedSymbol h) xs)) :=
    localSkolem_funMap_spec (skolemNeedSymbol h) xs hex
  have hwval : Structure.funMap
        ((LlocalInclusion s₀ (k + 1)).onFunction
          (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)) xs
      = Structure.funMap (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
          (skolemNeedSymbol h) xs := rfl
  rw [hwval] at hψw
  rw [BoundedFormulaω.realize_not] at hspec
  exact hspec hψw

/-- **Deep-term transport from the mixin**: the exact Skolem input the truth lemma's `all` case
consumes (`locSkWitness_universal`), derived from the mixin alone — the deep interpretations of
the argument terms supply the value assignment, and the witness term's value is the symbol's
value on them by `locDeepInterp_func`. -/
theorem locSkWitness_universal_of_mixin (s₀ : LocalStage) (J : Type) [LinearOrder J]
    {M : Type} [(localColim s₀).Structure M]
    (hsk : LocalSkolemUniversalForColim s₀ (M := M))
    (a : ℕ → M) (d : ℕ) (S : Finset J) {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) :
    (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
        (Fin.snoc (fun i => locDeepInterp (localColim s₀) J a d S (ts i))
          (locDeepInterp (localColim s₀) J a d S (locSkWitnessTerm s₀ J h ts))) →
      ∀ x : M,
        (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
          (Fin.snoc (fun i => locDeepInterp (localColim s₀) J a d S (ts i)) x) := by
  intro hw
  have hwval : locDeepInterp (localColim s₀) J a d S (locSkWitnessTerm s₀ J h ts)
      = Structure.funMap
          ((LlocalInclusion s₀ (k + 1)).onFunction
            (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n))
          (fun i => locDeepInterp (localColim s₀) J a d S (ts i)) := by
    rw [locSkWitnessTerm, locDeepInterp_func]
    rfl
  apply hsk.universal h (fun i => locDeepInterp (localColim s₀) J a d S (ts i))
  simpa only [hwval] using hw

end FirstOrder.Language
