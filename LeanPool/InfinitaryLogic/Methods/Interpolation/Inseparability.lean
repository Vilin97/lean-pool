/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.ConstantElimination
/-!
# Support-parameterized inseparability and the C7 closure step (issue #8 kernel gate)

`InsepAt F R A Γ Δ`: the pair `(Γ, Δ)` of `L[[ℕ]]`-sentence sets admits no separator `σ` whose
base symbols lie in `(F, R)` (the shared vocabulary), whose constant support lies in the finite
allowed set `A`, with `Γ ⊨ σ` and `Δ ⊨ ¬σ`. Parameterizing by the allowed support `A` is what
makes the quantifier (C7) closure step compositional and the root case (`A = ∅`) reachable
(`docs/craig-audit.md` §7).

This file is the **kernel gate** (audit §6a.6): it certifies that the constant-abstraction
machinery composes into the exact C7 closure argument — a separator of the witness-instantiated
pair at support `insert c A` abstracts, via the acceptance lemmas, to a separator of the
existential pair at support `A`. The full inseparability consistency-property instance and the
Henkin model existence belong to tranche 2.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- **Support-parameterized inseparability**: no separator with base symbols in `(F, R)`,
constant support in `A`, entailed by `Γ` and refuted on `Δ`. -/
def InsepAt (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n))
    (A : Finset ℕ) (Γ Δ : Set L[[ℕ]].Sentenceω) : Prop :=
  ¬ ∃ σ : L[[ℕ]].Sentenceω,
    σ.baseFunctionsIn ⊆ F ∧ σ.baseRelationsIn ⊆ R ∧
    sentenceJConsts (L' := L) (J := ℕ) σ ⊆ (↑A : Set ℕ) ∧
    Theoryω.Entails Γ σ ∧ Theoryω.Entails Δ σ.not

variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
  {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- **The C7 closure step** (separator abstraction): if the existential pair is inseparable at
support `A`, then the witness-instantiated pair is inseparable at support `insert c A`, for a
constant `c` fresh for both sides. This is the contrapositive of the acceptance pair: a
separator of `(Γ ∪ {φ(c)}, Δ)` at `insert c A` abstracts to the separator `genEx c σ` of
`(Γ ∪ {∃x φ}, Δ)` at `A`. -/
theorem insepAt_witness_of_insepAt_genEx (c : ℕ) (φc : L[[ℕ]].Sentenceω)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : InsepAt F R A (insert (genEx c φc) Γ) Δ) :
    InsepAt F R (insert c A) (insert φc Γ) Δ := by
  rintro ⟨σ, hbf, hbr, hsupp, hΓσ, hΔσ⟩
  refine h ⟨genEx c σ, (baseFunctionsIn_genEx_subset c σ).trans hbf, ?_, ?_, ?_, ?_⟩
  · rw [baseRelationsIn_genEx]; exact hbr
  · intro k hk
    have hk1 : k ∈ sentenceJConsts (L' := L) (J := ℕ) σ := sentenceJConsts_genEx_subset c σ hk
    have hk2 : k ≠ c := fun heq => notMem_sentenceJConsts_genEx c σ (heq ▸ hk)
    have hmem := hsupp hk1
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hmem
    exact hmem.resolve_left hk2
  · exact entails_genEx_of_entails hcΓ hΓσ
  · exact entails_not_genEx_of_entails_not hcΔ hΔσ


end FirstOrder.Language
