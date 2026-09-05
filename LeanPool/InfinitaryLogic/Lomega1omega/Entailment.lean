/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
/-!
# Semantic entailment for `L_{ω₁ω}` (issue #8 kernel step 1)

The frozen entailment convention of the Craig interpolation arc (`docs/craig-audit.md` §2):
set-level entailment is the primitive, carriers are `Type 0`, and models are **nonempty**
(standard model theory; forced here because the fresh-constant elimination arguments expand a
base structure by constant interpretations, which no empty carrier admits).

`Language.{0,0}` throughout, per the arc's D2 freeze.
-/

namespace FirstOrder

namespace Language

variable {L : Language.{0, 0}}

/-- **Semantic entailment from a theory** (the primitive form): every nonempty `Type 0` model
of `T` realizes `ψ`. -/
def Theoryω.Entails (T : L.Theoryω) (ψ : L.Sentenceω) : Prop :=
  ∀ (M : Type) [L.Structure M] [Nonempty M], T.Model M → Sentenceω.Realize ψ M

/-- **Semantic entailment between sentences** — the headline convention, derived from the
set-level primitive. -/
def Sentenceω.Entails (φ ψ : L.Sentenceω) : Prop :=
  Theoryω.Entails {φ} ψ

namespace Theoryω

variable {T T' : L.Theoryω} {φ ψ χ : L.Sentenceω}

theorem entails_of_mem (h : φ ∈ T) : T.Entails φ :=
  fun _M _ _ hM => hM φ h

/-- Entailment is monotone in the theory. -/
theorem Entails.mono (h : T.Entails φ) (hT : T ⊆ T') : T'.Entails φ :=
  fun _M _ _ hM => h _M (hM.mono hT)

/-- Cut: an entailed sentence can be added to the premises without changing entailments. -/
theorem Entails.cut (hφ : T.Entails φ) (hψ : (insert φ T).Entails ψ) : T.Entails ψ :=
  fun M _ _ hM => hψ M fun χ hχ => by
    rcases Set.mem_insert_iff.mp hχ with rfl | hχ
    · exact hφ M hM
    · exact hM χ hχ

end Theoryω

namespace Sentenceω

variable {φ ψ χ : L.Sentenceω}

theorem Entails.refl (φ : L.Sentenceω) : φ.Entails φ :=
  Theoryω.entails_of_mem rfl

theorem entails_iff :
    φ.Entails ψ ↔ ∀ (M : Type) [L.Structure M] [Nonempty M],
      Sentenceω.Realize φ M → Sentenceω.Realize ψ M := by
  constructor
  · intro h M _ _ hφ
    exact h M fun χ hχ => Set.mem_singleton_iff.mp hχ ▸ hφ
  · intro h M _ _ hM
    exact h M (hM φ rfl)

theorem Entails.trans (h₁ : φ.Entails ψ) (h₂ : ψ.Entails χ) : φ.Entails χ :=
  entails_iff.mpr fun M _ _ hφ => entails_iff.mp h₂ M (entails_iff.mp h₁ M hφ)

end Sentenceω

end Language

end FirstOrder
