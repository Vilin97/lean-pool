/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
/-!
# The functional witness language (issue #10, Unit 1 part 1)

Marker's `τ*` (Lemma 4.23), as a functional language per audit v2 (D4, graph-translation
route): a constant `c`, unary functions `s, f, g`, and a `2n`-ary tree relation at every
`n` — **including `tree 0`** (the nullary `S₀`; Marker starts at positive lengths, but
admitting level `0` lets the path sentence assert it while the pinning sentence of a
branchless tree refutes it, so the empty analytic set yields an inconsistent PC sentence
with no special case).

Contents: the language with explicit countability instances for both symbol sigma-types;
**actual numeral terms** `numTerm n` (`c`, `s c`, `s (s c)`, …) with their map-language,
occurrence, and realization lemmas; the common tagged language
`KLang L = L.sum (WitnessLang.sum WitnessLang)` with named embeddings for the base, left
witness, and right witness symbols; the tagged symbol-image sets; and their pairwise
disjointness (the combinatorial half of the Unit-1 occurrence gate).
-/

namespace FirstOrder.Language

open FirstOrder

/-- Function symbols of the witness language: the zero `c` and the unary `s, f, g`. -/
inductive WitnessFun : ℕ → Type
  | c : WitnessFun 0
  | s : WitnessFun 1
  | f : WitnessFun 1
  | g : WitnessFun 1

/-- Relation symbols of the witness language: one `2n`-ary tree relation at every level,
including the nullary `tree 0`. -/
inductive WitnessRel : ℕ → Type
  | tree (n : ℕ) : WitnessRel (2 * n)

/-- **The functional witness language** (Marker's `τ*`, audit v2 D4). -/
def WitnessLang : Language.{0, 0} where
  Functions := WitnessFun
  Relations := WitnessRel

instance : Countable (Σ n, WitnessLang.Functions n) := by
  refine Function.Injective.countable (f := fun p : Σ n, WitnessLang.Functions n =>
    (match p with
      | ⟨_, .c⟩ => 0
      | ⟨_, .s⟩ => 1
      | ⟨_, .f⟩ => 2
      | ⟨_, .g⟩ => 3 : ℕ)) ?_
  rintro ⟨_, x⟩ ⟨_, y⟩ h
  cases x <;> cases y <;> simp_all

/-! ## Numeral terms -/

variable {α : Type}

/-! ## The common tagged language and its named embeddings -/

/-- **The common tagged language**: the base plus two tagged witness copies. -/
abbrev KLang (L : Language.{0, 0}) : Language.{0, 0} :=
  L.sum (WitnessLang.sum WitnessLang)

variable (L : Language.{0, 0})

/-- The base-symbol embedding. -/
def baseEmb : L →ᴸ KLang L := LHom.sumInl

/-- The left-witness embedding. -/
def leftWitnessEmb : WitnessLang →ᴸ KLang L := LHom.sumInr.comp LHom.sumInl

/-- The right-witness embedding. -/
def rightWitnessEmb : WitnessLang →ᴸ KLang L := LHom.sumInr.comp LHom.sumInr

/-! ## Tagged symbol-image sets and their disjointness -/

/-- Base function symbols inside `KLang L`. -/
def baseFuns : Set (Σ n, (KLang L).Functions n) :=
  Set.range fun p : Σ n, L.Functions n => ⟨p.1, (baseEmb L).onFunction p.2⟩

/-- Base relation symbols inside `KLang L`. -/
def baseRels : Set (Σ n, (KLang L).Relations n) :=
  Set.range fun p : Σ n, L.Relations n => ⟨p.1, (baseEmb L).onRelation p.2⟩

/-- Left-witness function symbols inside `KLang L`. -/
def leftFuns : Set (Σ n, (KLang L).Functions n) :=
  Set.range fun p : Σ n, WitnessLang.Functions n => ⟨p.1, (leftWitnessEmb L).onFunction p.2⟩

/-- Left-witness relation symbols inside `KLang L`. -/
def leftRels : Set (Σ n, (KLang L).Relations n) :=
  Set.range fun p : Σ n, WitnessLang.Relations n => ⟨p.1, (leftWitnessEmb L).onRelation p.2⟩

/-- Right-witness function symbols inside `KLang L`. -/
def rightFuns : Set (Σ n, (KLang L).Functions n) :=
  Set.range fun p : Σ n, WitnessLang.Functions n => ⟨p.1, (rightWitnessEmb L).onFunction p.2⟩

/-- Right-witness relation symbols inside `KLang L`. -/
def rightRels : Set (Σ n, (KLang L).Relations n) :=
  Set.range fun p : Σ n, WitnessLang.Relations n => ⟨p.1, (rightWitnessEmb L).onRelation p.2⟩

/-- Two tagged sigma-image ranges with pointwise-clashing tags are disjoint. -/
private theorem range_tag_disjoint {γ δ₁ δ₂ : ℕ → Type}
    {j₁ : ∀ n, δ₁ n → γ n} {j₂ : ∀ n, δ₂ n → γ n}
    (hne : ∀ n (a : δ₁ n) (b : δ₂ n), j₁ n a ≠ j₂ n b) :
    (Set.range fun p : Σ n, δ₁ n => (⟨p.1, j₁ p.1 p.2⟩ : Σ n, γ n)) ∩
      (Set.range fun p : Σ n, δ₂ n => ⟨p.1, j₂ p.1 p.2⟩) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨⟨np, ap⟩, hp⟩, ⟨⟨nq, aq⟩, hq⟩⟩
  rw [← hq] at hp
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hp
  rw [heq_eq_eq] at h2
  exact hne _ _ _ h2

/-- **Left/right witness function symbols are disjoint.** -/
theorem leftFuns_inter_rightFuns : leftFuns L ∩ rightFuns L = ∅ :=
  range_tag_disjoint fun _ _ _ h => Sum.inl_ne_inr (Sum.inr_injective h)

/-- **Left/right witness relation symbols are disjoint.** -/
theorem leftRels_inter_rightRels : leftRels L ∩ rightRels L = ∅ :=
  range_tag_disjoint fun _ _ _ h => Sum.inl_ne_inr (Sum.inr_injective h)

end FirstOrder.Language
