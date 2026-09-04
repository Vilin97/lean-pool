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

instance : Countable (Σ n, WitnessLang.Relations n) := by
  refine Function.Injective.countable (f := fun p : Σ n, WitnessLang.Relations n =>
    (match p with | ⟨_, .tree n⟩ => n : ℕ)) ?_
  rintro ⟨_, ⟨m⟩⟩ ⟨_, ⟨n⟩⟩ h
  simp only at h
  subst h
  rfl

/-! ## Numeral terms -/

variable {α : Type}

/-- **The numeral terms**: `numTerm 0 = c`, `numTerm (n+1) = s (numTerm n)`. -/
def numTerm (α : Type) : ℕ → WitnessLang.Term α
  | 0 => Term.func WitnessFun.c Fin.elim0
  | n + 1 => Term.func WitnessFun.s ![numTerm α n]

/-- The numeral terms mention only `c` and `s`. -/
theorem functionsIn_numTerm (n : ℕ) :
    (numTerm α n).functionsIn ⊆
      {(⟨0, WitnessFun.c⟩ : Σ k, WitnessLang.Functions k), ⟨1, WitnessFun.s⟩} := by
  induction n with
  | zero =>
    intro p hp
    rcases hp with rfl | hp
    · exact Set.mem_insert _ _
    · exact absurd hp (by simp)
  | succ n ih =>
    intro p hp
    rcases hp with rfl | hp
    · exact Set.mem_insert_of_mem _ rfl
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      rw [Fin.eq_zero i] at hi
      exact ih hi

/-- Map-language commutation, zero case. -/
theorem onTerm_numTerm_zero {L' : Language.{0, 0}} (φ : WitnessLang →ᴸ L') :
    φ.onTerm (numTerm α 0) = Term.func (φ.onFunction WitnessFun.c) Fin.elim0 := by
  simp only [numTerm, LHom.onTerm]
  congr 1
  funext i
  exact i.elim0

/-- Map-language commutation, successor case. -/
theorem onTerm_numTerm_succ {L' : Language.{0, 0}} (φ : WitnessLang →ᴸ L') (n : ℕ) :
    φ.onTerm (numTerm α (n + 1)) =
      Term.func (φ.onFunction WitnessFun.s) ![φ.onTerm (numTerm α n)] := by
  simp only [numTerm, LHom.onTerm]
  congr 1
  funext i
  rw [Fin.eq_zero i]
  simp only [Matrix.cons_val_zero]

/-- Realization of the numeral terms: the `n`-fold `s`-iterate of `c`. -/
theorem realize_numTerm {M : Type*} [inst : WitnessLang.Structure M] (v : α → M) (n : ℕ) :
    (numTerm α n).realize v =
      (fun x => @Structure.funMap WitnessLang M inst 1 WitnessFun.s ![x])^[n]
        (@Structure.funMap WitnessLang M inst 0 WitnessFun.c (Fin.elim0 : Fin 0 → M)) := by
  induction n with
  | zero =>
    simp only [numTerm, Term.realize, Function.iterate_zero, id_eq]
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    simp only [numTerm, Term.realize, Function.iterate_succ_apply', ← ih]
    congr 1
    funext i
    rw [Fin.eq_zero i]
    simp only [Matrix.cons_val_zero]

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

/-- Base and left-witness function symbols are disjoint (likewise below for the right copy,
by the same `Sum.inl`/`Sum.inr` clash). -/
theorem baseFuns_inter_leftFuns : baseFuns L ∩ leftFuns L = ∅ :=
  range_tag_disjoint fun _ _ _ h => Sum.inl_ne_inr h

theorem baseRels_inter_leftRels : baseRels L ∩ leftRels L = ∅ :=
  range_tag_disjoint fun _ _ _ h => Sum.inl_ne_inr h

theorem baseFuns_inter_rightFuns : baseFuns L ∩ rightFuns L = ∅ :=
  range_tag_disjoint fun _ _ _ h => Sum.inl_ne_inr h

theorem baseRels_inter_rightRels : baseRels L ∩ rightRels L = ∅ :=
  range_tag_disjoint fun _ _ _ h => Sum.inl_ne_inr h

end FirstOrder.Language
