/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Polarity
import LeanPool.InfinitaryLogic.Lomega1omega.FiniteQuantification
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
import LeanPool.InfinitaryLogic.Methods.ConstantAbstraction
import LeanPool.InfinitaryLogic.Methods.Interpolation.ConstantElimination
import LeanPool.InfinitaryLogic.Methods.Interpolation.QuantifierRoundTrip
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.GeneratedUniverse
/-!
# The signed occurrence calculus (issue #14, Unit 0 layer 2)

The `Methods`-level half of Unit 0: the bridge from the signed traversal of
`Lomega1omega/Polarity.lean` to the unsigned `relationsIn`, and the signed twin of every
occurrence law the interpolation kernel consumes — language maps, relabelling, casting,
substitution, quantifier blocks, the constant-expansion machinery (`abstractConst`, `genEx`,
`instConst`, `stripConsts`), and the `baseRelationsIn` calculus.

Layering: the Core file knows nothing of `relationsIn`, `baseRelationsIn`, or the Henkin
machinery; everything that mentions them lives here.

Acceptance gates of Unit 0 (all in this file or its Core companion):

* `positiveRelationsIn_not` / `negativeRelationsIn_not` — the negation swaps (Core);
* `relationsIn_eq_signed_union` — `relationsIn = positive ∪ negative`, which is what turns
  Lyndon into Craig at the occurrence level;
* exact constructor equations for `imp`, `all`, `iInf`, `iSup` (Core);
* the exact image law `relationsInSigned_mapLanguage`.

No semantics and no inseparability notions appear in Unit 0.
-/

namespace FirstOrder.Language

open FirstOrder

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α β : Type}

/-! ## The bridge to the unsigned occurrence set -/

/-- **Acceptance gate**: the relation symbols of a formula are exactly those occurring with one
of the two signs.  This is what makes Craig interpolation a corollary of Lyndon interpolation at
the occurrence level. -/
theorem relationsIn_eq_signed_union :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n),
      φ.relationsIn = φ.positiveRelationsIn ∪ φ.negativeRelationsIn
  | _, .falsum => by simp [relationsIn]
  | _, .equal _ _ => by simp [relationsIn]
  | _, .rel R ts => by simp [relationsIn]
  | _, .imp φ ψ => by
    rw [relationsIn, relationsIn_eq_signed_union φ, relationsIn_eq_signed_union ψ]
    simp only [relationsInSigned_imp, Bool.not_true, Bool.not_false]
    ac_rfl
  | _, .all φ => by rw [relationsIn, relationsIn_eq_signed_union φ]; simp
  | _, .iSup φs => by
    rw [relationsIn]
    simp only [relationsInSigned_iSup]
    rw [← Set.iUnion_union_distrib]
    exact Set.iUnion_congr fun i => relationsIn_eq_signed_union (φs i)
  | _, .iInf φs => by
    rw [relationsIn]
    simp only [relationsInSigned_iInf]
    rw [← Set.iUnion_union_distrib]
    exact Set.iUnion_congr fun i => relationsIn_eq_signed_union (φs i)

theorem relationsInSigned_subset_relationsIn {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n) :
    relationsInSigned s φ ⊆ φ.relationsIn := by
  rw [relationsIn_eq_signed_union]
  cases s
  · exact Set.subset_union_right
  · exact Set.subset_union_left

/-! ## Language maps, relabelling, casting, substitution -/

/-- **Acceptance gate (exact image law)**: a language map moves the signed occurrence sets by the
symbol map, sign by sign. -/
theorem relationsInSigned_mapLanguage {L' : Language.{0, 0}} (g : L →ᴸ L') (s : Bool) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n),
      relationsInSigned s (φ.mapLanguage g) =
        (fun p : Σ n, L.Relations n => ⟨p.1, g.onRelation p.2⟩) '' relationsInSigned s φ
  | _, .falsum => by simp [mapLanguage]
  | _, .equal _ _ => by simp [mapLanguage]
  | _, .rel R ts => by cases s <;> simp [mapLanguage]
  | _, .imp φ ψ => by
    simp only [mapLanguage, relationsInSigned_imp, Set.image_union,
      relationsInSigned_mapLanguage g _ φ, relationsInSigned_mapLanguage g s ψ]
  | _, .all φ => by
    simp only [mapLanguage, relationsInSigned_all, relationsInSigned_mapLanguage g s φ]
  | _, .iSup φs => by
    simp only [mapLanguage, relationsInSigned_iSup, Set.image_iUnion]
    exact Set.iUnion_congr fun i => relationsInSigned_mapLanguage g s (φs i)
  | _, .iInf φs => by
    simp only [mapLanguage, relationsInSigned_iInf, Set.image_iUnion]
    exact Set.iUnion_congr fun i => relationsInSigned_mapLanguage g s (φs i)

private theorem relationsInSigned_castLE (s : Bool) :
    ∀ {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaω α m),
      relationsInSigned s (φ.castLE h) = relationsInSigned s φ
  | _, _, _, .falsum => rfl
  | _, _, _, .equal _ _ => rfl
  | _, _, _, .rel R ts => rfl
  | _, _, h, .imp φ ψ => by
    simp only [castLE, relationsInSigned_imp, relationsInSigned_castLE _ h φ,
      relationsInSigned_castLE s h ψ]
  | _, _, h, .all φ => by
    simp only [castLE, relationsInSigned_all, relationsInSigned_castLE s (Nat.succ_le_succ h) φ]
  | _, _, h, .iSup φs => by
    simp only [castLE, relationsInSigned_iSup]
    exact Set.iUnion_congr fun i => relationsInSigned_castLE s h (φs i)
  | _, _, h, .iInf φs => by
    simp only [castLE, relationsInSigned_iInf]
    exact Set.iUnion_congr fun i => relationsInSigned_castLE s h (φs i)

private theorem relationsInSigned_relabel (g : α → β ⊕ Fin n) (s : Bool) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      relationsInSigned s (φ.relabel g) = relationsInSigned s φ := by
  intro k φ
  induction φ generalizing s with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => simp only [relabel, relationsInSigned_imp, ihφ, ihψ]
  | all φ ih => simp only [relabel, relationsInSigned_all, relationsInSigned_castLE, ih]
  | iSup φs ih =>
    simp only [relabel, relationsInSigned_iSup]
    exact Set.iUnion_congr fun i => ih i s
  | iInf φs ih =>
    simp only [relabel, relationsInSigned_iInf]
    exact Set.iUnion_congr fun i => ih i s

private theorem relationsInSigned_subst (s : Bool) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (tf : α → L.Term β),
      relationsInSigned s (φ.subst tf) = relationsInSigned s φ
  | _, .falsum, _ => rfl
  | _, .equal _ _, _ => rfl
  | _, .rel R ts, _ => rfl
  | _, .imp φ ψ, tf => by
    simp only [subst, relationsInSigned_imp, relationsInSigned_subst _ φ tf,
      relationsInSigned_subst s ψ tf]
  | _, .all φ, tf => by
    simp only [subst, relationsInSigned_all, relationsInSigned_subst s φ tf]
  | _, .iSup φs, tf => by
    simp only [subst, relationsInSigned_iSup]
    exact Set.iUnion_congr fun i => relationsInSigned_subst s (φs i) tf
  | _, .iInf φs, tf => by
    simp only [subst, relationsInSigned_iInf]
    exact Set.iUnion_congr fun i => relationsInSigned_subst s (φs i) tf

private theorem relationsInSigned_openBounds (s : Bool) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
      relationsInSigned s (φ.openBounds) = relationsInSigned s φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel R ts => rfl
  | _, .imp φ ψ => by
    simp only [openBounds, relationsInSigned_imp, relationsInSigned_openBounds _ φ,
      relationsInSigned_openBounds s ψ]
  | _, .all φ => by
    simp only [openBounds, relationsInSigned_all, relationsInSigned_relabel,
      relationsInSigned_openBounds s φ]
  | _, .iSup φs => by
    simp only [openBounds, relationsInSigned_iSup]
    exact Set.iUnion_congr fun i => relationsInSigned_openBounds s (φs i)
  | _, .iInf φs => by
    simp only [openBounds, relationsInSigned_iInf]
    exact Set.iUnion_congr fun i => relationsInSigned_openBounds s (φs i)

/-! ## Finite quantifier blocks -/

theorem relationsInSigned_existsBlock (s : Bool) {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α (n + k)),
      relationsInSigned s (φ.existsBlock) = relationsInSigned s φ
  | 0, _ => rfl
  | _ + 1, φ =>
    (relationsInSigned_existsBlock s φ.ex).trans (relationsInSigned_ex s φ)

end BoundedFormulaω

/-! ## The constant-expansion machinery -/

section Consts

variable {L : Language.{0, 0}}

/-- Constant abstraction does not move the signed occurrence sets. -/
private theorem BoundedFormulaω.relationsInSigned_abstractConst (j : ℕ) (s : Bool) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
      relationsInSigned s (φ.abstractConst j) = relationsInSigned s φ := by
  intro n φ
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaω.abstractConst, relationsInSigned_imp, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.abstractConst, relationsInSigned_all, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.abstractConst, relationsInSigned_iSup]
    exact Set.iUnion_congr fun i => ih i s
  | iInf φs ih =>
    simp only [BoundedFormulaω.abstractConst, relationsInSigned_iInf]
    exact Set.iUnion_congr fun i => ih i s

/-- The existential generalization of a constant does not move the signed occurrence sets. -/
private theorem relationsInSigned_genEx (j : ℕ) (s : Bool) (ρ : L[[ℕ]].Sentenceω) :
    BoundedFormulaω.relationsInSigned s (genEx j ρ) = BoundedFormulaω.relationsInSigned s ρ := by
  rw [genEx, BoundedFormulaω.relationsInSigned_ex, BoundedFormulaω.relationsInSigned_relabel,
    BoundedFormulaω.relationsInSigned_abstractConst]

/-- Instantiating a universal at a constant does not move the signed occurrence sets. -/
private theorem relationsInSigned_instConst (c : ℕ) (s : Bool) (φ : L[[ℕ]].BoundedFormulaω
  Empty 1) :
    BoundedFormulaω.relationsInSigned s (instConst c φ) =
      BoundedFormulaω.relationsInSigned s φ := by
  rw [instConst, BoundedFormulaω.relationsInSigned_subst,
    BoundedFormulaω.relationsInSigned_openBounds]

end Consts

/-! ## The base signed occurrence sets -/

section Base

variable {L' : Language.{0, 0}} {J : Type} {α : Type}

/-- The **base** signed occurrence sets of a constant-expansion formula (the constant layer
contributes no relation symbols). -/
def BoundedFormulaω.baseRelationsInSigned {n : ℕ} (s : Bool)
    (φ : L'[[J]].BoundedFormulaω α n) : Set (Σ n, L'.Relations n) :=
  {p | (⟨p.1, Sum.inl p.2⟩ : Σ n, L'[[J]].Relations n) ∈ relationsInSigned s φ}

/-- The relation symbols occurring **positively** in a constant-expansion formula, read in the
base language. -/
abbrev BoundedFormulaω.basePositiveRelations {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) :
    Set (Σ n, L'.Relations n) := BoundedFormulaω.baseRelationsInSigned true φ

/-- The relation symbols occurring **negatively** in a constant-expansion formula, read in the
base language. -/
abbrev BoundedFormulaω.baseNegativeRelations {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) :
    Set (Σ n, L'.Relations n) := BoundedFormulaω.baseRelationsInSigned false φ

namespace BoundedFormulaω

/-- Signed occurrences of a **base-language** atom inside a constant expansion.

Stated with the symbol `Sum.inl R` baked in rather than left to the generic
`relationsInSigned_rel`: the goal's copy of that symbol carries the type
`L'.Relations l ⊕ (constantsOn J).Relations l`, which `rw`/`simp` cannot assign to
`relationsInSigned_rel`'s `?R : L'[[J]].Relations l` at `implicit` transparency. Spelling it the
same way here makes the match syntactic. -/
private theorem relationsInSigned_rel_inl {n l : ℕ} (s : Bool) (R : L'.Relations l)
    (ts : Fin l → L'[[J]].Term (α ⊕ Fin n)) :
    relationsInSigned s (BoundedFormulaω.rel (Sum.inl R : L'[[J]].Relations l) ts)
      = if s then {(⟨l, Sum.inl R⟩ : Σ n, L'[[J]].Relations n)} else ∅ := rfl

@[simp] theorem baseRelationsInSigned_falsum {n : ℕ} (s : Bool) :
    baseRelationsInSigned s (BoundedFormulaω.falsum : L'[[J]].BoundedFormulaω α n) = ∅ := by
  ext p; simp [baseRelationsInSigned]

/-- **Negation swaps the base signs.** -/
theorem baseRelationsInSigned_not {n : ℕ} (s : Bool) (φ : L'[[J]].BoundedFormulaω α n) :
    baseRelationsInSigned s φ.not = baseRelationsInSigned (!s) φ := by
  ext p; simp [baseRelationsInSigned]

/-- Alias gate: positive base occurrences of `¬φ` are the negative ones of `φ`. -/
theorem basePositiveRelations_not {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) :
    basePositiveRelations φ.not = baseNegativeRelations φ := baseRelationsInSigned_not true φ

/-- Alias gate: negative base occurrences of `¬φ` are the positive ones of `φ`. -/
theorem baseNegativeRelations_not {n : ℕ} (φ : L'[[J]].BoundedFormulaω α n) :
    baseNegativeRelations φ.not = basePositiveRelations φ := baseRelationsInSigned_not false φ

theorem baseRelationsInSigned_imp_left {s : Bool} {φ ψ : L'[[J]].BoundedFormulaω α n} :
    baseRelationsInSigned (!s) φ ⊆ baseRelationsInSigned s (φ.imp ψ) := by
  intro p hp
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_imp, Set.mem_union] at hp ⊢
  exact Or.inl hp

theorem baseRelationsInSigned_imp_right {s : Bool} {φ ψ : L'[[J]].BoundedFormulaω α n} :
    baseRelationsInSigned s ψ ⊆ baseRelationsInSigned s (φ.imp ψ) := by
  intro p hp
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_imp, Set.mem_union] at hp ⊢
  exact Or.inr hp

theorem baseRelationsInSigned_imp_subset {A : Set (Σ n, L'.Relations n)} {s : Bool}
    {φ ψ : L'[[J]].BoundedFormulaω α n}
    (h₁ : baseRelationsInSigned (!s) φ ⊆ A) (h₂ : baseRelationsInSigned s ψ ⊆ A) :
    baseRelationsInSigned s (φ.imp ψ) ⊆ A := by
  intro p hp
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_imp, Set.mem_union] at hp
  rcases hp with hp | hp
  · exact h₁ hp
  · exact h₂ hp

theorem baseRelationsInSigned_component_iInf {s : Bool} {φs : ℕ → L'[[J]].BoundedFormulaω α n}
    (k : ℕ) :
    baseRelationsInSigned s (φs k) ⊆ baseRelationsInSigned s (BoundedFormulaω.iInf φs) := by
  intro p hp
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_iInf,
    Set.mem_iUnion] at hp ⊢
  exact ⟨k, hp⟩

theorem baseRelationsInSigned_component_iSup {s : Bool} {φs : ℕ → L'[[J]].BoundedFormulaω α n}
    (k : ℕ) :
    baseRelationsInSigned s (φs k) ⊆ baseRelationsInSigned s (BoundedFormulaω.iSup φs) := by
  intro p hp
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_iSup,
    Set.mem_iUnion] at hp ⊢
  exact ⟨k, hp⟩

theorem baseRelationsInSigned_iSup_subset {A : Set (Σ n, L'.Relations n)} {s : Bool}
    (φs : ℕ → L'[[J]].BoundedFormulaω α n) (h : ∀ k, baseRelationsInSigned s (φs k) ⊆ A) :
    baseRelationsInSigned s (BoundedFormulaω.iSup φs) ⊆ A := by
  intro p hp
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_iSup,
    Set.mem_iUnion] at hp
  obtain ⟨k, hk⟩ := hp
  exact h k hk

end BoundedFormulaω

end Base

/-! ## Base signed occurrences of the kernel's atomic sentences -/

section Kernel

variable {L : Language.{0, 0}}

open BoundedFormulaω

/-- A constant equality has **no** signed base occurrences, in either sign — the syntactic form of
"equality is logical". -/
@[simp] theorem baseRelationsInSigned_constEq (s : Bool) (a b : ℕ) :
    baseRelationsInSigned s (constEq (L := L) a b) = ∅ := by
  ext p; simp [baseRelationsInSigned, constEq]

/-- An atomic relation instance's base **positive** set is exactly its own symbol. -/
theorem basePositiveRelations_relInst_eq {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) :
    basePositiveRelations (relInst R g) = {(⟨l, R⟩ : Σ n, L.Relations n)} := by
  ext p
  obtain ⟨n, r⟩ := p
  change (⟨n, Sum.inl r⟩ : Σ k, L[[ℕ]].Relations k)
      ∈ ({⟨l, Sum.inl R⟩} : Set (Σ k, L[[ℕ]].Relations k)) ↔ _
  rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
    exact congrArg _ (Sum.inl_injective (eq_of_heq h2))
  · intro h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
    exact congrArg _ (congrArg Sum.inl (eq_of_heq h2))

@[simp] theorem baseNegativeRelations_relInst {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) :
    baseNegativeRelations (relInst R g) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ h => h

/-- Universal instantiation does not enlarge the base signed sets. -/
theorem baseRelationsInSigned_instConst (c : ℕ) (s : Bool)
    (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    baseRelationsInSigned s (instConst c φ) = baseRelationsInSigned s (BoundedFormulaω.all φ) := by
  ext p
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_instConst,
    relationsInSigned_all]

/-- Existential generalization of a constant does not move the base signed sets. -/
theorem baseRelationsInSigned_genEx (j : ℕ) (s : Bool) (ρ : L[[ℕ]].Sentenceω) :
    baseRelationsInSigned s (genEx j ρ) = baseRelationsInSigned s ρ := by
  ext p
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq, relationsInSigned_genEx]

/-- **Base signed occurrences of a constant-expansion image** are the sentence's own signed
occurrences. -/
private theorem tag_inl_rel_inj :
    Function.Injective
      (fun p : Σ n, L.Relations n => (⟨p.1, Sum.inl p.2⟩ : Σ n, L[[ℕ]].Relations n)) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  exact Sigma.ext rfl (heq_of_eq (Sum.inl_injective (eq_of_heq h2)))

theorem baseRelationsInSigned_mapLanguage_withConstants (s : Bool) (r : L.Sentenceω) :
    baseRelationsInSigned s (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r) =
      relationsInSigned s r := by
  ext p
  simp only [baseRelationsInSigned, Set.mem_ofPred_eq,
    relationsInSigned_mapLanguage (L.lhomWithConstants ℕ)]
  exact tag_inl_rel_inj.mem_set_image

/-- Alias form of the constant-expansion image law, positive sign (matches the `abbrev` shape, so
`rw` fires on goals stated with `basePositiveRelations`). -/
theorem basePositiveRelations_mapLanguage_withConstants (r : L.Sentenceω) :
    (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r).basePositiveRelations =
      r.positiveRelationsIn :=
  baseRelationsInSigned_mapLanguage_withConstants true r

/-- Alias form of the constant-expansion image law, negative sign. -/
theorem baseNegativeRelations_mapLanguage_withConstants (r : L.Sentenceω) :
    (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r).baseNegativeRelations =
      r.negativeRelationsIn :=
  baseRelationsInSigned_mapLanguage_withConstants false r

/-- Stripping a constant-free formula keeps the signed occurrences inside the base signed set. -/
theorem relationsInSigned_stripConsts (s : Bool) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω α n) (h : sentenceJConsts (L' := L) φ ⊆ ∅),
      relationsInSigned s (φ.stripConsts h) ⊆ baseRelationsInSigned s φ := by
  intro n φ
  induction φ generalizing s with
  | falsum => intro h p hp; exact absurd hp (Set.notMem_empty p)
  | equal t u => intro h p hp; exact absurd hp (Set.notMem_empty p)
  | rel R ts =>
    rcases R with R | R
    · intro h p hp
      cases s
      · exact absurd hp (Set.notMem_empty p)
      · simp only [BoundedFormulaω.stripConsts, relationsInSigned_rel, ite_true,
          Set.mem_singleton_iff] at hp
        subst hp
        change (⟨_, Sum.inl R⟩ : Σ n, L[[ℕ]].Relations n) ∈
          relationsInSigned true (BoundedFormulaω.rel (Sum.inl R) ts)
        rw [relationsInSigned_rel_inl]
        exact Set.mem_singleton _
    · exact nomatch R
  | imp φ ψ ihφ ihψ =>
    intro h p hp
    simp only [BoundedFormulaω.stripConsts, relationsInSigned_imp, Set.mem_union] at hp
    rcases hp with hp | hp
    · exact baseRelationsInSigned_imp_left (ihφ _ _ hp)
    · exact baseRelationsInSigned_imp_right (ihψ _ _ hp)
  | all φ ih =>
    intro h p hp
    simp only [BoundedFormulaω.stripConsts, relationsInSigned_all] at hp
    exact ih _ _ hp
  | iSup φs ih =>
    intro h p hp
    simp only [BoundedFormulaω.stripConsts, relationsInSigned_iSup, Set.mem_iUnion] at hp
    obtain ⟨i, hi⟩ := hp
    exact baseRelationsInSigned_component_iSup i (ih i _ _ hi)
  | iInf φs ih =>
    intro h p hp
    simp only [BoundedFormulaω.stripConsts, relationsInSigned_iInf, Set.mem_iUnion] at hp
    obtain ⟨i, hi⟩ := hp
    exact baseRelationsInSigned_component_iInf i (ih i _ _ hi)

end Kernel

end FirstOrder.Language
