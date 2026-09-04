/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Admissible.Fragment.Honest
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
import LeanPool.InfinitaryLogic.Lomega1omega.FirstOrderImage
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# The HF fragment (issue #18)

`L_HF = L_ωω`: the first-order image inside `Lω₁ω`, as an honest admissible fragment, plus its
compactness theorem derived from Mathlib.

**This is the regression oracle for the interface.**  Any proposed change to `AdmissibleFragment`
must keep all four conditions:

1. the underlying formulas are exactly the `toLω`-image (`sentence_slice_hfFragment`);
2. coded families reduce to finite ones — here, to none at all;
3. the compactness theorem is `finitaryFragment_compact`;
4. no adapter widens it back to all of `Lω₁ω`.

**Where the emptiness lives.**  `hfFamily.IsFamilyCode` is `False`.  Not the index type's
cardinality, and not `einf`'s `⊤`-padding, which is legitimate for a real infinitary code.  The
forbidden move is granting the certificate to a finite code and using padding to manufacture a
primitive `iInf`.

**Universes.**  The syntax layer and `finitaryFragment_compactIn` are universe-general; the latter
returns Mathlib's canonical model in `Type (max u v)`.  The compatibility theorem
`finitaryFragment_compact` retains its published universe-zero result type.

**Not built on the legacy structures.**  `AdmissibleFragmentCore.hf := Set.univ` is a quarantined
placeholder; nothing here uses it, and nothing here may be proved from it.
-/

namespace FirstOrder.Language

universe u v w uCode uIndex

variable {L : Language.{0, 0}}

/-- The all-arity first-order image: every formula containing no infinitary node. -/
def hfSet (L : Language.{u, v}) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  {p | p.2.IsFirstOrder}

@[simp] theorem mem_hfSet_iff {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ hfSet L ↔ φ.IsFirstOrder := Iff.rfl

/-- **The HF fragment.**  Each field is now one appeal to the first-order-image API: three
structural equations and the two negative facts.  Compare the five hand-rolled constructor
inversions this replaces. -/
def hfFragment (L : Language.{u, v}) : Fragment L where
  toSet := hfSet L
  imp_left_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).1
  imp_right_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).2
  all_mem h := BoundedFormulaω.isFirstOrder_all_iff.mp h
  iInf_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iInf _)
  iSup_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iSup _)


/-- **The finitary fragment**: the image of first-order syntax in `Lω₁ω`.  This is `L_HF = L_ωω`. -/
def finitaryFragment (L : Language.{u, v}) : Set L.Sentenceω :=
  Set.range Sentence.toLω

theorem mem_finitaryFragment_iff {L : Language.{u, v}} {φ : L.Sentenceω} :
    φ ∈ finitaryFragment L ↔ ∃ φ₀ : L.Sentence, φ₀.toLω = φ := Iff.rfl

/-- **The oracle, condition 1.**  The sentence slice of `hfFragment` is exactly `finitaryFragment`.
Any proposed `AdmissibleFragment` whose HF instance fails this is wrong.

Both sides are universe-general. -/
theorem sentence_slice_hfFragment (L : Language.{u, v}) :
    {φ : L.Sentenceω | (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ hfFragment L} =
      finitaryFragment L := by
  ext φ
  simp only [Set.mem_ofPred_eq, Fragment.mem_def, mem_finitaryFragment_iff]
  exact Iff.rfl

/-- The **full preimage theory** — every first-order sentence whose image lies in `T`, not one
chosen representative per member.  Choosing representatives would need `Classical.choice` and would
make the model correspondence direction-sensitive. -/
def foTheory {L : Language.{u, v}} (T : Set L.Sentenceω) : L.Theory :=
  {φ₀ : L.Sentence | φ₀.toLω ∈ T}

/-- **Model correspondence.**  For a theory inside the finitary fragment, models of the preimage
theory are exactly models of the original. -/
theorem model_foTheory_iff {L : Language.{u, v}} {T : Set L.Sentenceω}
    (hT : T ⊆ finitaryFragment L) (M : Type w) [L.Structure M] [Nonempty M] :
    M ⊨ foTheory T ↔ Theoryω.Model T M := by
  constructor
  · intro hM φ hφ
    obtain ⟨φ₀, rfl⟩ := hT hφ
    exact (Sentence.realize_toLω φ₀).mpr (hM.realize_of_mem φ₀ hφ)
  · intro hM
    refine ⟨fun {φ₀} hφ₀ => ?_⟩
    exact (Sentence.realize_toLω φ₀).mp (hM _ hφ₀)

/-- **Universe-general compactness for the finitary fragment**, derived from Mathlib's first-order
compactness.

No `compact` field is consulted: the infinitary finite-satisfiability hypothesis is pushed through
`toLω` to the preimage theory, Mathlib supplies its canonical model in `Type (max u v)`, and the
correspondence carries it back.  Finite-subtheory witnesses may live in any fixed `Type w`; their
universe is independent of the output universe. -/
theorem finitaryFragment_compactIn {L : Language.{u, v}} {T : L.Theoryω}
    (hT : T ⊆ finitaryFragment L) (hfin : Theoryω.IsFinitelySatisfiableIn.{u, v, w} T) :
    Theoryω.IsSatisfiableIn.{u, v, max u v} T := by
  -- every finite subset of the preimage theory is satisfiable
  have hfs : (foTheory T).IsFinitelySatisfiable := by
    intro F₀ hF₀
    obtain ⟨M, instM, neM, hM⟩ :=
      hfin (Sentence.toLω '' (F₀ : Set L.Sentence))
        (by rintro _ ⟨φ₀, hφ₀, rfl⟩; exact hF₀ hφ₀)
        (F₀.finite_toSet.image _)
    let : L.Structure M := instM
    have := neM
    have : M ⊨ (↑F₀ : L.Theory) :=
      ⟨fun {φ₀} hφ₀ => (Sentence.realize_toLω φ₀).mp (hM _ ⟨φ₀, hφ₀, rfl⟩)⟩
    exact Theory.Model.isSatisfiable M
  -- Mathlib first-order compactness
  obtain ⟨M⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfs
  exact ⟨M, inferInstance, inferInstance, (model_foTheory_iff hT M).mp M.is_model⟩

/-- **Universe-zero compatibility endpoint.**  This retains the published result type while the
underlying first-order argument is universe-general; use `finitaryFragment_compactIn` when the
language or resulting carrier lives above universe zero. -/
theorem finitaryFragment_compact {T : L.Theoryω} (hT : T ⊆ finitaryFragment L)
    (hfin : T.IsFinitelySatisfiable) : T.IsSatisfiable :=
  finitaryFragment_compactIn hT hfin


/-! ## Gate 4 — the HF oracle

For HF the certificate is empty, so `CodedFamily` is uninhabited and the upward-closure fields of
any `AdmissibleFragment` over it are vacuous.  Note where the emptiness lives: in `IsFamilyCode`,
**not** in the index type's cardinality and **not** in `einf`'s padding. -/

/-- **Gate 4.**  `CodedFamily` over HF is uninhabited.

Stated over `hfFamily`, the family-layer HF presentation, so the syntax consumers of HF depend on
no presentation carrying theory decoding or `Sigma1`.  The emptiness comes solely from
`IsFamilyCode := False`. -/
theorem isEmpty_codedFamily_hf : IsEmpty (CodedFamily (hfFamily L) n) :=
  isEmpty_codedFamily_hfFamily

/-- Consequently every upward-closure obligation over HF is vacuous, for **any** target set. -/
theorem hf_coded_closure_vacuous (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ∀ F : CodedFamily (hfFamily L) n,
      (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S) →
        (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S :=
  hfFamily_coded_closure_vacuous S


/-! ## Step 4 — the honest HF instance

Essentially a structure literal: the base is `hfFragment`, and both upward fields are closed by
certificate absurdity.  That it *is* nearly definitional is the signal that the signature is right. -/

/-- **The HF admissible fragment.**  No adapter, no widening. -/
def hfAdmissibleFragment (L : Language.{0, 0}) : AdmissibleFragment (hfFamily L) where
  toFragment := hfFragment L
  iInf_coded_mem := fun F _ => absurd F.infinitary not_false
  iSup_coded_mem := fun F _ => absurd F.infinitary not_false

/-- **Oracle condition 1, at the interface level.**  The HF admissible fragment's underlying
`Fragment` is exactly `hfFragment`, whose sentence slice is `finitaryFragment`. -/
theorem hfAdmissibleFragment_toFragment (L : Language.{0, 0}) :
    (hfAdmissibleFragment L).toFragment = hfFragment L := rfl


/-! ## The universe boundary

The structures are **language-indexed and universe-polymorphic**: `FamilyPresentation L` for
`L : Language.{u, v}`, so `FamilyPresentation L[[J]]` is well-formed for an arbitrary parameter
type `J`.  The probes below record that, at the signature level only — nothing here claims a
presentation for `L` lifts to one for `L[[J]]`.

The low-level semantic boundary is now explicit: `Theoryω.IsSatisfiableIn` selects the carrier
universe, and `finitaryFragment_compactIn` works for any language.  The ambient presentation API
still concludes the published universe-zero `Theoryω.IsSatisfiable`; that remaining boundary is
enforced separately by `scripts/check_admissible_universes.lean`.

Write the probe results as `Type _`, not `Type`: bare `Type` means `Type 0`, and that constraint
propagates *backward* onto the presentation argument. -/

section UniverseGate

/-- Arbitrary parameter type, arbitrary language universes: a coded family elaborates. -/
example (Lb : Language.{u, v}) (J : Type w) (B : FamilyPresentation Lb[[J]]) (m : ℕ) : Type _ :=
  CodedFamily B m

/-- …and so does the fragment wrapper. -/
example (Lb : Language.{u, v}) (J : Type w) (B : FamilyPresentation Lb[[J]]) : Type _ :=
  AdmissibleFragment B

end UniverseGate

end FirstOrder.Language
