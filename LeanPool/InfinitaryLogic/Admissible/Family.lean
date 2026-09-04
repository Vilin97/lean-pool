/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Syntax
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
/-!
# The family layer (issues #18, #19A)

The honest replacement for closure under *arbitrary external* ℕ-indexed families.  A fragment may
only be asked to contain the conjunctions and disjunctions that the admissible set itself **names**.

**This file is the syntax boundary.**  It defines the minimal data a coded family needs and nothing
else — no theory decoding, no `Sigma1`, no definition codes, no KP, no numbering.  Those are not
merely absent by convention: they are defined in files that import *this* one, so `CodedFamily`
cannot reach them even in principle.  `scripts/check_family_cone.lean` pins that permanently.

Three details are load-bearing and each was validated against the HF instance before being fixed:

1. `decode` lands in the structure's own arity — no independent arity field can drift.
2. The enumeration is supplied by the presentation (`indexEncodable`), keyed on the code, **not**
   found by instance search; the syntax a coded family builds therefore depends on the code.
3. `IsFamilyCode` is a **certificate**, absorbed into the code subtype rather than carried as a
   separate hypothesis.  Without it any code with any decoding would build a coded family, and
   "HF has no primitive coded families" would be unstatable.

`decodes_unique` makes decoding code-determined, which is what the extensionality API below rests
on.

## Main definitions

- `FamilyPresentation`: ambient `Element`, the `IsFamilyCode` subdomain, and the decoding data.
- `CodedFamily`, `codedIInf`, `codedISup`.
-/

namespace FirstOrder.Language

universe u v uCode uIndex

/-- **The family view of a presentation.**  The *only* data the syntax layer may consult.

Phrased ambient-style: one `Element` carrier with `IsFamilyCode` carving out the subdomain of codes
naming infinitary families.  The certificate lives in the code subtype rather than in a separate
hypothesis, so `decodes_unique` is unconditional here while remaining vacuous for any presentation
whose `IsFamilyCode` is empty. -/
structure FamilyPresentation (L : Language.{u, v}) where
  /-- The elements of `A`. -/
  Element : Type uCode
  /-- The certificate that an element names a genuinely **infinitary** family.  This is the
  predicate that is empty for HF, and the sole source of that emptiness. -/
  IsFamilyCode : Element → Prop
  /-- The index type a code names.  Comes *from the code*, never fixed at `ℕ`. -/
  Index : {e // IsFamilyCode e} → Type uIndex
  /-- A code-determined enumeration.  Data, not a side condition: the `iInf` constructor is
  ℕ-indexed, so a family cannot be turned into syntax without one. -/
  indexEncodable : ∀ c, Encodable (Index c)
  /-- The decoding law: which family a code denotes. -/
  DecodesFamily : ∀ (n : ℕ) (c : {e // IsFamilyCode e}),
    (Index c → L.BoundedFormulaω Empty n) → Prop
  /-- **Functionality.**  A family code determines its family.  Without this, `DecodesFamily` is an
  arbitrary `Prop` and one code may admit many decodings, so `decoded_by_code` would constrain
  nothing and `codedIInf` would not be a function of the code. -/
  decodes_unique : ∀ {n : ℕ} {c : {e // IsFamilyCode e}}
    {f g : Index c → L.BoundedFormulaω Empty n},
    DecodesFamily n c f → DecodesFamily n c g → f = g

namespace FamilyPresentation

variable {L : Language.{u, v}} (P : FamilyPresentation.{u, v, uCode, uIndex} L)

/-- The family-code subdomain. -/
abbrev FamilyCode := {e // P.IsFamilyCode e}

end FamilyPresentation

/-- A **coded family**: a certified code, its decoded family, and the law tying the two together.

The certificate is no longer a separate field — it is carried by `code`, which lives in the
`IsFamilyCode` subdomain.  `CodedFamily.infinitary` recovers it. -/
structure CodedFamily {L : Language.{u, v}}
    (P : FamilyPresentation.{u, v, uCode, uIndex} L) (n : ℕ) where
  code : P.FamilyCode
  decode : P.Index code → L.BoundedFormulaω Empty n
  decoded_by_code : P.DecodesFamily n code decode

variable {L : Language.{u, v}} {P : FamilyPresentation.{u, v, uCode, uIndex} L} {n : ℕ}

/-- The infinitary certificate, recovered from the code's subdomain membership.  Kept as a named
accessor because "HF has no coded families" is proved by contradicting exactly this. -/
theorem CodedFamily.infinitary (F : CodedFamily P n) : P.IsFamilyCode F.code.1 := F.code.2

/-- The conjunction a coded family names.  The encoding is the **presentation's**, installed
locally, so the resulting syntax depends on the code rather than on ambient instance search. -/
def codedIInf (F : CodedFamily P n) : L.BoundedFormulaω Empty n :=
  BoundedFormulaω.einfWith (P.indexEncodable F.code) F.decode

/-- The disjunction a coded family names. -/
def codedISup (F : CodedFamily P n) : L.BoundedFormulaω Empty n :=
  BoundedFormulaω.esupWith (P.indexEncodable F.code) F.decode

/-! ## Acceptance gates -/

section Gates

variable {M : Type} [L.Structure M] {v : Empty → M} {xs : Fin n → M}

/-- **Gate 1a.**  `codedIInf` realizes as a conjunction over `P.Index code`. -/
theorem realize_codedIInf (F : CodedFamily P n) :
    (codedIInf F).Realize v xs ↔ ∀ i, (F.decode i).Realize v xs :=
  BoundedFormulaω.realize_einfWith _ F.decode

/-- **Gate 1b.**  …and `codedISup` as a disjunction. -/
theorem realize_codedISup (F : CodedFamily P n) :
    (codedISup F).Realize v xs ↔ ∃ i, (F.decode i).Realize v xs :=
  BoundedFormulaω.realize_esupWith _ F.decode

end Gates

/-- **Gate 2.**  The arity is the parameter `n`; there is no independent arity field.  Stated as a
type ascription that would not elaborate if the arity could drift. -/
example (F : CodedFamily P n) : L.BoundedFormulaω Empty n := codedIInf F

/-- **Gate 3.**  An alternative ambient `Encodable` on the index type cannot change the syntax.

The hypothesis `_e` is deliberately **unused**: it puts a competing instance in scope, and the
statement still holds by `rfl`, which is exactly the claim — `codedIInf` never consults instance
search, it reads `P.indexEncodable`. -/
theorem codedIInf_uses_presentation_encoding (F : CodedFamily P n)
    (_e : Encodable (P.Index F.code)) :
    codedIInf F = BoundedFormulaω.einfWith (P.indexEncodable F.code) F.decode := rfl

/-! ### Extensionality

Functionality (`decodes_unique`) is what makes a coded family *determined by its code*.  Everything
below is a consequence. -/

/-- Equal codes force equal decodings. -/
theorem decode_eq_of_code_eq {F G : CodedFamily P n} (h : F.code = G.code) :
    F.decode = h ▸ G.decode := by
  cases F with | mk c f hf =>
  cases G with | mk c' g hg =>
  cases h
  exact P.decodes_unique hf hg

/-- **Extensionality**: a coded family is its code.  The decoding law is a `Prop`, and the decoding
is determined by the code, so nothing else can differ. -/
@[ext] theorem CodedFamily.ext {F G : CodedFamily P n} (h : F.code = G.code) : F = G := by
  cases F with | mk c f hf =>
  cases G with | mk c' g hg =>
  cases h
  cases P.decodes_unique hf hg
  rfl

/-- **Gate 5 (functionality).**  The conjunction built from a coded family is determined by the
code. -/
theorem codedIInf_eq_of_code_eq {F G : CodedFamily P n} (h : F.code = G.code) :
    codedIInf F = codedIInf G := by rw [CodedFamily.ext h]

/-- …and the disjunction likewise. -/
theorem codedISup_eq_of_code_eq {F G : CodedFamily P n} (h : F.code = G.code) :
    codedISup F = codedISup G := by rw [CodedFamily.ext h]

/-! ## The HF family view

HF names no infinitary family, so its family layer is determined by `IsFamilyCode := False` and
everything else is vacuous.  Defined here, at the family layer, so the *syntax* consumers of HF
depend on nothing else — in particular not on a full presentation carrying theory decoding or
`Sigma1`.

`Element := ℕ` matches the ambient HF instance, so `(hfAmbient C).toFamilyPresentation` is this
presentation definitionally (`hfAmbient_toFamilyPresentation`). -/

/-- **The HF family view.**  No code names an infinitary family; the remaining fields are
discharged by the empty code subdomain. -/
def hfFamily (L : Language.{u, v}) : FamilyPresentation.{u, v, 0, 0} L where
  Element := ℕ
  IsFamilyCode _ := False
  Index c := c.2.elim
  indexEncodable c := c.2.elim
  DecodesFamily _ c _ := c.2.elim
  decodes_unique {_} {c} {_} {_} _ _ := c.2.elim

/-- **`CodedFamily` over HF is uninhabited** — the whole content of "HF has no primitive coded
families", and it depends on the family layer alone. -/
theorem isEmpty_codedFamily_hfFamily {L : Language.{u, v}} {n : ℕ} :
    IsEmpty (CodedFamily (hfFamily L) n) :=
  ⟨fun F => F.infinitary⟩

/-- Consequently every upward-closure obligation over HF is vacuous, for **any** target set. -/
theorem hfFamily_coded_closure_vacuous {L : Language.{u, v}} {n : ℕ}
    (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ∀ F : CodedFamily (hfFamily L) n,
      (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S) →
        (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S :=
  fun F => absurd F.infinitary not_false

end FirstOrder.Language
