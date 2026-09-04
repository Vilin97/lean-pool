/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.SchemaCompletion
/-!
# Layer 7b checkpoint 5a: the schema term-model substrate

The completed schema theory `Tσ = schemaCompletionTheory (schemaEnumeration s₀) hM` is complete on
the schema universe, `iSup`-witnessed, and finite-character consistent — but NOT a maximal
`ConsistencyPropertyEq` (deliberately: the pivot escaped the `extension`-field blocker). So its
term model's equality quotient cannot come from a syntactic `C6`-closure of `Tσ`. Instead, per the
design decision, equality on closed `(localColim s₀)[[ℕ]]` terms is defined **directly in the
`locDeEqAtom` vocabulary the completion controls**, and every quotient law (reflexivity, symmetry,
transitivity, congruence, relation well-definedness) is proved by the **same source-semantic
contradiction**: if the wrong sign were in `Tσ`, `finite_consistent` yields a source-model body
realizing an impossible equality situation in `M`.

The file delivers checkpoint 5a in full: the canonical-support equality relation `SchemaTermEq`
and the shared body-extraction engine `exists_body_of_subset`; the exported semantic bridges
`realize_schemaEqSentence_iff`/`realize_schemaRelSentence_iff` (via the σ-generalization
`locDeTermFin_realize_constInterp_nat`); the equivalence/congruence laws; and the quotient model —
`SchemaTermCarrier` with its `(localColim s₀)[[ℕ]]`-structure, the atomic API
(`schemaTerm_funMap_mk`/`schemaTerm_realize_eq_mk`/`schemaTerm_relMap_mk_iff`), and the canonical
sequence `schemaSeq` (the classes of the `d`-constants). No `iSup`, `all`, or truth lemma here —
that is checkpoint 5b.
-/

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- The canonical finite support of an equality between two closed schema terms. -/
def schemaSupport (t u : (localColim s₀)[[ℕ]].Term Empty) : Finset ℕ :=
  locJSupport (localColim s₀) ℕ t ∪ locJSupport (localColim s₀) ℕ u

/-- The lifted `templateSentence` of the de-substituted equality atom `locDeEqAtom` at the
canonical support — the schema-universe sentence that encodes "`t = u`". -/
def schemaEqSentence (t u : (localColim s₀)[[ℕ]].Term Empty) :
    ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω :=
  (Lomega1omegaTemplate.templateSentence
      (locDeEqAtom (localColim s₀) ℕ (schemaSupport t u) t u
        Finset.subset_union_left Finset.subset_union_right)
      ((schemaSupport t u).orderEmbOfFin rfl)).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)

/-- `schemaEqSentence t u` is a schema-universe member (its de-substituted atom is in `ΓEMlocal`). -/
theorem schemaEqSentence_mem_universe (t u : (localColim s₀)[[ℕ]].Term Empty) :
    (⟨schemaEqSentence t u, hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ :=
  Set.mem_biUnion
    (locDeEqAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaSupport t u) (t := t) (u := u)
      (ht := Finset.subset_union_left) (hu := Finset.subset_union_right))
    ⟨(schemaSupport t u).orderEmbOfFin rfl, rfl⟩

/-- **Canonical-support schema equality** on closed `(localColim s₀)[[ℕ]]` terms: `t ≈ u` iff the
completed theory contains the encoded equality sentence. -/
def SchemaTermEq (t u : (localColim s₀)[[ℕ]].Term Empty) : Prop :=
  schemaEqSentence t u ∈ schemaCompletionTheory (schemaEnumeration s₀) hM

/-- **The shared body-extraction engine.** A finite fragment of `Tσ` is `MarkerHenkinConsistent`,
so it has a body: a source interpretation `(σ, h)` realizing every member. Every equality law
derives its contradiction from this. -/
theorem exists_body_of_subset (F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω))
    (hF : ∀ τ ∈ F, τ ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ (σ : ℕ → M) (h : ℕ → M), ∀ τ ∈ F,
      realizeWith σ h τ (Empty.elim : Empty → M) Fin.elim0 := by
  obtain ⟨S, H, _, _, hcof⟩ :=
    (schemaCompletionTheorySpec hM).finite_consistent F hF
  obtain ⟨α, _, _, e, hsat⟩ := hcof 0 (Ordinal.omega_pos 1)
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  obtain ⟨h, hh⟩ := hsat σ hmono hrange
  exact ⟨σ, h, hh⟩

omit [LinearOrder M] [WellFoundedLT M] in
/-- The de-substituted equality atom of a term with itself realizes to `True` (reflexivity of the
underlying `=`), on any valuation. -/
theorem locDeEqAtom_self_realize {S : Finset ℕ} (t : (localColim s₀)[[ℕ]].Term Empty)
    (ht : locJSupport (localColim s₀) ℕ t ⊆ S) (w : Fin S.card → M) :
    (locDeEqAtom (localColim s₀) ℕ S t t ht ht).Realize (Empty.elim : Empty → M) w := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal]

omit [LinearOrder M] [WellFoundedLT M] in
/-- **The σ-generalization of `locDeTermFin_realize`** (specialized to `J := ℕ`): the de-substituted
term, realized on the tuple of `σ`-values of its support, equals the closed term realized under the
`σ`-constant interpretation. Unlike `locDeTermFin_realize`, the interpretation `σ` is arbitrary (not
a deep `a`-tuple) — exactly what the body from `exists_body_of_subset` supplies. Adapts the
`locDeTermFin_realize_superset` pattern (`restrictVar` + `constantsToVars` +
`realize_eq_of_eq_on_varFinset` + `orderEmbOfFin_deepRank`). -/
theorem locDeTermFin_realize_constInterp_nat (σ : ℕ → M) {S : Finset ℕ}
    (t : (localColim s₀)[[ℕ]].Term Empty) (hsub : locJSupport (localColim s₀) ℕ t ⊆ S) :
    (locDeTermFin (localColim s₀) ℕ S t hsub).realize
        (fun i : Fin S.card => σ (S.orderEmbOfFin rfl i))
      = letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
        t.realize (Empty.elim : Empty → M) := by
  classical
  let : (constantsOn ℕ).Structure M := constantsOn.structure σ
  have hRHS : t.realize (Empty.elim : Empty → M)
      = t.constantsToVars.realize (Sum.elim σ (Empty.elim : Empty → M)) :=
    (Term.realize_constantsToVars (t := t) (v := Empty.elim)).symm
  have hLHS : (locDeTermFin (localColim s₀) ℕ S t hsub).realize
        (fun i : Fin S.card => σ (S.orderEmbOfFin rfl i))
      = (locDeTermPos (localColim s₀) ℕ S t).realize
        (fun n => if h : n < S.card then σ (S.orderEmbOfFin rfl ⟨n, h⟩) else σ 0) := by
    rw [locDeTermFin]
    refine Term.realize_restrictVar
      (fun n => if h : n < S.card then σ (S.orderEmbOfFin rfl ⟨n, h⟩) else σ 0) (fun x => ?_)
    simp only [dite_eq_left (Finset.mem_range.mp
      (locDeTermPos_varFinset_subset (Λ := localColim s₀) (J := ℕ) hsub x.2))]
  rw [hRHS, hLHS, locDeTermPos, Term.realize_relabel]
  apply Term.realize_eq_of_eq_on_varFinset
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp
    (locConstantsToVars_varFinset_subset (localColim s₀) ℕ t hx)
  have hjS : j ∈ S := hsub hj
  have hlt : deepRank ℕ S j < S.card := deepRank_lt_card (J := ℕ) hjS
  -- `dif_pos` synthesizes its own `Decidable` instance and no longer matches the one in the goal;
  -- `dite_eq_left` takes it implicitly, so the branch selection happens in a standalone equation.
  have hdite : (if h : deepRank ℕ S j < S.card then σ (S.orderEmbOfFin rfl ⟨deepRank ℕ S j, h⟩)
      else σ 0) = σ j := by
    rw [dite_eq_left hlt, orderEmbOfFin_deepRank ℕ S rfl hjS hlt]
  simp only [Function.comp_apply, Sum.elim_inl]
  exact hdite

/-- **Reflexivity.** `t ≈ t`: the theory decides `schemaEqSentence t t`; the negative sign is
impossible because any source body would have to realize `¬(t = t)`. -/
theorem schemaTermEq_refl (t : (localColim s₀)[[ℕ]].Term Empty) : SchemaTermEq hM t t := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _ (schemaEqSentence_mem_universe t t)
    with hpos | hneg
  · exact hpos
  · exfalso
    obtain ⟨σ, h, hbody⟩ := exists_body_of_subset hM {(schemaEqSentence t t).not}
      (fun τ hτ => by rw [Finset.mem_singleton] at hτ; exact hτ ▸ hneg)
    have hneg' := hbody (schemaEqSentence t t).not (Finset.mem_singleton_self _)
    rw [realizeWith_not] at hneg'
    exact hneg' (by
      rw [schemaEqSentence, realizeWith_templateSentence]
      exact locDeEqAtom_self_realize t Finset.subset_union_left _)

omit [LinearOrder M] [WellFoundedLT M] in
/-- **The exported equality bridge.** Under a body interpretation `(σ, h)`, `schemaEqSentence t u`
is realized iff `t` and `u` have the same `σ`-value — the semantically meaningful form every
equality law consumes. -/
theorem realize_schemaEqSentence_iff (σ h : ℕ → M) (t u : (localColim s₀)[[ℕ]].Term Empty) :
    realizeWith σ h (schemaEqSentence t u) (Empty.elim : Empty → M) Fin.elim0 ↔
      letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
      t.realize (Empty.elim : Empty → M) = u.realize (Empty.elim : Empty → M) := by
  rw [schemaEqSentence, realizeWith_templateSentence]
  simp only [locDeEqAtom]
  rw [canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel, Term.realize_relabel,
    Sum.elim_comp_inr]
  -- Term mode: the support proofs carried by `schemaEqSentence` are stated against
  -- `locJSupport t ∪ locJSupport u`, while the goal spells the `Finset` as `schemaSupport t u`,
  -- so the goal is not type-correct at `implicit` transparency and `rw` cannot fire.
  exact iff_of_eq (congrArg₂ (· = ·)
    (locDeTermFin_realize_constInterp_nat (S := schemaSupport t u) σ t Finset.subset_union_left)
    (locDeTermFin_realize_constInterp_nat (S := schemaSupport t u) σ u Finset.subset_union_right))

/-- **Symmetry.** `t ≈ u → u ≈ t`: a body realizing `t = u` and `¬(u = t)` contradicts `Eq.symm`. -/
theorem schemaTermEq_symm {t u : (localColim s₀)[[ℕ]].Term Empty} (h : SchemaTermEq hM t u) :
    SchemaTermEq hM u t := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _ (schemaEqSentence_mem_universe u t)
    with hpos | hneg
  · exact hpos
  · exfalso
    classical
    obtain ⟨σ, hh, hbody⟩ := exists_body_of_subset hM
      {schemaEqSentence t u, (schemaEqSentence u t).not} (fun τ hτ => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hτ
        rcases hτ with rfl | rfl
        · exact h
        · exact hneg)
    have h1 := hbody (schemaEqSentence t u) (Finset.mem_insert_self _ _)
    have h2 := hbody (schemaEqSentence u t).not
      (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
    rw [realize_schemaEqSentence_iff] at h1
    rw [realizeWith_not, realize_schemaEqSentence_iff] at h2
    exact h2 h1.symm

/-- **Transitivity.** `t ≈ u → u ≈ v → t ≈ v`: a body realizing `t = u`, `u = v`, `¬(t = v)`
contradicts `Eq.trans`. -/
theorem schemaTermEq_trans {t u v : (localColim s₀)[[ℕ]].Term Empty}
    (h1 : SchemaTermEq hM t u) (h2 : SchemaTermEq hM u v) : SchemaTermEq hM t v := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _ (schemaEqSentence_mem_universe t v)
    with hpos | hneg
  · exact hpos
  · exfalso
    classical
    obtain ⟨σ, hh, hbody⟩ := exists_body_of_subset hM
      {schemaEqSentence t u, schemaEqSentence u v, (schemaEqSentence t v).not} (fun τ hτ => by
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hτ
        rcases hτ with rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact hneg)
    have ha := hbody (schemaEqSentence t u) (Finset.mem_insert_self _ _)
    have hb := hbody (schemaEqSentence u v)
      (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_insert_self _ _))
    have hc := hbody (schemaEqSentence t v).not (by
      rw [Finset.mem_insert, Finset.mem_insert]; exact Or.inr (Or.inr (Finset.mem_singleton_self _)))
    rw [realize_schemaEqSentence_iff] at ha hb
    rw [realizeWith_not, realize_schemaEqSentence_iff] at hc
    exact hc (ha.trans hb)

/-- **Function congruence.** If `ts i ≈ us i` for every argument, then `f ts ≈ f us`: a body
realizing all the argument equalities and `¬(f ts = f us)` contradicts the function interpretation
respecting equal arguments. This makes the quotient's `funMap` well-defined. -/
theorem schemaTermEq_func {n : ℕ} (f : (localColim s₀)[[ℕ]].Functions n)
    (ts us : Fin n → (localColim s₀)[[ℕ]].Term Empty)
    (h : ∀ i, SchemaTermEq hM (ts i) (us i)) :
    SchemaTermEq hM (Term.func f ts) (Term.func f us) := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _
    (schemaEqSentence_mem_universe (Term.func f ts) (Term.func f us)) with hpos | hneg
  · exact hpos
  · exfalso
    classical
    obtain ⟨σ, hh, hbody⟩ := exists_body_of_subset hM
      (insert (schemaEqSentence (Term.func f ts) (Term.func f us)).not
        (Finset.image (fun i => schemaEqSentence (ts i) (us i)) Finset.univ))
      (fun τ hτ => by
        rw [Finset.mem_insert, Finset.mem_image] at hτ
        rcases hτ with rfl | ⟨i, _, rfl⟩
        · exact hneg
        · exact h i)
    have hc := hbody (schemaEqSentence (Term.func f ts) (Term.func f us)).not
      (Finset.mem_insert_self _ _)
    rw [realizeWith_not, realize_schemaEqSentence_iff] at hc
    refine hc ?_
    have hi : ∀ i, letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
        (ts i).realize (Empty.elim : Empty → M) = (us i).realize Empty.elim := fun i => by
      have := hbody (schemaEqSentence (ts i) (us i))
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      rwa [realize_schemaEqSentence_iff] at this
    simp only [Term.realize_func]
    exact congrArg _ (funext hi)

/-! ### The relation interface (`schemaRelSentence` + well-definedness) -/

/-- The canonical finite support of a relation atom over a tuple of closed schema terms. -/
def schemaRelSupport {l : ℕ} (ts : Fin l → (localColim s₀)[[ℕ]].Term Empty) : Finset ℕ :=
  Finset.univ.biUnion fun i => locJSupport (localColim s₀) ℕ (ts i)

omit [(localColim s₀).Structure M] [LinearOrder M] [WellFoundedLT M] in
theorem locJSupport_subset_schemaRelSupport {l : ℕ}
    (ts : Fin l → (localColim s₀)[[ℕ]].Term Empty) (i : Fin l) :
    locJSupport (localColim s₀) ℕ (ts i) ⊆ schemaRelSupport ts := fun _ hj =>
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩

/-- The lifted `templateSentence` of the de-substituted relation atom `locDeRelAtom` at the
canonical support — the schema-universe sentence that encodes "`R ts`". -/
def schemaRelSentence {l : ℕ} (R : (localColim s₀).Relations l)
    (ts : Fin l → (localColim s₀)[[ℕ]].Term Empty) :
    ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω :=
  (Lomega1omegaTemplate.templateSentence
      (locDeRelAtom (localColim s₀) ℕ (schemaRelSupport ts) R ts
        (locJSupport_subset_schemaRelSupport ts))
      ((schemaRelSupport ts).orderEmbOfFin rfl)).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)

/-- `schemaRelSentence R ts` is a schema-universe member. -/
theorem schemaRelSentence_mem_universe {l : ℕ} (R : (localColim s₀).Relations l)
    (ts : Fin l → (localColim s₀)[[ℕ]].Term Empty) :
    (⟨schemaRelSentence R ts, hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ :=
  Set.mem_biUnion
    (locDeRelAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaRelSupport ts) R ts
      (locJSupport_subset_schemaRelSupport ts))
    ⟨(schemaRelSupport ts).orderEmbOfFin rfl, rfl⟩

omit [LinearOrder M] [WellFoundedLT M] in
/-- **The exported relation bridge.** Under a body interpretation `(σ, h)`, `schemaRelSentence R ts`
is realized iff `R` holds in `M` on the `σ`-values of the terms. -/
theorem realize_schemaRelSentence_iff (σ h : ℕ → M) {l : ℕ} (R : (localColim s₀).Relations l)
    (ts : Fin l → (localColim s₀)[[ℕ]].Term Empty) :
    realizeWith σ h (schemaRelSentence R ts) (Empty.elim : Empty → M) Fin.elim0 ↔
      letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
      Structure.RelMap R fun i => (ts i).realize (Empty.elim : Empty → M) := by
  let : (constantsOn ℕ).Structure M := constantsOn.structure σ
  rw [schemaRelSentence, realizeWith_templateSentence, locDeRelAtom, canonRelAtom,
    BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, locDeTermFin_realize_constInterp_nat]

/-- **Canonical-support schema relation membership** on tuples of closed schema terms. -/
def SchemaTermRel {l : ℕ} (R : (localColim s₀).Relations l)
    (ts : Fin l → (localColim s₀)[[ℕ]].Term Empty) : Prop :=
  schemaRelSentence R ts ∈ schemaCompletionTheory (schemaEnumeration s₀) hM

/-- **Relation well-definedness.** Argument-wise `SchemaTermEq` preserves `SchemaTermRel`: a body
realizing `R ts`, all argument equalities, and `¬(R us)` contradicts `M`'s `RelMap` respecting
equal arguments. This makes the quotient's `RelMap` well-defined. -/
theorem schemaTermRel_congr {l : ℕ} (R : (localColim s₀).Relations l)
    {ts us : Fin l → (localColim s₀)[[ℕ]].Term Empty}
    (h : ∀ i, SchemaTermEq hM (ts i) (us i)) (hR : SchemaTermRel hM R ts) :
    SchemaTermRel hM R us := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _
    (schemaRelSentence_mem_universe R us) with hpos | hneg
  · exact hpos
  · exfalso
    classical
    obtain ⟨σ, hh, hbody⟩ := exists_body_of_subset hM
      (insert (schemaRelSentence R ts) (insert (schemaRelSentence R us).not
        (Finset.image (fun i => schemaEqSentence (ts i) (us i)) Finset.univ)))
      (fun τ hτ => by
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_image] at hτ
        rcases hτ with rfl | rfl | ⟨i, _, rfl⟩
        · exact hR
        · exact hneg
        · exact h i)
    have ha := hbody (schemaRelSentence R ts) (Finset.mem_insert_self _ _)
    have hc := hbody (schemaRelSentence R us).not
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    rw [realize_schemaRelSentence_iff] at ha
    rw [realizeWith_not, realize_schemaRelSentence_iff] at hc
    refine hc ?_
    have hi : ∀ i, letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
        (ts i).realize (Empty.elim : Empty → M) = (us i).realize Empty.elim := fun i => by
      have := hbody (schemaEqSentence (ts i) (us i))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
      rwa [realize_schemaEqSentence_iff] at this
    let : (constantsOn ℕ).Structure M := constantsOn.structure σ
    rw [show (fun i => Term.realize (Empty.elim : Empty → M) (us i))
        = fun i => Term.realize (Empty.elim : Empty → M) (ts i) from (funext hi).symm]
    exact ha

/-! ### The quotient term model -/

/-- The setoid on closed schema terms induced by the completed theory. -/
def schemaTermSetoid : Setoid ((localColim s₀)[[ℕ]].Term Empty) where
  r := SchemaTermEq hM
  iseqv := ⟨schemaTermEq_refl hM, schemaTermEq_symm hM, schemaTermEq_trans hM⟩

/-- **The schema term-model carrier**: closed `(localColim s₀)[[ℕ]]` terms quotiented by the
completed theory's equality. An `abbrev`, so `Quotient` lemmas and dot-notation apply
transparently (the `FSentence` precedent). -/
abbrev SchemaTermCarrier : Type := Quotient (schemaTermSetoid (s₀ := s₀) (M := M) hM)

/-- The class of a closed schema term. -/
abbrev SchemaTermCarrier.mk (t : (localColim s₀)[[ℕ]].Term Empty) :
    SchemaTermCarrier (s₀ := s₀) (M := M) hM :=
  Quotient.mk (schemaTermSetoid hM) t

/-- The carrier is inhabited (class of the first sequence constant `d₀`). -/
instance : Nonempty (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
  ⟨SchemaTermCarrier.mk hM (henkinConst (L := localColim s₀) 0)⟩

/-- Two terms have the same class iff the completed theory contains their equality sentence. -/
theorem SchemaTermCarrier.mk_eq_mk_iff {t u : (localColim s₀)[[ℕ]].Term Empty} :
    SchemaTermCarrier.mk hM t = SchemaTermCarrier.mk hM u ↔ SchemaTermEq hM t u := by
  rw [SchemaTermCarrier.mk, SchemaTermCarrier.mk, Quotient.eq]
  rfl

/-- The representative of a class is equivalent to the term that formed it. -/
theorem SchemaTermCarrier.mk_out_eq (t : (localColim s₀)[[ℕ]].Term Empty) :
    SchemaTermEq hM (SchemaTermCarrier.mk hM t).out t :=
  Quotient.exact (Quotient.out_eq (SchemaTermCarrier.mk hM t))

/-- **The `(localColim s₀)[[ℕ]]`-structure on the carrier**: `funMap` by term formation on
`Quotient.out` representatives; `RelMap` (the constant layer adds no relations) by the completed
theory's relation membership on representatives. Well-definedness on classes is exposed by the
atomic API below (via `schemaTermEq_func`/`schemaTermRel_congr`), not baked into the definition. -/
@[reducible] noncomputable def schemaTermStructure :
    (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) where
  funMap f xs := SchemaTermCarrier.mk hM (Term.func f fun i => (xs i).out)
  RelMap R xs :=
    match R with
    | Sum.inl R => SchemaTermRel hM R fun i => (xs i).out
    | Sum.inr e => e.elim

/-- **Atomic API, function symbols**: `funMap` computes on classes — applying an interpreted symbol
to classes gives the class of the function term (well-definedness via `schemaTermEq_func`). -/
theorem schemaTerm_funMap_mk {n : ℕ} (f : (localColim s₀)[[ℕ]].Functions n)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    @Structure.funMap _ _ (schemaTermStructure (s₀ := s₀) (M := M) hM) n f
        (fun i => SchemaTermCarrier.mk hM (ts i)) = SchemaTermCarrier.mk hM (Term.func f ts) := by
  apply Quotient.sound
  apply schemaTermEq_func hM f
  exact fun i => SchemaTermCarrier.mk_out_eq hM (ts i)

/-- **Atomic API, terms**: every closed term realizes in the term model to its own class. -/
theorem schemaTerm_realize_eq_mk (t : (localColim s₀)[[ℕ]].Term Empty) :
    letI := schemaTermStructure (s₀ := s₀) (M := M) hM
    t.realize (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      = SchemaTermCarrier.mk hM t := by
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  induction t with
  | var x => exact x.elim
  | func f ts ih =>
    show Structure.funMap f (fun i => (ts i).realize Empty.elim) = _
    rw [funext ih]
    exact schemaTerm_funMap_mk hM f ts

/-- **Atomic API, relations**: a base relation holds in the term model on classes iff the completed
theory contains the relation sentence (well-definedness via `schemaTermRel_congr`). -/
theorem schemaTerm_relMap_mk_iff {l : ℕ} (R : (localColim s₀).Relations l)
    (ts : Fin l → (localColim s₀)[[ℕ]].Term Empty) :
    @Structure.RelMap _ _ (schemaTermStructure (s₀ := s₀) (M := M) hM) l
        (Sum.inl R : (localColim s₀)[[ℕ]].Relations l)
        (fun i => SchemaTermCarrier.mk hM (ts i)) ↔
      SchemaTermRel hM R ts := by
  show SchemaTermRel hM R (fun i => (SchemaTermCarrier.mk hM (ts i)).out) ↔ _
  constructor
  · exact schemaTermRel_congr hM R fun i => SchemaTermCarrier.mk_out_eq hM (ts i)
  · exact schemaTermRel_congr hM R fun i =>
      schemaTermEq_symm hM (SchemaTermCarrier.mk_out_eq hM (ts i))

/-- **The canonical schema sequence** in the term model: the classes of the sequence constants
`d₀, d₁, …`. This is the sequence the witnessed template (`TailTemplateOmegaWitnessed`) will be
established for. -/
noncomputable def schemaSeq (n : ℕ) : SchemaTermCarrier (s₀ := s₀) (M := M) hM :=
  SchemaTermCarrier.mk hM (henkinConst (L := localColim s₀) n)

/-! ### The general schema-formula interface and semantic sign transport (5b-3 substrate)

The restricted truth lemma treats equality/relation sentences as special cases of ONE
formula-application encoding: `schemaFormulaSentence φ ts`, the lifted template of the general
de-substituted formula `locDeForm` at the canonical support `schemaRelSupport ts`. Its
source-semantics bridge `realize_schemaFormulaSentence_iff` is the semantic engine of the truth
lemma. The sign-transport lemmas then move theory membership across ANY semantic equivalence of
universe sentences (support changes, canonical deForms, normalization to the atomic API) by one
body extraction — never by re-running quotient inductions: if the two sentences carried opposite
signs, `exists_body_of_subset` would realize both the source and the negated target under one
interpretation pair, contradicting the equivalence. -/

/-- The lifted `templateSentence` of the general de-substituted formula `locDeForm` at the
canonical support — the schema-universe sentence that encodes "`φ` holds on the closed terms
`ts`". `schemaEqSentence`/`schemaRelSentence` are the atomic special cases of this shape. -/
def schemaFormulaSentence {n : ℕ} (φ : (localColim s₀).BoundedFormulaω Empty n)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω :=
  (Lomega1omegaTemplate.templateSentence
      (locDeForm (localColim s₀) ℕ (schemaRelSupport ts) φ ts
        (locJSupport_subset_schemaRelSupport ts))
      ((schemaRelSupport ts).orderEmbOfFin rfl)).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)

/-- `schemaFormulaSentence φ ts` of a colimit-family member is a schema-universe member (its
de-substituted formula is in the `canonDeForms` component of `ΓEMlocal`). -/
theorem schemaFormulaSentence_mem_universe {n : ℕ}
    {φ : (localColim s₀).BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    (⟨schemaFormulaSentence φ ts,
        hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ := by
  apply Set.mem_biUnion
    (locDeForm_mem_ΓEMlocal ℕ s₀ (schemaRelSupport ts) hφ ts
      (locJSupport_subset_schemaRelSupport ts))
  exact ⟨(schemaRelSupport ts).orderEmbOfFin rfl, rfl⟩

omit [LinearOrder M] [WellFoundedLT M] in
/-- **The exported formula bridge — the truth lemma's semantic engine.** Under a body
interpretation `(σ, h)`, `schemaFormulaSentence φ ts` is realized iff `φ` holds in `M` on the
`σ`-values of the closed terms. Generalizes `realize_schemaEqSentence_iff`/
`realize_schemaRelSentence_iff` to arbitrary formulas via the same σ-generalized term bridge. -/
theorem realize_schemaFormulaSentence_iff (σ h : ℕ → M) {n : ℕ}
    (φ : (localColim s₀).BoundedFormulaω Empty n)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    realizeWith σ h (schemaFormulaSentence φ ts) (Empty.elim : Empty → M) Fin.elim0 ↔
      letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
      φ.Realize (Empty.elim : Empty → M)
        (fun i => (ts i).realize (Empty.elim : Empty → M)) := by
  let : (constantsOn ℕ).Structure M := constantsOn.structure σ
  rw [schemaFormulaSentence, realizeWith_templateSentence, locDeForm, canonDeForm,
    BoundedFormulaω.realize_relabel_sumInr_zero]
  simp only [Formulaω.realize_def, BoundedFormulaω.realize_subst]
  refine (realize_openBounds φ _).trans ?_
  apply iff_of_eq
  congr 1
  funext i
  exact locDeTermFin_realize_constInterp_nat σ (ts i)
    (locJSupport_subset_schemaRelSupport ts i)

/-- **Directional semantic sign transport.** If every body interpretation realizing
`schemaLift ψ t` also realizes `schemaLift χ u`, then theory membership transfers — only the
TARGET's universe membership is needed (to ask for its sign). If the target were negative, one
body would realize the source and the negated target, contradicting the implication. -/
theorem schemaLift_mem_of_semantic_imp {m : ℕ}
    {ψ : (localColim s₀).BoundedFormulaω Empty m} (t : Fin m ↪o ℕ)
    {n : ℕ} {χ : (localColim s₀).BoundedFormulaω Empty n}
    (hχ : (⟨n, χ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (u : Fin n ↪o ℕ)
    (hsem : ∀ σ h : ℕ → M,
      realizeWith σ h (schemaLift ψ t) (Empty.elim : Empty → M) Fin.elim0 →
        realizeWith σ h (schemaLift χ u) (Empty.elim : Empty → M) Fin.elim0)
    (hmem : schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    schemaLift χ u ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _
    (schemaLift_mem_universe hχ u) with hv | hnv
  · exact hv
  · exfalso
    classical
    obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
      {schemaLift ψ t, (schemaLift χ u).not} (fun τ hτ => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hτ
        rcases hτ with rfl | rfl
        · exact hmem
        · exact hnv)
    have h1 := hbody (schemaLift ψ t) (Finset.mem_insert_self _ _)
    have h2 := hbody (schemaLift χ u).not
      (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
    rw [realizeWith_not] at h2
    exact h2 (hsem σ w h1)

/-- **Semantic sign transport.** Two universe sentences semantically equivalent under every body
interpretation receive the same sign from the completed theory. The workhorse for normalizing
between `schemaFormulaSentence`, the atomic sentences, and canonical deForms in the truth
lemma — one body extraction per equivalence, no quotient induction. -/
theorem schema_mem_iff_of_semantic_iff {m : ℕ}
    {ψ : (localColim s₀).BoundedFormulaω Empty m}
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t : Fin m ↪o ℕ)
    {n : ℕ} {χ : (localColim s₀).BoundedFormulaω Empty n}
    (hχ : (⟨n, χ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (u : Fin n ↪o ℕ)
    (hsem : ∀ σ h : ℕ → M,
      realizeWith σ h (schemaLift ψ t) (Empty.elim : Empty → M) Fin.elim0 ↔
        realizeWith σ h (schemaLift χ u) (Empty.elim : Empty → M) Fin.elim0) :
    schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift χ u ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  ⟨schemaLift_mem_of_semantic_imp hM t hχ u (fun σ h => (hsem σ h).mp),
    schemaLift_mem_of_semantic_imp hM u hψ t (fun σ h => (hsem σ h).mpr)⟩

end FirstOrder.Language
