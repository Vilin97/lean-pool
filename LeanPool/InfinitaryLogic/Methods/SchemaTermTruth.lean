/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.SchemaTermModel
/-!
# Layer 7b, checkpoint 5b-3: the restricted schema truth lemma

The truth lemma for the schema term model (`SchemaTermCarrier`/`schemaTermStructure`): realization
of a staged-family formula in the quotient, on the classes of closed terms, is equivalent to
membership of its `schemaFormulaSentence` in the completed theory `Tσ`. Restricted — the induction
runs over the staged family `Γlocal s₀ (k+1)` (the `LocalEMContext.truthLemmaStage` organization),
never over arbitrary formulas.

This file opens with the **`all`-case input**: `locSkWitness_universal_constInterp_nat`, the
σ-generalization of `locSkWitness_universal` from the deep interpretations `locDeepInterp` to an
arbitrary constant interpretation `σ : ℕ → M` (the shape a Marker certificate body supplies). The
proof is the same contrapositive Hilbert-choice argument — `localSkolem_funMap_spec` needs no
tuple-shape hypothesis, so nothing about `σ` is used beyond interpreting the argument terms.
-/

namespace FirstOrder.Language

open Cardinal

/-! ## The `all`-case Skolem input -/

/-- **Arbitrary-constant local Skolem-witness universality**: under any constant interpretation
`σ : ℕ → M` of the sequence constants, if the body `ψ` of a staged universal `∀ψ ∈ Γlocal s₀ k`
holds at the `σ`-value of its Skolem-witness term, it holds at every `M`-element. Generalizes
`locSkWitness_universal` from the deep tuples `locDeepInterp` to the interpretations a Marker
certificate body supplies. -/
theorem locSkWitness_universal_constInterp_nat
    (s₀ : LocalStage) {M : Type} [s₀.Lang.Structure M] [Nonempty M]
    (σ : ℕ → M) {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ k) ψ).Realize (Empty.elim : Empty → M)
        (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M))
          ((locSkWitnessTerm s₀ ℕ h ts).realize (Empty.elim : Empty → M))) →
      ∀ x : M,
        (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ k) ψ).Realize (Empty.elim : Empty → M)
          (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M)) x) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  let : (constantsOn ℕ).Structure M := constantsOn.structure σ
  simp only [realize_map_LlocalInclusion]
  intro hψw x
  by_contra hcon
  have hex : ∃ b, (ψ.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M)) b) :=
    ⟨x, by rw [BoundedFormulaω.realize_not]; exact hcon⟩
  have hspec : (ψ.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M))
        (Structure.funMap
          (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
          (skolemNeedSymbol h) (fun i => (ts i).realize (Empty.elim : Empty → M)))) :=
    localSkolem_funMap_spec (skolemNeedSymbol h) _ hex
  rw [show Structure.funMap
        (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
        (skolemNeedSymbol h) (fun i => (ts i).realize (Empty.elim : Empty → M))
      = (locSkWitnessTerm s₀ ℕ h ts).realize (Empty.elim : Empty → M) by
        rw [locSkWitnessTerm, Term.realize_func]
        rfl,
    BoundedFormulaω.realize_not] at hspec
  exact hspec hψw

/-! ## The truth-lemma helper layer

Three small bridges the induction consumes at every case: the sign flip on universe members
(negation membership ↔ non-membership), the carrier term bridge (open terms realized at classes
are classes of closed substitution instances), and the substitution/valuation exchange for closed
instances in an arbitrary structure. -/

section Helpers

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- **Sign flip on the universe.** For a universe member, the completed theory contains its
negation iff it does not contain the sentence itself (forward: a two-element fragment of `Tσ`
would be a consistent set containing a sentence and its negation; backward: completeness). -/
theorem schemaCompletionTheory_not_mem_iff
    (τ : FSentence (L'' := localColim s₀) (J := ℕ)) (hτ : τ ∈ schemaFSentenceUniverse s₀) :
    τ.1.not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      τ.1 ∉ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  classical
  constructor
  · intro hneg hpos
    refine markerHenkinConsistent_not_mem_and_not_mem
      ((schemaCompletionTheorySpec hM).finite_consistent {τ.1, τ.1.not} fun τ' hτ' => ?_) τ.1
      ⟨Finset.mem_insert_self _ _, by
        rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _)⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hτ'
    rcases hτ' with rfl | rfl
    · exact hpos
    · exact hneg
  · intro hnot
    rcases (schemaCompletionTheorySpec hM).complete_on_universe τ hτ with hpos | hneg
    · exact absurd hpos hnot
    · exact hneg

/-- **The carrier term bridge**: an open `(localColim s₀)[[ℕ]]`-term realized in the schema term
model at class-valued variables is the class of its closed substitution instance. -/
private theorem schemaTerm_realize_sumElim_mk {n : ℕ}
    (u : (localColim s₀)[[ℕ]].Term (Empty ⊕ Fin n))
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    letI := schemaTermStructure (s₀ := s₀) (M := M) hM
    u.realize (Sum.elim (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        fun i => SchemaTermCarrier.mk hM (ts i))
      = SchemaTermCarrier.mk hM (u.subst (Sum.elim (fun e => e.elim) ts)) := by
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  induction u with
  | var x =>
    rcases x with e | i
    · exact e.elim
    · rfl
  | func f us ih =>
    show Structure.funMap f _ = _
    rw [funext ih]
    exact schemaTerm_funMap_mk hM f _

omit [(localColim s₀).Structure M] [LinearOrder M] [WellFoundedLT M] in
/-- **Substitution/valuation exchange**: a closed substitution instance realizes (in any
structure) to the open term realized at the values of the substituted terms. -/
private theorem realize_subst_sumElim {N : Type} [(localColim s₀)[[ℕ]].Structure N] {n : ℕ}
    (u : (localColim s₀)[[ℕ]].Term (Empty ⊕ Fin n))
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    (u.subst (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → N)
      = u.realize (Sum.elim (Empty.elim : Empty → N) fun i => (ts i).realize Empty.elim) := by
  rw [Term.realize_subst]
  congr 1
  funext x
  rcases x with e | i
  · exact e.elim
  · rfl

end Helpers

/-! ## The staged restricted truth lemma -/

section StagedTruthLemma

variable {s₀ : LocalStage} {M : Type} [s₀.Lang.Structure M] [Nonempty M] [LinearOrder M]
  [WellFoundedLT M]


private abbrev SchemaTruthStage
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n : ℕ}
    (ψ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) : Prop :=
  letI : (localColim s₀).Structure M := localColimStructure s₀
  (⟨n, ψ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) ∈ Γlocal s₀ (k + 1) →
    ∀ ts : Fin n → (localColim s₀)[[ℕ]].Term Empty,
      (@BoundedFormulaω.Realize ((localColim s₀)[[ℕ]])
          (SchemaTermCarrier (s₀ := s₀) (M := M) hM) (schemaTermStructure hM) Empty n
          ((BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ).mapLanguage
            (lhomWithConstants (localColim s₀) ℕ))
          (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
          (fun i => SchemaTermCarrier.mk hM (ts i)) ↔
        schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ) ts
          ∈ schemaCompletionTheory (schemaEnumeration s₀) hM)

private theorem schemaTruthStage_falsum
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n : ℕ} :
    SchemaTruthStage hM k (.falsum : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro _ ts
  simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.realize_falsum, false_iff]
  intro hT
  obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
    {schemaFormulaSentence (BoundedFormulaω.falsum.mapLanguage (LlocalInclusion s₀ (k + 1))) ts}
    (fun τ hτ => by rw [Finset.mem_singleton] at hτ; exact hτ ▸ hT)
  have hf := hbody _ (Finset.mem_singleton_self _)
  rw [realize_schemaFormulaSentence_iff] at hf
  exact hf

private theorem schemaTruthStage_equal
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n : ℕ}
    (t₁ t₂ : (Llocal s₀ (k + 1)).Term (Empty ⊕ Fin n)) :
    SchemaTruthStage hM k (.equal t₁ t₂) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro hmem ts
  rw [show ((BoundedFormulaω.equal t₁ t₂).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
        (lhomWithConstants (localColim s₀) ℕ)
      = BoundedFormulaω.equal
          ((lhomWithConstants (localColim s₀) ℕ).onTerm
            ((LlocalInclusion s₀ (k + 1)).onTerm t₁))
          ((lhomWithConstants (localColim s₀) ℕ).onTerm
            ((LlocalInclusion s₀ (k + 1)).onTerm t₂)) from rfl,
    BoundedFormulaω.realize_equal, schemaTerm_realize_sumElim_mk hM _ ts,
    schemaTerm_realize_sumElim_mk hM _ ts, SchemaTermCarrier.mk_eq_mk_iff hM]
  refine schema_mem_iff_of_semantic_iff hM
    (locDeEqAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaSupport _ _) _ _
      Finset.subset_union_left Finset.subset_union_right)
    ((schemaSupport _ _).orderEmbOfFin rfl)
    (locDeForm_mem_ΓEMlocal ℕ s₀ (schemaRelSupport ts)
      (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts
      (locJSupport_subset_schemaRelSupport ts))
    ((schemaRelSupport ts).orderEmbOfFin rfl)
    (fun σ w => ?_)
  let : (constantsOn ℕ).Structure M := constantsOn.structure σ
  have mid : ((((lhomWithConstants (localColim s₀) ℕ).onTerm
          ((LlocalInclusion s₀ (k + 1)).onTerm t₁)).subst
            (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → M)
        = (((lhomWithConstants (localColim s₀) ℕ).onTerm
          ((LlocalInclusion s₀ (k + 1)).onTerm t₂)).subst
            (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → M))
      ↔ ((BoundedFormulaω.equal t₁ t₂).mapLanguage (LlocalInclusion s₀ (k + 1))).Realize
          (Empty.elim : Empty → M) (fun i => (ts i).realize Empty.elim) := by
    rw [show (BoundedFormulaω.equal t₁ t₂).mapLanguage (LlocalInclusion s₀ (k + 1))
        = BoundedFormulaω.equal ((LlocalInclusion s₀ (k + 1)).onTerm t₁)
            ((LlocalInclusion s₀ (k + 1)).onTerm t₂) from rfl,
      BoundedFormulaω.realize_equal, realize_subst_sumElim, realize_subst_sumElim,
      LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ),
      LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ)]
  exact (realize_schemaEqSentence_iff σ w _ _).trans
    (mid.trans (realize_schemaFormulaSentence_iff σ w _ ts).symm)

private theorem schemaTruthStage_rel
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n l : ℕ}
    (R : (Llocal s₀ (k + 1)).Relations l)
    (args : Fin l → (Llocal s₀ (k + 1)).Term (Empty ⊕ Fin n)) :
    SchemaTruthStage hM k (.rel R args) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro hmem ts
  rw [show ((BoundedFormulaω.rel R args).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
        (lhomWithConstants (localColim s₀) ℕ)
      = BoundedFormulaω.rel
          (Sum.inl ((LlocalInclusion s₀ (k + 1)).onRelation R) :
            ((localColim s₀)[[ℕ]]).Relations _)
          (fun i => (lhomWithConstants (localColim s₀) ℕ).onTerm
            ((LlocalInclusion s₀ (k + 1)).onTerm (args i))) from rfl,
    -- Both explicit arguments are supplied: leaving `?R` open makes `rw` try to assign
    -- `Sum.inl _` to `?R : ((localColim s₀)[[ℕ]]).Relations _`, which fails at `implicit`
    -- transparency.
    BoundedFormulaω.realize_rel
      (Sum.inl ((LlocalInclusion s₀ (k + 1)).onRelation R) :
        ((localColim s₀)[[ℕ]]).Relations _)
      (fun i => (lhomWithConstants (localColim s₀) ℕ).onTerm
        ((LlocalInclusion s₀ (k + 1)).onTerm (args i)))]
  simp only [schemaTerm_realize_sumElim_mk hM]
  rw [schemaTerm_relMap_mk_iff hM]
  refine schema_mem_iff_of_semantic_iff hM
    (locDeRelAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaRelSupport _)
      ((LlocalInclusion s₀ (k + 1)).onRelation R) _
      (locJSupport_subset_schemaRelSupport _))
    ((schemaRelSupport _).orderEmbOfFin rfl)
    (locDeForm_mem_ΓEMlocal ℕ s₀ (schemaRelSupport ts)
      (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts
      (locJSupport_subset_schemaRelSupport ts))
    ((schemaRelSupport ts).orderEmbOfFin rfl)
    (fun σ w => ?_)
  let : (constantsOn ℕ).Structure M := constantsOn.structure σ
  have mid : (Structure.RelMap ((LlocalInclusion s₀ (k + 1)).onRelation R)
        fun i => (((lhomWithConstants (localColim s₀) ℕ).onTerm
            ((LlocalInclusion s₀ (k + 1)).onTerm (args i))).subst
              (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → M))
      ↔ ((BoundedFormulaω.rel R args).mapLanguage (LlocalInclusion s₀ (k + 1))).Realize
          (Empty.elim : Empty → M) (fun i => (ts i).realize Empty.elim) := by
    rw [show (BoundedFormulaω.rel R args).mapLanguage (LlocalInclusion s₀ (k + 1))
        = BoundedFormulaω.rel ((LlocalInclusion s₀ (k + 1)).onRelation R)
            (fun i => (LlocalInclusion s₀ (k + 1)).onTerm (args i)) from rfl,
      BoundedFormulaω.realize_rel]
    apply Iff.of_eq
    congr 1
    funext i
    rw [realize_subst_sumElim, LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ)]
  exact (realize_schemaRelSentence_iff σ w _ _).trans
    (mid.trans (realize_schemaFormulaSentence_iff σ w _ ts).symm)

private theorem schemaTruthStage_imp
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n : ℕ}
    (φ ψ' : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
    (ihφ : SchemaTruthStage hM k φ) (ihψ : SchemaTruthStage hM k ψ') :
    SchemaTruthStage hM k (φ.imp ψ') := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro hmem ts
  classical
  have hφmem : (⟨_, φ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
      ∈ Γlocal s₀ (k + 1) :=
    bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_insert _ _)
  have hψmem : (⟨_, ψ'⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
      ∈ Γlocal s₀ (k + 1) :=
    bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_insert_of_mem _ rfl)
  have hφu := schemaFormulaSentence_mem_universe
    (toLocalColimFormula_mem_ΓlocalColim s₀ hφmem) ts
  have hψu := schemaFormulaSentence_mem_universe
    (toLocalColimFormula_mem_ΓlocalColim s₀ hψmem) ts
  have himpu := schemaFormulaSentence_mem_universe
    (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts
  rw [show (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φ.imp ψ')).mapLanguage
        (lhomWithConstants (localColim s₀) ℕ)
      = ((BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) φ).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)).imp
        ((BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ').mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)) from rfl,
    BoundedFormulaω.realize_imp, ihφ hφmem ts, ihψ hψmem ts]
  constructor
  · intro h
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _ himpu with hpos | hneg
    · exact hpos
    · exfalso
      by_cases hφT : schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) φ) ts
          ∈ schemaCompletionTheory (schemaEnumeration s₀) hM
      · obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
          {(schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φ.imp ψ')) ts).not,
            schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ') ts}
          (fun τ hτ => by
            rw [Finset.mem_insert, Finset.mem_singleton] at hτ
            rcases hτ with rfl | rfl
            · exact hneg
            · exact h hφT)
        have h1 := hbody _ (Finset.mem_insert_self _ _)
        have h2 := hbody _
          (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h1
        rw [realize_schemaFormulaSentence_iff] at h2
        exact h1 fun _ => h2
      · obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
          {(schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φ.imp ψ')) ts).not,
            (schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) φ) ts).not}
          (fun τ hτ => by
            rw [Finset.mem_insert, Finset.mem_singleton] at hτ
            rcases hτ with rfl | rfl
            · exact hneg
            · exact (schemaCompletionTheory_not_mem_iff hM _ hφu).mpr hφT)
        have h1 := hbody _ (Finset.mem_insert_self _ _)
        have h2 := hbody _
          (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h1
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
        exact h1 fun hφr => absurd hφr h2
  · intro himp hφT
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _ hψu with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
        {schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φ.imp ψ')) ts,
          schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) φ) ts,
          (schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ') ts).not}
        (fun τ hτ => by
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hτ
          rcases hτ with rfl | rfl | rfl
          · exact himp
          · exact hφT
          · exact hneg)
      have h1 := hbody _ (Finset.mem_insert_self _ _)
      have h2 := hbody _
        (by rw [Finset.mem_insert, Finset.mem_insert]
            exact Or.inr (Or.inl rfl))
      have h3 := hbody _
        (by rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
            exact Or.inr (Or.inr rfl))
      rw [realize_schemaFormulaSentence_iff] at h1 h2
      rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h3
      exact h3 (h1 h2)

private theorem schemaTruthStage_all
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n : ℕ}
    (ψ₀ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty (n + 1))
    (ih : SchemaTruthStage hM k ψ₀) : SchemaTruthStage hM k ψ₀.all := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro hmem ts
  classical
  have hbodymem : (⟨_, ψ₀⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
      ∈ Γlocal s₀ (k + 1) :=
    bfSubformulas_subset_Γlocal_succ s₀ hmem rfl
  rw [show ((BoundedFormulaω.all ψ₀).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
        (lhomWithConstants (localColim s₀) ℕ)
      = BoundedFormulaω.all ((BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ₀).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)) from rfl,
    BoundedFormulaω.realize_all]
  constructor
  · intro hall
    have hw := hall (SchemaTermCarrier.mk hM (locSkWitnessTerm s₀ ℕ hmem ts))
    rw [show Fin.snoc (fun i => SchemaTermCarrier.mk hM (ts i))
          (SchemaTermCarrier.mk hM (locSkWitnessTerm s₀ ℕ hmem ts))
        = fun i => SchemaTermCarrier.mk hM
            ((Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts) :
              Fin _ → (localColim s₀)[[ℕ]].Term Empty) i) from
        (Fin.comp_snoc (SchemaTermCarrier.mk hM) ts
          (locSkWitnessTerm s₀ ℕ hmem ts)).symm] at hw
    have hwT := (ih hbodymem (Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts))).mp hw
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaFormulaSentence_mem_universe (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts)
      with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨σ, w', hbody⟩ := exists_body_of_subset hM
        {schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ₀)
            (Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts)),
          (schemaFormulaSentence ((BoundedFormulaω.all ψ₀).mapLanguage
            (LlocalInclusion s₀ (k + 1))) ts).not}
        (fun τ hτ => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hτ
          rcases hτ with rfl | rfl
          · exact hwT
          · exact hneg)
      have h1 := hbody _ (Finset.mem_insert_self _ _)
      have h2 := hbody _
        (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
      rw [realize_schemaFormulaSentence_iff] at h1
      rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
      let : (constantsOn ℕ).Structure M := constantsOn.structure σ
      refine h2 ?_
      intro x
      refine locSkWitness_universal_constInterp_nat s₀ σ hmem ts ?_ x
      rw [show (Fin.snoc (fun i => (ts i).realize Empty.elim)
            ((locSkWitnessTerm s₀ ℕ hmem ts).realize Empty.elim) : Fin _ → M)
          = fun i => ((Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts) :
              Fin _ → (localColim s₀)[[ℕ]].Term Empty) i).realize Empty.elim from
          (Fin.comp_snoc
            (fun t : (localColim s₀)[[ℕ]].Term Empty => t.realize (Empty.elim : Empty → M))
            ts (locSkWitnessTerm s₀ ℕ hmem ts)).symm]
      exact h1
  · intro hT
    refine Quotient.ind fun u => ?_
    rw [show Fin.snoc (fun i => SchemaTermCarrier.mk hM (ts i)) (SchemaTermCarrier.mk hM u)
        = fun i => SchemaTermCarrier.mk hM
            ((Fin.snoc ts u : Fin _ → (localColim s₀)[[ℕ]].Term Empty) i) from
        (Fin.comp_snoc (SchemaTermCarrier.mk hM) ts u).symm]
    refine (ih hbodymem (Fin.snoc ts u)).mpr ?_
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaFormulaSentence_mem_universe
        (toLocalColimFormula_mem_ΓlocalColim s₀ hbodymem) (Fin.snoc ts u)) with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨σ, w', hbody⟩ := exists_body_of_subset hM
        {schemaFormulaSentence ((BoundedFormulaω.all ψ₀).mapLanguage
            (LlocalInclusion s₀ (k + 1))) ts,
          (schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ₀)
            (Fin.snoc ts u)).not}
        (fun τ hτ => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hτ
          rcases hτ with rfl | rfl
          · exact hT
          · exact hneg)
      have h1 := hbody _ (Finset.mem_insert_self _ _)
      have h2 := hbody _
        (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
      rw [realize_schemaFormulaSentence_iff] at h1
      rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
      let : (constantsOn ℕ).Structure M := constantsOn.structure σ
      refine h2 ?_
      show (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ₀).Realize (Empty.elim : Empty → M)
        (fun i => ((Fin.snoc ts u : Fin _ → (localColim s₀)[[ℕ]].Term Empty) i).realize
          Empty.elim)
      rw [show (fun i => ((Fin.snoc ts u : Fin _ → (localColim s₀)[[ℕ]].Term Empty) i).realize
            (Empty.elim : Empty → M))
          = (Fin.snoc (fun i => (ts i).realize Empty.elim) (u.realize Empty.elim) :
              Fin _ → M) from
          Fin.comp_snoc
            (fun t : (localColim s₀)[[ℕ]].Term Empty => t.realize (Empty.elim : Empty → M))
            ts u]
      exact h1 (u.realize (Empty.elim : Empty → M))

private theorem schemaTruthStage_iSup
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n : ℕ}
    (φs : ℕ → (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
    (ih : ∀ i, SchemaTruthStage hM k (φs i)) :
    SchemaTruthStage hM k (.iSup φs) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro hmem ts
  classical
  rw [show ((BoundedFormulaω.iSup φs).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
        (lhomWithConstants (localColim s₀) ℕ)
      = BoundedFormulaω.iSup (fun i => (BoundedFormulaω.mapLanguage
          (LlocalInclusion s₀ (k + 1)) (φs i)).mapLanguage
            (lhomWithConstants (localColim s₀) ℕ)) from rfl,
    BoundedFormulaω.realize_iSup]
  constructor
  · rintro ⟨i, hi⟩
    have hiT := (ih i (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self i)) ts).mp hi
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaFormulaSentence_mem_universe (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts)
      with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
        {schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φs i)) ts,
          (schemaFormulaSentence ((BoundedFormulaω.iSup φs).mapLanguage
            (LlocalInclusion s₀ (k + 1))) ts).not}
        (fun τ hτ => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hτ
          rcases hτ with rfl | rfl
          · exact hiT
          · exact hneg)
      have h1 := hbody _ (Finset.mem_insert_self _ _)
      have h2 := hbody _
        (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
      rw [realize_schemaFormulaSentence_iff] at h1
      rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
      exact h2 ⟨i, h1⟩
  · intro hT
    obtain ⟨j, hj⟩ := schemaCompletionTheory_iSup_witness_canonDeForm hM
      (toLocalColimFormula_mem_ΓlocalColim s₀ hmem)
      (fun i => locDeTermFin (localColim s₀) ℕ (schemaRelSupport ts) (ts i)
        (locJSupport_subset_schemaRelSupport ts i))
      ((schemaRelSupport ts).orderEmbOfFin rfl) hT
    exact ⟨j, (ih j (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j)) ts).mpr hj⟩

private theorem schemaTruthStage_iInf
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (k : ℕ) {n : ℕ}
    (φs : ℕ → (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
    (ih : ∀ i, SchemaTruthStage hM k (φs i)) :
    SchemaTruthStage hM k (.iInf φs) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro hmem ts
  classical
  have hcolim : (⟨_, BoundedFormulaω.iInf fun i =>
        BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φs i)⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ :=
    toLocalColimFormula_mem_ΓlocalColim s₀ hmem
  rw [show ((BoundedFormulaω.iInf φs).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
        (lhomWithConstants (localColim s₀) ℕ)
      = BoundedFormulaω.iInf (fun i => (BoundedFormulaω.mapLanguage
          (LlocalInclusion s₀ (k + 1)) (φs i)).mapLanguage
            (lhomWithConstants (localColim s₀) ℕ)) from rfl,
    BoundedFormulaω.realize_iInf,
    show schemaFormulaSentence
          ((BoundedFormulaω.iInf φs).mapLanguage (LlocalInclusion s₀ (k + 1))) ts
        = schemaFormulaSentence (BoundedFormulaω.iInf fun i =>
            BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φs i)) ts from rfl]
  constructor
  · intro h
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaFormulaSentence_mem_universe hcolim ts) with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨j, hj⟩ := schemaCompletionTheory_neg_iInf_witness_canonDeForm hM hcolim
        (fun i => locDeTermFin (localColim s₀) ℕ (schemaRelSupport ts) (ts i)
          (locJSupport_subset_schemaRelSupport ts i))
        ((schemaRelSupport ts).orderEmbOfFin rfl) hneg
      have hjT := (ih j (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j)) ts).mp
        (h j)
      exact (schemaCompletionTheory_not_mem_iff hM _
        (schemaFormulaSentence_mem_universe
          (toLocalColimFormula_mem_ΓlocalColim s₀
            (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j))) ts)).mp hj hjT
  · intro hT j
    apply (ih j (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j)) ts).mpr
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaFormulaSentence_mem_universe
        (toLocalColimFormula_mem_ΓlocalColim s₀
          (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j))) ts)
      with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
        {schemaFormulaSentence ((BoundedFormulaω.iInf φs).mapLanguage
            (LlocalInclusion s₀ (k + 1))) ts,
          (schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) (φs j)) ts).not}
        (fun τ hτ => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hτ
          rcases hτ with rfl | rfl
          · exact hT
          · exact hneg)
      have h1 := hbody _ (Finset.mem_insert_self _ _)
      have h2 := hbody _
        (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
      rw [realize_schemaFormulaSentence_iff] at h1
      rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
      exact h2 (h1 j)

/-- **The staged restricted schema truth lemma.** For a successor-stage family formula
`ψ ∈ Γlocal s₀ (k + 1)` and closed argument terms `ts`, realizing the colimit image of `ψ` in the
schema term model on the classes of `ts` is equivalent to membership of its
`schemaFormulaSentence` in the completed theory `Tσ`. The source `M` carries the CANONICAL
`localColimStructure` (the `all` case consumes the Hilbert-choice Skolem interpretations via
`locSkWitness_universal_constInterp_nat`). Modeled on `LocalEMContext.truthLemmaStage`: the
induction threads the family membership; atoms normalize to the 5a atomic API through the carrier
term bridge and semantic sign transport; `imp` is propositional completeness; `iSup`/`iInf`
consume the canonical-deForm connective witnesses (5b-2) — the negative `iInf` direction is
exactly what the completion repair pinned; `all` runs the Skolem-witness argument against a
certificate body. (The heartbeat bump is for the seven-case induction as a single elaboration
unit; no individual step is deep.) -/
theorem schemaTruthLemmaStage :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)
      (k : ℕ) {n : ℕ} (ψ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n),
      (⟨n, ψ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) ∈ Γlocal s₀ (k + 1) →
      ∀ ts : Fin n → (localColim s₀)[[ℕ]].Term Empty,
        (@BoundedFormulaω.Realize ((localColim s₀)[[ℕ]])
            (SchemaTermCarrier (s₀ := s₀) (M := M) hM) (schemaTermStructure hM) Empty n
            ((BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ).mapLanguage
              (lhomWithConstants (localColim s₀) ℕ))
            (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
            (fun i => SchemaTermCarrier.mk hM (ts i)) ↔
          schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ (k + 1)) ψ) ts
            ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  intro hM k
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro n ψ
  induction ψ with
  | falsum => exact schemaTruthStage_falsum hM k
  | equal t₁ t₂ => exact schemaTruthStage_equal hM k t₁ t₂
  | rel R args => exact schemaTruthStage_rel hM k R args
  | imp φ ψ ihφ ihψ => exact schemaTruthStage_imp hM k φ ψ ihφ ihψ
  | all ψ ih => exact schemaTruthStage_all hM k ψ ih
  | iSup φs ih => exact schemaTruthStage_iSup hM k φs ih
  | iInf φs ih => exact schemaTruthStage_iInf hM k φs ih

/-- **Stage-agnostic lift corollary**: the staged schema truth lemma for an *original* stage-`k`
family member, at any stage including the raw seed stage `0`. Lifts the member one stage (along
`LlocalHom`, via `liftGamma_mem_Γlocal_succ`) where subformula closure is available, then rewrites
the colimit image back down with the cocone coherence `mapLanguage_LlocalInclusion_lift`. -/
theorem schemaTruthLemmaStage_of_mem :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)
      (k : ℕ) {n : ℕ} (ψ : (Llocal s₀ k).BoundedFormulaω Empty n),
      (⟨n, ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k →
      ∀ ts : Fin n → (localColim s₀)[[ℕ]].Term Empty,
        (@BoundedFormulaω.Realize ((localColim s₀)[[ℕ]])
            (SchemaTermCarrier (s₀ := s₀) (M := M) hM) (schemaTermStructure hM) Empty n
            ((BoundedFormulaω.mapLanguage (LlocalInclusion s₀ k) ψ).mapLanguage
              (lhomWithConstants (localColim s₀) ℕ))
            (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
            (fun i => SchemaTermCarrier.mk hM (ts i)) ↔
          schemaFormulaSentence (BoundedFormulaω.mapLanguage (LlocalInclusion s₀ k) ψ) ts
            ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  intro hM k n ψ hmem ts
  have h := schemaTruthLemmaStage hM k (BoundedFormulaω.mapLanguage (LlocalHom s₀ k) ψ)
    (liftGamma_mem_Γlocal_succ s₀ hmem) ts
  rwa [mapLanguage_LlocalInclusion_lift] at h

end StagedTruthLemma

/-! ## The ΓEMlocal sequence-realization bridge, layer 1: closing terms along the sequence

The exported bridge (below) is narrowly scoped to the distinguished sequence: realization of a
`ΓEMlocal` member on `schemaSeq ∘ t` in the base-language reduct of the term model, iff the
lifted template sentence is in `Tσ`. This layer supplies the term plumbing: closing an open
`Fin m`-variable base term along an increasing tuple of sequence constants, its value under a
certificate-body interpretation (`σ (t i)` at the variables), and its class in the term model
(the class of the closed instance). Plus the neutral restatement of the canonical-deForm
realization lemma (the residual file's copy is Conditional-facing and not imported here). -/

section ClosingTerms

/-- Realization of a canonical deForm in any structure: substituting the `Fin p`-variable terms
`g` for the bound variables and rebinding realizes as `φ` on the term values. Neutral twin of the
residual-file `realize_canonDeForm`. -/
private theorem canonDeForm_realize_iff {Λ : Language.{0, 0}} {N : Type} [Λ.Structure N] {n p : ℕ}
    (φ : Λ.BoundedFormulaω Empty n) (g : Fin n → Λ.Term (Fin p)) (xs : Fin p → N) :
    (canonDeForm Λ φ g).Realize (Empty.elim : Empty → N) xs ↔
      φ.Realize (Empty.elim : Empty → N) (fun i => (g i).realize xs) := by
  rw [canonDeForm, BoundedFormulaω.realize_relabel_sumInr_zero]
  simp only [Formulaω.realize_def, BoundedFormulaω.realize_subst]
  exact realize_openBounds φ _

variable {s₀ : LocalStage}

/-- **Closing a term along the sequence**: an open `Fin m`-variable base-language term, mapped
into the constant expansion and its variables substituted by the sequence constants `d_{t i}`. -/
private def schemaCloseTerm {m : ℕ} (u : (localColim s₀).Term (Fin m)) (t : Fin m ↪o ℕ) :
    (localColim s₀)[[ℕ]].Term Empty :=
  ((lhomWithConstants (localColim s₀) ℕ).onTerm u).subst fun i => henkinConst (t i)

variable {M : Type} [(localColim s₀).Structure M] [LinearOrder M] [WellFoundedLT M]
  (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)



omit [LinearOrder M] [WellFoundedLT M] in
/-- **The body value of a closed instance**: under a certificate-body interpretation `σ`, the
closed instance realizes to the open term realized at the `σ`-values of the tuple. -/
private theorem realize_schemaCloseTerm (σ : ℕ → M) {m : ℕ}
    (u : (localColim s₀).Term (Fin m)) (t : Fin m ↪o ℕ) :
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    (schemaCloseTerm u t).realize (Empty.elim : Empty → M)
      = u.realize fun i => σ (t i) := by
  let : (constantsOn ℕ).Structure M := constantsOn.structure σ
  rw [schemaCloseTerm, Term.realize_subst,
    LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ)]
  rfl

/-- **The class of a closed instance**: in the schema term model, the expansion image of an open
term realized on the sequence classes `schemaSeq ∘ t` is the class of its closed instance. -/
private theorem schemaCloseTerm_realize_mk {m : ℕ}
    (u : (localColim s₀).Term (Fin m)) (t : Fin m ↪o ℕ) :
    letI := schemaTermStructure (s₀ := s₀) (M := M) hM
    ((lhomWithConstants (localColim s₀) ℕ).onTerm u).realize
        (fun i => schemaSeq (s₀ := s₀) (M := M) hM (t i))
      = SchemaTermCarrier.mk hM (schemaCloseTerm u t) := by
  let := schemaTermStructure (s₀ := s₀) (M := M) hM
  rw [show (fun i => schemaSeq (s₀ := s₀) (M := M) hM (t i))
      = fun i => (henkinConst (L := localColim s₀) (t i)).realize
          (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM) from
    funext fun i => (schemaTerm_realize_eq_mk hM _).symm,
    ← Term.realize_subst]
  exact schemaTerm_realize_eq_mk hM _

/-- **The reduct value of a closed instance**: in the base-language reduct of the schema term
model, an open term realized on the sequence classes is the class of its closed instance. -/
private theorem schemaCloseTerm_reduct_realize {m : ℕ}
    (u : (localColim s₀).Term (Fin m)) (t : Fin m ↪o ℕ) :
    letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      schemaTermStructure hM
    letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      (lhomWithConstants (localColim s₀) ℕ).reduct _
    u.realize (fun i => schemaSeq (s₀ := s₀) (M := M) hM (t i))
      = SchemaTermCarrier.mk hM (schemaCloseTerm u t) := by
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  have : (lhomWithConstants (localColim s₀) ℕ).IsExpansionOn
      (SchemaTermCarrier (s₀ := s₀) (M := M) hM) := LHom.isExpansionOn_reduct _ _
  exact (LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ) u _).symm.trans
    (schemaCloseTerm_realize_mk hM u t)

/-! ### The three sign transports (semantic equivalence of universe sentences) -/

/-- **Colimit-member transport**: the formula sentence at the sequence constants and the lifted
template sentence at the tuple receive the same sign — under every body interpretation both say
"`φ` on `σ ∘ t`". -/
private theorem schemaFormulaSentence_henkin_mem_iff_schemaLift {m : ℕ}
    {φ : (localColim s₀).BoundedFormulaω Empty m}
    (hφ : (⟨m, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀)
    (t : Fin m ↪o ℕ) :
    schemaFormulaSentence φ (fun i => henkinConst (t i))
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift φ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  schema_mem_iff_of_semantic_iff hM
    (locDeForm_mem_ΓEMlocal ℕ s₀ _ hφ _ (locJSupport_subset_schemaRelSupport _))
    ((schemaRelSupport fun i => henkinConst (t i)).orderEmbOfFin rfl)
    (ΓlocalColim_subset_ΓEMlocal s₀ hφ) t
    (fun σ w => by
      let : (constantsOn ℕ).Structure M := constantsOn.structure σ
      exact (realize_schemaFormulaSentence_iff σ w φ (fun i => henkinConst (t i))).trans
        (realizeWith_templateSentence (L'' := localColim s₀) σ w φ t).symm)

/-- **Equality-atom transport**: the closed-instance equality sentence and the lifted canonical
equality atom receive the same sign. -/
private theorem schemaEqSentence_close_mem_iff_schemaLift {m : ℕ}
    (u₁ u₂ : (localColim s₀).Term (Fin m)) (t : Fin m ↪o ℕ) :
    schemaEqSentence (schemaCloseTerm u₁ t) (schemaCloseTerm u₂ t)
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift (canonEqAtom (localColim s₀) u₁ u₂) t
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  schema_mem_iff_of_semantic_iff hM
    (locDeEqAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaSupport _ _) _ _
      Finset.subset_union_left Finset.subset_union_right)
    ((schemaSupport (schemaCloseTerm u₁ t) (schemaCloseTerm u₂ t)).orderEmbOfFin rfl)
    (Or.inl (Or.inl (Or.inr ⟨⟨m, (u₁, u₂)⟩, rfl⟩))) t
    (fun σ w => by
      let : (constantsOn ℕ).Structure M := constantsOn.structure σ
      have h1 := realize_schemaEqSentence_iff σ w (schemaCloseTerm u₁ t) (schemaCloseTerm u₂ t)
      have h2 := realizeWith_templateSentence (L'' := localColim s₀) σ w
        (canonEqAtom (localColim s₀) u₁ u₂) t
      refine h1.trans (Iff.trans ?_ h2.symm)
      show ((schemaCloseTerm u₁ t).realize (Empty.elim : Empty → M)
            = (schemaCloseTerm u₂ t).realize Empty.elim)
          ↔ (canonEqAtom (localColim s₀) u₁ u₂).Realize (Empty.elim : Empty → M)
            (fun i => σ (t i))
      rw [realize_schemaCloseTerm σ u₁ t, realize_schemaCloseTerm σ u₂ t, canonEqAtom,
        BoundedFormulaω.realize_equal, Term.realize_relabel, Term.realize_relabel]
      rfl)

/-- **Relation-atom transport**: the closed-instance relation sentence and the lifted canonical
relation atom receive the same sign. -/
private theorem schemaRelSentence_close_mem_iff_schemaLift {m l : ℕ}
    (R : (localColim s₀).Relations l) (us : Fin l → (localColim s₀).Term (Fin m))
    (t : Fin m ↪o ℕ) :
    schemaRelSentence R (fun i => schemaCloseTerm (us i) t)
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift (canonRelAtom (localColim s₀) R us) t
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  schema_mem_iff_of_semantic_iff hM
    (locDeRelAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaRelSupport _) R _
      (locJSupport_subset_schemaRelSupport _))
    ((schemaRelSupport fun i => schemaCloseTerm (us i) t).orderEmbOfFin rfl)
    (Or.inl (Or.inr ⟨⟨m, l, (R, us)⟩, rfl⟩)) t
    (fun σ w => by
      let : (constantsOn ℕ).Structure M := constantsOn.structure σ
      have h1 := realize_schemaRelSentence_iff σ w R (fun i => schemaCloseTerm (us i) t)
      have h2 := realizeWith_templateSentence (L'' := localColim s₀) σ w
        (canonRelAtom (localColim s₀) R us) t
      refine h1.trans (Iff.trans ?_ h2.symm)
      show (Structure.RelMap R fun i => (schemaCloseTerm (us i) t).realize
            (Empty.elim : Empty → M))
          ↔ (canonRelAtom (localColim s₀) R us).Realize (Empty.elim : Empty → M)
            (fun i => σ (t i))
      rw [canonRelAtom, BoundedFormulaω.realize_rel]
      apply Iff.of_eq
      congr 1
      funext i
      rw [realize_schemaCloseTerm σ (us i) t, Term.realize_relabel]
      rfl)

/-- **Canonical-deForm transport**: the formula sentence of the base member at the closed
instances of `g` and the lifted template of the deForm receive the same sign. -/
private theorem schemaFormulaSentence_close_mem_iff_schemaLift_canonDeForm {q m : ℕ}
    {φ : (localColim s₀).BoundedFormulaω Empty q}
    (hφ : (⟨q, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀)
    (g : Fin q → (localColim s₀).Term (Fin m)) (t : Fin m ↪o ℕ) :
    schemaFormulaSentence φ (fun j => schemaCloseTerm (g j) t)
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift (canonDeForm (localColim s₀) φ g) t
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  schema_mem_iff_of_semantic_iff hM
    (locDeForm_mem_ΓEMlocal ℕ s₀ _ hφ _ (locJSupport_subset_schemaRelSupport _))
    ((schemaRelSupport fun j => schemaCloseTerm (g j) t).orderEmbOfFin rfl)
    (canonDeForm_mem_ΓEMlocal hφ g) t
    (fun σ w => by
      let : (constantsOn ℕ).Structure M := constantsOn.structure σ
      have h1 := realize_schemaFormulaSentence_iff σ w φ (fun j => schemaCloseTerm (g j) t)
      have h2 := realizeWith_templateSentence (L'' := localColim s₀) σ w
        (canonDeForm (localColim s₀) φ g) t
      refine h1.trans (Iff.trans ?_ h2.symm)
      show (φ.Realize (Empty.elim : Empty → M)
            fun j => (schemaCloseTerm (g j) t).realize Empty.elim)
          ↔ (canonDeForm (localColim s₀) φ g).Realize (Empty.elim : Empty → M)
            (fun i => σ (t i))
      rw [canonDeForm_realize_iff]
      apply Iff.of_eq
      congr 1
      funext j
      exact realize_schemaCloseTerm σ (g j) t)

end ClosingTerms

/-! ## The ΓEMlocal sequence-realization bridge -/

section SequenceBridge

variable {s₀ : LocalStage} {M : Type} [s₀.Lang.Structure M] [Nonempty M] [LinearOrder M]
  [WellFoundedLT M]

/-- **The colimit-family truth lemma**: the staged truth lemma at the colimit level, unpacking a
`ΓlocalColim` membership into its stage representation. -/
private theorem schemaTruthLemma_colim :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)
      {m : ℕ} {φ : (localColim s₀).BoundedFormulaω Empty m},
      (⟨m, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ →
      ∀ ts : Fin m → (localColim s₀)[[ℕ]].Term Empty,
        (@BoundedFormulaω.Realize ((localColim s₀)[[ℕ]])
            (SchemaTermCarrier (s₀ := s₀) (M := M) hM) (schemaTermStructure hM) Empty m
            (BoundedFormulaω.mapLanguage (lhomWithConstants (localColim s₀) ℕ) φ)
            (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
            (fun i => SchemaTermCarrier.mk hM (ts i)) ↔
          schemaFormulaSentence φ ts ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  intro hM m φ hφ ts
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hφ
  obtain ⟨⟨m', ψ₀⟩, hmem, heq⟩ := hk
  rw [toLocalColimFormula, Sigma.mk.injEq] at heq
  obtain ⟨rfl, heq2⟩ := heq
  rw [heq_eq_eq] at heq2
  subst heq2
  exact schemaTruthLemmaStage_of_mem hM k ψ₀ hmem ts

/-- **The ΓEMlocal sequence-realization bridge** (the exported statement, narrowly scoped to the
distinguished sequence): a `ΓEMlocal` member realized on `schemaSeq ∘ t` in the base-language
reduct of the schema term model, iff its lifted template sentence at `t` is in the completed
theory. Four summands: colimit members through the staged truth lemma; canonical equality and
relation atoms through the 5a atomic API on closed instances; canonical deForms by closing the
substituted terms along `t` and reducing to the base member. Every case ends in the matching
sign transport. -/
theorem schemaSeq_realize_iff_schemaLift_mem :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)
      {m : ℕ} (ψ : (localColim s₀).BoundedFormulaω Empty m),
      (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀ →
      ∀ t : Fin m ↪o ℕ,
        letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
          schemaTermStructure hM
        letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
          (lhomWithConstants (localColim s₀) ℕ).reduct _
        (ψ.Realize (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
            (fun i => schemaSeq hM (t i)) ↔
          schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  intro hM m ψ hψ t
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  have : (lhomWithConstants (localColim s₀) ℕ).IsExpansionOn
      (SchemaTermCarrier (s₀ := s₀) (M := M) hM) := LHom.isExpansionOn_reduct _ _
  show ψ.Realize (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      (fun i => schemaSeq hM (t i)) ↔
    schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM
  rcases hψ with ((hcolim | heqm) | hrelm) | hdem
  · -- colimit members
    exact (BoundedFormulaω.realize_mapLanguage (lhomWithConstants (localColim s₀) ℕ) ψ
        (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        (fun i => schemaSeq hM (t i))).symm.trans
      ((schemaTruthLemma_colim hM hcolim (fun i => henkinConst (t i))).trans
        (schemaFormulaSentence_henkin_mem_iff_schemaLift hM hcolim t))
  · -- canonical equality atoms
    obtain ⟨⟨m', u₁, u₂⟩, heq⟩ := heqm
    rw [Sigma.mk.injEq] at heq
    obtain ⟨rfl, heq2⟩ := heq
    rw [heq_eq_eq] at heq2
    subst heq2
    refine Iff.trans ?_ (schemaEqSentence_close_mem_iff_schemaLift hM u₁ u₂ t)
    rw [canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel, Term.realize_relabel]
    show (u₁.realize (fun i => schemaSeq (s₀ := s₀) (M := M) hM (t i))
          = u₂.realize (fun i => schemaSeq hM (t i))) ↔ _
    rw [schemaCloseTerm_reduct_realize hM u₁ t, schemaCloseTerm_reduct_realize hM u₂ t]
    exact SchemaTermCarrier.mk_eq_mk_iff hM
  · -- canonical relation atoms
    obtain ⟨⟨m', l, R, us⟩, heq⟩ := hrelm
    rw [Sigma.mk.injEq] at heq
    obtain ⟨rfl, heq2⟩ := heq
    rw [heq_eq_eq] at heq2
    subst heq2
    refine Iff.trans ?_ (schemaRelSentence_close_mem_iff_schemaLift hM R us t)
    rw [canonRelAtom, BoundedFormulaω.realize_rel,
      show (fun i => ((us i).relabel Sum.inr).realize
          (Sum.elim (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
            fun i => schemaSeq hM (t i)))
        = fun i => SchemaTermCarrier.mk hM (schemaCloseTerm (us i) t) from
      funext fun i => by
        rw [Term.realize_relabel]
        exact schemaCloseTerm_reduct_realize hM (us i) t]
    exact schemaTerm_relMap_mk_iff hM R fun i => schemaCloseTerm (us i) t
  · -- canonical deForms
    simp only [canonDeForms, Set.mem_iUnion] at hdem
    obtain ⟨⟨q, φ⟩, hqΓ, ⟨p', g⟩, heq⟩ := hdem
    rw [Sigma.mk.injEq] at heq
    obtain ⟨rfl, heq2⟩ := heq
    rw [heq_eq_eq] at heq2
    subst heq2
    refine Iff.trans ?_ (schemaFormulaSentence_close_mem_iff_schemaLift_canonDeForm hM hqΓ g t)
    rw [canonDeForm_realize_iff,
      show (fun j => (g j).realize (fun i => schemaSeq (s₀ := s₀) (M := M) hM (t i)))
        = fun j => SchemaTermCarrier.mk hM (schemaCloseTerm (g j) t) from
      funext fun j => schemaCloseTerm_reduct_realize hM (g j) t]
    exact (BoundedFormulaω.realize_mapLanguage (lhomWithConstants (localColim s₀) ℕ) φ
        (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        (fun j => SchemaTermCarrier.mk hM (schemaCloseTerm (g j) t))).symm.trans
      (schemaTruthLemma_colim hM hqΓ fun j => schemaCloseTerm (g j) t)

/-! ### Full indiscernibility and the Ω-witnesses -/

/-- **Full indiscernibility of the schema sequence** (cutoff `0`): in the base-language reduct of
the schema term model, `schemaSeq` is `Lω₁ω`-indiscernible on all of `ΓEMlocal` — realization at
any two strictly monotone tuples transports through the bridge to theory membership at the two
lifted templates, which agree by tuple uniformity. -/
theorem schemaSeq_indiscernibleOn :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M,
      letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
        schemaTermStructure hM
      letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
        (lhomWithConstants (localColim s₀) ℕ).reduct _
      IsLomega1omegaIndiscernibleOn (L := localColim s₀)
        (schemaSeq (s₀ := s₀) (M := M) hM) (ΓEMlocal s₀) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  intro hM
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  intro n φ hφ s t hs ht
  exact (schemaSeq_realize_iff_schemaLift_mem hM φ hφ
      (OrderEmbedding.ofStrictMono s hs)).trans
    ((schemaCompletionTheory_tuple_uniform hM hφ (OrderEmbedding.ofStrictMono s hs)
        (OrderEmbedding.ofStrictMono t ht)).trans
      (schemaSeq_realize_iff_schemaLift_mem hM φ hφ
        (OrderEmbedding.ofStrictMono t ht)).symm)

/-- **The tail-template truth collapse to the standard tuple**: by full indiscernibility, the
eventually-form template truth of a `ΓEMlocal` member equals theory membership of its lifted
template at the standard tuple. -/
private theorem tailTemplate_schemaSeq_truth_iff :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M,
      letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
        schemaTermStructure hM
      letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
        (lhomWithConstants (localColim s₀) ℕ).reduct _
      ∀ {p : ℕ} {ψ : (localColim s₀).BoundedFormulaω Empty p},
        (⟨p, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀ →
        ((tailTemplateOfSeq (L := localColim s₀) (schemaSeq (s₀ := s₀) (M := M) hM)).truth ψ ↔
          schemaLift ψ (stdTuple p) ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  intro hM
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  intro p ψ hψ
  have hind : IsLomega1omegaIndiscernibleOn (L := localColim s₀)
      (schemaSeq (s₀ := s₀) (M := M) hM) (ΓEMlocal s₀) := schemaSeq_indiscernibleOn hM
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨s, hs, hdeep⟩ := exists_strictMono_of_le p N
    exact (schemaSeq_realize_iff_schemaLift_mem hM ψ hψ (stdTuple p)).mp
      ((hind hψ s (stdTuple p) hs (stdTuple p).strictMono).mp (hN s hs hdeep))
  · intro hT
    refine ⟨0, fun s hs _ => ?_⟩
    exact (hind hψ (stdTuple p) s (stdTuple p).strictMono hs).mp
      ((schemaSeq_realize_iff_schemaLift_mem hM ψ hψ (stdTuple p)).mpr hT)

/-- **The schema-template Ω-witness property for the schema sequence** — the Layer-7a target,
discharged by the completed theory: a disjunction's template truth yields a component's (the
positive `iSup` witness pinned by the completion), and joint component truth yields the
conjunction's (via the negative-`iInf` witness pinned by the completion repair: were the
conjunction negative, its fixed refuted conjunct would contradict that component's truth). -/
theorem schemaSeq_tailTemplateOmegaWitnessed :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M,
      letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
        schemaTermStructure hM
      letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
        (lhomWithConstants (localColim s₀) ℕ).reduct _
      TailTemplateOmegaWitnessed s₀ (schemaSeq (s₀ := s₀) (M := M) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  intro hM
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  constructor
  · intro m φs hmem p g htruth
    obtain ⟨k, hk⟩ := schemaCompletionTheory_iSup_witness_canonDeForm hM hmem g (stdTuple p)
      ((tailTemplate_schemaSeq_truth_iff hM (canonDeForm_mem_ΓEMlocal hmem g)).mp htruth)
    exact ⟨k, (tailTemplate_schemaSeq_truth_iff hM
      (canonDeForm_mem_ΓEMlocal (iSup_component_mem_ΓlocalColim s₀ hmem k) g)).mpr hk⟩
  · intro m φs hmem p g hall
    refine (tailTemplate_schemaSeq_truth_iff hM (canonDeForm_mem_ΓEMlocal hmem g)).mpr ?_
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaLift_mem_universe (canonDeForm_mem_ΓEMlocal hmem g) (stdTuple p))
      with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨k, hk⟩ := schemaCompletionTheory_neg_iInf_witness_canonDeForm hM hmem g
        (stdTuple p) hneg
      exact (schemaCompletionTheory_not_mem_iff hM _
          (schemaLift_mem_universe (canonDeForm_mem_ΓEMlocal
            (iInf_component_mem_ΓlocalColim s₀ hmem k) g) (stdTuple p))).mp hk
        ((tailTemplate_schemaSeq_truth_iff hM
          (canonDeForm_mem_ΓEMlocal (iInf_component_mem_ΓlocalColim s₀ hmem k) g)).mp (hall k))

end SequenceBridge

/-! ## Checkpoint 5c substrate: validity positivity and pairwise distinctness

The two term-model facts the Morley-seed agreement (`morleySeed_template_agreement_cross`)
consumes: a universe sentence valid under every body interpretation gets the positive sign (the
route to seed-sentence realization), and the schema sequence is pairwise distinct (a body for the
equality sentence, evaluated on a support enlarged to both indices, would violate the strictness
of its skeleton interpretation). -/

section SeedFacts

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- **Validity forces the positive sign**: a universe sentence realized under EVERY body
interpretation pair cannot be decided negatively — the body of its singleton negation would
refute itself. -/
theorem schemaLift_mem_of_valid {m : ℕ}
    {ψ : (localColim s₀).BoundedFormulaω Empty m}
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t : Fin m ↪o ℕ)
    (hvalid : ∀ σ h : ℕ → M,
      realizeWith σ h (schemaLift ψ t) (Empty.elim : Empty → M) Fin.elim0) :
    schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  rcases (schemaCompletionTheorySpec hM).complete_on_universe _
    (schemaLift_mem_universe hψ t) with hpos | hneg
  · exact hpos
  · exfalso
    obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM {(schemaLift ψ t).not}
      (fun τ hτ => by
        rw [Finset.mem_singleton] at hτ
        exact hτ ▸ hneg)
    have hn := hbody (schemaLift ψ t).not (Finset.mem_singleton_self _)
    rw [realizeWith_not] at hn
    exact hn (hvalid σ w)

/-- **The schema sequence is pairwise distinct**: if two sequence classes were equal, the
completed theory would contain their equality sentence; a certificate body for it, evaluated on a
support enlarged to contain both indices, would equate two values of a strictly monotone skeleton
interpretation. -/
theorem schemaSeq_pairwise_ne {i j : ℕ} (hij : i ≠ j) :
    schemaSeq (s₀ := s₀) (M := M) hM i ≠ schemaSeq (s₀ := s₀) (M := M) hM j := by
  intro heq
  have hEqT : SchemaTermEq hM (henkinConst (L := localColim s₀) i)
      (henkinConst (L := localColim s₀) j) :=
    (SchemaTermCarrier.mk_eq_mk_iff hM).mp heq
  obtain ⟨S, H, hS, hH, hcof⟩ := (schemaCompletionTheorySpec hM).finite_consistent
    {schemaEqSentence (henkinConst (L := localColim s₀) i)
      (henkinConst (L := localColim s₀) j)}
    (fun τ' hτ' => by
      rw [Finset.mem_singleton] at hτ'
      exact hτ' ▸ hEqT)
  obtain ⟨α, hα0, hα1, hb⟩ := hcof 0 (Ordinal.omega_pos 1)
  have hSS' : S ⊆ insert i (insert j S) := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  obtain ⟨e, hsat⟩ := hb.enlarge_support hSS'
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e (insert i (insert j S))
  obtain ⟨w, hw⟩ := hsat σ hmono hrange
  have hreal := hw (schemaEqSentence (henkinConst (L := localColim s₀) i)
      (henkinConst (L := localColim s₀) j))
    (by rw [Finset.mem_coe]; exact Finset.mem_singleton_self _)
  rw [realize_schemaEqSentence_iff] at hreal
  have hiS' : i ∈ insert i (insert j S) := Finset.mem_insert_self _ _
  have hjS' : j ∈ insert i (insert j S) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact (hmono (Finset.mem_coe.mpr hiS') (Finset.mem_coe.mpr hjS') hijlt).ne hreal
  · exact (hmono (Finset.mem_coe.mpr hjS') (Finset.mem_coe.mpr hiS') hjilt).ne hreal.symm

end SeedFacts

end FirstOrder.Language
