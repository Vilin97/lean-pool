/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.GeneratedUniverse
/-!
# Base-symbol occurrence projections (neutral layer)

The generic, **unsigned** occurrence bookkeeping shared by the Craig engine and the Lyndon
refinement: how the base function/relation symbols of a subformula sit inside those of the whole,
their invariance under substitution and `openBounds`, the `instConst` bounds, and the atomic facts
for `constEq` and `relInst`.

Nothing here mentions inseparability, side bounds, the paired family, a consistency property, or
the Henkin completion; the file's own dependency cone stops at the generated universe.  It was
extracted from `PairedInsepFamily.lean` so that the polarity-refined development (issue #14, Units
2-3) can consume these projections without dragging the paired/Henkin assembly into its cone --
the boundary now matches the proof architecture.  Declaration names and namespaces are unchanged,
so no compatibility shims are needed.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## Base-symbol component projections

The dual of the `baseFunctionsIn_*_subset` union bounds: a subformula's base symbols are contained
in the whole's. -/

theorem baseFunctionsIn_imp_left {φ ψ : L[[ℕ]].Sentenceω} :
    φ.baseFunctionsIn ⊆ (φ.imp ψ).baseFunctionsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_union] at hs ⊢
  exact Or.inl hs

theorem baseFunctionsIn_imp_right {φ ψ : L[[ℕ]].Sentenceω} :
    ψ.baseFunctionsIn ⊆ (φ.imp ψ).baseFunctionsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_union] at hs ⊢
  exact Or.inr hs

theorem baseRelationsIn_imp_left {φ ψ : L[[ℕ]].Sentenceω} :
    φ.baseRelationsIn ⊆ (φ.imp ψ).baseRelationsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_union] at hs ⊢
  exact Or.inl hs

theorem baseRelationsIn_imp_right {φ ψ : L[[ℕ]].Sentenceω} :
    ψ.baseRelationsIn ⊆ (φ.imp ψ).baseRelationsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_union] at hs ⊢
  exact Or.inr hs

theorem baseFunctionsIn_component_iInf {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
    (φs k).baseFunctionsIn ⊆ (BoundedFormulaω.iInf φs).baseFunctionsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs ⊢
  exact ⟨k, hs⟩

theorem baseRelationsIn_component_iInf {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
    (φs k).baseRelationsIn ⊆ (BoundedFormulaω.iInf φs).baseRelationsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs ⊢
  exact ⟨k, hs⟩

theorem baseFunctionsIn_component_iSup {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
    (φs k).baseFunctionsIn ⊆ (BoundedFormulaω.iSup φs).baseFunctionsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs ⊢
  exact ⟨k, hs⟩

theorem baseRelationsIn_component_iSup {φs : ℕ → L[[ℕ]].Sentenceω} (k : ℕ) :
    (φs k).baseRelationsIn ⊆ (BoundedFormulaω.iSup φs).baseRelationsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_ofPred_eq,
    Set.mem_iUnion] at hs ⊢
  exact ⟨k, hs⟩

/-! ## Relation occurrences are invariant under `subst` / `openBounds` (for `instConst`) -/

private theorem relationsIn_subst_eq {α β : Type} {n : ℕ}
    (φ : L[[ℕ]].BoundedFormulaω α n) (tf : α → L[[ℕ]].Term β) :
    (φ.subst tf).relationsIn = φ.relationsIn := by
  induction φ with
  | falsum => rfl
  | equal t u => rfl
  | rel Rr ts => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.relationsIn, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.subst, BoundedFormulaω.relationsIn, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.relationsIn]; exact iSup_congr fun k => ih k
  | iInf φs ih =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.relationsIn]; exact iSup_congr fun k => ih k

private theorem relationsIn_openBounds_eq {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) :
    (φ.openBounds).relationsIn = φ.relationsIn := by
  induction φ with
  | falsum => rfl
  | equal t u => rfl
  | rel Rr ts => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relationsIn, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relationsIn,
      BoundedFormulaω.relationsIn_relabel, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relationsIn]
    exact iSup_congr fun k => ih k
  | iInf φs ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relationsIn]
    exact iSup_congr fun k => ih k

theorem baseFunctionsIn_instConst_subset (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    (instConst c φ).baseFunctionsIn ⊆ (BoundedFormulaω.all φ).baseFunctionsIn := by
  intro s hs
  simp only [BoundedFormulaω.baseFunctionsIn, Set.mem_ofPred_eq] at hs ⊢
  have hsub :=
    BoundedFormulaω.functionsIn_subst (fun _ : Fin 1 => constTerm (L' := L) c) φ.openBounds
  have hmem := hsub hs
  rw [BoundedFormulaω.functionsIn_openBounds] at hmem
  show (⟨s.1, Sum.inl s.2⟩ : Σ n, L[[ℕ]].Functions n) ∈ (BoundedFormulaω.all φ).functionsIn
  rcases hmem with h | h
  · exact h
  · exfalso
    simp only [Set.mem_iUnion] at h
    obtain ⟨_, ha⟩ := h
    rw [constTerm_functionsIn] at ha
    obtain ⟨n', f⟩ := s
    simp only [Set.mem_singleton_iff] at ha
    -- `rcases` now discharges the `Sum.inl`/`Sum.inr` clash itself.
    obtain ⟨rfl, ha2⟩ := ha

theorem baseRelationsIn_instConst_subset (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    (instConst c φ).baseRelationsIn ⊆ (BoundedFormulaω.all φ).baseRelationsIn := by
  have h1 : (instConst c φ).relationsIn = (BoundedFormulaω.all φ).relationsIn := by
    show ((φ.openBounds).subst _).relationsIn = _
    rw [relationsIn_subst_eq, relationsIn_openBounds_eq]; rfl
  intro s hs
  simp only [BoundedFormulaω.baseRelationsIn, Set.mem_ofPred_eq, h1] at hs ⊢
  exact hs

/-! ## Atomic base symbols

Constant equalities have no base symbols; a relation instance has only its own relation symbol,
independent of the argument constants. -/

theorem baseFunctionsIn_constEq (a b : ℕ) :
    (constEq (L := L) a b).baseFunctionsIn = ∅ := by
  ext s
  obtain ⟨n, f⟩ := s
  simp only [constEq, constTermS, BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn,
    Term.functionsIn, Set.mem_ofPred_eq, Set.mem_union, Set.iUnion_of_empty,
    Set.mem_insert_iff, Set.mem_empty_iff_false, or_false, iff_false, not_or]
  -- `rintro` closes both goals outright: the `rfl` pattern is already contradictory
  refine ⟨?_, ?_⟩ <;> rintro ⟨rfl, h⟩

theorem baseRelationsIn_constEq (a b : ℕ) :
    (constEq (L := L) a b).baseRelationsIn = ∅ := by
  ext s
  simp only [constEq, BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false]

theorem baseFunctionsIn_relInst {l : ℕ} (Rr : L.Relations l) (g : Fin l → ℕ) :
    (relInst Rr g).baseFunctionsIn = ∅ := by
  ext s
  obtain ⟨n, f⟩ := s
  simp only [relInst, constTermS, BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn,
    Term.functionsIn, Set.mem_ofPred_eq, Set.mem_iUnion, Set.iUnion_of_empty, Set.mem_insert_iff,
    Set.mem_empty_iff_false, or_false, iff_false, not_exists]
  -- `rintro` now discharges the `Sum.inl`/`Sum.inr` clash itself.
  rintro i ⟨rfl, h⟩

theorem baseRelationsIn_relInst {l : ℕ} (Rr : L.Relations l) (g g' : Fin l → ℕ) :
    (relInst Rr g).baseRelationsIn = (relInst Rr g').baseRelationsIn := by
  ext s
  simp only [relInst, BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn,
    Set.mem_ofPred_eq]

/-! ## The three constant-expansion transport equalities (the base-`L` ↔ `L[[ℕ]]` boundary) -/

private theorem tag_inl_fun_injective :
    Function.Injective
      (fun p : Σ n, L.Functions n => (⟨p.1, Sum.inl p.2⟩ : Σ n, L[[ℕ]].Functions n)) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  exact Sigma.ext rfl (heq_of_eq (Sum.inl_injective (eq_of_heq h2)))

private theorem tag_inl_rel_injective :
    Function.Injective
      (fun p : Σ n, L.Relations n => (⟨p.1, Sum.inl p.2⟩ : Σ n, L[[ℕ]].Relations n)) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  exact Sigma.ext rfl (heq_of_eq (Sum.inl_injective (eq_of_heq h2)))

/-- **Base functions of a constant-expansion image** are the sentence's own functions. -/
theorem baseFunctionsIn_mapLanguage_withConstants (r : L.Sentenceω) :
    (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r).baseFunctionsIn = r.functionsIn := by
  ext s
  simp only [BoundedFormulaω.baseFunctionsIn, Set.mem_ofPred_eq,
    BoundedFormulaω.functionsIn_mapLanguage]
  exact tag_inl_fun_injective.mem_set_image

/-- **Base relations of a constant-expansion image** are the sentence's own relations. -/
theorem baseRelationsIn_mapLanguage_withConstants (r : L.Sentenceω) :
    (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r).baseRelationsIn = r.relationsIn := by
  ext s
  simp only [BoundedFormulaω.baseRelationsIn, Set.mem_ofPred_eq,
    BoundedFormulaω.relationsIn_mapLanguage]
  exact tag_inl_rel_injective.mem_set_image

end FirstOrder.Language
