/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arith.D1

/-! # First -/



namespace List
namespace Vector

variable {α : Type*}

lemma cons_get {x : α} : (x ::ᵥ List.Vector.nil).get = ![x] := by
  ext i;
  simp;

end Vector
end List


namespace LO
namespace FirstOrder

namespace Arith

open LO.Arith LO.Entailment LO.Arith.Formalized

lemma re_iff_sigma1 {P : ℕ → Prop} : RePred P ↔ Sg1-Predicate P := by
  constructor
  · intro h
    exact ⟨.mkSigma (codeOfRePred P) (by simp [codeOfRePred, codeOfPartrec']), by
      intro v; symm; simp; simpa [←Matrix.constant_eq_singleton'] using codeOfRePred_spec h (x :=
        v 0)⟩
  · rintro ⟨φ, hφ⟩
    have := (sigma1_re id (φ.sigma_prop)).comp
      (f :=
        fun x : ℕ ↦ x ::ᵥ List.Vector.nil) (Primrec.to_comp <|
            Primrec.vector_cons.comp .id (.const _))
    exact this.of_eq <| by intro x; symm; simpa [List.Vector.cons_get] using hφ ![x];

variable (T : Theory ℒₒᵣ) [𝐑₀ wkn T] [Sigma1Sound T] [T.Delta1Definable]

/-- Gödel's First Incompleteness Theorem -/
theorem goedel_first_incompleteness : ¬Entailment.Complete T := by
  let D : ℕ → Prop := fun n : ℕ ↦ ∃ φ : SyntacticSemiformula ℒₒᵣ 1, n = ⌜φ⌝ ∧ T ⊢! ∼φ/[⌜φ⌝]
  have D_re : RePred D := by
    have : Sg1-Predicate fun φ : ℕ ↦
      ⌜ℒₒᵣ⌝.IsSemiformula 1 φ ∧
          (T.codeIn ℕ).Provable (⌜ℒₒᵣ⌝.neg <| ⌜ℒₒᵣ⌝.substs ?[numeral φ] φ) := by definability
    exact (re_iff_sigma1.mpr this).of_eq <| by
      intro φ; constructor
      · rintro ⟨hφ, b⟩
        rcases hφ.sound with ⟨φ, rfl⟩
        refine ⟨φ, rfl, Language.Theory.Provable.sound (by simpa)⟩
      · rintro ⟨φ, rfl, b⟩
        exact ⟨by simp, by simpa [Matrix.constant_eq_singleton, quote_cons,
          quote_matrix_empty] using provable_of_provable (V := ℕ) b⟩
  let σ : SyntacticSemiformula ℒₒᵣ 1 := codeOfRePred (D)
  let ρ : SyntacticFormula ℒₒᵣ := σ/[⌜σ⌝]
  have : ∀ n : ℕ, D n ↔ T ⊢! σ/[‘↑n’] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁] using re_complete (T := T) (D_re) (x := n)
  have : T ⊢! ∼ρ ↔ T ⊢! ρ := by
    have h := this ⌜σ⌝
    simp only [D, goedelNumber'_def, quote_eq_encode, Semiterm.Operator.encode,
      Encodable.encode_inj, exists_eq_left'] at h
    change T ⊢! ∼σ/[⌜σ⌝] ↔ T ⊢! σ/[⌜σ⌝]
    simp only [goedelNumber'_def, Semiterm.Operator.encode, Semiterm.numeral] at h ⊢
    exact h
  have con : Entailment.Consistent T := consistent_of_sigma1Sound T
  refine LO.Entailment.incomplete_iff_exists_undecidable.mpr ⟨↑ρ, ?_, ?_⟩
  · intro h
    have : T ⊢! ∼↑ρ := by simpa [provable₀_iff] using this.mpr h
    exact LO.Entailment.not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable
      h this) inferInstance
  · intro h
    have : T ⊢! ↑ρ := this.mp (by simpa [provable₀_iff] using h)
    exact LO.Entailment.not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable
      this h) inferInstance

end Arith
end FirstOrder
end LO
