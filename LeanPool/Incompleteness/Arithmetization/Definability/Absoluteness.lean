/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Definability.BoundedBoldface

/-! # Absoluteness -/


namespace LO
namespace FirstOrder
namespace Arith

open LO.Arith

lemma nat_modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : Semisentence ℒₒᵣ k} :
    ℕ ⊧/v φ ↔ ℕ ⊧ₘ₀ (φ <~ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i))) := by simp [models_iff]

variable (V : Type*) [ORingStruc V] [V ⊧ₘ* 𝐏𝐀⁻]

lemma modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : Semisentence ℒₒᵣ k} :
    V ⊧/(v ·) φ ↔ V ⊧ₘ₀ (φ <~ (fun i ↦ Semiterm.Operator.numeral ℒₒᵣ (v i))) := by
  simp [models_iff, numeral_eq_natCast]

lemma shigmaZero_absolute {k} (φ : Sg0.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧/v φ.val ↔ V ⊧/(v ·) φ.val :=
  ⟨by
    rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
    exact nat_extention_sigmaOne V (by simp),
   by
    rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
    exact nat_extention_piOne V (by simp)⟩

lemma _root_.LO.FirstOrder.Arith.Defined.shigmaZero_absolute {k} {R : (Fin k → ℕ) → Prop} {R' :
    (Fin k → V) → Prop} {φ :
    Sg0.Semisentence k}
    (hR : Sg0.Defined R φ) (hR' : Sg0.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by simpa [hR.iff, hR'.iff] using Arith.shigmaZero_absolute V φ v

lemma _root_.LO.FirstOrder.Arith.DefinedFunction.shigmaZero_absolute_func
    {k} {f : (Fin k → ℕ) → ℕ} {f' :
    (Fin k → V) → V} {φ :
    Sg0.Semisentence (k + 1)}
    (hf : Sg0.DefinedFunction f φ) (hf' : Sg0.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (fun i ↦ (v i)) := by simpa using Defined.shigmaZero_absolute V hf hf' (f v :> v)

lemma sigmaOne_upward_absolute {k} (φ : Sg1.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧/v φ.val → V ⊧/(v ·) φ.val := by
  rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_sigmaOne V (by simp)

lemma piOne_downward_absolute {k} (φ : Pg1.Semisentence k) (v : Fin k → ℕ) :
    V ⊧/(v ·) φ.val → ℕ ⊧/v φ.val := by
  rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_piOne V (by simp)

lemma deltaOne_absolute {k} (φ : Dlt1.Semisentence k)
    (properNat : φ.ProperOn ℕ) (proper : φ.ProperOn V) (v : Fin k → ℕ) :
    ℕ ⊧/v φ.val ↔ V ⊧/(v ·) φ.val :=
  ⟨by simpa [HierarchySymbol.Semiformula.val_sigma] using sigmaOne_upward_absolute V φ.sigma v,
   by simpa [proper.iff', properNat.iff'] using piOne_downward_absolute V φ.pi v⟩

lemma _root_.LO.FirstOrder.Arith.Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' :
    (Fin k → V) → Prop} {φ :
    Dlt1.Semisentence k}
    (hR : Dlt1.Defined R φ) (hR' : Dlt1.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by
  simpa [hR.df.iff, hR'.df.iff] using deltaOne_absolute V φ hR.proper hR'.proper v

lemma _root_.LO.FirstOrder.Arith.DefinedFunction.shigmaOne_absolute_func
    {k} {f : (Fin k → ℕ) → ℕ} {f' :
    (Fin k → V) → V} {φ :
    Sg1.Semisentence (k + 1)}
    (hf : Sg1.DefinedFunction f φ) (hf' : Sg1.DefinedFunction f' φ) (v : Fin k → ℕ) :
    (f v : V) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaOne_absolute V hf.graph_delta hf'.graph_delta (f v :> v)

variable {V}

lemma models_iff_of_Sigma0 {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy Sg 0 σ) {e : Fin n → ℕ} :
    V ⊧/(e ·) σ ↔ ℕ ⊧/e σ := by
  by_cases h : ℕ ⊧/e σ <;> simp [h]
  · have : V ⊧/(e ·) σ := by
      simpa [numeral_eq_natCast] using LO.Arith.bold_sigma_one_completeness' (M :=
        V) (by simp [Hierarchy.of_zero hσ]) h
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : ℕ ⊧/e (∼σ) := by simpa using h
    have : V ⊧/(e ·) (∼σ) := by
      simpa [numeral_eq_natCast] using LO.Arith.bold_sigma_one_completeness' (M := V) (by simp
        [Hierarchy.of_zero hσ]) this
    simpa using this

lemma models_iff_of_Delta1 {σ : Dlt1.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V) {e :
    Fin n → ℕ} :
    V ⊧/(e ·) σ.val ↔ ℕ ⊧/e σ.val := by
  by_cases h : ℕ ⊧/e σ.val <;> simp [h]
  · have : ℕ ⊧/e σ.sigma.val := by simpa [HierarchySymbol.Semiformula.val_sigma] using h
    have : V ⊧/(e ·) σ.sigma.val := by
      simpa [numeral_eq_natCast] using LO.Arith.bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : ℕ ⊧/e (∼σ.pi.val) := by simpa [hσ.iff'] using h
    have : V ⊧/(e ·) (∼σ.pi.val) := by
      simpa [numeral_eq_natCast] using LO.Arith.bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [hσV.iff'] using this

variable {T : Theory ℒₒᵣ} [𝐏𝐀⁻ wkn T] [Sigma1Sound T]

noncomputable instance :
    𝐑₀ wkn T :=
  Entailment.WeakerThan.trans (𝓣 := 𝐏𝐀⁻) inferInstance inferInstance

theorem sigma_one_completeness_iff_param {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy Sg 1 σ) {e :
    Fin n → ℕ} :
    ℕ ⊧/e σ ↔ T ⊢!. (σ <~ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := Iff.trans
  (by simp [models_iff, Semiformula.eval_substs])
  (sigma_one_completeness_iff (T := T) (by simp [hσ]))

lemma models_iff_provable_of_Sigma0_param [V ⊧ₘ* T] {σ : Semisentence ℒₒᵣ n} (hσ :
    Hierarchy Sg 0 σ) {e :
    Fin n → ℕ} :
    V ⊧/(e ·) σ ↔ T ⊢!. (σ <~ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(e ·) σ ↔ ℕ ⊧/e σ        := by simp [models_iff_of_Sigma0 hσ]
  _             ↔ T ⊢!. (σ <~ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp [Hierarchy.of_zero hσ])

lemma models_iff_provable_of_Delta1_param
    [V ⊧ₘ* T] {σ : Dlt1.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV :
    σ.ProperOn V) {e :
    Fin n → ℕ} :
    V ⊧/(e ·) σ.val ↔ T ⊢!. (σ <~ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
  calc
    V ⊧/(e ·) σ.val ↔ ℕ ⊧/e σ.val        := by simp [models_iff_of_Delta1 hσ hσV]
  _                 ↔ ℕ ⊧/e σ.sigma.val  := by simp [HierarchySymbol.Semiformula.val_sigma]
  _                 ↔ T ⊢!. (σ.sigma.val <~ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x)) := by
      apply sigma_one_completeness_iff_param (by simp)
  _                 ↔ T ⊢!. (σ.val <~ fun x ↦ Semiterm.Operator.numeral ℒₒᵣ (e x))       := by
      simp [HierarchySymbol.Semiformula.val_sigma]

end Arith

end FirstOrder
end LO
