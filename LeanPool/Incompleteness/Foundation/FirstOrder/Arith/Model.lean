/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Theory

/-! # Model -/


namespace LO

namespace FirstOrder

namespace Arith
open Language

section «lp_section_1»

variable {L : Language} [L.ORing]

@[simp] lemma oringEmb_operator_zero_val :
    Semiterm.Operator.Zero.zero.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) =
        Semiterm.Operator.Zero.zero.term := by
  simp [Semiterm.Operator.Zero.term_eq, Semiterm.lMap_func, Matrix.empty_eq]

@[simp] lemma oringEmb_operator_one_val :
    Semiterm.Operator.One.one.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) =
        Semiterm.Operator.One.one.term := by
  simp [Semiterm.Operator.One.term_eq, Semiterm.lMap_func, Matrix.empty_eq]

@[simp] lemma oringEmb_operator_add_val :
    Semiterm.Operator.Add.add.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) =
        Semiterm.Operator.Add.add.term := by
  simp [Semiterm.Operator.Add.term_eq, Semiterm.lMap_func]

@[simp] lemma oringEmb_operator_mul_val :
    Semiterm.Operator.Mul.mul.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) =
        Semiterm.Operator.Mul.mul.term := by
  simp [Semiterm.Operator.Mul.term_eq, Semiterm.lMap_func]

@[simp] lemma oringEmb_operator_eq_val :
    .lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) Semiformula.Operator.Eq.eq.sentence =
        Semiformula.Operator.Eq.eq.sentence := by
  simp [Semiformula.Operator.Eq.sentence_eq, Semiformula.lMap_rel]

@[simp] lemma oringEmb_operator_lt_val :
    .lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) Semiformula.Operator.LT.lt.sentence =
        Semiformula.Operator.LT.lt.sentence := by
  simp [Semiformula.Operator.LT.sentence_eq, Semiformula.lMap_rel]

end «lp_section_1»

section «lp_section_2»

section «lp_section_3»

variable (M : Type*) [ORingStruc M]

instance standardModel : Structure ℒₒᵣ M where
  func := fun _ f =>
    match f with
    | ORing.Func.zero => fun _ => 0
    | ORing.Func.one  => fun _ => 1
    | ORing.Func.add  => fun v => v 0 + v 1
    | ORing.Func.mul  => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORing.Rel.eq => fun v => v 0 = v 1
    | ORing.Rel.lt => fun v => v 0 < v 1

instance : Structure.Eq ℒₒᵣ M :=
  ⟨by intro a b; simp[standardModel, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel]⟩

instance : Structure.Zero ℒₒᵣ M := ⟨rfl⟩

instance : Structure.One ℒₒᵣ M := ⟨rfl⟩

instance : Structure.Add ℒₒᵣ M := ⟨fun _ _ => rfl⟩

instance : Structure.Mul ℒₒᵣ M := ⟨fun _ _ => rfl⟩

instance : Structure.Eq ℒₒᵣ M := ⟨fun _ _ => iff_of_eq rfl⟩

instance : Structure.LT ℒₒᵣ M := ⟨fun _ _ => iff_of_eq rfl⟩

instance : ORing ℒₒᵣ := ORing.mk

lemma standardModel_unique' (s : Structure ℒₒᵣ M)
    (hZero : Structure.Zero ℒₒᵣ M) (hOne : Structure.One ℒₒᵣ M) (hAdd : Structure.Add ℒₒᵣ M) (hMul
      : Structure.Mul ℒₒᵣ M)
    (hEq : Structure.Eq ℒₒᵣ M) (hLT : Structure.LT ℒₒᵣ M) : s = standardModel M := Structure.ext
  (funext₃ fun k f _ =>
    match k, f with
    | _, Language.Zero.zero => by simp[Matrix.empty_eq]
    | _, Language.One.one   => by simp[Matrix.empty_eq]
    | _, Language.Add.add   => by simp
    | _, Language.Mul.mul   => by simp)
  (funext₃ fun k r _ =>
    match k, r with
    | _, Language.Eq.eq => by simp
    | _, Language.LT.lt => by simp)

lemma standardModel_unique (s : Structure ℒₒᵣ M)
    [hZero : Structure.Zero ℒₒᵣ M] [hOne : Structure.One ℒₒᵣ M] [hAdd : Structure.Add ℒₒᵣ M] [hMul
      : Structure.Mul ℒₒᵣ M]
    [hEq : Structure.Eq ℒₒᵣ M] [hLT : Structure.LT ℒₒᵣ M] : s = standardModel M :=
  standardModel_unique' M s hZero hOne hAdd hMul hEq hLT

variable {L : Language} [L.ORing] [s : Structure L M]
  [Structure.Zero L M] [Structure.One L M] [Structure.Add L M] [Structure.Mul L M] [Structure.Eq L
    M] [Structure.LT L M]

lemma standardModel_lMap_oringEmb_eq_standardModel : s.lMap (Language.oringEmb :
    ℒₒᵣ →ᵥ L) = standardModel M := by
  apply standardModel_unique' M _
  · exact @Structure.Zero.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (by simpa [Semiterm.Operator.val,
    ←Semiterm.val_lMap] using Structure.Zero.zero)
  · exact @Structure.One.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (by simpa [Semiterm.Operator.val,
    ←Semiterm.val_lMap] using Structure.One.one)
  · exact @Structure.Add.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by
      simpa [Semiterm.Operator.val, ←Semiterm.val_lMap] using Structure.Add.add a b)
  · exact @Structure.Mul.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by
      simpa [Semiterm.Operator.val, ←Semiterm.val_lMap] using Structure.Mul.mul a b)
  · exact @Structure.Eq.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ (fun a b ↦ by
      simpa [Semiformula.Operator.val, ←Semiformula.eval_lMap] using Structure.Eq.eq a b)
  · exact @Structure.LT.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by
      simpa [Semiformula.Operator.val, ←Semiformula.eval_lMap] using Structure.LT.lt a b)

variable {M} {e : Fin n → M} {ε : ξ → M}

@[simp] lemma val_lMap_oringEmb {t : Semiterm ℒₒᵣ ξ n} :
    (t.lMap Language.oringEmb : Semiterm L ξ n).valm M e ε = t.valm M e ε := by
  simp [Semiterm.val_lMap, standardModel_lMap_oringEmb_eq_standardModel]

@[simp] lemma eval_lMap_oringEmb {φ : Semiformula ℒₒᵣ ξ n} :
    Semiformula.Evalm M e ε (.lMap Language.oringEmb φ : Semiformula L ξ n) ↔
        Semiformula.Evalm M e ε φ := by
  simp [Semiformula.eval_lMap, standardModel_lMap_oringEmb_eq_standardModel]

end «lp_section_3»

section «lp_section_4»

variable {L : Language} [L.ORing]
variable {M : Type*} [ORingStruc M] [s : Structure L M]
  [Structure.Zero L M] [Structure.One L M] [Structure.Add L M] [Structure.Mul L M] [Structure.Eq L
    M] [Structure.LT L M]

@[simp] lemma modelsTheory_lMap_oringEmb (T : Theory ℒₒᵣ) :
    M ⊧ₘ* (T.lMap oringEmb : Theory L) ↔ M ⊧ₘ* T := by
  simp only [modelsTheory_iff]
  constructor
  · intro H φ hp f
    exact eval_lMap_oringEmb.mp <| @H (Semiformula.lMap oringEmb φ) (Set.mem_image_of_mem _ hp) f
  · simp only [Theory.lMap, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro H φ hp f; exact eval_lMap_oringEmb.mpr (H hp f)

instance [M ⊧ₘ* 𝐈open] :
    M ⊧ₘ* 𝐏𝐀⁻ :=
  ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ Semiformula.Open)

instance [M ⊧ₘ* 𝐈open] : M ⊧ₘ* Theory.indScheme ℒₒᵣ Semiformula.Open :=
  ModelsTheory.of_add_right M 𝐏𝐀⁻ (Theory.indScheme _ Semiformula.Open)

/-- Imported declaration from the Incompleteness formalization. -/
lemma models_PeanoMinus_of_models_indH (Γ n) [M ⊧ₘ* Theory.indH Γ n] :
    M ⊧ₘ* 𝐏𝐀⁻ :=
  ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ (Arith.Hierarchy Γ n))

/-- Imported declaration from the Incompleteness formalization. -/
lemma models_indScheme_of_models_indH (Γ n) [M ⊧ₘ* Theory.indH Γ n] :
    M ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ n) :=
  ModelsTheory.of_add_right M 𝐏𝐀⁻ (Theory.indScheme _ (Arith.Hierarchy Γ n))

instance models_PeanoMinus_of_models_peano [M ⊧ₘ* 𝐏𝐀] :
    M ⊧ₘ* 𝐏𝐀⁻ :=
  ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ Set.univ)

end «lp_section_4»

end «lp_section_2»

namespace Standard

variable {ξ : Type v} (e : Fin n → ℕ) (ε : ξ → ℕ)

instance models_CobhamR0 : ℕ ⊧ₘ* 𝐑₀ := ⟨by
  intro σ h
  rcases h <;> try { simp [models_def]; done }
  case equal h =>
    have : ℕ ⊧ₘ* (𝐄𝐐 : Theory ℒₒᵣ) := inferInstance
    simpa [models_def] using modelsTheory_iff.mp this h
  case Ω₃ h =>
    simpa [models_def, ←le_iff_eq_or_lt] using h⟩

instance models_PeanoMinus : ℕ ⊧ₘ* 𝐏𝐀⁻ := ⟨by
  intro σ h
  rcases h <;> simp only [models_def, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, Semiformula.eval_operator₂, Semiformula.eval_ex,
    Semiterm.val_operator₂, Semiterm.val_fvar, Semiterm.val_const, Semiterm.val_bvar,
    Matrix.vecCons_zero, Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero,
    ORingStruc.one_eq_one, Structure.Add.add, Structure.Mul.mul, Structure.Eq.eq,
    Structure.LT.lt, Structure.LE.le, LogicalConnective.Prop.arrow_eq,
    LogicalConnective.Prop.and_eq, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq,
    add_zero, mul_zero, mul_one, zero_le, zero_lt_one, add_lt_add_iff_right, lt_self_iff_false,
    not_false_eq_true, implies_true, imp_self, and_imp, Nat.reduceAdd, Nat.succ_eq_add_one,
    Fin.isValue]
  case addAssoc => intro f; exact add_assoc _ _ _
  case addComm  => intro f; exact add_comm _ _
  case mulAssoc => intro f; exact mul_assoc _ _ _
  case mulComm  => intro f; exact mul_comm _ _
  case addEqOfLt => intro f h; exact ⟨f 1 - f 0, Nat.add_sub_of_le (le_of_lt h)⟩
  case oneLeOfZeroLt => intro n hn; exact hn
  case mulLtMul => rintro f h hl; exact (Nat.mul_lt_mul_right hl).mpr h
  case distr => intro f; exact Nat.mul_add _ _ _
  case ltTrans => intro f; exact Nat.lt_trans
  case ltTri => intro f; exact Nat.lt_trichotomy _ _
  case equal h =>
    have : ℕ ⊧ₘ* (𝐄𝐐 : Theory ℒₒᵣ) := inferInstance
    exact modelsTheory_iff.mp this h⟩

lemma models_succInd (φ : Semiformula ℒₒᵣ ℕ 1) : ℕ ⊧ₘ succInd φ := by
  simp only [succInd, Nat.reduceAdd, Fin.isValue, models_iff,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.cons_val_fin_one,
    Semiterm.val_const, Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero,
    Matrix.constant_eq_singleton, Semiformula.eval_all, Nat.succ_eq_add_one, Semiterm.val_bvar,
    Semiterm.val_operator₂, ORingStruc.one_eq_one, Structure.Add.add,
    LogicalConnective.Prop.arrow_eq]
  intro e hzero hsucc x
  induction x with
  | zero => exact hzero
  | succ x ih => exact hsucc x ih

instance models_iSigma (Γ k) : ℕ ⊧ₘ* 𝐈𝐍𝐃Γ k := by
  simp only [ModelsTheory.add_iff, models_PeanoMinus, Theory.indScheme,
    Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]

instance models_iSigmaZero : ℕ ⊧ₘ* 𝐈Sg0 := inferInstance

instance models_iSigmaOne : ℕ ⊧ₘ* 𝐈Sg1 := inferInstance

instance models_peano : ℕ ⊧ₘ* 𝐏𝐀 := by
  simp only [Theory.peano, Theory.indScheme, ModelsTheory.add_iff, models_PeanoMinus,
    Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]

end Standard

section «lp_section_5»

variable (L : Language.{u}) [ORing L]

/-- Imported declaration from the Incompleteness formalization. -/
structure Cut (M : Type w) [s : Structure L M] where
  /-- Imported declaration from the Incompleteness formalization. -/
  domain : Set M
  closedSucc : ∀ x ∈ domain, (‘x. x + 1’).valb s ![x] ∈ domain
  closedLt : ∀ x y : M, Semiformula.Evalb s ![x, y] “x y. x < y” → y ∈ domain → x ∈ domain

/-- Imported declaration from the Incompleteness formalization. -/
structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, Semiformula.Evalb s ![x, y] “x y. x < y” → y ∈ domain → x ∈ domain

end «lp_section_5»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Arith.Theory.TrueArith : Theory ℒₒᵣ := Structure.theory ℒₒᵣ ℕ

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐓𝐀" => Theory.TrueArith

instance _root_.LO.FirstOrder.Arith.Standard.models_trueArith : ℕ ⊧ₘ* 𝐓𝐀 :=
  modelsTheory_iff.mpr fun {φ} ↦ by simp

lemma trueArith_provable_iff {φ : SyntacticFormula ℒₒᵣ} :
    𝐓𝐀 ⊢! φ ↔ ℕ ⊧ₘ φ :=
  ⟨fun h ↦ consequence_iff'.mp (sound₀! h) ℕ, fun h ↦ Entailment.by_axm _ h⟩

instance (T : Theory ℒₒᵣ) [ℕ ⊧ₘ* T] : T wkn 𝐓𝐀 := ⟨by
  rintro φ h
  have : ℕ ⊧ₘ φ := consequence_iff'.mp (sound₀! h) ℕ
  exact trueArith_provable_iff.mpr this⟩

lemma oRing_consequence_of (T : Theory ℒₒᵣ) [𝐄𝐐 wkn T] (φ : SyntacticFormula ℒₒᵣ) (H : ∀ (M :
    Type*) [ORingStruc M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊨ φ := consequence_of T φ fun M _ s _ _ ↦ by
  rcases standardModel_unique M s
  exact H M

lemma oRing_weakerThan_of (T S : Theory ℒₒᵣ) [𝐄𝐐 wkn S]
    (H : ∀ (M : Type*)
           [ORingStruc M]
           [M ⊧ₘ* S],
           M ⊧ₘ* T) : T wkn S :=
  Entailment.weakerThan_iff.mpr fun h ↦ complete <|
      oRing_consequence_of _ _ fun M _ _ ↦ sound! h (H M)

end Arith

namespace Theory

open Arith

instance _root_.LO.FirstOrder.Theory.CobhamR0.consistent : Entailment.Consistent 𝐑₀ :=
  Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* 𝐑₀)⟩

instance _root_.LO.FirstOrder.Theory.Peano.consistent : Entailment.Consistent 𝐏𝐀 :=
  Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* 𝐏𝐀)⟩

instance _root_.LO.FirstOrder.Theory.TrueArith.consistent : Entailment.Consistent 𝐓𝐀 :=
  Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* 𝐓𝐀)⟩

end Theory

end FirstOrder

end LO
