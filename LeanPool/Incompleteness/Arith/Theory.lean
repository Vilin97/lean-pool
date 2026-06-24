/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arith.FormalizedArithmetic

/-!

# Formalized $\Sigma_1$-Completeness

-/

namespace LO
namespace FirstOrder

variable {L : Language}

section «lp_section_1»

open Lean PrettyPrinter Delaborator

/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "let " ident " := " term:max firstOrderTerm:61* "; " firstOrderFormula:0 :
    firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "let' " ident " := " term:max firstOrderTerm:61* "; " firstOrderFormula:0 :
    firstOrderFormula

macro_rules
  | `(foFormula[
      $binders* | $fbinders* |
      let $x:ident := $f:term $vs:firstOrderTerm*; $φ:firstOrderFormula]) =>
    `(foFormula[$binders* | $fbinders* | ∃ $x, !$f:term #0 $vs:firstOrderTerm* ∧ $φ])
  | `(foFormula[
      $binders* | $fbinders* |
      let' $x:ident := $f:term $vs:firstOrderTerm*; $φ:firstOrderFormula]) =>
    `(foFormula[$binders* | $fbinders* | ∀ $x, !$f:term #0 $vs:firstOrderTerm* → $φ])

end «lp_section_1»

namespace Theory

/-- Imported declaration from the Incompleteness formalization. -/
inductive CobhamR0' : Theory ℒₒᵣ
  | eq_refl : CobhamR0' “∀ x, x = x”
  | replace (φ : SyntacticSemiformula ℒₒᵣ 1) : CobhamR0' “∀ x y, x = y → !φ x → !φ y”
  | Ω₁ (n m : ℕ)  : CobhamR0' “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ)  : CobhamR0' “↑n * ↑m = ↑(n * m)”
  | Ω₃ (n m : ℕ)  : n ≠ m → CobhamR0' “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : CobhamR0' “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐑₀'" => CobhamR0'

/-- Imported declaration from the Incompleteness formalization. -/
abbrev addCobhamR0' (T : Theory ℒₒᵣ) : Theory ℒₒᵣ := T + 𝐑₀'

end Theory

namespace Arith

open LO.Arith

noncomputable instance _root_.LO.FirstOrder.Arith.CobhamR0'.subtheoryOfCobhamR0 : 𝐑₀' wkn 𝐑₀ :=
  Entailment.WeakerThan.ofAxm! <| by
  intro φ hp
  rcases hp
  · apply complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by simp [models_iff]
  · apply complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by simp [models_iff]
  case Ω₁ n m => exact Entailment.by_axm _ (Theory.CobhamR0.Ω₁ n m)
  case Ω₂ n m => exact Entailment.by_axm _ (Theory.CobhamR0.Ω₂ n m)
  case Ω₃ n m h => exact Entailment.by_axm _ (Theory.CobhamR0.Ω₃ n m h)
  case Ω₄ n => exact Entailment.by_axm _ (Theory.CobhamR0.Ω₄ n)

variable {T : Theory ℒₒᵣ} [𝐑₀ wkn T]

/-- Imported declaration from the Incompleteness formalization. -/
lemma add_cobhamR0' {φ} : T ⊢! φ ↔ T + 𝐑₀' ⊢! φ := by
  constructor
  · intro h; exact Entailment.wk! (by simp [Theory.add_def]) h
  · intro h
    exact Entailment.StrongCut.cut!
      (by
        rintro φ (hp | hp)
        · exact Entailment.by_axm _ hp
        · have : 𝐑₀' ⊢! φ := Entailment.by_axm _ hp
          have : 𝐑₀ ⊢! φ := Entailment.WeakerThan.pbl this
          exact Entailment.WeakerThan.pbl this) h

end Arith

end FirstOrder
end LO

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

section «lp_section_2»

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) →
  Encodable (L.Rel k)] [DefinableLanguage L]

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def singleton (φ : SyntacticFormula L) : Theory.Delta1Definable {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑⌜φ⌝” (by simp)) _
  mem_iff {ψ} := by simp
  isDelta1 :=
    Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

/-- Imported declaration from the Incompleteness formalization. -/
@[simp] lemma singleton_toTDef_ch_val (φ : FirstOrder.SyntacticFormula L) : letI := singleton φ
    (Theory.Delta1Definable.toTDef {φ}).ch.val = “x. x = ↑⌜φ⌝” := rfl

end «lp_section_2»

namespace Formalized

namespace Theory
namespace CobhamR0'

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def eqRefl : FirstOrder.Theory.Delta1Definable {(“∀ x, x = x” : SyntacticFormula ℒₒᵣ)} :=
  singleton _

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def replace : FirstOrder.Theory.Delta1Definable {“∀ x y, x =
      y → !φ x → !φ y” | φ : SyntacticSemiformula ℒₒᵣ 1} where
  ch := .mkDelta
    (.mkSigma
      “p.
      ∃ q < p, !p⌜ℒₒᵣ⌝.isSemiformulaDef.sigma 1 q ∧
      let x0 := qqBvarDef 0;
      let x1 := qqBvarDef 1;
      let eq := qqEQDef x1 x0;
      let v0 := mkVec₁Def x0;
      let v1 := mkVec₁Def x1;
      let q0 := p⌜ℒₒᵣ⌝.substsDef v1 q;
      let q1 := p⌜ℒₒᵣ⌝.substsDef v0 q;
      let imp0 := p⌜ℒₒᵣ⌝.impDef q0 q1;
      let imp1 := p⌜ℒₒᵣ⌝.impDef eq imp0;
      let all0 := qqAllDef imp1;
      !qqAllDef p all0” (by simp))
    (.mkPi
      “p.
      ∃ q < p, !p⌜ℒₒᵣ⌝.isSemiformulaDef.pi 1 q ∧
      let' x0 := qqBvarDef 0;
      let' x1 := qqBvarDef 1;
      let' eq := qqEQDef x1 x0;
      let' v0 := mkVec₁Def x0;
      let' v1 := mkVec₁Def x1;
      let' q0 := p⌜ℒₒᵣ⌝.substsDef v1 q;
      let' q1 := p⌜ℒₒᵣ⌝.substsDef v0 q;
      let' imp0 := p⌜ℒₒᵣ⌝.impDef q0 q1;
      let' imp1 := p⌜ℒₒᵣ⌝.impDef eq imp0;
      let' all0 := qqAllDef imp1;
      !qqAllDef p all0” (by simp))
  mem_iff {φ} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V :=
      ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, Set.mem_setOf_eq,
      HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.val_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
      Matrix.cons_val_fin_one, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
      Matrix.comp_vecCons', Semiterm.val_operator₀, Structure.numeral_eq_numeral,
      ORingStruc.one_eq_one, Matrix.cons_val_zero, Matrix.constant_eq_singleton,
      (Language.isSemiformula_defined (LOR (V := ℕ))).df.iff, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, ORingStruc.zero_eq_zero, eval_qqBvarDef, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, eval_qqEQDef,
      Matrix.cons_val_three, Fin.succ_one_eq_two, eval_mkVec₁Def, Matrix.cons_app_six,
      Matrix.cons_app_five, Matrix.cons_val_four, Matrix.cons_val_succ,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, Matrix.cons_app_seven,
      (Language.imp_defined (LOR (V := ℕ))).df.iff, eval_qqAllDef,
      Language.TermRec.Construction.cons_app_11, Language.TermRec.Construction.cons_app_10,
      Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight,
      LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨x, _, hx, h⟩
      rcases hx.sound with ⟨q, rfl⟩
      exact ⟨q, by
        symm
        apply (quote_inj_iff (V := ℕ)).mp
        simpa [Matrix.constant_eq_singleton] using h⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⌜q⌝, by
        simp only [Fin.isValue, Semiformula.quote_all, Nat.reduceAdd, quote_imply,
          Semiformula.quote_eq', Semiterm.quote_bvar, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          natCast_nat, Nat.zero_mod, quote_substs, Matrix.cons_val_fin_one,
          Matrix.constant_eq_singleton, quote_cons, quote_matrix_empty, semiformula_quote1,
          subst_eq_self₁]
        refine lt_trans ?_ (lt_forall _)
        refine lt_trans ?_ (lt_forall _)
        refine lt_trans ?_ (lt_or_right _ _)
        exact lt_or_right _ _,
        by simp [Matrix.constant_eq_singleton, quote_cons, quote_matrix_empty]⟩
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V :=
        V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.sigma_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Semiterm.val_operator₀, Structure.numeral_eq_numeral, ORingStruc.one_eq_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.constant_eq_singleton,
      (Language.isSemiformula_defined (LOR (V := V))).df.iff, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, ORingStruc.zero_eq_zero, eval_qqBvarDef, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, eval_qqEQDef,
      Matrix.cons_val_three, Fin.succ_one_eq_two, eval_mkVec₁Def, Matrix.cons_app_six,
      Matrix.cons_app_five, Matrix.cons_val_four, Matrix.cons_val_succ,
      (Language.substs_defined (LOR (V := V))).df.iff, Matrix.cons_app_seven,
      (Language.imp_defined (LOR (V := V))).df.iff, eval_qqAllDef,
      Language.TermRec.Construction.cons_app_11, Language.TermRec.Construction.cons_app_10,
      Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight,
      LogicalConnective.Prop.and_eq, exists_eq_left, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi,
      (Language.isSemiformula_defined (LOR (V := V))).proper.iff', Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq]

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def Ω₁ : FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, φ = “↑n + ↑m =
      ↑(n + m)”} where
  ch := .mkDelta
    (.mkSigma “p.
      ∃ n < p, ∃ m < p,
      let numn := numeralDef n;
      let numm := numeralDef m;
      let lhd := qqAddDef numn numm;
      let rhd := numeralDef (n + m);
      !qqEQDef p lhd rhd” (by simp))
    (.mkPi “p.
      ∃ n < p, ∃ m < p,
      let' numn := numeralDef n;
      let' numm := numeralDef m;
      let' lhd := qqAddDef numn numm;
      let' rhd := numeralDef (n + m);
      ∀ p', !qqEQDef p' lhd rhd → p = p'” (by simp))
  mem_iff {φ} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V :=
      ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.vecHead, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralDef, eval_qqAddDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Add.add,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, _, m, _, h⟩
      use n; use m
      exact (quote_inj_iff (V := ℕ)).mp (by simpa using h)
    · rintro ⟨n, m, rfl⟩
      refine ⟨n, by
          simp only [Semiformula.quote_eq', Semiterm.quote_add', quote_numeral_eq_numeral,
            natCast_nat]
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqAdd_left _ _),
        m, by
          simp only [Semiformula.quote_eq', Semiterm.quote_add', quote_numeral_eq_numeral,
            natCast_nat]
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt,
            ←LO.Arith.le_def]) (lt_qqAdd_right _ _), by simp⟩
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V :=
        V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralDef, eval_qqAddDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Add.add,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      Semiformula.eval_all, LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂,
      Matrix.cons_app_seven, Structure.Eq.eq, LogicalConnective.Prop.arrow_eq, forall_eq]

private lemma Ω₁_set_mem_iff {φ : SyntacticFormula ℒₒᵣ} :
    φ ∈ {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, φ = “↑n + ↑m = ↑(n + m)”} ↔
      ∃ n m : ℕ, φ = “↑n + ↑m = ↑(n + m)” := Iff.rfl

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def Ω₂ : FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, φ = “↑n * ↑m =
      ↑(n * m)”} where
  ch := .mkDelta
    (.mkSigma “p.
      ∃ n < p, ∃ m < p,
      let numn := numeralDef n;
      let numm := numeralDef m;
      let lhd := qqMulDef numn numm;
      let rhd := numeralDef (n * m);
      !qqEQDef p lhd rhd” (by simp))
    (.mkPi “p.
      ∃ n < p, ∃ m < p,
      let' numn := numeralDef n;
      let' numm := numeralDef m;
      let' lhd := qqMulDef numn numm;
      let' rhd := numeralDef (n * m);
      ∀ p', !qqEQDef p' lhd rhd → p = p'” (by simp))
  mem_iff {φ} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V :=
      ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.vecHead, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralDef, eval_qqMulDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Mul.mul,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, _, m, _, h⟩
      use n; use m
      exact (quote_inj_iff (V := ℕ)).mp (by simpa using h)
    · rintro ⟨n, m, rfl⟩
      refine ⟨n, by
          simp only [Semiformula.quote_eq', Semiterm.quote_mul', quote_numeral_eq_numeral,
            natCast_nat]
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqMul_left _ _),
        m, by
          simp only [Semiformula.quote_eq', Semiterm.quote_mul', quote_numeral_eq_numeral,
            natCast_nat]
          apply lt_trans ?_ (lt_qqEQ_left _ _)
          apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt,
            ←LO.Arith.le_def]) (lt_qqMul_right _ _), by simp⟩
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V :=
        V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
      Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.constant_eq_singleton,
      eval_numeralDef, eval_qqMulDef, Semiterm.val_operator₂, Matrix.cons_app_five,
      Matrix.cons_val_four, Fin.succ_one_eq_two, Matrix.cons_val_succ, Structure.Mul.mul,
      Matrix.cons_app_six, eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      Semiformula.eval_all, LogicalConnective.HomClass.map_imply, Semiformula.eval_operator₂,
      Matrix.cons_app_seven, Structure.Eq.eq, LogicalConnective.Prop.arrow_eq, forall_eq]

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def Ω₃ : FirstOrder.Theory.Delta1Definable {φ : SyntacticFormula ℒₒᵣ | ∃ n m : ℕ, n ≠ m ∧ φ =
      “↑n ≠ ↑m”} where
  ch := .mkDelta
    (.mkSigma “p. ∃ n < p, ∃ m < p, n ≠ m ∧
      let numn := numeralDef n;
      let numm := numeralDef m;
      !qqNEQDef p numn numm” (by simp))
    (.mkPi “p. ∃ n < p, ∃ m < p, n ≠ m ∧
      let' numn := numeralDef n;
      let' numm := numeralDef m;
      ∀ p', !qqNEQDef p' numn numm → p = p'” (by simp))
  mem_iff {φ} := by
    /-
    simp?
    -/
    simp only [ne_eq, Set.mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.vecHead, LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg,
      Semiformula.eval_operator₂, Matrix.cons_val_zero, Structure.Eq.eq,
      LogicalConnective.Prop.neg_eq, Semiformula.eval_ex, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, Matrix.constant_eq_singleton, eval_numeralDef, Matrix.cons_val_four,
      Fin.succ_one_eq_two, Matrix.cons_val_succ, eval_qqNEQDef, LogicalConnective.Prop.and_eq,
      exists_eq_left]
    constructor
    · rintro ⟨n, _, m, _, ne, h⟩
      refine ⟨n, m, ne, ?_⟩
      exact (quote_inj_iff (V := ℕ)).mp (by simpa using h)
    · rintro ⟨n, m, ne, rfl⟩
      refine ⟨n, by
          simp only [Semiformula.quote_neq', quote_numeral_eq_numeral, natCast_nat]
          exact lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqNEQ_left _ _),
        m, by
          simp only [Semiformula.quote_neq', quote_numeral_eq_numeral, natCast_nat]
          exact lt_of_le_of_lt (by simp [le_iff_eq_or_lt,
            ←LO.Arith.le_def]) (lt_qqNEQ_right _ _), ne, ?_⟩
      simp
  isDelta1 :=
    Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by simp

private lemma quote_disjLt_eq (n : ℕ) :
    ⌜(disjLt (fun i ↦ “#0 = ↑i”) n : SyntacticSemiformula ℒₒᵣ 1)⌝ =
    ^⋁ substItr (^#0 ∷ 0) (^#1 ^= ^#0) n := by
  induction n
  case zero => simp
  case succ n ih =>
    simp only [Fin.isValue, disjLt_succ, Semiformula.quote_or, Semiformula.quote_eq',
      Semiterm.quote_bvar, Fin.val_eq_zero, natCast_nat, quote_numeral_eq_numeral,
      substItr_succ, qqDisj_cons, qqOr_inj]
    rw [substs_eq (by simp) (by simp)]
    simp only [Language.termSubst_bvar, nth_cons_one, nth_cons_zero, Fin.isValue, true_and]
    exact ih

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def Ω₄ : FirstOrder.Theory.Delta1Definable {(“∀ x, x < ↑n ↔
      ⋁ i < n, x = ↑i” : SyntacticFormula ℒₒᵣ) | n} where
  ch := .mkDelta
    (.mkSigma “p. ∃ n < p,
      let numn := numeralDef n;
      let x₀ := qqBvarDef 0;
      let x₁ := qqBvarDef 1;
      let lhd := qqLTDef x₀ numn;
      let v := consDef x₀ 0;
      let e := qqEQDef x₁ x₀;
      let ti := substItrDef v e n;
      let rhd := qqDisjDef ti;
      let iff := p⌜ℒₒᵣ⌝.qqIffDef lhd rhd;
      !qqAllDef p iff” (by simp))
    (.mkPi “p. ∃ n < p,
      let' numn := numeralDef n;
      let' x₀ := qqBvarDef 0;
      let' x₁ := qqBvarDef 1;
      let' lhd := qqLTDef x₀ numn;
      let' v := consDef x₀ 0;
      let' e := qqEQDef x₁ x₀;
      let' ti := substItrDef v e n;
      let' rhd := qqDisjDef ti;
      let' iff := p⌜ℒₒᵣ⌝.qqIffDef lhd rhd;
      !qqAllDef p iff” (by simp))
  mem_iff {p} := by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma, (Language.isSemiformula_defined (LOR (V :=
      ℕ))).df.iff,
      (Language.substs_defined (LOR (V := ℕ))).df.iff, (Language.imp_defined (LOR (V := ℕ))).df.iff,
      (Language.iff_defined (LOR (V := ℕ))).df.iff]
    -/
    simp only [Nat.reduceAdd, Fin.isValue, Set.mem_setOf_eq, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.val_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.constant_eq_singleton,
      eval_numeralDef, Semiterm.val_operator₀, Structure.numeral_eq_numeral,
      ORingStruc.zero_eq_zero, eval_qqBvarDef, ORingStruc.one_eq_one, Matrix.cons_val_two,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_three,
      Fin.succ_one_eq_two, eval_qqLTDef, eval_cons, Matrix.cons_val_four, Matrix.cons_val_succ,
      eval_qqEQDef, Matrix.cons_app_seven, Matrix.cons_app_six, Matrix.cons_app_five,
      substItr_defined_iff, eval_qqDisj, (Language.iff_defined (LOR (V := ℕ))).df.iff,
      Language.TermRec.Construction.cons_app_10, Language.TermRec.Construction.cons_app_9,
      Matrix.cons_app_eight, eval_qqAllDef, LogicalConnective.Prop.and_eq, exists_eq_left]
    constructor
    · rintro ⟨n, _, h⟩
      use n
      symm;
      exact (quote_inj_iff (V := ℕ)).mp (by simpa [quote_disjLt_eq] using h)
    · rintro ⟨n, rfl⟩
      refine ⟨n, by
        simp only [Fin.isValue, Semiformula.quote_all, Nat.reduceAdd, quote_iff,
          Semiformula.quote_lt', Semiterm.quote_bvar, Fin.val_eq_zero, natCast_nat,
          quote_numeral_eq_numeral]
        apply lt_trans ?_ (lt_forall _)
        apply lt_trans ?_ (lt_iff_left _ _)
        apply lt_of_le_of_lt (by simp [le_iff_eq_or_lt, ←LO.Arith.le_def]) (lt_qqLT_right _ _), ?_⟩
      simp [quote_disjLt_eq]
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ by
    /-
    simp? [HierarchySymbol.Semiformula.val_sigma,
      (Language.isSemiformula_defined (LOR (V :=
        V))).df.iff, (Language.isSemiformula_defined (LOR (V := V))).proper.iff',
      (Language.substs_defined (LOR (V := V))).df.iff, (Language.imp_defined (LOR (V := V))).df.iff,
      (Language.iff_defined (LOR (V := V))).df.iff]
    -/
    simp only [Fin.isValue, Nat.reduceAdd, Nat.succ_eq_add_one,
      HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
      Semiformula.eval_bexLT, Semiterm.val_bvar, Semiformula.eval_ex,
      LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.constant_eq_singleton, eval_numeralDef, Semiterm.val_operator₀,
      Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, eval_qqBvarDef, ORingStruc.one_eq_one,
      Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqLTDef, eval_cons, Matrix.cons_val_four,
      Matrix.cons_val_succ, eval_qqEQDef, Matrix.cons_app_seven, Matrix.cons_app_six,
      Matrix.cons_app_five, substItr_defined_iff, eval_qqDisj,
      (Language.iff_defined (LOR (V := V))).df.iff, Language.TermRec.Construction.cons_app_10,
      Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight, eval_qqAllDef,
      LogicalConnective.Prop.and_eq, exists_eq_left, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi, Semiformula.eval_all,
      LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq]

private lemma Ω₄_block_boundary : True := by trivial

end CobhamR0'
end Theory

open Theory.CobhamR0'

instance _root_.LO.Arith.Formalized.Theory.CobhamR0'Delta1Definable : 𝐑₀'.Delta1Definable :=
  (eqRefl.add <| replace.add <| Ω₁.add <| Ω₂.add <| Ω₃.add Ω₄).ofEq <| by
    ext φ; constructor
    · rintro (hφ | hφ | hφ | hφ | hφ | hφ)
      · rcases hφ; exact Theory.CobhamR0'.eq_refl
      · rcases hφ with ⟨φ, rfl⟩; exact FirstOrder.Theory.CobhamR0'.replace φ
      · rcases hφ with ⟨n, m, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₁ n m
      · rcases hφ with ⟨n, m, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₂ n m
      · rcases hφ with ⟨n, m, ne, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₃ n m ne
      · rcases hφ with ⟨n, rfl⟩; exact FirstOrder.Theory.CobhamR0'.Ω₄ n
    · intro hφ; cases hφ
      case eq_refl => left; simp
      case replace φ => right; left; exact ⟨φ, by simp⟩
      case Ω₁ n m => right; right; left; exact ⟨n, m, by simp⟩
      case Ω₂ n m => right; right; right; left; exact ⟨n, m, by simp⟩
      case Ω₃ n m ne => right; right; right; right; left; exact ⟨n, m, ne, by simp⟩
      case Ω₄ n => right; right; right; right; right; exact ⟨n, by simp⟩

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Formalized.Theory.CobhamR0' : ⌜ℒₒᵣ⌝[V].Theory := 𝐑₀'.codeIn V

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Formalized.TTheory.CobhamR0' : ⌜ℒₒᵣ⌝[V].TTheory := 𝐑₀'.tCodeIn V

/-- Imported declaration from the Incompleteness formalization. -/
notation "⌜𝐑₀'⌝" => TTheory.CobhamR0'
/-- Imported declaration from the Incompleteness formalization. -/
notation "⌜𝐑₀'⌝[" V "]" => TTheory.CobhamR0' (V := V)

namespace Theory
namespace CobhamR0'

/-- Imported declaration from the Incompleteness formalization. -/
private lemma cobhamR0'_proof_block_boundary : True := by trivial

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.Theory.CobhamR0'.eqRefl.proof : ⌜𝐑₀'⌝[V] ⊢ (#'0 =' #'0).all :=
  Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_left
  unfold eqRefl
  simp [HierarchySymbol.Semiformula.val_sigma, Theory.tDef, Semiformula.curve, numeral_eq_natCast]
  simp [qqAll, nat_cast_pair, qqEQ, qqRel, cons_absolute, qqBvar]
  constructor <;> rfl

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.Theory.CobhamR0'.replace.proof (φ : ⌜ℒₒᵣ⌝[V].Semiformula (0 + 1)) :
    ⌜𝐑₀'⌝[V] ⊢ (#'1 =' #'0 ==> φ^/[(#'1).sing] ==> φ^/[(#'0).sing]).all.all :=
      Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold replace
  simp only [Semiformula.curve, Nat.succ_eq_add_one, Nat.reduceAdd, Theory.tDef,
    Fin.isValue, HierarchySymbol.Semiformula.val_sigma,
    HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.vecCons_zero,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Semiterm.val_const, Structure.numeral_eq_numeral, ORingStruc.one_eq_one,
    Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
    (Language.isSemiformula_defined (LOR (V := V))).df.iff, Matrix.cons_val_one,
    Semiformula.eval_ex, ORingStruc.zero_eq_zero, eval_qqBvarDef, Matrix.cons_app_two,
    eval_qqEQDef, Matrix.cons_app_three, eval_mkVec₁Def, Matrix.cons_app_six,
    Matrix.cons_app_five, Matrix.cons_app_four,
    (Language.substs_defined (LOR (V := V))).df.iff, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Matrix.cons_app_seven,
    (Language.imp_defined (LOR (V := V))).df.iff, eval_qqAllDef,
    Language.TermRec.Construction.cons_app_11, Language.TermRec.Construction.cons_app_10,
    Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight,
    LogicalConnective.Prop.and_eq, exists_eq_left, Language.Semiformula.val_all,
    Language.Semiformula.val_imp, val_equals, Language.val_bvar, Language.Semiformula.val_substs,
    Language.Semitermvec.val_cons, Language.Semitermvec.val_nil, Set.mem_setOf_eq,
    qqAll_inj]
  refine ⟨φ.val, ?_, by simpa using φ.prop, rfl⟩
  · rw [subst_eq_self₁ (by simpa using φ.prop)]
    refine lt_trans ?_ (lt_forall _)
    refine lt_trans ?_ (lt_forall _)
    refine lt_trans ?_ (lt_or_right _ _)
    exact lt_or_right _ _

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.Theory.CobhamR0'.Ω₁.proof (n m : V) :
    ⌜𝐑₀'⌝[V] ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := Language.Theory.TProof.byAxm <| by
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₁
  simp only [Semiformula.curve, Nat.succ_eq_add_one, Nat.reduceAdd, Theory.tDef,
    Fin.isValue, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
    Matrix.vecCons_zero, Matrix.cons_val_one, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.cons_val_fin_one, Matrix.cons_app_two, Matrix.constant_eq_singleton,
    eval_numeralDef, eval_qqAddDef, Semiterm.val_operator₂, Matrix.cons_app_five,
    Matrix.cons_app_four, Matrix.cons_app_three, Structure.Add.add, Matrix.cons_app_six,
    eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left, val_equals, val_add,
    val_numeral, Set.mem_setOf_eq]
  refine ⟨n, ?_, m, ?_, rfl⟩
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqAdd_left _ _)
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqAdd_right _ _)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.Theory.CobhamR0'.Ω₂.proof (n m : V) :
    ⌜𝐑₀'⌝[V] ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := Language.Theory.TProof.byAxm <| by
  iterate 3 apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₂
  simp only [Semiformula.curve, Nat.succ_eq_add_one, Nat.reduceAdd, Theory.tDef,
    Fin.isValue, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
    Matrix.vecCons_zero, Matrix.cons_val_one, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.cons_val_fin_one, Matrix.cons_app_two, Matrix.constant_eq_singleton,
    eval_numeralDef, eval_qqMulDef, Semiterm.val_operator₂, Matrix.cons_app_five,
    Matrix.cons_app_four, Matrix.cons_app_three, Structure.Mul.mul, Matrix.cons_app_six,
    eval_qqEQDef, LogicalConnective.Prop.and_eq, exists_eq_left, val_equals, val_mul,
    val_numeral, Set.mem_setOf_eq]
  refine ⟨n, ?_, m, ?_, rfl⟩
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqMul_left _ _)
  · apply lt_trans ?_ (lt_qqEQ_left _ _)
    apply lt_of_le_of_lt (by simp) (lt_qqMul_right _ _)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.Theory.CobhamR0'.Ω₃.proof {n m : V} (ne : n ≠ m) :
    ⌜𝐑₀'⌝[V] ⊢ ↑n ≠' ↑m :=
  Language.Theory.TProof.byAxm <| by
  iterate 4 apply FirstOrder.Semiformula.curve_mem_right
  apply FirstOrder.Semiformula.curve_mem_left
  unfold Ω₃
  simp only [Semiformula.curve, Nat.succ_eq_add_one, Nat.reduceAdd, Theory.tDef,
    Fin.isValue, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
    Matrix.vecCons_zero, Matrix.cons_val_one, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_neg, Semiformula.eval_operator₂, Structure.Eq.eq,
    LogicalConnective.Prop.neg_eq, Semiformula.eval_ex, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.cons_val_fin_one, Matrix.cons_app_two,
    Matrix.constant_eq_singleton, eval_numeralDef, Matrix.cons_app_four,
    Matrix.cons_app_three, eval_qqNEQDef, LogicalConnective.Prop.and_eq, exists_eq_left,
    val_notEquals, val_numeral, Set.mem_setOf_eq]
  refine ⟨n, ?_, m, ?_, ne, rfl⟩
  · exact lt_of_le_of_lt (by simp) (lt_qqNEQ_left _ _)
  · exact lt_of_le_of_lt (by simp) (lt_qqNEQ_right _ _)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Formalized.Theory.CobhamR0'.Ω₄.proof (n :
    V) : ⌜𝐑₀'⌝[V] ⊢ (#'0 <' ↑n <=> (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all :=
  Language.Theory.TProof.byAxm <| by
  iterate 5 apply FirstOrder.Semiformula.curve_mem_right
  unfold Ω₄
  simp only [Semiformula.curve, Nat.succ_eq_add_one, Nat.reduceAdd, Theory.tDef,
    Fin.isValue, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLT, Semiterm.val_bvar,
    Matrix.vecCons_zero, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.constant_eq_singleton, eval_numeralDef, Semiterm.val_const,
    Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero, eval_qqBvarDef,
    ORingStruc.one_eq_one, Matrix.cons_app_two, Matrix.cons_app_three, eval_qqLTDef,
    eval_cons, Matrix.cons_app_four, eval_qqEQDef, Matrix.cons_app_seven,
    Matrix.cons_app_six, Matrix.cons_app_five, substItr_defined_iff, eval_qqDisj,
    (Language.iff_defined (LOR (V := V))).df.iff, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Language.TermRec.Construction.cons_app_10,
    Language.TermRec.Construction.cons_app_9, Matrix.cons_app_eight, eval_qqAllDef,
    LogicalConnective.Prop.and_eq, exists_eq_left, Language.Semiformula.val_all,
    Language.Semiformula.val_iff, val_lessThan, Language.val_bvar, val_numeral,
    Language.SemiformulaVec.val_disj, val_tSubstItr, Language.Semitermvec.val_cons,
    Language.Semitermvec.val_nil, val_equals, Set.mem_setOf_eq, qqAll_inj]
  refine ⟨n, ?_, rfl⟩
  apply lt_trans ?_ (lt_forall _)
  apply lt_trans ?_ (lt_iff_left _ _)
  apply lt_of_le_of_lt (by simp) (lt_qqLT_right _ _)

end CobhamR0'
end Theory

instance _root_.LO.Arith.Formalized.Theory.addCobhamR0'Delta1Definable (T : Theory ℒₒᵣ) [d :
    T.Delta1Definable] : (T + 𝐑₀').Delta1Definable :=
  d.add Theory.CobhamR0'Delta1Definable
section «lp_section_3»

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.AddR₀TTheory : ⌜ℒₒᵣ⌝[V].TTheory := (T + 𝐑₀').tCodeIn V

variable {T}

@[simp] lemma R₀'_subset_AddR₀ : ⌜𝐑₀'⌝[V] ⊆ T.AddR₀TTheory := Set.subset_union_right

@[simp] lemma theory_subset_AddR₀ : T.tCodeIn V ⊆ T.AddR₀TTheory :=
  FirstOrder.Theory.Delta1Definable.add_subset_left _ _

instance : R₀Theory (T.AddR₀TTheory (V := V)) where
  refl := Language.Theory.TProof.ofSubset (by simp) Theory.CobhamR0'.eqRefl.proof
  replace := fun φ ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.replace.proof φ)
  add := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₁.proof n m)
  mul := fun n m ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₂.proof n m)
  ne := fun h ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₃.proof h)
  ltNumeral := fun n ↦ Language.Theory.TProof.ofSubset (by simp) (Theory.CobhamR0'.Ω₄.proof n)

end «lp_section_3»

end Formalized

open Formalized

section «lp_section_4»

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

/-- Provability predicate for arithmetic stronger than $\mathbf{R_0}$. -/
def _root_.LO.FirstOrder.Theory.Provableₐ (φ : V) : Prop := ((T + 𝐑₀').codeIn V).Provable φ

variable {T}

lemma provableₐ_iff {σ : Sentence ℒₒᵣ} : T.Provableₐ (⌜σ⌝ : V) ↔ (T + 𝐑₀').tCodeIn V ⊢! ⌜σ⌝ := by
  simp [Language.Theory.TProvable.iff_provable]; rfl

section «lp_section_5»

variable (T)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Theory.provableₐ : Sg1.Semisentence 1 := .mkSigma
  “p. !(T + 𝐑₀').tDef.prv p” (by simp)

lemma provableₐ_defined : Sg1-Predicate (T.Provableₐ : V → Prop) via T.provableₐ := by
  intro v; simp [FirstOrder.Theory.provableₐ, FirstOrder.Theory.Provableₐ,
    ((T + 𝐑₀').codeIn V).provable_defined.df.iff]

@[simp] lemma eval_provableₐ (v) :
    Semiformula.Evalbm V v T.provableₐ.val ↔ T.Provableₐ (v 0) := (provableₐ_defined T).df.iff v

instance provableₐ_definable : Sg1-Predicate (T.Provableₐ : V → Prop) :=
  (provableₐ_defined T).to_definable

/-- instance for definability tactic -/
instance provableₐ_definable' : Sg-[0 + 1]-Predicate (T.Provableₐ : V → Prop) :=
  provableₐ_definable T

end «lp_section_5»

end «lp_section_4»

end Arith
end LO
