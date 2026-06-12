/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Basic.PeanoMinus

/-! # Ind -/


namespace LO
namespace FirstOrder
namespace Arith

open FirstOrder.Theory

variable {C C' : Semiformula ℒₒᵣ ℕ 1 → Prop}

lemma mem_indScheme_of_mem {φ : Semiformula ℒₒᵣ ℕ 1} (hp : C φ) :
    succInd φ ∈ indScheme ℒₒᵣ C := by
  exact ⟨φ, hp, rfl⟩

lemma mem_iOpen_of_qfree {φ : Semiformula ℒₒᵣ ℕ 1} (hp : φ.Open) :
    succInd φ ∈ indScheme ℒₒᵣ Semiformula.Open := by
  exact ⟨φ, hp, rfl⟩

lemma indScheme_subset (h : ∀ {φ : Semiformula ℒₒᵣ ℕ 1}, C φ → C' φ) :
    indScheme ℒₒᵣ C ⊆ indScheme ℒₒᵣ C' := by
  rintro _ ⟨φ, hp, rfl⟩
  exact ⟨φ, h hp, rfl⟩

lemma iSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈Sg s₁ ⊆ 𝐈Sg s₂ :=
  Set.union_subset_union_right _ (indScheme_subset (fun H ↦ H.mono h))

end Arith
end FirstOrder
end LO

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V]

section «lp_section_1»

section «lp_section_2»

variable {C : Semiformula ℒₒᵣ ℕ 1 → Prop} [V ⊧ₘ* Theory.indScheme ℒₒᵣ C]

private lemma induction_eval {φ : Semiformula ℒₒᵣ ℕ 1} (hp : C φ) (v) :
    Semiformula.Evalm V ![0] v φ →
    (∀ x, Semiformula.Evalm V ![x] v φ → Semiformula.Evalm V ![x + 1] v φ) →
    ∀ x, Semiformula.Evalm V ![x] v φ := by
  have : V ⊧ₘ succInd φ :=
    ModelsTheory.models (T := Theory.indScheme _ C) V (by simpa using mem_indScheme_of_mem hp)
  simp only [succInd, Nat.reduceAdd, Fin.isValue, models_iff,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.cons_val_fin_one,
    Semiterm.val_const, Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero,
    Matrix.constant_eq_singleton, Semiformula.eval_all, Nat.succ_eq_add_one,
    Semiterm.val_bvar, Semiterm.val_operator₂, ORingStruc.one_eq_one, Structure.Add.add,
    LogicalConnective.Prop.arrow_eq] at this
  exact this v

@[elab_as_elim]
lemma induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : Semiformula ℒₒᵣ ℕ 1, C φ ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] e φ) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, φ, Cp, hp⟩; simpa [←hp] using induction_eval (V := V) Cp e

end «lp_section_2»

variable [V ⊧ₘ* 𝐏𝐀⁻]

section «lp_section_3»

variable (Γ : Polarity) (m : ℕ) [V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ m)]

lemma induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (P := P) (C := Hierarchy Γ m) (by
    rcases hP with ⟨φ, hp⟩
    haveI : Inhabited V := Classical.inhabited_of_nonempty'
    exact ⟨φ.val.fvarEnumInv, (Rew.rewriteMap φ.val.fvarEnum) ▹ φ.val, by simp [],
      by  intro x; simp [Semiformula.eval_rewriteMap]
          have : (Semiformula.Evalm V ![x] fun x ↦ φ.val.fvarEnumInv (φ.val.fvarEnum x)) φ.val ↔
            (Semiformula.Evalm V ![x] id) φ.val :=
            Semiformula.eval_iff_of_funEqOn _ (by
              intro x hx
              simp [Semiformula.fvarEnumInv_fvarEnum (Semiformula.mem_fvarList_iff_fvar?.mpr hx)])
          simp [this, hp.df.iff]⟩)
    zero succ

lemma order_induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using induction_h
  · exact Γ
  · exact m
  · suffices Γ-[m].BoldfacePred fun x => ∀ y < x, P y by exact this
    exact HierarchySymbol.Boldface.ball_blt (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => exact inferInstance

private lemma neg_induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using induction_h
    · exact Γ
    · exact m
    · suffices Γ-[m].BoldfacePred fun x => x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Boldface.imp
      · apply HierarchySymbol.Boldface.bcomp₂ (by definability) (by definability)
      · apply HierarchySymbol.Boldface.bcomp₁ (by definability)
    case zero =>
      intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact (not_imp_not.mp <| nsucc (a - (x + 1))) (by
        rw [←sub_sub, sub_add_self_of_le]
        · exact this
        · exact le_tsub_of_add_le_left hx)
    case inst => exact inferInstance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

lemma models_indScheme_alt : V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ.alt m) := by
  simp only [Theory.indScheme, Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp]
  rintro _ φ hp rfl
  simp only [succInd, Nat.reduceAdd, Fin.isValue, models_iff,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.cons_val_fin_one,
    Semiterm.val_const, Structure.numeral_eq_numeral, ORingStruc.zero_eq_zero,
    Matrix.constant_eq_singleton, Semiformula.eval_all, Nat.succ_eq_add_one,
    Semiterm.val_bvar, Semiterm.val_operator₂, ORingStruc.one_eq_one, Structure.Add.add,
    LogicalConnective.Prop.arrow_eq]
  intro v H0 Hsucc x
  have : Semiformula.Evalm V ![0] v φ →
    (∀ x, Semiformula.Evalm V ![x] v φ → Semiformula.Evalm V ![x + 1] v φ) →
      ∀ x, Semiformula.Evalm V ![x] v φ := by
    simpa using
      neg_induction_h Γ m (P := fun x ↦ ¬Semiformula.Evalm V ![x] v φ)
        (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
        (by intro x; simp [←Matrix.constant_eq_singleton', Semiformula.eval_rewriteMap]))
  exact this H0 Hsucc x

instance : V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ.alt m) := models_indScheme_alt Γ m

lemma least_number_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using induction_h
    · exact Γ.alt
    · exact m
    · suffices Γ.alt-[m].BoldfacePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply HierarchySymbol.Boldface.ball_blt (by definability)
      apply HierarchySymbol.Boldface.not
      apply HierarchySymbol.Boldface.bcomp₁ (hP := by simpa using hP) (by definability)
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => exact inferInstance
  exact this (x + 1) x (by simp) h

end «lp_section_3»

section «lp_section_4»

variable (Γ : SigmaPiDelta) (m : ℕ) [V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Sg m)]

lemma induction_hh {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | Sg => induction_h Sg m hP zero succ
  | Pg =>
    haveI : V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Pg m) := models_indScheme_alt Sg m
    induction_h Pg m hP zero succ
  | Dlt => induction_h Sg m hP.of_delta zero succ

lemma order_induction_hh {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | Sg => order_induction_h Sg m hP ind
  | Pg =>
    haveI : V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Pg m) := models_indScheme_alt Sg m
    order_induction_h Pg m hP ind
  | Dlt => order_induction_h Sg m hP.of_delta ind

lemma least_number_hh {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | Sg => least_number_h Sg m hP h
  | Pg =>
    haveI : V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Pg m) := models_indScheme_alt Sg m
    least_number_h Pg m hP h
  | Dlt => least_number_h Sg m hP.of_delta h

end «lp_section_4»

instance [V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Sg m)] :
    V ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ m) := by
  rcases Γ
  · exact inferInstance
  · exact models_indScheme_alt Sg m

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
lemma mod_IOpen_of_mod_indH (Γ n) [V ⊧ₘ* 𝐈𝐍𝐃Γ n] : V ⊧ₘ* 𝐈open :=
  ModelsTheory.of_ss (U := 𝐈𝐍𝐃Γ n) inferInstance
    (Set.union_subset_union_right _ (indScheme_subset Hierarchy.of_open))

/-- Imported declaration from the Incompleteness formalization. -/
lemma mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V ⊧ₘ* Theory.iSigma n₂] :
    V ⊧ₘ* Theory.iSigma n₁ :=
  ModelsTheory.of_ss inferInstance (iSigma_subset_mono h)

instance [V ⊧ₘ* 𝐈open] :
    V ⊧ₘ* 𝐏𝐀⁻ :=
  ModelsTheory.of_add_left V 𝐏𝐀⁻ (Theory.indScheme _ Semiformula.Open)

instance [V ⊧ₘ* 𝐈Sg0] : V ⊧ₘ* 𝐈open := mod_IOpen_of_mod_indH Sg 0

instance [V ⊧ₘ* 𝐈Sg1] : V ⊧ₘ* 𝐈Sg0 := mod_ISigma_of_le (show 0 ≤ 1 from by simp)

instance [V ⊧ₘ* Theory.iSigma n] : V ⊧ₘ* Theory.iPi n :=
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := models_PeanoMinus_of_models_indH Sg n
  inferInstance

instance [V ⊧ₘ* Theory.iPi n] : V ⊧ₘ* Theory.iSigma n :=
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := Arith.models_PeanoMinus_of_models_indH Pg n
  by simp [*]; simpa [Theory.iPi] using models_indScheme_alt (V := V) Pg n

lemma models_ISigma_iff_models_IPi {n} : V ⊧ₘ* 𝐈Sg n ↔ V ⊧ₘ* 𝐈Pg n :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [V ⊧ₘ* Theory.iSigma n] : V ⊧ₘ* Theory.indH Γ n :=
  match Γ with
  | Sg => inferInstance
  | Pg => inferInstance

@[elab_as_elim] lemma induction_sigma0 [V ⊧ₘ* 𝐈Sg0]
    {P : V → Prop} (hP : Sg0.BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h Sg 0 hP zero succ

@[elab_as_elim] lemma induction_sigma1 [V ⊧ₘ* 𝐈Sg1]
    {P : V → Prop} (hP : Sg1-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h Sg 1 hP zero succ

@[elab_as_elim] lemma induction_pi1 [V ⊧ₘ* 𝐈Sg1]
    {P : V → Prop} (hP : Pg1-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_h Pg 1 hP zero succ

@[elab_as_elim] lemma order_induction_sigma0 [V ⊧ₘ* 𝐈Sg0]
    {P : V → Prop} (hP : Sg0-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h Sg 0 hP ind

@[elab_as_elim] lemma order_induction_sigma1 [V ⊧ₘ* 𝐈Sg1]
    {P : V → Prop} (hP : Sg1-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h Sg 1 hP ind

@[elab_as_elim] lemma order_induction_pi1 [V ⊧ₘ* 𝐈Sg1]
    {P : V → Prop} (hP : Pg1-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  order_induction_h Pg 1 hP ind

lemma least_number_sigma0 [V ⊧ₘ* 𝐈Sg0] {P : V → Prop} (hP : Sg0-Predicate P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  least_number_h Sg 0 hP h

@[elab_as_elim] lemma induction_h_sigma1 [V ⊧ₘ* 𝐈Sg1] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := induction_hh Γ 1 hP zero succ

@[elab_as_elim] lemma order_induction_h_sigma1 [V ⊧ₘ* 𝐈Sg1] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := order_induction_hh Γ 1 hP ind

end Arith
end LO

end «lp_nc_section_1»
