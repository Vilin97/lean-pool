/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arith.Theory

/-! # D1 -/


noncomputable section «lp_nc_section_1»

namespace LO
namespace FirstOrder

open LO.Arith FirstOrder.Arith

/-- Local classical decidable equality instance used by imported proofs. -/
local instance instDecidableEqOfClassical (α : Sort _) : DecidableEq α := Classical.decEq α

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [L.DecidableEq] [(k : ℕ) → Encodable (L.Func k)]
variable [(k : ℕ) → Encodable (L.Rel k)]

variable (V)

namespace Derivation2

/-- Imported declaration from the Incompleteness formalization. -/
def cast {T : Theory L} (d : T ⊢₂ Γ) (h : Γ = Δ) : T ⊢₂ Δ := h ▸ d

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.FirstOrder.Derivation2.Sequent.codeIn
    (Γ : Finset (SyntacticFormula L)) :
    V := ∑ φ ∈ Γ, exp (⌜φ⌝ : V)

noncomputable instance : GoedelQuote (Finset (SyntacticFormula L)) V := ⟨Sequent.codeIn V⟩

omit [L.DecidableEq] in
lemma _root_.LO.FirstOrder.Derivation2.Sequent.codeIn_def
    (Γ : Finset (SyntacticFormula L)) : ⌜Γ⌝ = ∑ φ ∈ Γ, exp (⌜φ⌝ :
    V) := rfl

variable {V}

omit [L.DecidableEq] in
@[simp] lemma _root_.LO.FirstOrder.Derivation2.Sequent.codeIn_empty
    : (⌜(∅ : Finset (SyntacticFormula L))⌝ :
    V) = ∅ := by simp [Sequent.codeIn_def, emptyset_def]

lemma _root_.LO.FirstOrder.Derivation2.Sequent.mem_codeIn_iff
    {Γ : Finset (SyntacticFormula L)} {φ} : ⌜φ⌝ ∈ (⌜Γ⌝ :
    V) ↔ φ ∈ Γ := by
  induction Γ using Finset.induction generalizing φ
  case empty => simp [Sequent.codeIn_def]
  case insert a Γ ha ih =>
    have : exp ⌜a⌝ + ∑ φ ∈ Γ, exp (⌜φ⌝ : V) = insert (⌜a⌝ : V) (⌜Γ⌝ : V) := by
      simp only [insert, bitInsert, (not_iff_not.mpr ih.symm).mp ha, ↓reduceIte,
        add_comm, add_right_inj]
      rw [Sequent.codeIn_def]
    simp only [Sequent.codeIn_def, ha, not_false_eq_true, Finset.sum_insert,
      Finset.mem_insert]
    rw [this]
    simp [←ih]

lemma _root_.LO.FirstOrder.Derivation2.Sequent.quote_inj
    {Γ Δ : Finset (SyntacticFormula L)} : (⌜Γ⌝ :
    V) = ⌜Δ⌝ → Γ = Δ := fun h ↦ by
  ext φ; simp [←Sequent.mem_codeIn_iff (V := V), h]

lemma _root_.LO.FirstOrder.Derivation2.Sequent.subset_of_quote_subset_quote {Γ Δ :
    Finset (SyntacticFormula L)} :
    (⌜Γ⌝ : V) ⊆ ⌜Δ⌝ → Γ ⊆ Δ := fun h _ hp ↦
  Sequent.mem_codeIn_iff.mp <| h <| Sequent.mem_codeIn_iff.mpr hp

omit [L.DecidableEq] in
@[simp] lemma _root_.LO.FirstOrder.Derivation2.Sequent.codeIn_singleton [L.DecidableEq] (φ :
    SyntacticFormula L) :
    (⌜({φ} : Finset (SyntacticFormula L))⌝ : V) = {⌜φ⌝} := by simp [Sequent.codeIn_def]; rfl

omit [L.DecidableEq] in
@[simp] lemma _root_.LO.FirstOrder.Derivation2.Sequent.codeIn_insert
    [L.DecidableEq] (Γ : Finset (SyntacticFormula L)) (φ) : (⌜(insert φ Γ)⌝ :
    V) = insert ⌜φ⌝ ⌜Γ⌝ := by
  by_cases hp : φ ∈ Γ
  · simp [Sequent.mem_codeIn_iff, hp, insert_eq_self_of_mem]
  · have : (⌜insert φ Γ⌝ : V) = exp ⌜φ⌝ + ⌜Γ⌝ := by simp [Sequent.codeIn_def, hp]
    simp [Sequent.mem_codeIn_iff, this, insert_eq, bitInsert, hp, add_comm]

omit [L.DecidableEq] in
lemma _root_.LO.FirstOrder.Derivation2.Sequent.mem_codeIn
    [L.DecidableEq] {Γ : Finset (SyntacticFormula L)} (hx : x ∈ (⌜Γ⌝ : V)) :
    ∃ φ ∈ Γ, x = ⌜φ⌝ := by
  induction Γ using Finset.induction
  case empty => simp at hx
  case insert a Γ _ ih =>
    have : x = ⌜a⌝ ∨ x ∈ (⌜Γ⌝ : V) := by simpa using hx
    rcases this with (rfl | hx)
    · exact ⟨a, by simp⟩
    · rcases ih hx with ⟨p, hx, rfl⟩
      exact ⟨p, by simp [*]⟩

lemma _root_.LO.FirstOrder.Derivation2.Sequent.mem_codeIn_iff'
    {Γ : Finset (SyntacticFormula L)} : x ∈ (⌜Γ⌝ :
    V) ↔ (∃ φ ∈ Γ, x = ⌜φ⌝) := by
  constructor
  · intro h; exact Sequent.mem_codeIn h
  · rintro ⟨p, hp, rfl⟩; simp [Sequent.mem_codeIn_iff, hp]

lemma setShift_quote [DefinableLanguage L] (Γ : Finset (SyntacticFormula L)) :
    (L.codeIn V).setShift ⌜Γ⌝ = ⌜Finset.image Rewriting.shift Γ⌝ := by
  apply mem_ext
  intro x; simp only [mem_setShift_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Sequent.mem_codeIn hx with ⟨p, _, rfl⟩
    rw [←quote_shift, Sequent.mem_codeIn_iff]
    simpa only [Finset.mem_image] using ⟨p, by simpa [Sequent.mem_codeIn_iff] using hx, rfl⟩
  · intro hx
    rcases Sequent.mem_codeIn hx with ⟨p', hp', rfl⟩
    rcases by simpa using hp' with ⟨p, hp, rfl⟩
    exact ⟨⌜p⌝, by simpa [Sequent.mem_codeIn_iff] using hp, by simp⟩

variable (V)

variable {T : Theory L}

/-- Imported declaration from the Incompleteness formalization. -/
def codeIn : {Γ : Finset (SyntacticFormula L)} → T ⊢₂ Γ → V
  | _, closed Δ φ _ _                         => Arith.axL ⌜Δ⌝ ⌜φ⌝
  | _, root (Δ := Δ) φ _ _                    => Arith.root ⌜Δ⌝ ⌜φ⌝
  | _, verum (Δ := Δ) _                       => Arith.verumIntro ⌜Δ⌝
  | _, and (Δ := Δ) _ (φ := φ) (ψ := ψ) bp bq => Arith.andIntro ⌜Δ⌝ ⌜φ⌝ ⌜ψ⌝ bp.codeIn bq.codeIn
  | _, or (Δ := Δ) (φ := φ) (ψ := ψ) _ d      => Arith.orIntro ⌜Δ⌝ ⌜φ⌝ ⌜ψ⌝ d.codeIn
  | _, all (Δ := Δ) (φ := φ) _ d              => Arith.allIntro ⌜Δ⌝ ⌜φ⌝ d.codeIn
  | _, ex (Δ := Δ) (φ := φ) _ t d             => Arith.exIntro ⌜Δ⌝ ⌜φ⌝ ⌜t⌝ d.codeIn
  | _, wk (Γ := Γ) d _                        => Arith.wkRule ⌜Γ⌝ d.codeIn
  | _, shift (Δ := Δ) d                       => Arith.shiftRule ⌜Δ.image Rewriting.shift⌝ d.codeIn
  | _, cut (Δ := Δ) (φ := φ) d dn             => Arith.cutRule ⌜Δ⌝ ⌜φ⌝ d.codeIn dn.codeIn

instance (Γ : Finset (SyntacticFormula L)) : GoedelQuote (T ⊢₂ Γ) V := ⟨codeIn V⟩

lemma quote_derivation_def
    {Γ : Finset (SyntacticFormula L)} (d : T ⊢₂ Γ) : (⌜d⌝ : V) = d.codeIn V :=
  rfl

@[simp] lemma fstidx_quote
    {Γ : Finset (SyntacticFormula L)} (d : T ⊢₂ Γ) : fstIdx (⌜d⌝ : V) = ⌜Γ⌝ := by
  induction d <;> simp [quote_derivation_def, codeIn]

end Derivation2

end FirstOrder
end LO

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith FirstOrder.Semiformula

/-- Local classical decidable equality instance used by imported proofs. -/
local instance instDecidableEqOfClassical₂ (α : Sort _) : DecidableEq α := Classical.decEq α

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]
variable [DefinableLanguage L]

variable {T : Theory L} [T.Delta1Definable]

@[simp] lemma formulaSet_codeIn_finset (Γ : Finset (SyntacticFormula L)) :
    (L.codeIn V).IsFormulaSet ⌜Γ⌝ := by
  intro x hx
  rcases Derivation2.Sequent.mem_codeIn hx with ⟨p, _, rfl⟩;
  apply semiformula_quote (n := 0)

open Derivation2

lemma quote_image_shift
    [L.DecidableEq] (Γ : Finset (SyntacticFormula L)) : (L.codeIn V).setShift (⌜Γ⌝ :
    V) = ⌜Γ.image Rewriting.shift⌝ := by
  induction Γ using Finset.induction
  case empty => simp
  case insert φ Γ _ ih => simp [ih]

@[simp] lemma derivation_quote [L.DecidableEq] {Γ : Finset (SyntacticFormula L)} (d : T ⊢₂ Γ) :
    (T.codeIn V).Derivation ⌜d⌝ := by
  induction d
  case closed φ hp hn =>
    exact Language.Theory.Derivation.axL (by simp)
      (by simp [Sequent.mem_codeIn_iff, hp])
      (by rw [←quote_neg, Sequent.mem_codeIn_iff]; simp [hn])
  case root Δ φ hT hp =>
    apply Language.Theory.Derivation.root (by simp)
      (by simp [Sequent.mem_codeIn_iff, hp])
      (by simp [hT])
  case verum Δ h =>
    exact Language.Theory.Derivation.verumIntro (by simp)
      (by simpa [quote_verum] using (Sequent.mem_codeIn_iff (V := V)).mpr h)
  case and Δ φ ψ hpq dp dq ihp ihq =>
    apply Language.Theory.Derivation.andIntro
      (by simpa [quote_and] using (Sequent.mem_codeIn_iff (V := V)).mpr hpq)
      ⟨by simp [fstidx_quote], ihp⟩
      ⟨by simp [fstidx_quote], ihq⟩
  case or Δ φ ψ hpq d ih =>
    apply Language.Theory.Derivation.orIntro
      (by simpa [quote_or] using (Sequent.mem_codeIn_iff (V := V)).mpr hpq)
      ⟨by simp [fstidx_quote], ih⟩
  case all Δ φ h d ih =>
    apply Language.Theory.Derivation.allIntro
      (by simpa [quote_all] using (Sequent.mem_codeIn_iff (V := V)).mpr h)
      ⟨by simp [fstidx_quote, quote_image_shift, free_quote], ih⟩
  case ex Δ φ h t d ih =>
    apply Language.Theory.Derivation.exIntro
      (by simpa [quote_ex] using (Sequent.mem_codeIn_iff (V := V)).mpr h)
      (semiterm_codeIn t)
      ⟨by simp [fstidx_quote, Language.substs₁, Matrix.constant_eq_singleton, quote_cons,
        quote_matrix_empty], ih⟩
  case wk Δ Γ d h ih =>
    apply Language.Theory.Derivation.wkRule (s' := ⌜Δ⌝)
      (by simp)
      (by intro x hx; rcases Sequent.mem_codeIn hx with ⟨p, hp, rfl⟩
          simp [Sequent.mem_codeIn_iff, h hp])
      ⟨by simp [fstidx_quote], ih⟩
  case shift Δ d ih =>
    simp only [quote_derivation_def, Derivation2.codeIn, ←quote_image_shift]
    apply Language.Theory.Derivation.shiftRule
      ⟨by simp [fstidx_quote], ih⟩
  case cut Δ φ d dn ih ihn =>
    apply Language.Theory.Derivation.cutRule
      ⟨by simp [fstidx_quote], ih⟩
      ⟨by simp [fstidx_quote], ihn⟩

@[simp] lemma derivationOf_quote {Γ : Finset (SyntacticFormula L)} (d : T ⊢₂ Γ) :
    (T.codeIn V).DerivationOf ⌜d⌝ ⌜Γ⌝ :=
  ⟨by simp, by simp⟩

lemma derivable_of_quote {Γ : Finset (SyntacticFormula L)} (d : T ⊢₂ Γ) :
    (T.codeIn V).Derivable ⌜Γ⌝ :=
  ⟨⌜d⌝, by simp⟩

section «lp_section_1»

variable {T : Theory L} [T.Delta1Definable]

theorem provable_of_provable {φ} : T ⊢! φ → (T.codeIn V).Provable ⌜φ⌝ := fun h ↦ by
  unfold Language.Theory.Provable
  simpa using derivable_of_quote (V := V) (provable_iff_derivable2.mp h).some

/-- Hilbert–Bernays provability condition D1 -/
theorem tprovable_of_provable {φ} : T ⊢! φ → T.tCodeIn V ⊢! ⌜φ⌝ := fun h ↦ by
  apply Language.Theory.TProvable.iff_provable.mpr
  exact provable_of_provable (V := V) h

end «lp_section_1»

section «lp_section_2»

variable {T : Theory ℒₒᵣ} [T.Delta1Definable]

theorem provableₐ_of_provable {σ} : T ⊢! σ → T.Provableₐ (⌜σ⌝ : V) := fun h ↦
  Language.Theory.Derivable.of_ss Formalized.theory_subset_AddR₀ (provable_of_provable h)

end «lp_section_2»

end Arith
end LO

namespace Nat

lemma double_add_one_div_of_double (n m : ℕ) : (2 * n + 1) / (2 * m) = n / m := calc
      (2 * n + 1) / (2 * m)
    = (1 + 2 * n) / 2 / m := by simp [add_comm, Nat.div_div_eq_div_mul]
  _ = n / m := by simp [Nat.add_mul_div_left]

example (x : ℕ) : ¬Odd (2 * x) := by { refine not_odd_iff_even.mpr (even_two_mul x) }

lemma mem_bitIndices_iff {x s : ℕ} : x ∈ s.bitIndices ↔ Odd (s / 2 ^ x) := by
  induction s using Nat.binaryRec generalizing x
  case zero => simp []
  case bit b s ih =>
    cases b
    · simp only [bit_false_apply, bitIndices_two_mul, List.mem_map, ih]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm],
          Nat.mul_div_mul_left _ _ (by simp)]
        exact hx
      · intro h
        cases x with
        | zero => simp [not_odd_iff_even.mpr (even_two_mul s)] at h
        | succ x =>
          refine ⟨x, ?_, rfl⟩
          rwa [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm],
            Nat.mul_div_mul_left _ _ (by simp)] at h
    · simp only [bit_true_apply, bitIndices_two_mul_add_one, List.mem_cons, List.mem_map, ih]
      constructor
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · simp
        · rw [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm],
          double_add_one_div_of_double]
          exact hx
      · intro h
        cases x with
        | zero => simp
        | succ x =>
          right
          refine ⟨x, ?_, rfl⟩
          rwa [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm],
            double_add_one_div_of_double] at h

end Nat

namespace LO
namespace FirstOrder

variable {L : Language} {T : Theory L}

end FirstOrder
end LO

namespace LO
namespace Arith

open FirstOrder Encodable

variable {L : Language} [L.DecidableEq] [(k : ℕ) → Encodable (L.Func k)]
variable [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

lemma isFormulaSet_sound {s : ℕ} : (L.codeIn ℕ).IsFormulaSet s → ∃ S :
    Finset (SyntacticFormula L), ⌜S⌝ = s := by
  intro h
  have : ∀ x, ∃ φ : SyntacticFormula L, x ∈ s → ⌜φ⌝ = x := by
    intro x
    by_cases hx : x ∈ s
    · rcases (h x hx).sound with ⟨φ, hφ⟩
      exact ⟨φ, fun _ => hφ⟩
    · exact ⟨⊥, fun hx' => False.elim (hx hx')⟩
  choose ps hps using this
  exact ⟨(s.bitIndices.map ps).toFinset, by
    apply mem_ext
    intro x
    constructor
    · intro h
      rcases Derivation2.Sequent.mem_codeIn h with ⟨p, hp, rfl⟩
      rcases by simp only [List.mem_toFinset, List.mem_map] at hp; exact hp with ⟨x, hx, rfl⟩
      simpa [hps x (mem_iff_mem_bitIndices.mpr hx)] using mem_iff_mem_bitIndices.mpr hx
    · intro h
      rw [←hps x h]
      simp only [Derivation2.Sequent.mem_codeIn_iff, List.mem_toFinset, List.mem_map,
        ←mem_iff_mem_bitIndices]
      exact ⟨x, h, rfl⟩⟩

section «lp_section_3»

variable {T : Theory L} [T.Delta1Definable]

open Derivation2

lemma _root_.LO.Arith.Language.Theory.Derivation.sound {d : ℕ} (h : (T.codeIn ℕ).Derivation d) :
    ∃ Γ, ⌜Γ⌝ = fstIdx d ∧ T ⊢₂! Γ := by
  induction d using Nat.strongRec
  case ind d ih =>
  rcases h.case with ⟨hs, H⟩
  rcases isFormulaSet_sound hs with ⟨Γ, hΓ⟩
  refine ⟨Γ, hΓ, ?_⟩
  rcases H with (⟨s, φ, rfl, hφ, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, φ, ψ, dp, dq, rfl, hpq, ⟨hφ, hdφ⟩, ⟨hψ, hdq⟩⟩ | ⟨s, φ, ψ, d, rfl, hpq, ⟨h, hd⟩⟩ |
    ⟨s, φ, d, rfl, hps, hd, dd⟩ | ⟨s, φ, t, d, rfl, hps, ht, hd, dd⟩ |
    ⟨s, d, rfl, hs, dd⟩ | ⟨s, d, rfl, rfl, dd⟩ |
    ⟨s, φ, d₁, d₂, rfl, ⟨h₁, dd₁⟩, ⟨h₂, dd₂⟩⟩ | ⟨s, φ, rfl, hs, hT⟩)
  · rcases (hs φ (by simp [hφ])).sound with ⟨φ, rfl⟩
    refine ⟨Derivation2.closed Γ φ
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), hΓ, hφ])
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), hΓ, hnp])⟩
  · refine ⟨Derivation2.verum (by simp [←Sequent.mem_codeIn_iff (V := ℕ), hΓ,
    Semiformula.quote_verum, hv])⟩
  · have fpq : (L.codeIn ℕ).IsFormula φ ∧
      (L.codeIn ℕ).IsFormula ψ := by simpa using hs (φ ^⋏ ψ) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨φ, rfl⟩
    rcases fpq.2.sound with ⟨ψ, rfl⟩
    rcases ih dp (by simp) hdφ with ⟨Γφ, hΓφ, ⟨bφ⟩⟩
    rcases ih dq (by simp) hdq with ⟨Γψ, hΓψ, ⟨bψ⟩⟩
    refine ⟨Derivation2.and (φ := φ) (ψ := ψ)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_and, hpq])
      (bφ.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΓφ, hφ]))
      (bψ.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΓψ, hψ]))⟩
  · have fpq : (L.codeIn ℕ).IsFormula φ ∧
      (L.codeIn ℕ).IsFormula ψ := by simpa using hs (φ ^⋎ ψ) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨φ, rfl⟩
    rcases fpq.2.sound with ⟨ψ, rfl⟩
    rcases ih d (by simp) hd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.or (φ := φ) (ψ := ψ)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_or, hpq])
      (b.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΔ, h]))⟩
  · rcases by simpa using hΓ
    have : (L.codeIn ℕ).IsSemiformula 1 φ := by simpa using hs (^∀ φ) (by simp [hps])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.all (φ := φ)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_all, hps])
      (b.cast <| Sequent.quote_inj (V := ℕ) <| by simp [hΔ, hd, ←free_quote, setShift_quote])⟩
  · rcases by simpa using hΓ
    have : (L.codeIn ℕ).IsSemiformula 1 φ := by simpa using hs (^∃ φ) (by simp [hps])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ht.sound with ⟨t, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.ex (φ := φ)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_ex, hps]) t
      (b.cast <| Sequent.quote_inj (V := ℕ) <| by simp [hΔ, hd, Language.substs₁,
        Matrix.constant_eq_singleton, quote_cons, quote_matrix_empty])⟩
  · rcases by simpa using hΓ
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.wk (Δ := Δ) b
      (Sequent.subset_of_quote_subset_quote (V := ℕ) <| by simp [hΔ, hs])⟩
  · rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    have : Γ = Finset.image Rewriting.shift Δ :=
      Sequent.quote_inj <| by simpa [←hΔ, setShift_quote] using hΓ
    rcases this
    refine ⟨Derivation2.shift b⟩
  · rcases by simpa using hΓ
    have : (L.codeIn ℕ).IsFormula φ := dd₁.isFormulaSet φ (by simp [h₁])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ih d₁ (by simp) dd₁ with ⟨Δ₁, hΔ₁, ⟨b₁⟩⟩
    have : Δ₁ = (φ :+> Γ) := Sequent.quote_inj (V := ℕ) <| by simp [hΔ₁, h₁]
    rcases this
    rcases ih d₂ (by simp) dd₂ with ⟨Δ₂, hΔ₂, ⟨b₂⟩⟩
    have : Δ₂ = (∼φ :+> Γ) := Sequent.quote_inj (V := ℕ) <| by simp [hΔ₂, h₂]
    rcases this
    refine ⟨Derivation2.cut b₁ b₂⟩
  · rcases by simpa using hΓ
    rcases Sequent.mem_codeIn hs with ⟨φ, hφ, rfl⟩
    refine ⟨Derivation2.root φ (by simpa using hT) hφ⟩

lemma _root_.LO.Arith.Language.Theory.Provable.sound2
    {φ : SyntacticFormula L} (h : (T.codeIn ℕ).Provable ⌜φ⌝) :
    T ⊢₂.! φ := by
  rcases h with ⟨d, hp, hd⟩
  rcases hd.sound with ⟨Γ, e, b⟩
  have : Γ = {φ} := Sequent.quote_inj (V := ℕ) <| by simp [e, hp]
  rcases this
  exact b

end «lp_section_3»

variable {T : Theory L} [T.Delta1Definable]

lemma _root_.LO.Arith.Language.Theory.Provable.sound
    {φ : SyntacticFormula L} (h : (T.codeIn ℕ).Provable ⌜φ⌝) :
    T ⊢! φ :=
  provable_iff_derivable2.mpr <| Language.Theory.Provable.sound2 (by simpa using h)

lemma _root_.LO.Arith.Language.Theory.Provable.sound₀
    {σ : Sentence L} (h : (T.codeIn ℕ).Provable ⌜σ⌝) :
    T ⊢! ↑σ :=
  provable_iff_derivable2.mpr <| Language.Theory.Provable.sound2 (by simpa using h)

lemma _root_.LO.Arith.Language.Theory.Provable.complete {φ : SyntacticFormula L} :
    T.tCodeIn ℕ ⊢! ⌜φ⌝ ↔ T ⊢! φ :=
  ⟨fun h => Language.Theory.Provable.sound (Language.Theory.TProvable.iff_provable.mp h),
    tprovable_of_provable⟩

lemma _root_.LO.Arith.Language.Theory.Provable.complete₀ {σ : Sentence L} :
    T.tCodeIn ℕ ⊢! ⌜σ⌝ ↔ T ⊢! ↑σ :=
  ⟨fun h =>
      Language.Theory.Provable.sound₀
        (by simpa [Language.Theory.TProvable.iff_provable, Theory.tCodeIn] using h),
    tprovable_of_provable⟩

@[simp] lemma provableₐ_iff_provable₀ {T : Theory ℒₒᵣ} [T.Delta1Definable] [𝐑₀ wkn T] {σ :
    Sentence ℒₒᵣ} :
    T.Provableₐ (⌜σ⌝ : ℕ) ↔ T ⊢! ↑σ := by
  simpa [provableₐ_iff, Language.Theory.Provable.complete₀] using
    FirstOrder.Arith.add_cobhamR0'.symm

end Arith
end LO
