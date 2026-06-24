/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Hierarchy

/-! # Theory -/


namespace LO

namespace FirstOrder

open Arith

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

/-- Imported declaration from the Incompleteness formalization. -/
def succInd {ξ} (φ : Semiformula L ξ 1) :
    Formula L ξ := “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

/-- Imported declaration from the Incompleteness formalization. -/
def orderInd {ξ} (φ : Semiformula L ξ 1) :
    Formula L ξ := “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”

/-- Imported declaration from the Incompleteness formalization. -/
def leastNumber {ξ} (φ : Semiformula L ξ 1) :
    Formula L ξ := “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”

namespace Theory

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
inductive CobhamR0 : Theory ℒₒᵣ
  | equal : ∀ φ ∈ 𝐄𝐐, CobhamR0 φ
  | Ω₁ (n m : ℕ)  : CobhamR0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ)  : CobhamR0 “↑n * ↑m = ↑(n * m)”
  | Ω₃  (n m : ℕ)  : n ≠ m → CobhamR0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : CobhamR0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐑₀" => CobhamR0

variable {L}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addZero : SyntacticFormula L := “x | x + 0 = x”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addAssoc :
    SyntacticFormula L := “x y z | (x + y) + z = x + (y + z)”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addComm : SyntacticFormula L := “x y | x + y = y + x”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addEqOfLt :
    SyntacticFormula L := “x y | x < y → ∃ z, x + z = y”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.zeroLe : SyntacticFormula L := “x | 0 ≤ x”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.zeroLtOne : SyntacticFormula L := “0 < 1”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.oneLeOfZeroLt : SyntacticFormula L := “x | 0 < x → 1 ≤ x”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addLtAdd :
    SyntacticFormula L := “x y z | x < y → x + z < y + z”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulZero : SyntacticFormula L := “x | x * 0 = 0”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulOne : SyntacticFormula L := “x | x * 1 = x”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulAssoc :
    SyntacticFormula L := “x y z | (x * y) * z = x * (y * z)”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulComm : SyntacticFormula L := “x y | x * y = y * x”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulLtMul :
    SyntacticFormula L := “x y z | x < y ∧ 0 < z → x * z < y * z”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.distr :
    SyntacticFormula L := “x y z | x * (y + z) = x * y + x * z”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.ltIrrefl : SyntacticFormula L := “x | x </ x”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.ltTrans :
    SyntacticFormula L := “x y z | x < y ∧ y < z → x < z”
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.ltTri :
    SyntacticFormula L := “x y | x < y ∨ x = y ∨ x > y”

/-- Imported declaration from the Incompleteness formalization. -/
inductive PeanoMinus : Theory ℒₒᵣ
  | equal         : ∀ φ ∈ 𝐄𝐐, PeanoMinus φ
  | addZero       : PeanoMinus Arith.addZero
  | addAssoc      : PeanoMinus Arith.addAssoc
  | addComm       : PeanoMinus Arith.addComm
  | addEqOfLt     : PeanoMinus Arith.addEqOfLt
  | zeroLe        : PeanoMinus Arith.zeroLe
  | zeroLtOne     : PeanoMinus Arith.zeroLtOne
  | oneLeOfZeroLt : PeanoMinus Arith.oneLeOfZeroLt
  | addLtAdd      : PeanoMinus Arith.addLtAdd
  | mulZero       : PeanoMinus Arith.mulZero
  | mulOne        : PeanoMinus Arith.mulOne
  | mulAssoc      : PeanoMinus Arith.mulAssoc
  | mulComm       : PeanoMinus Arith.mulComm
  | mulLtMul      : PeanoMinus Arith.mulLtMul
  | distr         : PeanoMinus Arith.distr
  | ltIrrefl      : PeanoMinus Arith.ltIrrefl
  | ltTrans       : PeanoMinus Arith.ltTrans
  | ltTri         : PeanoMinus Arith.ltTri

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐏𝐀⁻" => PeanoMinus

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
def indScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = succInd φ }

/-- Imported declaration from the Incompleteness formalization. -/
abbrev iOpen : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ Semiformula.Open

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈open" => iOpen

/-- Imported declaration from the Incompleteness formalization. -/
abbrev indH (Γ : Polarity) (k : ℕ) : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ (Arith.Hierarchy Γ k)

/-- Imported declaration from the Incompleteness formalization. -/
prefix:max "𝐈𝐍𝐃" => indH

/-- Imported declaration from the Incompleteness formalization. -/
abbrev iSigma (k : ℕ) : Theory ℒₒᵣ := 𝐈𝐍𝐃Sg k

/-- Imported declaration from the Incompleteness formalization. -/
prefix:max "𝐈Sg" => iSigma

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Sg0" => iSigma 0

/-- Imported declaration from the Incompleteness formalization. -/
abbrev iPi (k : ℕ) : Theory ℒₒᵣ := 𝐈𝐍𝐃Pg k

/-- Imported declaration from the Incompleteness formalization. -/
prefix:max "𝐈Pg" => iPi

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Pg0" => iPi 0

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Sg1" => iSigma 1

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Pg1" => iPi 1

/-- Imported declaration from the Incompleteness formalization. -/
abbrev peano : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ

/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐏𝐀" => peano

variable {L}

lemma coe_indH_subset_indH : (indScheme ℒₒᵣ (Arith.Hierarchy Γ ν) :
    Theory L) ⊆ indScheme L (Arith.Hierarchy Γ ν) := by
  simp only [indScheme, Set.image_subset_iff, Set.preimage_setOf_eq, Set.setOf_subset_setOf,
    forall_exists_index, and_imp]
  rintro _ φ Hp rfl
  exact ⟨Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) φ, Hierarchy.oringEmb Hp,
    by simp [succInd, Semiformula.lMap_substs]⟩

lemma indScheme_subset (h : ∀ {φ : Semiformula ℒₒᵣ ℕ 1}, C φ → C' φ) :
    indScheme ℒₒᵣ C ⊆ indScheme ℒₒᵣ C' := by
  rintro _ ⟨φ, hp, rfl⟩
  exact ⟨φ, h hp, rfl⟩

lemma iSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈Sg s₁ ⊆ 𝐈Sg s₂ :=
  Set.union_subset_union_right _ (indScheme_subset (fun H ↦ H.mono h))

instance : 𝐏𝐀⁻ wkn 𝐈𝐍𝐃Γ n := Entailment.WeakerThan.ofSubset (by simp [indH, Theory.add_def])

instance : 𝐄𝐐 wkn 𝐑₀ := Entailment.WeakerThan.ofSubset <| fun φ hp ↦ CobhamR0.equal φ hp

instance : 𝐄𝐐 wkn 𝐏𝐀⁻ := Entailment.WeakerThan.ofSubset <| fun φ hp ↦ PeanoMinus.equal φ hp

instance : 𝐄𝐐 wkn 𝐈𝐍𝐃Γ n := Entailment.WeakerThan.trans (inferInstance : 𝐄𝐐 wkn 𝐏𝐀⁻) inferInstance

instance : 𝐄𝐐 wkn 𝐈open := Entailment.WeakerThan.trans (inferInstance : 𝐄𝐐 wkn 𝐏𝐀⁻) inferInstance

instance (i) : 𝐈open wkn 𝐈Sgi :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <|
      indScheme_subset Hierarchy.of_open

lemma iSigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈Sg s₁ wkn 𝐈Sg s₂ :=
  Entailment.WeakerThan.ofSubset (iSigma_subset_mono h)

instance : 𝐈Sg0 wkn 𝐈Sg1 := iSigma_weakerThan_of_le (by decide)

instance (i) : 𝐈Sgi wkn 𝐏𝐀 :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <|
      indScheme_subset (by intros; trivial)

example (a b : ℕ) : Set.Finite {a, b} := by simp only [Set.finite_singleton, Set.Finite.insert]

@[simp] lemma _root_.LO.FirstOrder.Theory.PeanoMinus.finite : Set.Finite 𝐏𝐀⁻ := by
  have : 𝐏𝐀⁻ =
    𝐄𝐐 ∪
    { Arith.addZero,
      Arith.addAssoc,
      Arith.addComm,
      Arith.addEqOfLt,
      Arith.zeroLe,
      Arith.zeroLtOne,
      Arith.oneLeOfZeroLt,
      Arith.addLtAdd,
      Arith.mulZero,
      Arith.mulOne,
      Arith.mulAssoc,
      Arith.mulComm,
      Arith.mulLtMul,
      Arith.distr,
      Arith.ltIrrefl,
      Arith.ltTrans,
      Arith.ltTri } := by
    ext φ; constructor
    · rintro ⟨⟩
      case equal => left; assumption
      case addZero => tauto
      case addAssoc => tauto
      case addComm => tauto
      case addEqOfLt => tauto
      case zeroLe => tauto
      case zeroLtOne => tauto
      case oneLeOfZeroLt => tauto
      case addLtAdd => tauto
      case mulZero => tauto
      case mulOne => tauto
      case mulAssoc => tauto
      case mulComm => tauto
      case mulLtMul => tauto
      case distr => tauto
      case ltIrrefl => tauto
      case ltTrans => tauto
      case ltTri => tauto
    · rintro (h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl)
      · exact PeanoMinus.equal _ h
      · exact PeanoMinus.addZero
      · exact PeanoMinus.addAssoc
      · exact PeanoMinus.addComm
      · exact PeanoMinus.addEqOfLt
      · exact PeanoMinus.zeroLe
      · exact PeanoMinus.zeroLtOne
      · exact PeanoMinus.oneLeOfZeroLt
      · exact PeanoMinus.addLtAdd
      · exact PeanoMinus.mulZero
      · exact PeanoMinus.mulOne
      · exact PeanoMinus.mulAssoc
      · exact PeanoMinus.mulComm
      · exact PeanoMinus.mulLtMul
      · exact PeanoMinus.distr
      · exact PeanoMinus.ltIrrefl
      · exact PeanoMinus.ltTrans
      · exact PeanoMinus.ltTri
  rw [this]; simp only [Set.finite_union, EqAxiom.finite, true_and]
  exact Set.toFinite _

end Theory

end FirstOrder

end LO
