/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.GaoLeungProblem.Counterexample
public import Mathlib.SetTheory.Ordinal.Principal


/-!
# The Cantor-normal-form extension order
-/

@[expose] public section

namespace OrderClosures

open Set

universe u v

section OrdinalConstruction

/-- The relation `≺` from the proof of Theorem `thm:solid-iterations`, expressed
directly using Mathlib's Cantor normal form at base `ω`. -/
def cnfExtensionLT (ζ ζ' : Ordinal.{u}) : Prop :=
  ∃ (pre tail : List (Ordinal.{u} × Ordinal.{u})) (β c γ d : Ordinal.{u}),
    Ordinal.CNF Ordinal.omega0 ζ = pre ++ (β, c) :: tail ∧
      Ordinal.CNF Ordinal.omega0 ζ' = pre ++ [(γ, d)] ∧
      ((γ = β ∧ c < d) ∨
        (β < γ ∧
          (pre = [] ∨ ∃ δ e, pre.getLast? = some (δ, e) ∧ γ < δ)))

/-- Reflexive closure of the paper's relation `≺`. -/
def cnfExtensionLE (ζ ζ' : Ordinal.{u}) : Prop := ζ = ζ' ∨ cnfExtensionLT ζ ζ'

/-- One strict extension after a fixed CNF prefix; introduced separately so
transitivity and comparability can be proved before taking transitive closure. -/
def CNFStep (pre : List (Ordinal.{u} × Ordinal.{u}))
    (x y : Ordinal.{u} × Ordinal.{u}) : Prop :=
  (y.1 = x.1 ∧ x.2 < y.2) ∨
    (x.1 < y.1 ∧
      (pre = [] ∨ ∃ z, pre.getLast? = some z ∧ y.1 < z.1))

/-- The transitive closure of one-step CNF extensions; used as a tractable list
model of `cnfExtensionLT`. -/
def CNFListLT (l l' : List (Ordinal.{u} × Ordinal.{u})) : Prop :=
  ∃ (pre tail : List (Ordinal.{u} × Ordinal.{u}))
    (x y : Ordinal.{u} × Ordinal.{u}),
    l = pre ++ x :: tail ∧ l' = pre ++ [y] ∧ CNFStep pre x y

/-- Evaluates a list of exponent-coefficient pairs as an ordinal CNF sum; used
to compare list extensions with ordinal inequalities. -/
noncomputable def cnfValue
    (l : List (Ordinal.{u} × Ordinal.{u})) : Ordinal.{u} :=
  l.foldr (fun p r ↦ Ordinal.omega0 ^ p.1 * p.2 + r) 0

/-- Computes the ordinal represented by concatenated CNF lists; used in the
later comparison lemmas for common prefixes. -/
theorem cnfValue_append
    (l m : List (Ordinal.{u} × Ordinal.{u})) :
    cnfValue (l ++ m) = cnfValue l + cnfValue m := by
  induction l with
  | nil => simp [cnfValue]
  | cons p l ih =>
      change Ordinal.omega0 ^ p.1 * p.2 + cnfValue (l ++ m) =
        (Ordinal.omega0 ^ p.1 * p.2 + cnfValue l) + cnfValue m
      rw [ih, add_assoc]

/-- Bounds a valid CNF tail by the next larger omega power; used to compare
CNF values after extending a common prefix. -/
theorem cnfValue_lt_opow
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hcoeff : ∀ p ∈ l, p.2 < Ordinal.omega0)
    {e : Ordinal.{u}} (hexp : ∀ p ∈ l, p.1 < e) :
    cnfValue l < Ordinal.omega0 ^ e := by
  induction l generalizing e with
  | nil =>
      simpa [cnfValue] using Ordinal.opow_pos e Ordinal.omega0_pos
  | cons a l ih =>
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htail : cnfValue l < Ordinal.omega0 ^ a.1 := by
        apply ih hsorted.2
        · intro p hp
          exact hcoeff p (List.mem_cons_of_mem a hp)
        · intro p hp
          exact hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      rw [cnfValue, List.foldr_cons]
      exact Ordinal.opow_mul_add_lt_opow
        (hcoeff a (by simp)) htail (hexp a (by simp))

/-- Shows that evaluating the CNF list of an ordinal recovers that ordinal;
used to translate between list and ordinal formulations of the extension order. -/
theorem CNF_cnfValue
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0) :
    Ordinal.CNF Ordinal.omega0 (cnfValue l) = l := by
  induction l with
  | nil => simp [cnfValue]
  | cons p l ih =>
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailPos : ∀ q ∈ l, 0 < q.2 := fun q hq ↦
        hpos q (List.mem_cons_of_mem p hq)
      have htailLt : ∀ q ∈ l, q.2 < Ordinal.omega0 := fun q hq ↦
        hlt q (List.mem_cons_of_mem p hq)
      have htailExp : ∀ q ∈ l, q.1 < p.1 := fun q hq ↦
        hsorted.1 q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have htailValue : cnfValue l < Ordinal.omega0 ^ p.1 :=
        cnfValue_lt_opow l hsorted.2 htailLt htailExp
      change Ordinal.CNF Ordinal.omega0
        (Ordinal.omega0 ^ p.1 * p.2 + cnfValue l) = p :: l
      rw [Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0
          (hpos p (by simp)).ne' (hlt p (by simp)) htailValue,
        ih hsorted.2 htailPos htailLt]

/-- Inserts one monomial into a valid CNF list with ordinal-addition semantics;
used to construct explicit strict extensions. -/
noncomputable def cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u}) :
    List (Ordinal.{u} × Ordinal.{u}) :=
  match l with
  | [] => [(γ, d)]
  | (δ, e) :: tail =>
      if γ < δ then (δ, e) :: cnfAddMonomial tail γ d
      else if γ = δ then [(δ, e + d)] else [(γ, d)]

/-- Computes the value after inserting one monomial into a CNF list; used to
verify that `cnfAddMonomial` models ordinal addition. -/
theorem cnfValue_cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hd : 0 < d) :
    cnfValue (cnfAddMonomial l γ d) =
      cnfValue l + Ordinal.omega0 ^ γ * d := by
  induction l with
  | nil => simp [cnfAddMonomial, cnfValue]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailLt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
        hlt p (List.mem_cons_of_mem (δ, e) hp)
      have htailExp : ∀ p ∈ l, p.1 < δ := fun p hp ↦
        hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have htailValue : cnfValue l < Ordinal.omega0 ^ δ :=
        cnfValue_lt_opow l hsorted.2 htailLt htailExp
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
        change Ordinal.omega0 ^ δ * e + cnfValue (cnfAddMonomial l γ d) =
          (Ordinal.omega0 ^ δ * e + cnfValue l) + Ordinal.omega0 ^ γ * d
        rw [ih hsorted.2 htailLt, add_assoc]
      · by_cases hγeqδ : γ = δ
        · subst γ
          simp only [cnfAddMonomial, hγδ, ↓reduceIte]
          simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
          change Ordinal.omega0 ^ δ * (e + d) =
            (Ordinal.omega0 ^ δ * e + cnfValue l) + Ordinal.omega0 ^ δ * d
          rw [mul_add, add_assoc,
            Ordinal.add_of_omega0_opow_le htailValue
              (Ordinal.le_mul_left _ hd)]
        · have hδγ : δ < γ :=
            lt_of_le_of_ne (le_of_not_gt hγδ) (Ne.symm hγeqδ)
          have hallExp : ∀ p ∈ (δ, e) :: l, p.1 < γ := by
            intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with hp | hp
            · simpa only [hp] using hδγ
            · exact (htailExp p hp).trans hδγ
          have hvalue : cnfValue ((δ, e) :: l) < Ordinal.omega0 ^ γ :=
            cnfValue_lt_opow ((δ, e) :: l)
              (by simpa only [List.map_cons, List.pairwise_cons] using hsorted)
              hlt hallExp
          simp only [cnfAddMonomial, hγδ, hγeqδ, ↓reduceIte]
          simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
          exact (Ordinal.add_of_omega0_opow_le hvalue
            (Ordinal.le_mul_left _ hd)).symm

/-- Preserves the upper exponent bound when adding a monomial; needed for the
validity proof of the constructed CNF list. -/
theorem cnfAddMonomial_exponents_lt
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d δ : Ordinal.{u})
    (hl : ∀ p ∈ l, p.1 < δ) (hγ : γ < δ) :
    ∀ p ∈ cnfAddMonomial l γ d, p.1 < δ := by
  induction l with
  | nil => simpa [cnfAddMonomial] using hγ
  | cons p l ih =>
      rcases p with ⟨e, c⟩
      have he : e < δ := hl (e, c) (by simp)
      have htail : ∀ p ∈ l, p.1 < δ := fun p hp ↦
        hl p (List.mem_cons_of_mem (e, c) hp)
      by_cases hγe : γ < e
      · simp only [cnfAddMonomial, hγe, ↓reduceIte]
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact he
        · exact ih htail p hp
      · by_cases hγeqe : γ = e
        · subst γ
          simpa [cnfAddMonomial, hγe] using he
        · simpa [cnfAddMonomial, hγe, hγeqe] using hγ

/-- Identifies the final exponent after adding a monomial; used to control
subsequent extensions of the constructed CNF list. -/
theorem cnfAddMonomial_lastExponent
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u}) :
    ((cnfAddMonomial l γ d).getLast?.map Prod.fst).getD 0 = γ := by
  induction l with
  | nil => simp [cnfAddMonomial]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
        cases l with
        | nil => simp [cnfAddMonomial]
        | cons q l =>
            have hout : cnfAddMonomial (q :: l) γ d ≠ [] := by
              rcases q with ⟨qδ, qe⟩
              by_cases hγq : γ < qδ
              · simp [cnfAddMonomial, hγq]
              · by_cases hγeq : γ = qδ
                · simp [cnfAddMonomial, hγeq]
                · simp [cnfAddMonomial, hγq, hγeq]
            rw [show (δ, e) :: cnfAddMonomial (q :: l) γ d =
                [(δ, e)] ++ cnfAddMonomial (q :: l) γ d by rfl,
              List.getLast?_append_of_ne_nil _ hout]
            exact ih
      · by_cases hγeqδ : γ = δ
        · subst γ
          simp [cnfAddMonomial]
        · simp [cnfAddMonomial, hγδ, hγeqδ]

/-- Reduces monomial insertion to list append when its exponent is below all
existing exponents; used in the strict-extension construction. -/
theorem cnfAddMonomial_eq_append_of_lt_all
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u})
    (hγ : ∀ p ∈ l, γ < p.1) :
    cnfAddMonomial l γ d = l ++ [(γ, d)] := by
  induction l with
  | nil => simp [cnfAddMonomial]
  | cons p l ih =>
      have hγp := hγ p (by simp)
      simp only [cnfAddMonomial, hγp, ↓reduceIte, List.cons_append]
      rw [ih (fun q hq ↦ hγ q (List.mem_cons_of_mem p hq))]

/-- Proves that monomial insertion preserves CNF validity; this allows its
value to be recognized by Mathlib's canonical CNF operation. -/
theorem cnfAddMonomial_valid
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    let out := cnfAddMonomial l γ d
    (out.map Prod.fst).Pairwise (fun a b ↦ b < a) ∧
      (∀ p ∈ out, 0 < p.2) ∧
      (∀ p ∈ out, p.2 < Ordinal.omega0) := by
  induction l with
  | nil => simp [cnfAddMonomial, hdpos, hdlt]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailPos : ∀ p ∈ l, 0 < p.2 := fun p hp ↦
        hpos p (List.mem_cons_of_mem (δ, e) hp)
      have htailLt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
        hlt p (List.mem_cons_of_mem (δ, e) hp)
      obtain ⟨ihsorted, ihpos, ihlt⟩ :=
        ih hsorted.2 htailPos htailLt
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte, List.map_cons,
          List.pairwise_cons]
        refine ⟨⟨?_, ihsorted⟩, ?_, ?_⟩
        · intro e' he'
          rw [List.mem_map] at he'
          obtain ⟨p, hp, rfl⟩ := he'
          exact cnfAddMonomial_exponents_lt l γ d δ
            (fun p hp ↦ hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)) hγδ p hp
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hpos (δ, e) (by simp)
          · exact ihpos p hp
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hlt (δ, e) (by simp)
          · exact ihlt p hp
      · by_cases hγeqδ : γ = δ
        · subst γ
          have hepos : 0 < e := hpos (δ, e) (by simp)
          have helt : e < Ordinal.omega0 := hlt (δ, e) (by simp)
          have hsumpos : 0 < e + d := hepos.trans_le (le_self_add)
          have hsumlt : e + d < Ordinal.omega0 := by
            obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp helt
            obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hdlt
            rw [← Nat.cast_add]
            exact Ordinal.natCast_lt_omega0 (m + n)
          simp [cnfAddMonomial, hsumpos, hsumlt]
        · simp [cnfAddMonomial, hγδ, hγeqδ, hdpos, hdlt]

/-- Identifies the canonical CNF of a value with one added monomial; used to
construct explicit CNF extensions. -/
theorem CNF_cnfValue_add_monomial
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    Ordinal.CNF Ordinal.omega0
      (cnfValue l + Ordinal.omega0 ^ γ * d) = cnfAddMonomial l γ d := by
  rw [← cnfValue_cnfAddMonomial l hsorted hlt γ d hdpos]
  obtain ⟨hsorted', hpos', hlt'⟩ :=
    cnfAddMonomial_valid l hsorted hpos hlt γ d hdpos hdlt
  exact CNF_cnfValue _ hsorted' hpos' hlt'

/-- Adds a common head to a one-step CNF extension; used to lift extensions
through arbitrary common prefixes. -/
theorem CNFStep.cons_prefix
    {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y : Ordinal.{u} × Ordinal.{u}} {δ e : Ordinal.{u}}
    (h : CNFStep pre x y) (hy : y.1 < δ) :
    CNFStep ((δ, e) :: pre) x y := by
  rcases h with hsame | ⟨hxy, hpre⟩
  · exact Or.inl hsame
  · refine Or.inr ⟨hxy, Or.inr ?_⟩
    cases pre with
    | nil => exact ⟨(δ, e), by simp, hy⟩
    | cons p pre =>
        rcases hpre with hfalse | ⟨z, hz, hyz⟩
        · simp at hfalse
        · exact ⟨z, by simpa using hz, hyz⟩

/-- Shows that adding a sufficiently small monomial gives a strict CNF-list
extension; used to approximate ordinals from below. -/
theorem CNFListLT_cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u})) (hne : l ≠ [])
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (β c : Ordinal.{u}) (hlast : l.getLast? = some (β, c))
    (γ d : Ordinal.{u}) (hdpos : 0 < d)
    (hβγ : β ≤ γ) :
    CNFListLT l (cnfAddMonomial l γ d) := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      cases l with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          rcases hlast with ⟨rfl, rfl⟩
          by_cases hγeqβ : γ = β
          · subst γ
            refine ⟨[], [], (β, c), (β, c + d), by simp,
              by simp [cnfAddMonomial], ?_⟩
            exact Or.inl ⟨rfl, lt_add_of_pos_right c hdpos⟩
          · have hβγ' : β < γ := lt_of_le_of_ne hβγ (Ne.symm hγeqβ)
            refine ⟨[], [], (β, c), (γ, d), by simp,
              by simp [cnfAddMonomial, hβγ'.not_gt, hγeqβ], ?_⟩
            exact Or.inr ⟨hβγ', Or.inl rfl⟩
      | cons q l =>
          simp only [List.map_cons, List.pairwise_cons] at hsorted
          have htailPos : ∀ p ∈ q :: l, 0 < p.2 := fun p hp ↦
            hpos p (List.mem_cons_of_mem (δ, e) hp)
          have htailLt : ∀ p ∈ q :: l, p.2 < Ordinal.omega0 := fun p hp ↦
            hlt p (List.mem_cons_of_mem (δ, e) hp)
          have htailSorted : (List.map Prod.fst (q :: l)).Pairwise
              (fun a b ↦ b < a) := by
            simpa only [List.map_cons, List.pairwise_cons] using hsorted.2
          have hlastTail : (q :: l).getLast? = some (β, c) := by
            simpa using hlast
          by_cases hγδ : γ < δ
          · rcases ih (by simp) htailSorted htailPos htailLt hlastTail with
              ⟨pre, tail, x, y, hin, hout, hstep⟩
            have hyMem : y ∈ cnfAddMonomial (q :: l) γ d := by
              rw [hout]
              exact List.mem_append_right _ (by simp)
            have hyδ : y.1 < δ :=
              cnfAddMonomial_exponents_lt (q :: l) γ d δ
                (fun p hp ↦ hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
                hγδ y hyMem
            refine ⟨(δ, e) :: pre, tail, x, y, ?_, ?_,
              CNFStep.cons_prefix hstep hyδ⟩
            · simpa only [List.cons_append] using
                congrArg (List.cons (δ, e)) hin
            · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
              simpa only [cnfAddMonomial, hγδ, ↓reduceIte, List.cons_append] using
                congrArg (List.cons (δ, e)) hout
          · by_cases hγeqδ : γ = δ
            · subst γ
              refine ⟨[], q :: l, (δ, e), (δ, e + d), by simp,
                by simp [cnfAddMonomial], ?_⟩
              exact Or.inl ⟨rfl, lt_add_of_pos_right e hdpos⟩
            · have hδγ : δ < γ :=
                lt_of_le_of_ne (le_of_not_gt hγδ) (Ne.symm hγeqδ)
              refine ⟨[], q :: l, (δ, e), (γ, d), by simp,
                by simp [cnfAddMonomial, hγδ, hγeqδ], ?_⟩
              exact Or.inr ⟨hδγ, Or.inl rfl⟩

/-- Compares values of lists with the same valid prefix; used to show that
CNF-list extension implies ordinary ordinal inequality. -/
theorem cnfValue_append_lt_append
    (pre l l' : List (Ordinal.{u} × Ordinal.{u}))
    (h : cnfValue l < cnfValue l') :
    cnfValue (pre ++ l) < cnfValue (pre ++ l') := by
  induction pre with
  | nil => simpa using h
  | cons p pre ih =>
      simp only [List.cons_append, cnfValue, List.foldr_cons]
      exact (add_lt_add_iff_left _).2 ih

/-- Converts strict extension of canonical CNF lists into strict ordinal
inequality; used throughout the ordinal-space construction. -/
theorem CNFListLT.ordinal_lt {ζ ζ' : Ordinal.{u}}
    (h : CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
      (Ordinal.CNF Ordinal.omega0 ζ')) : ζ < ζ' := by
  rcases h with ⟨pre, tail, ⟨β, c⟩, ⟨γ, d⟩, hζ, hζ', hstep⟩
  have hsorted := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ).pairwise
  rw [hζ, List.map_append, List.map_cons, List.pairwise_append] at hsorted
  have hsuffix : ((β, c) :: tail).map Prod.fst |>.Pairwise (fun a b ↦ b < a) :=
    hsorted.2.1
  rw [List.map_cons, List.pairwise_cons] at hsuffix
  have hcoeff : ∀ p ∈ tail, p.2 < Ordinal.omega0 := by
    intro p hp
    apply Ordinal.CNF.snd_lt Ordinal.one_lt_omega0
    rw [hζ]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  have htail : cnfValue tail < Ordinal.omega0 ^ β :=
    cnfValue_lt_opow tail hsuffix.2 hcoeff (fun p hp ↦
      hsuffix.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hc : c < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (o := ζ) (x := (β, c)) Ordinal.one_lt_omega0
    rw [hζ]
    exact List.mem_append_right _ List.mem_cons_self
  have hd : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := ζ') (x := (γ, d))
    rw [hζ']
    exact List.mem_append_right _ (by simp)
  have hdiv : cnfValue ((β, c) :: tail) < cnfValue [(γ, d)] := by
    rcases hstep with ⟨rfl, hcd⟩ | ⟨hβγ, _⟩
    · simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
      exact Ordinal.opow_mul_add_lt_opow_mul htail hcd
    · simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
      exact (Ordinal.opow_mul_add_lt_opow hc htail hβγ).trans_le
        (Ordinal.le_mul_left _ hd)
  rw [← Ordinal.CNF.foldr Ordinal.omega0 ζ,
    ← Ordinal.CNF.foldr Ordinal.omega0 ζ']
  change cnfValue (Ordinal.CNF Ordinal.omega0 ζ) <
    cnfValue (Ordinal.CNF Ordinal.omega0 ζ')
  rw [hζ, hζ']
  exact cnfValue_append_lt_append pre _ _ hdiv

/-- Equates the ordinal definition of `cnfExtensionLT` with its list model;
this bridge supplies transitivity and upper-cone linearity. -/
theorem cnfExtensionLT_iff_CNFListLT {ζ ζ' : Ordinal.{u}} :
    cnfExtensionLT ζ ζ' ↔
      CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
        (Ordinal.CNF Ordinal.omega0 ζ') := by
  constructor
  · rintro ⟨pre, tail, β, c, γ, d, hζ, hζ', hstep⟩
    refine ⟨pre, tail, (β, c), (γ, d), hζ, hζ', ?_⟩
    rcases hstep with hstep | ⟨hβγ, hpre⟩
    · exact Or.inl hstep
    · refine Or.inr ⟨hβγ, ?_⟩
      rcases hpre with rfl | ⟨δ, e, hlast, hγδ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨(δ, e), hlast, hγδ⟩
  · rintro ⟨pre, tail, ⟨β, c⟩, ⟨γ, d⟩, hζ, hζ', hstep⟩
    refine ⟨pre, tail, β, c, γ, d, hζ, hζ', ?_⟩
    rcases hstep with hstep | ⟨hβγ, hpre⟩
    · exact Or.inl hstep
    · refine Or.inr ⟨hβγ, ?_⟩
      rcases hpre with rfl | ⟨⟨δ, e⟩, hlast, hγδ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨δ, e, hlast, hγδ⟩

/-- Appending one smaller singleton monomial creates a strict CNF extension;
used in the later Gao-stage approximation argument. -/
theorem cnfExtensionLT_add_singleton_of_last
    {ζ q γ d β c : Ordinal.{u}}
    {pre : List (Ordinal.{u} × Ordinal.{u})}
    (hζ : Ordinal.CNF Ordinal.omega0 ζ = pre ++ [(β, c)])
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hβγ : β ≤ γ) : cnfExtensionLT ζ (ζ + q) := by
  let l := Ordinal.CNF Ordinal.omega0 ζ
  have hl : l = pre ++ [(β, c)] := hζ
  have hlne : l ≠ [] := by rw [hl]; simp
  have hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a) :=
    (Ordinal.CNF.sortedGT Ordinal.omega0 ζ).pairwise
  have hpos : ∀ p ∈ l, 0 < p.2 := fun p hp ↦
    Ordinal.CNF.snd_pos hp
  have hlt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
    Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hp
  have hlast : l.getLast? = some (β, c) := by rw [hl]; simp
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  have hζvalue : cnfValue l = ζ := Ordinal.CNF.foldr Ordinal.omega0 ζ
  have hqvalue : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  apply cnfExtensionLT_iff_CNFListLT.mpr
  rw [← hζvalue, hqvalue,
    CNF_cnfValue_add_monomial l hsorted hpos hlt γ d hdpos hdlt,
    CNF_cnfValue l hsorted hpos hlt]
  exact CNFListLT_cnfAddMonomial l hlne hsorted hpos hlt β c hlast
    γ d hdpos hβγ

/-- Proves transitivity for one-step extensions sharing a prefix; used in the
global transitivity proof for `CNFListLT`. -/
theorem CNFStep.trans {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y z : Ordinal.{u} × Ordinal.{u}}
    (hxy : CNFStep pre x y) (hyz : CNFStep pre y z) : CNFStep pre x z := by
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
  · exact Or.inl ⟨hyz.1.trans hxy.1, hxy.2.trans hyz.2⟩
  · exact Or.inr ⟨hxy.1 ▸ hyz.1, hyz.2⟩
  · refine Or.inr ⟨hxy.1.trans_eq hyz.1.symm, ?_⟩
    rcases hxy.2 with hp | ⟨w, hw, hb⟩
    · exact Or.inl hp
    · exact Or.inr ⟨w, hw, by simpa only [hyz.1] using hb⟩
  · exact Or.inr ⟨hxy.1.trans hyz.1, hyz.2⟩

/-- Establishes comparability of two one-step extensions above a common
prefix; used to linearize each upper cone. -/
theorem CNFStep.trichotomy {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y z : Ordinal.{u} × Ordinal.{u}}
    (hxy : CNFStep pre x y) (hxz : CNFStep pre x z) :
    y = z ∨ CNFStep pre y z ∨ CNFStep pre z y := by
  rcases x with ⟨β, c⟩
  rcases y with ⟨γ, d⟩
  rcases z with ⟨δ, e⟩
  simp only [CNFStep] at hxy hxz ⊢
  rcases hxy with ⟨rfl, hcd⟩ | ⟨hβγ, hγ⟩ <;>
    rcases hxz with ⟨rfl, hce⟩ | ⟨hβδ, hδ⟩
  · rcases lt_trichotomy d e with hde | rfl | hed
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, hde⟩))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hed⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hβδ, hδ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hβγ, hγ⟩))
  · rcases lt_trichotomy γ δ with hγδ | hγδ | hδγ
    · exact Or.inr (Or.inl (Or.inr ⟨hγδ, hδ⟩))
    · subst δ
      rcases lt_trichotomy d e with hde | rfl | hed
      · exact Or.inr (Or.inl (Or.inl ⟨rfl, hde⟩))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hed⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hδγ, hγ⟩))

/-- Lifts one-step transitivity to the transitive closure `CNFListLT`; used to
prove that `cnfExtensionLE` is a partial order. -/
theorem CNFListLT.trans {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hmn : CNFListLT m n) : CNFListLT l n := by
  rcases hlm with ⟨p, t, x, y, hl, hm, hxy⟩
  rcases hmn with ⟨q, s, y', z, hm', hn, hyz⟩
  have heq : p ++ [y] = q ++ y' :: s := hm.symm.trans hm'
  have hlen : q.length ≤ p.length := by
    have h : p.length + 1 = q.length + s.length + 1 := by
      simpa only [List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.add_assoc]
        using congrArg List.length heq
    omega
  have hqp : q <+: p := by
    apply (List.isPrefix_append_of_length hlen).mp
    exact ⟨y' :: s, heq.symm⟩
  rcases hqp with ⟨r, hpr⟩
  rw [← hpr] at hl hm hxy heq
  have hr : r ++ [y] = y' :: s :=
    List.append_cancel_left (by simpa only [List.append_assoc] using heq)
  cases r with
  | nil =>
      simp only [List.append_nil] at hl hm hxy
      simp only [List.nil_append] at hr
      simp only [List.cons.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact ⟨q, t, x, z, by simpa only [List.nil_append] using hl,
        hn, CNFStep.trans hxy hyz⟩
  | cons w r =>
      simp only [List.cons_append, List.cons.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      refine ⟨q, r ++ x :: t, w, z, ?_, hn, hyz⟩
      simpa only [List.cons_append, List.append_assoc] using hl

/-- Shows that two CNF lists extending a fixed list are comparable; used for
linearity of upper cones in the ordinal extension order. -/
theorem CNFListLT.upper_trichotomy
    {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hln : CNFListLT l n) :
    m = n ∨ CNFListLT m n ∨ CNFListLT n m := by
  rcases hlm with ⟨p, t, x, y, hl, hm, hxy⟩
  rcases hln with ⟨q, s, x', z, hl', hn, hxz⟩
  have hpref : p <+: l := ⟨x :: t, hl.symm⟩
  have qpref : q <+: l := ⟨x' :: s, hl'.symm⟩
  rcases lt_trichotomy p.length q.length with hpq | hpq | hqp
  · have hprefq : p <+: q := by
      apply (List.isPrefix_append_of_length hpq.le).mp
      rw [hl'] at hpref
      exact hpref
    rcases hprefq with ⟨r, hqr⟩
    rw [← hqr] at hl' hn hxz
    cases r with
    | nil =>
        simp only [List.append_nil] at hqr
        exact (hpq.ne (congrArg List.length hqr)).elim
    | cons w r =>
        have heq : w :: r ++ x' :: s = x :: t :=
          List.append_cancel_left (by
            simpa only [List.cons_append, List.append_assoc] using hl'.symm.trans hl)
        have hw : w = x := (List.cons.inj heq).1
        have hr : r ++ x' :: s = t := (List.cons.inj heq).2
        subst w
        subst t
        refine Or.inr (Or.inr ⟨p, r ++ [z], x, y, ?_, hm, hxy⟩)
        simpa only [List.cons_append, List.append_assoc] using hn
  · have hpqeq : p = q := by
      rw [List.prefix_iff_eq_take] at hpref qpref
      rw [hpref, qpref, hpq]
    subst q
    have heq : x :: t = x' :: s :=
      List.append_cancel_left (hl.symm.trans hl')
    have hxx' : x = x' := (List.cons.inj heq).1
    have hts : t = s := (List.cons.inj heq).2
    subst x'
    subst s
    rcases CNFStep.trichotomy hxy hxz with rfl | hyz | hzy
    · exact Or.inl (hm.trans hn.symm)
    · exact Or.inr (Or.inl ⟨p, [], y, z, hm, hn, hyz⟩)
    · exact Or.inr (Or.inr ⟨p, [], z, y, hn, hm, hzy⟩)
  · have qprefp : q <+: p := by
      apply (List.isPrefix_append_of_length hqp.le).mp
      rw [hl] at qpref
      exact qpref
    rcases qprefp with ⟨r, hpr⟩
    rw [← hpr] at hl hm hxy
    cases r with
    | nil =>
        simp only [List.append_nil] at hpr
        exact (hqp.ne (congrArg List.length hpr)).elim
    | cons w r =>
        have heq : w :: r ++ x :: t = x' :: s :=
          List.append_cancel_left (by
            simpa only [List.cons_append, List.append_assoc] using hl.symm.trans hl')
        have hw : w = x' := (List.cons.inj heq).1
        have hr : r ++ x :: t = s := (List.cons.inj heq).2
        subst w
        subst s
        refine Or.inr (Or.inl ⟨q, r ++ [y], x', z, ?_, hn, hxz⟩)
        simpa only [List.cons_append, List.append_assoc] using hm

/-- Property P1 of the ordinal relation in the proof of `thm:solid-iterations`. -/
theorem cnfExtensionLE_partialOrder_and_subrelation :
    IsPartialOrder (Ordinal.{u}) cnfExtensionLE ∧
      ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLE ζ ζ' → ζ ≤ ζ' := by
  have hlt : ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLT ζ ζ' → ζ < ζ' := by
    intro ζ ζ' h
    exact CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp h)
  have htrans : ∀ a b c : Ordinal.{u}, cnfExtensionLT a b →
      cnfExtensionLT b c → cnfExtensionLT a c := by
    intro a b c hab hbc
    apply cnfExtensionLT_iff_CNFListLT.mpr
    exact CNFListLT.trans (cnfExtensionLT_iff_CNFListLT.mp hab)
      (cnfExtensionLT_iff_CNFListLT.mp hbc)
  let : IsPreorder (Ordinal.{u}) cnfExtensionLE := {
    refl := fun _ ↦ Or.inl rfl
    trans := fun a b c hab hbc ↦ by
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (htrans a b c hab hbc)
    }
  let : Std.Antisymm
      (cnfExtensionLE : Ordinal.{u} → Ordinal.{u} → Prop) := ⟨by
    intro a b hab hba
    rcases hab with rfl | hab
    · rfl
    rcases hba with rfl | hba
    · rfl
    · exact ((hlt hab).asymm (hlt hba)).elim
    ⟩
  constructor
  · exact IsPartialOrder.mk
  · intro ζ ζ' h
    rcases h with rfl | h
    · exact le_rfl
    · exact (hlt h).le

/-- Property P2 of the ordinal relation in the proof of `thm:solid-iterations`. -/
theorem cnfExtensionLT_linear_above (ζ : Ordinal.{u}) :
    ∀ {η η' : Ordinal.{u}}, cnfExtensionLT ζ η → cnfExtensionLT ζ η' →
      (cnfExtensionLT η η' ↔ η < η') := by
  intro η η' hη hη'
  constructor
  · intro h
    exact CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp h)
  · intro hlt
    rcases CNFListLT.upper_trichotomy
      (cnfExtensionLT_iff_CNFListLT.mp hη)
      (cnfExtensionLT_iff_CNFListLT.mp hη') with heq | h | h
    · have hηeq : η = η' := by
        rw [← Ordinal.CNF.foldr Ordinal.omega0 η,
          ← Ordinal.CNF.foldr Ordinal.omega0 η', heq]
      exact (hlt.ne hηeq).elim
    · exact cnfExtensionLT_iff_CNFListLT.mpr h
    · exact ((CNFListLT.ordinal_lt h).asymm hlt).elim

/-- Includes equality in upper-cone comparability; used when minimal Gao
dominators must be compared in `StageFormula`. -/
theorem cnfExtensionLE_linear_above (ζ : Ordinal.{u})
    {η η' : Ordinal.{u}} (hη : cnfExtensionLE ζ η)
    (hη' : cnfExtensionLE ζ η') :
    cnfExtensionLE η η' ∨ cnfExtensionLE η' η := by
  rcases hη with rfl | hη
  · exact Or.inl hη'
  rcases hη' with rfl | hη'
  · exact Or.inr (Or.inr hη)
  rcases lt_trichotomy η η' with hlt | heq | hgt
  · exact Or.inl (Or.inr ((cnfExtensionLT_linear_above ζ hη hη').mpr hlt))
  · exact Or.inl (Or.inl heq)
  · exact Or.inr (Or.inr ((cnfExtensionLT_linear_above ζ hη' hη).mpr hgt))

end OrdinalConstruction

end OrderClosures
