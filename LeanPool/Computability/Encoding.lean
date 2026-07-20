/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import LeanPool.Computability.TuringDegree
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.PSub
import Mathlib.Data.PFun
import Mathlib.Data.Part
import Mathlib.Tactic.Cases


/-!
# Encoding of Oracle Programs and Universality

This file provides an encoding for oracle partial recursive functions and a definition of the
universal partial recursive function relative to an oracle, along with a proof that it is universal.
-/

open Denumerable Encodable

namespace Computability

/-- The identity function is recursive in any oracle `O`. -/
theorem RecursiveIn_id {O : Set (ℕ →. ℕ)} : RecursiveIn O (fun n => Part.some n) :=
  recursiveIn_of_partrec (Nat.Partrec.of_primrec Nat.Primrec.id)

/-- The composition of two total recursive functions is recursive. -/
lemma RecursiveIn_comp_total {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
  (hf : RecursiveIn O (fun n => Part.some (f n)))
  (hg : RecursiveIn O (fun n => Part.some (g n))) :
  RecursiveIn O (fun n => Part.some (f (g n))) := by
    convert hf.comp hg using 1
    aesop

lemma RecursiveIn_pair_total {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
  (hf : RecursiveIn O (fun n => Part.some (f n)))
  (hg : RecursiveIn O (fun n => Part.some (g n))) :
  RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
    convert RecursiveIn.pair hf hg using 1
    ext
    simp only [Part.mem_some_iff, Part.map_eq_map, Part.map_some]
    erw [Part.mem_bind_iff]
    aesop

lemma RecursiveIn_prec_total {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} {h : ℕ → ℕ}
    (hf : RecursiveIn O (fun n => Part.some (f n)))
    (hh : RecursiveIn O (fun n => Part.some (h n))) :
    RecursiveIn O (fun p => Part.some
      (Nat.rec (f p.unpair.1) (fun y IH => h (Nat.pair p.unpair.1 (Nat.pair y IH)))
        p.unpair.2)) := by
  refine (RecursiveIn.prec hf hh).of_eq ?_
  intro p
  change Nat.rec (Part.some (f p.unpair.1))
      (fun y IH => IH.bind fun i => Part.some (h (Nat.pair p.unpair.1 (Nat.pair y i)))) p.unpair.2
    = Part.some _
  generalize p.unpair.1 = a
  induction p.unpair.2 with
  | zero => rfl
  | succ y ih => simp only [ih, Part.bind_some]

theorem RecursiveIn_add {O : Set (ℕ →. ℕ)} :
    RecursiveIn O (fun p => Part.some (p.unpair.1 + p.unpair.2)) :=
  recursiveIn_of_partrec (Nat.Partrec.of_primrec Nat.Primrec.add)

/-- Every primitive recursive function is recursive. -/
theorem RecursiveIn_of_Primrec {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    RecursiveIn O (fun n => Part.some (f n)) := by
  induction hf with
  | zero => exact RecursiveIn.zero
  | succ => exact RecursiveIn.succ
  | left => exact RecursiveIn.left
  | right => exact RecursiveIn.right
  | pair _ _ ihf ihg => exact RecursiveIn_pair_total ihf ihg
  | comp _ _ ihf ihg => exact RecursiveIn_comp_total ihf ihg
  | prec _ _ ihf ihg => exact RecursiveIn_prec_total ihf ihg

theorem RecursiveIn.rfind' {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
  RecursiveIn O (Nat.unpaired fun a m =>
    (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m))
  := by
    have hg : RecursiveIn O (fun x =>
        f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2))) := by
      have h_g : RecursiveIn O
          (fun p => Nat.pair (p.unpair.1.unpair.1) (p.unpair.1.unpair.2 + p.unpair.2)) := by
        apply RecursiveIn_pair_total
        · apply RecursiveIn_of_Primrec
          exact Nat.Primrec.left.comp Nat.Primrec.left
        · apply RecursiveIn_of_Primrec
          refine Nat.Primrec.of_eq (Nat.Primrec.add.comp
            (Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.left) Nat.Primrec.right)) ?_
          intro n; simp [Nat.unpaired]
      have h_g' : RecursiveIn O (fun p =>
          f (Nat.pair (p.unpair.1.unpair.1) (p.unpair.1.unpair.2 + p.unpair.2))) := by
        convert RecursiveIn.comp hf h_g using 1
        aesop
      simpa only [add_comm] using h_g'
    have hH : RecursiveIn O (fun p => Nat.rfind (fun n => let x := Nat.pair p n; (fun m =>
        Decidable.decide (m = 0)) <$>
        f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2)))) :=
      hg.rfind
    have h_target : RecursiveIn O (fun p => (Nat.rfind (fun n => let x := Nat.pair p n; (fun m =>
        Decidable.decide (m = 0)) <$>
        f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2)))) +
        (Nat.unpair p).2) := by
      have h_add : RecursiveIn O (fun p => (Nat.unpair p).2) := right
      convert RecursiveIn_add.comp (hH.pair h_add) using 1
      ext
      simp_all only [Nat.unpair_pair, Part.map_eq_map, Part.coe_some, Part.bind_eq_bind,
        Part.mem_bind_iff, Part.mem_some_iff]
      apply Iff.intro
      · intro a_1
        rename_i a b
        obtain ⟨x, hx⟩ : ∃ x, b = x + (Nat.unpair a).2 := by
          cases a_1; aesop
        use Nat.pair x (Nat.unpair a).2
        subst hx
        simp_all only [Nat.unpair_pair, and_true]
        cases a_1
        rename_i w h
        simp_all only [Part.add_get_eq, Part.get_some, Nat.add_right_cancel_iff]
        subst h
        exact ⟨w, by aesop⟩
      · intro a_1
        rename_i a b
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        subst right
        obtain ⟨n, hn⟩ : ∃ n, (Nat.rfind (fun n => Part.map (fun m => Decidable.decide (m = 0))
            (f (Nat.pair (Nat.unpair a).1 (n + (Nat.unpair a).2))))) = Part.some n
            ∧ w = Nat.pair n (Nat.unpair a).2 := by
          cases left; aesop
        simp_all only [Part.map_some, Nat.unpair_pair]
        obtain ⟨left_1, right⟩ := hn
        subst right
        simp [Part.some, Part.add_def]
    convert h_target using 1
    funext p
    simp only [Nat.unpaired, Part.map_eq_map, Nat.unpair_pair, Part.coe_some]
    cases h : Nat.rfind (fun n => Part.map (fun m => Decidable.decide (m = 0))
        (f (Nat.pair (Nat.unpair p).1 (n + (Nat.unpair p).2))))
    simp_all only [Nat.unpair_pair, Part.map_eq_map, Part.coe_some]
    ext
    simp [Part.map]
    simp [Part.add_def]
    simp only [eq_comm]

/-- Reindexes an oracle family `f : α → ℕ →. ℕ` to a family indexed by `ℕ` via the
denumerable encoding of `α`; out-of-range indices map to the nowhere-defined function. -/
def oracleCode {α : Type} [Denumerable α] (f : α → ℕ →. ℕ) : ℕ → ℕ →. ℕ :=
  fun i n => match decode i with
           | some a => f a n
           | none   => ⊥

/-- Codes (Gödel numberings) for oracle partial recursive functions. -/
inductive codeo : Type
| zero : codeo
| succ : codeo
| left : codeo
| right : codeo
| oracle : ℕ → codeo
| pair : codeo → codeo → codeo
| comp : codeo → codeo → codeo
| prec : codeo → codeo → codeo
| rfind' : codeo → codeo

/-- Semantics of `codeo`, relative to an indexed oracle family. -/
def evalo {α : Type} [Primcodable α] (f : α → ℕ →. ℕ) : codeo → ℕ →. ℕ
| codeo.zero => pure 0
| codeo.succ => fun n => some (n + 1)
| codeo.left => fun n => some (Nat.unpair n).1
| codeo.right => fun n => some (Nat.unpair n).2
| codeo.oracle i =>
    match decode i with
    | some a => f a
    | none   => fun _ => ⊥
| codeo.pair cf cg =>
    fun n => Nat.pair <$> evalo f cf n <*> evalo f cg n
| codeo.comp cf cg =>
    fun n => evalo f cg n >>= evalo f cf
| codeo.prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (evalo f cf a) fun y IH => do
        let i ← IH
        evalo f cg (Nat.pair a (Nat.pair y i))
| codeo.rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun x => x = 0) <$> evalo f cf (Nat.pair a (n + m))).map (· + m)

/-- Encodes a code as a natural number. -/
def encodeCodeo : codeo → ℕ
| codeo.zero       => 0
| codeo.succ       => 1
| codeo.left       => 2
| codeo.right      => 3
| codeo.oracle i   => 4 + 5 * i
| codeo.pair cf cg => 4 + (5 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 1)
| codeo.comp cf cg => 4 + (5 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 2)
| codeo.prec cf cg => 4 + (5 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 3)
| codeo.rfind' cf  => 4 + (5 * encodeCodeo cf + 4)

/-- Decodes a natural number into a code; the inverse of `encodeCodeo`. -/
def decodeCodeo : ℕ → codeo
  | 0 => codeo.zero
  | 1 => codeo.succ
  | 2 => codeo.left
  | 3 => codeo.right
  | n + 4 =>
    let q := n / 5
    have hq : q < n + 4 := by
      have : n + 1 ≤ n + 4 := Nat.add_le_add_left (show (1 : ℕ) ≤ 4 from by decide) _
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le (Nat.lt_succ_self _) this)
    have hq₁ : q.unpair.1 < n + 4 := lt_of_le_of_lt q.unpair_left_le hq
    have hq₂ : q.unpair.2 < n + 4 := lt_of_le_of_lt q.unpair_right_le hq
    match n % 5 with
    | 0 => codeo.oracle q
    | 1 => codeo.pair   (decodeCodeo q.unpair.1) (decodeCodeo q.unpair.2)
    | 2 => codeo.comp   (decodeCodeo q.unpair.1) (decodeCodeo q.unpair.2)
    | 3 => codeo.prec   (decodeCodeo q.unpair.1) (decodeCodeo q.unpair.2)
    | _ => codeo.rfind' (decodeCodeo q)
termination_by n => n
decreasing_by all_goals first | exact hq₁ | exact hq₂ | exact hq

theorem encodeCodeo_decodeCodeo' : ∀ c, encodeCodeo (decodeCodeo c) = c :=
fun c => match c with
  | 0 => by simp [decodeCodeo, encodeCodeo]
  | 1 => by simp [decodeCodeo, encodeCodeo]
  | 2 => by simp [decodeCodeo, encodeCodeo]
  | 3 => by simp [decodeCodeo, encodeCodeo]
  | 4 => by simp [decodeCodeo, encodeCodeo]
  | n + 5 => by
    have h_inv : ∀ c : codeo, encodeCodeo (decodeCodeo (encodeCodeo c)) = encodeCodeo c := by
      intro c
      induction n using Nat.strong_induction_on generalizing c with | _ n ih => ?_
      generalize_proofs at *
      induction c generalizing n
      all_goals generalize_proofs at *
      all_goals simp +arith [encodeCodeo, decodeCodeo] at *
      all_goals norm_num [Nat.add_div] at *
      all_goals aesop
    have h_surjective : ∀ m : ℕ, ∃ c : codeo, encodeCodeo c = m := by
      intro m
      use decodeCodeo m
      induction m using Nat.strong_induction_on with | _ m ih => ?_
      rcases m with ( _ | _ | _ | _ | _ | m ) <;> simp +arith only [zero_add, Nat.reduceAdd,
        not_lt_zero, IsEmpty.forall_iff, implies_true, Nat.lt_one_iff, forall_eq] at *
      all_goals unfold decodeCodeo
      all_goals simp +decide only [*] at *
      by_cases h : (m + 1) % 5 = 0 ∨ (m + 1) % 5 = 1 ∨ (m + 1) % 5 = 2 ∨ (m + 1) % 5 = 3 ∨
        (m + 1) % 5 = 4
      · rcases h with ( h | h | h | h | h ) <;> simp +arith only [h]
        · linarith [Nat.mod_add_div (m + 1) 5,
            show encodeCodeo (codeo.oracle ((m + 1) / 5)) = 4 + 5 * ((m + 1) / 5) from rfl]
        · have h_encode_pair : ∀ a b : codeo,
              encodeCodeo (codeo.pair a b)
                = 4 + (5 * Nat.pair (encodeCodeo a) (encodeCodeo b) + 1) := fun _ _ => rfl
          rw [h_encode_pair, ih, ih] <;> norm_num [Nat.div_add_mod]
          · omega
          · exact le_trans (Nat.unpair_right_le _) (by omega)
          · exact le_trans (Nat.unpair_left_le _) (by omega)
        · have := ih ( Nat.unpair ( ( m + 1 ) / 5 ) |>.1 )
            ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5, Nat.div_add_mod ( m + 1 ) 5,
              Nat.mod_lt ( m + 1 ) ( by decide : 5 > 0 ), Nat.unpair_left_le ( ( m + 1 ) / 5 ) ] )
          have := ih ( Nat.unpair ( ( m + 1 ) / 5 ) |>.2 )
            ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5, Nat.div_add_mod ( m + 1 ) 5,
              Nat.mod_lt ( m + 1 ) ( by decide : 5 > 0 ), Nat.unpair_right_le ( ( m + 1 ) / 5 ) ] )
          simp_all +arith +decide [encodeCodeo]
          omega
        · have h_ind : encodeCodeo (decodeCodeo (Nat.unpair ((m + 1) / 5)).1)
                = (Nat.unpair ((m + 1) / 5)).1
              ∧ encodeCodeo (decodeCodeo (Nat.unpair ((m + 1) / 5)).2)
                = (Nat.unpair ((m + 1) / 5)).2 :=
            ⟨ ih _ ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5,
                Nat.unpair_left_le ( ( m + 1 ) / 5 ) ] ),
              ih _ ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5,
                Nat.unpair_right_le ( ( m + 1 ) / 5 ) ] ) ⟩
          simp +arith [*, encodeCodeo] at *
          omega
        · have h_encode_rfind' : encodeCodeo (decodeCodeo ((m + 1) / 5)).rfind'
              = 4 + (5 * encodeCodeo (decodeCodeo ((m + 1) / 5)) + 4) := rfl
          grind
      · grind
    obtain ⟨c, hc⟩ := h_surjective (n + 5)
    specialize h_inv c
    aesop

theorem decodeCodeo_encodeCodeo (c : codeo) : decodeCodeo (encodeCodeo c) = c := by
  have h_inj : ∀ c1 c2 : codeo, encodeCodeo c1 = encodeCodeo c2 → c1 = c2 := by
    intro c1 c2 h_eq
    induction c1 generalizing c2
    all_goals rcases c2 with ( _ | _ | _ | _ | _ | _ | _ | _ | _ ) <;>
      simp only [encodeCodeo, OfNat.one_ne_ofNat, Nat.add_left_cancel_iff, reduceCtorEq,
        zero_ne_one, Nat.succ_ne_self, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false,
        codeo.oracle.injEq, Nat.add_eq_zero_iff, mul_eq_zero, false_or, one_ne_zero, and_false,
        and_self, Nat.add_right_cancel_iff, codeo.rfind'.injEq, OfNat.zero_ne_ofNat,
        Nat.reduceEqDiff, Nat.pair_eq_pair, codeo.prec.injEq, codeo.comp.injEq, false_and,
        codeo.pair.injEq, OfNat.ofNat_ne_one] at h_eq ⊢
    any_goals omega
    · tauto
    · aesop
    · aesop
    · solve_by_elim
  exact h_inj _ _ (encodeCodeo_decodeCodeo' (encodeCodeo c))

/-- Returns a code for the constant function outputting a particular natural. -/
def const : ℕ → codeo
  | 0 => codeo.zero
  | n + 1 => codeo.comp codeo.succ (const n)

theorem const_inj : ∀ {n₁ n₂}, const n₁ = const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
def idCode : codeo :=
  codeo.pair codeo.left codeo.right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : codeo) (n : ℕ) : codeo :=
  codeo.comp c (codeo.pair (const n) idCode)

-- helper lemma to prove rfind' case of univ theorem, since rfind' is defined differently from rfind
theorem rfind'o {α : Type} [Primcodable α] {g : α → ℕ →. ℕ} {cf : codeo}
    (hf : RecursiveIn (Set.range g) (evalo g cf)) :
  RecursiveIn (Set.range g)
    (Nat.unpaired fun a m =>
      (Nat.rfind fun n =>
        (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))
      ).map (· + m))
 :=
  RecursiveIn.rfind' hf

/-- The encoding of the code for the constant function with value `n`. -/
def encodeConst (n : ℕ) : ℕ := encodeCodeo (const n)

/-- One primitive-recursion step used to show `encodeConst` is primitive recursive. -/
def encodeConstStepFun (p : ℕ) : ℕ :=
  let ih := p.unpair.2.unpair.2
  4 + (5 * Nat.pair 1 ih + 2)

/-- Every affine function `n ↦ a * n + b` is primitive recursive. -/
private theorem nat_primrec_linear (a b : ℕ) : Nat.Primrec (fun n => a * n + b) := by
  have hmul : Nat.Primrec (fun n => a * n) :=
    (Nat.Primrec.mul.comp (Nat.Primrec.pair (Nat.Primrec.const a) Nat.Primrec.id)).of_eq fun n => by
      simp
  exact (Nat.Primrec.add.comp (Nat.Primrec.pair hmul (Nat.Primrec.const b))).of_eq fun n => by simp

theorem encode_const_step_primrec : Nat.Primrec encodeConstStepFun := by
  have h_inner : Nat.Primrec (fun p : ℕ => Nat.pair 1 (Nat.unpair (Nat.unpair p).2).2) :=
    Nat.Primrec.pair (Nat.Primrec.const 1) (Nat.Primrec.right.comp Nat.Primrec.right)
  exact ((nat_primrec_linear 5 6).comp h_inner).of_eq fun p => by
    simp only [encodeConstStepFun]
    omega

theorem encode_const_succ (n : ℕ) :
    encodeConst (n + 1) = 4 + (5 * Nat.pair 1 (encodeConst n) + 2) := rfl

theorem encode_const_primrec : Nat.Primrec encodeConst := by
  have ih_step : Nat.Primrec (Nat.unpaired fun a n => Nat.rec (encodeCodeo codeo.zero) (fun y IH =>
      encodeConstStepFun (Nat.pair a (Nat.pair y IH))) n) := by
    apply_rules [ Nat.Primrec.prec, Nat.Primrec.const ];
    apply encode_const_step_primrec;
  have h_eq : ∀ n, Nat.unpaired (fun a n => Nat.rec (encodeCodeo codeo.zero) (fun y IH =>
      encodeConstStepFun (Nat.pair a (Nat.pair y IH))) n) (Nat.pair 0 n) = encodeConst n := by
    intro n; induction n <;> simp_all +decide only [Nat.unpaired, Nat.unpair_pair];
    unfold encodeConstStepFun encodeConst; aesop;
  convert ih_step.comp ( show Nat.Primrec fun n => Nat.pair 0 n from ?_ ) using 1;
  · exact funext fun n => h_eq n ▸ rfl;
  · exact Nat.Primrec.pair ( Nat.Primrec.const 0 ) Nat.Primrec.id

/-- The encoding of the code pairing the constant `n` with the identity code. -/
def sInner (n : ℕ) : ℕ := encodeCodeo (codeo.pair (const n) idCode)

@[simp] lemma s_inner_eq (n : ℕ) :
    sInner n = 4 + (5 * Nat.pair (encodeConst n) (encodeCodeo idCode) + 1) := rfl

theorem s_inner_primrec : Nat.Primrec sInner := by
  have h_pair : Nat.Primrec (fun n => Nat.pair (encodeCodeo (const n)) (encodeCodeo idCode)) :=
    Nat.Primrec.pair encode_const_primrec (Nat.Primrec.const _)
  exact ((nat_primrec_linear 5 5).comp h_pair).of_eq fun n => by
    simp only [sInner, encodeCodeo]
    omega

/-- The encoding of the code applying oracle `0` to the constant `n` (an `s`-`m`-`n` index). -/
def s (n : ℕ) : ℕ := encodeCodeo (codeo.comp (codeo.oracle 0) (const n))

theorem s_eq (n : ℕ) : s n = 4 + (5 * Nat.pair 4 (encodeConst n) + 2) := rfl

theorem s_primrec : Nat.Primrec s := by
  have h_pair : Nat.Primrec (fun n => Nat.pair (encodeCodeo (codeo.oracle 0)) (encodeConst n)) :=
    Nat.Primrec.pair (Nat.Primrec.const _) encode_const_primrec
  exact ((nat_primrec_linear 5 6).comp h_pair).of_eq fun n => by
    simp only [s, encodeCodeo, encodeConst]
    omega

/-- A function is partial recursive relative to an indexed set of oracles `O` if and only if there
is a code implementing it.
Therefore, `evalo` is a **universal partial recursive function relative to `g`**. -/
theorem exists_code_rel {α : Type} [Primcodable α] (g : α → ℕ →. ℕ) (f : ℕ →. ℕ) :
  RecursiveIn (Set.range g) f ↔ ∃ c : codeo, evalo g c = f := by
  constructor
  · intro gf
    induction gf with
    | zero => exact ⟨codeo.zero, rfl⟩
    | succ => exact ⟨codeo.succ, rfl⟩
    | left => exact ⟨codeo.left, rfl⟩
    | right => exact ⟨codeo.right, rfl⟩
    | oracle _ hf =>
      rcases hf with ⟨cf, rfl⟩
      exact ⟨codeo.oracle (encode cf), by
        funext n
        simp only [evalo]
        rw [encodek]⟩
    | pair _ _ hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.pair cf cg, rfl⟩
    | comp _ _ hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.comp cf cg, rfl⟩
    | prec _ _ hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.prec cf cg, rfl⟩
    | rfind _ hf =>
      rcases hf with ⟨cg, h⟩
      use (cg.rfind'.comp (idCode.pair codeo.zero))
      funext a
      have hz : (pure 0 : ℕ →. ℕ) a = Part.some 0 := rfl
      have key : evalo g (idCode.pair codeo.zero) a = Part.some (Nat.pair a 0) := by
        simp only [evalo, idCode, Seq.seq, hz]
        simp [Part.map_some, Part.bind_some]
      change (evalo g (idCode.pair codeo.zero) a >>= evalo g cg.rfind') = _
      rw [key]
      change (Part.bind (Part.some (Nat.pair a 0)) (evalo g cg.rfind')) = _
      rw [Part.bind_some]
      simp only [evalo, Nat.unpaired, Nat.unpair_pair, add_zero, h]
      exact Part.map_id' (fun _ => rfl) _
  · rintro ⟨c, rfl⟩
    induction c with
    | zero => exact RecursiveIn.zero
    | succ => exact RecursiveIn.succ
    | left => exact RecursiveIn.left
    | right => exact RecursiveIn.right
    | oracle i =>
      cases h : decode (α := α) i with
      | some a =>
        apply RecursiveIn.of_eq (RecursiveIn.oracle (g a) (Set.mem_range_self _))
        intro n
        simp [evalo, h]
      | none =>
        apply RecursiveIn.of_eq RecursiveIn.none
        intro n
        simp [evalo, h]
        rfl
    | pair cf cg pf pg => exact pf.pair pg
    | comp cf cg pf pg => exact pf.comp pg
    | prec cf cg pf pg => exact pf.prec pg
    | rfind' cf pf => exact rfind'o pf

end Computability
