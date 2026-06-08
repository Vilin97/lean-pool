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


open Denumerable Encodable

-- This section provides and encoding for oracle partial recursive functions and a definition
-- of the universal partial recursive function relative to an oracle, along with a proof that it is universal.

/-
The identity function is recursive in any oracle O.
-/
theorem RecursiveIn_id {O : Set (ℕ →. ℕ)} : RecursiveIn O (fun n => Part.some n) := by
  -- The left and right projections are recursive, so their pairing is also recursive.
  have h_left : RecursiveIn O (fun n => Part.some (Nat.unpair n).1) := by
    -- The left projection function is one of the basic functions in the definition of recursive functions, so it is recursive.
    apply RecursiveIn.left
  have h_right : RecursiveIn O (fun n => Part.some (Nat.unpair n).2) := by
    -- The right projection function is primitive recursive, so it is recursive.
    apply RecursiveIn.right;
  have h_pair : ∀ (f g : ℕ →. ℕ), RecursiveIn O f → RecursiveIn O g → RecursiveIn O (fun n => (f n).bind (fun x => (g n).map (fun y => Nat.pair x y))) := by
    exact fun f g a a_1 ↦ RecursiveIn.pair a a_1;
  convert h_pair _ _ h_left h_right using 2 ; aesop



/-
Addition is recursive.
-/
lemma RecursiveIn_comp_total {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
  (hf : RecursiveIn O (fun n => Part.some (f n)))
  (hg : RecursiveIn O (fun n => Part.some (g n))) :
  RecursiveIn O (fun n => Part.some (f (g n))) := by
    -- Apply the composition theorem to f and g, given that they are both recursive.
    have h_comp : RecursiveIn O (fun n => Part.some (f (g n))) := by
      have h_f : RecursiveIn O (fun n => Part.some (f n)) := hf
      have h_g : RecursiveIn O (fun n => Part.some (g n)) := hg
      exact (by
      convert h_f.comp h_g using 1;
      aesop);
    exact h_comp

lemma RecursiveIn_pair_total {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
  (hf : RecursiveIn O (fun n => Part.some (f n)))
  (hg : RecursiveIn O (fun n => Part.some (g n))) :
  RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
    -- By definition of $RecursiveIn$, we know that the composition of the projection function and the pairing function is recursive.
    have h_comp : RecursiveIn O (fun n => Part.some (Nat.unpair (Nat.pair (f n) (g n)) |>.1)) ∧ RecursiveIn O (fun n => Part.some (Nat.unpair (Nat.pair (f n) (g n)) |>.2)) := by
      aesop;
    convert RecursiveIn.pair h_comp.1 h_comp.2 using 1;
    ext; simp only [Part.mem_some_iff, Nat.unpair_pair, Part.map_eq_map, Part.map_some];
    erw [ Part.mem_bind_iff ] ; aesop

lemma RecursiveIn_prec_total {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} {h : ℕ → ℕ}
  (hf : RecursiveIn O (fun n => Part.some (f n)))
  (hh : RecursiveIn O (fun n => Part.some (h n))) :
  RecursiveIn O (fun p => Part.some (Nat.rec (f p.unpair.1) (fun y IH => h (Nat.pair p.unpair.1 (Nat.pair y IH))) p.unpair.2)) := by
    convert ( RecursiveIn.prec ) ?_ ?_ using 1;
    simp +zetaDelta at *;
    rotate_left;
    exact fun n => Part.some ( f n );
    exact fun n => Part.some ( h n );
    · assumption;
    · assumption;
    · -- By induction on the second component of the pair, we can show that the two functions are equal.
      funext p; induction' (Nat.unpair p).2 with y ih generalizing p; aesop;
      simp +decide [ ← ih ]

theorem RecursiveIn_add {O : Set (ℕ →. ℕ)} : RecursiveIn O (fun p => Part.some (p.unpair.1 + p.unpair.2)) := by
  -- By definition of primitive recursive functions, addition is primitive recursive.
  have h_primrec : Nat.Primrec (fun p : ℕ => (Nat.unpair p).1 + (Nat.unpair p).2) := by
    -- The addition function is primitive recursive by definition.
    apply Nat.Primrec.add;
  -- Since primitive recursive functions are a subset of recursive functions, and recursive functions are closed under composition with oracles, this should hold.
  have h_rec : ∀ {f : ℕ → ℕ}, Nat.Primrec f → RecursiveIn O (fun p => Part.some (f p)) := by
    intro f hf;
    induction hf;
    all_goals try { exact? };
    -- The successor function is primitive recursive, so it is recursive in any oracle.
    apply RecursiveIn.succ;
  exact h_rec h_primrec

/-
Every primitive recursive function is recursive.
-/
theorem RecursiveIn_of_Primrec {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} (hf : Nat.Primrec f) : RecursiveIn O (fun n => Part.some (f n)) := by
  induction hf
  case zero =>
    exact RecursiveIn.zero
  case succ =>
    exact RecursiveIn.succ
  case left =>
    exact RecursiveIn.left
  case right =>
    exact RecursiveIn.right
  case pair f g hf hg ihf ihg =>
    apply RecursiveIn_pair_total ihf ihg
  case comp f g hf hg ihf ihg =>
    apply RecursiveIn_comp_total ihf ihg
  case prec f g hf hg ihf ihg =>
    apply RecursiveIn_prec_total ihf ihg

theorem RecursiveIn.rfind' {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
  RecursiveIn O (Nat.unpaired fun a m =>
    (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m))
  := by
    have hg : RecursiveIn O (fun x => f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2))) := by
      have h_g : RecursiveIn O (fun p => f (Nat.pair (p.unpair.1.unpair.1) (p.unpair.1.unpair.2 + p.unpair.2))) := by
        have h_g : RecursiveIn O (fun p => Nat.pair (p.unpair.1.unpair.1) (p.unpair.1.unpair.2 + p.unpair.2)) := by
          apply RecursiveIn_pair_total;
          · apply RecursiveIn_of_Primrec;
            have h_unpair1 : Nat.Primrec (fun n => (Nat.unpair n).1) := by
              exact Nat.Primrec.left;
            exact h_unpair1.comp h_unpair1;
          · convert RecursiveIn_add.comp _ using 1;
            rotate_left;
            exact fun n => Part.some ( Nat.pair ( Nat.unpair ( Nat.unpair n |>.1 ) |>.2 ) ( Nat.unpair n |>.2 ) );
            · apply RecursiveIn_pair_total;
              · convert RecursiveIn_of_Primrec _ using 1;
                have h_comp : Nat.Primrec (fun n => (Nat.unpair n).1) ∧ Nat.Primrec (fun n => (Nat.unpair n).2) := by
                  constructor;
                  · exact Nat.Primrec.left;
                  · exact Nat.Primrec.right;
                exact h_comp.2.comp h_comp.1;
              · exact right;
            · simp at *
        have h_g : RecursiveIn O (fun p => f (Nat.pair (p.unpair.1.unpair.1) (p.unpair.1.unpair.2 + p.unpair.2))) := by
          have := h_g
          convert RecursiveIn.comp hf this using 1;
          aesop;
        assumption;
      simpa only [ add_comm ] using h_g;
    have hH : RecursiveIn O (fun p => Nat.rfind (fun n => let x := Nat.pair p n; (fun m => Decidable.decide (m = 0)) <$> f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2)))) := by
      convert hg.rfind;
    have h_target : RecursiveIn O (fun p => (Nat.rfind (fun n => let x := Nat.pair p n; (fun m => Decidable.decide (m = 0)) <$> f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2)))) + (Nat.unpair p).2) := by
      have h_target : RecursiveIn O (fun p => (Nat.rfind (fun n => let x := Nat.pair p n; (fun m => Decidable.decide (m = 0)) <$> f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2)))) + (Nat.unpair p).2) := by
        have h_comp : RecursiveIn O (fun p => (Nat.rfind (fun n => let x := Nat.pair p n; (fun m => Decidable.decide (m = 0)) <$> f (Nat.pair (x.unpair.1).unpair.1 (x.unpair.2 + (x.unpair.1).unpair.2))))) := hH
        have h_add : RecursiveIn O (fun p => (Nat.unpair p).2) := by
          exact right
        convert RecursiveIn_add.comp ( h_comp.pair h_add ) using 1;
        ext;
        simp_all only [Nat.unpair_pair, Part.map_eq_map, Part.coe_some, Part.bind_eq_bind, Part.mem_bind_iff,
          Part.mem_some_iff]
        apply Iff.intro
        · intro a_1
          rename_i a b
          obtain ⟨x, hx⟩ : ∃ x, b = x + (Nat.unpair a).2 := by
            cases a_1 ; aesop;
          use Nat.pair x (Nat.unpair a).2;
          subst hx
          simp_all only [Nat.unpair_pair, and_true]
          cases a_1 ;
          rename_i w h
          simp_all only [Part.add_get_eq, Part.get_some, Nat.add_right_cancel_iff]
          subst h
          exact ⟨ w, by aesop ⟩;
        · intro a_1
          rename_i a b
          obtain ⟨w, h⟩ := a_1
          obtain ⟨left, right⟩ := h
          subst right
          obtain ⟨n, hn⟩ : ∃ n, (Nat.rfind (fun n => Part.map (fun m => Decidable.decide (m = 0)) (f (Nat.pair (Nat.unpair a).1 (n + (Nat.unpair a).2))))) = Part.some n ∧ w = Nat.pair n (Nat.unpair a).2 := by
            cases left ; aesop;
          simp_all only [Part.map_some, Nat.unpair_pair]
          obtain ⟨left_1, right⟩ := hn
          subst right
          simp [Part.some, Part.add_def];
      convert h_target using 1;
    convert h_target using 1;
    funext p; simp [Nat.unpaired];
    cases h : Nat.rfind ( fun n => Part.map ( fun m => Decidable.decide ( m = 0 ) ) ( f ( Nat.pair ( Nat.unpair p ).1 ( n + ( Nat.unpair p ).2 ) ) ) ) ;
    simp_all only [Nat.unpair_pair, Part.map_eq_map, Part.coe_some]
    ext ; simp [ Part.map ];
    simp [ Part.add_def ];
    simp only [eq_comm]

def oracleCode {α : Type} [Denumerable α] (f : α → ℕ →. ℕ) : ℕ → ℕ →. ℕ :=
  λ i n => match decode i with
           | some a => f a n
           | none   => ⊥

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
    | none   => λ _ => ⊥
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
decreasing_by
  simp [Nat.add_comm, Nat.add_left_comm]  -- turns n+3+1 into n+4
  simp [q] at hq₁ hq₂
  · exact hq₁
  · exact hq₂
  · aesop

theorem encodeCodeo_decodeCodeo' : ∀ c, encodeCodeo (decodeCodeo c) = c :=
λ c => match c with
  | 0 => by simp [decodeCodeo, encodeCodeo]
  | 1 => by simp [decodeCodeo, encodeCodeo]
  | 2 => by simp [decodeCodeo, encodeCodeo]
  | 3 => by simp [decodeCodeo, encodeCodeo]
  | 4 => by simp [decodeCodeo, encodeCodeo]
  | n + 5 => by
    have h_inv : ∀ c : codeo, encodeCodeo (decodeCodeo (encodeCodeo c)) = encodeCodeo c := by
      intro c
      induction' n using Nat.strong_induction_on with n ih generalizing c
      generalize_proofs at *;
      induction' c with c ih generalizing n
      all_goals generalize_proofs at *;
      all_goals simp +arith [ encodeCodeo, decodeCodeo ] at *;
      · norm_num [ Nat.add_div ] at * ; aesop ;
      · norm_num [ Nat.add_div ] at * ; aesop ;
      · norm_num [ Nat.add_div ] at * ; aesop ;
      · norm_num [ Nat.add_div ] at * ; aesop ;
    have h_surjective : ∀ m : ℕ, ∃ c : codeo, encodeCodeo c = m := by
      intro m;
      use decodeCodeo m;
      induction' m using Nat.strong_induction_on with m ih;
      rcases m with ( _ | _ | _ | _ | _ | m ) <;> simp +arith [ * ] at *;
      all_goals unfold decodeCodeo; simp +decide [ * ] at *;
      by_cases h : (m + 1) % 5 = 0 ∨ (m + 1) % 5 = 1 ∨ (m + 1) % 5 = 2 ∨ (m + 1) % 5 = 3 ∨ (m + 1) % 5 = 4;
      · rcases h with ( h | h | h | h | h ) <;> simp +arith [ h ];
        · have h_encode_oracle : ∀ i : ℕ, encodeCodeo (codeo.oracle i) = 4 + 5 * i := by
            exact fun i ↦ rfl;
          linarith [ Nat.mod_add_div ( m + 1 ) 5, h_encode_oracle ( ( m + 1 ) / 5 ) ];
        · have h_encode_pair : ∀ a b : codeo, encodeCodeo (codeo.pair a b) = 4 + (5 * Nat.pair (encodeCodeo a) (encodeCodeo b) + 1) := by
            aesop;
          rw [ h_encode_pair, ih, ih ] <;> norm_num [ Nat.div_add_mod ];
          · omega;
          · exact le_trans ( Nat.unpair_right_le _ ) ( by omega );
          · exact le_trans ( Nat.unpair_left_le _ ) ( by omega );
        · have := ih ( Nat.unpair ( ( m + 1 ) / 5 ) |>.1 ) ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5, Nat.div_add_mod ( m + 1 ) 5, Nat.mod_lt ( m + 1 ) ( by decide : 5 > 0 ), Nat.unpair_left_le ( ( m + 1 ) / 5 ) ] ) ; have := ih ( Nat.unpair ( ( m + 1 ) / 5 ) |>.2 ) ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5, Nat.div_add_mod ( m + 1 ) 5, Nat.mod_lt ( m + 1 ) ( by decide : 5 > 0 ), Nat.unpair_right_le ( ( m + 1 ) / 5 ) ] ) ; simp_all +arith +decide [ encodeCodeo ] ;
          omega;
        · have h_ind : encodeCodeo (decodeCodeo (Nat.unpair ((m + 1) / 5)).1) = (Nat.unpair ((m + 1) / 5)).1 ∧ encodeCodeo (decodeCodeo (Nat.unpair ((m + 1) / 5)).2) = (Nat.unpair ((m + 1) / 5)).2 := by
            exact ⟨ ih _ ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5, Nat.unpair_left_le ( ( m + 1 ) / 5 ) ] ), ih _ ( by linarith [ Nat.div_mul_le_self ( m + 1 ) 5, Nat.unpair_right_le ( ( m + 1 ) / 5 ) ] ) ⟩;
          simp +arith [ *, encodeCodeo ] at * ; omega;
        · have h_encode_rfind' : encodeCodeo (decodeCodeo ((m + 1) / 5)).rfind' = 4 + (5 * encodeCodeo (decodeCodeo ((m + 1) / 5)) + 4) := by
            rfl;
          grind;
      · grind;
    obtain ⟨ c, hc ⟩ := h_surjective ( n + 5 ) ; specialize h_inv c; aesop;

theorem decodeCodeo_encodeCodeo (c : codeo) : decodeCodeo (encodeCodeo c) = c := by
  apply Eq.symm; exact (by
  have h_encode_decode : ∀ c : codeo, encodeCodeo (decodeCodeo (encodeCodeo c)) = encodeCodeo c := by
    intros c
    apply encodeCodeo_decodeCodeo';
  have h_inj : ∀ c1 c2 : codeo, encodeCodeo c1 = encodeCodeo c2 → c1 = c2 := by
    intros c1 c2 h_eq
    induction' c1 with c1 ih generalizing c2;
    all_goals rcases c2 with ( _ | _ | _ | _ | _ | _ | _ | _ | _ ) <;> simp [ encodeCodeo ] at h_eq ⊢;
    any_goals omega;
    · tauto;
    · aesop;
    · aesop;
    · solve_by_elim;
  exact h_inj _ _ ( h_encode_decode c |> Eq.symm ))

/-- Returns a code for the constant function outputting a particular natural. -/
def const : ℕ → codeo
  | 0 => codeo.zero
  | n + 1 => codeo.comp codeo.succ (const n)

def const_inj : ∀ {n₁ n₂}, const n₁ = const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
def id_code : codeo :=
  codeo.pair codeo.left codeo.right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : codeo) (n : ℕ) : codeo :=
  codeo.comp c (codeo.pair (const n) id_code)

-- helper lemma to prove rfind' case of univ theorem, since rfind' is defined differently from rfind
theorem rfind'o {α : Type} [Primcodable α] {g : α → ℕ →. ℕ} {cf : codeo}
    (hf : RecursiveIn (Set.range g) (evalo g cf)) :
  RecursiveIn (Set.range g)
    (Nat.unpaired fun a m =>
      (Nat.rfind fun n =>
        (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))
      ).map (· + m))
 := by
   convert RecursiveIn.rfind' hf using 1

def encode_const (n : ℕ) : ℕ := encodeCodeo (const n)

def encode_const_step_fun (p : ℕ) : ℕ :=
  let ih := p.unpair.2.unpair.2
  4 + (5 * Nat.pair 1 ih + 2)

theorem encode_const_step_primrec : Nat.Primrec encode_const_step_fun := by
  have h_encode_const_step_fun_primrec : Nat.Primrec (fun n => 5 * n + 4) := by
    have h_add_mul : Nat.Primrec (fun n => n + 4) ∧ Nat.Primrec (fun n => 5 * n) := by
      have h_succ : Nat.Primrec Nat.succ := by
        apply Nat.Primrec.succ;
      constructor;
      · exact Nat.Primrec.of_eq ( h_succ.comp Nat.Primrec.id |> Nat.Primrec.comp <| h_succ.comp Nat.Primrec.id |> Nat.Primrec.comp <| h_succ.comp Nat.Primrec.id |> Nat.Primrec.comp <| h_succ ) fun n => by simp +arith +decide;
      · have h_mul : Nat.Primrec (fun n => Nat.mul 5 n) := by
          have h_mul_const : ∀ c : ℕ, Nat.Primrec (fun n => Nat.mul c n) := by
            intro c; induction c <;>
            simp_all only [Nat.mul_eq, zero_mul]
            · exact Nat.Primrec.const 0;
            · simp [ add_mul ];
              rename_i n ih;
              have h_add : Nat.Primrec (fun n_1 => n * n_1) → Nat.Primrec (fun n_1 => n_1) → Nat.Primrec (fun n_1 => n * n_1 + n_1) := by
                intros h1 h2; exact (by
                apply Nat.Primrec.of_eq;
                apply Nat.Primrec.comp Nat.Primrec.add (Nat.Primrec.pair h1 h2);
                all_goals norm_num [ Nat.unpair_pair ]);
              exact h_add ih ( Nat.Primrec.id )
          exact h_mul_const 5;
        exact h_mul;
    exact h_add_mul.1.comp h_add_mul.2;
  have h_encode_const_step_fun_primrec : Nat.Primrec (fun n => 5 * n + 4) → Nat.Primrec (fun n => 5 * n + 4 + 2) := by
    exact fun _ => Nat.Primrec.succ.comp ( Nat.Primrec.succ.comp h_encode_const_step_fun_primrec );
  unfold encode_const_step_fun;
  simp_all only [forall_const]
  convert h_encode_const_step_fun_primrec.comp ( show Nat.Primrec ( fun p : ℕ => Nat.pair 1 ( Nat.unpair ( Nat.unpair p ).2 ).2 ) from ?_ ) using 1;
  · ac_rfl;
  · convert Nat.Primrec.pair ( Nat.Primrec.const 1 ) ( Nat.Primrec.comp ( show Nat.Primrec ( fun p : ℕ => Nat.unpair p |> Prod.snd ) from ?_ ) ( show Nat.Primrec ( fun p : ℕ => Nat.unpair p |> Prod.snd ) from ?_ ) ) using 1
    all_goals generalize_proofs at *;
    · exact Nat.Primrec.right;
    · exact Nat.Primrec.right

theorem encode_const_succ (n : ℕ) : encode_const (n + 1) = 4 + (5 * Nat.pair 1 (encode_const n) + 2) := by
  rw [show encode_const (n + 1) = 4 + (5 * Nat.pair 1 (encode_const n) + 2) from rfl]

theorem encode_const_primrec : Nat.Primrec encode_const := by
  have ih_step : Nat.Primrec (Nat.unpaired fun a n => Nat.rec (encodeCodeo codeo.zero) (fun y IH => encode_const_step_fun (Nat.pair a (Nat.pair y IH))) n) := by
    apply_rules [ Nat.Primrec.prec, Nat.Primrec.const ];
    apply encode_const_step_primrec;
  have h_eq : ∀ n, Nat.unpaired (fun a n => Nat.rec (encodeCodeo codeo.zero) (fun y IH => encode_const_step_fun (Nat.pair a (Nat.pair y IH))) n) (Nat.pair 0 n) = encode_const n := by
    intro n; induction n <;> simp_all +decide [ Nat.unpair_pair ] ;
    unfold encode_const_step_fun encode_const; aesop;
  convert ih_step.comp ( show Nat.Primrec fun n => Nat.pair 0 n from ?_ ) using 1;
  · exact funext fun n => h_eq n ▸ rfl;
  · exact Nat.Primrec.pair ( Nat.Primrec.const 0 ) Nat.Primrec.id

def s_inner (n : ℕ) : ℕ := encodeCodeo (codeo.pair (const n) id_code)

@[simp] lemma s_inner_eq (n : ℕ) : s_inner n = 4 + (5 * Nat.pair (encode_const n) (encodeCodeo id_code) + 1) := by rfl

theorem s_inner_primrec : Nat.Primrec s_inner := by
  have h_pair : Nat.Primrec (fun n => Nat.pair (encodeCodeo (const n)) (encodeCodeo id_code)) := by
    exact Nat.Primrec.pair encode_const_primrec ( Nat.Primrec.const _ );
  have h_linear : Nat.Primrec (fun n => 4 + (5 * n + 1)) := by
    have h_linear' : Nat.Primrec (fun n => 5 * n + 1) := by
      have h_linear'' : Nat.Primrec (fun n => 5 * n) := by
        have h_mul_const : ∀ k : ℕ, Nat.Primrec (fun n => k * n) := by
          intro k; induction' k with k ih <;> simp_all [ Nat.succ_mul ] ;
          · exact Nat.Primrec.const 0;
          · have h_sum : Nat.Primrec (fun n => k * n) → Nat.Primrec (fun n => n) → Nat.Primrec (fun n => k * n + n) := by
              intro h1 h2
              exact Nat.Primrec.of_eq (Nat.Primrec.comp (Nat.Primrec.add) (h1.pair h2)) (by
              simp [ Nat.unpair_pair ]);
            exact h_sum ih ( by exact Nat.Primrec.id )
        exact h_mul_const 5;
      exact Nat.Primrec.succ.comp h_linear'';
    have h_add : Nat.Primrec (fun n => 4 + n) := by
      exact Nat.Primrec.succ.comp ( Nat.Primrec.succ.comp ( Nat.Primrec.succ.comp ( Nat.Primrec.succ.comp Nat.Primrec.id ) ) ) |> fun h => h.of_eq fun n => by simp +arith +decide only [id_eq,
        Nat.succ_eq_add_one];
    exact h_add.comp h_linear';
  exact h_linear.comp h_pair

def s (n : ℕ) : ℕ := encodeCodeo (codeo.comp (codeo.oracle 0) (const n))

theorem s_eq (n : ℕ) : s n = 4 + (5 * Nat.pair 4 (encode_const n) + 2) := by
  rw [show s n = 4 + (5 * Nat.pair 4 (encode_const n) + 2) from rfl]

theorem s_primrec : Nat.Primrec s := by
  have h_comp : Nat.Primrec (fun n => encode_const n) ∧ Nat.Primrec (fun n => encodeCodeo id_code) := by
    apply And.intro (encode_const_primrec);
    apply Nat.Primrec.const;
  unfold s; have := h_comp.1; have := h_comp.2;
  simp_all only [and_self]
  apply Nat.Primrec.comp;
  · have h_add_const : Nat.Primrec (fun n => n + 4) := by
      exact Nat.Primrec.succ.comp ( Nat.Primrec.succ.comp ( Nat.Primrec.succ.comp ( Nat.Primrec.succ.comp Nat.Primrec.id ) ) );
    exact h_add_const.of_eq fun n => by ac_rfl;
  · have h_pair : Nat.Primrec (fun n => Nat.pair (encodeCodeo (codeo.oracle 0)) (encode_const n)) := by
      exact Nat.Primrec.pair ( Nat.Primrec.const _ ) ( encode_const_primrec );
    have h_mul : Nat.Primrec (fun n => 5 * Nat.pair (encodeCodeo (codeo.oracle 0)) (encode_const n)) := by
      have h_mul : Nat.Primrec (fun n => 5 * n) := by
        have h_id : Nat.Primrec (fun n => n) := by
          exact Nat.Primrec.id
        exact Nat.Primrec.of_eq ( Nat.Primrec.comp ( Nat.Primrec.mul ) ( (Nat.Primrec.const 5).pair h_id ) ) fun n => by simp ;
      exact h_mul.comp h_pair
    have h_add : Nat.Primrec (fun n => 5 * Nat.pair (encodeCodeo (codeo.oracle 0)) (encode_const n) + 2) := by
      have h_add : Nat.Primrec (fun n => 5 * Nat.pair (encodeCodeo (codeo.oracle 0)) (encode_const n)) ∧ Nat.Primrec (fun n => 2) := by
        exact ⟨ h_mul, Nat.Primrec.const 2 ⟩;
      apply Nat.Primrec.comp;
      · exact Nat.Primrec.succ;
      · simp_all only [Nat.add_eq]
        obtain ⟨lt, rt⟩ := h_add
        exact Nat.Primrec.succ.comp lt
    exact h_add

/-- A function is partial recursive relative to an indexed set of oracles `O` if and only if there is a code implementing it.
Therefore, `evalo` is a **universal partial recursive function relative to `g`**. -/
theorem exists_code_rel {α : Type} [Primcodable α] (g : α → ℕ →. ℕ) (f : ℕ →. ℕ) :
  RecursiveIn (Set.range g) f ↔ ∃ c : codeo, evalo g c = f := by
  constructor
  · intro gf
    induction gf
    · exact ⟨codeo.zero, rfl⟩
    · exact ⟨codeo.succ, rfl⟩
    · exact ⟨codeo.left, rfl⟩
    · exact ⟨codeo.right, rfl⟩
    · case mp.oracle hf =>
      rcases hf with ⟨cf, rfl⟩
      exact ⟨codeo.oracle (encode cf), by
        funext n
        simp only [evalo]
        rw [encodek]⟩
    · case mp.pair hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.pair cf cg, rfl⟩
    · case mp.comp hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.comp cf cg, rfl⟩
    · case mp.prec hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.prec cf cg, rfl⟩
    · case mp.rfind f' pf hf =>
      rcases hf with ⟨cg, h⟩
      use (cg.rfind'.comp (id_code.pair codeo.zero))
      simp [evalo]
      have h_id : ∀ n, evalo g id_code n = Part.some n := by
        intro n; unfold id_code;
        subst h
        have h_left_right : evalo g codeo.left n = some (Nat.unpair n).1 ∧ evalo g codeo.right n = some (Nat.unpair n).2 := by
          aesop;
        have h_pair : evalo g (codeo.left.pair codeo.right) n = Part.map (fun p => Nat.pair p.1 p.2) (Part.bind (evalo g codeo.left n) fun x => Part.bind (evalo g codeo.right n) fun y => Part.some (x, y)) := by
          norm_num at *;
          exact
            Eq.symm
              (Part.Dom.bind trivial fun y ↦
                (evalo g codeo.right n).bind fun y_1 ↦ Part.some (Nat.pair y y_1));
        aesop;
      ext; aesop;
      · cases left ;
        rename_i h
        subst h
        convert left_1 using 1;
        congr;
        have h_unpair : Nat.unpair (Nat.pair a 0) = (a, 0) := by
          exact Nat.unpair_pair a 0;
        convert congr_arg Prod.fst h_unpair.symm using 1;
      · cases left ;
        rename_i h
        subst h
        have h_m_lt_w1 : m < w_1 := by
          convert a_1 using 1;
          have h_unpair : Nat.unpair (Nat.pair a 0) = (a, 0) := by
            exact Nat.unpair_pair _ _;
          exact h_unpair.symm ▸ rfl;
        obtain ⟨a_2, ha_2⟩ := right_1 h_m_lt_w1;
        use a_2;
        simp_all only [not_false_eq_true, and_true]
        obtain ⟨left, right⟩ := ha_2
        convert left using 1;
        congr! 2;
        · have h_unpair : Nat.unpair (Nat.pair a 0) = (a, 0) := by
            exact Nat.unpair_pair a 0;
          convert congr_arg Prod.fst h_unpair.symm using 1;
        · simp;
          have h_unpair : Nat.unpair (Nat.pair a 0) = (a, 0) := by
            exact Nat.unpair_pair a 0;
          convert congr_arg Prod.snd h_unpair using 1;
      · use Nat.pair a 0;
        simp_all only [Nat.unpair_pair, add_zero, exists_eq_right, implies_true, and_self, and_true]
        exact ⟨ ⟨ trivial, trivial ⟩, rfl ⟩
  · rintro ⟨c, rfl⟩
    induction c with
    | zero =>
      exact RecursiveIn.zero
    | succ =>
      exact RecursiveIn.succ
    | left =>
      exact RecursiveIn.left
    | right =>
      exact RecursiveIn.right
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
    | pair cf cg pf pg =>
      exact pf.pair pg
    | comp cf cg pf pg =>
      apply RecursiveIn.comp
      exact pf
      exact pg
    | prec cf cg pf pg =>
      apply RecursiveIn.prec
      exact pf
      exact pg
    | rfind' cf pf =>
      apply rfind'o
      exact pf
