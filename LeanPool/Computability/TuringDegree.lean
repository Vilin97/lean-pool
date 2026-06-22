/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import LeanPool.Computability.Oracle
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NormNum
import Aesop
import Mathlib.Computability.Halting

/-!
# Turing Reducibility and Turing Degrees

This file defines Turing reducibility and Turing equivalence in terms of oracle computability,
as well as the notion of Turing degrees as equivalence classes under mutual reducibility.

## Main Definitions

* `TuringReducible f g`:
  The function `f` is Turing reducible to `g` if `f` is recursive in the singleton set `{g}`.
* `TuringEquivalent f g`:
  Functions `f` and `g` are Turing equivalent if they are mutually Turing reducible.
* `TuringDegree`:
  The type of Turing degrees, given by the quotient of `ℕ →. ℕ` under `TuringEquivalent`.

## Notation

* `f ≤ᵀ g`: `f` is Turing reducible to `g`.
* `f ≡ᵀ g`: `f` is Turing equivalent to `g`.

## Implementation Notes

We define `TuringDegree` as the `Antisymmetrization` of the preorder of partial functions under
Turing reducibility. This gives a concrete representation of degrees as equivalence classes.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.

## Tags

Computability, Turing Degrees, Reducibility, Equivalence Relation
-/


namespace Computability

/--
`f` is Turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := .oracle _ <| by simp
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _

instance : Std.Refl TuringReducible where refl _ := .rfl

theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h := by
  induction hg with
  | zero | succ | left | right => constructor
  | oracle g' hg => rw [hg]; exact hh
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

instance : IsTrans (ℕ →. ℕ) TuringReducible :=
  ⟨@TuringReducible.trans⟩

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := .refl

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
protected theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

private instance : Preorder (ℕ →. ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization

open scoped Computability
open Encodable

/-!
## Turing join on partial functions

We define the join \(f ⊕ g\) by coding answers from `f` as even numbers and answers from `g` as odd
numbers:

- on even inputs `2*n`, query `f n` and return `2 * y`
- on odd inputs `2*n+1`, query `g n` and return `2 * y + 1`
-/

/-- The Turing join `f ⊕ g`: answers from `f` are coded as even numbers and answers from `g` as
odd numbers. -/
def turingJoin (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n =>
    cond n.bodd ( (g n.div2).map (fun y => 2 * y + 1) ) ( (f n.div2).map (fun y => 2 * y) )

@[inherit_doc] infix:50 " ⊕ " => turingJoin

@[simp] lemma turingJoin_even (f g : ℕ →. ℕ) (n : ℕ) :
    (f ⊕ g) (2 * n) = (f n).map (fun y => 2 * y) := by
  simp [turingJoin]

@[simp] lemma turingJoin_odd (f g : ℕ →. ℕ) (n : ℕ) :
    (f ⊕ g) (2 * n + 1) = (g n).map (fun y => 2 * y + 1) := by
  simp [turingJoin, Nat.bodd_mul]

/-- Decode a side of the Turing join `j` from the oracle: querying `j` at the primitive recursive
index `q n` and applying `div2` recovers `h n`. -/
private lemma le_join_aux (j h : ℕ →. ℕ) (q : ℕ → ℕ)
    (hq : RecursiveIn {j} (fun n : ℕ => (q n : ℕ)))
    (hdec : ∀ n, (j (q n) >>= fun m => (Nat.div2 m : ℕ)) = h n) :
    RecursiveIn {j} h := by
  have hj : RecursiveIn {j} j := RecursiveIn.oracle j (by simp)
  have hdiv2 : RecursiveIn {j} (fun n : ℕ => (Nat.div2 n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using (Primrec.nat_div2 : Primrec Nat.div2)
  have hquery : RecursiveIn {j} (fun n => j (q n)) :=
    RecursiveIn.of_eq (RecursiveIn.comp hj hq) fun n => by simp [Part.bind_some]
  exact RecursiveIn.of_eq (RecursiveIn.comp hdiv2 hquery) hdec

lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
  -- compute `f n` from the oracle `(f ⊕ g)` by querying at `2*n` and decoding by `div2`
  have hdouble : RecursiveIn {f ⊕ g} (fun n : ℕ => (2 * n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
  refine le_join_aux (f ⊕ g) f (fun n => 2 * n) hdouble fun n => ?_
  have hcomp : (Nat.div2 ∘ fun y : ℕ => 2 * y) = (fun y => y) := by
    funext y; simp [Function.comp, Nat.div2_bit0]
  simpa [turingJoin, Part.bind_some_eq_map, Part.map_map, Function.comp, hcomp] using
    (Part.map_id' (f := fun y : ℕ => y) (fun y => rfl) (f n))

lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by
  -- compute `g n` from the oracle `(f ⊕ g)` by querying at `2*n+1` and decoding by `div2`
  have hdouble1 : RecursiveIn {f ⊕ g} (fun n : ℕ => (2 * n + 1 : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1))
  refine le_join_aux (f ⊕ g) g (fun n => 2 * n + 1) hdouble1 fun n => ?_
  have hcomp : (Nat.div2 ∘ fun y : ℕ => 2 * y + 1) = (fun y => y) := by
    funext y; simp [Function.comp]
  simpa [turingJoin, Part.bind_some_eq_map, Part.map_map, Function.comp, hcomp] using
    (Part.map_id' (f := fun y : ℕ => y) (fun y => rfl) (g n))

theorem RecursiveIn_cond_const {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (k : ℕ) :
    RecursiveIn O (fun n => bif (c n) then f n else (Part.some k)) := by
  classical
  have hid : RecursiveIn O (fun n : ℕ => n) :=
    recursiveIn_of_partrec (O := O) ((Partrec.nat_iff).1 (Computable.id.partrec))
  have hcode : RecursiveIn O (fun n : ℕ => encode (c n)) := by
    have hcomp : Computable (fun n : ℕ => encode (c n)) := (Computable.encode.comp hc)
    exact recursiveIn_of_partrec (O := O) ((Partrec.nat_iff).1 hcomp.partrec)
  let pairFn : ℕ →. ℕ := fun n =>
    Nat.pair <$> (show Part ℕ from n) <*> (show Part ℕ from encode (c n))
  have hpair : RecursiveIn O pairFn := by
    simpa [pairFn] using (RecursiveIn.pair hid hcode)
  let base : ℕ →. ℕ := fun _ : ℕ => (k : ℕ)
  have hbase : RecursiveIn O base :=
    recursiveIn_of_partrec (O := O) ((Partrec.nat_iff).1 (Computable.partrec (Computable.const k)))
  let step : ℕ →. ℕ := fun p : ℕ => (Nat.unpair p).1 >>= f
  have hstep : RecursiveIn O step := by
    simpa [step] using (RecursiveIn.comp hf RecursiveIn.left)
  let precFn : ℕ →. ℕ :=
    fun p : ℕ =>
      let (a, n) := Nat.unpair p
      n.rec (base a) (fun y IH => do
        let i ← IH
        step (Nat.pair a (Nat.pair y i)))
  have hprec : RecursiveIn O precFn := by
    simpa [precFn] using (RecursiveIn.prec hbase hstep)
  let mainFn : ℕ →. ℕ := fun n => pairFn n >>= precFn
  have hmain : RecursiveIn O mainFn := by
    simpa [mainFn] using (RecursiveIn.comp hprec hpair)
  have hEq : mainFn = (fun n => bif (c n) then f n else Part.some k) := by
    funext n
    cases h : c n <;>
      simp [mainFn, pairFn, precFn, base, step, h, Seq.seq, Nat.unpair_pair]
  simpa [hEq] using hmain


/-- The equality test on pairs: returns `0` if the two components are equal and `1` otherwise. -/
def eq01 : ℕ →. ℕ := fun p => Part.some (if (Nat.unpair p).1 = (Nat.unpair p).2 then 0 else 1)

theorem eq01_natPartrec : Nat.Partrec eq01 := by
  have hcomp :
      Computable (fun p : ℕ => if (Nat.unpair p).1 = (Nat.unpair p).2 then (0 : ℕ) else 1) := by
    have hEq : Computable (fun q : ℕ × ℕ => decide (q.1 = q.2)) := by
      have hprim : Primrec (fun q : ℕ × ℕ => decide (q.1 = q.2)) := by
        simpa using
          (PrimrecPred.decide (p := fun q : ℕ × ℕ => q.1 = q.2)
            (Primrec.eq : PrimrecPred fun q : ℕ × ℕ => q.1 = q.2))
      exact Primrec.to_comp hprim
    have hdec : Computable (fun p : ℕ => decide ((Nat.unpair p).1 = (Nat.unpair p).2)) :=
      Computable.comp hEq Computable.unpair
    have hcond :
        Computable
          (fun p : ℕ => cond (decide ((Nat.unpair p).1 = (Nat.unpair p).2)) (0 : ℕ) 1) := by
      have h0 : Computable (fun _ : ℕ => (0 : ℕ)) := Computable.const 0
      have h1 : Computable (fun _ : ℕ => (1 : ℕ)) := Computable.const 1
      simpa using
        (Computable.cond (c := fun p : ℕ => decide ((Nat.unpair p).1 = (Nat.unpair p).2))
          (f := fun _ : ℕ => (0 : ℕ)) (g := fun _ : ℕ => (1 : ℕ)) hdec h0 h1)
    refine Computable.of_eq hcond ?_
    intro p
    by_cases h : (Nat.unpair p).1 = (Nat.unpair p).2 <;> simp [h]
  have hpart : _root_.Partrec eq01 := by
    refine _root_.Partrec.of_eq (Computable.partrec hcomp) ?_
    intro p
    by_cases h : (Nat.unpair p).1 = (Nat.unpair p).2 <;> simp [eq01, h]
  exact (Partrec.nat_iff).1 hpart

theorem eq01_recursiveIn (O : Set (ℕ →. ℕ)) : RecursiveIn O eq01 :=
  recursiveIn_of_partrec (O := O) eq01_natPartrec

theorem eq01_rfind_none :
    Nat.rfind
        (fun k =>
          (fun m : ℕ => m = 0) <$>
            ((Nat.pair <$> (Part.none : Part ℕ) <*> Part.some k) >>= eq01)) =
      (Part.none : Part ℕ) := by
  classical
  refine Nat.rfind_zero_none
    (p := fun k => (fun m : ℕ => m = 0) <$>
      ((Nat.pair <$> (Part.none : Part ℕ) <*> Part.some k) >>= eq01)) ?_
  simp [Seq.seq]

theorem eq01_rfind_some (n : ℕ) :
    Nat.rfind
        (fun k =>
          (fun m : ℕ => m = 0) <$>
            ((Nat.pair <$> (Part.some n : Part ℕ) <*> Part.some k) >>= eq01)) =
      Part.some n := by
  classical
  refine Part.mem_right_unique ?_ (Part.mem_some n)
  refine (Nat.mem_rfind).2 ?_
  constructor
  · simp [eq01, Nat.unpair_pair, Seq.seq]
  · intro m hm
    have hne : n ≠ m := Nat.ne_of_gt hm
    simp [eq01, Nat.unpair_pair, Seq.seq, hne]

theorem eq01_rfind (v : Part ℕ) :
    Nat.rfind
        (fun k => (fun m : ℕ => m = 0) <$> ((Nat.pair <$> v <*> Part.some k) >>= eq01)) = v := by
  refine Part.induction_on v ?_ ?_
  · simpa using eq01_rfind_none
  · intro n; simpa using eq01_rfind_some (n := n)

/-- The comparison gadget `p ↦ eq01 (pair (h p.1) p.2)` is recursive in `O` whenever `h` is. -/
private lemma eqCmp_recursiveIn {O : Set (ℕ →. ℕ)} {h : ℕ →. ℕ} (hh : RecursiveIn O h) :
    RecursiveIn O (fun p => (Nat.pair <$>
        ((fun n : ℕ => (Nat.unpair n).1) p >>= h) <*>
        (fun n : ℕ => (Nat.unpair n).2) p) >>= eq01) :=
  RecursiveIn.comp (eq01_recursiveIn O)
    (RecursiveIn.pair (RecursiveIn.comp hh RecursiveIn.left) RecursiveIn.right)

theorem RecursiveIn_cond_core_rfind {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    ∃ cmp : ℕ →. ℕ,
      RecursiveIn O cmp ∧
        (fun n => Nat.rfind (fun k => (fun m => m = 0) <$> cmp (Nat.pair n k))) =
          (fun n => cond (c n) (f n) (g n)) := by
  let eqF : ℕ →. ℕ := fun p =>
    (Nat.pair <$>
        ((fun n : ℕ => (Nat.unpair n).1) p >>= f) <*>
        (fun n : ℕ => (Nat.unpair n).2) p) >>= eq01
  let eqG : ℕ →. ℕ := fun p =>
    (Nat.pair <$>
        ((fun n : ℕ => (Nat.unpair n).1) p >>= g) <*>
        (fun n : ℕ => (Nat.unpair n).2) p) >>= eq01
  let c1 : ℕ → Bool := fun p => c (Nat.unpair p).1
  let c2 : ℕ → Bool := fun p => !c (Nat.unpair p).1
  have hc1 : Computable c1 := by
    have hleft : Computable (fun p : ℕ => (Nat.unpair p).1) :=
      Computable.fst.comp Computable.unpair
    simpa [c1] using hc.comp hleft
  have hc2 : Computable c2 := by
    have hnot : Computable not := Primrec.not.to_comp
    simpa [c2] using hnot.comp hc1
  have heqF : RecursiveIn O eqF := eqCmp_recursiveIn hf
  have heqG : RecursiveIn O eqG := eqCmp_recursiveIn hg
  let t1 : ℕ →. ℕ := fun p => bif c1 p then eqF p else Part.some 1
  let t2 : ℕ →. ℕ := fun p => bif c2 p then eqG p else Part.some 1
  have ht1 : RecursiveIn O t1 := by
    simpa [t1] using (RecursiveIn_cond_const (O := O) (c := c1) (f := eqF) hc1 heqF 1)
  have ht2 : RecursiveIn O t2 := by
    simpa [t2] using (RecursiveIn_cond_const (O := O) (c := c2) (f := eqG) hc2 heqG 1)
  let mulPair : ℕ →. ℕ := (Nat.unpaired (fun a b : ℕ => a * b) : ℕ → ℕ)
  have hmul : RecursiveIn O mulPair := by
    have hpart : Nat.Partrec (mulPair : ℕ →. ℕ) := by
      simpa [mulPair] using (Nat.Partrec.of_primrec (Nat.Primrec.mul))
    exact recursiveIn_of_partrec (O := O) hpart
  let cmp : ℕ →. ℕ := fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair
  have hcmp : RecursiveIn O cmp := by
    have hpair : RecursiveIn O (fun p => Nat.pair <$> t1 p <*> t2 p) :=
      RecursiveIn.pair ht1 ht2
    have : RecursiveIn O (fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair) :=
      RecursiveIn.comp hmul hpair
    simpa [cmp] using this
  refine ⟨cmp, hcmp, ?_⟩
  funext n
  let φ : ℕ → Bool := fun m => decide (m = 0)
  cases hn : c n with
  | true =>
      simp only [Part.map_eq_map, cond]
      have hpred :
          (fun k => Part.map φ (cmp (Nat.pair n k))) =
            (fun k => Part.map φ (((Nat.pair <$> f n <*> Part.some k) >>= eq01))) := by
        funext k
        have hcmpk : cmp (Nat.pair n k) = ((Nat.pair <$> f n <*> Part.some k) >>= eq01) := by
          simp [cmp, t1, t2, c1, c2, eqF, eqG, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
            Seq.seq, Part.bind_assoc, Part.bind_some, Part.bind_some_right]
        simp [hcmpk]
      rw [hpred]
      exact eq01_rfind (v := f n)
  | false =>
      simp only [Part.map_eq_map, cond]
      have hpred :
          (fun k => Part.map φ (cmp (Nat.pair n k))) =
            (fun k => Part.map φ (((Nat.pair <$> g n <*> Part.some k) >>= eq01))) := by
        funext k
        have hcmpk : cmp (Nat.pair n k) = ((Nat.pair <$> g n <*> Part.some k) >>= eq01) := by
          simp [cmp, t1, t2, c1, c2, eqF, eqG, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
            Seq.seq, Part.bind_assoc, Part.bind_some, Part.bind_some_right]
        simp [hcmpk]
      rw [hpred]
      exact eq01_rfind (v := g n)

theorem RecursiveIn_cond {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O (fun n => cond (c n) (f n) (g n)) := by
  rcases RecursiveIn_cond_core_rfind (O := O) (c := c) (f := f) (g := g) hc hf hg with
    ⟨cmp, hcmp, hEq⟩
  have hr : RecursiveIn O
      (fun n => Nat.rfind (fun k => (fun m => m = 0) <$> cmp (Nat.pair n k))) :=
    RecursiveIn.rfind hcmp
  refine RecursiveIn.of_eq hr ?_
  intro n
  simpa using congrArg (fun h => h n) hEq

theorem turingJoin_recursiveIn_pair (f g : ℕ →. ℕ) :
    RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) := by
  let O : Set (ℕ →. ℕ) := ({f, g} : Set (ℕ →. ℕ))
  let payload : ℕ →. ℕ := fun n => (Nat.div2 n : ℕ)
  let dbl : ℕ →. ℕ := fun n => (2 * n : ℕ)
  let dbl1 : ℕ →. ℕ := fun n => (2 * n + 1 : ℕ)
  have hpayload : RecursiveIn O payload := by
    refine RecursiveIn.of_primrec (O := O) ?_
    exact (Primrec.nat_iff.1 (by simpa using (Primrec.nat_div2 : Primrec Nat.div2)))
  have hdbl : RecursiveIn O dbl := by
    refine RecursiveIn.of_primrec (O := O) ?_
    have hprim : Primrec (fun n : ℕ => 2 * n) :=
      Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
    exact (Primrec.nat_iff.1 hprim)
  have hdbl1 : RecursiveIn O dbl1 := by
    refine RecursiveIn.of_primrec (O := O) ?_
    have hprim : Primrec (fun n : ℕ => 2 * n + 1) :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
        (Primrec.const 1)
    exact (Primrec.nat_iff.1 hprim)
  have hfO : RecursiveIn O f := RecursiveIn.oracle f (by simp [O])
  have hgO : RecursiveIn O g := RecursiveIn.oracle g (by simp [O])
  let evenBranch : ℕ →. ℕ := fun n => (payload n >>= f) >>= dbl
  let oddBranch : ℕ →. ℕ := fun n => (payload n >>= g) >>= dbl1
  have heven : RecursiveIn O evenBranch := by
    have h1 : RecursiveIn O (fun n => payload n >>= f) := RecursiveIn.comp hfO hpayload
    have h2 : RecursiveIn O (fun n => (payload n >>= f) >>= dbl) := RecursiveIn.comp hdbl h1
    simpa [evenBranch] using h2
  have hodd : RecursiveIn O oddBranch := by
    have h1 : RecursiveIn O (fun n => payload n >>= g) := RecursiveIn.comp hgO hpayload
    have h2 : RecursiveIn O (fun n => (payload n >>= g) >>= dbl1) := RecursiveIn.comp hdbl1 h1
    simpa [oddBranch] using h2
  have hc : Computable Nat.bodd := by
    simpa using (Computable.nat_bodd : Computable Nat.bodd)
  have hcond :
      RecursiveIn O (fun n => cond (Nat.bodd n) (oddBranch n) (evenBranch n)) :=
    RecursiveIn_cond (O := O) (c := Nat.bodd) (f := oddBranch) (g := evenBranch) hc hodd heven
  refine (RecursiveIn.of_eq (O := O) hcond ?_)
  intro n
  by_cases hbn : Nat.bodd n <;>
    simp [turingJoin, payload, dbl, dbl1, evenBranch, oddBranch, hbn, Part.bind_some_eq_map]


theorem join_le (f g h : ℕ →. ℕ) (hf : TuringReducible f h) (hg : TuringReducible g h) :
    TuringReducible (f ⊕ g) h := by
  have hj : RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) := turingJoin_recursiveIn_pair f g
  have hO : ∀ k, k ∈ ({f, g} : Set (ℕ →. ℕ)) →
      RecursiveIn ({h} : Set (ℕ →. ℕ)) k := by
    intro k hk
    have hk' : k = f ∨ k = g := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
    rcases hk' with hkf | hkg
    · simpa [hkf] using hf
    · simpa [hkg] using hg
  exact RecursiveIn_subst (O := ({f, g} : Set (ℕ →. ℕ))) (O' := ({h} : Set (ℕ →. ℕ)))
    (f := (f ⊕ g)) hj hO

/-!
## Semilattice Structure on Turing Degrees

We show that `turingJoin` respects Turing equivalence and lifts to a supremum operation
on `TuringDegree`, making it a `SemilatticeSup`.
-/

namespace TuringDegree

/-- The Turing join respects Turing reducibility: if `f ≤ᵀ f'` and `g ≤ᵀ g'`,
then `f ⊕ g ≤ᵀ f' ⊕ g'`. -/
theorem join_mono {f f' g g' : ℕ →. ℕ} (hf : f ≤ᵀ f') (hg : g ≤ᵀ g') :
    (f ⊕ g) ≤ᵀ (f' ⊕ g') := by
  have hf' : f ≤ᵀ (f' ⊕ g') := hf.trans (left_le_join f' g')
  have hg' : g ≤ᵀ (f' ⊕ g') := hg.trans (right_le_join f' g')
  exact join_le f g (f' ⊕ g') hf' hg'

/-- The Turing join respects Turing equivalence. -/
theorem join_congr {f f' g g' : ℕ →. ℕ} (hf : f ≡ᵀ f') (hg : g ≡ᵀ g') :
    (f ⊕ g) ≡ᵀ (f' ⊕ g') :=
  ⟨join_mono hf.1 hg.1, join_mono hf.2 hg.2⟩

/-- The supremum operation on Turing degrees, induced by the Turing join. -/
def sup : TuringDegree → TuringDegree → TuringDegree :=
  Quotient.lift₂
    (fun f g => toAntisymmetrization TuringReducible (f ⊕ g))
    (fun _ _ _ _ hf hg => Quotient.sound (join_congr hf hg))

theorem sup_mk (f g : ℕ →. ℕ) :
    TuringDegree.sup (toAntisymmetrization TuringReducible f)
        (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

theorem le_sup_left (a b : TuringDegree) : a ≤ TuringDegree.sup a b := by
  induction a using Quotient.inductionOn'
  induction b using Quotient.inductionOn'
  exact left_le_join _ _

theorem le_sup_right (a b : TuringDegree) : b ≤ TuringDegree.sup a b := by
  induction a using Quotient.inductionOn'
  induction b using Quotient.inductionOn'
  exact right_le_join _ _

theorem sup_le {a b c : TuringDegree} (ha : a ≤ c) (hb : b ≤ c) :
    TuringDegree.sup a b ≤ c := by
  induction a using Quotient.inductionOn'
  induction b using Quotient.inductionOn'
  induction c using Quotient.inductionOn'
  exact join_le _ _ _ ha hb

instance instSemilatticeSup : SemilatticeSup TuringDegree where
  sup := sup
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le _ _ _ := sup_le

/-- The sup on Turing degrees agrees with the Turing join on representatives. -/
@[simp]
lemma sup_def (f g : ℕ →. ℕ) :
    (toAntisymmetrization TuringReducible f) ⊔ (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

end TuringDegree

end Computability
