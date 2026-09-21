/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Defs
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.FstBlock
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.SndBlock
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Cat
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.ConsBit
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Reorder
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Vec
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Algebra
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Encoding
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.StepAlgebra
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Simulate
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.IterateLayout
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Iterate
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.TakeLen
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Reverse
import LeanPool.BeyondBethe.Complexitylib.Classes.P.UnaryLength
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.MulLen
import LeanPool.BeyondBethe.Complexitylib.Classes.P.NormalForm
import LeanPool.BeyondBethe.Complexitylib.Classes.P.Composition
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.HeadFlag
import LeanPool.BeyondBethe.Complexitylib.Classes.P.PairWithInput

/-!
# Cobham's characterization of FP — proof internals

The assembly of `CobhamFP = FP` (`Complexitylib.Classes.P.Cobham`). Not meant
for human review of the mathematics — the surface file carries the auditable
statements; the type checker carries this.

The machines are in sibling modules (`Internal.BlockScan`, `Internal.Cat`,
`Internal.ConsBit`, `Internal.Reorder`, `Internal.MulLen`, `Internal.Iterate`),
the algebra toolkit in `Internal.Algebra`, and the interpreter of the
completeness direction in `Internal.Encoding`, `Internal.StepAlgebra`,
`Internal.Extract` and `Internal.Simulate`. What remains here is the soundness
induction and the `boundedRec` loop.

## Contents

- the six constructor cases `fpn_empty`, `fpn_proj`, `fpn_bit`, `fpn_smash`,
  `fpn_comp`, `fpn_boundedRec`, and the induction `cobham_imp_FPn` over them;
- the `FP` closure lemmas they need: `pairFn_mem_FP`, `appendFn_mem_FP`,
  `selectHeadFn_mem_FP` (branching on a bit, via `Complexity.headFlag`),
  `takeLenFn_mem_FP`, `assembleVec_mem_FP`;
- the `boundedRec` loop: `recNotation_eq_foldr`, `recFold_eq_recNotation`,
  `recFoldClamp_eq_recFold`, `loopStep_iterate` and `recFoldClamp_mem_FP`, on top
  of `iterate_mem_FP`;
- the rulers `exists_ruler` and `exists_exact_ruler` that carry the loop's width
  clamp as data.
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-! ## The canonical tuple encoding is in the algebra -/

/-- The nested tuple encoding is a Cobham function at every fixed arity. -/
theorem encodeVec_mem_internal {n : ℕ} : Cobham (@encodeVec n) := by
  induction n with
  | zero =>
      exact Cobham.empty.of_eq fun v => by simp
  | succ n ih =>
      have htail : Cobham fun v : Fin (n + 1) → List Bool => encodeVec (Fin.tail v) :=
        (Cobham.comp ih fun i : Fin n => Cobham.proj i.succ).of_eq fun v => rfl
      exact (comp₂ pairing htail (Cobham.proj 0)).of_eq fun v => by
        rw [encodeVec_succ]
        rfl

/-! ## Soundness: `Cobham f → FPn f`, constructor by constructor -/

/-- `empty` case: the constant empty function is `FPn` at every arity, witnessed
by `const_nil_mem_FP`. -/
theorem fpn_empty {n : ℕ} : FPn (fun _ : Fin n → List Bool => ([] : List Bool)) :=
  ⟨fun _ => [], const_nil_mem_FP, fun _ => rfl⟩

/-- `proj` case: extracting the `i`-th component of an encoded vector is `FP`.

The extraction is `sndBlock` after `i`-fold `fstBlock`: peel `i` leading blocks to
reach the encoding of components `i, i+1, …`, then read its head with `sndBlock`.
Proved here by induction on the arity; each atomic step is `FP`
(`fstBlock_mem_FP`, `sndBlock_mem_FP`) and `FP` is closed under composition
(`mem_FP_comp`), so only those two machine lemmas remain open. -/
theorem fpn_proj {n : ℕ} (i : Fin n) : FPn (fun v : Fin n → List Bool => v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          exact ⟨sndBlock, sndBlock_mem_FP, fun v => sndBlock_encodeVec_succ v⟩
      | succ j =>
          obtain ⟨g, hg, hgf⟩ := ih j
          refine ⟨g ∘ fstBlock, mem_FP_comp fstBlock_mem_FP hg, fun v => ?_⟩
          show g (fstBlock (encodeVec v)) = v j.succ
          rw [fstBlock_encodeVec_succ, hgf]
          rfl

/-- `bit` case: prepending a fixed bit is `FPn` at arity one. On the arity-one
encoding `encodeVec ![x] = pair [] x`, the head component `x` is `sndBlock`, so the
witness is `(b :: ·) ∘ sndBlock`; both factors are `FP`. -/
theorem fpn_bit (b : Bool) :
    FPn (fun v : Fin 1 → List Bool => b :: v 0) := by
  refine ⟨(fun x => b :: x) ∘ sndBlock,
    mem_FP_comp sndBlock_mem_FP (cons_mem_FP b), fun v => ?_⟩
  show b :: sndBlock (encodeVec v) = b :: v 0
  rw [sndBlock_encodeVec_succ]

/-- Pairing two `FP` functions of the same input is `FP`.

Built without a two-output machine: `mem_FP_pairWithInput` gives the nested triple
`z ↦ pair (a z) (pair (b z) z)` (pairing each computed value against the raw
input, then again), and the self-contained `reorder` drops the trailing input
copy to leave `pair (a z) (b z)`. This is what lets `fpn_comp` avoid a bespoke
tuple-assembly machine. -/
theorem pairFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => pair (a z) (b z)) ∈ FP := by
  have h1 : (fun z => pair (b z) z) ∈ FP := mem_FP_pairWithInput hb
  have h2 : (fun w => pair (a (sndBlock w)) w) ∈ FP :=
    mem_FP_pairWithInput (mem_FP_comp sndBlock_mem_FP ha)
  have h12 := mem_FP_comp h1 h2
  have heq : ((fun w => pair (a (sndBlock w)) w) ∘ fun z => pair (b z) z)
      = fun z => pair (a z) (pair (b z) z) := by
    funext z; simp [Function.comp, sndBlock_pair]
  rw [heq] at h12
  have hr := mem_FP_comp h12 reorder_mem_FP
  have heq2 : (reorder ∘ fun z => pair (a z) (pair (b z) z))
      = fun z => pair (a z) (b z) := by
    funext z; simp [Function.comp, reorder_pair_pair]
  rwa [heq2] at hr

/-- **`FP` is closed under concatenation.** -/
theorem appendFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => a z ++ b z) ∈ FP := by
  have h := mem_FP_comp (pairFn_mem_FP ha hb) catBlocks_mem_FP
  have heq : (catBlocks ∘ fun z => pair (a z) (b z)) = fun z => a z ++ b z := by
    funext z
    simp [Function.comp]
  rwa [heq] at h

/-- Emitting `|a z| · |b z|` copies of `false` is `FP` when `a, b` are. This
zero-filled ruler is an internal length-arithmetic helper, not Cobham's public
all-one smash. It is built as the self-contained `mulUnpair` (see
`Complexitylib.Classes.P.Cobham.Internal.MulLen`) after `pairFn a b`. -/
theorem mulLenFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => List.replicate ((a z).length * (b z).length) false) ∈ FP := by
  have hc := mem_FP_comp (pairFn_mem_FP ha hb) mulUnpair_mem_FP
  have heq : (mulUnpair ∘ fun z => pair (a z) (b z))
      = fun z => List.replicate ((a z).length * (b z).length) false := by
    funext z; simp [Function.comp, mulUnpair_pair]
  rwa [heq] at hc

/-- Truncating one `FP` value to another's length. -/
theorem takeLenFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => (b z).take (a z).length) ∈ FP := by
  have hc := mem_FP_comp (pairFn_mem_FP ha hb) takeLen_mem_FP
  have heq : (takeLen ∘ fun z => pair (a z) (b z))
      = fun z => (b z).take (a z).length := by
    funext z; simp [Function.comp, takeLen_pair]
  rwa [heq] at hc

/-- Select `x` or `y` according to the leading bit of `s`; nothing when `s` is
empty. This is the only shape of value-dependent branching the algebra's loop
needs, and `Complexity.headFlag` is what makes it expressible. -/
def selectHead (s x y : List Bool) : List Bool :=
  if s.head? = some true then x else if s.head? = some false then y else []

/-- **Selection is masking.** Exactly one of the two masks is full width, so the
concatenation returns exactly one branch. -/
theorem selectHead_eq (s x y : List Bool) :
    selectHead s x y = x.take ((headFlag true s).length * x.length)
      ++ y.take ((headFlag false s).length * y.length) := by
  rw [selectHead, headFlag, headFlag]
  rcases hs : s.head? with _ | a
  · simp
  · cases a <;> simp

/-- **Selecting between two `FP` values by a bit is `FP`.** -/
theorem selectHeadFn_mem_FP {f a b : List Bool → List Bool}
    (hf : f ∈ FP) (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => selectHead (f z) (a z) (b z)) ∈ FP := by
  have hflag : ∀ t : Bool, (fun z => headFlag t (f z)) ∈ FP := fun t => by
    have := mem_FP_comp hf (headFlag_mem_FP t)
    simpa [Function.comp] using this
  have hx : (fun z => (a z).take ((headFlag true (f z)).length * (a z).length)) ∈ FP := by
    have := takeLenFn_mem_FP (mulLenFn_mem_FP (hflag true) ha) ha
    simpa using this
  have hy : (fun z => (b z).take ((headFlag false (f z)).length * (b z).length)) ∈ FP := by
    have := takeLenFn_mem_FP (mulLenFn_mem_FP (hflag false) hb) hb
    simpa using this
  have h := appendFn_mem_FP hx hy
  have heq : (fun z => (a z).take ((headFlag true (f z)).length * (a z).length)
      ++ (b z).take ((headFlag false (f z)).length * (b z).length))
      = fun z => selectHead (f z) (a z) (b z) := by
    funext z; rw [selectHead_eq]
  rwa [heq] at h

/-- `smash` case: the smash function is `FPn`. On `encodeVec ![x, y]` the two
components are `sndBlock` and `sndBlock ∘ fstBlock`; `smash x y` is
`|x| · |y|` copies of `true`, so the witness first computes a zero-filled ruler
with `mulLenFn_mem_FP` and then applies `unaryLength_mem_FP`. -/
theorem fpn_smash :
    FPn (fun v : Fin 2 → List Bool => Complexity.smash (v 0) (v 1)) := by
  refine ⟨fun z =>
      List.replicate ((sndBlock z).length * (sndBlock (fstBlock z)).length) true,
    ?_, fun v => ?_⟩
  · have hmul :=
      mulLenFn_mem_FP sndBlock_mem_FP (mem_FP_comp fstBlock_mem_FP sndBlock_mem_FP)
    have h := mem_FP_comp hmul unaryLength_mem_FP
    have heq : (fun z =>
        List.replicate ((sndBlock z).length * (sndBlock (fstBlock z)).length) true) =
        (fun x => List.replicate x.length true) ∘ fun z =>
          List.replicate ((sndBlock z).length * (sndBlock (fstBlock z)).length) false := by
      funext z
      simp [Function.comp]
    rw [heq]
    exact h
  show List.replicate
      ((sndBlock (encodeVec v)).length *
        (sndBlock (fstBlock (encodeVec v))).length) true
    = Complexity.smash (v 0) (v 1)
  rw [sndBlock_encodeVec_succ, fstBlock_encodeVec_succ, sndBlock_encodeVec_succ,
    Complexity.smash]
  rfl

/-- Assembling an encoded vector out of `FP` component functions of a common input
is `FP`. Proved by induction on the arity: the empty vector is the constant `[]`,
and the successor step is one `pairFn_mem_FP`. -/
theorem assembleVec_mem_FP {m : ℕ} (w : Fin m → (List Bool → List Bool))
    (hw : ∀ i, w i ∈ FP) :
    (fun z => encodeVec fun i => w i z) ∈ FP := by
  induction m with
  | zero =>
      have : (fun z : List Bool => encodeVec fun i : Fin 0 => w i z)
          = fun _ => [] := by funext z; rfl
      rw [this]; exact const_nil_mem_FP
  | succ m ih =>
      have htail : (fun z => encodeVec fun i : Fin m => Fin.tail w i z) ∈ FP :=
        ih (Fin.tail w) fun i => hw i.succ
      have h0 : w 0 ∈ FP := hw 0
      have hpair := pairFn_mem_FP htail h0
      have heq : (fun z => encodeVec fun i : Fin (m + 1) => w i z)
          = fun z => pair (encodeVec fun i : Fin m => Fin.tail w i z) (w 0 z) := by
        funext z; rw [encodeVec_succ]; rfl
      rw [heq]; exact hpair

/-- `comp` case: `FPn` is closed under Cobham composition. On `encodeVec v`, each
inner `gs i` is computed by its `FP` witness `G i`, the results are assembled into
`encodeVec (fun i => gs i v)` (`assembleVec_mem_FP`), and the outer `f`'s witness
is applied; `FP` is closed under composition. Rests only on `pairFn_mem_FP`. -/
theorem fpn_comp {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
    {gs : Fin m → (Fin n → List Bool) → List Bool}
    (ihf : FPn f) (ihgs : ∀ i, FPn (gs i)) :
    FPn (fun v => f fun i => gs i v) := by
  obtain ⟨F, hF, hFf⟩ := ihf
  choose G hG hGf using ihgs
  refine ⟨F ∘ fun z => encodeVec fun i => G i z,
    mem_FP_comp (assembleVec_mem_FP G hG) hF, fun v => ?_⟩
  show F (encodeVec fun i => G i (encodeVec v)) = f fun i => gs i v
  have hinner : (fun i => G i (encodeVec v)) = fun i => gs i v := by
    funext i; exact hGf i v
  rw [hinner, hFf]

/-- One step of recursion on notation viewed as a fold operation: extend the
running suffix `p.1` by the bit `b` and update the running recursive value `p.2` by
the bit-selected step function. Folding this over a string with `List.foldr`
reproduces `recNotation` (see `recNotation_eq_foldr`); it is the per-iteration
body a loop machine runs. -/
def recNotationStep {n : ℕ} (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool)
    (w : Fin n → List Bool) (b : Bool) (p : List Bool × List Bool) :
    List Bool × List Bool :=
  (b :: p.1, (bif b then h₁ else h₀) (Fin.cons p.1 (Fin.cons p.2 w)))

/-- The first component of the recursion-on-notation fold accumulates exactly the
bits processed so far — i.e. it rebuilds the input string. -/
theorem recNotationStep_foldr_fst {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool} (s : List Bool)
    (w : Fin n → List Bool) :
    (s.foldr (recNotationStep h₀ h₁ w) ([], g w)).1 = s := by
  induction s with
  | nil => rfl
  | cons b x ih => simp [List.foldr_cons, recNotationStep, ih]

/-- **Recursion on notation is a fold.** `recNotation g h₀ h₁ s w` is the second
component of folding `recNotationStep` over `s` from the empty suffix and base
value `g w`. This reduces the `boundedRec` case to iterating a single step
function over the bits of `s` — exactly what a loop machine computes — and is the
target identity for `fpn_boundedRec`. -/
theorem recNotation_eq_foldr {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) (s : List Bool)
    (w : Fin n → List Bool) :
    recNotation g h₀ h₁ s w =
      (s.foldr (recNotationStep h₀ h₁ w) ([], g w)).2 := by
  induction s with
  | nil => rfl
  | cons b x ih =>
      rw [recNotation_cons, List.foldr_cons]
      simp only [recNotationStep]
      rw [recNotationStep_foldr_fst g x w, ih]

/-! ### The `boundedRec` loop

The `boundedRec` case runs the recursion as a loop on *encoded* arguments:
`recFold A B e W s` threads a running suffix `t` of `s` and the running
accumulator `a` through the argument encoding `pair (pair W a) t`, which is
exactly `encodeVec (Fin.cons t (Fin.cons a w))` when `W = encodeVec w`.

A machine cannot run `recFold` as written: nothing stops the accumulator from
doubling in length at every iteration, so intermediate values would need
exponential space. `recFoldClamp` truncates every intermediate value to a
prescribed width, which makes the loop unconditionally polynomial-time
(`recFoldClamp_mem_FP`); Cobham's limited-recursion side condition is then
exactly what shows the truncation never fires (`recFoldClamp_eq_recFold`). -/

/-- The recursion-on-notation loop on encoded arguments: fold the bit-selected
step functions `A` (bit `false`) and `B` (bit `true`) over `s`, threading the
running suffix and accumulator through the argument encoding. -/
def recFold (A B : List Bool → List Bool) (e W : List Bool) :
    List Bool → List Bool
  | [] => e
  | b :: t => (bif b then B else A) (pair (pair W (recFold A B e W t)) t)

/-- `recFold` with every intermediate value truncated to `bound` bits. This is
the loop a machine can actually run: each iteration's state is length-bounded,
so the whole loop takes polynomial time. -/
def recFoldClamp (A B : List Bool → List Bool) (bound : ℕ) (e W : List Bool) :
    List Bool → List Bool
  | [] => e.take bound
  | b :: t =>
      ((bif b then B else A)
        (pair (pair W (recFoldClamp A B bound e W t)) t)).take bound

/-- A natural-coefficient polynomial is dominated by a single power of `n + 1`
scaled by the sum of its coefficients. -/
private theorem poly_eval_le_pow (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤
      (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * (n + 1) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ p.natDegree := by rw [Finset.mem_range] at hi; omega
  exact Nat.mul_le_mul_left _
    (le_trans (Nat.pow_le_pow_left (by omega) i) (Nat.pow_le_pow_right (by omega) hi'))

/-- An `FP` function whose output is at least `c` bits long, for any constant `c`.
Built by iterating `pair · []`, which doubles the length and adds two. -/
theorem exists_const_ruler (c : ℕ) :
    ∃ K : List Bool → List Bool, K ∈ FP ∧ ∀ z, c ≤ (K z).length := by
  induction c with
  | zero => exact ⟨fun _ => [], const_nil_mem_FP, fun _ => by simp⟩
  | succ c ih =>
      obtain ⟨K, hK, hlen⟩ := ih
      refine ⟨fun z => pair (K z) [], pairFn_mem_FP hK const_nil_mem_FP, fun z => ?_⟩
      have := hlen z
      simp only [pair_length, List.length_nil]
      omega

/-- **Rulers.** For every constant `c` and exponent `d` there is an `FP` function
whose output is at least `c · (|z| + 1) ^ d` bits long. Rulers let the loop of the
`boundedRec` case carry its width clamp as *data* — truncating to a string costs
linear time, whereas truncating to a computed number would not. -/
theorem exists_pow_ruler (c d : ℕ) :
    ∃ R : List Bool → List Bool, R ∈ FP ∧
      ∀ z, c * (z.length + 1) ^ d ≤ (R z).length := by
  induction d with
  | zero =>
      obtain ⟨K, hK, hlen⟩ := exists_const_ruler c
      exact ⟨K, hK, fun z => by simpa using hlen z⟩
  | succ d ih =>
      obtain ⟨R, hR, hlen⟩ := ih
      refine ⟨fun z => List.replicate ((R z).length * (pair [] z).length) false,
        mulLenFn_mem_FP hR pairLeftNil_mem_FP, fun z => ?_⟩
      have hR' := hlen z
      have hL : z.length + 1 ≤ (pair [] z).length := by simp
      calc c * (z.length + 1) ^ (d + 1)
          = (c * (z.length + 1) ^ d) * (z.length + 1) := by ring
        _ ≤ (R z).length * (pair [] z).length := Nat.mul_le_mul hR' hL
        _ = _ := by simp

/-- Every polynomial bound has an `FP` ruler. -/
theorem exists_ruler (p : Polynomial ℕ) :
    ∃ R : List Bool → List Bool, R ∈ FP ∧ ∀ z, p.eval z.length ≤ (R z).length := by
  obtain ⟨R, hR, hlen⟩ :=
    exists_pow_ruler (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) p.natDegree
  exact ⟨R, hR, fun z => le_trans (poly_eval_le_pow p z.length) (hlen z)⟩

/-! ### Exact rulers

`exists_ruler` builds an `FP` string *at least* `p.eval |z|` bits long, which is
all a clamp needs. The loop needs an exact one: the width it truncates to is the
ruler's length, and that has to be the bound the statement names. Exactness comes
from `Complexity.unaryLength_mem_FP` together with the two exact length
arithmetic operations now available — `mulLenFn_mem_FP` multiplies lengths and
`appendFn_mem_FP` adds them. -/

/-- Constants of any width are `FP`. -/
theorem const_replicate_mem_FP (c : ℕ) :
    (fun _ : List Bool => List.replicate c false) ∈ FP := by
  induction c with
  | zero => simpa using const_nil_mem_FP
  | succ c ih =>
      have := mem_FP_comp ih (cons_mem_FP false)
      simpa [Function.comp, List.replicate_succ] using this

/-- A ruler of length exactly `|z| ^ d`. -/
private theorem exists_pow_exact_ruler (d : ℕ) :
    ∃ R : List Bool → List Bool, R ∈ FP ∧ ∀ z, (R z).length = z.length ^ d := by
  induction d with
  | zero => exact ⟨fun _ => List.replicate 1 false, const_replicate_mem_FP 1,
      fun z => by simp⟩
  | succ d ih =>
      obtain ⟨R, hR, hlen⟩ := ih
      refine ⟨fun z => List.replicate ((R z).length * (List.replicate z.length true).length)
        false, mulLenFn_mem_FP hR unaryLength_mem_FP, fun z => ?_⟩
      simp [hlen, pow_succ]

/-- **A ruler of length exactly `p.eval |z|`.** -/
theorem exists_exact_ruler (p : Polynomial ℕ) :
    ∃ R : List Bool → List Bool, R ∈ FP ∧ ∀ z, (R z).length = p.eval z.length := by
  have hsum : ∀ N : ℕ, ∃ R : List Bool → List Bool, R ∈ FP ∧
      ∀ z, (R z).length = ∑ i ∈ Finset.range N, p.coeff i * z.length ^ i := by
    intro N
    induction N with
    | zero => exact ⟨fun _ => [], const_nil_mem_FP, fun z => by simp⟩
    | succ N ih =>
        obtain ⟨R, hR, hlen⟩ := ih
        obtain ⟨S, hS, hSlen⟩ := exists_pow_exact_ruler N
        refine ⟨fun z => R z ++ List.replicate
          ((List.replicate (p.coeff N) false).length * (S z).length) false,
          appendFn_mem_FP hR (mulLenFn_mem_FP (const_replicate_mem_FP _) hS),
          fun z => ?_⟩
        rw [List.length_append, hlen, List.length_replicate, List.length_replicate,
          hSlen, Finset.sum_range_succ]
  obtain ⟨R, hR, hlen⟩ := hsum (p.natDegree + 1)
  exact ⟨R, hR, fun z => by rw [hlen, ← Polynomial.eval_eq_sum_range]⟩

/-! ### The loop as an iteration

`recFoldClamp` is an iteration of a *single* `FP` step function on a packed
state. Writing `s` for `sndBlock z`, the state after `m` iterations is

  `pair (pair R (pair W s)) (pair (s.drop (|s| - m)) (recFoldClamp … (s.drop (|s| - m))))`

so the answer is the accumulator after `|s|` iterations. Every ingredient of the
step is now `FP`: the suffix grows by `Complexity.takeLen` against a ruler one
longer, read off `s.reverse`; the branch on the new leading bit is `selectHead`;
and the clamp is `takeLen` against `R`. -/

/-- One iteration of the clamped loop, on the loop's components. -/
def loopStepOn (A B : List Bool → List Bool) (R W s t a : List Bool) : List Bool :=
  pair (pair R (pair W s))
    (pair ((takeLen (pair (false :: t) s.reverse)).reverse)
      (takeLen (pair R
        (selectHead ((takeLen (pair (false :: t) s.reverse)).reverse)
          (B (pair (pair W a) t)) (A (pair (pair W a) t))))))

/-- One iteration of the clamped loop, on the packed state. -/
def loopStep (A B : List Bool → List Bool) (v : List Bool) : List Bool :=
  loopStepOn A B (fstBlock (fstBlock v)) (fstBlock (sndBlock (fstBlock v)))
    (sndBlock (sndBlock (fstBlock v))) (fstBlock (sndBlock v)) (sndBlock (sndBlock v))

@[simp] theorem loopStep_pair (A B : List Bool → List Bool) (R W s t a : List Bool) :
    loopStep A B (pair (pair R (pair W s)) (pair t a)) = loopStepOn A B R W s t a := by
  simp [loopStep]

/-- **The step is `FP`.** -/
theorem loopStep_mem_FP {A B : List Bool → List Bool} (hA : A ∈ FP) (hB : B ∈ FP) :
    loopStep A B ∈ FP := by
  have hfst : fstBlock ∈ FP := fstBlock_mem_FP
  have hsnd : sndBlock ∈ FP := sndBlock_mem_FP
  have hcomp₁ : ∀ {g : List Bool → List Bool}, g ∈ FP →
      (fun v => fstBlock (g v)) ∈ FP := fun hg => by
    simpa [Function.comp] using mem_FP_comp hg hfst
  have hcomp₂ : ∀ {g : List Bool → List Bool}, g ∈ FP →
      (fun v => sndBlock (g v)) ∈ FP := fun hg => by
    simpa [Function.comp] using mem_FP_comp hg hsnd
  have hP : (fun v : List Bool => fstBlock v) ∈ FP := hfst
  have hR : (fun v : List Bool => fstBlock (fstBlock v)) ∈ FP := hcomp₁ hP
  have hW : (fun v : List Bool => fstBlock (sndBlock (fstBlock v))) ∈ FP :=
    hcomp₁ (hcomp₂ hP)
  have hs : (fun v : List Bool => sndBlock (sndBlock (fstBlock v))) ∈ FP :=
    hcomp₂ (hcomp₂ hP)
  have ht : (fun v : List Bool => fstBlock (sndBlock v)) ∈ FP := hcomp₁ hsnd
  have ha : (fun v : List Bool => sndBlock (sndBlock v)) ∈ FP := hcomp₂ hsnd
  have hrev : ∀ {g : List Bool → List Bool}, g ∈ FP →
      (fun v => (g v).reverse) ∈ FP := fun hg => by
    simpa [Function.comp] using mem_FP_comp hg reverse_mem_FP
  have hcons : (fun v : List Bool => false :: fstBlock (sndBlock v)) ∈ FP := by
    simpa [Function.comp] using mem_FP_comp ht (cons_mem_FP false)
  have ht' : (fun v : List Bool =>
      (takeLen (pair (false :: fstBlock (sndBlock v))
        (sndBlock (sndBlock (fstBlock v))).reverse)).reverse) ∈ FP := by
    refine hrev ?_
    have := takeLenFn_mem_FP hcons (hrev hs)
    simpa [takeLen_pair] using this
  have hX : (fun v : List Bool =>
      pair (pair (fstBlock (sndBlock (fstBlock v))) (sndBlock (sndBlock v)))
        (fstBlock (sndBlock v))) ∈ FP := pairFn_mem_FP (pairFn_mem_FP hW ha) ht
  have hsel := selectHeadFn_mem_FP ht'
    (by simpa [Function.comp] using mem_FP_comp hX hB)
    (by simpa [Function.comp] using mem_FP_comp hX hA)
  have hacc : (fun v : List Bool => takeLen (pair (fstBlock (fstBlock v))
      (selectHead ((takeLen (pair (false :: fstBlock (sndBlock v))
          (sndBlock (sndBlock (fstBlock v))).reverse)).reverse)
        (B (pair (pair (fstBlock (sndBlock (fstBlock v))) (sndBlock (sndBlock v)))
            (fstBlock (sndBlock v))))
        (A (pair (pair (fstBlock (sndBlock (fstBlock v))) (sndBlock (sndBlock v)))
            (fstBlock (sndBlock v))))))) ∈ FP := by
    have := takeLenFn_mem_FP hR hsel
    simpa [takeLen_pair, Function.comp] using this
  have hall := pairFn_mem_FP (pairFn_mem_FP hR (pairFn_mem_FP hW hs))
    (pairFn_mem_FP ht' hacc)
  simpa [loopStep, loopStepOn] using hall

/-- **The loop's invariant.** After `m` iterations the state holds the suffix
`s.drop (|s| - m)` and the clamped fold over it. -/
theorem loopStep_iterate {A B : List Bool → List Bool} (R W s e : List Bool) :
    ∀ m ≤ s.length,
      (loopStep A B)^[m]
          (pair (pair R (pair W s)) (pair [] (e.take R.length)))
        = pair (pair R (pair W s))
            (pair (s.drop (s.length - m))
              (recFoldClamp A B R.length e W (s.drop (s.length - m)))) := by
  intro m
  induction m with
  | zero => intro _; simp [recFoldClamp]
  | succ m ih =>
      intro hm
      rw [Function.iterate_succ_apply', ih (by omega), loopStep_pair, loopStepOn]
      have hlt : s.length - (m + 1) < s.length := by omega
      have hdrop : s.drop (s.length - (m + 1))
          = s[s.length - (m + 1)] :: s.drop (s.length - m) := by
        rw [List.drop_eq_getElem_cons hlt,
          show s.length - (m + 1) + 1 = s.length - m from by omega]
      have hnext : (takeLen (pair (false :: s.drop (s.length - m)) s.reverse)).reverse
          = s.drop (s.length - (m + 1)) := by
        rw [takeLen_pair, List.length_cons, List.length_drop,
          show s.length - (s.length - m) + 1 = s.length - (s.length - (m + 1)) from by omega,
          ← List.reverse_drop, List.reverse_reverse]
      rw [hnext, hdrop, recFoldClamp]
      congr 2
      rw [takeLen_pair, selectHead]
      cases hb : s[s.length - (m + 1)] <;> simp

/-- The clamp really clamps. -/
theorem recFoldClamp_length_le (A B : List Bool → List Bool) (bound : ℕ)
    (e W s : List Bool) : (recFoldClamp A B bound e W s).length ≤ bound := by
  cases s with
  | nil => simp [recFoldClamp]
  | cons b t => simp [recFoldClamp]

/-! ### The loop's step function

`Complexity.iterate_input_mem_FP` supplies a machine that applies an `FP`
function once per bit of its own input, starting from `pair [] x`. The state
below is `pair (pair C v) x`: a counter `C`, the running value `v`, and the
machine's input `x` kept verbatim. Keeping `x` is what makes the whole
construction work: the ruler and the width stay readable at every step, and
truncating the new state to `|x|` bounds the state length *globally* — the
machine's contract needs a bound that holds for every input, not just for the
well-formed ones. -/

/-- A flag whose leading bit is `true` exactly when `s` is empty — the one test
`Complexity.selectHead` cannot make directly. -/
def emptyFlag (s : List Bool) : List Bool :=
  headFlag true s ++ headFlag false s ++ [true]

@[simp] theorem emptyFlag_nil : emptyFlag [] = [true] := rfl

theorem emptyFlag_head_cons (b : Bool) (t : List Bool) :
    (emptyFlag (b :: t)).head? = some false := by
  cases b <;> rfl

theorem selectHead_emptyFlag_nil (x y : List Bool) : selectHead (emptyFlag []) x y = x := by
  rw [emptyFlag_nil, selectHead,
    ite_eq_left (show ([true] : List Bool).head? = some true from rfl)]

theorem length_take_le_arg (n : ℕ) (l : List Bool) : (l.take n).length ≤ n := by
  rw [List.length_take]; omega

theorem selectHead_emptyFlag_cons (b : Bool) (t x y : List Bool) :
    selectHead (emptyFlag (b :: t)) x y = y := by
  rw [selectHead, ite_eq_right (by rw [emptyFlag_head_cons]; simp),
    ite_eq_left (emptyFlag_head_cons b t)]

theorem selectHead_length_le (s x y : List Bool) :
    (selectHead s x y).length ≤ max x.length y.length := by
  rw [selectHead]
  split
  · exact le_max_left _ _
  · split
    · exact le_max_right _ _
    · simp

/-- The counter of the next iteration: one more mark of the reversed ruler. -/
def nextCounter (w : List Bool) : List Bool :=
  (takeLen (pair (false :: fstBlock (fstBlock w))
    (fstBlock (fstBlock (sndBlock w))))).reverse

/-- The value of the next iteration: the initial value on the first step, then
`F` of the current value until the counter saturates. -/
def nextValue (F : List Bool → List Bool) (w : List Bool) : List Bool :=
  selectHead (emptyFlag (fstBlock (fstBlock w)))
    (sndBlock (sndBlock w))
    (selectHead (nextCounter w) (sndBlock (fstBlock w))
      (takeLen (pair (sndBlock (fstBlock (sndBlock w))) (F (sndBlock (fstBlock w))))))

/-- One iteration of the loop, truncated to the machine's own input length. -/
def iterStep (F : List Bool → List Bool) (w : List Bool) : List Bool :=
  pair (takeLen (pair (sndBlock w) (pair (nextCounter w) (nextValue F w)))) (sndBlock w)

theorem sndBlock_iterStep (F : List Bool → List Bool) (w : List Bool) :
    sndBlock (iterStep F w) = sndBlock w := by
  rw [iterStep, sndBlock_pair]

theorem iterStep_length_le (F : List Bool → List Bool) (w : List Bool) :
    (iterStep F w).length ≤ 3 * (sndBlock w).length + 2 := by
  rw [iterStep, pair_length, takeLen_pair]
  have := length_take_le_arg (sndBlock w).length (pair (nextCounter w) (nextValue F w))
  omega

/-- **The state length is globally bounded**: whatever the input, the state
after one or more iterations fits in `3|x| + 2`. -/
theorem iterStep_iterate_length_le (F : List Bool → List Bool) (x : List Bool) :
    ∀ i, ((iterStep F)^[i] (pair [] x)).length ≤ 3 * x.length + 2 := by
  have hsnd : ∀ i, sndBlock ((iterStep F)^[i] (pair [] x)) = x := by
    intro i
    induction i with
    | zero => exact sndBlock_pair [] x
    | succ i ih => rw [Function.iterate_succ_apply', sndBlock_iterStep, ih]
  intro i
  cases i with
  | zero =>
      rw [Function.iterate_zero_apply, pair_length]
      simp
      omega
  | succ i =>
      rw [Function.iterate_succ_apply']
      have := iterStep_length_le F ((iterStep F)^[i] (pair [] x))
      rw [hsnd i] at this
      exact this

theorem emptyFlag_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => emptyFlag (f z)) ∈ FP := by
  have hcst : (fun _ : List Bool => [true]) ∈ FP := by
    simpa [Function.comp] using mem_FP_comp const_nil_mem_FP (cons_mem_FP true)
  have h1 : (fun z => headFlag true (f z)) ∈ FP := by
    simpa [Function.comp] using mem_FP_comp hf (headFlag_mem_FP true)
  have h2 : (fun z => headFlag false (f z)) ∈ FP := by
    simpa [Function.comp] using mem_FP_comp hf (headFlag_mem_FP false)
  exact appendFn_mem_FP (appendFn_mem_FP h1 h2) hcst

theorem nextCounter_mem_FP : nextCounter ∈ FP := by
  have hf : fstBlock ∈ FP := fstBlock_mem_FP
  have hs : sndBlock ∈ FP := sndBlock_mem_FP
  have hc : (fun w => false :: fstBlock (fstBlock w)) ∈ FP := by
    simpa [Function.comp] using
      mem_FP_comp (mem_FP_comp hf hf) (cons_mem_FP false)
  have hk : (fun w => fstBlock (fstBlock (sndBlock w))) ∈ FP := by
    simpa [Function.comp] using mem_FP_comp hs (mem_FP_comp hf hf)
  have := takeLenFn_mem_FP hc hk
  have hrev : (fun w => ((fstBlock (fstBlock (sndBlock w))).take
      (false :: fstBlock (fstBlock w)).length).reverse) ∈ FP := by
    simpa [Function.comp] using mem_FP_comp this reverse_mem_FP
  have heq : (fun w => ((fstBlock (fstBlock (sndBlock w))).take
      (false :: fstBlock (fstBlock w)).length).reverse) = nextCounter := by
    funext w
    rw [nextCounter, takeLen_pair]
  rwa [heq] at hrev

theorem nextValue_mem_FP {F : List Bool → List Bool} (hF : F ∈ FP) :
    nextValue F ∈ FP := by
  have hf : fstBlock ∈ FP := fstBlock_mem_FP
  have hs : sndBlock ∈ FP := sndBlock_mem_FP
  have hC : (fun w => fstBlock (fstBlock w)) ∈ FP := mem_FP_comp hf hf
  have hv : (fun w => sndBlock (fstBlock w)) ∈ FP := mem_FP_comp hf hs
  have hv0 : (fun w => sndBlock (sndBlock w)) ∈ FP := mem_FP_comp hs hs
  have hW : (fun w => sndBlock (fstBlock (sndBlock w))) ∈ FP :=
    mem_FP_comp hs (mem_FP_comp hf hs)
  have hFv : (fun w => F (sndBlock (fstBlock w))) ∈ FP := mem_FP_comp hv hF
  have hclamp : (fun w => takeLen (pair (sndBlock (fstBlock (sndBlock w)))
      (F (sndBlock (fstBlock w))))) ∈ FP := by
    have := takeLenFn_mem_FP hW hFv
    simpa [takeLen_pair] using this
  exact selectHeadFn_mem_FP (emptyFlag_mem_FP hC) hv0
    (selectHeadFn_mem_FP nextCounter_mem_FP hv hclamp)

theorem iterStep_mem_FP {F : List Bool → List Bool} (hF : F ∈ FP) :
    iterStep F ∈ FP := by
  have hs : sndBlock ∈ FP := sndBlock_mem_FP
  have hpair : (fun w => pair (nextCounter w) (nextValue F w)) ∈ FP :=
    pairFn_mem_FP nextCounter_mem_FP (nextValue_mem_FP hF)
  have hclamp : (fun w => takeLen (pair (sndBlock w)
      (pair (nextCounter w) (nextValue F w)))) ∈ FP := by
    have := takeLenFn_mem_FP hs hpair
    simpa [takeLen_pair] using this
  exact pairFn_mem_FP hclamp hs

/-- The value the loop carries after `i` iterations, from the second on. -/
def iterVal (F : List Bool → List Bool) (Krev W v₀ : List Bool) : ℕ → List Bool
  | 0 => v₀
  | i + 1 => selectHead ((Krev.take (i + 2)).reverse) (iterVal F Krev W v₀ i)
      ((F (iterVal F Krev W v₀ i)).take W.length)

theorem iterVal_length_le (F : List Bool → List Bool) (Krev W v₀ : List Bool) :
    ∀ i, (iterVal F Krev W v₀ i).length ≤ max v₀.length W.length := by
  intro i
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
      refine le_trans (selectHead_length_le _ _ _) ?_
      have := length_take_le_arg W.length (F (iterVal F Krev W v₀ i))
      omega

theorem take_succ_min (l : List Bool) (i : ℕ) :
    l.take (min i l.length + 1) = l.take (i + 1) := by
  rcases Nat.lt_or_ge l.length i with h | h
  · rw [min_eq_right (by omega), List.take_of_length_le (by omega),
      List.take_of_length_le (by omega)]
  · rw [min_eq_left h]

/-- **The loop's trajectory.** With the counter growing one mark per iteration
and the state always fitting in the input, the `i+1`-st state is exactly the
counter `(Krev.take (i+1)).reverse` beside the value `iterVal … i`. -/
theorem iterStep_iterate (F : List Bool → List Bool) (Krev W v₀ : List Bool)
    (hK : Krev ≠ [])
    (hfit : ∀ i, (pair ((Krev.take (i + 1)).reverse) (iterVal F Krev W v₀ i)).length
      ≤ (pair (pair Krev W) v₀).length) :
    ∀ i, (iterStep F)^[i + 1] (pair [] (pair (pair Krev W) v₀))
      = pair (pair ((Krev.take (i + 1)).reverse) (iterVal F Krev W v₀ i))
          (pair (pair Krev W) v₀) := by
  intro i
  induction i with
  | zero =>
      rw [Function.iterate_succ_apply', Function.iterate_zero_apply, iterStep, sndBlock_pair]
      rw [show nextCounter (pair [] (pair (pair Krev W) v₀)) = (Krev.take 1).reverse from by
        rw [nextCounter, fstBlock_pair, sndBlock_pair, fstBlock_pair, fstBlock_pair,
          takeLen_pair]
        simp [fstBlock]]
      rw [show nextValue F (pair [] (pair (pair Krev W) v₀)) = v₀ from by
        rw [nextValue, fstBlock_pair, show fstBlock ([] : List Bool) = [] from rfl,
          selectHead_emptyFlag_nil, sndBlock_pair, sndBlock_pair]]
      rw [takeLen_pair]
      show pair ((pair ((Krev.take (0 + 1)).reverse) (iterVal F Krev W v₀ 0)).take
        (pair (pair Krev W) v₀).length) (pair (pair Krev W) v₀) = _
      rw [List.take_of_length_le (hfit 0)]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, iterStep, sndBlock_pair]
      have hlen : ((Krev.take (i + 1)).reverse).length = min (i + 1) Krev.length := by
        simp
      have hC : nextCounter (pair (pair ((Krev.take (i + 1)).reverse)
          (iterVal F Krev W v₀ i)) (pair (pair Krev W) v₀))
          = (Krev.take (i + 2)).reverse := by
        rw [nextCounter, fstBlock_pair, sndBlock_pair, fstBlock_pair, fstBlock_pair,
          fstBlock_pair, takeLen_pair, List.length_cons, hlen, take_succ_min]
      have hne : (Krev.take (i + 1)).reverse ≠ [] := by
        intro hc
        have : Krev.length = 0 := by
          have h0 : ((Krev.take (i + 1)).reverse).length = 0 := by rw [hc]; rfl
          rw [hlen] at h0
          omega
        exact hK (List.eq_nil_of_length_eq_zero this)
      obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil hne
      have hV : nextValue F (pair (pair ((Krev.take (i + 1)).reverse)
          (iterVal F Krev W v₀ i)) (pair (pair Krev W) v₀))
          = iterVal F Krev W v₀ (i + 1) := by
        rw [nextValue, fstBlock_pair, fstBlock_pair, sndBlock_pair, sndBlock_pair,
          fstBlock_pair, sndBlock_pair, hbt, selectHead_emptyFlag_cons, ← hbt, hC,
          takeLen_pair, sndBlock_pair, iterVal]
      rw [hC, hV, takeLen_pair, List.take_of_length_le (hfit (i + 1))]

theorem counter_take_le (a j : ℕ) (h : j ≤ a) :
    (List.replicate a false ++ [true]).take j = List.replicate j false := by
  rw [List.take_append_of_le_length (by simpa using h), List.take_replicate, min_eq_left h]

theorem counter_head_false (a j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a) :
    (((List.replicate a false ++ [true]).take j).reverse).head? = some false := by
  rw [counter_take_le a j h2, List.reverse_replicate]
  cases j with
  | zero => omega
  | succ j => rfl

theorem counter_head_true (a j : ℕ) (h : a + 1 ≤ j) :
    (((List.replicate a false ++ [true]).take j).reverse).head? = some true := by
  rw [List.take_of_length_le (by simp; omega), List.reverse_append, List.reverse_replicate]
  rfl

/-- **The value sequence is the iterate.** While the counter has marks left the
step applies `F`; once it saturates the value stops changing. The clamp is a
no-op because every intermediate value fits in `W`. -/
theorem iterVal_eq_iterate (F : List Bool → List Bool) (W v₀ : List Bool) (M : ℕ)
    (hclamp : ∀ j, j ≤ M → (F^[j] v₀).length ≤ W.length) :
    ∀ i, iterVal F (List.replicate (M + 1) false ++ [true]) W v₀ i = F^[min i M] v₀ := by
  intro i
  induction i with
  | zero => simp [iterVal]
  | succ i ih =>
      rw [iterVal, ih]
      by_cases h : i + 2 ≤ M + 1
      · have hhead := counter_head_false (M + 1) (i + 2) (by omega) h
        rw [selectHead, ite_eq_right (by rw [hhead]; simp), ite_eq_left hhead,
          show min i M = i from by omega, ← Function.iterate_succ_apply' F i v₀,
          List.take_of_length_le (hclamp (i + 1) (by omega)),
          show min (i + 1) M = i + 1 from by omega]
      · have hhead := counter_head_true (M + 1) (i + 2) (by omega)
        rw [selectHead, ite_eq_left hhead, show min i M = M from by omega,
          show min (i + 1) M = M from by omega]

/-- **`FP` is closed under bounded iteration** — the one machine-level fact the
soundness direction needs.

*Construction.* The machine is assembled in
`Complexitylib.Classes.P.Cobham.Internal.Iterate` out of the phase contracts of
`Complexitylib.Classes.P.Cobham.Internal.IterateLayout`; `iterate_input_mem_FP` is its
interface. Three details are worth recording, because three earlier plans died
on them.

*Why resetting scratch is the crux.* `F`'s machine `M` comes from an
existential (`F ∈ FP`), so nothing is known about the shape it leaves its
scratch tapes in. Re-running it needs those tapes genuinely blank, but a
content-driven eraser (`TM.blankWorkTM` scans right to the *first* blank)
under-wipes whenever `M` left a gap — an isolated blank cell with more content
beyond it. `TM.wipeStepTM` therefore writes blank *unconditionally*, and
`Complexity.resetTapesTM` drives it a fixed number of times off a fuel register
that is unrelated to the wiped tapes' content. `TM.reachesIn_work_cells_far`
supplies the bound that makes the fixed count sufficient: a `t`-step run cannot
have touched anything past `head + t`. `Complexity.iterTail` is the resulting
five-phase cleanup, shared by the loop body and the setup; its first two phases
are not bookkeeping either, since `δ_right_of_start` only forces a head
*reading* `▷` to move right, so an arbitrary witness machine may legitimately
*halt* with a head at cell `0`.

*Why the state carries the machine's own input.* `TM.ComputesInTime` quantifies
over *all* inputs, so the loop's contract has to survive malformed ones: the
state is `pair (pair C v) x` with the machine's input `x` kept verbatim, and
every new state is truncated to `|x|` (`iterStep`). That makes
`iterStep_iterate_length_le` — a state-length bound holding for every input,
not just the well-formed ones — available for free, and keeps the ruler and the
width readable at every step. On the intended trajectory the truncation is a
no-op (`iterStep_iterate`).

*How the counter avoids a second fuel value.* The loop runs `|x| + 1` times, one
per bit of the machine's own input (`TM.inputLenRegTM`), which is more
iterations than needed; the surplus is absorbed by a counter that grows one mark
of `Krev = 0^(m+1) 1` per step, whose leading bit turns `true` exactly when the
`m` real applications are done (`counter_head_false`, `counter_head_true`). So
`iterVal` is `F` iterated `min i m` times, and over-iteration is harmless
(`iterVal_eq_iterate`). The wipe width is a *different* register, `p.eval |x|`,
computed by `TM.polyEvalTM` — the state is longer than the input, so `|x|`
alone cannot pay for the reset.

*Time.* Each iteration costs `iterStep`'s own polynomial bound at width
`(width z).length` — which is why `hbound` is a hypothesis — plus the linear
copies and the wipe, and there are `|x| + 1` of them, so the total is polynomial
(`polyBnd_iterBound`). -/
theorem iterate_mem_FP {F init ruler width : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (hwidth : width ∈ FP)
    (hbound : ∀ z, ∀ n ≤ (ruler z).length,
      (F^[n] (init z)).length ≤ (width z).length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  set Krev : List Bool → List Bool :=
    fun z => List.replicate ((ruler z).length + 1) false ++ [true] with hKrev
  have hKrevLen : ∀ z, (Krev z).length = (ruler z).length + 2 := by
    intro z; rw [hKrev]; simp
  have hKrevNe : ∀ z, Krev z ≠ [] := by
    intro z h
    have := hKrevLen z
    rw [h] at this
    simp at this
  -- the machine's input
  set X : List Bool → List Bool :=
    fun z => pair (pair (Krev z) (width z)) (init z) with hX
  have hXlen : ∀ z, (X z).length
      = 4 * (Krev z).length + 2 * (width z).length + (init z).length + 6 := by
    intro z; rw [hX]; simp only [pair_length]; omega
  -- the iterated step is `FP`, and its state length is globally bounded
  have hstep : iterStep F ∈ FP := iterStep_mem_FP hF
  have hr : ∀ (x : List Bool), ∀ i ≤ x.length,
      ((iterStep F)^[i] (pair [] x)).length
        ≤ (3 * Polynomial.X + Polynomial.C 2 : Polynomial ℕ).eval x.length := by
    intro x i _
    have := iterStep_iterate_length_le F x i
    simpa using this
  have hΛ := iterate_input_mem_FP hstep (3 * Polynomial.X + Polynomial.C 2) hr
  -- the wrapper is `FP`, so the composite is
  have hXFP : X ∈ FP := by
    have hone : (fun _ : List Bool => [false]) ∈ FP := by
      simpa [Function.comp] using mem_FP_comp const_nil_mem_FP (cons_mem_FP false)
    have htrue : (fun _ : List Bool => [true]) ∈ FP := by
      simpa [Function.comp] using mem_FP_comp const_nil_mem_FP (cons_mem_FP true)
    have hrl : (fun z => ruler z ++ [false]) ∈ FP := appendFn_mem_FP hruler hone
    have hrep : (fun z => List.replicate ((ruler z).length + 1) false) ∈ FP := by
      have := mulLenFn_mem_FP hrl hone
      simpa using this
    exact pairFn_mem_FP (pairFn_mem_FP (appendFn_mem_FP hrep htrue) hwidth) hinit
  have hXeq : ∀ z, X z = pair (pair (Krev z) (width z)) (init z) := fun z => by rw [hX]
  have heq : (fun z => F^[(ruler z).length] (init z))
      = sndBlock ∘ (fstBlock ∘ ((fun x => (iterStep F)^[x.length + 1] (pair [] x)) ∘ X)) := by
    funext z
    simp only [Function.comp_apply]
    have hfit : ∀ i, (pair (((Krev z).take (i + 1)).reverse)
        (iterVal F (Krev z) (width z) (init z) i)).length ≤ (X z).length := by
      intro i
      have h1 : (((Krev z).take (i + 1)).reverse).length ≤ (Krev z).length := by simp
      have h2 := iterVal_length_le F (Krev z) (width z) (init z) i
      rw [pair_length, hXlen z]
      omega
    have hval : ∀ i, iterVal F (Krev z) (width z) (init z) i
        = F^[min i (ruler z).length] (init z) := by
      have hclamp : ∀ j, j ≤ (ruler z).length → (F^[j] (init z)).length ≤ (width z).length :=
        fun j hj => hbound z j hj
      intro i
      exact iterVal_eq_iterate F (width z) (init z) (ruler z).length hclamp i
    have hiter := iterStep_iterate F (Krev z) (width z) (init z) (hKrevNe z) hfit (X z).length
    have hlarge : (ruler z).length ≤ (X z).length := by
      have := hKrevLen z
      rw [hXlen z]; omega
    rw [hXeq z, hiter, fstBlock_pair, sndBlock_pair, hval, min_eq_right hlarge]
  rw [heq]
  exact mem_FP_comp (mem_FP_comp (mem_FP_comp hXFP hΛ) fstBlock_mem_FP) sndBlock_mem_FP

/-- **The loop of the `boundedRec` case.** `recFoldClamp` is `loopStep` iterated
once per bit of `sndBlock z` (`loopStep_iterate`), started from the packed state
`pair (pair R (pair W s)) (pair [] (e.take |R|))` — with `R` an *exact* ruler for
the clamp (`exists_exact_ruler`) — and read off with two `sndBlock`s. -/
theorem recFoldClamp_mem_FP {A B E : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hE : E ∈ FP) (p : Polynomial ℕ) :
    (fun z => recFoldClamp A B (p.eval z.length) (E z) (fstBlock z) (sndBlock z))
      ∈ FP := by
  obtain ⟨R, hR, hRlen⟩ := exists_exact_ruler p
  have hfst : fstBlock ∈ FP := fstBlock_mem_FP
  have hsnd : sndBlock ∈ FP := sndBlock_mem_FP
  have hP : (fun z => pair (R z) (pair (fstBlock z) (sndBlock z))) ∈ FP :=
    pairFn_mem_FP hR (pairFn_mem_FP hfst hsnd)
  have hinit : (fun z => pair (pair (R z) (pair (fstBlock z) (sndBlock z)))
      (pair [] ((E z).take (R z).length))) ∈ FP :=
    pairFn_mem_FP hP (pairFn_mem_FP const_nil_mem_FP (takeLenFn_mem_FP hR hE))
  have hwidth : (fun z => pair (pair (R z) (pair (fstBlock z) (sndBlock z)))
      (pair (sndBlock z) (R z))) ∈ FP := pairFn_mem_FP hP (pairFn_mem_FP hsnd hR)
  have hbound : ∀ z, ∀ n ≤ (sndBlock z).length,
      ((loopStep A B)^[n] (pair (pair (R z) (pair (fstBlock z) (sndBlock z)))
        (pair [] ((E z).take (R z).length)))).length
        ≤ (pair (pair (R z) (pair (fstBlock z) (sndBlock z)))
            (pair (sndBlock z) (R z))).length := by
    intro z n hn
    rw [loopStep_iterate (A := A) (B := B) (R z) (fstBlock z) (sndBlock z) (E z) n hn]
    have h1 : ((sndBlock z).drop ((sndBlock z).length - n)).length
        ≤ (sndBlock z).length := by simp
    have h2 : (recFoldClamp A B (R z).length (E z) (fstBlock z)
        ((sndBlock z).drop ((sndBlock z).length - n))).length ≤ (R z).length :=
      recFoldClamp_length_le _ _ _ _ _ _
    simp only [pair_length]
    omega
  have hiter := iterate_mem_FP (loopStep_mem_FP hA hB) hinit hsnd hwidth hbound
  have hout := mem_FP_comp hiter (mem_FP_comp hsnd hsnd)
  have heq : ((sndBlock ∘ sndBlock) ∘ fun z =>
      (loopStep A B)^[(sndBlock z).length]
        (pair (pair (R z) (pair (fstBlock z) (sndBlock z)))
          (pair [] ((E z).take (R z).length))))
      = fun z => recFoldClamp A B (p.eval z.length) (E z) (fstBlock z) (sndBlock z) := by
    funext z
    rw [Function.comp, Function.comp,
      loopStep_iterate (A := A) (B := B) (R z) (fstBlock z) (sndBlock z) (E z)
        (sndBlock z).length le_rfl]
    simp [hRlen z]
  rwa [heq] at hout

/-- Truncation is a no-op as soon as every intermediate value already fits. -/
theorem recFoldClamp_eq_recFold {A B : List Bool → List Bool} {bound : ℕ}
    {e W : List Bool} (s : List Bool)
    (hle : ∀ t : List Bool, t.length ≤ s.length →
      (recFold A B e W t).length ≤ bound) :
    recFoldClamp A B bound e W s = recFold A B e W s := by
  induction s with
  | nil =>
      show e.take bound = e
      exact List.take_of_length_le (hle [] (by simp))
  | cons b t ih =>
      have htail : recFoldClamp A B bound e W t = recFold A B e W t :=
        ih fun u hu => hle u (by simp only [List.length_cons]; omega)
      show ((bif b then B else A)
        (pair (pair W (recFoldClamp A B bound e W t)) t)).take bound = _
      rw [htail]
      exact List.take_of_length_le (hle (b :: t) le_rfl)

/-- On encoded arguments the loop computes recursion on notation: `recFold` over
the `FP` witnesses of `g`, `h₀`, `h₁` reproduces `recNotation`. -/
theorem recFold_eq_recNotation {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool}
    {G H₀ H₁ : List Bool → List Bool}
    (hG : ∀ u : Fin n → List Bool, G (encodeVec u) = g u)
    (hH₀ : ∀ u : Fin (n + 2) → List Bool, H₀ (encodeVec u) = h₀ u)
    (hH₁ : ∀ u : Fin (n + 2) → List Bool, H₁ (encodeVec u) = h₁ u)
    (w : Fin n → List Bool) (s : List Bool) :
    recFold H₀ H₁ (G (encodeVec w)) (encodeVec w) s = recNotation g h₀ h₁ s w := by
  -- The encoded step argument is exactly the vector `Fin.cons t (Fin.cons a w)`.
  have henc : ∀ (t a : List Bool),
      pair (pair (encodeVec w) a) t = encodeVec (Fin.cons t (Fin.cons a w)) := by
    intro t a
    rw [encodeVec_succ, encodeVec_succ]
    simp [Fin.tail_cons]
  induction s with
  | nil => exact hG w
  | cons b t ih =>
      show (bif b then H₁ else H₀)
        (pair (pair (encodeVec w) (recFold H₀ H₁ (G (encodeVec w)) (encodeVec w) t)) t)
        = _
      rw [ih, henc, recNotation_cons]
      cases b
      · simp only [Bool.cond_false]; exact hH₀ _
      · simp only [Bool.cond_true]; exact hH₁ _

/-- Every `FP` function has polynomially bounded output length: a time bound is
also an output-length bound (`TM.ComputesInTime.output_length_le`). -/
theorem output_length_poly_of_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ p : Polynomial ℕ, ∀ x, (f x).length ≤ p.eval x.length := by
  obtain ⟨k, tm, p, hcomp⟩ := mem_FP_iff_computesInTime_polynomial.mp hf
  exact ⟨p, fun x => hcomp.output_length_le x⟩

/-- `boundedRec` case: `FPn` is closed under limited recursion on notation.

By `recFold_eq_recNotation` the value is the encoded-argument loop `recFold` run
over the bits of `v 0`. Cobham's limited-recursion side condition `hbound` caps
every intermediate accumulator by `|j (…)|`, which is polynomial in `|encodeVec v|`
(`output_length_poly_of_mem_FP`), so the clamped loop `recFoldClamp` — which a
machine can run in polynomial time (`recFoldClamp_mem_FP`) — never truncates and
therefore agrees with `recFold`. -/
theorem fpn_boundedRec {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool}
    {j : (Fin (n + 1) → List Bool) → List Bool}
    (ihg : FPn g) (ih0 : FPn h₀) (ih1 : FPn h₁) (ihj : FPn j)
    (hbound : ∀ x v, (recNotation g h₀ h₁ x v).length ≤ (j (Fin.cons x v)).length) :
    FPn (fun v : Fin (n + 1) → List Bool =>
      recNotation g h₀ h₁ (v 0) (Fin.tail v)) := by
  obtain ⟨G, hGFP, hG⟩ := ihg
  obtain ⟨H₀, hH0FP, hH0⟩ := ih0
  obtain ⟨H₁, hH1FP, hH1⟩ := ih1
  obtain ⟨J, hJFP, hJ⟩ := ihj
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hJFP
  have hE : (fun z => G (fstBlock z)) ∈ FP := mem_FP_comp fstBlock_mem_FP hGFP
  refine ⟨fun z => recFoldClamp H₀ H₁ (p.eval z.length) (G (fstBlock z)) (fstBlock z)
      (sndBlock z), recFoldClamp_mem_FP hH0FP hH1FP hE p, fun v => ?_⟩
  show recFoldClamp H₀ H₁ (p.eval (encodeVec v).length) (G (fstBlock (encodeVec v)))
      (fstBlock (encodeVec v)) (sndBlock (encodeVec v))
    = recNotation g h₀ h₁ (v 0) (Fin.tail v)
  rw [fstBlock_encodeVec_succ, sndBlock_encodeVec_succ]
  rw [recFoldClamp_eq_recFold (v 0) ?_]
  · exact recFold_eq_recNotation hG hH0 hH1 (Fin.tail v) (v 0)
  · -- Cobham's limited-recursion bound caps every intermediate accumulator.
    intro t ht
    rw [recFold_eq_recNotation hG hH0 hH1 (Fin.tail v) t]
    refine le_trans (hbound t (Fin.tail v)) ?_
    have hJt : (j (Fin.cons t (Fin.tail v))).length
        ≤ p.eval (encodeVec (Fin.cons t (Fin.tail v))).length := by
      rw [← hJ (Fin.cons t (Fin.tail v))]
      exact hp _
    refine le_trans hJt (polynomial_eval_mono_nat p ?_)
    have e1 : (encodeVec (Fin.cons t (Fin.tail v))).length
        = 2 * (encodeVec (Fin.tail v)).length + 2 + t.length := by
      simp [encodeVec_succ, Fin.tail_cons]
    have e2 : (encodeVec v).length
        = 2 * (encodeVec (Fin.tail v)).length + 2 + (v 0).length := by
      simp [encodeVec_succ]
    omega

/-- **Soundness induction.** Every function of Cobham's algebra is polynomial
time on encoded argument vectors. -/
theorem cobham_imp_FPn : ∀ {n : ℕ} {f : (Fin n → List Bool) → List Bool},
    Cobham f → FPn f := by
  intro n f h
  induction h with
  | proj i => exact fpn_proj i
  | empty => exact fpn_empty
  | bit b => exact fpn_bit b
  | smash => exact fpn_smash
  | comp _ _ ihf ihgs => exact fpn_comp ihf ihgs
  | boundedRec _ _ _ _ hbound ihg ih0 ih1 ihj =>
      exact fpn_boundedRec ihg ih0 ih1 ihj hbound

/-- Arity-one specialization: from the multi-arity soundness induction, the
unary fragment `CobhamFP` lands in `FP`. -/
theorem CobhamFP_subset_FP_of_FPn : CobhamFP ⊆ FP := by
  intro f hf
  obtain ⟨g, hg, hgf⟩ := cobham_imp_FPn hf
  -- `hgf` specialized to `![x]`: `g (pair [] x) = f x`.
  have hval : ∀ x : List Bool, g (pair [] x) = f x := by
    intro x
    have := hgf ![x]
    rwa [encodeVec_one] at this
  -- Hence `f = g ∘ (x ↦ pair [] x)`, a composition of `FP` functions.
  have hfeq : f = g ∘ fun x : List Bool => pair [] x := by
    funext x; simp [Function.comp, hval x]
  rw [hfeq]
  exact mem_FP_comp pairLeftNil_mem_FP hg

/-! ## Completeness: `FP ⊆ CobhamFP` -/

/-- **Completeness direction.** Every polynomial-time function belongs to
Cobham's algebra.

*Construction:* a polynomial-time Turing machine is simulated inside the algebra.
1. A whole configuration — state, input tape, output tape, work tapes and every
   head position — is one bitstring of equal-width blocks, each tape split at its
   head so that a head move is a two-bit shift (`Cobham.cfgCode`).
2. The one-step transition is a finite case split on (state, symbols read), which
   is `Cobham.tableFn` against the finitely many constant key patterns, with each
   branch built from `takeFn`/`dropFn`/`appendFn`/`padFn` (`Cobham.stepFn`). At
   the halting state the branch is the identity, so the encoding is a fixed point
   once the machine stops.
3. The step is iterated once per bit of a clock string built from `smash`
   (`Cobham.exists_pow_clock`), long enough by the polynomial normal form
   `mem_FP_iff_computesInTime_polynomial`.
4. A second iteration walks the output head back to cell `0`
   (`Cobham.rewindFn`), after which that tape's right half-block is the whole
   tape in order, and the output is read off it by two `Complexity.cellBits`
   recursions and one `Complexity.runTrue` (`Cobham.simFn`).
The length bounds throughout are polynomial, so every `boundedRec` side condition
is met. -/
theorem FP_subset_CobhamFP_internal : FP ⊆ CobhamFP := by
  intro f hf
  obtain ⟨k, tm, p, hcomp⟩ := mem_FP_iff_computesInTime_polynomial.mp hf
  exact computes_mem_CobhamFP tm
    (S := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) (D := p.natDegree)
    (poly_eval_le_pow p) hcomp

/-- **Multi-arity completeness.** A unary `FP` witness on canonical encodings is
first translated into the unary Cobham algebra and then composed with
`encodeVec_mem_internal`. -/
theorem FPn_imp_cobham_internal {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : FPn f) : Cobham f := by
  obtain ⟨g, hg, hgf⟩ := hf
  have hgCobham : Cobham fun v : Fin 1 → List Bool => g (v 0) :=
    FP_subset_CobhamFP_internal hg
  refine (Cobham.comp hgCobham fun _ : Fin 1 => encodeVec_mem_internal).of_eq fun v => ?_
  exact hgf v
