/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
-- For the purposes of this library, a "Rake" is a sorted
-- list of arithmetic sequences that share the same delta.
import LeanPool.Leansieve.ASeq.ASeq
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic

/-!
# Rakes (`Rake`)

A `Rake` is a sorted collection of arithmetic sequences sharing a common delta.
This module defines rakes, their `term`/`terms` enumeration, the `term_iff`
characterization of the produced set, sorting and deduplication, the
`partition` that refines each sequence modulo `j`, the `rem` operation that
removes all multiples of `j`, and `gte` truncation.
-/

namespace Leansieve

namespace List

/-- A list is `Sorted` for `r` when consecutive elements are pairwise related. -/
abbrev Sorted {α : Type _} (r : α → α → Prop) (l : List α) : Prop := l.Pairwise r

end List

/-- A `Rake` is a (by default sorted, deduplicated) list of constants `ks`
sharing a common delta `d`, representing the union of arithmetic sequences
`ks[i] + d * n`. -/
structure Rake : Type where
  /-- The common delta shared by every sequence. -/
  d : Nat
  /-- The list of constants, one per arithmetic sequence. -/
  ks : List Nat
  /-- The number of constants (defaults to `ks.length`). -/
  size : Nat := ks.length
  /-- Whether `ks` is maintained sorted and deduplicated. -/
  sorted : Bool := true
  /-- When sorted, `ks` is strictly increasing. -/
  hsort : sorted → List.Sorted (·<·) ks := by simp
  /-- When sorted, `ks` has no duplicates. -/
  huniq : sorted → ks.Nodup := by simp
  /-- `ks` is nonempty. -/
  hsize : 0 < ks.length := by simp

namespace Rake

/-- The empty/zero rake `{0}` with delta `0`. -/
def zer : Rake := { d := 0, ks := [0] }
/-- The rake enumerating all naturals (`0 + 1 * n`). -/
def nat : Rake := { d := 1, ks := [0] }
/-- The rake enumerating naturals `≥ 2` (`2 + 1 * n`). -/
def ge2 : Rake := { d := 1, ks := [2] }

section « terms » -- generating output terms from the rake

/-- The `n`-th term produced by the rake (interleaving its sequences). -/
def term (r : Rake) (n : Nat) : Nat :=
  let q := r.ks.length
  have : n%q < r.ks.length := Nat.mod_lt _ r.hsize
  aseq r.ks[n%q] r.d |>.term (n/q)

/-- The first `n` terms produced by the rake. -/
def terms (r : Rake) (n : Nat) : List Nat :=
  List.range n |>.map r.term

theorem term_simp (r : Rake) (n : Nat)
: (∃ k, (r.term n = k + r.d * (n/r.ks.length)) ∧
    ∃ i : Fin r.ks.length, i = n%r.ks.length ∧ k = r.ks[i]) := by
  let i : Fin r.ks.length := ⟨n%r.ks.length, Nat.mod_lt n r.hsize⟩
  use r.ks[i]
  apply And.intro
  · dsimp[term, i]
  · use i

theorem term_iff (r : Rake)
  : ∀ m, (∃ n, r.term n = m) ↔ (∃ k ∈ r.ks, ∃ x : Nat, k + x*r.d = m) := by
  intro m; apply Iff.intro
  · show (∃ n, r.term n = m) → ∃ k ∈ r.ks, ∃ x, k + x * r.d = m
    -- this is just grunt work, but it follows from the definition of term
    intro ⟨n, hn⟩; obtain ⟨k, hk, i, hi, hki⟩ := r.term_simp n
    use k; apply And.intro
    · simp only [List.mem_iff_get, List.get_eq_getElem]; use i; exact hki.symm
    · use (n/r.ks.length); subst hki hn
      simp_all only [Fin.getElem_fin, Nat.add_left_cancel_iff]
      exact Nat.mul_comm (n / r.ks.length) r.d
  · show (∃ k ∈ r.ks, ∃ x, k + x * r.d = m) → ∃ n, r.term n = m
    -- in other words, given some k in our list and an arbitrary x
    -- the rake ought to produce m = k + x * r.d at some point. we prove
    -- this by working backwards to calculate what n we have to plug
    -- into (r.term n) in order to get n back out.
    intro ⟨k, hk, hx₀⟩
    -- k is a member of ks so it must have an index in ks: k=r.ks.get i
    rw[List.mem_iff_get] at hk
    obtain ⟨i : Fin r.ks.length, hi₀ : r.ks.get i = k⟩ := hk
    -- k uniquely identifies a particular arithmetic sequence within
    -- the rake, and there's some x that we can feed into this sequence
    -- to get the result m. we can obtain it:
    obtain ⟨x, hx : k + x * r.d = m⟩ := hx₀
    -- now we can choose n so that r.term n picks k=ks[ i ] as the constant.
    -- this happens ∀ n, i = n % r.ks.length ∧ x = n / r.ks.length
    have hi₁ : i.val % r.ks.length = i.val := Nat.mod_eq_of_lt i.prop
    let n := (i.val % r.ks.length) + (x * r.ks.length)
    -- now we run this definition of `n` through `r.term n` and
    -- once we deal with annoying divmod issues, out comes the result.
    use n
    have hmod : (n % r.ks.length) = i.val := by
      dsimp [n]
      calc
        (i.val % r.ks.length + x * r.ks.length) % r.ks.length
            = (i.val % r.ks.length) % r.ks.length := by
          rw [Nat.add_mul_mod_self_right]
        _ = i.val % r.ks.length := Nat.mod_mod _ _
        _ = i.val := Nat.mod_eq_of_lt i.prop
    have hdiv : (n / r.ks.length) = x := by
      dsimp [n]
      rw [Nat.add_mul_div_right _ _ r.hsize, Nat.div_eq_of_lt (Nat.mod_lt _ r.hsize)]
      simp
    calc
      r.term n = r.ks[i] + x * r.d := by
        dsimp [term]
        simp [hmod, hdiv, Nat.mul_comm]
      _ = k + x * r.d := by simpa using congrArg (fun t => t + x * r.d) hi₀
      _ = m := hx

end « terms »

section « sequences » -- arithmetic sequences for each k ∈ ks

/-- The `n`-th arithmetic sequence of the rake (constant `ks[n]`, delta `d`). -/
def seq (r : Rake) (n : Nat) {hn : n < r.ks.length} : ASeq :=
  aseq (r.ks[n]'hn) r.d

/-- The list of arithmetic sequences making up the rake. -/
def seqs (r : Rake) : List ASeq :=
  r.ks.map (fun k => aseq k r.d)

/-- this is slightly more specific than `term_iff`, in that
it gives you a specific k and its index -/
theorem k_of_term (r : Rake) (hmn : r.term m = n)
: ∃ k ∈ r.ks, ∃ i : (Fin r.ks.length),
    i = m%r.ks.length
    ∧ k = r.ks[i]
    ∧ n = k + r.d * (m/r.ks.length) := by
  set q := r.ks.length with hq
  have hmq : m%q < r.ks.length := Nat.mod_lt _ r.hsize
  set k := r.ks[m%q] with hk; use k
  split_ands
  · show k ∈ r.ks
    exact List.get_mem r.ks ⟨m % q, hmq⟩
  · set i : Fin _ := ⟨m%q, Nat.mod_lt m r.hsize⟩ with hi
    use i
    split_ands
    · rw[hi]
    · rw[hi, hk]; simp
    · simp[←hmn, term, ← hq, hk]

end « sequences »

section « sort and dedup »

/-- Sort a duplicate-free list of naturals, with proofs that the result is
strictly sorted, a permutation of the input, of equal length, and duplicate-free. -/
def sortNodup (xs : List Nat) (hxs₀ : List.Nodup xs)
: { xs' : List Nat // List.Sorted (·<·) xs' ∧ xs'.Perm xs
    ∧ xs.length = xs'.length ∧ xs'.Nodup } :=
  let xs' := xs.mergeSort (·≤·)
  have hnodup : xs'.Nodup := (List.mergeSort_perm xs (·≤·)).nodup_iff.mpr hxs₀
  have hsorted : xs'.SortedLE := List.sortedLE_mergeSort (l := xs)
  have hlength := by simp_all only [List.length_mergeSort, xs']
  have hperm : xs'.Perm xs := List.mergeSort_perm xs (·≤·)
  ⟨xs', And.intro (List.SortedLE.sortedLT_of_nodup hsorted hnodup |>.pairwise)
    (And.intro hperm (And.intro hlength hnodup))⟩

/-- Sort and deduplicate a rake's constants, returning an equivalent sorted rake. -/
def sort (r : Rake) : {r' : Rake // r'.d = r.d ∧ r'.sorted ∧ r'.ks.Perm r.ks.dedup } :=
  if hs : r.sorted then
    have hp : r.ks.Perm r.ks.dedup := by
      have := r.huniq hs
      rw[←r.ks.dedup_eq_self] at this
      rw[this]
    ⟨r, And.intro rfl <| And.intro hs hp⟩
  else
    let ks₀ := r.ks
    let ks₁ := ks₀.dedup
    let ks₂ := sortNodup ks₁ ks₀.nodup_dedup
  have ⟨hsort, hperm, hlength, hnodup⟩ := ks₂.prop
  have hlen₁ : ks₁.length ≠ 0 := by have := r.hsize; aesop
  have hsize := Nat.lt_of_lt_of_eq (Nat.zero_lt_of_ne_zero hlen₁) hlength
  ⟨{ d := r.d, ks := ks₂, hsort := fun _ => hsort, huniq := fun _ => hnodup, hsize := hsize}, by
    refine ⟨rfl, ?_, hperm⟩
    rfl⟩

lemma length_pos_of_dedup {l : List Nat} (hlen : 0 < l.length) : 0 < l.dedup.length := by
  obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_length_pos hlen
  have : hd ∈ l := by rw [hcons]; simp
  rw[←List.mem_dedup] at this
  exact List.length_pos_of_mem this

/-- Case split on whether `n` is zero or positive, choosing the matching branch. -/
def zeroLeCases (n : Nat) (zeq : 0 = n → P) (zlt : 0 < n → P) : P :=
  if h : 0 = n then zeq h else zlt <| Nat.zero_lt_of_ne_zero fun a => h a.symm

lemma sorted_get (xs : List Nat) (hxs : List.Sorted (· < ·) xs) (i j : Fin xs.length)
    (hij : i < j)
  : (xs[i] < xs[j]) := by
  conv at hxs => dsimp[List.Sorted]; rw[List.pairwise_iff_get]
  simp_all

/--
As currently defined, the terms of a sorted rake can be non-ascending in one of two ways:
- ascending sawtooth pattern if ∃k∈r.ks, k>r.d
- cyclic (and possibly constant) if r.d=0
But in all cases, if the rake is sorted, term 0 is the minimum. -/
theorem sorted_min_term_zero (r : Rake) (hr : r.sorted) : ∀ n, (r.term 0 ≤ r.term n) := by
  intro n
  obtain ⟨k₀, hk₀, i₀, hi₀⟩ := r.term_simp 0
  obtain ⟨k₁, hk₁, i₁, hi₁⟩ := r.term_simp n
  simp only [hk₀, Nat.zero_div, mul_zero, add_zero, hk₁]
  suffices k₀ ≤ k₁ by exact le_add_right this
  rw[hi₀.right, hi₁.right]
  apply zeroLeCases i₁.val; all_goals intro hi
  case zeq => simp_all
  case zlt =>
    have : i₀.val < i₁.val := by aesop
    exact Nat.le_of_succ_le <| sorted_get r.ks (r.hsort hr) i₀ i₁ this

theorem sort_term_iff_term (r : Rake) (n : Nat)
  : (∃ m, r.term m = n) ↔ (∃ m', r.sort.val.term m' = n) := by
  if h : r.sorted then
    constructor <;> intro hm <;> simpa [sort, h] using hm
  else
    let ⟨rs, ⟨hd, hsort, hperm⟩⟩ := r.sort; simp only
    have : ∀ k, k ∈ rs.ks ↔ k ∈ r.ks.dedup := fun k => List.Perm.mem_iff hperm
    have hmem : ∀ k, k ∈ r.ks ↔ k ∈ rs.ks := by aesop
    apply Iff.intro
    all_goals
      intro h; rw[term_iff] at h; obtain ⟨k, hk₀, hk₁⟩ := h
      specialize hmem k
      rw[term_iff]
      use k
      apply And.intro
    · rwa[←hmem]
    · rwa[hd]
    · rwa[hmem]
    · rwa[←hd]

end « sort and dedup »

section « rake operations »

section « partition »

lemma List.mod_length {α : Type} (l : List α) (i : Nat) (hl : 0 < l.length)
  : (i % l.length) < l.length := by exact Nat.mod_lt (↑i) hl

/--
Partition each sequence in the rake by partitioning their *inputs*
into equivalance classes mod n. This multiplies the number of sequences
by n. We can't allow n to be zero because then we'd have no sequences left,
and this would break the guarantee that term (n) < term n+1. -/
def partition (r : Rake) (j : Nat) (hj : 0 < j := by simp) : Rake :=
  let ks' := List.range (j*r.ks.length) |>.map fun i =>
    r.ks[i%r.ks.length]'(List.mod_length r.ks i r.hsize) + (i/r.ks.length) * r.d
  have : ks'.length = j*r.ks.length := by simp [ks']
  have := r.hsize
  { d := r.d*j, ks := ks', sorted := false, hsize := by aesop }

@[simp]
theorem length_partition (r : Rake) (j : Nat) (hj : 0 < j)
  : (r.partition j hj).ks.length = j * r.ks.length := by simp[partition]

theorem partition_def (r : Rake) (j : Nat) (hj : 0 < j) (i') (hi')
  : (r.partition j hj).ks[i'] =
    r.ks[i'%r.ks.length]'(List.mod_length r.ks i' r.hsize) + (i'/r.ks.length) * r.d
  := by simp[partition]

theorem partition_term_same (r : Rake) (j : Nat) (hj : 0 < j) (r' : Rake)
    (hr' : r' = r.partition j hj)
  : ∀ n, (∃ m', r'.term m' = n) → (∃ m, r.term m = n) := by
  -- `partition` changes `d` and `ks` but keeps a permutation of the terms.
  -- we use term_iff so we can argue in terms of `.ks` before and after.
  intro n; repeat rw[term_iff]
  -- note that r'.d := r.d*j by the definition of `partition`
  (have : r'.d = r.d*j := by simp[hr', partition]); simp only[this]; clear this
  -- we can now write the goal like so:
  -- `(∃ k' ∈ r'.ks, ∃ x', k' + x' * (r.d * j) = n) → ∃ k ∈ r.ks, ∃ x, k + x * r.d = n`
  -- introduce variables for the left side such that
  -- hik: (r'[i']=k)   and   hx': k' + x' + r.d * j= n
  intro ⟨k', hk', x', hx'⟩
  obtain ⟨i', hik'⟩ : ∃ (i' : Fin r'.ks.length), _ := by
    rw[List.mem_iff_get] at hk'; exact hk'
  -- goal: `∃ k, k ∈ r.ks ∧ ∃ x, k + x * r.d = n`
  -- we already have a theorem that relates the indices of k and k'
  -- derived from the definition of `partition`.
  have hdef := partition_def r j hj
  specialize hdef i' (by rw[←hr']; exact i'.prop)
  set i := i' % r.ks.length with hi
  set k := r.ks[i]'(List.mod_length r.ks i' r.hsize) with hk
  set x := i' / r.ks.length with hx
  use k
  apply And.intro
  · exact List.get_mem r.ks ⟨i, by simpa [i] using List.mod_length r.ks i' r.hsize⟩
  · replace hdef : k' = k + x * r.d := by simp_all
    open Nat in rw[mul_comm, hdef, mul_comm, add_assoc, mul_assoc, ←mul_add, mul_comm] at hx'
    use x + j * x'

theorem partition_term_keep (r : Rake) (j : Nat) (hj : 0 < j) (r' : Rake)
    (hr' : r' = r.partition j hj)
  : ∀ t, (∃ n, r.term n = t) → (∃ n, r'.term n = t) := by
  /- In this direction, each sequence `ksᵢ + d` gets partitioned into
    *multiple* sequences. There are exactly `j` new sequences, arranged like so:

    `  r.ks  = [ks₀, ks₁, ..., ksₖ₋₁]`
    `  r'.ks = [ks₀, ks₁, ..., ks₀+d, ks₁+d, ..., ks[z]₋₁+d×(j-1)]`

    Since `r.term n = r.ks[(i := n % z)] + d * (n /z)`, and
    `r'.ks.length` is a multiple of `r.ks.length`, the terms come out
    in the exact same order.

    To prove this, we first use `k_of_term` to expand the formula for `r.term n`: -/
  intro t ⟨n, hn⟩; simp only [term_iff]
  set z := r.ks.length
  set z' := r'.ks.length with hz'
  have hz'z : z' = (z * j) := by rw[hz', hr', length_partition, Nat.mul_comm]
  obtain ⟨k, _, i, hi, hki, ht⟩ := r.k_of_term (hn : r.term n = t)
  set i' : Fin z' := ⟨n%z', Nat.mod_lt n r'.hsize⟩ with hi'
  set k' := r'.ks[i'] with hk'
  have hi'_val : (i' : Nat) = n % z' := by simp [hi']
  -- map the new constant to the old one
  have hdef : k' = k + i'/z * r.d := by
    have hpart := partition_def r j hj i' (by simpa [hr', length_partition, hz', z] using i'.prop)
    have hidx : (↑i' % r.ks.length) = n % r.ks.length := by
      rw [hi'_val, hz'z, Nat.mod_mul_right_mod]
    have hkidx : r.ks[↑i' % r.ks.length] = k := by
      simpa [hidx, hi] using hki.symm
    calc
      k' = r.ks[↑i' % r.ks.length] + (↑i' / r.ks.length) * r.d := by
        simpa [hr', hk'] using hpart
      _ = k + (↑i' / z) * r.d := by
        simpa [z] using congrArg (fun t => t + (↑i' / z) * r.d) hkidx
  -- goal: `∃ k' ∈ r'.ks, ∃ x', k' + x' * r'.d = t`
  use k'
  apply And.intro
  · show k' ∈ r'.ks
    exact List.get_mem r'.ks i'
  · use n/z'; subst ht; rw[Nat.mul_comm]
    set t' := k' + r'.d * (n/z') with ht'
    -- goal: `t' = k + r.d * (n/z)`; we need to remove the `'` on `r'.d` and `z'`
    calc t' = k + i'/z * r.d + (r.d * j) * (n/(z *j)) := by simp_all [partition]
      _= k + r.d * (i'/z + j * (n/(z *j))) :=
         by rw[Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm, Nat.mul_add]
      _= k + r.d * ((n%(z*j)/z) + j * (n/(z *j))) := by
         have hiDiv : ↑i' / z = n % (z * j) / z := by rw [hi'_val, hz'z]
         rw [hiDiv]
      _= k + r.d * (((n/z)%j) + j * (n/(z *j))) := by rw[Nat.mod_mul_right_div_self]
      _= k + r.d * ((n/z)%j + j * ((n/z)/j)) :=
         by
           simp only [Nat.add_left_cancel_iff, mul_eq_mul_left_iff, z]
           left
           left
           exact Eq.symm (Nat.div_div_eq_div_mul n z j)
      _= k + r.d * (n / z) := by rw[Nat.mod_add_div (n/z) j]

theorem partition_term_iff (r : Rake) (j : Nat) (hj : 0 < j)
  : ∀ n, (∃ m, (r.partition j hj).term m = n) ↔ (∃ m, r.term m = n) :=
  fun n => Iff.intro
    (partition_term_same r j hj (r.partition j hj) rfl n)
    (partition_term_keep r j hj (r.partition j hj) rfl n)

end « partition »

section « rem (remove multiples) »

variable (r : Rake) {j : Nat} (hj : 0 < j)

/-- remove all multiples of `j`. -/
def rem : Rake :=
  -- !! I was going to have be a bit smarter in the general case but
  --    this makes no difference in RakeSieve because j is always prime
  -- let gcd := r.d.gcd j
  -- have hz : 0 < (j/gcd) := Nat.div_gcd_pos_of_pos_right r.d hj
  -- let r' := if j∣r.d then r else r.partition (j/gcd) hz
  let r' := r.partition j hj
  let ks := r'.ks.filter (fun k => ¬j ∣ k)
  if hlen : ks.length = 0 then zer
  else { d := r'.d, ks := ks, sorted := false, hsize := Nat.zero_lt_of_ne_zero hlen }

/-- The rake has a term that is not a multiple of `j`. -/
abbrev HasNonMultiple (j : Nat) : Prop := ∃ n, ¬j ∣ n ∧ ∃ m, r.term m = n

lemma rem_def' (r : Rake) {j : Nat} (hj : 0 < j) (r' : Rake) (hr' : r' = r.rem hj)
  : r' = zer
  ∨ (r'.d = r.d*j ∧ r'.ks = (r.partition j hj).ks.filter (fun k => ¬j ∣ k) ∧ 0 < r'.ks.length) := by
    simp[hr', rem, partition]; split <;> simp_all[Nat.zero_lt_of_ne_zero]

theorem rem_def (r : Rake) {j : Nat} (hj : 0 < j) (r' : Rake) (hr' : r' = r.rem hj)
    (hnm : HasNonMultiple r j)
  : r'.d = r.d*j ∧ r'.ks = (r.partition j hj).ks.filter (fun k => ¬j ∣ k) ∧ 0 < r'.ks.length := by
  obtain hzer | ⟨hd', hks', hlen'⟩ := rem_def' r hj r' hr'
  · -- show hzer case cannot happen thanks to h₁
    -- r produces terms that don't divide k, and r.partition produces the same terms.
    -- from h1 we can obtain a k∈r.k coprime to p
    obtain ⟨n, hn, hex⟩ := hnm
    obtain ⟨k, hk, x, hx⟩ := by rwa[←r.partition_term_iff j hj n, term_iff] at hex
    have hjk : ¬j ∣ k := by
      by_contra h
      have : j ∣ r.d * j * x := by
        have := Nat.dvd_mul_right j (r.d*x); rwa[Nat.mul_left_comm, ←Nat.mul_assoc] at this
      have : j ∣ k + r.d * j * x := by exact (Nat.dvd_add_iff_right h).mp this
      have : ¬j ∣ k + r.d * j * x := by
        have : (r.partition j hj).d = r.d * j := by aesop
        rwa[←hx, this, Nat.mul_comm] at hn
      contradiction
    -- now show that k survives the filter operation:
    set r'k := (r.partition j hj).ks.filter (fun k => ¬j ∣ k)
    have rk : k ∈ r'k := by simp[hk, r'k, hjk, List.mem_filter]
    -- k ≠ 0 because ¬p∣k and ∀n,n∣0
    have : k ≠ 0 := by by_contra h; have := Nat.dvd_zero j; rw[h] at hjk; contradiction
    -- but that contradicts the notion that r'=hzer
    have : k = 0 := by
      set rpk := (r.partition j hj).ks.filter (fun k => ¬j ∣ k)
      have rk : k ∈ rpk := by simp[hk, hjk, rpk, List.mem_filter]
      have hlen : rpk.length ≠ 0 := Nat.ne_of_gt (List.length_pos_of_mem rk)
      have hnot : ¬ ∀ a ∈ (r.partition j hj).ks, j ∣ a := by
        intro hall
        exact hjk (hall k hk)
      have : r'.ks = rpk := by simp [hr', rem, rpk, hnot]
      have : r'.ks = [0] := by simp[hzer, zer]
      simp_all
    contradiction
  · -- the non-zer case just passes through
    exact ⟨hd', hks', hlen'⟩

theorem rem_drop (r : Rake) {j : Nat} (hj : 0 < j) (r' : Rake) (hr' : r' = r.rem hj)
    (hnm : HasNonMultiple r j)
  : ∀ n, j ∣ n → ¬(∃ m, r'.term m = n) := by
  -- general idea:
  --   the only way term m = n is if ∃x, ∃k∈r.ks, k + x*d = n
  --   x would have to be be n/ks.length, but i'm not sure we need that fact
  --   term_iff supplies this fact.
  intro n hjn; rw[term_iff]
  -- we will show no such k exists
  push Not; intro k hk x
  set d' := r'.d
  -- either rem returns zer, or we can extract the formulas for d and ks
  obtain ⟨hd', hks', hlen'⟩ := rem_def r hj r' hr' hnm
  -- we only have to show ¬j∣k, because `j∣d` so `x*d` cancels out mod j
  suffices ¬j ∣ k from by
    by_contra h
    have h₀ : j ∣ k + x * d' := by rwa[h.symm] at hjn
    have h₁ : j ∣ x * d' := Dvd.dvd.mul_left (Dvd.intro_left r.d hd'.symm) x
    have : j ∣ k := (Nat.dvd_add_iff_left h₁).mpr h₀
    contradiction
  show ¬j ∣ k
  simp_all[List.mem_filter]

theorem rem_keep (r : Rake) {j : Nat} (hj : 0 < j) (r' : Rake) (hr' : r' = r.rem hj)
  : ∀ n, ¬j ∣ n → (∃ m, r.term m = n) → (∃ m', r'.term m' = n) := by
  -- this follows from partition_term_iff and the nature of filter
  intro n hjn ht
  have ht' := ht
  -- r produces terms that don't divide k, and r.partition produces the same terms.
  rw[←r.partition_term_iff j hj n, term_iff] at ht'
  -- since r.partition produces n, we can show ¬j∣k for the corresponding k
  obtain ⟨k, hk, x, hx⟩ := ht'
  have hnm : HasNonMultiple r j := by use n
  obtain ⟨hd', hks'⟩ := rem_def r hj r' hr' hnm
  -- !! this duplicates some work from rem_def' ... consolidate?
  have hjk : ¬ j ∣ k := by
    by_contra h
    have : j ∣ r.d * j * x := by
      have : j ∣ j * (r.d * x) := Nat.dvd_mul_right j _
      rwa[Nat.mul_left_comm, ←Nat.mul_assoc] at this
    have : j ∣ k + r.d * j * x := by exact (Nat.dvd_add_iff_right h).mp this
    have : ¬j ∣ k + r.d * j * x := by
      have : (r.partition j hj).d = r.d * j := by aesop
      rwa[←hx, this, Nat.mul_comm] at hjn
    contradiction
  have : k ∈ r'.ks := by simp[hk, hks', hjk, List.mem_filter]
  rw[term_iff]
  use k; aesop

theorem rem_same (r : Rake) {j : Nat} (hj : 0 < j) (r' : Rake) (hr' : r' = r.rem hj)
    (hnm : HasNonMultiple r j)
  : ∀ n, (∃ m', r'.term m' = n) → (∃ m, r.term m = n) := by
  -- this follows from partition_term_iff and the nature of filter.
  intro n h; rw[term_iff] at h; obtain ⟨k, hk, x, hx⟩ := h
  obtain ⟨hd', hks'⟩ := rem_def r hj r' hr' hnm
  have := r.partition_term_iff j hj n
  rw[term_iff] at this; rw[←this]
  have : k ∈ (r.partition j hj).ks := by simp_all
  use k; aesop

end « rem (remove multiples) »

section « gte (greater than or equal to) »

/-- Truncate every sequence of the rake to keep only terms `≥ n`. -/
def gte (r : Rake) (n : Nat) : Rake :=
  let f : ℕ → ℕ := (fun k => let s := aseq k r.d; (ASeq.gte s n).k)
  { d := r.d, ks := r.ks.map f, sorted := false,
    hsize := Nat.lt_of_lt_of_eq r.hsize (r.ks.length_map _).symm }

end « gte (greater than or equal to) »

end « rake operations »

end Rake

end Leansieve
