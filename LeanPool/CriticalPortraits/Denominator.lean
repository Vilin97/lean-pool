/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/

import LeanPool.CriticalPortraits.Core

/-!
# The `/d` denominator: `#level-canonical = C(N, d-1)/d` (all d), Mathlib, sorry-free.

PRIMARY (multiplicative form):
  `d * #{S // S.card = d-1 ∧ LevelCanonical d m S} = (d*m).choose (d-1)`
COROLLARY (division form), one-liner from the above.

Route: rotation `rhoPow t` (translate by `+(t*m)`), the per-level count vector `cnt`,
the cycle-lemma bridge (`∃!` canonical rotation index per `(d-1)`-subset), assembled into a
bijection `{(d-1)-subsets} ≃ {canonical} × Fin d` (uniqueness of the canonical index supplies
freeness for free), giving `card = #canonical * d`.
-/

namespace CriticalPortraits

open Finset
open scoped BigOperators

/-! ## Part 0: a Fintype instance for the target subtype (all `d, m`).

The TARGET statement uses `Fintype.card {S : Finset (ZMod (d*m)) // …}` with no `[NeZero (d*m)]`
binder, so we must provide the `Fintype` instance unconditionally. When `d*m ≠ 0` it comes from
`NeZero`; in the degenerate case `d*m = 0` the predicate forces every `S = ∅` (a singleton),
so the subtype is still finite. -/

instance instFiniteCanonical (d m : ℕ) :
    Finite {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S} := by
  rcases Nat.eq_zero_or_pos (d * m) with h0 | hpos
  · have hsub : ∀ S : {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S},
        S.1 = ∅ := by
      rintro ⟨S, hcard, hLC⟩
      simp only
      apply Finset.card_eq_zero.mp
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · have hd1 : d - 1 = 0 := by omega
        rw [hd1] at hcard; exact hcard
      · have hm0 : m = 0 := by
          rcases Nat.eq_zero_or_pos m with h | h
          · exact h
          · exfalso; have : 0 < d * m := Nat.mul_pos hdpos h; omega
        have hLC0 := hLC 0 hdpos
        have hfilter : (S.filter (fun i => i.val / m ≤ 0)) = S := by
          apply Finset.filter_true_of_mem
          intro i _
          have hdiv : i.val / m = 0 := (congrArg (i.val / ·) hm0).trans (Nat.div_zero i.val)
          rw [hdiv]
        rw [hfilter] at hLC0
        exact Nat.le_zero.mp hLC0
    exact Finite.of_injective (fun _ => (0 : Unit)) (by
      intro a b _; exact Subtype.ext ((hsub a).trans (hsub b).symm))
  · haveI : NeZero (d * m) := ⟨hpos.ne'⟩
    infer_instance

noncomputable instance instFintypeCanonical (d m : ℕ) :
    Fintype {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S} :=
  Fintype.ofFinite _

/-! ## Part 1: level arithmetic. -/

/-- Every level is `< d` (when `N = d*m`, `m > 0`). -/
lemma level_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (i : ZMod (d * m)) :
    i.val / m < d := by
  haveI : NeZero (d * m) := ⟨by positivity⟩
  have hi : i.val < d * m := ZMod.val_lt i
  have hi' : i.val < m * d := by rw [Nat.mul_comm m d]; exact hi
  exact Nat.div_lt_of_lt_mul hi'

/-- The shift element `t*m` reduces to `(t%d)*m` in `ZMod (d*m)`. -/
lemma shift_cast {d m : ℕ} (t : ℕ) :
    ((t * m : ℕ) : ZMod (d * m)) = (((t % d) * m : ℕ) : ZMod (d * m)) := by
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]
  rw [Nat.mul_mod_mul_right m t d, Nat.mul_mod_mul_right m (t % d) d, Nat.mod_mod_of_dvd t dvd_rfl]

/-- `(t%d)*m < d*m`, so its `val` is itself. -/
lemma shift_val_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (t : ℕ) :
    (t % d) * m < d * m := by
  have h : t % d < d := Nat.mod_lt _ hd
  exact (Nat.mul_lt_mul_right hm).mpr h

/-- The fundamental level-shift identity: translating by `+(t*m)` adds `t` to the level
    cyclically. -/
lemma level_add {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (t : ℕ) (i : ZMod (d * m)) :
    (i + ((t * m : ℕ) : ZMod (d * m))).val / m = (i.val / m + t % d) % d := by
  haveI : NeZero (d * m) := ⟨by positivity⟩
  set t' := t % d with ht'
  have ht'd : t' < d := Nat.mod_lt _ hd
  have hcval : (((t * m : ℕ) : ZMod (d * m))).val = t' * m := by
    rw [shift_cast t, ZMod.val_natCast, Nat.mod_eq_of_lt (shift_val_lt hd hm t)]
  have hsum : (i + ((t * m : ℕ) : ZMod (d * m))).val = (i.val + t' * m) % (d * m) := by
    rw [ZMod.val_add, hcval]
  rw [hsum]
  set q := i.val / m with hq
  set r := i.val % m with hr
  have hival : i.val = q * m + r := by
    rw [hq, hr]; exact (Nat.div_add_mod' i.val m).symm
  have hrm : r < m := Nat.mod_lt _ hm
  have hqd : q < d := level_lt hd hm i
  have hrewrite : i.val + t' * m = (q + t') * m + r := by rw [hival]; ring
  rw [hrewrite]
  set a := q + t' with ha
  have hbound : (a % d) * m + r < d * m := by
    have : a % d < d := Nat.mod_lt _ hd
    have h2 : (a % d) * m + r < (a % d) * m + m := by omega
    have h3 : (a % d) * m + m = (a % d + 1) * m := by ring
    have h4 : (a % d + 1) * m ≤ d * m := by
      apply Nat.mul_le_mul_right; omega
    omega
  have hmod2 : (a * m + r) % (d * m) = (a % d) * m + r := by
    have hdecomp : a * m + r = ((a % d) * m + r) + (a / d) * (d * m) := by
      have hh : a = (a / d) * d + a % d := (Nat.div_add_mod' a d).symm
      calc a * m + r = ((a / d) * d + a % d) * m + r := by rw [← hh]
        _ = ((a % d) * m + r) + (a / d) * (d * m) := by ring
    rw [hdecomp, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hbound
  rw [hmod2]
  rw [Nat.add_comm ((a % d) * m) r, Nat.add_mul_div_right r (a % d) hm,
      Nat.div_eq_of_lt hrm, Nat.zero_add]

/-! ## Part 2: counts and prefix sums. -/

/-- Number of elements of `S` at level exactly `j`. -/
def cnt {d m : ℕ} (S : Finset (ZMod (d * m))) (j : ℕ) : ℕ :=
  (S.filter (fun i => i.val / m = j)).card

/-- `S` is partitioned by level into `range d`: total count is `S.card`. -/
lemma sum_cnt {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m))) :
    ∑ j ∈ Finset.range d, cnt S j = S.card := by
  classical
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := fun i => i.val / m) (s := S) (t := Finset.range d)
    (by intro i _; exact Finset.mem_range.mpr (level_lt hd hm i))]

/-- Prefix count: `#{i ∈ S : level i ≤ j} = ∑_{l ≤ j} cnt S l`. -/
lemma prefix_cnt {d m : ℕ} (S : Finset (ZMod (d * m))) (j : ℕ) :
    (S.filter (fun i => i.val / m ≤ j)).card = ∑ l ∈ Finset.range (j + 1), cnt S l := by
  classical
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun i => i.val / m) (s := S.filter (fun i => i.val / m ≤ j))
    (t := Finset.range (j + 1))
    (by intro i hi
        rw [Finset.mem_coe, Finset.mem_filter] at hi
        change i.val / m ∈ Finset.range (j + 1)
        exact Finset.mem_range.mpr (by omega))]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hl
  congr 1
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hiS, _⟩, hil⟩; exact ⟨hiS, hil⟩
  · rintro ⟨hiS, hil⟩; exact ⟨⟨hiS, by omega⟩, hil⟩

/-! ## Part 3: the rotation `rhoPow` and the count-shift. -/

/-- Cyclic round-trip: for `a, b < d`, `(((a + (d-b)) % d) + b) % d = a`. -/
lemma cyc_round (a b d : ℕ) (_hd : 0 < d) (ha : a < d) (hb : b < d) :
    (((a + (d - b)) % d) + b) % d = a := by
  have h1 : (((a + (d - b)) % d) + b) ≡ (a + (d - b) + b) [MOD d] :=
    (Nat.mod_modEq _ _).add_right b
  have h2 : a + (d - b) + b = a + d := by omega
  have h3 : (a + d) ≡ a [MOD d] := Nat.add_mod_right a d
  have h4 : (((a + (d - b)) % d) + b) ≡ a [MOD d] := by
    rw [h2] at h1; exact h1.trans h3
  have hlt : (((a + (d - b)) % d) + b) % d = a % d := h4
  rw [Nat.mod_eq_of_lt ha] at hlt
  exact hlt

/-- The inverse cyclic relation. -/
lemma cyc_inv (a b c d : ℕ) (_hd : 0 < d) (ha : a < d) (hb : b < d) (_hc : c < d)
    (h : c = (a + b) % d) : a = (c + (d - b)) % d := by
  have h1 : (c + (d - b)) ≡ ((a + b) + (d - b)) [MOD d] := by
    rw [h]; exact (Nat.mod_modEq _ _).add_right (d - b)
  have h2 : (a + b) + (d - b) = a + d := by omega
  have h3 : (a + d) ≡ a [MOD d] := Nat.add_mod_right a d
  have h4 : (c + (d - b)) ≡ a [MOD d] := by rw [h2] at h1; exact h1.trans h3
  have hlt : (c + (d - b)) % d = a % d := h4
  rw [Nat.mod_eq_of_lt ha] at hlt
  exact hlt.symm

/-- `t`-fold rotation: translate every element by `+(t*m)`. -/
def rhoPow {d m : ℕ} (t : ℕ) (S : Finset (ZMod (d * m))) : Finset (ZMod (d * m)) :=
  S.map (Equiv.addRight (((t * m : ℕ) : ZMod (d * m)))).toEmbedding

@[simp] lemma card_rhoPow {d m : ℕ} (t : ℕ) (S : Finset (ZMod (d * m))) :
    (rhoPow t S).card = S.card := by
  unfold rhoPow; rw [Finset.card_map]

lemma mem_rhoPow {d m : ℕ} (t : ℕ) (S : Finset (ZMod (d * m))) (x : ZMod (d * m)) :
    x ∈ rhoPow t S ↔ ∃ y ∈ S, y + ((t * m : ℕ) : ZMod (d * m)) = x := by
  unfold rhoPow
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [Equiv.coe_toEmbedding, Equiv.coe_addRight]⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [Equiv.coe_toEmbedding, Equiv.coe_addRight]⟩

/-- Composing rotations: `rhoPow t (rhoPow u S) = rhoPow (t + u) S`. -/
lemma rhoPow_add {d m : ℕ} (t u : ℕ) (S : Finset (ZMod (d * m))) :
    rhoPow t (rhoPow u S) = rhoPow (t + u) S := by
  unfold rhoPow
  rw [Finset.map_map]
  congr 1
  ext x
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.coe_addRight]
  rw [add_assoc]
  congr 1
  push_cast
  ring

/-- `rhoPow 0 S = S`. -/
@[simp] lemma rhoPow_zero {d m : ℕ} (S : Finset (ZMod (d * m))) : rhoPow 0 S = S := by
  unfold rhoPow
  simp only [Nat.zero_mul, Nat.cast_zero]
  rw [show (Equiv.addRight (0 : ZMod (d * m))) = Equiv.refl _ from by ext x; simp]
  simp

/-- `rhoPow d S = S` (a full cycle is the identity). -/
lemma rhoPow_period {d m : ℕ} (S : Finset (ZMod (d * m))) : rhoPow d S = S := by
  unfold rhoPow
  have : ((d * m : ℕ) : ZMod (d * m)) = 0 := by rw [ZMod.natCast_self]
  rw [this]
  rw [show (Equiv.addRight (0 : ZMod (d * m))) = Equiv.refl _ from by ext x; simp]
  simp

/-- `rhoPow` only depends on `t % d`. -/
lemma rhoPow_mod {d m : ℕ} (t : ℕ) (S : Finset (ZMod (d * m))) :
    rhoPow (t % d) S = rhoPow t S := by
  unfold rhoPow
  rw [shift_cast t]

/-- The count-shift: rotating by `t` shifts the level-count vector cyclically.
    For `j < d`, the elements of `rhoPow t S` at level `j` biject (via `+t'*m`) with the
    elements of `S` at level `(j + (d - t%d)) % d`. -/
lemma cnt_rhoPow {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (t : ℕ) (S : Finset (ZMod (d * m)))
    (j : ℕ) (hj : j < d) :
    cnt (rhoPow t S) j = cnt S ((j + (d - t % d)) % d) := by
  classical
  haveI : NeZero (d * m) := ⟨by positivity⟩
  have ht'd : t % d < d := Nat.mod_lt _ hd
  unfold cnt
  have hcancel_ts : ∀ y : ZMod (d * m),
      y + ((t * m : ℕ) : ZMod (d * m)) + (((d - t % d) * m : ℕ) : ZMod (d * m)) = y := by
    intro y
    rw [shift_cast t]; push_cast
    have h0 : ((t % d : ℕ) : ZMod (d * m)) * m + ((d - t % d : ℕ) : ZMod (d * m)) * m = 0 := by
      rw [← add_mul]
      have he : (((t % d : ℕ) : ZMod (d * m)) + ((d - t % d : ℕ) : ZMod (d * m)))
          = ((d : ℕ) : ZMod (d * m)) := by
        rw [← Nat.cast_add]; congr 1; omega
      rw [he, show ((d : ℕ) : ZMod (d * m)) * m = ((d * m : ℕ) : ZMod (d * m)) by push_cast; ring,
        ZMod.natCast_self]
    rw [add_assoc, h0, add_zero]
  have hcancel_st : ∀ x : ZMod (d * m),
      x + (((d - t % d) * m : ℕ) : ZMod (d * m)) + ((t * m : ℕ) : ZMod (d * m)) = x := by
    intro x
    rw [shift_cast t]; push_cast
    have h0 : ((d - t % d : ℕ) : ZMod (d * m)) * m + ((t % d : ℕ) : ZMod (d * m)) * m = 0 := by
      rw [← add_mul]
      have he : (((d - t % d : ℕ) : ZMod (d * m)) + ((t % d : ℕ) : ZMod (d * m)))
          = ((d : ℕ) : ZMod (d * m)) := by
        rw [← Nat.cast_add]; congr 1; omega
      rw [he, show ((d : ℕ) : ZMod (d * m)) * m = ((d * m : ℕ) : ZMod (d * m)) by push_cast; ring,
        ZMod.natCast_self]
    rw [add_assoc, h0, add_zero]
  apply Finset.card_nbij'
    (i := fun x => x + (((d - t % d) * m : ℕ) : ZMod (d * m)))
    (j := fun y => y + ((t * m : ℕ) : ZMod (d * m)))
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hxR, hxlev⟩ := hx
    obtain ⟨y, hyS, rfl⟩ := (mem_rhoPow t S x).mp hxR
    simp only [Finset.mem_coe, Finset.mem_filter, hcancel_ts y]
    refine ⟨hyS, ?_⟩
    have hlev := level_add hd hm t y
    rw [hxlev] at hlev
    have hqd : y.val / m < d := level_lt hd hm y
    exact cyc_inv (y.val / m) (t % d) j d hd hqd ht'd hj hlev
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨hyS, hylev⟩ := hy
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(mem_rhoPow t S _).mpr ⟨y, hyS, rfl⟩, ?_⟩
    rw [level_add hd hm t y, hylev]
    exact cyc_round j (t % d) d hd hj ht'd
  · intro x hx
    exact hcancel_st x
  · intro y hy
    exact hcancel_ts y

/-! ## Part 4: the period-`d` count sequence and the cycle-lemma bridge. -/

open Cycle

/-- The period-`d` natural count sequence: `aP S l = cnt S (l % d)`. -/
def aP {d m : ℕ} (S : Finset (ZMod (d * m))) (l : ℕ) : ℕ := cnt S (l % d)

/-- The integer complement sequence whose partial sums drive the cycle lemma:
    `bSeq S l = 1 - (aP S l : ℤ)`. -/
def bSeq {d m : ℕ} (S : Finset (ZMod (d * m))) (l : ℕ) : ℤ := 1 - (aP S l : ℤ)

lemma aP_lt {d m : ℕ} (S : Finset (ZMod (d * m))) {l : ℕ} (hl : l < d) :
    aP S l = cnt S l := by unfold aP; rw [Nat.mod_eq_of_lt hl]

lemma bSeq_periodic {d m : ℕ} (S : Finset (ZMod (d * m))) (k : ℕ) :
    bSeq S (k + d) = bSeq S k := by
  unfold bSeq aP; rw [Nat.add_mod_right]

/-- Period sum of `aP` is `S.card`. -/
lemma sum_aP {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m))) :
    ∑ l ∈ Finset.range d, (aP S l : ℤ) = (S.card : ℤ) := by
  rw [← Nat.cast_sum]
  congr 1
  rw [← sum_cnt hd hm S]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hl
  exact aP_lt S hl

/-- Period sum of `bSeq` over `range d` is `d - S.card`. -/
lemma Q_bSeq_d {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m))) :
    Q (bSeq S) d = (d : ℤ) - (S.card : ℤ) := by
  unfold Q bSeq
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      sum_aP hd hm S]

/-- For a `(d-1)`-subset, the period sum of `bSeq` is exactly `1`. -/
lemma Q_bSeq_d_one {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m)))
    (hcard : S.card = d - 1) : Q (bSeq S) d = 1 := by
  rw [Q_bSeq_d hd hm S, hcard]
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
    have hle : 1 ≤ d := hd
    rw [Nat.cast_sub hle, Nat.cast_one]
  rw [h1]; ring

/-- The integer partial sum `Q (bSeq S) k = k - (∑_{l<k} aP S l)`. -/
lemma Q_bSeq_eq {d m : ℕ} (S : Finset (ZMod (d * m))) (k : ℕ) :
    Q (bSeq S) k = (k : ℤ) - ∑ l ∈ Finset.range k, (aP S l : ℤ) := by
  unfold Q bSeq
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Periodicity of the partial sums of `bSeq` for a `(d-1)`-subset. -/
lemma Q_bSeq_period {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m)))
    (hcard : S.card = d - 1) (k : ℕ) : Q (bSeq S) (k + d) = Q (bSeq S) k + 1 := by
  have hper : ∀ j, bSeq S (j + d) = bSeq S j := bSeq_periodic S
  have hsum : Q (bSeq S) d = 1 := Q_bSeq_d_one hd hm S hcard
  exact Q_periodic (bSeq S) hper hsum k

/-! ## Part 5: the core equivalence `LevelCanonical ↔ Good`. -/

/-- The prefix sum of the rotated count is a shifted window of `aP`.
    For `t < d` and `j < d`, with `e = d - t`. -/
lemma prefix_rhoPow {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (t : ℕ) (ht : t < d)
    (S : Finset (ZMod (d * m))) (j : ℕ) (hj : j < d) :
    ∑ l ∈ Finset.range (j + 1), ((cnt (rhoPow t S) l : ℤ))
      = ∑ l ∈ Finset.range (j + 1), (aP S (l + (d - t)) : ℤ) := by
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hl
  have hld : l < d := by omega
  have hkey := cnt_rhoPow hd hm t S l hld
  rw [Nat.mod_eq_of_lt ht] at hkey
  -- cnt (rhoPow t S) l = cnt S ((l + (d-t)) % d) = aP S (l + (d-t))
  have heq : cnt (rhoPow t S) l = aP S (l + (d - t)) := by
    rw [hkey]; rfl
  rw [heq]

/-- Reindex: `∑_{l<j+1} f (l + e) = (∑_{l<e+j+1} f) - (∑_{l<e} f)`. -/
lemma sum_shift_window (f : ℕ → ℤ) (e j : ℕ) :
    ∑ l ∈ Finset.range (j + 1), f (l + e)
      = (∑ l ∈ Finset.range (e + (j + 1)), f l) - (∑ l ∈ Finset.range e, f l) := by
  have hIco : ∑ l ∈ Finset.range (j + 1), f (l + e)
      = ∑ l ∈ Finset.Ico e (e + (j + 1)), f l := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by congr 1; omega)
    intro l _; rw [Nat.add_comm e l]
  have hcons : (∑ l ∈ Finset.Ico 0 e, f l) + (∑ l ∈ Finset.Ico e (e + (j + 1)), f l)
      = ∑ l ∈ Finset.Ico 0 (e + (j + 1)), f l :=
    Finset.sum_Ico_consecutive f (Nat.zero_le e) (by omega : e ≤ e + (j + 1))
  rw [hIco, Finset.range_eq_Ico, Finset.range_eq_Ico]
  linarith [hcons]

/-- The LC prefix inequality (index `j`) for `rhoPow t S`, recast via partial sums of `bSeq`.
    For `t < d`, `j < d`, with `e = d - t`:
    `(#{i ∈ rhoPow t S : level i ≤ j} ≤ j)  ↔  Q b e < Q b (e + (j+1))`. -/
lemma lc_index_iff {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (t : ℕ) (ht : t < d)
    (S : Finset (ZMod (d * m))) (j : ℕ) (hj : j < d) :
    (((rhoPow t S).filter (fun i => i.val / m ≤ j)).card ≤ j)
      ↔ Q (bSeq S) (d - t) < Q (bSeq S) ((d - t) + (j + 1)) := by
  set e := d - t with he
  -- cast the LC inequality to ℤ
  rw [show (((rhoPow t S).filter (fun i => i.val / m ≤ j)).card ≤ j)
        ↔ (((rhoPow t S).filter (fun i => i.val / m ≤ j)).card : ℤ) ≤ (j : ℤ) from by
      exact_mod_cast Iff.rfl]
  -- prefix card of rhoPow t S = window sum of aP
  have hpref : (((rhoPow t S).filter (fun i => i.val / m ≤ j)).card : ℤ)
      = ∑ l ∈ Finset.range (j + 1), (aP S (l + e) : ℤ) := by
    rw [prefix_cnt (rhoPow t S) j]
    push_cast
    rw [prefix_rhoPow hd hm t ht S j hj]
  rw [hpref, sum_shift_window (fun l => (aP S l : ℤ)) e j]
  -- now: (Qa(e+j+1) - Qa e ≤ j) ↔ (Q b e < Q b (e+j+1))
  rw [show ∑ l ∈ Finset.range (e + (j + 1)), (aP S l : ℤ)
        = (↑(e + (j + 1)) : ℤ) - Q (bSeq S) (e + (j + 1)) from by
      have := Q_bSeq_eq S (e + (j + 1)); linarith,
      show ∑ l ∈ Finset.range e, (aP S l : ℤ) = (e : ℤ) - Q (bSeq S) e from by
      have := Q_bSeq_eq S e; linarith]
  push_cast
  constructor <;> intro h <;> linarith

/-- Cross-equality relating `Q b e` to `Q b c` where `c = e % d` and `e ≤ d`
    (so `e = c`, or `e = d` with `c = 0`). -/
lemma Q_e_c_cross {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m)))
    (hcard : S.card = d - 1) (t : ℕ) (ht : t < d) (x : ℕ) :
    Q (bSeq S) (d - t) + Q (bSeq S) ((d - t) % d + x)
      = Q (bSeq S) ((d - t) % d) + Q (bSeq S) ((d - t) + x) := by
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · -- t = 0 : e = d, c = 0
    subst ht0
    simp only [Nat.sub_zero]
    rw [Nat.mod_self]
    -- Q b d + Q b (0 + x) = Q b 0 + Q b (d + x)
    have hp1 : Q (bSeq S) d = Q (bSeq S) 0 + 1 := by
      have := Q_bSeq_period hd hm S hcard 0; simpa using this
    have hp2 : Q (bSeq S) (d + x) = Q (bSeq S) x + 1 := by
      have := Q_bSeq_period hd hm S hcard x
      rw [Nat.add_comm x d] at this; exact this
    rw [hp1, hp2, Nat.zero_add]; ring
  · -- t > 0 : e = d - t < d, so c = e
    have helt : d - t < d := by omega
    rw [Nat.mod_eq_of_lt helt]

/-- **The cycle-lemma bridge (single rotation).** For `t < d` and a `(d-1)`-subset `S`,
    `LevelCanonical d m (rhoPow t S) ↔ Good d (bSeq S) ((d - t) % d)`. -/
lemma lc_iff_good {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m)))
    (hcard : S.card = d - 1) (t : ℕ) (ht : t < d) :
    LevelCanonical d m (rhoPow t S) ↔ Good d (bSeq S) ((d - t) % d) := by
  set e := d - t with he
  set c := e % d with hc
  -- LC ↔ ∀ j < d, Q b e < Q b (e + (j+1))
  have hLCiff : LevelCanonical d m (rhoPow t S)
      ↔ ∀ j, j < d → Q (bSeq S) e < Q (bSeq S) (e + (j + 1)) := by
    unfold LevelCanonical
    constructor
    · intro h j hj
      exact (lc_index_iff hd hm t ht S j hj).mp (h j hj)
    · intro h j hj
      exact (lc_index_iff hd hm t ht S j hj).mpr (h j hj)
  rw [hLCiff]
  -- relate e-form to c-form via cross equality, and drop the trivial j = d-1
  unfold Good
  constructor
  · -- forward: from ∀ j < d (e-form), prove Good at c
    intro h s hcs hsd
    -- s = c + (s - c), with s - c = j + 1, j < d - 1 hence j < d
    obtain ⟨w, hw⟩ : ∃ w, s = c + (w + 1) := ⟨s - c - 1, by omega⟩
    have hwd : w < d := by
      have hcd : c < d := Nat.mod_lt _ hd
      omega
    have hcross := Q_e_c_cross hd hm S hcard t ht (w + 1)
    have he_lt := h w hwd
    rw [hw]
    -- from he_lt : Q b e < Q b (e + (w+1)); cross : Q b e + Q b (c+(w+1)) = Q b c + Q b (e+(w+1))
    have : Q (bSeq S) e + Q (bSeq S) (c + (w + 1))
        = Q (bSeq S) c + Q (bSeq S) (e + (w + 1)) := hcross
    linarith
  · -- backward: from Good at c, prove ∀ j < d (e-form)
    intro h j hj
    rcases Nat.lt_or_ge j (d - 1) with hjlt | hjge
    · -- j < d - 1 : s = c + (j+1) is in window (c, c+d)
      have hcd : c < d := Nat.mod_lt _ hd
      have hgs := h (c + (j + 1)) (by omega) (by omega)
      have hcross := Q_e_c_cross hd hm S hcard t ht (j + 1)
      have : Q (bSeq S) e + Q (bSeq S) (c + (j + 1))
          = Q (bSeq S) c + Q (bSeq S) (e + (j + 1)) := hcross
      linarith
    · -- j = d - 1 : automatic from periodicity, Q b (e + d) = Q b e + 1
      have hjeq : j = d - 1 := by omega
      subst hjeq
      have hrw : e + (d - 1 + 1) = e + d := by omega
      rw [hrw, Q_bSeq_period hd hm S hcard e]
      linarith

/-! ## Part 7: the unique canonical rotation index. -/

/-- `σ t = (d - t) % d` is `< d`. -/
lemma sigma_lt {d : ℕ} (hd : 0 < d) (t : ℕ) : (d - t) % d < d := Nat.mod_lt _ hd

/-- `σ` is an involution on `[0, d)`: `(d - ((d - t) % d)) % d = t` for `t < d`. -/
lemma sigma_invol {d : ℕ} (_hd : 0 < d) {t : ℕ} (ht : t < d) :
    (d - ((d - t) % d)) % d = t := by
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0; simp [Nat.mod_self]
  · have h1 : d - t < d := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : d - (d - t) = t := by omega
    rw [h2, Nat.mod_eq_of_lt ht]

/-- **The unique canonical rotation.** For a `(d-1)`-subset `S`, exactly one `t ∈ [0,d)`
    makes `rhoPow t S` level-canonical. -/
theorem canonical_unique {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m)))
    (hcard : S.card = d - 1) :
    ∃! t, t < d ∧ LevelCanonical d m (rhoPow t S) := by
  -- apply the cycle lemma to bSeq S
  have hper : ∀ k, bSeq S (k + d) = bSeq S k := bSeq_periodic S
  have hsum : Q (bSeq S) d = 1 := Q_bSeq_d_one hd hm S hcard
  obtain ⟨i0, ⟨hi0d, hi0good⟩, hi0uniq⟩ := cycle_lemma (bSeq S) hd hper hsum
  refine ⟨(d - i0) % d, ⟨sigma_lt hd i0, ?_⟩, ?_⟩
  · -- LC at t0 = σ i0
    rw [lc_iff_good hd hm S hcard _ (sigma_lt hd i0)]
    rw [sigma_invol hd hi0d]
    exact hi0good
  · -- uniqueness
    rintro t ⟨htd, htLC⟩
    rw [lc_iff_good hd hm S hcard t htd] at htLC
    -- htLC : Good d (bSeq S) ((d - t) % d)
    have hgood_idx : (d - t) % d = i0 := hi0uniq ((d - t) % d) ⟨sigma_lt hd t, htLC⟩
    -- t = σ ((d-t)%d) = σ i0 = (d - i0) % d
    have := sigma_invol hd htd
    rw [hgood_idx] at this
    omega

/-! ## Part 8: the bijection `{(d-1)-subsets} ≃ {canonical} × Fin d`. -/

open Classical in
/-- The canonical rotation index of a `(d-1)`-subset (junk `0` for non-`(d-1)`-subsets). -/
noncomputable def canIdx {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m))) : ℕ :=
  if h : S.card = d - 1 then (canonical_unique hd hm S h).choose else 0

lemma canIdx_spec {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m)))
    (hcard : S.card = d - 1) :
    canIdx hd hm S < d ∧ LevelCanonical d m (rhoPow (canIdx hd hm S) S) := by
  unfold canIdx
  rw [dif_pos hcard]
  exact (canonical_unique hd hm S hcard).choose_spec.1

/-- Uniqueness characterization of `canIdx`. -/
lemma canIdx_eq {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (S : Finset (ZMod (d * m)))
    (hcard : S.card = d - 1) {t : ℕ} (htd : t < d) (htLC : LevelCanonical d m (rhoPow t S)) :
    t = canIdx hd hm S := by
  unfold canIdx
  rw [dif_pos hcard]
  exact (canonical_unique hd hm S hcard).choose_spec.2 t ⟨htd, htLC⟩

/-- For a canonical `(d-1)`-subset, the canonical index is `0`. -/
lemma canIdx_of_canonical {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (c : Finset (ZMod (d * m)))
    (hcard : c.card = d - 1) (hLC : LevelCanonical d m c) : canIdx hd hm c = 0 := by
  symm
  apply canIdx_eq hd hm c hcard hd
  rw [rhoPow_zero]; exact hLC

/-- `rhoPow` is "mod-d periodic with the round-trip cancelling to identity". -/
lemma rhoPow_round {d m : ℕ} (t : ℕ) (ht : t < d) (S : Finset (ZMod (d * m))) :
    rhoPow ((d - t) % d) (rhoPow t S) = S := by
  rw [rhoPow_add, ← rhoPow_mod]
  have : ((d - t) % d + t) % d = 0 := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0; simp [Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega : d - t < d)]
      have : d - t + t = d := by omega
      rw [this, Nat.mod_self]
  rw [this, rhoPow_zero]

variable {d m : ℕ}

/-- The Fintype subtype of `(d-1)`-subsets. -/
abbrev Asub (d m : ℕ) := {S : Finset (ZMod (d * m)) // S.card = d - 1}

/-- The Fintype subtype of canonical `(d-1)`-subsets (the TARGET). -/
abbrev Csub (d m : ℕ) := {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S}

open Classical in
/-- The bijection `Asub ≃ Csub × Fin d`. -/
noncomputable def equivCanFin (hd : 0 < d) (hm : 0 < m) : Asub d m ≃ Csub d m × Fin d where
  toFun := fun S =>
    (⟨rhoPow (canIdx hd hm S.1) S.1,
        ⟨by rw [card_rhoPow]; exact S.2, (canIdx_spec hd hm S.1 S.2).2⟩⟩,
      ⟨canIdx hd hm S.1, (canIdx_spec hd hm S.1 S.2).1⟩)
  invFun := fun p =>
    ⟨rhoPow ((d - (p.2 : ℕ)) % d) p.1.1, by rw [card_rhoPow]; exact p.1.2.1⟩
  left_inv := by
    rintro ⟨S, hS⟩
    apply Subtype.ext
    simp only
    exact rhoPow_round (canIdx hd hm S) (canIdx_spec hd hm S hS).1 S
  right_inv := by
    rintro ⟨⟨c, hc1, hc2⟩, s, hs⟩
    -- T := rhoPow ((d - s) % d) c
    set e := (d - (s : ℕ)) % d with he
    have hcard_T : (rhoPow e c).card = d - 1 := by rw [card_rhoPow]; exact hc1
    -- canIdx of T = s, and rhoPow (canIdx T) T = c
    have hsd : (s : ℕ) < d := hs
    have hed : e < d := Nat.mod_lt _ hd
    -- s makes rhoPow s T = rhoPow s (rhoPow e c) = rhoPow (s + e) c = c canonical
    have hsT_LC : LevelCanonical d m (rhoPow (s : ℕ) (rhoPow e c)) := by
      rw [rhoPow_add]
      have hmod0 : ((s : ℕ) + e) % d = 0 := by
        rw [he]
        rcases Nat.eq_zero_or_pos (s : ℕ) with h0 | hpos
        · rw [h0]; simp [Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega : d - (s : ℕ) < d)]
          have : (s : ℕ) + (d - (s : ℕ)) = d := by omega
          rw [this, Nat.mod_self]
      rw [← rhoPow_mod, hmod0, rhoPow_zero]
      exact hc2
    have hcanT : (s : ℕ) = canIdx hd hm (rhoPow e c) :=
      canIdx_eq hd hm (rhoPow e c) hcard_T hsd hsT_LC
    -- now build the pair equality
    apply Prod.ext
    · -- first component: rhoPow (canIdx T) T = c (as Csub element)
      apply Subtype.ext
      simp only
      rw [← hcanT, rhoPow_add]
      have hmod0 : ((s : ℕ) + e) % d = 0 := by
        rw [he]
        rcases Nat.eq_zero_or_pos (s : ℕ) with h0 | hpos
        · rw [h0]; simp [Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega : d - (s : ℕ) < d)]
          have : (s : ℕ) + (d - (s : ℕ)) = d := by omega
          rw [this, Nat.mod_self]
      rw [← rhoPow_mod, hmod0, rhoPow_zero]
    · -- second component: canIdx T = s (as Fin d)
      apply Fin.ext
      simp only
      exact hcanT.symm

/-! ## Part 9: the final count. -/

/-- **PRIMARY.** `d · #{canonical (d-1)-subsets} = C(d*m, d-1)`. -/
theorem card_levelCanonical_mul (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    d * Fintype.card {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S}
      = (d * m).choose (d - 1) := by
  haveI : NeZero (d * m) := ⟨by positivity⟩
  -- card Asub = card Csub * d  via the bijection
  have hbij : Fintype.card (Asub d m) = Fintype.card (Csub d m × Fin d) :=
    Fintype.card_congr (equivCanFin hd hm)
  rw [Fintype.card_prod, Fintype.card_fin] at hbij
  -- card Asub = C(d*m, d-1)
  have hA : Fintype.card (Asub d m) = (d * m).choose (d - 1) := by
    unfold Asub
    rw [card_kSubsets (d * m) (d - 1)]
  -- combine
  rw [hA] at hbij
  -- hbij : C(d*m,d-1) = card Csub * d
  rw [Nat.mul_comm d _]
  exact hbij.symm

/-- **COROLLARY.** `#{canonical (d-1)-subsets} = C(d*m, d-1) / d`. -/
theorem card_levelCanonical (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Fintype.card {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S}
      = (d * m).choose (d - 1) / d :=
  (Nat.div_eq_of_eq_mul_right hd (card_levelCanonical_mul d m hd hm).symm).symm

end CriticalPortraits
