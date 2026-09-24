/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Spectral.CertFamily

/-!
# Off-diagonal Gram entries

Sections 11.2 and 11.3 of `bs_lambda.txt`.

Let `F : CertFamily V ι` and let `x ≠ y` be two positive inputs of `F.ind`, with owners
`i = owner x` and `j = owner y`.  Write `G = gram F.ind`, so that `G x y` counts the
common negative Hamming neighbours of `x` and `y`.

Two pure cube-geometry lemmas come first: a common neighbour of `x ≠ y` forces
`y = x^{p,q}` for two distinct coordinates `p ≠ q`, and then the only possible common
neighbours are the two midpoints `x^p` and `x^q`.

The classification itself is `exists_flip_pair_of_gram_ne_zero`: for a nonzero off-diagonal
entry the owners differ, one of the two flipped coordinates is the (unique) conflict
coordinate `q` of `C_i` and `C_j`, and the other one, `p`, is fixed by exactly one of the
two certificates.  Everything else in the file is a consequence:

* `gram_eq_zero_of_owner_eq` — if `i = j` then `G x y = 0`;
* `gram_le_one` — for `x ≠ y` always `G x y ≤ 1`;
* `dist_eq_one_or_dist_eq_one` — if `G x y ≠ 0` then `dist(x, C_j) = 1` or `dist(y, C_i) = 1`;
* `exists_flip_pair_of_dist_eq_one` — in the first case the ambiguity in `p` is resolved:
  `C_i` fixes `p` and `C_j` does not;
* `dist_eq_two_of_dist_eq_one` — in the first case `dist(y, C_i) = 2` (so in particular the
  two alternatives above are exclusive) and `x = π_{C_i}(y)`, the column bound of
  Section 11.3;
* `exists_flip_proj` — in the first case `y = (π_{C_j} x)^p` with `p` fixed by `C_i`
  (the row bound of Section 11.3);
* `exists_flip_proj_self` — and `x = (π_{C_j} x)^q` is another such flip, which is what
  produces the `c - 1` rather than `c` in the row bound.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Cube geometry

The two facts about the Boolean cube that drive the whole classification: a pair of points
with a common neighbour is a two-coordinate flip, and such a pair has only the two obvious
common neighbours.
-/

/-- Two distinct inputs with a common Hamming neighbour differ in exactly two
coordinates (Section 11.2). -/
theorem exists_pair_of_common_nbr {x y z : Input V} (hxy : x ≠ y)
    (hxz : hammingDist x z = 1) (hyz : hammingDist y z = 1) :
    ∃ p q : V, p ≠ q ∧ y = flipSet x {p, q} := by
  obtain ⟨p, rfl⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one hxz
  obtain ⟨q, hq⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one hyz
  have hpq : p ≠ q := by
    rintro rfl
    exact hxy (flipSet_left_inj.mp hq)
  refine ⟨p, q, hpq, ?_⟩
  rw [← flipSet_singleton_flipSet_singleton x hpq, hq, flipSet_flipSet]

/-- The only common Hamming neighbours of `x` and its two-coordinate flip `x^{p,q}` are the
two midpoints `x^p` and `x^q`: a third one would sit at distance three from `x^{p,q}`
(Section 11.2). -/
theorem eq_flipSet_singleton_of_common_nbr {x z : Input V} {p q : V} (hpq : p ≠ q)
    (hxz : hammingDist x z = 1) (hyz : hammingDist (flipSet x {p, q}) z = 1) :
    z = flipSet x {p} ∨ z = flipSet x {q} := by
  obtain ⟨r, rfl⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one hxz
  rw [hammingDist_flipSet_flipSet] at hyz
  have hr : r ∈ ({p, q} : Finset V) := by
    by_contra hr
    have hd : Disjoint ({p, q} : Finset V) {r} := Finset.disjoint_singleton_right.2 hr
    rw [(symmDiff_eq_sup _ _).2 hd, Finset.sup_eq_union, Finset.card_union_of_disjoint hd,
      Finset.card_pair hpq, Finset.card_singleton] at hyz
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  exacts [Or.inl rfl, Or.inr rfl]

namespace CertFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)

/-- Two distinct positive inputs with the same owner have no common negative neighbour:
both flipped coordinates are free for the common owner, so both midpoints stay inside
its certificate and are therefore positive (Section 11.2, case `i = j`). -/
theorem gram_eq_zero_of_owner_eq {x y : Ones F.ind} (hxy : x ≠ y)
    (h : F.owner x = F.owner y) : gram F.ind x y = 0 := by
  by_contra hne
  obtain ⟨z, hxz, hyz⟩ := gram_ne_zero_iff.1 hne
  obtain ⟨p, q, hpq, hy⟩ := exists_pair_of_common_nbr (Subtype.coe_injective.ne hxy) hxz hyz
  have hxs := F.owner_sat x
  have hys : (F.P (F.owner x)).Sat y.1 := h ▸ F.owner_sat y
  -- Either midpoint is a free flip of `x`, hence positive, contradicting `z.2`.
  have key {r : V} (hr : r ∈ ({p, q} : Finset V)) (hz : z.1 = flipSet x.1 {r}) : False :=
    PartialAssign.notMem_fixedSet_of_apply_ne hxs hys (hy ▸ ne_flipSet_apply hr)
      (F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hxs (hz ▸ z.2))
  rcases eq_flipSet_singleton_of_common_nbr hpq hxz (hy ▸ hyz) with h1 | h1
  · exact key (Finset.mem_insert_self p {q}) h1
  · exact key (by simp) h1

/-- A nonzero off-diagonal Gram entry forces distinct owners (Section 11.2). -/
theorem owner_ne_of_gram_ne_zero {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) : F.owner x ≠ F.owner y :=
  fun h ↦ hne (F.gram_eq_zero_of_owner_eq hxy h)

/-- A point at distance one from another point's certificate is not that point, since every
point satisfies its own certificate.  This is why the oriented lemmas below take no
separate `x ≠ y` hypothesis (Section 11.2). -/
theorem ne_of_dist_eq_one {x y : Ones F.ind} (hd : (F.P (F.owner y)).dist x.1 = 1) : x ≠ y := by
  rintro rfl
  rw [PartialAssign.dist_eq_zero_iff.2 (F.owner_sat x)] at hd
  omega

/-- The classification of Section 11.2, run at the midpoint `x^a` that is known to be
negative.  Only `exists_flip_pair_of_gram_ne_zero` uses it, twice: once for each of the two
midpoints. -/
private theorem exists_flip_pair_of_ind_flipSet_singleton_eq_false {x y : Ones F.ind}
    (hij : F.owner x ≠ F.owner y) {a b : V} (hab : a ≠ b) (hyf : y.1 = flipSet x.1 {a, b})
    (hfalse : F.ind (flipSet x.1 {a}) = false) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧
      ((p ∈ (F.P (F.owner x)).fixedSet ∧ p ∉ (F.P (F.owner y)).fixedSet) ∨
        (p ∈ (F.P (F.owner y)).fixedSet ∧ p ∉ (F.P (F.owner x)).fixedSet)) := by
  have hxs := F.owner_sat x
  have hys := F.owner_sat y
  -- Undoing the `b`-half of the pair flip turns `y` into the same negative midpoint.
  have hswap : flipSet y.1 {b} = flipSet x.1 {a} := by
    rw [hyf, flipSet_pair_flipSet_singleton _ hab]
  have hai := F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hxs hfalse
  have hbj := F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hys (hswap ▸ hfalse)
  have hne_a : x.1 a ≠ y.1 a := hyf ▸ ne_flipSet_apply (Finset.mem_insert_self a {b})
  have hne_b : x.1 b ≠ y.1 b := hyf ▸ ne_flipSet_apply (by simp)
  have hr := F.conflict_conflictCoord hij
  -- Outside `{a, b}` the two points agree, so the conflict coordinate lies inside it.
  have hrmem : F.conflictCoord hij = a ∨ F.conflictCoord hij = b := by
    by_contra hc
    push Not at hc
    refine hr.ne hxs hys ?_
    rw [hyf, flipSet_apply_of_notMem (by simp [hc.1, hc.2])]
  rcases hrmem with hra | hrb
  · refine ⟨b, a, hab.symm, hra ▸ hr, ?_, Or.inr ⟨hbj, fun hbi ↦ hab.symm ?_⟩⟩
    · rw [hyf, Finset.pair_comm]
    · exact (F.eq_conflictCoord hij
        (PartialAssign.conflict_of_mem_fixedSet hxs hys hbi hbj hne_b)).trans hra
  · refine ⟨a, b, hab, hrb ▸ hr, hyf, Or.inl ⟨hai, fun haj ↦ hab ?_⟩⟩
    exact (F.eq_conflictCoord hij
      (PartialAssign.conflict_of_mem_fixedSet hxs hys hai haj hne_a)).trans hrb

/-- **Classification of a nonzero off-diagonal Gram entry** (Section 11.2).  The two
inputs differ in exactly two coordinates `p ≠ q`; the coordinate `q` is the unique
conflict of the two owners' certificates, and the other coordinate `p` is fixed by
exactly one of them. -/
theorem exists_flip_pair_of_gram_ne_zero {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧
      ((p ∈ (F.P (F.owner x)).fixedSet ∧ p ∉ (F.P (F.owner y)).fixedSet) ∨
        (p ∈ (F.P (F.owner y)).fixedSet ∧ p ∉ (F.P (F.owner x)).fixedSet)) := by
  obtain ⟨z, hxz, hyz⟩ := gram_ne_zero_iff.1 hne
  obtain ⟨p, q, hpq, hyf⟩ := exists_pair_of_common_nbr (Subtype.coe_injective.ne hxy) hxz hyz
  have hij := F.owner_ne_of_gram_ne_zero hxy hne
  -- Whichever of the two midpoints `z` is, it is negative.
  rcases eq_flipSet_singleton_of_common_nbr hpq hxz (hyf ▸ hyz) with h1 | h1
  · exact F.exists_flip_pair_of_ind_flipSet_singleton_eq_false hij hpq hyf (h1 ▸ z.2)
  · refine F.exists_flip_pair_of_ind_flipSet_singleton_eq_false hij hpq.symm ?_ (h1 ▸ z.2)
    rw [hyf, Finset.pair_comm]

/-- Of the two midpoints between `x` and `y = x^{p,q}`, at least one is positive: some
certificate containing `x` or `y` leaves `p` or `q` free, because otherwise `p` and `q`
would both be conflict coordinates of the two owners (Section 11.2). -/
theorem ind_flipSet_singleton_eq_true_or {x y : Ones F.ind} {p q : V} (hpq : p ≠ q)
    (hy : y.1 = flipSet x.1 {p, q}) :
    F.ind (flipSet x.1 {p}) = true ∨ F.ind (flipSet x.1 {q}) = true := by
  have hxs := F.owner_sat x
  have hys := F.owner_sat y
  have hne_p : x.1 p ≠ y.1 p := hy ▸ ne_flipSet_apply (Finset.mem_insert_self p {q})
  have hne_q : x.1 q ≠ y.1 q := hy ▸ ne_flipSet_apply (by simp)
  have hfree : p ∉ (F.P (F.owner x)).fixedSet ∨ q ∉ (F.P (F.owner x)).fixedSet ∨
      p ∉ (F.P (F.owner y)).fixedSet ∨ q ∉ (F.P (F.owner y)).fixedSet := by
    by_contra hc
    push Not at hc
    obtain ⟨hpi, hqi, hpj, hqj⟩ := hc
    by_cases hij : F.owner x = F.owner y
    · exact PartialAssign.notMem_fixedSet_of_apply_ne hxs (hij ▸ hys) hne_p hpi
    · exact hpq ((F.eq_conflictCoord hij
        (PartialAssign.conflict_of_mem_fixedSet hxs hys hpi hpj hne_p)).trans
        (F.eq_conflictCoord hij
          (PartialAssign.conflict_of_mem_fixedSet hxs hys hqi hqj hne_q)).symm)
  -- Flipping `y` at one of the two coordinates lands on the other midpoint of `x`.
  have hyq : flipSet y.1 {q} = flipSet x.1 {p} := by
    rw [hy, flipSet_pair_flipSet_singleton _ hpq]
  have hyp : flipSet y.1 {p} = flipSet x.1 {q} := by
    rw [hy, Finset.pair_comm, flipSet_pair_flipSet_singleton _ hpq.symm]
  rcases hfree with h | h | h | h
  · exact Or.inl (F.ind_flipSet_singleton_eq_true hxs h)
  · exact Or.inr (F.ind_flipSet_singleton_eq_true hxs h)
  · exact Or.inr (hyp ▸ F.ind_flipSet_singleton_eq_true hys h)
  · exact Or.inl (hyq ▸ F.ind_flipSet_singleton_eq_true hys h)

/-- Distinct positive inputs have at most one common negative neighbour: the two candidates
are the midpoints `x^p` and `x^q`, and by `ind_flipSet_singleton_eq_true_or` at most one of
them is negative (Section 11.2). -/
theorem gram_le_one {x y : Ones F.ind} (hxy : x ≠ y) : gram F.ind x y ≤ 1 := by
  rw [gram_apply, Nat.cast_le_one, Finset.card_le_one]
  intro z hz w hw
  rw [Finset.mem_filter_univ] at hz hw
  obtain ⟨p, q, hpq, hy⟩ := exists_pair_of_common_nbr (Subtype.coe_injective.ne hxy) hz.1 hz.2
  have hboth : ¬(F.ind (flipSet x.1 {p}) = false ∧ F.ind (flipSet x.1 {q}) = false) := by
    rcases F.ind_flipSet_singleton_eq_true_or hpq hy with h | h <;> simp [h]
  rcases eq_flipSet_singleton_of_common_nbr hpq hz.1 (hy ▸ hz.2) with hz1 | hz1 <;>
    rcases eq_flipSet_singleton_of_common_nbr hpq hw.1 (hy ▸ hw.2) with hw1 | hw1
  · exact Subtype.ext (hz1.trans hw1.symm)
  · exact absurd ⟨hz1 ▸ z.2, hw1 ▸ w.2⟩ hboth
  · exact absurd ⟨hw1 ▸ w.2, hz1 ▸ z.2⟩ hboth
  · exact Subtype.ext (hz1.trans hw1.symm)

/-- Orientation of a nonzero off-diagonal entry: one of the two inputs lies at distance
exactly one from the other's certificate (Section 11.2).  In either case the conflict
coordinate is the only violated literal, by
`PartialAssign.violSet_eq_singleton_of_conflict`. -/
theorem dist_eq_one_or_dist_eq_one {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) :
    (F.P (F.owner y)).dist x.1 = 1 ∨ (F.P (F.owner x)).dist y.1 = 1 := by
  obtain ⟨p, q, -, hconf, hyf, hp⟩ := F.exists_flip_pair_of_gram_ne_zero hxy hne
  -- Flipping is an involution, so `x` is equally the `{p, q}`-flip of `y`.
  have hxf : x.1 = flipSet y.1 {p, q} := by rw [hyf, flipSet_flipSet]
  rcases hp with hpx | hpy
  · refine Or.inl ?_
    rw [PartialAssign.dist_eq_card_violSet, PartialAssign.violSet_eq_singleton_of_conflict
      (F.owner_sat x) (hyf ▸ F.owner_sat y) hconf hpx.2, Finset.card_singleton]
  · refine Or.inr ?_
    rw [PartialAssign.dist_eq_card_violSet, PartialAssign.violSet_eq_singleton_of_conflict
      (F.owner_sat y) (hxf ▸ F.owner_sat x) hconf.symm hpy.2, Finset.card_singleton]

/-- Oriented form of `exists_flip_pair_of_gram_ne_zero`: once it is known which of the two
inputs is the near one, the alternative on `p` is resolved — `C_i` fixes `p` and `C_j` leaves
it free, since otherwise `x` would violate both `p` and `q` of `C_j` (Section 11.3). -/
theorem exists_flip_pair_of_dist_eq_one {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧ p ∈ (F.P (F.owner x)).fixedSet ∧
        p ∉ (F.P (F.owner y)).fixedSet := by
  obtain ⟨p, q, hpq, hconf, hyf, hp⟩ :=
    F.exists_flip_pair_of_gram_ne_zero (F.ne_of_dist_eq_one hd) hne
  refine ⟨p, q, hpq, hconf, hyf, hp.resolve_right fun h ↦ ?_⟩
  obtain ⟨b, hb⟩ := PartialAssign.mem_fixedSet_iff_exists.1 h.1
  have hxp : x.1 p ≠ b := by
    have hyp : y.1 p = b := (F.owner_sat y).eq_of_fixed hb
    rw [hyf, flipSet_apply_of_mem (Finset.mem_insert_self p {q})] at hyp
    rw [← hyp]
    exact (Bool.not_ne_self _).symm
  -- Both `p` and `q` would then be violated literals of `C_j` at `x`, contradicting `hd`.
  have hsub : ({p, q} : Finset V) ⊆ (F.P (F.owner y)).violSet x.1 :=
    Finset.insert_subset (PartialAssign.mem_violSet_iff_exists_ne.2 ⟨b, hb, hxp⟩)
      (Finset.singleton_subset_iff.2 (hconf.mem_violSet (F.owner_sat x)))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hpq, ← PartialAssign.dist_eq_card_violSet, hd] at hcard
  omega

/-- The two alternatives of `dist_eq_one_or_dist_eq_one` are exclusive, and in the oriented
case the reverse distance is exactly two and is realised by the nearest-point projection: `y`
violates both `p` and `q` for `C_i`, and resetting them returns `x` (Section 11.3,
column bound). -/
theorem dist_eq_two_of_dist_eq_one {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    (F.P (F.owner x)).dist y.1 = 2 ∧ x.1 = (F.P (F.owner x)).proj y.1 := by
  obtain ⟨p, q, hpq, hconf, hyf, hpi, -⟩ := F.exists_flip_pair_of_dist_eq_one hne hd
  have hxs := F.owner_sat x
  have hqi : q ∈ (F.P (F.owner x)).fixedSet :=
    PartialAssign.mem_fixedSet_iff_exists.2 (hconf.imp fun _ hb ↦ hb.1)
  have hviol : (F.P (F.owner x)).violSet y.1 = {p, q} := by
    rw [hyf]
    exact PartialAssign.violSet_eq_pair_of_conflict hxs (hyf ▸ F.owner_sat y) hconf hpi
  refine ⟨by rw [PartialAssign.dist_eq_card_violSet, hviol, Finset.card_pair hpq],
    (PartialAssign.proj_eq_of_sat_of_eq_off_fixedSet hxs fun v hv ↦ ?_).symm⟩
  have hvpq : v ∉ ({p, q} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    exacts [hv hpi, hv hqi]
  rw [hyf, flipSet_apply_of_notMem hvpq]

/-- In the oriented case the projection of `x` onto `C_j` is `x^q`, and `y` is obtained
from it by flipping the single coordinate `p`, which is fixed by `C_i`
(Section 11.3, row bound). -/
theorem exists_flip_proj {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    ∃ p ∈ (F.P (F.owner x)).fixedSet, y.1 = flipSet ((F.P (F.owner y)).proj x.1) {p} := by
  obtain ⟨p, q, hpq, hconf, hyf, hpi, -⟩ := F.exists_flip_pair_of_dist_eq_one hne hd
  obtain ⟨v, hv, hx_eq⟩ := PartialAssign.eq_flipSet_proj_of_dist_eq_one hd
  -- `x` satisfies `C_i` and `q` is a conflict, so `q` violates `C_j`; the violation set
  -- is the singleton `{v}`, hence `v = q`.
  have hqv : q = v := by
    have hmem := hconf.mem_violSet (F.owner_sat x)
    rwa [hv, Finset.mem_singleton] at hmem
  subst hqv
  -- Now `y = x^{p,q} = ((π x)^q)^{p,q} = (π x)^p`.
  rw [hx_eq] at hyf
  refine ⟨p, hpi, hyf.trans ?_⟩
  rw [Finset.pair_comm, ← flipSet_singleton_flipSet_singleton _ hpq.symm, flipSet_flipSet]

/-- The point `x` itself is a single flip of its own projection onto `C_j`, namely at the
conflict coordinate, which is fixed by `C_i`.  This removes one option from the row bound
of Section 11.3. -/
theorem exists_flip_proj_self {i j : ι} (hij : i ≠ j) {x : Input V} (hx : (F.P i).Sat x)
    (hd : (F.P j).dist x = 1) :
    ∃ p₀ ∈ (F.P i).fixedSet, x = flipSet ((F.P j).proj x) {p₀} := by
  obtain ⟨v, hviol, hx_eq⟩ := PartialAssign.eq_flipSet_proj_of_dist_eq_one hd
  obtain ⟨b, hb, -⟩ := F.conflict_conflictCoord hij
  -- The violation set is the singleton `{v}` and the conflict coordinate of `C_i` and
  -- `C_j` lies in it, so `v` is that conflict coordinate — in particular `C_i` fixes it.
  have hcv : F.conflictCoord hij = v := by
    have hmem := (F.conflict_conflictCoord hij).mem_violSet hx
    rwa [hviol, Finset.mem_singleton] at hmem
  exact ⟨v, PartialAssign.mem_fixedSet_iff_exists.2 ⟨b, hcv ▸ hb⟩, hx_eq⟩

end CertFamily

end BSLambda
