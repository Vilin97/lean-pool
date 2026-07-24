/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import LeanPool.BooleanIsoperimetry.Compression

/-!
# Upper-shadow and Macaulay layer

This file connects Kruskal-Katona upper-shadow estimates to the Macaulay
exchange inequalities used in Harper's theorem.
-/

open scoped BigOperators

/-
# Upper-shadow / Macaulay layer for Harper's theorem

This module isolates the **Frankl–Füredi / Kruskal–Katona / Macaulay shadow
layer** that the positive-cascade Harper step
(`boundaryCost_le_of_lower_interleaves_step_live` in `Harper.lean`) reduces to.

The central object is the *upper-shadow / excess function*

```
upperShadow N r t = H N (binomPrefix N r + t) - binomPrefix N (r + 1)
```

i.e. the number of vertices that the closed `1`-neighbourhood of the
simplicial initial segment of `binomPrefix N r + t` vertices adds *on top of*
the full Hamming ball of radius `r` (the next full binomial prefix
`binomPrefix N (r+1)`).  Combinatorially `upperShadow N r t` is exactly the size
of the **upper shadow** (the layer-`(r+1)` neighbourhood) of the first `t`
vertices of Hamming layer `r` in the simplicial/colex order, which is the
quantity controlled by Kruskal–Katona/Macaulay.

The provable infrastructure below (`H_shadow_closed_form`, `upperShadow_zero`,
`upperShadow_mono`, `upperShadow_full`, `upperShadow_le_choose`) is sorry-free
and reusable.  The genuine numerical heart of Harper's theorem is then isolated
into the two named scalar leaves `H_shadow_LE_sum` and `H_shadow_GT_sum`, which
are the Macaulay shadow-sum minimisations in the two regimes; via the closed
form these are literally inequalities between sums of `upperShadow` quantities
(see `H_shadow_LE_sum_as_upperShadow`).  These two leaves are *strictly closer to
the Frankl–Füredi proof* than the max-form boundary step: they drop the outer
`max`/boundary-cost wrapper and the four-block profile, and expose the pure
shadow-sum comparison.
-/

namespace BooleanIsoperimetry

/-- **Upper-shadow / excess function.**  For a count `binomPrefix N r + t`
(a full Hamming ball of radius `r-1` plus `t` vertices of layer `r`), this is the
number of vertices the closed neighbourhood adds beyond the full ball of radius
`r`, i.e. the size of the upper shadow of the first `t` vertices of layer `r`. -/
noncomputable def upperShadow (N r t : ℕ) : ℕ :=
  H N (binomPrefix N r + t) - binomPrefix N (r + 1)

/-- **Macaulay closed form for `H` on a partial layer.**  For `1 ≤ r`, the
boundary of a full ball of radius `r-1` plus the first `t` vertices of layer `r`
equals the next full ball `binomPrefix N (r+1)` plus the upper shadow
`upperShadow N r t`.  This is sorry-free: it is just the definition of
`upperShadow` together with the monotonicity bound
`binomPrefix N (r+1) = H N (binomPrefix N r) ≤ H N (binomPrefix N r + t)`. -/
theorem H_shadow_closed_form (N r t : ℕ) (hr : 1 ≤ r) :
    H N (binomPrefix N r + t) = binomPrefix N (r + 1) + upperShadow N r t := by
  unfold upperShadow
  have hbase : H N (binomPrefix N r) = binomPrefix N (r + 1) := H_binomPrefix N r hr
  have hmono : H N (binomPrefix N r) ≤ H N (binomPrefix N r + t) :=
    H_mono (Nat.le_add_right _ _)
  omega

/-- The upper shadow of an empty partial layer is empty. -/
theorem upperShadow_zero (N r : ℕ) (hr : 1 ≤ r) : upperShadow N r 0 = 0 := by
  unfold upperShadow
  rw [Nat.add_zero, H_binomPrefix N r hr, Nat.sub_self]

/-- The upper shadow is monotone in the partial-layer parameter `t`. -/
theorem upperShadow_mono (N r : ℕ) {t t' : ℕ} (h : t ≤ t') :
    upperShadow N r t ≤ upperShadow N r t' := by
  unfold upperShadow
  exact Nat.sub_le_sub_right (H_mono (by omega)) _

/-- A complete layer has upper shadow equal to the full next layer
`Nat.choose N (r+1)`: the upper shadow of all of layer `r` is all of layer
`r+1`. -/
theorem upperShadow_full (N r : ℕ) (hr : 1 ≤ r) :
    upperShadow N r (Nat.choose N r) = Nat.choose N (r + 1) := by
  unfold upperShadow
  have hsucc : binomPrefix N r + Nat.choose N r = binomPrefix N (r + 1) :=
    (binomPrefix_succ N r).symm
  rw [hsucc, H_binomPrefix N (r + 1) (by omega), binomPrefix_succ N (r + 1)]
  omega

/-- Kruskal–Katona/Macaulay upper bound: the upper shadow of a partial layer
never exceeds the full next layer.  Sorry-free monotone consequence of
`upperShadow_full`. -/
theorem upperShadow_le_choose (N r t : ℕ) (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadow N r t ≤ Nat.choose N (r + 1) := by
  calc upperShadow N r t ≤ upperShadow N r (Nat.choose N r) := upperShadow_mono N r ht
    _ = Nat.choose N (r + 1) := upperShadow_full N r hr

/-! ## The Macaulay exchange leaf and its two shadow-sum corollaries

The genuine numerical heart of the positive-cascade Harper step is the
regime-free max-form exchange theorem below.  It says that for `p + q = a + b`
with `(p, q)` the canonical cascade split of the common total, the canonical
cross-boundary cost is no larger than the cost of the arbitrary split `(a, b)`.

The two public `H_shadow_*` statements are max-free regime corollaries of this
single exchange theorem: the positive canonical split collapses the left `max`s
to `H N p + H N q`, and the LE/GT hypotheses collapse the right `max`s to the
advertised sums.  Via `H_shadow_closed_form` (see
`H_shadow_LE_sum_as_upperShadow`) these corollaries are still the upper-shadow
sum comparisons used by the Frankl–Füredi/Kruskal–Katona calculation.
-/

/-- **Positive Frankl–Füredi / Macaulay exchange step.**  For a positive
canonical cascade split `(p, q)` of `a + b` at level `N`, the canonical
cross-boundary cost is at most the cross-boundary cost of the arbitrary split
`(a, b)`.

This is the remaining PDF-layer theorem: the paired Up/Down compression plus the
Macaulay/Kruskal–Katona shadow comparison in the nondegenerate branch.  The
`q = 0` branch is proved separately below by direct cascade arithmetic, and the
full exchange theorem is assembled from the two branches. -/
theorem H_exchange_max_form_pos {N p q a b : ℕ}
    (hpq : CascadeSplit N (a + b) p q) (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (_hq_pos : 1 ≤ q) :
    max (H N p) q + max (H N q) p ≤ max (H N a) b + max (H N b) a := by
  have ha_card : (simplicialInitSeg N a).card = a := by rw [card_simplicialInitSeg, min_eq_left ha]
  have hb_card : (simplicialInitSeg N b).card = b := by rw [card_simplicialInitSeg, min_eq_left hb]
  have hpq_structural :
      CascadeSplit N ((simplicialInitSeg N a).card + (simplicialInitSeg N b).card) p q := by
    rwa [ha_card, hb_card]
  have h_FF := franklFuredi_pairedCompression_exchange (simplicialInitSeg N a)
    (simplicialInitSeg N b) p q hpq_structural
  have hp : p ≤ 2 ^ N := cascade_p_le hpq
  have hq : q ≤ 2 ^ N := cascade_q_le hpq
  rw [PairShadowCost_initSeg_eq_max_H hp hq,
      PairShadowCost_initSeg_eq_max_H ha hb] at h_FF
  exact h_FF

/-- The top coordinate `Fin.last n` never lies in the image of `Fin.castSucc`,
since `Fin.castSucc i < Fin.last n` always. -/
lemma last_not_mem_image_castSucc {n : ℕ} (x : Cube n) :
    Fin.last n ∉ x.image Fin.castSucc := by
  simp only [Finset.mem_image, not_exists, not_and]
  intro i _ h
  exact (Fin.castSucc_lt_last i).ne h

/-- `embed0` is injective: it is `Finset.image` along the injective `Fin.castSucc`. -/
lemma embed0_injective {n : ℕ} : Function.Injective (@embed0 n) :=
  Finset.image_injective (Fin.castSucc_injective n)

/-- `embed1` is injective: it inserts the top coordinate into the image of the
injective `Fin.castSucc`, and that top coordinate is never already present. -/
lemma embed1_injective {n : ℕ} : Function.Injective (@embed1 n) := by
  intro x y h
  unfold embed1 at h
  have key : x.image Fin.castSucc = y.image Fin.castSucc := by
    have := congrArg (·.erase (Fin.last n)) h
    simpa [Finset.erase_insert, last_not_mem_image_castSucc] using this
  exact Finset.image_injective (Fin.castSucc_injective n) key

lemma slice0_union_embed {N a b : ℕ} :
    slice0 ((simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1) =
      simplicialInitSeg N a := by
  ext x
  simp only [slice0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · rwa [embed0_injective hxy] at hy
    · have hlast : Fin.last N ∈ embed1 y := Finset.mem_insert_self _ _
      rw [hxy] at hlast
      exact ((last_not_mem_image_castSucc x) hlast).elim
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

lemma slice1_union_embed {N a b : ℕ} :
    slice1 ((simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1) =
      simplicialInitSeg N b := by
  ext x
  simp only [slice1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · have hlast : Fin.last N ∈ embed1 x := Finset.mem_insert_self _ _
      rw [← hxy] at hlast
      exact ((last_not_mem_image_castSucc y) hlast).elim
    · rwa [embed1_injective hxy] at hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩

lemma disjoint_embed {N a b : ℕ} :
    Disjoint ((simplicialInitSeg N a).image embed0) ((simplicialInitSeg N b).image embed1) := by
  rw [Finset.disjoint_left]
  rintro z hz0 hz1
  simp only [Finset.mem_image] at hz0 hz1
  obtain ⟨x, _, hx⟩ := hz0
  obtain ⟨y, _, hy⟩ := hz1
  have hlast : Fin.last N ∈ embed1 y := Finset.mem_insert_self _ _
  rw [hy, ← hx] at hlast
  exact (last_not_mem_image_castSucc x) hlast

lemma card_embed0 {N a : ℕ} (ha : a ≤ 2 ^ N) :
    ((simplicialInitSeg N a).image embed0).card = a := by
  rw [Finset.card_image_of_injective _ embed0_injective, card_simplicialInitSeg, min_eq_left ha]

lemma card_embed1 {N b : ℕ} (hb : b ≤ 2 ^ N) :
    ((simplicialInitSeg N b).image embed1).card = b := by
  rw [Finset.card_image_of_injective _ embed1_injective, card_simplicialInitSeg, min_eq_left hb]

/-- **Macaulay shadow-sum leaf, LE regime.**  For the canonical cascade split
`(p, q)` of `a + b` with `b ≤ a` and `a ≤ H N b` (the LE regime in which the
outer boundary `max`s collapse to `H N a + H N b`), the canonical boundary sum is
minimal.  Via `H_shadow_closed_form` this is the upper-shadow comparison
`upperShadow N rp tp + upperShadow N rq tq ≤ upperShadow N ra ta + upperShadow N rb tb`
modulo whole layers (see `H_shadow_LE_sum_as_upperShadow`).  This is the genuine
Kruskal–Katona/Macaulay leaf; it is true (verified against the exact cascade model
of `H`, all split dimensions `N ≤ 4`) but its proof is the Frankl–Füredi shadow
calculation, which is now fully formalized and sorry-free. -/
theorem H_shadow_LE_sum {N a b p q : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hcasc : CascadeSplit N (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : a ≤ H N b) :
    H N p + H N q ≤ H N a + H N b := by
  have hp : p ≤ 2 ^ N := cascade_p_le hcasc
  have hq : q ≤ 2 ^ N := cascade_q_le hcasc
  have hmax := H_exchange_max_form_pos hcasc ha hb hq_pos
  rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc,
      boundaryCost_eq_case_le ha hba hcase] at hmax
  exact hmax

/-- **Macaulay shadow-sum leaf, GT regime.**  For the canonical cascade split
`(p, q)` of `a + b` with `b ≤ a` and `H N b < a` (the GT/slack regime in which the
outer boundary `max (H N b) a` collapses to `a`), the canonical boundary sum is
bounded by `H N a + a`.  As with the LE leaf, via `H_shadow_closed_form` this is a
sum comparison of `upperShadow` quantities with the GT slack `a`.  This is the
genuine GT shadow-deficit leaf of Frankl–Füredi; true (cascade-model verified) but
now fully formalized and sorry-free. -/
theorem H_shadow_GT_sum {N a b p q : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hcasc : CascadeSplit N (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H N b < a) :
    H N p + H N q ≤ H N a + a := by
  have hp : p ≤ 2 ^ N := cascade_p_le hcasc
  have hq : q ≤ 2 ^ N := cascade_q_le hcasc
  have hmax := H_exchange_max_form_pos hcasc ha hb hq_pos
  rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc,
      boundaryCost_eq_case_gt ha hba hcase] at hmax
  exact hmax

lemma H_exchange_max_form_q_zero {N a b p : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) (hp : p ≤ 2 ^ N)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit N (a + b) p 0) :
    H N p + p ≤ max (H N a) b + max (H N b) a :=
  harper_bc_min_q_zero_core N ha hb hp hb_le_a hpq hcasc

/-- Regime-free max-form exchange theorem, assembled from the proved degenerate
`q = 0` branch and the positive Frankl–Füredi/Macaulay leaf. -/
theorem H_exchange_max_form {N s p q a b : ℕ}
    (hpq : CascadeSplit N s p q) (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hab : a + b = s) :
    max (H N p) q + max (H N q) p ≤ max (H N a) b + max (H N b) a := by
  subst hab
  have hp : p ≤ 2 ^ N := cascade_p_le hpq
  rcases eq_or_lt_of_le (Nat.zero_le q) with rfl | hq_pos
  · have h_LHS : max (H N p) 0 + max (H N 0) p = H N p + p := by
      rw [H_zero]
      exact congr_arg₂ (· + ·) (max_eq_left (Nat.zero_le _)) (max_eq_right (Nat.zero_le _))
    rw [h_LHS]
    rcases le_total b a with hba | hab'
    · have hp_eq : p = a + b := by
        have : p + 0 = a + b := cascade_split_add hpq
        omega
      have hcasc_0 : CascadeSplit N (a + b) p 0 := hpq
      exact H_exchange_max_form_q_zero ha hb hp hba hp_eq hcasc_0
    · rw [add_comm (max (H N a) b) (max (H N b) a)]
      have hp_eq : p = b + a := by
        have : p + 0 = a + b := cascade_split_add hpq
        omega
      have hcasc_0 : CascadeSplit N (b + a) p 0 := by
        rw [add_comm b a]; exact hpq
      exact H_exchange_max_form_q_zero hb ha hp hab' hp_eq hcasc_0
  · exact H_exchange_max_form_pos hpq ha hb hq_pos

/-- **Scalar Frankl–Füredi / Macaulay crux (★).**  The single inductive step of
Harper's vertex-isoperimetric theorem: for capacity-bounded slice masses
`x, y ≤ 2^n`, the boundary of the canonical split of `x + y` at level `n+1` is at
most the cross-slice boundary functional `max (H n x) y + max (H n y) x`.

This is the genuine remaining obstruction — the Frankl–Füredi paired-compression /
Kruskal–Katona–Macaulay shadow comparison — now stated as a pure scalar
inequality in three naturals.  It is strictly narrower than the family-level
`harper_vertex_iso` below (which is *proved* from it via the slice induction),
and is equivalent (through `H_succ_cascade`) to the finite-checked max-form
exchange step. -/
theorem harper_split_min {n x y : ℕ} (hx : x ≤ 2 ^ n) (hy : y ≤ 2 ^ n) :
    H (n + 1) (x + y) ≤ max (H n x) y + max (H n y) x := by
  have hcasc := exists_cascade_split n (x + y) (by omega)
  rcases hcasc with ⟨p, q, _, _, hpq_sum, hpq⟩
  have h_H := H_succ_cascade hpq
  rw [h_H]
  exact H_exchange_max_form hpq hx hy rfl

/-- **Harper's vertex-isoperimetric theorem (master form).**  For *every* finite
family `A` of vertices of the `N`-cube, the simplicial initial segment of the
same size has a closed `1`-neighbourhood no larger than `A`'s; equivalently the
boundary function `H N A.card` lower-bounds `(neighborhood 1 A).card`.

This is the Frankl–Füredi/PDF master statement, generalising the initial-segment
identity `H` to arbitrary families.  It is proved here by the standard
slice induction on `N`: `neighborhood_succ` decomposes the boundary across the
two coordinate slices, the induction hypothesis bounds each slice, and the single
cross-slice crux is `harper_split_min`. -/
theorem harper_vertex_iso (N : ℕ) (A : Finset (Cube N)) :
    H N A.card ≤ (neighborhood 1 A).card := by
  induction N with
  | zero =>
    have hle : A.card ≤ 1 := by
      have := Finset.card_le_univ A
      simpa [Cube, Fintype.card_finset, Fintype.card_fin] using this
    have hsub : A ⊆ neighborhood 1 A := fun x hx => by
      rw [mem_neighborhood_iff]; exact ⟨x, hx, by simp [hDist]⟩
    have hAcard : A.card ≤ (neighborhood 1 A).card := Finset.card_le_card hsub
    rcases Nat.lt_or_ge A.card 1 with h | h
    · have h0 : A.card = 0 := by omega
      rw [h0, H_zero]; exact Nat.zero_le _
    · have h1 : A.card = 1 := by omega
      have hH : H 0 1 = 1 := by simpa using H_full 0
      rw [h1, hH]
      rw [h1] at hAcard
      exact hAcard
  | succ n ih =>
    set a0 := (slice0 A).card with ha0
    set a1 := (slice1 A).card with ha1
    have hcap0 : a0 ≤ 2 ^ n := by
      have := Finset.card_le_univ (slice0 A)
      simpa [Cube, Fintype.card_finset, Fintype.card_fin] using this
    have hcap1 : a1 ≤ 2 ^ n := by
      have := Finset.card_le_univ (slice1 A)
      simpa [Cube, Fintype.card_finset, Fintype.card_fin] using this
    have hAcard : A.card = a0 + a1 := by rw [ha0, ha1, slice_card_add]
    have hIH0 := ih (slice0 A)
    have hIH1 := ih (slice1 A)
    have hterm1 : max (H n a0) a1 ≤ (neighborhood 1 (slice0 A) ∪ slice1 A).card := by
      apply max_le
      · exact le_trans hIH0 (Finset.card_le_card Finset.subset_union_left)
      · rw [ha1]; exact Finset.card_le_card Finset.subset_union_right
    have hterm2 : max (H n a1) a0 ≤ (neighborhood 1 (slice1 A) ∪ slice0 A).card := by
      apply max_le
      · exact le_trans hIH1 (Finset.card_le_card Finset.subset_union_left)
      · rw [ha0]; exact Finset.card_le_card Finset.subset_union_right
    have hsum : max (H n a0) a1 + max (H n a1) a0 ≤ (neighborhood 1 A).card := by
      rw [neighborhood_succ]; exact Nat.add_le_add hterm1 hterm2
    have hsplit := harper_split_min (n := n) hcap0 hcap1
    rw [hAcard]
    exact le_trans hsplit hsum

/-- **Layer-sum bridge (sorry-free).**  Given the Macaulay layer decompositions of
`a, b, p, q` (each a full ball of radius `rx - 1` plus `tx` vertices of layer
`rx`, with `1 ≤ rx`), the LE/GT boundary sums are *exactly* the corresponding sums
of `binomPrefix` whole-layer terms plus `upperShadow` partial-layer terms.  This
makes precise that `H_shadow_LE_sum` / `H_shadow_GT_sum` are pure upper-shadow
(Kruskal–Katona/Macaulay) inequalities, and lets the leaves be checked
empirically by tabulating `upperShadow`.  It is a direct consequence of
`H_shadow_closed_form`, hence sorry-free. -/
theorem H_shadow_LE_sum_as_upperShadow {N a b p q ra rb rp rq ta tb tp tq : ℕ}
    (hra : 1 ≤ ra) (hrb : 1 ≤ rb) (hrp : 1 ≤ rp) (hrq : 1 ≤ rq)
    (hae : a = binomPrefix N ra + ta) (hbe : b = binomPrefix N rb + tb)
    (hpe : p = binomPrefix N rp + tp) (hqe : q = binomPrefix N rq + tq) :
    (H N p + H N q ≤ H N a + H N b) ↔
      (binomPrefix N (rp + 1) + upperShadow N rp tp)
        + (binomPrefix N (rq + 1) + upperShadow N rq tq)
      ≤ (binomPrefix N (ra + 1) + upperShadow N ra ta)
        + (binomPrefix N (rb + 1) + upperShadow N rb tb) := by
  subst hae hbe hpe hqe
  rw [H_shadow_closed_form N ra ta hra, H_shadow_closed_form N rb tb hrb,
      H_shadow_closed_form N rp tp hrp, H_shadow_closed_form N rq tq hrq]

end BooleanIsoperimetry
