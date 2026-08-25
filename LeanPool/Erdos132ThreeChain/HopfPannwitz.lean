/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.Plane
import LeanPool.Erdos132ThreeChain.CaroWei

/-!
# The Hopf--Pannwitz diameter bound

Hopf and Pannwitz (1934): a set of `n` points of the plane realises its diameter at most `n`
times.  This file proves the bound in the form the main theorem consumes, and in fact proves
slightly more: only *maximality* of `D` is used, never that `D` is attained.

Nothing here is claimed as new.  The same bound is already in the pool as
`LeanPool.Erdos132N14.diameterEdges_card_le`, proved by Perles charging over an injective map
from a linearly ordered index type into `ℂ` and stated as a bound on the cardinality of a
`Finset` of unordered pairs.  This file reproves it over a `Finset (ℝ × ℝ)`, in squared
distances and handshake degree-sum form, because pool projects do not import one another; it is
a supporting lemma of this development rather than one of its results.

The classical argument deletes a pendant vertex.  If a point `v` has three points of `X` at
squared distance exactly `D`, then one of the three — the one lying angularly between the other
two, seen from `v` — has no other such partner, so it can be deleted and induction applies.

The angular step is entirely algebraic here.  Write `A`, `B`, `C` for the vectors from `v` to
the three points and let `X`, `Y`, `Z` be the cross products `A × B`, `B × C`, `A × C`.  Cramer's
rule in the plane is the identity `Z • B = Y • A + X • C`, and comparing squared lengths turns
maximality of `D` into the strict inequality `Z < X + Y`.  A partner `w` of the middle point
satisfies `⟪B, w - v⟫ = |w - v|² / 2` while `⟪A, w - v⟫` and `⟪C, w - v⟫` are at least that, so
pairing Cramer's identity with `w - v` forces `|w - v|² ≤ 0`, i.e. `w = v`.
-/

namespace Erdos132ThreeChain

open Finset

/-- Adjacency in the diameter graph: distinct points at squared distance exactly `D`. -/
def DiameterAdj (D : ℝ) (p q : Point) : Prop := p ≠ q ∧ sqDist p q = D

noncomputable instance decidableDiameterAdj (D : ℝ) : DecidableRel (DiameterAdj D) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

theorem diameterAdj_symm (D : ℝ) (p q : Point) : DiameterAdj D p q → DiameterAdj D q p :=
  fun h => ⟨h.1.symm, by rw [sqDist_comm q p]; exact h.2⟩

theorem diameterAdj_irrefl (D : ℝ) (p : Point) : ¬ DiameterAdj D p p := fun h => h.1 rfl

theorem IsSqDiameter.pos {X : Finset Point} {D : ℝ} (h : IsSqDiameter X D) : 0 < D := by
  obtain ⟨⟨p, _, q, _, hpq, rfl⟩, -⟩ := h
  exact sqDist_pos hpq

/-! ### The plane geometry -/

/-- The squared distance between two points expanded around a third. -/
theorem sqDist_expand (v a w : Point) :
    sqDist a w = sqDist v a + sqDist v w - 2 * dotp v a w := by
  simp only [sqDist, dotp]; ring

/-- Lagrange's identity in the plane. -/
theorem dotp_sq_add_cross_sq (v a b : Point) :
    dotp v a b ^ 2 + cross v a b ^ 2 = sqDist v a * sqDist v b := by
  simp only [dotp, cross, sqDist]; ring

/-- Cramer's rule in the plane, paired with a fourth point. -/
theorem cross_dotp_identity (v a b c w : Point) :
    cross v a c * dotp v b w = cross v b c * dotp v a w + cross v a b * dotp v c w := by
  simp only [cross, dotp]; ring

/-- Cramer's rule in the plane, in squared-length form. -/
theorem cross_sq_identity (v a b c : Point) :
    cross v a c ^ 2 * sqDist v b
      = cross v b c ^ 2 * sqDist v a + cross v a b ^ 2 * sqDist v c
        + 2 * (cross v b c * cross v a b) * dotp v a c := by
  simp only [cross, dotp, sqDist]; ring

/-- Two distinct points at squared distance `D` from `v`, no farther than `D` from each other,
are not collinear with `v`. -/
theorem cross_ne_zero {v a b : Point} {D : ℝ} (hD : 0 < D)
    (hva : sqDist v a = D) (hvb : sqDist v b = D) (hab : sqDist a b ≤ D) (hne : a ≠ b) :
    cross v a b ≠ 0 := by
  intro hzero
  have hlag := dotp_sq_add_cross_sq v a b
  rw [hzero, hva, hvb] at hlag
  have hexp := sqDist_expand v a b
  rw [hva, hvb] at hexp
  have hpos : 0 < sqDist a b := sqDist_pos hne
  nlinarith [hlag, hexp, hpos, hab, hD]

/-- **The pendant lemma.**  Let `a`, `b`, `c` sit at squared distance `D` from `v`, with `b`
strictly between `a` and `c` as seen from `v` (both cross products positive).  If no squared
distance among the points involved exceeds `D`, then the only point at squared distance `D`
from `b` is `v` itself. -/
theorem middle_no_other_neighbour {v a b c w : Point} {D : ℝ} (hD : 0 < D)
    (hva : sqDist v a = D) (hvb : sqDist v b = D) (hvc : sqDist v c = D) (hac : a ≠ c)
    (hX : 0 < cross v a b) (hY : 0 < cross v b c)
    (hbw : sqDist b w = D) (haw : sqDist a w ≤ D) (hcw : sqDist c w ≤ D) : w = v := by
  have hB : 2 * dotp v b w = sqDist v w := by
    have h := sqDist_expand v b w
    rw [hvb, hbw] at h
    linarith
  have hA : sqDist v w ≤ 2 * dotp v a w := by
    have h := sqDist_expand v a w
    rw [hva] at h
    linarith
  have hC : sqDist v w ≤ 2 * dotp v c w := by
    have h := sqDist_expand v c w
    rw [hvc] at h
    linarith
  have hdac : dotp v a c < D := by
    have h := sqDist_expand v a c
    rw [hva, hvc] at h
    have := sqDist_pos hac
    linarith
  have hZ : cross v a c < cross v a b + cross v b c := by
    have hid := cross_sq_identity v a b c
    rw [hva, hvb, hvc] at hid
    have hsq : cross v a c ^ 2 < (cross v a b + cross v b c) ^ 2 := by
      nlinarith [hid, hdac, mul_pos hX hY, hD]
    nlinarith [hsq, hX, hY]
  have hid2 := cross_dotp_identity v a b c w
  have h1 : 0 ≤ cross v b c * (2 * dotp v a w - sqDist v w) :=
    mul_nonneg hY.le (by linarith)
  have h2 : 0 ≤ cross v a b * (2 * dotp v c w - sqDist v w) :=
    mul_nonneg hX.le (by linarith)
  have hkey : (cross v a b + cross v b c - cross v a c) * sqDist v w ≤ 0 := by nlinarith [hid2, hB]
  have hnn := sqDist_nonneg v w
  have hzero : sqDist v w = 0 := by nlinarith [hkey, hZ, hnn]
  exact (sqDist_eq_zero_iff.mp hzero).symm

/-- Of three points seen from `v` with no two collinear with `v`, one lies strictly between the
other two.  The six alternatives are the three choices of middle point, each in the two possible
orientations. -/
theorem exists_middle (v a b c : Point) (hab : cross v a b ≠ 0) (hbc : cross v b c ≠ 0)
    (hac : cross v a c ≠ 0) :
    (0 < cross v a b ∧ 0 < cross v b c) ∨ (0 < cross v c b ∧ 0 < cross v b a) ∨
      (0 < cross v b a ∧ 0 < cross v a c) ∨ (0 < cross v c a ∧ 0 < cross v a b) ∨
      (0 < cross v a c ∧ 0 < cross v c b) ∨ (0 < cross v b c ∧ 0 < cross v c a) := by
  have eba : cross v b a = -cross v a b := by simp only [cross]; ring
  have ecb : cross v c b = -cross v b c := by simp only [cross]; ring
  have eca : cross v c a = -cross v a c := by simp only [cross]; ring
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3
  · exact Or.inr (Or.inl ⟨by rw [ecb]; linarith, by rw [eba]; linarith⟩)
  · exact Or.inr (Or.inl ⟨by rw [ecb]; linarith, by rw [eba]; linarith⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, by rw [eca]; linarith⟩))))
  · exact Or.inr (Or.inr (Or.inl ⟨by rw [eba]; linarith, h3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [eca]; linarith, h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, by rw [ecb]; linarith⟩))))
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

/-- Three points at squared distance `D` from `v` inside a set of diameter `D` force one of the
three to have `v` as its only partner at squared distance `D`. -/
theorem exists_pendant {X : Finset Point} {D : ℝ} (hD : 0 < D)
    (hmax : ∀ p ∈ X, ∀ q ∈ X, sqDist p q ≤ D)
    {v a b c : Point} (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hva : sqDist v a = D) (hvb : sqDist v b = D) (hvc : sqDist v c = D)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∀ w ∈ X, sqDist a w = D → w = v) ∨ (∀ w ∈ X, sqDist b w = D → w = v)
      ∨ (∀ w ∈ X, sqDist c w = D → w = v) := by
  have kab : cross v a b ≠ 0 := cross_ne_zero hD hva hvb (hmax a haX b hbX) hab
  have kbc : cross v b c ≠ 0 := cross_ne_zero hD hvb hvc (hmax b hbX c hcX) hbc
  have kac : cross v a c ≠ 0 := cross_ne_zero hD hva hvc (hmax a haX c hcX) hac
  rcases exists_middle v a b c kab kbc kac with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inl fun w hw hbw =>
      middle_no_other_neighbour hD hva hvb hvc hac h1 h2 hbw (hmax a haX w hw) (hmax c hcX w hw))
  · exact Or.inr (Or.inl fun w hw hbw =>
      middle_no_other_neighbour hD hvc hvb hva hac.symm h1 h2 hbw (hmax c hcX w hw)
        (hmax a haX w hw))
  · exact Or.inl fun w hw haw =>
      middle_no_other_neighbour hD hvb hva hvc hbc h1 h2 haw (hmax b hbX w hw) (hmax c hcX w hw)
  · exact Or.inl fun w hw haw =>
      middle_no_other_neighbour hD hvc hva hvb hbc.symm h1 h2 haw (hmax c hcX w hw)
        (hmax b hbX w hw)
  · exact Or.inr (Or.inr fun w hw hcw =>
      middle_no_other_neighbour hD hva hvc hvb hab h1 h2 hcw (hmax a haX w hw)
        (hmax b hbX w hw))
  · exact Or.inr (Or.inr fun w hw hcw =>
      middle_no_other_neighbour hD hvb hvc hva hab.symm h1 h2 hcw (hmax b hbX w hw)
        (hmax a haX w hw))

/-! ### Counting -/

/-- Deleting a pendant vertex removes exactly one edge, i.e. two from the degree sum. -/
theorem sum_degree_erase {X : Finset Point} {D : ℝ} {b v : Point} (hbX : b ∈ X) (hvX : v ∈ X)
    (hbv : b ≠ v) (hstar : X.filter (DiameterAdj D b) = {v}) :
    ∑ u ∈ X, degree (DiameterAdj D) X u
      = (∑ u ∈ X.erase b, degree (DiameterAdj D) (X.erase b) u) + 2 := by
  classical
  have hdegb : degree (DiameterAdj D) X b = 1 := by
    rw [degree, hstar, Finset.card_singleton]
  have hstep : ∀ u ∈ X.erase b, degree (DiameterAdj D) X u
      = degree (DiameterAdj D) (X.erase b) u + (if DiameterAdj D u b then 1 else 0) := by
    intro u _
    have hfil : (X.erase b).filter (DiameterAdj D u) = (X.filter (DiameterAdj D u)).erase b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    by_cases h : DiameterAdj D u b
    · have hif : (if DiameterAdj D u b then (1 : ℕ) else 0) = 1 := by simp [h]
      have hmem : b ∈ X.filter (DiameterAdj D u) := Finset.mem_filter.mpr ⟨hbX, h⟩
      rw [hif, degree, degree, hfil, Finset.card_erase_add_one hmem]
    · have hif : (if DiameterAdj D u b then (1 : ℕ) else 0) = 0 := by simp [h]
      have hnot : b ∉ X.filter (DiameterAdj D u) := by
        simp only [Finset.mem_filter]
        exact fun hc => h hc.2
      rw [hif, degree, degree, hfil, Finset.erase_eq_of_notMem hnot, add_zero]
  have hnbr : (X.erase b).filter (fun u => DiameterAdj D u b) = {v} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hxb, hxX⟩, hadj⟩
      have : x ∈ X.filter (DiameterAdj D b) :=
        Finset.mem_filter.mpr ⟨hxX, diameterAdj_symm D x b hadj⟩
      rw [hstar] at this
      exact Finset.mem_singleton.mp this
    · rintro rfl
      have hv : x ∈ X.filter (DiameterAdj D b) := by rw [hstar]; simp
      exact ⟨⟨fun hc => hbv hc.symm, hvX⟩, diameterAdj_symm D b x (Finset.mem_filter.mp hv).2⟩
  calc ∑ u ∈ X, degree (DiameterAdj D) X u
      = degree (DiameterAdj D) X b + ∑ u ∈ X.erase b, degree (DiameterAdj D) X u :=
        (Finset.add_sum_erase _ _ hbX).symm
    _ = 1 + ∑ u ∈ X.erase b, (degree (DiameterAdj D) (X.erase b) u
          + (if DiameterAdj D u b then 1 else 0)) := by
        rw [hdegb, Finset.sum_congr rfl hstep]
    _ = 1 + ((∑ u ∈ X.erase b, degree (DiameterAdj D) (X.erase b) u)
          + ((X.erase b).filter (fun u => DiameterAdj D u b)).card) := by
        rw [Finset.sum_add_distrib, Finset.sum_boole]
        norm_cast
    _ = (∑ u ∈ X.erase b, degree (DiameterAdj D) (X.erase b) u) + 2 := by
        rw [hnbr, Finset.card_singleton]; omega

/-- The induction step packaged: a pendant vertex `b` whose only partner is `v`. -/
theorem sum_degree_le_of_pendant {X : Finset Point} {D : ℝ} {b v : Point}
    (hbX : b ∈ X) (hvX : v ∈ X) (hbv : b ≠ v) (hvb : sqDist v b = D)
    (hstar : ∀ w ∈ X, sqDist b w = D → w = v)
    (ih : ∑ u ∈ X.erase b, degree (DiameterAdj D) (X.erase b) u ≤ 2 * (X.erase b).card) :
    ∑ u ∈ X, degree (DiameterAdj D) X u ≤ 2 * X.card := by
  classical
  have hfil : X.filter (DiameterAdj D b) = {v} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxX, hadj⟩
      exact hstar x hxX hadj.2
    · rintro rfl
      exact ⟨hvX, hbv, by rw [sqDist_comm b x]; exact hvb⟩
  have hcard : (X.erase b).card = X.card - 1 := Finset.card_erase_of_mem hbX
  have hpos : 1 ≤ X.card := Finset.card_pos.mpr ⟨b, hbX⟩
  rw [sum_degree_erase hbX hvX hbv hfil]
  omega

/-- **Hopf--Pannwitz.**  If every squared distance inside `X` is at most `D > 0`, then the graph
joining points of `X` at squared distance exactly `D` has degree sum at most `2 * #X`, that is,
at most `#X` edges. -/
theorem sum_degree_le {D : ℝ} (hD : 0 < D) (X : Finset Point)
    (hmax : ∀ p ∈ X, ∀ q ∈ X, sqDist p q ≤ D) :
    ∑ v ∈ X, degree (DiameterAdj D) X v ≤ 2 * X.card := by
  classical
  induction X using Finset.strongInduction with
  | _ X ih =>
    by_cases hdeg : ∀ v ∈ X, degree (DiameterAdj D) X v ≤ 2
    · calc ∑ v ∈ X, degree (DiameterAdj D) X v ≤ ∑ _v ∈ X, 2 := Finset.sum_le_sum hdeg
        _ = 2 * X.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · rw [not_forall] at hdeg
      obtain ⟨v, hdeg⟩ := hdeg
      rw [Classical.not_imp] at hdeg
      obtain ⟨hvX, hvdeg⟩ := hdeg
      rw [not_le] at hvdeg
      simp only [degree] at hvdeg
      obtain ⟨T, hTsub, hTcard⟩ :=
        Finset.exists_subset_card_eq (n := 3) (s := X.filter (DiameterAdj D v)) (by omega)
      obtain ⟨a, b, c, hab, hac, hbc, hTeq⟩ := Finset.card_eq_three.mp hTcard
      have hmemT : ∀ x ∈ T, x ∈ X ∧ DiameterAdj D v x := by
        intro x hx
        exact Finset.mem_filter.mp (hTsub hx)
      obtain ⟨haX, hvaAdj⟩ := hmemT a (by rw [hTeq]; simp)
      obtain ⟨hbX, hvbAdj⟩ := hmemT b (by rw [hTeq]; simp)
      obtain ⟨hcX, hvcAdj⟩ := hmemT c (by rw [hTeq]; simp)
      have hsubX : ∀ x ∈ X, X.erase x ⊂ X := fun x hx => Finset.erase_ssubset hx
      rcases exists_pendant hD hmax haX hbX hcX hvaAdj.2 hvbAdj.2 hvcAdj.2 hab hac hbc with
        hp | hp | hp
      · exact sum_degree_le_of_pendant haX hvX (Ne.symm hvaAdj.1) hvaAdj.2 hp
          (ih _ (hsubX a haX) fun p hp' q hq' =>
            hmax p (Finset.mem_of_mem_erase hp') q (Finset.mem_of_mem_erase hq'))
      · exact sum_degree_le_of_pendant hbX hvX (Ne.symm hvbAdj.1) hvbAdj.2 hp
          (ih _ (hsubX b hbX) fun p hp' q hq' =>
            hmax p (Finset.mem_of_mem_erase hp') q (Finset.mem_of_mem_erase hq'))
      · exact sum_degree_le_of_pendant hcX hvX (Ne.symm hvcAdj.1) hvcAdj.2 hp
          (ih _ (hsubX c hcX) fun p hp' q hq' =>
            hmax p (Finset.mem_of_mem_erase hp') q (Finset.mem_of_mem_erase hq'))

/-- **Hopf--Pannwitz for a diameter.**  The diameter graph of a finite planar set has at most as
many edges as the set has points. -/
theorem hopfPannwitz {X : Finset Point} {D : ℝ} (hD : IsSqDiameter X D) :
    ∑ v ∈ X, degree (DiameterAdj D) X v ≤ 2 * X.card :=
  sum_degree_le hD.pos X hD.2

end Erdos132ThreeChain
