/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini, Aristotle
-/
import LeanPool.MinimumDegreeMatching.BKLOInfrastructure

/-!
# Deterministic simultaneous matching selection

A pessimistic-estimator sweep chooses perfect matchings in overlapping apex neighbourhoods while
keeping all previously selected matching edges disjoint. This is the deterministic core used for
the `r = 2` specialization of BKLO Lemma 10.7.
-/

open Finset

namespace BKLOK2

variable {V : Type*} [DecidableEq V]
/-! ### The used-degree counter and the potential -/

/-- The number of edges of the used set `F` at `y` lying inside the apex neighbourhood `N_H(x,W)`.
This is exactly the amount by which the Dirac degree of `y` in `H[N_H(x,W)]` has been eroded. -/
def usedCnt (H : Finset (Sym2 V)) (W : Finset V) (F : Finset (Sym2 V)) (x y : V) : ℕ :=
  edeg (edgesIn F (nbhdIn H x W)) y

/-- **The pessimistic-estimator potential.**  `R` is the set of apices not yet processed. -/
noncomputable def pot (H : Finset (Sym2 V)) (W : Finset V) (q : ℝ) (F : Finset (Sym2 V))
    (R : Finset V) : ℝ :=
  ∑ x ∈ R, ∑ y ∈ nbhdIn H x W, (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R)

/-- The weight function fed to the spread clause at the apex being processed: the potential mass
carried by the pair `(y, z)`, i.e. the total over the remaining apices containing both. -/
noncomputable def wgt (H : Finset (Sym2 V)) (W : Finset V) (q : ℝ) (F : Finset (Sym2 V))
    (R' R : Finset V) (y z : V) : ℝ :=
  ∑ x ∈ R'.filter (fun x => y ∈ nbhdIn H x W ∧ z ∈ nbhdIn H x W),
    (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R)

theorem wgt_nonneg {H : Finset (Sym2 V)} {W : Finset V} {q : ℝ} (hq : 0 ≤ q)
    (F : Finset (Sym2 V)) (R' R : Finset V) (y z : V) : 0 ≤ wgt H W q F R' R y z := by
  refine Finset.sum_nonneg fun x _ => ?_
  positivity

theorem pot_nonneg {H : Finset (Sym2 V)} {W : Finset V} {q : ℝ} (hq : 0 ≤ q)
    (F : Finset (Sym2 V)) (R : Finset V) : 0 ≤ pot H W q F R := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  positivity

/-- Every single term of the potential is at most the potential. -/
theorem pow_usedCnt_le_pot {H : Finset (Sym2 V)} {W : Finset V} {q : ℝ} (hq : 0 ≤ q)
    {F : Finset (Sym2 V)} {R : Finset V} {x y : V} (hx : x ∈ R) (hy : y ∈ nbhdIn H x W) :
    (2 : ℝ) ^ (usedCnt H W F x y) ≤ pot H W q F R := by
  classical
  have hterm : (2 : ℝ) ^ (usedCnt H W F x y)
      ≤ (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) := by
    have h1 : (1 : ℝ) ≤ (1 + q) ^ (degTo H y R) := one_le_pow₀ (by linarith)
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (usedCnt H W F x y)]
  refine hterm.trans ?_
  have hinner : (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R)
      ≤ ∑ z ∈ nbhdIn H x W, (2 : ℝ) ^ (usedCnt H W F x z) * (1 + q) ^ (degTo H z R) :=
    Finset.single_le_sum (f := fun z => (2 : ℝ) ^ (usedCnt H W F x z) * (1 + q) ^ (degTo H z R))
      (fun z _ => by positivity) hy
  refine hinner.trans ?_
  exact Finset.single_le_sum
    (f := fun x' => ∑ z ∈ nbhdIn H x' W, (2 : ℝ) ^ (usedCnt H W F x' z) * (1 + q) ^ (degTo H z R))
    (fun x' _ => Finset.sum_nonneg fun z _ => by positivity) hx

/-- The potential controls the used degrees: if `Φ < 2 ^ (s+1)` then no counter exceeds `s`. -/
theorem usedCnt_le_of_pot {H : Finset (Sym2 V)} {W : Finset V} {q : ℝ} (hq : 0 ≤ q)
    {F : Finset (Sym2 V)} {R : Finset V} {s : ℕ} (hpot : pot H W q F R < 2 ^ (s + 1))
    {x y : V} (hx : x ∈ R) (hy : y ∈ nbhdIn H x W) : usedCnt H W F x y ≤ s := by
  by_contra hcon
  push Not at hcon
  have h1 : (2 : ℝ) ^ (s + 1) ≤ (2 : ℝ) ^ (usedCnt H W F x y) :=
    pow_le_pow_right₀ (by norm_num) hcon
  have h2 := pow_usedCnt_le_pot (F := F) hq hx hy
  linarith only [hpot, h1, h2]

/-! ### The step inequality -/

/-- The used degree inside `N_H(x,W)` grows by at most one, and only at vertices of the current
neighbourhood matched into `N_H(x,W)`. -/
theorem usedCnt_union_le {H : Finset (Sym2 V)} {W : Finset V} (F : Finset (Sym2 V))
    {N : Finset V} {f : V → V} (hmap : ∀ a ∈ N, f a ∈ N) (hinv : ∀ a ∈ N, f (f a) = a)
    (x y : V) :
    usedCnt H W (F ∪ famEdges (involutionMatching N f)) x y
      ≤ usedCnt H W F x y +
        (if y ∈ N ∧ y ∈ nbhdIn H x W ∧ f y ∈ nbhdIn H x W then 1 else 0) := by
  classical
  set T := nbhdIn H x W with hT
  set M := involutionMatching N f with hM
  have hsplit : edgesIn (F ∪ famEdges M) T = edgesIn F T ∪ edgesIn (famEdges M) T := by
    simp [edgesIn, Finset.filter_union]
  have h1 : usedCnt H W (F ∪ famEdges M) x y
      ≤ usedCnt H W F x y + edeg (edgesIn (famEdges M) T) y := by
    unfold usedCnt edeg
    rw [hsplit, Finset.filter_union]
    exact Finset.card_union_le _ _
  have key : ∀ e ∈ (edgesIn (famEdges M) T).filter (fun e => y ∈ e),
      e = s(y, f y) ∧ (y ∈ N ∧ y ∈ T ∧ f y ∈ T) := by
    intro e he
    obtain ⟨heIn, hye⟩ := Finset.mem_filter.1 he
    obtain ⟨heF, hsubT⟩ := mem_edgesIn.1 heIn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (famEdges_involutionMatching_subset N f heF)
    rcases Sym2.mem_iff.1 hye with rfl | hfa
    · exact ⟨rfl, ha, hsubT y (by simp), hsubT (f y) (by simp)⟩
    · have hfy : f y = a := by rw [hfa]; exact hinv a ha
      have hyN : y ∈ N := by rw [hfa]; exact hmap a ha
      refine ⟨?_, hyN, hsubT y (by rw [hfa]; simp), ?_⟩
      · rw [hfy, hfa, Sym2.eq_swap]
      · rw [hfy]; exact hsubT a (by simp)
  have h2 : edeg (edgesIn (famEdges M) T) y ≤ (if y ∈ N ∧ y ∈ T ∧ f y ∈ T then 1 else 0) := by
    by_cases hc : y ∈ N ∧ y ∈ T ∧ f y ∈ T
    · rw [ite_eq_left hc]
      refine le_trans (Finset.card_le_card (fun e he => ?_))
        (by simp : ({s(y, f y)} : Finset (Sym2 V)).card ≤ 1)
      exact Finset.mem_singleton.2 (key e he).1
    · rw [ite_eq_right hc]
      refine Nat.le_zero.2 (Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem ?_))
      intro e he
      exact hc (key e he).2
  omega

/-- Deleting an apex from the index set deletes it from every neighbourhood. -/
theorem nbhdIn_erase (H : Finset (Sym2 V)) (R : Finset V) (x₀ y : V) :
    nbhdIn H y (R.erase x₀) = (nbhdIn H y R).erase x₀ := by
  ext z
  simp only [mem_nbhdIn, Finset.mem_erase]
  tauto

/-- A vertex of the processed neighbourhood loses exactly one apex. -/
theorem degTo_erase_of_mem_nbhd {H : Finset (Sym2 V)} {W R : Finset V} {x₀ y : V}
    (hx₀ : x₀ ∈ R) (hy : y ∈ nbhdIn H x₀ W) :
    degTo H y R = degTo H y (R.erase x₀) + 1 := by
  have hmem : x₀ ∈ nbhdIn H y R := by
    rw [mem_nbhdIn]
    exact ⟨hx₀, by rw [Sym2.eq_swap]; exact (mem_nbhdIn.1 hy).2⟩
  rw [degTo, degTo, nbhdIn_erase, Finset.card_erase_of_mem hmem]
  have : 1 ≤ (nbhdIn H y R).card := Finset.card_pos.2 ⟨x₀, hmem⟩
  omega

/-- A vertex outside the processed neighbourhood loses no apex. -/
theorem degTo_erase_of_notMem_nbhd {H : Finset (Sym2 V)} {W R : Finset V} {x₀ y : V}
    (hyW : y ∈ W) (hy : y ∉ nbhdIn H x₀ W) :
    degTo H y (R.erase x₀) = degTo H y R := by
  have hmem : x₀ ∉ nbhdIn H y R := by
    intro hc
    exact hy (mem_nbhdIn.2 ⟨hyW, by rw [Sym2.eq_swap]; exact (mem_nbhdIn.1 hc).2⟩)
  rw [degTo, degTo, nbhdIn_erase, Finset.erase_eq_of_notMem hmem]

/-- The term bound at a vertex of the neighbourhood being processed: one unit of used degree may
be created, and the factor `(1+q)` released by deleting `x₀` from the index set pays for it. -/
theorem pot_step_mem_term {H : Finset (Sym2 V)} {W : Finset V} {q : ℝ}
    {F : Finset (Sym2 V)} {R : Finset V} {x₀ x y : V} {f : V → V} (hx₀ : x₀ ∈ R)
    (hmap : ∀ a ∈ nbhdIn H x₀ W, f a ∈ nbhdIn H x₀ W)
    (hinv : ∀ a ∈ nbhdIn H x₀ W, f (f a) = a)
    (hq : 0 ≤ q) (hy : y ∈ nbhdIn H x W) (hy0 : y ∈ nbhdIn H x₀ W) :
    (1 + q) * ((2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
        * (1 + q) ^ (degTo H y (R.erase x₀)))
      ≤ ((2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R))
        + (if f y ∈ nbhdIn H x W then
            (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0) := by
  have hd : degTo H y R = degTo H y (R.erase x₀) + 1 := degTo_erase_of_mem_nbhd hx₀ hy0
  have hu := usedCnt_union_le (H := H) (W := W) F hmap hinv x y
  have hpow : (0 : ℝ) < (1 + q) ^ (degTo H y (R.erase x₀)) := by positivity
  have h1q : (0 : ℝ) ≤ 1 + q := by linarith only [hq]
  by_cases hf : f y ∈ nbhdIn H x W
  · rw [ite_eq_left hf, hd, pow_succ]
    rw [ite_eq_left ⟨hy0, hy, hf⟩] at hu
    have h2 : (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
        ≤ 2 * 2 ^ (usedCnt H W F x y) := by
      calc (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
          ≤ (2 : ℝ) ^ (usedCnt H W F x y + 1) := pow_le_pow_right₀ (by norm_num) hu
        _ = 2 * 2 ^ (usedCnt H W F x y) := by rw [pow_succ]; ring
    have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hpow.le) h1q
    linarith only [h4]
  · rw [ite_eq_right hf, hd, pow_succ]
    rw [ite_eq_right (fun h => hf h.2.2)] at hu
    have h2 : (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
        ≤ 2 ^ (usedCnt H W F x y) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hpow.le) h1q
    linarith only [h4]

/-- The term bound away from the neighbourhood being processed: nothing changes there. -/
theorem pot_step_notMem_term {H : Finset (Sym2 V)} {W : Finset V} {q : ℝ}
    {F : Finset (Sym2 V)} {R : Finset V} {x₀ x y : V} {f : V → V}
    (hmap : ∀ a ∈ nbhdIn H x₀ W, f a ∈ nbhdIn H x₀ W)
    (hinv : ∀ a ∈ nbhdIn H x₀ W, f (f a) = a)
    (hq : 0 ≤ q) (hy : y ∈ nbhdIn H x W) (hy0 : y ∉ nbhdIn H x₀ W) :
    (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
        * (1 + q) ^ (degTo H y (R.erase x₀))
      ≤ (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) := by
  have hyW : y ∈ W := nbhdIn_subset H x W hy
  have hd : degTo H y (R.erase x₀) = degTo H y R := degTo_erase_of_notMem_nbhd hyW hy0
  have hu := usedCnt_union_le (H := H) (W := W) F hmap hinv x y
  rw [ite_eq_right (fun h => hy0 h.1)] at hu
  rw [hd]
  have h2 : (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
      ≤ (2 : ℝ) ^ (usedCnt H W F x y) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℝ) ≤ (1 + q) ^ (degTo H y R) := pow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_right h2 hpos

/-- **Fubini for the partner weight.**  The mass the sweep pays at the processed apex is exactly
the weight of the chosen involution. -/
theorem sum_wgt_partner_eq (H : Finset (Sym2 V)) (W : Finset V) (q : ℝ) (F : Finset (Sym2 V))
    (R' R : Finset V) (x₀ : V) (f : V → V) :
    ∑ y ∈ nbhdIn H x₀ W, wgt H W q F R' R y (f y)
      = ∑ x ∈ R', ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
          (if f y ∈ nbhdIn H x W then
            (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0) := by
  classical
  have h1 : ∀ y : V, wgt H W q F R' R y (f y)
      = ∑ x ∈ R', (if y ∈ nbhdIn H x W ∧ f y ∈ nbhdIn H x W then
          (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0) := by
    intro y; rw [wgt, Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hset : (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W)
      = (nbhdIn H x₀ W).filter (fun y => y ∈ nbhdIn H x W) := by
    ext y; simp only [Finset.mem_filter]; tauto
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : y ∈ nbhdIn H x W <;> simp [h]

/-- **The total weight**, evaluated: each remaining apex contributes its codegree with `x₀` times
its own potential mass inside `N_H(x₀, W)`. -/
theorem sum_sum_wgt_eq (H : Finset (Sym2 V)) (W : Finset V) (q : ℝ) (F : Finset (Sym2 V))
    (R' R : Finset V) (x₀ : V) :
    ∑ y ∈ nbhdIn H x₀ W, ∑ z ∈ nbhdIn H x₀ W, wgt H W q F R' R y z
      = ∑ x ∈ R', (codegTo H x x₀ W : ℝ) *
          ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
            (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) := by
  classical
  have h1 : ∀ y z : V, wgt H W q F R' R y z
      = ∑ x ∈ R', (if y ∈ nbhdIn H x W ∧ z ∈ nbhdIn H x W then
          (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0) := by
    intro y z; rw [wgt, Finset.sum_filter]
  simp_rw [h1]
  have hswap : ∀ y : V, ∑ z ∈ nbhdIn H x₀ W, ∑ x ∈ R',
      (if y ∈ nbhdIn H x W ∧ z ∈ nbhdIn H x W then
        (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0)
      = ∑ x ∈ R', ∑ z ∈ nbhdIn H x₀ W,
      (if y ∈ nbhdIn H x W ∧ z ∈ nbhdIn H x W then
        (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0) := fun _ => Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hinner : ∀ y : V, ∑ z ∈ nbhdIn H x₀ W,
      (if y ∈ nbhdIn H x W ∧ z ∈ nbhdIn H x W then
        (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0)
      = if y ∈ nbhdIn H x W then
          (codegTo H x x₀ W : ℝ) * ((2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R))
        else 0 := by
    intro y
    by_cases hyx : y ∈ nbhdIn H x W
    · simp only [hyx, true_and, ite_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 2
      have hs : (nbhdIn H x₀ W).filter (fun z => z ∈ nbhdIn H x W)
          = nbhdIn H x W ∩ nbhdIn H x₀ W := by
        ext z; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
      rw [hs, codegTo]
    · simp [hyx]
  simp_rw [hinner]
  have hset : (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W)
      = (nbhdIn H x₀ W).filter (fun y => y ∈ nbhdIn H x W) := by
    ext y; simp only [Finset.mem_filter]; tauto
  rw [hset, ← Finset.sum_filter, Finset.mul_sum]

/-- The half of the step inequality living inside the processed neighbourhood: this is where the
spread clause and the codegree bound are consumed. -/
theorem pot_step_mem_sum {β q : ℝ} (hq : 0 ≤ q) {H : Finset (Sym2 V)} {W R : Finset V}
    {x₀ : V} (hx₀ : x₀ ∈ R) {F : Finset (Sym2 V)} {f : V → V}
    (hmap : ∀ a ∈ nbhdIn H x₀ W, f a ∈ nbhdIn H x₀ W)
    (hinv : ∀ a ∈ nbhdIn H x₀ W, f (f a) = a)
    (hbound : ∑ y ∈ nbhdIn H x₀ W, wgt H W q F (R.erase x₀) R y (f y)
      ≤ β * ∑ y ∈ nbhdIn H x₀ W, ∑ z ∈ nbhdIn H x₀ W, wgt H W q F (R.erase x₀) R y z)
    (hcodeg : ∀ x ∈ R.erase x₀, β * (codegTo H x x₀ W : ℝ) ≤ q) :
    ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
        (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
          * (1 + q) ^ (degTo H y (R.erase x₀))
      ≤ ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
          (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) := by
  classical
  have h1q : (0 : ℝ) < 1 + q := by linarith only [hq]
  set A : ℝ := ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
      (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
        * (1 + q) ^ (degTo H y (R.erase x₀)) with hA
  set S : V → ℝ := fun x => ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
      (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) with hS
  set T : ℝ := ∑ x ∈ R.erase x₀, S x with hT
  set IP : ℝ := ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
      (if f y ∈ nbhdIn H x W then
        (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) else 0) with hIP
  have hSnonneg : ∀ x : V, 0 ≤ S x := by
    intro x
    rw [hS]
    exact Finset.sum_nonneg fun y _ => by positivity
  have hstep1 : (1 + q) * A ≤ T + IP := by
    rw [hA, Finset.mul_sum, hT, hIP, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mul_sum, hS, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    exact pot_step_mem_term hx₀ hmap hinv hq hy1 hy2
  have hIPeq : IP = ∑ y ∈ nbhdIn H x₀ W, wgt H W q F (R.erase x₀) R y (f y) := by
    rw [hIP]
    exact (sum_wgt_partner_eq H W q F (R.erase x₀) R x₀ f).symm
  have hIPle : IP ≤ q * T := by
    rw [hIPeq]
    refine hbound.trans ?_
    rw [sum_sum_wgt_eq H W q F (R.erase x₀) R x₀, hT, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have h1 : β * ((codegTo H x x₀ W : ℝ) * S x) = (β * (codegTo H x x₀ W : ℝ)) * S x := by ring
    rw [hS] at h1 ⊢
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hcodeg x hx) (by rw [← hS]; exact hSnonneg x)
  have hfin : (1 + q) * A ≤ (1 + q) * T := by linarith only [hstep1, hIPle]
  exact le_of_mul_le_mul_left hfin h1q

/-- **The pessimistic estimator does not increase.**  Processing the apex `x₀` with a matching
chosen by the spread clause leaves the potential no larger. -/
theorem pot_step {β q : ℝ} (hq : 0 ≤ q) {H : Finset (Sym2 V)} {W : Finset V} {R : Finset V}
    {x₀ : V} (hx₀ : x₀ ∈ R) {F : Finset (Sym2 V)} {f : V → V}
    (hmap : ∀ a ∈ nbhdIn H x₀ W, f a ∈ nbhdIn H x₀ W)
    (hinv : ∀ a ∈ nbhdIn H x₀ W, f (f a) = a)
    (hbound : ∑ y ∈ nbhdIn H x₀ W, wgt H W q F (R.erase x₀) R y (f y)
      ≤ β * ∑ y ∈ nbhdIn H x₀ W, ∑ z ∈ nbhdIn H x₀ W, wgt H W q F (R.erase x₀) R y z)
    (hcodeg : ∀ x ∈ R.erase x₀, β * (codegTo H x x₀ W : ℝ) ≤ q) :
    pot H W q (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) (R.erase x₀)
      ≤ pot H W q F R := by
  classical
  have hA1 := pot_step_mem_sum hq hx₀ hmap hinv hbound hcodeg
  have hA2 : ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∉ nbhdIn H x₀ W),
        (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
          * (1 + q) ^ (degTo H y (R.erase x₀))
      ≤ ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∉ nbhdIn H x₀ W),
          (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    exact pot_step_notMem_term hmap hinv hq hy1 hy2
  calc pot H W q (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) (R.erase x₀)
      = (∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
            (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
              * (1 + q) ^ (degTo H y (R.erase x₀)))
          + ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∉ nbhdIn H x₀ W),
            (2 : ℝ) ^ (usedCnt H W (F ∪ famEdges (involutionMatching (nbhdIn H x₀ W) f)) x y)
              * (1 + q) ^ (degTo H y (R.erase x₀)) := by
        rw [pot, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ =>
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ (∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∈ nbhdIn H x₀ W),
            (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R))
          + ∑ x ∈ R.erase x₀, ∑ y ∈ (nbhdIn H x W).filter (fun y => y ∉ nbhdIn H x₀ W),
            (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) := add_le_add hA1 hA2
    _ = ∑ x ∈ R.erase x₀, ∑ y ∈ nbhdIn H x W,
            (2 : ℝ) ^ (usedCnt H W F x y) * (1 + q) ^ (degTo H y R) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_filter_add_sum_filter_not _ _ _
    _ ≤ pot H W q F R := by
        rw [pot]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun x _ _ => Finset.sum_nonneg fun y _ => by positivity)

/-! ### The sweep -/

/-- **The sequential selection.**  The apices of `R` can be processed one at a time, each receiving
a perfect matching of its neighbourhood avoiding all the edges used so far, as long as the potential
stays below `2 ^ (s₁+1)`.  The Dirac slack is split: `s₁` absorbs the already used edges, and the
remaining `s₂` supplies the `1/(s₂+1)`-spread matching of `BKLO.exists_spread_involution`. -/
theorem spread_process {H : Finset (Sym2 V)} {U W : Finset V}
    {q : ℝ} {s₁ s₂ : ℕ} (hq : 0 ≤ q) (hloop : ∀ e ∈ H, ¬ e.IsDiag) (hUW : Disjoint U W)
    (hEven : ∀ x ∈ U, Even (nbhdIn H x W).card)
    (hmindeg : ∀ x ∈ U, ∀ v ∈ nbhdIn H x W,
      (nbhdIn H x W).card / 2 + s₂ + s₁ ≤ edeg (edgesIn H (nbhdIn H x W)) v)
    (hcodeg : ∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → (codegTo H x x' W : ℝ) ≤ q * ((s₂ : ℝ) + 1)) :
    ∀ R : Finset V, R ⊆ U → ∀ F : Finset (Sym2 V), pot H W q F R < 2 ^ (s₁ + 1) →
      ∃ Mx : V → Finset (Finset V), (∀ x ∈ R, GoodMatching H W x (Mx x)) ∧
        (R : Set V).Pairwise (fun x y => Disjoint (famEdges (Mx x)) (famEdges (Mx y))) ∧
        (∀ x ∈ R, Disjoint (famEdges (Mx x)) F) := by
  classical
  intro R
  induction R using Finset.strongInduction with
  | _ R ih =>
    intro hRU F hpot
    rcases R.eq_empty_or_nonempty with rfl | hRne
    · exact ⟨fun _ => ∅, by simp, by simp, by simp⟩
    obtain ⟨x₀, hx₀⟩ := hRne
    have hx₀U : x₀ ∈ U := hRU hx₀
    set N₀ : Finset V := nbhdIn H x₀ W with hN₀
    have hx₀N : x₀ ∉ N₀ := fun hc =>
      (Finset.disjoint_left.1 hUW hx₀U) (nbhdIn_subset H x₀ W hc)
    set A : Finset (Sym2 V) := edgesIn H N₀ \ F with hA
    have hAsub : A ⊆ cliqueEdges N₀ :=
      Finset.sdiff_subset.trans (edgesIn_subset_cliqueEdges_loopless hloop N₀)
    -- the potential keeps the used degree inside the Dirac slack
    have hused : ∀ v ∈ N₀, usedCnt H W F x₀ v ≤ s₁ := fun v hv =>
      usedCnt_le_of_pot hq hpot hx₀ hv
    have hAeq : A = edgesIn H N₀ \ edgesIn F N₀ := by
      ext e
      simp only [hA, Finset.mem_sdiff, mem_edgesIn]
      constructor
      · rintro ⟨⟨heH, hsub⟩, heF⟩
        exact ⟨⟨heH, hsub⟩, fun hc => heF hc.1⟩
      · rintro ⟨⟨heH, hsub⟩, hne⟩
        exact ⟨⟨heH, hsub⟩, fun hc => hne ⟨hc, hsub⟩⟩
    have hdegA : ∀ v ∈ N₀, N₀.card / 2 + s₂ ≤ edeg A v := by
      intro v hv
      rw [hAeq]
      exact edeg_sdiff_ge_of_slack (hmindeg x₀ hx₀U v hv) (hused v hv)
    -- the Dirac slack supplies a partner involution of small weight
    obtain ⟨f, hmap, hinv, hfne, hadj, hwbound⟩ :=
      exists_spread_involution hAsub (hEven x₀ hx₀U) hdegA
        (fun y z => wgt H W q F (R.erase x₀) R y z) (fun y z => wgt_nonneg hq _ _ _ _ _)
    set M : Finset (Finset V) := involutionMatching N₀ f with hM
    obtain ⟨hMatch, hMsub, hMcov, hMedges⟩ :=
      matching_data_of_involution hx₀N hmap hinv hfne hadj
    have hfamM : famEdges M ⊆ A := by
      intro e he
      rw [famEdges, Finset.mem_biUnion] at he
      obtain ⟨t, ht, het⟩ := he
      exact hMedges t ht het
    have hMF : Disjoint (famEdges M) F :=
      Finset.disjoint_left.2 fun e he heF => (Finset.mem_sdiff.1 (hfamM he)).2 heF
    -- the potential does not increase
    have hbeta : ∀ x ∈ R.erase x₀,
        (1 / ((s₂ : ℝ) + 1)) * (codegTo H x x₀ W : ℝ) ≤ q := by
      intro x hx
      have h1 := hcodeg x (hRU (Finset.mem_of_mem_erase hx)) x₀ hx₀U (Finset.ne_of_mem_erase hx)
      have hpos : (0 : ℝ) < (s₂ : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
      exact h1
    have hstep : pot H W q (F ∪ famEdges M) (R.erase x₀) ≤ pot H W q F R :=
      pot_step hq hx₀ hmap hinv hwbound hbeta
    have hpot' : pot H W q (F ∪ famEdges M) (R.erase x₀) < 2 ^ (s₁ + 1) :=
      lt_of_le_of_lt hstep hpot
    obtain ⟨Mx, hgood, hpair, hdisj⟩ :=
      ih (R.erase x₀) (Finset.erase_ssubset hx₀)
        (fun z hz => hRU (Finset.mem_of_mem_erase hz)) (F ∪ famEdges M) hpot'
    have hx₀notmem : x₀ ∉ R.erase x₀ := Finset.notMem_erase x₀ R
    refine ⟨Function.update Mx x₀ M, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hxx : x = x₀
      · rw [hxx, Function.update_self]
        exact ⟨hMatch, hMsub, hMcov, fun e he => (hMedges e he).trans Finset.sdiff_subset⟩
      · rw [Function.update_of_ne hxx]
        exact hgood x (Finset.mem_erase.2 ⟨hxx, hx⟩)
    · intro x hx y hy hxy
      by_cases hxx : x = x₀
      · have hyx₀ : y ≠ x₀ := fun hc => hxy (hxx.trans hc.symm)
        have hyE : y ∈ R.erase x₀ := Finset.mem_erase.2 ⟨hyx₀, hy⟩
        rw [hxx, Function.update_self, Function.update_of_ne hyx₀]
        exact ((hdisj y hyE).mono_right (Finset.subset_union_right)).symm
      · by_cases hyy : y = x₀
        · have hxE : x ∈ R.erase x₀ := Finset.mem_erase.2 ⟨hxx, hx⟩
          rw [hyy, Function.update_self, Function.update_of_ne hxx]
          exact (hdisj x hxE).mono_right (Finset.subset_union_right)
        · rw [Function.update_of_ne hxx, Function.update_of_ne hyy]
          exact hpair (Finset.mem_erase.2 ⟨hxx, hx⟩) (Finset.mem_erase.2 ⟨hyy, hy⟩) hxy
    · intro x hx
      by_cases hxx : x = x₀
      · rw [hxx, Function.update_self]
        exact hMF
      · rw [Function.update_of_ne hxx]
        exact (hdisj x (Finset.mem_erase.2 ⟨hxx, hx⟩)).mono_right Finset.subset_union_left

/-- **Edge-disjoint perfect matchings of all the apex neighbourhoods**, from the spread clause and
a potential bound at the start of the sweep. -/
theorem exists_matchings_of_spread {H : Finset (Sym2 V)}
    {U W : Finset V} {q : ℝ} {s₁ s₂ : ℕ} (hq : 0 ≤ q) (hloop : ∀ e ∈ H, ¬ e.IsDiag)
    (hUW : Disjoint U W)
    (hEven : ∀ x ∈ U, Even (nbhdIn H x W).card)
    (hmindeg : ∀ x ∈ U, ∀ v ∈ nbhdIn H x W,
      (nbhdIn H x W).card / 2 + s₂ + s₁ ≤ edeg (edgesIn H (nbhdIn H x W)) v)
    (hcodeg : ∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → (codegTo H x x' W : ℝ) ≤ q * ((s₂ : ℝ) + 1))
    (hpot : pot H W q ∅ U < 2 ^ (s₁ + 1)) :
    ∃ Mx : V → Finset (Finset V), (∀ x ∈ U, GoodMatching H W x (Mx x)) ∧
      (U : Set V).Pairwise (fun x y => Disjoint (famEdges (Mx x)) (famEdges (Mx y))) := by
  obtain ⟨Mx, hgood, hpair, -⟩ :=
    spread_process hq hloop hUW hEven hmindeg hcodeg U (le_refl U) ∅ hpot
  exact ⟨Mx, hgood, hpair⟩


end BKLOK2
