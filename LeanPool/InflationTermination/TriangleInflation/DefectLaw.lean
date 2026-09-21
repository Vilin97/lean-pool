/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Defect

/-!
# The defect cube: laws of triangles, symmetry, and the diagonal

Proofs of paper Lemma 5.5 (`lem:triangle-law`), equation (eq:s), Lemma 5.6
(`lem:symmetry`) and Lemma 5.9 (`lem:diag`). The independence lemmas they build on are in
`Defect.lean`.

The three substantive proofs share one mechanism. The output of a copied observation is
the conjunction "my private bit is `0`, and every defect on my line is `0`", so it is the
indicator `allFalse S` that a block `S` of root bits is all-zero. Under a product weight
such an indicator has marginal `Bern(∏_{u ∈ S} w_u(0))` (`pushforward_allFalse`), and
indicators of disjoint blocks are independent (`indep_of_disjoint_support`). Lemma 5.5
splits the root bits read by `Δ_{ijk}` into four disjoint blocks — the shared cell
`(i,j,k)`, and for each of the three observations its private bit together with the `t-1`
remaining cells of its line — and assembles the four marginals into `Q(ε,r)`.
-/

namespace TriangleInflation

open Finset

/-! ## Private helpers

Everything in `DefectLawAux` is auxiliary to the four statements below.
-/

namespace DefectLawAux

/-- The indicator that every coordinate in `S` is `false`. -/
private def allFalse {ι : Type*} (S : Finset ι) (x : ι → Bool) : Bool :=
  decide (∀ u ∈ S, x u = false)

private theorem allFalse_congr {ι : Type*} (S : Finset ι) {x y : ι → Bool}
    (h : ∀ i ∈ S, x i = y i) : allFalse S x = allFalse S y := by
  simp only [allFalse, decide_eq_decide]
  constructor <;> intro H u hu
  · rw [← h u hu]; exact H u hu
  · rw [h u hu]; exact H u hu

noncomputable
section

private theorem pushforward_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (w : α → ℝ) (F : α → β) (G : β → γ) :
    pushforward (pushforward w F) G = pushforward w (fun a => G (F a)) := by
  funext c
  simp only [pushforward]
  have key : ∀ b : β, (if G b = c then ∑ a, (if F a = b then w a else 0) else 0)
      = ∑ a, (if F a = b then (if G b = c then w a else 0) else 0) := by
    intro b
    by_cases h : G b = c <;> simp [h]
  rw [Finset.sum_congr rfl (fun b _ => key b), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (F a) (fun b => if G b = c then w a else 0)]
  simp

private theorem sum_prod_bool {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Bool → ℝ) :
    ∑ x : ι → Bool, ∏ i, f i (x i) = ∏ i, ∑ b, f i b := by
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]

private theorem prodLaw_total {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → Bool → ℝ}
    (hw : ∀ i, IsLaw (w i)) : ∑ x : ι → Bool, prodLaw w x = 1 := by
  simp only [prodLaw]
  rw [sum_prod_bool]
  exact Finset.prod_eq_one (fun i _ => (hw i).2)

private theorem sum_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (F : α → β) : ∑ b, pushforward w F b = ∑ a, w a := by
  simp only [pushforward]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (F a) (fun _ => w a)]
  simp

private theorem allFalse_eq_true {ι : Type*} (S : Finset ι) (x : ι → Bool) :
    allFalse S x = true ↔ ∀ u ∈ S, x u = false := by
  simp [allFalse]

private theorem pushforward_allFalse_true {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i)) (S : Finset ι) :
    pushforward (prodLaw w) (allFalse S) true = ∏ u ∈ S, w u false := by
  simp only [pushforward, prodLaw]
  have key : ∀ x : ι → Bool,
      (if allFalse S x = true then (∏ i, w i (x i)) else 0)
        = ∏ i, (if i ∈ S then (if x i = true then 0 else w i (x i)) else w i (x i)) := by
    intro x
    by_cases h : ∀ u ∈ S, x u = false
    · rw [ite_eq_left ((allFalse_eq_true S x).mpr h)]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi, ite_eq_right (by rw [h i hi]; simp)]
      · rw [ite_eq_right hi]
    · rw [ite_eq_right (fun hc => h ((allFalse_eq_true S x).mp hc))]
      obtain ⟨u, hu, hxu⟩ : ∃ u ∈ S, x u ≠ false := by
        by_contra hc
        exact h (fun u hu => by
          by_contra hd
          exact hc ⟨u, hu, hd⟩)
      refine (Finset.prod_eq_zero (Finset.mem_univ u) ?_).symm
      rw [ite_eq_left hu, ite_eq_left (by simpa using hxu)]
  rw [Finset.sum_congr rfl (fun x _ => key x),
    sum_prod_bool (fun i b => if i ∈ S then (if b = true then 0 else w i b) else w i b)]
  rw [show (∏ u ∈ S, w u false) = ∏ i ∈ Finset.univ, (if i ∈ S then w i false else 1) by
    rw [Finset.prod_ite_mem, Finset.univ_inter]]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [hi, ite_false, Fintype.sum_bool]
    simpa [Fintype.sum_bool] using (hw i).2

private theorem pushforward_allFalse {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i)) (S : Finset ι) :
    pushforward (prodLaw w) (allFalse S) = bern (∏ u ∈ S, w u false) := by
  have htot : ∑ b, pushforward (prodLaw w) (allFalse S) b = 1 := by
    rw [sum_pushforward]; exact prodLaw_total hw
  rw [Fintype.sum_bool, pushforward_allFalse_true hw] at htot
  funext b
  cases b
  · have hb : bern (∏ u ∈ S, w u false) false = 1 - ∏ u ∈ S, w u false := by simp [bern]
    rw [hb]; linarith
  · have hb : bern (∏ u ∈ S, w u false) true = ∏ u ∈ S, w u false := by simp [bern]
    rw [hb]; exact pushforward_allFalse_true hw S

private theorem isLaw_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsLaw (bern p) := by
  constructor
  · intro b; cases b <;> simp [bern] <;> linarith
  · simp [bern]

private theorem isLaw_rootWeight {t : ℕ} {ε s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (u : Root t) : IsLaw (rootWeight t ε s u) := by
  cases u with
  | inl c => exact isLaw_bern hε0 hε1
  | inr v => exact isLaw_bern hs0 hs1
/-! ### The four root blocks of a copied triangle -/

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The cells on the line of `A^{ij}` other than `(i,j,k)`. -/
private def cellsA {t : ℕ} (i j k : Fin t) : Finset (Cell t) :=
  (Finset.univ.erase k).image (fun m => (i, j, m))

/-- The cells on the line of `B^{ik}` other than `(i,j,k)`. -/
private def cellsB {t : ℕ} (i j k : Fin t) : Finset (Cell t) :=
  (Finset.univ.erase j).image (fun m => (i, m, k))

/-- The cells on the line of `C^{jk}` other than `(i,j,k)`. -/
private def cellsC {t : ℕ} (i j k : Fin t) : Finset (Cell t) :=
  (Finset.univ.erase i).image (fun m => (m, j, k))

private theorem mem_cellsA {t : ℕ} (i j k : Fin t) (c : Cell t) :
    c ∈ cellsA i j k ↔ c.1 = i ∧ c.2.1 = j ∧ c.2.2 ≠ k := by
  obtain ⟨c1, c2, c3⟩ := c
  simp only [cellsA, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
    Prod.mk.injEq]
  constructor
  · rintro ⟨m, hm, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, hm⟩
  · rintro ⟨rfl, rfl, h3⟩; exact ⟨c3, h3, rfl, rfl, rfl⟩

private theorem mem_cellsB {t : ℕ} (i j k : Fin t) (c : Cell t) :
    c ∈ cellsB i j k ↔ c.1 = i ∧ c.2.2 = k ∧ c.2.1 ≠ j := by
  obtain ⟨c1, c2, c3⟩ := c
  simp only [cellsB, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
    Prod.mk.injEq]
  constructor
  · rintro ⟨m, hm, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, hm⟩
  · rintro ⟨rfl, rfl, h3⟩; exact ⟨c2, h3, rfl, rfl, rfl⟩

private theorem mem_cellsC {t : ℕ} (i j k : Fin t) (c : Cell t) :
    c ∈ cellsC i j k ↔ c.2.1 = j ∧ c.2.2 = k ∧ c.1 ≠ i := by
  obtain ⟨c1, c2, c3⟩ := c
  simp only [cellsC, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
    Prod.mk.injEq]
  constructor
  · rintro ⟨m, hm, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, hm⟩
  · rintro ⟨rfl, rfl, h3⟩; exact ⟨c1, h3, rfl, rfl, rfl⟩

private theorem card_cellsA {t : ℕ} (i j k : Fin t) : (cellsA i j k).card = t - 1 := by
  rw [cellsA, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]

private theorem card_cellsB {t : ℕ} (i j k : Fin t) : (cellsB i j k).card = t - 1 := by
  rw [cellsB, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

private theorem card_cellsC {t : ℕ} (i j k : Fin t) : (cellsC i j k).card = t - 1 := by
  rw [cellsC, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

/-- The block of root bits carrying the shared defect cell `(i,j,k)`. -/
private def rootsD {t : ℕ} (i j k : Fin t) : Finset (Root t) := {Sum.inl (i, j, k)}

/-- The private root bits of `A^{ij}`: its own private bit and its line minus `(i,j,k)`. -/
private def rootsA {t : ℕ} (i j k : Fin t) : Finset (Root t) :=
  insert (Sum.inr (Obs.A i j)) ((cellsA i j k).image Sum.inl)

private def rootsB {t : ℕ} (i j k : Fin t) : Finset (Root t) :=
  insert (Sum.inr (Obs.B i k)) ((cellsB i j k).image Sum.inl)

private def rootsC {t : ℕ} (i j k : Fin t) : Finset (Root t) :=
  insert (Sum.inr (Obs.C j k)) ((cellsC i j k).image Sum.inl)

private theorem allFalse_roots {t : ℕ} (v : Obs t) (L : Finset (Cell t)) (x : Root t → Bool) :
    allFalse (insert (Sum.inr v) (L.image Sum.inl) : Finset (Root t)) x = true
      ↔ (x (Sum.inr v) = false ∧ ∀ c ∈ L, x (Sum.inl c) = false) := by
  simp only [allFalse, decide_eq_true_eq, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro h
    exact ⟨h _ (Or.inl rfl), fun c hc => h _ (Or.inr ⟨c, hc, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ u hu
    rcases hu with rfl | ⟨c, hc, rfl⟩
    · exact h1
    · exact h2 c hc

private theorem allFalse_rootsD {t : ℕ} (i j k : Fin t) (x : Root t → Bool) :
    allFalse (rootsD i j k) x = true ↔ x (Sum.inl (i, j, k)) = false := by
  simp [allFalse, rootsD]

/-- Disjointness of two blocks of the shape "one private bit plus a set of cells". -/
private theorem disjoint_roots {t : ℕ} {v v' : Obs t} {L L' : Finset (Cell t)}
    (hv : v ≠ v') (hL : Disjoint L L') :
    Disjoint (insert (Sum.inr v) (L.image Sum.inl) : Finset (Root t))
      (insert (Sum.inr v') (L'.image Sum.inl)) := by
  rw [Finset.disjoint_left]
  rintro u hu hu'
  simp only [Finset.mem_insert, Finset.mem_image] at hu hu'
  rcases hu with rfl | ⟨c, hc, rfl⟩ <;> rcases hu' with h | ⟨c', hc', h⟩
  · exact hv (Sum.inr.inj h)
  · cases h
  · cases h
  · exact (Finset.disjoint_left.mp hL hc) (Sum.inl.inj h ▸ hc')

private theorem disjoint_rootsD_roots {t : ℕ} {c₀ : Cell t} {v : Obs t} {L : Finset (Cell t)}
    (h : c₀ ∉ L) :
    Disjoint ({Sum.inl c₀} : Finset (Root t)) (insert (Sum.inr v) (L.image Sum.inl)) := by
  rw [Finset.disjoint_left]
  rintro u hu hu'
  simp only [Finset.mem_singleton] at hu
  subst hu
  simp only [Finset.mem_insert, Finset.mem_image] at hu'
  rcases hu' with h' | ⟨c', hc', h'⟩
  · exact absurd h' (by simp)
  · exact h (by rwa [show c' = c₀ from by simpa using h'] at hc')

private theorem outputs_A {t : ℕ} (i j k : Fin t) (x : Root t → Bool) :
    outputsOf x (Obs.A i j) = (allFalse (rootsD i j k) x && allFalse (rootsA i j k) x) := by
  refine bool_ext ?_
  rw [Bool.and_eq_true, allFalse_rootsD, rootsA, allFalse_roots]
  simp only [outputsOf, outputs, decide_eq_true_eq]
  constructor
  · rintro ⟨hN, hd⟩
    refine ⟨hd _ (by simp [onLine]), hN, fun c hc => hd c ?_⟩
    rw [mem_cellsA] at hc
    simp [onLine, hc.1, hc.2.1]
  · rintro ⟨hD, hN, hrest⟩
    refine ⟨hN, fun c hc => ?_⟩
    simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hc
    by_cases hk : c.2.2 = k
    · have hce : c = (i, j, k) := by
        obtain ⟨c1, c2, c3⟩ := c; simp_all
      rw [hce]; exact hD
    · exact hrest c (by rw [mem_cellsA]; exact ⟨hc.1, hc.2, hk⟩)

private theorem outputs_B {t : ℕ} (i j k : Fin t) (x : Root t → Bool) :
    outputsOf x (Obs.B i k) = (allFalse (rootsD i j k) x && allFalse (rootsB i j k) x) := by
  refine bool_ext ?_
  rw [Bool.and_eq_true, allFalse_rootsD, rootsB, allFalse_roots]
  simp only [outputsOf, outputs, decide_eq_true_eq]
  constructor
  · rintro ⟨hN, hd⟩
    refine ⟨hd _ (by simp [onLine]), hN, fun c hc => hd c ?_⟩
    rw [mem_cellsB] at hc
    simp [onLine, hc.1, hc.2.1]
  · rintro ⟨hD, hN, hrest⟩
    refine ⟨hN, fun c hc => ?_⟩
    simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hc
    by_cases hk : c.2.1 = j
    · have hce : c = (i, j, k) := by
        obtain ⟨c1, c2, c3⟩ := c; simp_all
      rw [hce]; exact hD
    · exact hrest c (by rw [mem_cellsB]; exact ⟨hc.1, hc.2, hk⟩)

private theorem outputs_C {t : ℕ} (i j k : Fin t) (x : Root t → Bool) :
    outputsOf x (Obs.C j k) = (allFalse (rootsD i j k) x && allFalse (rootsC i j k) x) := by
  refine bool_ext ?_
  rw [Bool.and_eq_true, allFalse_rootsD, rootsC, allFalse_roots]
  simp only [outputsOf, outputs, decide_eq_true_eq]
  constructor
  · rintro ⟨hN, hd⟩
    refine ⟨hd _ (by simp [onLine]), hN, fun c hc => hd c ?_⟩
    rw [mem_cellsC] at hc
    simp [onLine, hc.1, hc.2.1]
  · rintro ⟨hD, hN, hrest⟩
    refine ⟨hN, fun c hc => ?_⟩
    simp only [onLine, Bool.and_eq_true, beq_iff_eq] at hc
    by_cases hk : c.1 = i
    · have hce : c = (i, j, k) := by
        obtain ⟨c1, c2, c3⟩ := c; simp_all
      rw [hce]; exact hD
    · exact hrest c (by rw [mem_cellsC]; exact ⟨hc.1, hc.2, hk⟩)

/-! ### Weights and disjointness of the blocks -/

private theorem prod_rootsD {t : ℕ} (ε s : ℝ) (i j k : Fin t) :
    ∏ u ∈ rootsD i j k, rootWeight t ε s u false = 1 - ε := by
  simp [rootsD, rootWeight, bern]

private theorem prod_roots {t : ℕ} (ε s : ℝ) (v : Obs t) (L : Finset (Cell t)) :
    ∏ u ∈ (insert (Sum.inr v) (L.image Sum.inl) : Finset (Root t)), rootWeight t ε s u false
      = (1 - s) * (1 - ε) ^ L.card := by
  rw [Finset.prod_insert (by simp), Finset.prod_image (fun a _ b _ h => by simpa using h)]
  simp [rootWeight, bern, Finset.prod_const]

private theorem prod_rootsA {t : ℕ} (ε s : ℝ) (i j k : Fin t) :
    ∏ u ∈ rootsA i j k, rootWeight t ε s u false = (1 - s) * (1 - ε) ^ (t - 1) := by
  rw [rootsA, prod_roots, card_cellsA]

private theorem prod_rootsB {t : ℕ} (ε s : ℝ) (i j k : Fin t) :
    ∏ u ∈ rootsB i j k, rootWeight t ε s u false = (1 - s) * (1 - ε) ^ (t - 1) := by
  rw [rootsB, prod_roots, card_cellsB]

private theorem prod_rootsC {t : ℕ} (ε s : ℝ) (i j k : Fin t) :
    ∏ u ∈ rootsC i j k, rootWeight t ε s u false = (1 - s) * (1 - ε) ^ (t - 1) := by
  rw [rootsC, prod_roots, card_cellsC]

private theorem disjoint_cellsAB {t : ℕ} (i j k : Fin t) :
    Disjoint (cellsA i j k) (cellsB i j k) := by
  rw [Finset.disjoint_left]
  intro c hA hB
  rw [mem_cellsA] at hA
  rw [mem_cellsB] at hB
  exact hA.2.2 hB.2.1

private theorem disjoint_cellsAC {t : ℕ} (i j k : Fin t) :
    Disjoint (cellsA i j k) (cellsC i j k) := by
  rw [Finset.disjoint_left]
  intro c hA hC
  rw [mem_cellsA] at hA
  rw [mem_cellsC] at hC
  exact hA.2.2 hC.2.1

private theorem disjoint_cellsBC {t : ℕ} (i j k : Fin t) :
    Disjoint (cellsB i j k) (cellsC i j k) := by
  rw [Finset.disjoint_left]
  intro c hB hC
  rw [mem_cellsB] at hB
  rw [mem_cellsC] at hC
  exact hC.2.2 hB.1

private theorem disjoint_rootsAB {t : ℕ} (i j k : Fin t) :
    Disjoint (rootsA i j k) (rootsB i j k) :=
  disjoint_roots (by simp) (disjoint_cellsAB i j k)

private theorem disjoint_rootsAC {t : ℕ} (i j k : Fin t) :
    Disjoint (rootsA i j k) (rootsC i j k) :=
  disjoint_roots (by simp) (disjoint_cellsAC i j k)

private theorem disjoint_rootsBC {t : ℕ} (i j k : Fin t) :
    Disjoint (rootsB i j k) (rootsC i j k) :=
  disjoint_roots (by simp) (disjoint_cellsBC i j k)

private theorem disjoint_rootsDA {t : ℕ} (i j k : Fin t) :
    Disjoint (rootsD i j k) (rootsA i j k) :=
  disjoint_rootsD_roots (by rw [mem_cellsA]; rintro ⟨-, -, h⟩; exact h rfl)

private theorem disjoint_rootsDB {t : ℕ} (i j k : Fin t) :
    Disjoint (rootsD i j k) (rootsB i j k) :=
  disjoint_rootsD_roots (by rw [mem_cellsB]; rintro ⟨-, -, h⟩; exact h rfl)

private theorem disjoint_rootsDC {t : ℕ} (i j k : Fin t) :
    Disjoint (rootsD i j k) (rootsC i j k) :=
  disjoint_rootsD_roots (by rw [mem_cellsC]; rintro ⟨-, -, h⟩; exact h rfl)
/-! ### The induced permutation of root bits (Lemma 5.6) -/

/-- The action of an index permutation on copied observations, as an equivalence. -/
private def obsPermEquiv {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) : Obs t ≃ Obs t where
  toFun := Obs.perm π
  invFun := Obs.perm (π.1⁻¹, π.2.1⁻¹, π.2.2⁻¹)
  left_inv := by intro v; cases v <;> simp [Obs.perm]
  right_inv := by intro v; cases v <;> simp [Obs.perm]

private theorem obsPermEquiv_apply {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (v : Obs t) :
    obsPermEquiv π v = Obs.perm π v := rfl

/-- The action of an index permutation on the cells of the defect cube. -/
private def cellPermEquiv {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) : Cell t ≃ Cell t :=
  Equiv.prodCongr π.1 (Equiv.prodCongr π.2.1 π.2.2)

/-- The action of an index permutation on the root bits. -/
private def rootPermEquiv {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) : Root t ≃ Root t :=
  Equiv.sumCongr (cellPermEquiv π) (obsPermEquiv π)

private theorem perm_beq {t : ℕ} (σ : Equiv.Perm (Fin t)) (a b : Fin t) :
    (σ a == σ b) = (a == b) := by
  refine bool_ext ?_
  simp [EmbeddingLike.apply_eq_iff_eq]

private theorem onLine_perm {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (v : Obs t) (c : Cell t) :
    onLine (Obs.perm π v) (cellPermEquiv π c) = onLine v c := by
  obtain ⟨c1, c2, c3⟩ := c
  cases v <;>
    simp [onLine, Obs.perm, cellPermEquiv, Equiv.prodCongr_apply, Prod.map, perm_beq]

private theorem rootWeight_perm {t : ℕ} (ε s : ℝ)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (u : Root t) :
    rootWeight t ε s (rootPermEquiv π u) = rootWeight t ε s u := by
  cases u <;> rfl

private theorem prodLaw_perm {t : ℕ} (ε s : ℝ)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (x : Root t → Bool) :
    prodLaw (rootWeight t ε s) (fun u => x (rootPermEquiv π u))
      = prodLaw (rootWeight t ε s) x := by
  simp only [prodLaw]
  refine Fintype.prod_equiv (rootPermEquiv π) _ _ (fun u => ?_)
  rw [rootWeight_perm]

private theorem outputsOf_perm {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (x : Root t → Bool) :
    outputsOf (fun u => x (rootPermEquiv π u)) = relabel π (outputsOf x) := by
  funext v
  refine bool_ext ?_
  simp only [outputsOf, outputs, relabel, rootPermEquiv, Equiv.sumCongr_apply, Sum.map_inl,
    Sum.map_inr, obsPermEquiv_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨hN, hd⟩
    refine ⟨hN, fun c' hc' => ?_⟩
    have hc : onLine v ((cellPermEquiv π).symm c') = true := by
      rw [← onLine_perm π v ((cellPermEquiv π).symm c'), Equiv.apply_symm_apply]
      exact hc'
    have hx := hd _ hc
    rwa [Equiv.apply_symm_apply] at hx
  · rintro ⟨hN, hd⟩
    exact ⟨hN, fun c hc => hd _ (by rw [onLine_perm]; exact hc)⟩

/-- Relabelling assignments by an index permutation, as an equivalence of root assignments. -/
private def rootAssignPermEquiv {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    (Root t → Bool) ≃ (Root t → Bool) where
  toFun x := fun u => x (rootPermEquiv π u)
  invFun x := fun u => x ((rootPermEquiv π).symm u)
  left_inv := by intro x; funext u; simp
  right_inv := by intro x; funext u; simp

private theorem relabel_injective {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) {a b : Assign t}
    (h : relabel π a = relabel π b) : a = b := by
  funext u
  have hv := congrFun h ((obsPermEquiv π).symm u)
  simp only [relabel] at hv
  rwa [show Obs.perm π ((obsPermEquiv π).symm u) = u from
    (obsPermEquiv π).apply_symm_apply u] at hv
/-! ### Lemma 5.9 -/

private theorem ancestorsOf_diagonalTriangle {t : ℕ} (l : Fin t) (a : Latent t)
    (h : a ∈ ancestorsOf (diagonalTriangle l)) :
    a = Latent.X l ∨ a = Latent.Z l ∨ a = Latent.Y l := by
  simp only [ancestorsOf, diagonalTriangle, copiedTriangle, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton] at h
  obtain ⟨u, hu, hau⟩ := h
  rcases hu with rfl | rfl | rfl <;>
    simp only [Obs.ancestors, Finset.mem_insert, Finset.mem_singleton] at hau <;> tauto

private theorem ancestrallyIndependent_diagonal {t : ℕ} {l m : Fin t} (h : l ≠ m) :
    AncestrallyIndependent (diagonalTriangle l) (diagonalTriangle m) := by
  rw [AncestrallyIndependent, Finset.disjoint_left]
  intro a ha ha'
  have h1 := ancestorsOf_diagonalTriangle l a ha
  have h2 := ancestorsOf_diagonalTriangle m a ha'
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with h' | h' | h' <;> simp_all
end

end DefectLawAux

open DefectLawAux

noncomputable
section

/-! ## The law of a copied triangle (Lemma 5.5) -/

/-- Paper Lemma 5.5 (`lem:triangle-law`): under the defect law every copied triangle
`Δ_{ijk}` has law `Q(ε, r)` with `r = (1-s)(1-ε)^{t-1}`. -/
theorem defect_copiedTriangle_law {t : ℕ} {ε s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i j k : Fin t) :
    pushforward (defectLaw t ε s) (readTriangle i j k) = Q ε ((1 - s) * (1 - ε) ^ (t - 1)) := by
  have hw : ∀ u : Root t, IsLaw (rootWeight t ε s u) := isLaw_rootWeight hε0 hε1 hs0 hs1
  have mD : pushforward (prodLaw (rootWeight t ε s)) (allFalse (rootsD i j k))
      = bern (1 - ε) := by rw [pushforward_allFalse hw, prod_rootsD]
  have mA : pushforward (prodLaw (rootWeight t ε s)) (allFalse (rootsA i j k))
      = bern ((1 - s) * (1 - ε) ^ (t - 1)) := by rw [pushforward_allFalse hw, prod_rootsA]
  have mB : pushforward (prodLaw (rootWeight t ε s)) (allFalse (rootsB i j k))
      = bern ((1 - s) * (1 - ε) ^ (t - 1)) := by rw [pushforward_allFalse hw, prod_rootsB]
  have mC : pushforward (prodLaw (rootWeight t ε s)) (allFalse (rootsC i j k))
      = bern ((1 - s) * (1 - ε) ^ (t - 1)) := by rw [pushforward_allFalse hw, prod_rootsC]
  have hBC : pushforward (prodLaw (rootWeight t ε s))
      (fun x => (allFalse (rootsB i j k) x, allFalse (rootsC i j k) x))
      = fun q : Bool × Bool => bern ((1 - s) * (1 - ε) ^ (t - 1)) q.1
          * bern ((1 - s) * (1 - ε) ^ (t - 1)) q.2 := by
    rw [indep_of_disjoint_support (F := allFalse (rootsB i j k))
      (G := allFalse (rootsC i j k)) (I := rootsB i j k) (J := rootsC i j k) hw
      (disjoint_rootsBC i j k) (fun x y h => allFalse_congr _ h)
      (fun x y h => allFalse_congr _ h), mB, mC]
  have hABC : pushforward (prodLaw (rootWeight t ε s))
      (fun x => (allFalse (rootsA i j k) x,
        (allFalse (rootsB i j k) x, allFalse (rootsC i j k) x)))
      = fun q : Bool × Bool × Bool => bern ((1 - s) * (1 - ε) ^ (t - 1)) q.1
          * (bern ((1 - s) * (1 - ε) ^ (t - 1)) q.2.1
            * bern ((1 - s) * (1 - ε) ^ (t - 1)) q.2.2) := by
    rw [indep_of_disjoint_support (F := allFalse (rootsA i j k))
      (G := fun x => (allFalse (rootsB i j k) x, allFalse (rootsC i j k) x))
      (I := rootsA i j k) (J := rootsB i j k ∪ rootsC i j k) hw
      (by rw [Finset.disjoint_union_right]
          exact ⟨disjoint_rootsAB i j k, disjoint_rootsAC i j k⟩)
      (fun x y h => allFalse_congr _ h)
      (fun x y h => by
        rw [allFalse_congr _ (fun u hu => h u (Finset.mem_union_left _ hu)),
          allFalse_congr _ (fun u hu => h u (Finset.mem_union_right _ hu))]), mA, hBC]
  have hAll : pushforward (prodLaw (rootWeight t ε s))
      (fun x => (allFalse (rootsD i j k) x, (allFalse (rootsA i j k) x,
        (allFalse (rootsB i j k) x, allFalse (rootsC i j k) x))))
      = fun q : Bool × Bool × Bool × Bool => bern (1 - ε) q.1
          * (bern ((1 - s) * (1 - ε) ^ (t - 1)) q.2.1
            * (bern ((1 - s) * (1 - ε) ^ (t - 1)) q.2.2.1
              * bern ((1 - s) * (1 - ε) ^ (t - 1)) q.2.2.2)) := by
    rw [indep_of_disjoint_support (F := allFalse (rootsD i j k))
      (G := fun x => (allFalse (rootsA i j k) x,
        (allFalse (rootsB i j k) x, allFalse (rootsC i j k) x)))
      (I := rootsD i j k) (J := rootsA i j k ∪ (rootsB i j k ∪ rootsC i j k)) hw
      (by rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
          exact ⟨disjoint_rootsDA i j k, disjoint_rootsDB i j k, disjoint_rootsDC i j k⟩)
      (fun x y h => allFalse_congr _ h)
      (fun x y h => by
        rw [allFalse_congr (rootsA i j k) (fun u hu => h u (Finset.mem_union_left _ hu)),
          allFalse_congr (rootsB i j k)
            (fun u hu => h u (Finset.mem_union_right _ (Finset.mem_union_left _ hu))),
          allFalse_congr (rootsC i j k)
            (fun u hu => h u (Finset.mem_union_right _ (Finset.mem_union_right _ hu)))]),
      mD, hABC]
  have hfun : (fun x : Root t → Bool => readTriangle i j k (outputsOf x))
      = (fun x : Root t → Bool =>
          (((allFalse (rootsD i j k) x && allFalse (rootsA i j k) x),
            (allFalse (rootsD i j k) x && allFalse (rootsB i j k) x),
            (allFalse (rootsD i j k) x && allFalse (rootsC i j k) x)) : ThreeBit)) := by
    funext x
    simp only [readTriangle]
    rw [outputs_A i j k x, outputs_B i j k x, outputs_C i j k x]
  calc pushforward (defectLaw t ε s) (readTriangle i j k)
      = pushforward (prodLaw (rootWeight t ε s))
          (fun x => readTriangle i j k (outputsOf x)) := by
        simp only [defectLaw, rootLaw]
        rw [pushforward_comp]
    _ = pushforward (pushforward (prodLaw (rootWeight t ε s))
          (fun x => (allFalse (rootsD i j k) x, (allFalse (rootsA i j k) x,
            (allFalse (rootsB i j k) x, allFalse (rootsC i j k) x)))))
          (fun q : Bool × Bool × Bool × Bool =>
            ((q.1 && q.2.1, q.1 && q.2.2.1, q.1 && q.2.2.2) : ThreeBit)) := by
        rw [pushforward_comp, hfun]
    _ = Q ε ((1 - s) * (1 - ε) ^ (t - 1)) := by
        rw [hAll]
        funext y
        obtain ⟨y1, y2, y3⟩ := y
        simp only [pushforward, Fintype.sum_prod_type, Fintype.sum_bool, Q, bern]
        cases y1 <;> cases y2 <;> cases y3 <;>
          simp only [Bool.and_self, Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true,
            and_self, Bool.and_false, Bool.and_true, and_true, and_false, ite_true, ite_false,
            add_zero, zero_add, mul_zero, sub_sub_cancel, mul_one, mul_eq_mul_left_iff] <;>
          first | ring1 | exact Or.inl (by ring1)

/-- Paper equation (eq:s): with `s = 1 - r/(1-ε)^{t-1}` the copied-triangle parameter
`(1-s)(1-ε)^{t-1}` is `r`. -/
theorem one_sub_sParam_mul (t : ℕ) {ε r : ℝ} (hε : ε < 1) :
    (1 - sParam t ε r) * (1 - ε) ^ (t - 1) = r := by
  have hpos : (0:ℝ) < (1 - ε) ^ (t - 1) := pow_pos (by linarith) _
  simp only [sParam, sub_sub_cancel]
  exact div_mul_cancel₀ _ (ne_of_gt hpos)

/-- Paper equation (eq:s): `s ∈ [0,1]` exactly in the parameter range of Theorem 5.1. -/
theorem sParam_mem_Icc (t : ℕ) {ε r : ℝ} (hε1 : ε < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ (1 - ε) ^ (t - 1)) :
    0 ≤ sParam t ε r ∧ sParam t ε r ≤ 1 := by
  have hpos : (0:ℝ) < (1 - ε) ^ (t - 1) := pow_pos (by linarith) _
  refine ⟨?_, ?_⟩
  · simp only [sParam, sub_nonneg]
    rw [div_le_one hpos]
    exact hr1
  · simp only [sParam]
    have : 0 ≤ r / (1 - ε) ^ (t - 1) := div_nonneg hr0 hpos.le
    linarith

/-! ## Symmetry (Lemma 5.6) -/

/-- Paper Lemma 5.6 (`lem:symmetry`): the defect law is invariant under independent
permutations of the `X`-, `Z`- and `Y`-copy indices. -/
theorem defect_symmetric {t : ℕ} (ε s : ℝ) : SymmetricLaw t (defectLaw t ε s) := by
  intro π ω
  simp only [defectLaw, rootLaw, pushforward]
  refine (Fintype.sum_equiv (rootAssignPermEquiv π)
    (fun y => if outputsOf y = ω then prodLaw (rootWeight t ε s) y else 0)
    (fun x => if outputsOf x = relabel π ω then prodLaw (rootWeight t ε s) x else 0)
    (fun y => ?_)).symm
  change (if outputsOf y = ω then prodLaw (rootWeight t ε s) y else 0)
    = if outputsOf (fun u => y (rootPermEquiv π u)) = relabel π ω then
        prodLaw (rootWeight t ε s) (fun u => y (rootPermEquiv π u)) else 0
  rw [outputsOf_perm, prodLaw_perm]
  by_cases h : outputsOf y = ω
  · rw [ite_eq_left h, ite_eq_left (by rw [h])]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (relabel_injective π hc))]

/-! ## The diagonal (Lemma 5.9) -/

/-- Paper Lemma 5.9 (`lem:diag`), combinatorial half: the regions `R_l` of distinct diagonal
triangles are disjoint, since a cell cannot have two coordinates equal to `l` and two equal
to `m ≠ l`. -/
theorem diagRegion_disjoint {t : ℕ} {l m : Fin t} (h : l ≠ m) (c : Cell t) :
    ¬ (inDiagRegion l c = true ∧ inDiagRegion m c = true) := by
  rintro ⟨h1, h2⟩
  simp only [inDiagRegion, onLine, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h1 h2
  rcases h1 with (⟨a1, a2⟩ | ⟨a1, a2⟩) | ⟨a1, a2⟩ <;>
    rcases h2 with (⟨b1, b2⟩ | ⟨b1, b2⟩) | ⟨b1, b2⟩ <;> simp_all

/-- The region `R_l` of paper equation (eq:Rl) is the root support of the diagonal triangle
`Δ_{lll}` on the defect cells. -/
theorem inDiagRegion_iff {t : ℕ} (l : Fin t) (c : Cell t) :
    inDiagRegion l c = true ↔ ∃ v ∈ diagonalTriangle l, onLine v c = true := by
  simp [inDiagRegion, diagonalTriangle, copiedTriangle, or_assoc]

/-- Paper Lemma 5.9 (`lem:diag`): the `t` diagonal triangles are mutually independent under
the defect law and their joint law is `Q(ε,r)^{⊗t}` with `r = (1-s)(1-ε)^{t-1}`. This is the
tensor-power diagonal condition of Definition 2.3(ii). -/
theorem defect_diagonal_law {t : ℕ} {ε s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    pushforward (defectLaw t ε s) readDiagonal
      = tensorPow t (Q ε ((1 - s) * (1 - ε) ^ (t - 1))) := by
  have hw : ∀ u : Root t, IsLaw (rootWeight t ε s u) := isLaw_rootWeight hε0 hε1 hs0 hs1
  have hI : ∀ l m : Fin t, l ≠ m →
      Disjoint (rootSupport (diagonalTriangle l)) (rootSupport (diagonalTriangle m)) :=
    fun l m h => rootSupport_disjoint (ancestrallyIndependent_diagonal h)
  have hF : ∀ (l : Fin t) (x y : Root t → Bool),
      (∀ u ∈ rootSupport (diagonalTriangle l), x u = y u) →
      readTriangle l l l (outputsOf x) = readTriangle l l l (outputsOf y) := by
    intro l x y h
    have hr := restrictAssign_outputsOf_congr (diagonalTriangle l) x y h
    have hA : Obs.A l l ∈ diagonalTriangle l := by
      simp [diagonalTriangle, copiedTriangle]
    have hB : Obs.B l l ∈ diagonalTriangle l := by
      simp [diagonalTriangle, copiedTriangle]
    have hC : Obs.C l l ∈ diagonalTriangle l := by
      simp [diagonalTriangle, copiedTriangle]
    have eA := congrFun hr ⟨Obs.A l l, hA⟩
    have eB := congrFun hr ⟨Obs.B l l, hB⟩
    have eC := congrFun hr ⟨Obs.C l l, hC⟩
    simp only [restrictAssign] at eA eB eC
    simp only [readTriangle, eA, eB, eC]
  have hone : ∀ l : Fin t, pushforward (prodLaw (rootWeight t ε s))
      (fun x => readTriangle l l l (outputsOf x))
      = Q ε ((1 - s) * (1 - ε) ^ (t - 1)) := by
    intro l
    rw [show pushforward (prodLaw (rootWeight t ε s))
        (fun x => readTriangle l l l (outputsOf x))
        = pushforward (defectLaw t ε s) (readTriangle l l l) from by
      simp only [defectLaw, rootLaw]; rw [pushforward_comp]]
    exact defect_copiedTriangle_law hε0 hε1 hs0 hs1 l l l
  calc pushforward (defectLaw t ε s) readDiagonal
      = pushforward (prodLaw (rootWeight t ε s))
          (fun x l => readTriangle l l l (outputsOf x)) := by
        simp only [defectLaw, rootLaw]
        rw [pushforward_comp]
        rfl
    _ = fun φ : Fin t → ThreeBit => ∏ l, pushforward (prodLaw (rootWeight t ε s))
          (fun x => readTriangle l l l (outputsOf x)) (φ l) :=
        indep_of_disjoint_family (β := fun _ : Fin t => ThreeBit)
          (F := fun l x => readTriangle l l l (outputsOf x)) hw
          (I := fun l => rootSupport (diagonalTriangle l)) hI hF
    _ = tensorPow t (Q ε ((1 - s) * (1 - ε) ^ (t - 1))) := by
        funext φ
        simp only [tensorPow]
        exact Finset.prod_congr rfl (fun l _ => by rw [hone l])

end

end TriangleInflation
