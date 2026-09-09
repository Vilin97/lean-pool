/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Instances.Int
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Rational auxiliary slots separated under bounded covering powers

This file constructs the rational centers required in Lemma 8.3 for the
specific covering matrix `J = [[3,1],[1,5]]`. The centers are explicit.
Finite-dimensional continuity then gives a single positive rectangle radius,
including padding and injectivity modulo the integer lattice.
-/

noncomputable section

namespace NavierStokes.SlotGeometry

open Set
open scoped Topology

abbrev Plane := ℝ × ℝ

/-- The actual integer covering matrix from the manuscript. -/
def cover : Plane →L[ℝ] Plane :=
  (3 • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ + 5 • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem cover_apply (x : Plane) :
    cover x = (3 * x.1 + x.2, x.1 + 5 * x.2) := by
  simp [cover]

theorem cover_injective : Function.Injective cover := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [cover_apply] at h1 h2
  apply Prod.ext <;> linarith

theorem cover_pow_injective (n : ℕ) : Function.Injective (cover ^ n : Plane →L[ℝ] Plane) := by
  induction n with
  | zero => simpa using Function.injective_id
  | succ n ih =>
      intro x y h
      rw [pow_succ', _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp] at h
      exact ih (cover_injective h)

theorem norm_cover_le (x : Plane) : ‖cover x‖ ≤ 6 * ‖x‖ := by
  have hx : |x.1| ≤ ‖x‖ := le_max_left _ _
  have hy : |x.2| ≤ ‖x‖ := le_max_right _ _
  rw [cover_apply]
  change max |3 * x.1 + x.2| |x.1 + 5 * x.2| ≤ 6 * ‖x‖
  apply max_le
  · calc
      |3 * x.1 + x.2| ≤ |3 * x.1| + |x.2| := abs_add_le _ _
      _ ≤ 6 * ‖x‖ := by rw [abs_mul]; norm_num; linarith [norm_nonneg x]
  · calc
      |x.1 + 5 * x.2| ≤ |x.1| + |5 * x.2| := abs_add_le _ _
      _ ≤ 6 * ‖x‖ := by rw [abs_mul]; norm_num; linarith

theorem norm_cover_pow_le (n : ℕ) (x : Plane) :
    ‖(cover ^ n) x‖ ≤ (6 : ℝ) ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', _root_.mul_apply_eq_comp, pow_succ']
      calc
        ‖cover ((cover ^ n) x)‖ ≤ 6 * ‖(cover ^ n) x‖ := norm_cover_le _
        _ ≤ 6 * ((6 : ℝ) ^ n * ‖x‖) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by ring

theorem cover_pow_positive (n : ℕ) (x : Plane) (hx : 0 < x.1) (hy : 0 ≤ x.2) :
    0 < ((cover ^ n) x).1 ∧ 0 ≤ ((cover ^ n) x).2 := by
  induction n with
  | zero => simpa using And.intro hx hy
  | succ n ih =>
      rw [pow_succ', _root_.mul_apply_eq_comp, cover_apply]
      dsimp
      constructor <;> linarith [ih.1, ih.2]

theorem cover_pow_second_positive {n : ℕ} (hn : 0 < n) (x : Plane)
    (hx : 0 < x.1) (hy : 0 ≤ x.2) : 0 < ((cover ^ n) x).2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hp := cover_pow_positive k x hx hy
  rw [pow_succ', _root_.mul_apply_eq_comp, cover_apply]
  dsimp
  linarith [hp.1, hp.2]

def denominator (m D : ℕ) : ℝ := ((m : ℝ) + 1) * (6 : ℝ) ^ D

theorem denominator_pos (m D : ℕ) : 0 < denominator m D := by
  unfold denominator
  positivity

/-- Explicit rational centers: they lie on the horizontal line `Y₂=0`. -/
def center (m D : ℕ) (i : Fin m) : Plane :=
  (((i.val : ℝ) + 1) / denominator m D, 0)

theorem center_rational (m D : ℕ) (i : Fin m) :
    ∃ a b : ℚ, center m D i = ((a : ℝ), (b : ℝ)) := by
  refine ⟨((i.val : ℚ) + 1) / (((m : ℚ) + 1) * 6 ^ D), 0, ?_⟩
  simp [center, denominator]

theorem center_first_pos (m D : ℕ) (i : Fin m) : 0 < (center m D i).1 := by
  exact div_pos (by positivity) (denominator_pos m D)

theorem center_norm (m D : ℕ) (i : Fin m) : ‖center m D i‖ = (center m D i).1 := by
  change max |(center m D i).1| |(0 : ℝ)| = (center m D i).1
  rw [abs_zero, abs_of_pos (center_first_pos m D i),
    max_eq_left (center_first_pos m D i).le]

theorem scaled_center_lt_one (m D : ℕ) (i : Fin m) :
    (6 : ℝ) ^ D * ‖center m D i‖ < 1 := by
  rw [center_norm]
  have heq : (6 : ℝ) ^ D * (center m D i).1 = ((i.val : ℝ) + 1) / ((m : ℝ) + 1) := by
    unfold center denominator
    dsimp
    field_simp
  rw [heq]
  apply (div_lt_one (by positivity : 0 < (m : ℝ) + 1)).mpr
  exact_mod_cast Nat.add_lt_add_right i.isLt 1

theorem center_injective (m D : ℕ) : Function.Injective (center m D) := by
  intro i j h
  have h1 := congrArg Prod.fst h
  change ((i.val : ℝ) + 1) / denominator m D =
    ((j.val : ℝ) + 1) / denominator m D at h1
  have hnum := (div_left_inj' (ne_of_gt (denominator_pos m D))).mp h1
  apply Fin.ext
  exact_mod_cast (add_right_cancel hnum)

def lattice : Set Plane := (Set.range (Int.cast : ℤ → ℝ)) ×ˢ (Set.range (Int.cast : ℤ → ℝ))

/-- Equality on the torus, stated on its universal cover. -/
def torusEq (x y : Plane) : Prop := x - y ∈ lattice

theorem isClosed_lattice : IsClosed lattice :=
  Int.isClosedEmbedding_coe_real.isClosed_range.prod Int.isClosedEmbedding_coe_real.isClosed_range

theorem lattice_norm_lt_one {x : Plane} (hx : x ∈ lattice) (hn : ‖x‖ < 1) : x = 0 := by
  rcases hx with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hx1 : |x.1| < 1 := lt_of_le_of_lt (le_max_left _ _) hn
  have hx2 : |x.2| < 1 := lt_of_le_of_lt (le_max_right _ _) hn
  rw [← ha] at hx1
  rw [← hb] at hx2
  have ha0 : a = 0 := by
    have : |a| < (1 : ℤ) := by exact_mod_cast hx1
    have := abs_lt.mp this
    omega
  have hb0 : b = 0 := by
    have : |b| < (1 : ℤ) := by exact_mod_cast hx2
    have := abs_lt.mp this
    omega
  apply Prod.ext
  · simpa [ha0] using ha.symm
  · simpa [hb0] using hb.symm

theorem torusEq_of_unit_square {x y : Plane} (hxy : torusEq x y)
    (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) (hy1 : 0 ≤ y.1) (hy2 : 0 ≤ y.2)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : x = y := by
  have hx1' : x.1 < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) (le_max_left _ _)) hx
  have hx2' : x.2 < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) (le_max_right _ _)) hx
  have hy1' : y.1 < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) (le_max_left _ _)) hy
  have hy2' : y.2 < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) (le_max_right _ _)) hy
  apply sub_eq_zero.mp
  apply lattice_norm_lt_one hxy
  change max |x.1 - y.1| |x.2 - y.2| < 1
  rw [max_lt_iff, abs_lt, abs_lt]
  constructor <;> constructor <;> linarith

theorem cover_center_norm_lt_one (m D : ℕ) (i : Fin m) (n : ℕ) (hn : n ≤ D) :
    ‖(cover ^ n) (center m D i)‖ < 1 := by
  calc
    ‖(cover ^ n) (center m D i)‖ ≤ (6 : ℝ) ^ n * ‖center m D i‖ := norm_cover_pow_le _ _
    _ ≤ (6 : ℝ) ^ D * ‖center m D i‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (norm_nonneg _)
    _ < 1 := scaled_center_lt_one m D i

/-- All forbidden coincidences are ruled out for the explicit centers,
including self-coincidence under every positive allowed covering power. -/
theorem centers_avoid_covering (m D : ℕ) (i j : Fin m) (n : ℕ) (hn : n ≤ D)
    (hij : 0 < n ∨ i ≠ j) : ¬ torusEq ((cover ^ n) (center m D i)) (center m D j) := by
  intro h
  have hi := cover_pow_positive n (center m D i) (center_first_pos m D i) le_rfl
  have hj : ‖center m D j‖ < 1 := by
    simpa using cover_center_norm_lt_one m D j 0 (Nat.zero_le D)
  have heq := torusEq_of_unit_square h hi.1.le hi.2 (center_first_pos m D j).le le_rfl
    (cover_center_norm_lt_one m D i n hn) hj
  rcases hij with hpos | hne
  · have hp := cover_pow_second_positive hpos (center m D i) (center_first_pos m D i) le_rfl
    rw [heq] at hp
    exact (lt_irrefl 0) hp
  · by_cases hn0 : n = 0
    · subst n
      exact hne (center_injective m D (by simpa using heq))
    · have hp := cover_pow_second_positive (Nat.pos_of_ne_zero hn0)
        (center m D i) (center_first_pos m D i) le_rfl
      rw [heq] at hp
      exact (lt_irrefl 0) hp

/-- Closed rectangles in the product supremum norm. -/
def rectangle (c : Plane) (r : ℝ) : Set Plane := {x | ‖x - c‖ ≤ r}

private def separationOffsets (m D : ℕ) (n : Fin (D + 1)) (i j : Fin m) :
    Set (Plane × Plane) :=
  if 0 < n.val ∨ i ≠ j then
    {e | ¬ torusEq ((cover ^ n.val) (center m D i + e.1)) (center m D j + e.2)}
  else Set.univ

private def injectiveOffsets (n : ℕ) : Set (Plane × Plane) :=
  {e | ‖(cover ^ n) (e.1 - e.2)‖ < 1}

private theorem isOpen_separationOffsets (m D : ℕ) (n : Fin (D + 1)) (i j : Fin m) :
    IsOpen (separationOffsets m D n i j) := by
  unfold separationOffsets
  split_ifs
  · have hc : Continuous (fun e : Plane × Plane =>
        (cover ^ n.val) (center m D i + e.1) - (center m D j + e.2)) :=
      (((cover ^ n.val).continuous).comp (continuous_const.add continuous_fst)).sub
        (continuous_const.add continuous_snd)
    exact (isClosed_lattice.preimage hc).isOpen_compl
  · exact isOpen_univ

private theorem isOpen_injectiveOffsets (n : ℕ) : IsOpen (injectiveOffsets n) := by
  apply isOpen_lt _ continuous_const
  exact (((cover ^ n).continuous).comp (continuous_fst.sub continuous_snd)).norm

private def safeOffsets (m D : ℕ) : Set (Plane × Plane) :=
  (⋂ n : Fin (D + 1), injectiveOffsets n.val) ∩
    (⋂ n : Fin (D + 1), ⋂ i : Fin m, ⋂ j : Fin m, separationOffsets m D n i j)

private theorem isOpen_safeOffsets (m D : ℕ) : IsOpen (safeOffsets m D) := by
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite (fun n => isOpen_injectiveOffsets n.val)
  · apply isOpen_iInter_of_finite
    intro n
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_iInter_of_finite (fun j => isOpen_separationOffsets m D n i j)

private theorem zero_mem_safeOffsets (m D : ℕ) : (0 : Plane × Plane) ∈ safeOffsets m D := by
  constructor
  · apply mem_iInter.mpr
    intro n
    simp [injectiveOffsets]
  · apply mem_iInter.mpr
    intro n
    apply mem_iInter.mpr
    intro i
    apply mem_iInter.mpr
    intro j
    by_cases hh : 0 < n.val ∨ i ≠ j
    · rw [separationOffsets, ite_eq_left hh]
      simpa only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, add_zero] using
        centers_avoid_covering m D i j n.val (Nat.le_of_lt_succ n.isLt) hh
    · rw [separationOffsets, ite_eq_right hh]
      exact mem_univ _

private theorem exists_safe_offset_radius (m D : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ e : Plane × Plane,
      ‖e.1‖ ≤ 2 * r → ‖e.2‖ ≤ 2 * r → e ∈ safeOffsets m D := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_safeOffsets m D)
    (0 : Plane × Plane) (zero_mem_safeOffsets m D)
  refine ⟨ε / 4, by linarith, ?_⟩
  intro e he1 he2
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, Prod.norm_def]
  exact max_lt (by linarith) (by linarith)

/-- A common positive radius exists for the explicit rational centers.
The rectangles of radius `2*r` already include fixed padding.

Distinct colors have disjoint slots at equal levels, and every positive
covering difference up to `D` separates even equal colors. Every covering
power up to `D` is also injective modulo the lattice on each padded slot. -/
theorem exists_common_radius (m D : ℕ) :
    ∃ r : ℝ, 0 < r ∧
      (∀ n ≤ D, ∀ i j : Fin m, 0 < n ∨ i ≠ j →
        ∀ x ∈ rectangle (center m D i) (2 * r),
        ∀ y ∈ rectangle (center m D j) (2 * r), ¬ torusEq ((cover ^ n) x) y) ∧
      (∀ n ≤ D, ∀ i : Fin m,
        ∀ x ∈ rectangle (center m D i) (2 * r),
        ∀ y ∈ rectangle (center m D i) (2 * r),
          torusEq ((cover ^ n) x) ((cover ^ n) y) → x = y) := by
  obtain ⟨r, hr, hoffsets⟩ := exists_safe_offset_radius m D
  refine ⟨r, hr, ?_, ?_⟩
  · intro n hn i j hij x hx y hy
    let n' : Fin (D + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    have he := hoffsets (x - center m D i, y - center m D j) hx hy
    have hs := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp he.2 n') i) j
    change (x - center m D i, y - center m D j) ∈
      separationOffsets m D n' i j at hs
    have hcx : center m D i + (x - center m D i) = x := by abel
    have hcy : center m D j + (y - center m D j) = y := by abel
    simpa only [separationOffsets, n', hij, ite_eq_left, Set.mem_ofPred_eq, hcx, hcy] using hs
  · intro n hn i x hx y hy hxy
    let n' : Fin (D + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    have he := hoffsets (x - center m D i, y - center m D i) hx hy
    have hi := mem_iInter.mp he.1 n'
    change ‖(cover ^ n) ((x - center m D i) - (y - center m D i))‖ < 1 at hi
    have hsub : (x - center m D i) - (y - center m D i) = x - y := by abel
    rw [hsub, map_sub] at hi
    exact cover_pow_injective n (sub_eq_zero.mp (lattice_norm_lt_one hxy hi))

theorem torusEq_refl (x : Plane) : torusEq x x := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> simp

theorem torusEq_symm {x y : Plane} (h : torusEq x y) : torusEq y x := by
  rcases h with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨⟨-a, ?_⟩, ⟨-b, ?_⟩⟩
  · push_cast
    dsimp at ha ⊢
    linarith
  · push_cast
    dsimp at hb ⊢
    linarith

theorem torusEq_trans {x y z : Plane} (hxy : torusEq x y) (hyz : torusEq y z) :
    torusEq x z := by
  rcases hxy with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases hyz with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  refine ⟨⟨a + c, ?_⟩, ⟨b + d, ?_⟩⟩
  · push_cast
    dsimp at ha hc ⊢
    linarith
  · push_cast
    dsimp at hb hd ⊢
    linarith

/-- The covering preserves the integer lattice and therefore torus equality. -/
theorem cover_torusEq {x y : Plane} (h : torusEq x y) : torusEq (cover x) (cover y) := by
  rcases h with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨⟨3 * a + b, ?_⟩, ⟨a + 5 * b, ?_⟩⟩
  · push_cast
    simp only [Prod.fst_sub, cover_apply]
    dsimp at ha hb ⊢
    linarith
  · push_cast
    simp only [Prod.snd_sub, cover_apply]
    dsimp at ha hb ⊢
    linarith

theorem cover_pow_torusEq (n : ℕ) {x y : Plane} (h : torusEq x y) :
    torusEq ((cover ^ n) x) ((cover ^ n) y) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [pow_succ', _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp]
      exact cover_torusEq ih

/-- All periodically reindexed copies of a native slot, on the absolute lift. -/
def liftedSupport (level : ℕ) (slot : Set Plane) : Set Plane :=
  {Y | ∃ x ∈ slot, torusEq ((cover ^ level) Y) x}

theorem liftedSupport_disjoint_of_separation (level n : ℕ) (S T : Set Plane)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, ¬ torusEq ((cover ^ n) x) y) :
    Disjoint (liftedSupport level S) (liftedSupport (level + n) T) := by
  apply Set.disjoint_left.mpr
  intro Y hS hT
  rcases hS with ⟨x, hx, hYx⟩
  rcases hT with ⟨y, hy, hYy⟩
  have hcover := cover_pow_torusEq n hYx
  have hp : (cover ^ n) ((cover ^ level) Y) = (cover ^ (level + n)) Y := by
    rw [Nat.add_comm level n, pow_add, _root_.mul_apply_eq_comp]
  rw [hp] at hcover
  exact hsep x hx y hy (torusEq_trans (torusEq_symm hcover) hYy)

/-- The padded native slots are disjoint on the actual absolute lift, at
arbitrary levels whose difference is at most `D`. -/
theorem exists_disjoint_lifted_slots (m D : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ level n, n ≤ D → ∀ i j : Fin m,
      0 < n ∨ i ≠ j →
      Disjoint (liftedSupport level (rectangle (center m D i) (2 * r)))
        (liftedSupport (level + n) (rectangle (center m D j) (2 * r))) := by
  obtain ⟨r, hr, hsep, _⟩ := exists_common_radius m D
  refine ⟨r, hr, ?_⟩
  intro level n hn i j hij
  exact liftedSupport_disjoint_of_separation level n _ _ (hsep n hn i j hij)

/-- A rectangle in any two prescribed auxiliary directions. -/
def orientedRectangle (c a b : Plane) (r : ℝ) : Set Plane :=
  {x | ∃ ξ η : ℝ, |ξ| ≤ r ∧ |η| ≤ r ∧ x = c + ξ • a + η • b}

theorem orientedRectangle_subset (c a b : Plane) (r : ℝ) (hr : 0 ≤ r) :
    orientedRectangle c a b (r / (1 + ‖a‖ + ‖b‖)) ⊆ rectangle c r := by
  intro x hx
  rcases hx with ⟨ξ, η, hξ, hη, rfl⟩
  change ‖c + ξ • a + η • b - c‖ ≤ r
  have hc : c + ξ • a + η • b - c = ξ • a + η • b := by abel
  rw [hc]
  have hden : 0 < 1 + ‖a‖ + ‖b‖ := by positivity
  have hquot : 0 ≤ r / (1 + ‖a‖ + ‖b‖) := div_nonneg hr hden.le
  calc
    ‖ξ • a + η • b‖ ≤ ‖ξ • a‖ + ‖η • b‖ := norm_add_le _ _
    _ = |ξ| * ‖a‖ + |η| * ‖b‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (r / (1 + ‖a‖ + ‖b‖)) * (‖a‖ + ‖b‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hξ (norm_nonneg a),
        mul_le_mul_of_nonneg_right hη (norm_nonneg b)]
    _ ≤ (r / (1 + ‖a‖ + ‖b‖)) * (1 + ‖a‖ + ‖b‖) := by nlinarith
    _ = r := div_mul_cancel₀ _ (ne_of_gt hden)

/-- In particular this applies to the manuscript's two eigendirections.
The same coordinate radius works for all colors, levels, and padded slots. -/
theorem exists_oriented_slots (m D : ℕ) (a b : Plane) :
    ∃ r : ℝ, 0 < r ∧
      (∀ level n, n ≤ D → ∀ i j : Fin m, 0 < n ∨ i ≠ j →
        Disjoint (liftedSupport level (orientedRectangle (center m D i) a b (2 * r)))
          (liftedSupport (level + n) (orientedRectangle (center m D j) a b (2 * r)))) ∧
      (∀ n ≤ D, ∀ i : Fin m,
        ∀ x ∈ orientedRectangle (center m D i) a b (2 * r),
        ∀ y ∈ orientedRectangle (center m D i) a b (2 * r),
          torusEq ((cover ^ n) x) ((cover ^ n) y) → x = y) := by
  obtain ⟨R, hR, hsep, hinj⟩ := exists_common_radius m D
  let r := R / (1 + ‖a‖ + ‖b‖)
  have hr : 0 < r := div_pos hR (by positivity)
  have hsub (i : Fin m) : orientedRectangle (center m D i) a b (2 * r) ⊆
      rectangle (center m D i) (2 * R) := by
    simpa only [r, mul_div_assoc] using
      orientedRectangle_subset (center m D i) a b (2 * R) (by positivity)
  refine ⟨r, hr, ?_, ?_⟩
  · intro level n hn i j hij
    apply liftedSupport_disjoint_of_separation
    intro x hx y hy
    exact hsep n hn i j hij x (hsub i hx) y (hsub j hy)
  · intro n hn i x hx y hy hxy
    exact hinj n hn i x (hsub i hx) y (hsub i hy) hxy

/-- The manuscript's axes are `(1,-β)` and `(β,1)`, with `β=sqrt(2)-1`.
They define genuine coordinates for every real `β`. -/
theorem rotated_axes_injective (β : ℝ) :
    Function.Injective (fun q : Plane =>
      q.1 • ((1, -β) : Plane) + q.2 • ((β, 1) : Plane)) := by
  intro q z h
  have h1 : q.1 + β * q.2 = z.1 + β * z.2 := by
    simpa [mul_comm] using congrArg Prod.fst h
  have h2 : -β * q.1 + q.2 = -β * z.1 + z.2 := by
    simpa [mul_comm] using congrArg Prod.snd h
  have hdet : (1 + β ^ 2) ≠ 0 := by nlinarith [sq_nonneg β]
  have hprod : (1 + β ^ 2) * (q.1 - z.1) = 0 := by
    have hm := congrArg (fun t : ℝ => β * t) h2
    nlinarith
  have hq : q.1 = z.1 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdet)
  exact Prod.ext hq (by rw [hq] at h2; linarith)

/-- Application to any label family with a finite proper coloring and a
bounded difference of interacting levels. Constructing that coloring from
the physical grid is a separate combinatorial obligation. -/
theorem colored_labels_have_slots {Label : Type*} (m D : ℕ) (a b : Plane)
    (Adj : Label → Label → Prop) (color : Label → Fin m) (level : Label → ℕ)
    (hcolor : ∀ i j, Adj i j → color i ≠ color j)
    (hlevel : ∀ i j, Adj i j → level i ≤ level j + D ∧ level j ≤ level i + D) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j, Adj i j →
      Disjoint
        (liftedSupport (level i) (orientedRectangle (center m D (color i)) a b (2 * r)))
        (liftedSupport (level j) (orientedRectangle (center m D (color j)) a b (2 * r))) := by
  obtain ⟨r, hr, hslots, _⟩ := exists_oriented_slots m D a b
  refine ⟨r, hr, ?_⟩
  intro i j hij
  have hc := hcolor i j hij
  have hd := hlevel i j hij
  rcases le_total (level i) (level j) with hle | hle
  · have hd' : level j - level i ≤ D := by omega
    have h := hslots (level i) (level j - level i) hd' (color i) (color j) (Or.inr hc)
    have heq : level i + (level j - level i) = level j := by omega
    simpa only [heq] using h
  · have hd' : level i - level j ≤ D := by omega
    have h := hslots (level j) (level i - level j) hd' (color j) (color i) (Or.inr hc.symm)
    have heq : level j + (level i - level j) = level i := by omega
    simpa only [heq] using h.symm

end NavierStokes.SlotGeometry
