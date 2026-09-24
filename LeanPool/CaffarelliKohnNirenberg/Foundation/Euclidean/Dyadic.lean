/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Positivity

/-!
# Dyadic cubes in the native three-dimensional carrier

The cubes use the half-open product grid on `Vec3 = Fin 3 → ℝ`.  The scale
index is integral so that parent and child cubes are represented uniformly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Euclidean

abbrev DyadicCorner := Fin 3 → ℤ

structure DyadicIndex where
  scale : ℤ
  corner : DyadicCorner

def dyadicScale (k : ℤ) : ℝ := (2 : ℝ) ^ (-k : ℤ)

def dyadicCube (k : ℤ) (a : DyadicCorner) : Set Vec3 :=
  Set.univ.pi (fun i => Ico ((a i : ℝ) * dyadicScale k)
    (((a i : ℝ) + 1) * dyadicScale k))

def dyadicCubeCenter (k : ℤ) (a : DyadicCorner) : Vec3 :=
  fun i => ((a i : ℝ) + 1 / 2) * dyadicScale k

def dyadicCorner (k : ℤ) (x : Vec3) : DyadicCorner :=
  fun i => ⌊x i / dyadicScale k⌋

def dyadicParent (Q : DyadicIndex) : DyadicIndex :=
  { scale := Q.scale - 1
    corner := fun i => Q.corner i / 2 }

@[simp] theorem mem_dyadicCube {k : ℤ} {a : DyadicCorner} {x : Vec3} :
    x ∈ dyadicCube k a ↔
      ∀ i, (a i : ℝ) * dyadicScale k ≤ x i ∧
        x i < ((a i : ℝ) + 1) * dyadicScale k := by
  simp [dyadicCube]

theorem dyadicScale_pos (k : ℤ) : 0 < dyadicScale k := by
  dsimp [dyadicScale]
  positivity

theorem dyadicCube_measurable (k : ℤ) (a : DyadicCorner) :
    MeasurableSet (dyadicCube k a) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i hi
  exact measurableSet_Ico

theorem volume_dyadicCube (k : ℤ) (a : DyadicCorner) :
    volume (dyadicCube k a) = ENNReal.ofReal (dyadicScale k) ^ (3 : ℕ) := by
  rw [dyadicCube, Real.volume_pi_Ico]
  simp only [add_mul, one_mul, add_sub_cancel_left]
  norm_num [Fin.prod_univ_succ]

theorem volume_dyadicCube_eq_pow (k : ℤ) (a : DyadicCorner) :
    volume (dyadicCube k a) = ENNReal.ofReal ((8 : ℝ) ^ (-k : ℤ)) := by
  rw [volume_dyadicCube]
  rw [← ENNReal.ofReal_pow (dyadicScale_pos k).le]
  congr 1
  dsimp [dyadicScale]
  calc
    ((2 : ℝ) ^ (-k : ℤ)) ^ (3 : ℕ) = (2 : ℝ) ^ (3 * (-k : ℤ)) := by
      symm
      exact zpow_mul' 2 3 (-k)
    _ = ((2 : ℝ) ^ (3 : ℤ)) ^ (-k : ℤ) := by
      exact zpow_mul 2 3 (-k)
    _ = (8 : ℝ) ^ (-k : ℤ) := by norm_num

theorem dyadicCube_nonempty (k : ℤ) (a : DyadicCorner) :
    (dyadicCube k a).Nonempty := by
  refine ⟨dyadicCubeCenter k a, ?_⟩
  rw [mem_dyadicCube]
  dsimp [dyadicCubeCenter]
  intro i
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  constructor <;> nlinarith only [hs]

theorem mem_dyadicCube_of_corner (k : ℤ) (x : Vec3) :
    x ∈ dyadicCube k (dyadicCorner k x) := by
  rw [mem_dyadicCube]
  intro i
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  constructor
  · exact (le_div_iff₀ hs).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hs).mp (Int.lt_floor_add_one _)

theorem dyadicCorner_unique {k : ℤ} {x : Vec3} {a b : DyadicCorner}
    (ha : x ∈ dyadicCube k a) (hb : x ∈ dyadicCube k b) : a = b := by
  funext i
  have hscale : 0 < dyadicScale k := dyadicScale_pos k
  have ha' := (mem_dyadicCube.mp ha) i
  have hb' := (mem_dyadicCube.mp hb) i
  apply le_antisymm
  · apply (Int.cast_le (R := ℝ)).1
    apply le_of_not_gt
    intro hlt
    have hltInt : b i < a i := Int.cast_lt.mp hlt
    have hlt' : (b i : ℝ) + 1 ≤ a i := by
      exact_mod_cast (Int.add_one_le_iff.mpr hltInt)
    nlinarith only [ha'.1, hb'.2, hscale, hlt']
  · apply (Int.cast_le (R := ℝ)).1
    apply le_of_not_gt
    intro hlt
    have hltInt : a i < b i := Int.cast_lt.mp hlt
    have hlt' : (a i : ℝ) + 1 ≤ b i := by
      exact_mod_cast (Int.add_one_le_iff.mpr hltInt)
    nlinarith only [ha'.2, hb'.1, hscale, hlt']

theorem dyadicCube_unique_at_scale {k : ℤ} {x : Vec3} :
    ∃! a : DyadicCorner, x ∈ dyadicCube k a := by
  refine ⟨dyadicCorner k x, mem_dyadicCube_of_corner k x, ?_⟩
  intro a ha
  exact dyadicCorner_unique ha (mem_dyadicCube_of_corner k x)

theorem dyadicCube_subset_closedBall {k : ℤ} {a : DyadicCorner}
    {x : Vec3} (hx : x ∈ dyadicCube k a) :
    dyadicCube k a ⊆ Metric.closedBall x (dyadicScale k) := by
  intro y hy
  rw [Metric.mem_closedBall]
  rw [dist_eq_norm]
  have hscale : 0 < dyadicScale k := dyadicScale_pos k
  apply (pi_norm_le_iff_of_nonneg hscale.le).2
  intro i
  have hx' := (mem_dyadicCube.mp hx) i
  have hy' := (mem_dyadicCube.mp hy) i
  change |y i - x i| ≤ dyadicScale k
  rw [abs_le]
  constructor <;> nlinarith only [hx'.1, hx'.2, hy'.1, hy'.2, hscale]

theorem supBall_subset_dyadicCubeCenter (k : ℤ) (a : DyadicCorner) :
    Metric.ball (dyadicCubeCenter k a) (dyadicScale k / 2) ⊆
      dyadicCube k a := by
  intro x hx
  rw [Metric.mem_ball] at hx
  rw [dist_eq_norm] at hx
  rw [mem_dyadicCube]
  intro i
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  have hcoord := norm_le_pi_norm (x - dyadicCubeCenter k a) i
  have hxi : |x i - dyadicCubeCenter k a i| < dyadicScale k / 2 := by
    have hcoord' := lt_of_le_of_lt hcoord hx
    change ‖x i - dyadicCubeCenter k a i‖ < dyadicScale k / 2 at hcoord'
    simpa only [Real.norm_eq_abs] using hcoord'
  dsimp [dyadicCubeCenter] at hxi ⊢
  rw [abs_lt] at hxi
  constructor <;> nlinarith only [hxi.1, hxi.2, hs]

theorem dyadicScale_ratio {k l : ℤ} (hkl : k ≤ l) :
    ∃ m : ℤ, 0 < m ∧ dyadicScale k = (m : ℝ) * dyadicScale l := by
  let n : ℕ := Int.toNat (l - k)
  have hnonneg : 0 ≤ l - k := sub_nonneg.mpr hkl
  have hn : (l - k : ℤ) = n := by
    dsimp [n]
    exact (Int.toNat_of_nonneg hnonneg).symm
  refine ⟨(2 : ℤ) ^ n, by positivity, ?_⟩
  calc
    dyadicScale k = (2 : ℝ) ^ (-k : ℤ) := rfl
    _ = (2 : ℝ) ^ ((-l : ℤ) + (l - k)) := by congr 1; ring
    _ = (2 : ℝ) ^ (-l : ℤ) * (2 : ℝ) ^ (l - k) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (2 : ℝ) ^ (-l : ℤ) * (2 : ℝ) ^ n := by
      rw [hn, zpow_natCast]
    _ = (((2 : ℤ) ^ n : ℤ) : ℝ) * dyadicScale l := by
      have hcast : (((2 : ℤ) ^ n : ℤ) : ℝ) = (2 : ℝ) ^ n := by
        norm_cast
      rw [hcast]
      dsimp [dyadicScale]
      ring

theorem dyadicCube_subset_parent (Q : DyadicIndex) :
    dyadicCube Q.scale Q.corner ⊆
      dyadicCube (Q.scale - 1) (fun i => Q.corner i / 2) := by
  intro x hx
  rw [mem_dyadicCube]
  intro i
  have hs : dyadicScale (Q.scale - 1) = 2 * dyadicScale Q.scale := by
    dsimp [dyadicScale]
    rw [show - (Q.scale - 1) = -Q.scale + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hx' := (mem_dyadicCube.mp hx) i
  have hleft : 2 * (Q.corner i / 2) ≤ Q.corner i := by omega
  have hright : Q.corner i + 1 ≤ 2 * (Q.corner i / 2 + 1) := by omega
  have hleft' : (2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) ≤ (Q.corner i : ℝ) := by
    exact_mod_cast hleft
  have hright'' : ((Q.corner i + 1 : ℤ) : ℝ) ≤
      ((2 * (Q.corner i / 2 + 1) : ℤ) : ℝ) := by
    exact_mod_cast hright
  norm_num at hright''
  have hright' : (Q.corner i : ℝ) + 1 ≤
      (2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) + 2 := by
    calc
      (Q.corner i : ℝ) + 1 ≤
          (2 : ℝ) * (((Q.corner i / 2 : ℤ) : ℝ) + 1) := hright''
      _ = (2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) + 2 := by ring
  constructor
  · calc
      ((Q.corner i / 2 : ℤ) : ℝ) * dyadicScale (Q.scale - 1) =
          ((2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ)) * dyadicScale Q.scale := by
            rw [hs]
            ring
      _ ≤ (Q.corner i : ℝ) * dyadicScale Q.scale :=
        mul_le_mul_of_nonneg_right hleft' (dyadicScale_pos Q.scale).le
      _ ≤ x i := hx'.1
  · calc
      x i < ((Q.corner i : ℝ) + 1) * dyadicScale Q.scale := hx'.2
      _ ≤ ((2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) + 2) * dyadicScale Q.scale := by
        exact mul_le_mul_of_nonneg_right hright' (dyadicScale_pos Q.scale).le
      _ = (((Q.corner i / 2 : ℤ) : ℝ) + 1) * dyadicScale (Q.scale - 1) := by
        rw [hs]
        ring

theorem dyadicCube_subset_of_intersect {k l : ℤ} (hkl : k ≤ l)
    {a b : DyadicCorner}
    (hint : (dyadicCube k a ∩ dyadicCube l b).Nonempty) :
    dyadicCube l b ⊆ dyadicCube k a := by
  obtain ⟨x, hxa, hxb⟩ := hint
  obtain ⟨m, hm, hscale⟩ := dyadicScale_ratio hkl
  intro y hy
  rw [mem_dyadicCube]
  intro i
  have hxa' := (mem_dyadicCube.mp hxa) i
  have hxb' := (mem_dyadicCube.mp hxb) i
  have hy' := (mem_dyadicCube.mp hy) i
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hleft : (a i : ℤ) * m ≤ b i := by
    apply Int.lt_add_one_iff.mp
    have hprod : ((a i : ℝ) * (m : ℝ)) * dyadicScale l <
        ((b i : ℝ) + 1) * dyadicScale l := by
      calc
        ((a i : ℝ) * (m : ℝ)) * dyadicScale l =
            (a i : ℝ) * dyadicScale k := by rw [hscale]; ring
        _ ≤ x i := hxa'.1
        _ < ((b i : ℝ) + 1) * dyadicScale l := hxb'.2
    have hreal : (a i : ℝ) * (m : ℝ) < (b i : ℝ) + 1 := by
      exact lt_of_mul_lt_mul_right hprod (dyadicScale_pos l).le
    exact_mod_cast hreal
  have hright : b i + 1 ≤ (a i + 1) * m := by
    apply Int.add_one_le_iff.mpr
    have hprod : (b i : ℝ) * dyadicScale l <
        (((a i : ℝ) + 1) * (m : ℝ)) * dyadicScale l := by
      calc
        (b i : ℝ) * dyadicScale l ≤ x i := hxb'.1
        _ < ((a i : ℝ) + 1) * dyadicScale k := hxa'.2
        _ = (((a i : ℝ) + 1) * (m : ℝ)) * dyadicScale l := by
          rw [hscale]
          ring
    have hreal : (b i : ℝ) < ((a i : ℝ) + 1) * (m : ℝ) := by
      exact lt_of_mul_lt_mul_right hprod (dyadicScale_pos l).le
    exact_mod_cast hreal
  constructor
  · have hleft' : (a i : ℝ) * (m : ℝ) ≤ b i := by exact_mod_cast hleft
    calc
      (a i : ℝ) * dyadicScale k =
          ((a i : ℝ) * (m : ℝ)) * dyadicScale l := by rw [hscale]; ring
      _ ≤ (b i : ℝ) * dyadicScale l :=
        mul_le_mul_of_nonneg_right hleft' (dyadicScale_pos l).le
      _ ≤ y i := hy'.1
  · have hright' : (b i : ℝ) + 1 ≤ ((a i : ℝ) + 1) * (m : ℝ) := by
      exact_mod_cast hright
    calc
      y i < ((b i : ℝ) + 1) * dyadicScale l := hy'.2
      _ ≤ (((a i : ℝ) + 1) * (m : ℝ)) * dyadicScale l :=
        mul_le_mul_of_nonneg_right hright' (dyadicScale_pos l).le
      _ = ((a i : ℝ) + 1) * dyadicScale k := by rw [hscale]; ring

theorem dyadicCube_nested_or_disjoint (Q R : DyadicIndex) :
    dyadicCube Q.scale Q.corner ⊆ dyadicCube R.scale R.corner ∨
      dyadicCube R.scale R.corner ⊆ dyadicCube Q.scale Q.corner ∨
      Disjoint (dyadicCube Q.scale Q.corner) (dyadicCube R.scale R.corner) := by
  by_cases hQR : Q.scale ≤ R.scale
  · by_cases hint : (dyadicCube Q.scale Q.corner ∩
        dyadicCube R.scale R.corner).Nonempty
    · exact Or.inr (Or.inl (dyadicCube_subset_of_intersect hQR hint))
    · exact Or.inr (Or.inr (Set.disjoint_left.2 (by
        intro x hxQ hxR
        exact hint ⟨x, hxQ, hxR⟩)))
  · have hRQ : R.scale ≤ Q.scale := le_of_not_ge hQR
    by_cases hint : (dyadicCube Q.scale Q.corner ∩
        dyadicCube R.scale R.corner).Nonempty
    · have hint' : (dyadicCube R.scale R.corner ∩
          dyadicCube Q.scale Q.corner).Nonempty := by
        obtain ⟨x, hxQ, hxR⟩ := hint
        exact ⟨x, hxR, hxQ⟩
      exact Or.inl (dyadicCube_subset_of_intersect hRQ hint')
    · exact Or.inr (Or.inr (Set.disjoint_left.2 (by
        intro x hxQ hxR
        exact hint ⟨x, hxQ, hxR⟩)))

theorem dyadicParent_volume_ratio (Q : DyadicIndex) :
    volume (dyadicCube (dyadicParent Q).scale (dyadicParent Q).corner) =
      8 * volume (dyadicCube Q.scale Q.corner) := by
  change volume (dyadicCube (Q.scale - 1) (fun i => Q.corner i / 2)) =
      8 * volume (dyadicCube Q.scale Q.corner)
  rw [volume_dyadicCube, volume_dyadicCube]
  have hs : dyadicScale (Q.scale - 1) = 2 * dyadicScale Q.scale := by
    dsimp [dyadicScale]
    rw [show - (Q.scale - 1) = -Q.scale + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [hs, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [mul_pow]
  norm_num

end CKN.Foundation.Euclidean
