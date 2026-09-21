/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

/-- The level-`n` dyadic ceiling of a nonnegative real time. -/
def dyadicCeiling (n : ℕ) (t : NNReal) : NNReal :=
  ⟨(⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) / 2 ^ n, by positivity⟩

/-- The level-`n` dyadic floor of a nonnegative real time. -/
def dyadicFloor (n : ℕ) (t : NNReal) : NNReal :=
  ⟨(⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) / 2 ^ n, by positivity⟩

/-- The real coercion of a dyadic ceiling is its defining quotient. -/
private theorem coe_dyadicCeiling (n : ℕ) (t : NNReal) :
    ((dyadicCeiling n t : NNReal) : ℝ) = (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) / 2 ^ n := rfl

/-- The real coercion of a dyadic floor is its defining quotient. -/
private theorem coe_dyadicFloor (n : ℕ) (t : NNReal) :
    ((dyadicFloor n t : NNReal) : ℝ) = (⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) / 2 ^ n := rfl

/-- The level-`n` dyadic ceiling is at least the time it approximates. -/
theorem le_dyadicCeiling (n : ℕ) (t : NNReal) : t ≤ dyadicCeiling n t := by
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc (t : ℝ) * 2 ^ n = (2 ^ n : ℝ) * (t : ℝ) := by ring
    _ ≤ (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _

/-- The level-`n` dyadic floor is at most the time it approximates. -/
theorem dyadicFloor_le (n : ℕ) (t : NNReal) : dyadicFloor n t ≤ t := by
  rw [← NNReal.coe_le_coe, coe_dyadicFloor, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc (⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ (2 ^ n : ℝ) * (t : ℝ) := Nat.floor_le (by positivity)
    _ = (t : ℝ) * 2 ^ n := by ring

/-- The level-`n` dyadic ceiling overshoots by at most one grid step. -/
theorem dyadicCeiling_le_add (n : ℕ) (t : NNReal) :
    dyadicCeiling n t ≤ t + (2 ^ n : NNReal)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hinv : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt h2)
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, div_le_iff₀ h2]
  calc (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) ≤ (2 ^ n : ℝ) * (t : ℝ) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
    _ = ((t : ℝ) + ((2 : ℝ) ^ n)⁻¹) * 2 ^ n := by rw [add_mul, hinv]; ring

/-- The ceiling comparison rewritten as an inequality between natural indices. -/
private theorem dyadicCeiling_le_iff_nat (n : ℕ) (t i : NNReal) :
    dyadicCeiling n t ≤ i ↔ ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfloor : ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ ↔
      ((⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℕ) : ℝ) ≤ (2 ^ n : ℝ) * (i : ℝ) :=
    Nat.le_floor_iff (by positivity)
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, div_le_iff₀ h2, hfloor,
    mul_comm ((2 : ℝ) ^ n) (i : ℝ)]

/-- The floor comparison rewritten as the same inequality between natural indices. -/
private theorem le_dyadicFloor_iff_nat (n : ℕ) (t i : NNReal) :
    t ≤ dyadicFloor n i ↔ ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [← NNReal.coe_le_coe, coe_dyadicFloor, le_div_iff₀ h2, Nat.ceil_le,
    mul_comm ((2 : ℝ) ^ n) (t : ℝ)]

/-- The dyadic ceiling lies below a time exactly when the time's dyadic floor lies above. -/
theorem dyadicCeiling_le_iff (n : ℕ) (t i : NNReal) :
    dyadicCeiling n t ≤ i ↔ t ≤ dyadicFloor n i :=
  (dyadicCeiling_le_iff_nat n t i).trans (le_dyadicFloor_iff_nat n t i).symm

/-- Refining the dyadic level decreases the ceiling. -/
theorem antitone_dyadicCeiling (t : NNReal) : Antitone fun n ↦ dyadicCeiling n t := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  show dyadicCeiling (n + 1) t ≤ dyadicCeiling n t
  have hceil : ⌈(2 : ℝ) ^ (n + 1) * (t : ℝ)⌉₊ ≤ 2 * ⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ := by
    rw [Nat.ceil_le]
    push_cast
    calc (2 : ℝ) ^ (n + 1) * (t : ℝ) = 2 * ((2 : ℝ) ^ n * (t : ℝ)) := by ring
      _ ≤ 2 * (⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ) := by gcongr; exact Nat.le_ceil _
  have hceilR : ((⌈(2 : ℝ) ^ (n + 1) * (t : ℝ)⌉₊ : ℕ) : ℝ) ≤
      2 * ((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast hceil
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, coe_dyadicCeiling,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((⌈(2 : ℝ) ^ (n + 1) * (t : ℝ)⌉₊ : ℕ) : ℝ) * 2 ^ n
      ≤ (2 * ((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℕ) : ℝ)) * 2 ^ n := by gcongr
    _ = ((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℕ) : ℝ) * 2 ^ (n + 1) := by ring

/-- The dyadic ceilings of a fixed time converge to that time. -/
theorem tendsto_dyadicCeiling (t : NNReal) :
    Tendsto (fun n ↦ dyadicCeiling n t) atTop (𝓝 t) := by
  have hhalf : ((2 : NNReal))⁻¹ < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.coe_one]
    norm_num
  have hinv : Tendsto (fun n : ℕ ↦ (2 ^ n : NNReal)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hhalf
  have hupper : Tendsto (fun n : ℕ ↦ t + (2 ^ n : NNReal)⁻¹) atTop (𝓝 t) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ le_dyadicCeiling n t) (fun n ↦ dyadicCeiling_le_add n t)

/-- The level-`n` dyadic grid point with index `k`. -/
def dyadicGrid (n k : ℕ) : NNReal := ⟨(k : ℝ) / 2 ^ n, by positivity⟩

/-- The grid index of the level-`n` dyadic ceiling. -/
def dyadicCeilingIndex (n : ℕ) (t : NNReal) : ℕ :=
  ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊

/-- A dyadic ceiling is the grid point at its ceiling index. -/
theorem dyadicGrid_ceilingIndex (n : ℕ) (t : NNReal) :
    dyadicGrid n (dyadicCeilingIndex n t) = dyadicCeiling n t :=
  rfl

/-- The dyadic grid is monotone in its index. -/
theorem monotone_dyadicGrid (n : ℕ) : Monotone (dyadicGrid n) := by
  intro k l hkl
  rw [← NNReal.coe_le_coe]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hkl) (by positivity)

/-- The dyadic grid is strictly monotone in its index. -/
theorem strictMono_dyadicGrid (n : ℕ) : StrictMono (dyadicGrid n) := by
  intro k l hkl
  rw [← NNReal.coe_lt_coe]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hkl) (by positivity)

/-- Each dyadic level has only countably many ceiling values. -/
theorem countable_range_dyadicCeiling (n : ℕ) : (Set.range (dyadicCeiling n)).Countable := by
  refine (Set.countable_range (dyadicGrid n)).mono ?_
  rintro x ⟨t, rfl⟩
  exact ⟨⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊, rfl⟩

variable {Omega : Type*} {m : MeasurableSpace Omega}

/-- The dyadic ceiling of any time-valued map has countable range. -/
theorem countable_range_dyadicCeiling_comp (n : ℕ) (T : Omega → NNReal) :
    (Set.range fun omega ↦ dyadicCeiling n (T omega)).Countable := by
  refine (countable_range_dyadicCeiling n).mono ?_
  rintro x ⟨omega, rfl⟩
  exact ⟨T omega, rfl⟩

/-- The dyadic ceiling of a time-valued map dominates it pointwise. -/
theorem le_dyadicCeiling_comp (n : ℕ) (T : Omega → NNReal) :
    T ≤ fun omega ↦ dyadicCeiling n (T omega) := fun omega ↦ le_dyadicCeiling n (T omega)

/-- The dyadic ceilings of a time-valued map converge pointwise to it. -/
theorem tendsto_dyadicCeiling_comp (T : Omega → NNReal) (omega : Omega) :
    Tendsto (fun n ↦ dyadicCeiling n (T omega)) atTop (𝓝 (T omega)) :=
  tendsto_dyadicCeiling (T omega)

/-- The dyadic ceiling of a finite stopping time is a stopping time for the same filtration. -/
theorem isStoppingTime_dyadicCeiling {f : Filtration NNReal m} {T : Omega → NNReal}
    (hT : IsStoppingTime f (fun omega ↦ (T omega : WithTop NNReal))) (n : ℕ) :
    IsStoppingTime f (fun omega ↦ (dyadicCeiling n (T omega) : WithTop NNReal)) := by
  intro i
  refine (f.mono (dyadicFloor_le n i) _ (hT (dyadicFloor n i))).congr ?_
  ext omega
  simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
  exact (dyadicCeiling_le_iff n (T omega) i).symm

end

end MarkovProcess
