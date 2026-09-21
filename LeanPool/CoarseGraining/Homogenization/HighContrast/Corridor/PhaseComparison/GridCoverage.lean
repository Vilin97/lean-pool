/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.Geometry

/-!
# Discrete uniform-grid corridor coverage count

Phase comparison (Prop 4.4 of the high-moment paper, Armstrong–Kuusi–Loher, in
preparation) is proved with the continuum `σ`-average replaced by a finite
uniform grid `gridPhase ℓ N j i = (j i) · ℓ / N` for `j : Fin d → Fin N`.  This
file records the elementary grid-counting coverage bound that replaces the
continuum corridor-coverage estimate `e.corridor.coverage`:

* `card_gridHits_le` (**1-d heart**): for `4 ≤ ℓ` and `ℓ ≤ N`, at most `3N/ℓ`
  of the `N` grid points `c ↦ c·ℓ/N` land within (sup-)distance `1` of a fixed
  real `t` modulo `ℓ`.  The bound is via an injection of the admissible grid
  indices into the integer points of an open interval of length `2N/ℓ`.
* `sum_indicator_gridPhase_corridor_le` (**d-dim corollary**): for a fixed `x`,
  the number of grid phases `σ_j` whose corridor set contains `x`, summed as
  indicators over `Finset.univ : Finset (Fin d → Fin N)`, is at most
  `(3d/ℓ)·N^d`; i.e. the average of the corridor indicators over the grid is at
  most `3d/ℓ`.

Only `4 ≤ ℓ` and `ℓ ≤ N` are used; the constant `3` is not sharp (any
`C·N/ℓ` is acceptable, absorbed into `C_d` downstream).
-/

open Homogenization
open scoped MeasureTheory
open Classical

namespace Homogenization

variable {d : ℕ}

/-- The finite uniform phase grid: `gridPhase ℓ N j` is the phase vector with
`i`-th coordinate `(j i)·ℓ/N`. -/
noncomputable def gridPhase (ℓ : ℝ) (N : ℕ) (j : Fin d → Fin N) : Vec d :=
  fun i => (j i : ℝ) * ℓ / N

@[simp] theorem gridPhase_apply (ℓ : ℝ) (N : ℕ) (j : Fin d → Fin N) (i : Fin d) :
    gridPhase ℓ N j i = (j i : ℝ) * ℓ / N := rfl

/-- Cast bound: `(k.toNat : ℝ) ≤ r` whenever `(k:ℝ) ≤ r` and `0 ≤ r`. -/
private theorem toNat_cast_le {k : ℤ} {r : ℝ} (h : (k : ℝ) ≤ r) (hr : 0 ≤ r) :
    ((k.toNat : ℕ) : ℝ) ≤ r := by
  rcases le_or_gt 0 k with hk | hk
  · have : ((k.toNat : ℤ) : ℝ) = (k : ℝ) := by
      rw [Int.toNat_of_nonneg hk]
    rw [show ((k.toNat : ℕ) : ℝ) = ((k.toNat : ℤ) : ℝ) by push_cast; ring, this]
    exact h
  · rw [Int.toNat_of_nonpos hk.le]
    simpa using hr

/-! ## 1-d heart -/

/-- **M0 (1-d count).**  For `4 ≤ ℓ` and `ℓ ≤ N`, at most `3N/ℓ` of the grid
points `c ↦ c·ℓ/N`, `c : Fin N`, lie within sup-distance `1` of `t` modulo the
lattice `ℓ·ℤ`. -/
theorem card_gridHits_le {ℓ : ℝ} (hℓ : 4 ≤ ℓ) {N : ℕ} (hN : (ℓ : ℝ) ≤ (N : ℝ))
    (t : ℝ) :
    ((Finset.univ.filter
        (fun c : Fin N => ∃ n : ℤ, |t - (c : ℝ) * ℓ / N - n * ℓ| < 1)).card : ℝ)
      ≤ 3 * N / ℓ := by
  classical
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hℓ0 hN
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  set a : ℝ := (t - 1) * N / ℓ with ha
  set b : ℝ := (t + 1) * N / ℓ with hb
  set A : Finset (Fin N) :=
    Finset.univ.filter (fun c : Fin N => ∃ n : ℤ, |t - (c : ℝ) * ℓ / N - n * ℓ| < 1)
    with hA
  -- choice of shift for each admissible index
  set ncf : Fin N → ℤ :=
    fun c => if h : ∃ n : ℤ, |t - (c : ℝ) * ℓ / N - n * ℓ| < 1 then Classical.choose h else 0
    with hncf
  set g : Fin N → ℤ := fun c => (c : ℤ) + ncf c * N with hg
  -- the injection lands in the integer points of the open interval `(a, b)`
  have hmaps : ∀ c ∈ A, g c ∈ Finset.Ioo ⌊a⌋ ⌈b⌉ := by
    intro c hc
    rw [hA, Finset.mem_filter] at hc
    have hex := hc.2
    have hncfc : ncf c = Classical.choose hex := by
      simp only [hncf]; exact dif_pos hex
    have hspec : |t - (c : ℝ) * ℓ / N - (ncf c) * ℓ| < 1 := by
      rw [hncfc]; exact Classical.choose_spec hex
    -- rewrite the argument as `t - (g c)·ℓ/N`
    have hgcR : (g c : ℝ) = (c : ℝ) + (ncf c : ℝ) * (N : ℝ) := by
      rw [hg]; push_cast; ring
    have hkey : t - (c : ℝ) * ℓ / N - (ncf c) * ℓ = t - (g c : ℝ) * ℓ / N := by
      rw [hgcR]; field_simp; ring
    rw [hkey, abs_lt] at hspec
    obtain ⟨hlo, hhi⟩ := hspec
    -- clear denominators
    have hhi' : (t - 1) * (N : ℝ) < (g c : ℝ) * ℓ := by
      have h : t - 1 < (g c : ℝ) * ℓ / N := by linarith
      rw [lt_div_iff₀ hN0] at h; linarith
    have hlo' : (g c : ℝ) * ℓ < (t + 1) * (N : ℝ) := by
      have h : (g c : ℝ) * ℓ / N < t + 1 := by linarith
      rw [div_lt_iff₀ hN0] at h; linarith
    -- `a < g c < b`
    have hgc_lo : a < (g c : ℝ) := by
      rw [ha, div_lt_iff₀ hℓ0]; linarith
    have hgc_hi : (g c : ℝ) < b := by
      rw [hb, lt_div_iff₀ hℓ0]; linarith
    rw [Finset.mem_Ioo]
    exact ⟨Int.floor_lt.2 hgc_lo, Int.lt_ceil.2 hgc_hi⟩
  -- the injection is injective on `A`
  have hinj : Set.InjOn g A := by
    intro c hc c' hc' hgg
    have hgg2 : (c : ℤ) + ncf c * (N : ℤ) = (c' : ℤ) + ncf c' * (N : ℤ) := hgg
    have hdvd : (N : ℤ) ∣ ((c : ℤ) - (c' : ℤ)) :=
      ⟨ncf c' - ncf c, by linear_combination hgg2⟩
    have h1 : (c : ℤ) < N := by exact_mod_cast c.isLt
    have h2 : (c' : ℤ) < N := by exact_mod_cast c'.isLt
    have h3 : (0 : ℤ) ≤ (c : ℤ) := by positivity
    have h4 : (0 : ℤ) ≤ (c' : ℤ) := by positivity
    have habs : |(c : ℤ) - (c' : ℤ)| < (N : ℤ) := by rw [abs_lt]; constructor <;> omega
    have hzero : (c : ℤ) - (c' : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    have hcc : (c : ℤ) = (c' : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast hcc)
  -- card comparison
  have hcard : A.card ≤ (Finset.Ioo ⌊a⌋ ⌈b⌉).card :=
    Finset.card_le_card_of_injOn g hmaps hinj
  rw [Int.card_Ioo] at hcard
  -- pass to reals
  have hcardR : (A.card : ℝ) ≤ ((⌈b⌉ - ⌊a⌋ - 1).toNat : ℝ) := by exact_mod_cast hcard
  -- `((⌈b⌉ - ⌊a⌋ - 1).toNat : ℝ) ≤ b - a + 1`
  have hba : b - a = 2 * N / ℓ := by rw [ha, hb]; field_simp; ring
  have hintbound : ((⌈b⌉ - ⌊a⌋ - 1 : ℤ) : ℝ) ≤ b - a + 1 := by
    have hc1 : (⌈b⌉ : ℝ) < b + 1 := Int.ceil_lt_add_one b
    have hc2 : a - 1 < (⌊a⌋ : ℝ) := Int.sub_one_lt_floor a
    push_cast
    linarith
  have hrb : (0 : ℝ) ≤ b - a + 1 := by rw [hba]; positivity
  have hfin : (A.card : ℝ) ≤ b - a + 1 :=
    le_trans hcardR (toNat_cast_le hintbound hrb)
  -- `b - a + 1 = 2N/ℓ + 1 ≤ 3N/ℓ` since `ℓ ≤ N`
  have hfinal : b - a + 1 ≤ 3 * N / ℓ := by
    rw [hba]
    rw [div_add' _ _ _ hℓ0.ne', div_le_div_iff_of_pos_right hℓ0]
    nlinarith [hN]
  calc (A.card : ℝ) ≤ b - a + 1 := hfin
    _ ≤ 3 * N / ℓ := hfinal

/-! ## d-dim corollary -/

/-- Marginal count: the number of grid multi-indices `j : Fin d → Fin N` with a
constraint on a single coordinate `j i` factors through `N^{d-1}`. -/
private theorem sum_eval_eq {N : ℕ} (i : Fin d) (f : Fin N → ℝ) :
    (∑ j : Fin d → Fin N, f (j i)) = (N : ℝ) ^ (d - 1) * ∑ c : Fin N, f c := by
  classical
  have hcard : Fintype.card ({ k : Fin d // k ≠ i } → Fin N) = N ^ (d - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  rw [← Equiv.sum_comp (Equiv.funSplitAt i (Fin N)).symm (fun j => f (j i))]
  rw [Fintype.sum_prod_type]
  have hval : ∀ (a : Fin N) (b : { k : Fin d // k ≠ i } → Fin N),
      f (((Equiv.funSplitAt i (Fin N)).symm (a, b)) i) = f a := by
    intro a b
    congr 1
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp_rw [hval, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  push_cast
  ring

/-- **M0 (d-dim coverage).**  For a fixed `x` and `4 ≤ ℓ ≤ N`, the sum over the
finite grid `j : Fin d → Fin N` of the corridor indicators of the phases
`gridPhase ℓ N j` at `x` is at most `(3d/ℓ)·N^d`.  Dividing by `N^d`, the grid
average of `𝟙_{corridorSet}` at any point is at most `3d/ℓ`. -/
theorem sum_indicator_gridPhase_corridor_le [NeZero d] {ℓ : ℝ} (hℓ : 4 ≤ ℓ)
    {N : ℕ} (hN : (ℓ : ℝ) ≤ (N : ℝ)) (x : Vec d) :
    (∑ j : Fin d → Fin N,
        (corridorSet ℓ (gridPhase ℓ N j)).indicator (fun _ => (1 : ℝ)) x)
      ≤ 3 * (d : ℝ) / ℓ * (N : ℝ) ^ d := by
  classical
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  -- per-coordinate hit indicator
  set gcoord : Fin d → Fin N → ℝ :=
    fun i c => if (∃ n : ℤ, |x i - (c : ℝ) * ℓ / N - n * ℓ| < 1) then (1 : ℝ) else 0
    with hgcoord
  -- union bound pointwise
  have hunion : ∀ j : Fin d → Fin N,
      (corridorSet ℓ (gridPhase ℓ N j)).indicator (fun _ => (1 : ℝ)) x
        ≤ ∑ i : Fin d, gcoord i (j i) := by
    intro j
    by_cases hmem : x ∈ corridorSet ℓ (gridPhase ℓ N j)
    · rw [Set.indicator_of_mem hmem]
      rw [mem_corridorSet] at hmem
      obtain ⟨i, n, hin⟩ := hmem
      have hgi : gcoord i (j i) = 1 := by
        simp only [hgcoord]
        rw [if_pos ⟨n, by simpa [gridPhase_apply] using hin⟩]
      calc (1 : ℝ) = gcoord i (j i) := hgi.symm
        _ ≤ ∑ i : Fin d, gcoord i (j i) := by
            apply Finset.single_le_sum (f := fun i => gcoord i (j i))
            · intro k _
              rw [hgcoord]; positivity
            · exact Finset.mem_univ i
    · rw [Set.indicator_of_notMem hmem]
      apply Finset.sum_nonneg
      intro k _
      rw [hgcoord]; positivity
  -- sum the union bound and swap order
  calc
    (∑ j : Fin d → Fin N,
        (corridorSet ℓ (gridPhase ℓ N j)).indicator (fun _ => (1 : ℝ)) x)
      ≤ ∑ j : Fin d → Fin N, ∑ i : Fin d, gcoord i (j i) :=
        Finset.sum_le_sum (fun j _ => hunion j)
    _ = ∑ i : Fin d, ∑ j : Fin d → Fin N, gcoord i (j i) := Finset.sum_comm
    _ = ∑ i : Fin d, (N : ℝ) ^ (d - 1) * ∑ c : Fin N, gcoord i c := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_eval_eq i (gcoord i)
    _ ≤ ∑ i : Fin d, (N : ℝ) ^ (d - 1) * (3 * N / ℓ) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- `∑_c gcoord i c = card of the 1-d hit set ≤ 3N/ℓ`
        have hcard : (∑ c : Fin N, gcoord i c)
            = ((Finset.univ.filter
                (fun c : Fin N => ∃ n : ℤ, |x i - (c : ℝ) * ℓ / N - n * ℓ| < 1)).card : ℝ) := by
          simp only [hgcoord]
          rw [Finset.sum_boole]
        rw [hcard]
        exact card_gridHits_le hℓ hN (x i)
    _ = 3 * (d : ℝ) / ℓ * (N : ℝ) ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hpow : (N : ℝ) ^ (d - 1) * N = (N : ℝ) ^ d := by
          rw [← pow_succ]; congr 1; omega
        rw [show (d : ℝ) * ((N : ℝ) ^ (d - 1) * (3 * N / ℓ))
              = 3 * (d : ℝ) / ℓ * ((N : ℝ) ^ (d - 1) * N) by ring, hpow]

end Homogenization
