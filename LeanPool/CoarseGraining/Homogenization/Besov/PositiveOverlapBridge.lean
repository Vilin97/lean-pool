/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Positive.Full

/-! # Positive Overlap Bridge -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Disjoint-to-overlap positive Besov bridge

The basic geometric input is that every ordinary depth-`j` descendant cube is
the scalar-overlap cube of its middle child. This gives the one useful bridge
direction: the disjoint depth average is controlled by the overlapping depth
average, with only the cardinality loss from the extra generation of centers.
-/

namespace ScalarOverlap

theorem centersAtDepth_card_le_three_pow_mul_descendantsAtDepth_card
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (centersAtDepth Q j).card ≤
      3 ^ d * (descendantsAtDepth Q j).card := by
  calc
    (centersAtDepth Q j).card
        ≤ (descendantsAtDepth Q (j + 1)).card :=
          centersAtDepth_card_le_descendantsAtDepth_card Q j
    _ = (descendantsAtDepth Q j).card * 3 ^ d :=
          descendantsAtDepth_card_succ Q j
    _ = 3 ^ d * (descendantsAtDepth Q j).card := by
          rw [Nat.mul_comm]

end ScalarOverlap

theorem cubeBesovDepthAverage_le_three_pow_mul_overlapDepthAverage
    {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthAverage Q p u j ≤
      (3 ^ d : ℝ) * cubeBesovOverlapDepthAverage Q p u j := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let O : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  let G : TriadicCube d → ℝ :=
    fun S => (cubeBesovOverlapOscillation S p u) ^ p.toReal
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hD_card_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD_nonempty
  have hD_card_ne : (D.card : ℝ) ≠ 0 := ne_of_gt hD_card_pos
  have hO_nonempty : O.Nonempty := by
    simpa [O] using ScalarOverlap.centersAtDepth_nonempty Q j
  have hO_card_pos : 0 < (O.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hO_nonempty
  have hO_card_ne : (O.card : ℝ) ≠ 0 := ne_of_gt hO_card_pos
  have hG_nonneg : ∀ S ∈ O, 0 ≤ G S := by
    intro S _hS
    exact Real.rpow_nonneg (cubeBesovOverlapOscillation_nonneg S p u) _
  have himage_subset : D.image ScalarOverlap.middleChildCube ⊆ O := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, rfl⟩
    exact ScalarOverlap.middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth
      (by simpa [D] using hR)
  have hsum_image_le : (D.image ScalarOverlap.middleChildCube).sum G ≤ O.sum G := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun S hSO _hSnot => hG_nonneg S hSO)
  have hsum_desc_eq_image :
      D.sum (fun R => (cubeBesovOscillation R p u) ^ p.toReal) =
        (D.image ScalarOverlap.middleChildCube).sum G := by
    rw [Finset.sum_image]
    · simp
    · intro R _hR S _hS hRS
      exact ScalarOverlap.middleChildCube_injective hRS
  have hsum_nonneg : 0 ≤ O.sum G := by
    exact Finset.sum_nonneg hG_nonneg
  have hcard_nat :
      O.card ≤ 3 ^ d * D.card := by
    simpa [D, O] using
      ScalarOverlap.centersAtDepth_card_le_three_pow_mul_descendantsAtDepth_card Q j
  have hcard_real :
      (O.card : ℝ) ≤ (3 ^ d : ℝ) * (D.card : ℝ) := by
    exact_mod_cast hcard_nat
  have hdenom :
      (D.card : ℝ)⁻¹ * O.sum G ≤
        (3 ^ d : ℝ) * ((O.card : ℝ)⁻¹ * O.sum G) := by
    calc
      (D.card : ℝ)⁻¹ * O.sum G
          = ((O.card : ℝ) / (D.card : ℝ)) *
              ((O.card : ℝ)⁻¹ * O.sum G) := by
              field_simp [hD_card_ne, hO_card_ne]
      _ ≤ (3 ^ d : ℝ) * ((O.card : ℝ)⁻¹ * O.sum G) := by
          have hratio :
              (O.card : ℝ) / (D.card : ℝ) ≤ (3 ^ d : ℝ) := by
            rw [div_le_iff₀ hD_card_pos]
            simpa [mul_comm, mul_left_comm, mul_assoc] using hcard_real
          have havg_nonneg : 0 ≤ (O.card : ℝ)⁻¹ * O.sum G :=
            mul_nonneg (inv_nonneg.mpr (le_of_lt hO_card_pos)) hsum_nonneg
          exact mul_le_mul_of_nonneg_right hratio havg_nonneg
  calc
    cubeBesovDepthAverage Q p u j
        = (D.card : ℝ)⁻¹ *
            D.sum (fun R => (cubeBesovOscillation R p u) ^ p.toReal) := by
            rfl
    _ = (D.card : ℝ)⁻¹ * (D.image ScalarOverlap.middleChildCube).sum G := by
          rw [hsum_desc_eq_image]
    _ ≤ (D.card : ℝ)⁻¹ * O.sum G := by
          exact mul_le_mul_of_nonneg_left hsum_image_le
            (inv_nonneg.mpr (le_of_lt hD_card_pos))
    _ ≤ (3 ^ d : ℝ) * ((O.card : ℝ)⁻¹ * O.sum G) := hdenom
    _ = (3 ^ d : ℝ) *
          cubeBesovOverlapDepthAverage Q p u j := by
          rfl

private theorem three_pow_depth_loss_root
    {d : ℕ} {p : ℝ≥0∞} :
    ((3 ^ d : ℝ) ^ (1 / p.toReal)) =
      (3 : ℝ) ^ ((d : ℝ) / p.toReal) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
  congr 1
  ring

theorem cubeBesovDepthSeminorm_le_three_rpow_mul_overlapDepthSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthSeminorm Q s p u j
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapDepthSeminorm Q s p u j := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  let r : ℝ := 1 / p.toReal
  have hr_nonneg : 0 ≤ r := by
    exact (one_div_pos.mpr hp).le
  have hbase_le :
      cubeBesovDepthAverage Q p u j ≤
        (3 ^ d : ℝ) * cubeBesovOverlapDepthAverage Q p u j :=
    cubeBesovDepthAverage_le_three_pow_mul_overlapDepthAverage Q p u j
  have hroot_le :
      (cubeBesovDepthAverage Q p u j) ^ r
        ≤ C * (cubeBesovOverlapDepthAverage Q p u j) ^ r := by
    have hC_eq : ((3 ^ d : ℝ) ^ r) = C := by
      simpa [C, r] using three_pow_depth_loss_root (d := d) (p := p)
    calc
      (cubeBesovDepthAverage Q p u j) ^ r
          ≤ ((3 ^ d : ℝ) *
              cubeBesovOverlapDepthAverage Q p u j) ^ r := by
            exact Real.rpow_le_rpow
              (cubeBesovDepthAverage_nonneg Q p u j) hbase_le hr_nonneg
      _ = ((3 ^ d : ℝ) ^ r) *
            (cubeBesovOverlapDepthAverage Q p u j) ^ r := by
            rw [Real.mul_rpow (by positivity)
              (cubeBesovOverlapDepthAverage_nonneg Q p u j)]
      _ = C * (cubeBesovOverlapDepthAverage Q p u j) ^ r := by
            rw [hC_eq]
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q s j :=
    cubeBesovDepthWeight_nonneg Q s j
  calc
    cubeBesovDepthSeminorm Q s p u j
        = cubeBesovDepthWeight Q s j *
            (cubeBesovDepthAverage Q p u j) ^ r := by
            rfl
    _ ≤ cubeBesovDepthWeight Q s j *
          (C * (cubeBesovOverlapDepthAverage Q p u j) ^ r) := by
          exact mul_le_mul_of_nonneg_left hroot_le hweight_nonneg
    _ = C * (cubeBesovDepthWeight Q s j *
          (cubeBesovOverlapDepthAverage Q p u j) ^ r) := by
          ring
    _ = C * cubeBesovOverlapDepthSeminorm Q s p u j := by
          rfl

private theorem finset_lq_le_mul_of_forall_le_mul
    {ι : Type*} (s : Finset ι) {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (h : ∀ i ∈ s, a i ≤ C * b i) :
    (Finset.sum s fun i => (a i) ^ q) ^ (1 / q)
      ≤ C * (Finset.sum s fun i => (b i) ^ q) ^ (1 / q) := by
  have hq_nonneg : 0 ≤ q := hq.le
  have hq_ne : q ≠ 0 := hq.ne'
  have hsumA_nonneg :
      0 ≤ Finset.sum s fun i => (a i) ^ q := by
    exact Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) q
  have hsumB_nonneg :
      0 ≤ Finset.sum s fun i => (b i) ^ q := by
    exact Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hb i hi) q
  have hsum_le :
      Finset.sum s (fun i => (a i) ^ q)
        ≤ C ^ q * Finset.sum s fun i => (b i) ^ q := by
    calc
      Finset.sum s (fun i => (a i) ^ q)
          ≤ Finset.sum s (fun i => (C * b i) ^ q) := by
            exact Finset.sum_le_sum fun i hi =>
              Real.rpow_le_rpow (ha i hi) (h i hi) hq_nonneg
      _ = Finset.sum s (fun i => C ^ q * (b i) ^ q) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact Real.mul_rpow hC (hb i hi)
      _ = C ^ q * Finset.sum s fun i => (b i) ^ q := by
            rw [Finset.mul_sum]
  calc
    (Finset.sum s fun i => (a i) ^ q) ^ (1 / q)
        ≤ (C ^ q * Finset.sum s fun i => (b i) ^ q) ^ (1 / q) := by
          exact Real.rpow_le_rpow hsumA_nonneg hsum_le
            (one_div_pos.mpr hq).le
    _ = (C ^ q) ^ (1 / q) *
          (Finset.sum s fun i => (b i) ^ q) ^ (1 / q) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hC q) hsumB_nonneg]
    _ = C * (Finset.sum s fun i => (b i) ^ q) ^ (1 / q) := by
          rw [show (1 / q : ℝ) = q⁻¹ by ring]
          simp [Real.rpow_rpow_inv hC hq_ne]

theorem cubeBesovPartialSeminorm_le_three_rpow_mul_overlapPartialSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p q : ℝ≥0∞}
    (hp : 0 < p.toReal) (hq : 1 ≤ q.toReal) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialSeminorm Q s p q N u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapPartialSeminorm Q s p q N u := by
  classical
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  have hq_pos : 0 < q.toReal :=
    lt_of_lt_of_le zero_lt_one hq
  have hC_nonneg : 0 ≤ C :=
    (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _).le
  simpa [cubeBesovPartialSeminorm, cubeBesovOverlapPartialSeminorm, C] using
    finset_lq_le_mul_of_forall_le_mul
      (s := Finset.range (N + 1)) (q := q.toReal) (C := C)
      hq_pos hC_nonneg
      (fun j _hj => cubeBesovDepthSeminorm_nonneg Q s p u j)
      (fun j _hj => cubeBesovOverlapDepthSeminorm_nonneg Q s p u j)
      (fun j _hj =>
        cubeBesovDepthSeminorm_le_three_rpow_mul_overlapDepthSeminorm
          Q s hp u j)

theorem cubeBesovPartialSeminormTop_le_three_rpow_mul_overlapPartialSeminormTop
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialSeminormTop Q s p N u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapPartialSeminormTop Q s p N u := by
  classical
  let R : Finset ℕ := Finset.range (N + 1)
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  have hR : R.Nonempty := by
    exact ⟨0, by simp [R]⟩
  have hC_nonneg : 0 ≤ C :=
    (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _).le
  unfold cubeBesovPartialSeminormTop cubeBesovOverlapPartialSeminormTop
  change
    R.sup' hR (fun j => cubeBesovDepthSeminorm Q s p u j) ≤
      C * R.sup' hR (fun j => cubeBesovOverlapDepthSeminorm Q s p u j)
  refine Finset.sup'_le hR _ ?_
  intro j hj
  calc
    cubeBesovDepthSeminorm Q s p u j
        ≤ C * cubeBesovOverlapDepthSeminorm Q s p u j :=
          cubeBesovDepthSeminorm_le_three_rpow_mul_overlapDepthSeminorm
            Q s hp u j
    _ ≤ C * R.sup' hR
          (fun j => cubeBesovOverlapDepthSeminorm Q s p u j) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup'
              (f := fun j => cubeBesovOverlapDepthSeminorm Q s p u j) hj)
            hC_nonneg

private theorem three_rpow_depth_loss_ge_one
    {d : ℕ} {p : ℝ≥0∞} (hp : 0 < p.toReal) :
    1 ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) := by
  have hexp_nonneg : 0 ≤ (d : ℝ) / p.toReal :=
    div_nonneg (by positivity) hp.le
  exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hexp_nonneg

theorem cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p q : ℝ≥0∞}
    (hp : 0 < p.toReal) (hq : 1 ≤ q.toReal) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialNorm Q s p q N u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapPartialNorm Q s p q N u := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  let A : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  have hsem :
      cubeBesovPartialSeminorm Q s p q N u
        ≤ C * cubeBesovOverlapPartialSeminorm Q s p q N u := by
    exact cubeBesovPartialSeminorm_le_three_rpow_mul_overlapPartialSeminorm
      Q s hp hq N u
  have hA_nonneg : 0 ≤ A := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _)
  have hC_ge_one : 1 ≤ C :=
    three_rpow_depth_loss_ge_one (d := d) (p := p) hp
  have hA_le : A ≤ C * A := by
    calc
      A = 1 * A := by rw [one_mul]
      _ ≤ C * A := by
            exact mul_le_mul_of_nonneg_right hC_ge_one hA_nonneg
  unfold cubeBesovPartialNorm cubeBesovOverlapPartialNorm
  change cubeBesovPartialSeminorm Q s p q N u + A ≤
    C * (cubeBesovOverlapPartialSeminorm Q s p q N u + A)
  calc
    cubeBesovPartialSeminorm Q s p q N u + A
        ≤ C * cubeBesovOverlapPartialSeminorm Q s p q N u + C * A := by
          exact add_le_add hsem hA_le
    _ = C * (cubeBesovOverlapPartialSeminorm Q s p q N u + A) := by
          ring

theorem cubeBesovPartialNormTop_le_three_rpow_mul_overlapPartialNormTop
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞}
    (hp : 0 < p.toReal) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialNormTop Q s p N u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapPartialNormTop Q s p N u := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  let A : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  have hsem :
      cubeBesovPartialSeminormTop Q s p N u
        ≤ C * cubeBesovOverlapPartialSeminormTop Q s p N u := by
    exact cubeBesovPartialSeminormTop_le_three_rpow_mul_overlapPartialSeminormTop
      Q s hp N u
  have hA_nonneg : 0 ≤ A := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _)
  have hC_ge_one : 1 ≤ C :=
    three_rpow_depth_loss_ge_one (d := d) (p := p) hp
  have hA_le : A ≤ C * A := by
    calc
      A = 1 * A := by rw [one_mul]
      _ ≤ C * A := by
            exact mul_le_mul_of_nonneg_right hC_ge_one hA_nonneg
  unfold cubeBesovPartialNormTop cubeBesovOverlapPartialNormTop
  change cubeBesovPartialSeminormTop Q s p N u + A ≤
    C * (cubeBesovOverlapPartialSeminormTop Q s p N u + A)
  calc
    cubeBesovPartialSeminormTop Q s p N u + A
        ≤ C * cubeBesovOverlapPartialSeminormTop Q s p N u + C * A := by
          exact add_le_add hsem hA_le
    _ = C * (cubeBesovOverlapPartialSeminormTop Q s p N u + A) := by
          ring

theorem cubeBesovDisjointSeminorm_le_three_rpow_mul_overlapSeminorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p q : ℝ≥0∞}
    (hp : 0 < p.toReal) (hq : 1 ≤ q.toReal) (u : Vec d → ℝ)
    (hBddOverlap :
      BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u)) :
    cubeBesovDisjointSeminorm Q s p q u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapSeminorm Q s p q u := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  have hC_nonneg : 0 ≤ C :=
    (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _).le
  unfold cubeBesovDisjointSeminorm
  refine csSup_le
    (cubeBesovDisjointSeminormValueSet_nonempty Q s p q u) ?_
  rintro x ⟨N, rfl⟩
  have hpartial :
      cubeBesovDisjointPartialSeminorm Q s p q N u ≤
        C * cubeBesovOverlapPartialSeminorm Q s p q N u := by
    simpa [cubeBesovDisjointPartialSeminorm, C] using
      cubeBesovPartialSeminorm_le_three_rpow_mul_overlapPartialSeminorm
        Q s hp hq N u
  calc
    cubeBesovDisjointPartialSeminorm Q s p q N u
        ≤ C * cubeBesovOverlapPartialSeminorm Q s p q N u := hpartial
    _ ≤ C * cubeBesovOverlapSeminorm Q s p q u := by
          exact mul_le_mul_of_nonneg_left
            (cubeBesovOverlapPartialSeminorm_le_cubeBesovOverlapSeminorm_of_bddAbove
              Q s p q u hBddOverlap N)
            hC_nonneg

theorem cubeBesovDisjointSeminormTop_le_three_rpow_mul_overlapSeminormTop_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞}
    (hp : 0 < p.toReal) (u : Vec d → ℝ)
    (hBddOverlap :
      BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u)) :
    cubeBesovDisjointSeminormTop Q s p u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapSeminormTop Q s p u := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  have hC_nonneg : 0 ≤ C :=
    (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _).le
  unfold cubeBesovDisjointSeminormTop
  refine csSup_le
    (cubeBesovDisjointSeminormTopValueSet_nonempty Q s p u) ?_
  rintro x ⟨N, rfl⟩
  have hpartial :
      cubeBesovDisjointPartialSeminormTop Q s p N u ≤
        C * cubeBesovOverlapPartialSeminormTop Q s p N u := by
    simpa [cubeBesovDisjointPartialSeminormTop, C] using
      cubeBesovPartialSeminormTop_le_three_rpow_mul_overlapPartialSeminormTop
        Q s hp N u
  calc
    cubeBesovDisjointPartialSeminormTop Q s p N u
        ≤ C * cubeBesovOverlapPartialSeminormTop Q s p N u := hpartial
    _ ≤ C * cubeBesovOverlapSeminormTop Q s p u := by
          exact mul_le_mul_of_nonneg_left
            (cubeBesovOverlapPartialSeminormTop_le_cubeBesovOverlapSeminormTop_of_bddAbove
              Q s p u hBddOverlap N)
            hC_nonneg

theorem cubeBesovDisjointNorm_le_three_rpow_mul_overlapNorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p q : ℝ≥0∞}
    (hp : 0 < p.toReal) (hq : 1 ≤ q.toReal) (u : Vec d → ℝ)
    (hBddOverlap :
      BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u)) :
    cubeBesovDisjointNorm Q s p q u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapNorm Q s p q u := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  have hC_nonneg : 0 ≤ C :=
    (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _).le
  unfold cubeBesovDisjointNorm
  refine csSup_le (cubeBesovDisjointNormValueSet_nonempty Q s p q u) ?_
  rintro x ⟨N, rfl⟩
  have hpartial :
      cubeBesovDisjointPartialNorm Q s p q N u ≤
        C * cubeBesovOverlapPartialNorm Q s p q N u := by
    simpa [cubeBesovDisjointPartialNorm, C] using
      cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm
        Q s hp hq N u
  calc
    cubeBesovDisjointPartialNorm Q s p q N u
        ≤ C * cubeBesovOverlapPartialNorm Q s p q N u := hpartial
    _ ≤ C * cubeBesovOverlapNorm Q s p q u := by
          exact mul_le_mul_of_nonneg_left
            (cubeBesovOverlapPartialNorm_le_cubeBesovOverlapNorm_of_bddAbove
              Q s p q u hBddOverlap N)
            hC_nonneg

theorem cubeBesovDisjointNormTop_le_three_rpow_mul_overlapNormTop_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞}
    (hp : 0 < p.toReal) (u : Vec d → ℝ)
    (hBddOverlap :
      BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u)) :
    cubeBesovDisjointNormTop Q s p u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapNormTop Q s p u := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p.toReal)
  have hC_nonneg : 0 ≤ C :=
    (Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _).le
  unfold cubeBesovDisjointNormTop
  refine csSup_le (cubeBesovDisjointNormTopValueSet_nonempty Q s p u) ?_
  rintro x ⟨N, rfl⟩
  have hpartial :
      cubeBesovDisjointPartialNormTop Q s p N u ≤
        C * cubeBesovOverlapPartialNormTop Q s p N u := by
    simpa [cubeBesovDisjointPartialNormTop, C] using
      cubeBesovPartialNormTop_le_three_rpow_mul_overlapPartialNormTop
        Q s hp N u
  calc
    cubeBesovDisjointPartialNormTop Q s p N u
        ≤ C * cubeBesovOverlapPartialNormTop Q s p N u := hpartial
    _ ≤ C * cubeBesovOverlapNormTop Q s p u := by
          exact mul_le_mul_of_nonneg_left
            (cubeBesovOverlapPartialNormTop_le_cubeBesovOverlapNormTop_of_bddAbove
              Q s p u hBddOverlap N)
            hC_nonneg

theorem cubeBesovDisjointSeminorm_le_three_rpow_mul_overlapSeminorm_of_overlapRegularity
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p q : ℝ≥0∞}
    (hp : 0 < p.toReal) (hq : 1 ≤ q.toReal) (u : Vec d → ℝ)
    (hu : CubeBesovOverlapRegularity Q s p q u) :
    cubeBesovDisjointSeminorm Q s p q u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapSeminorm Q s p q u :=
  cubeBesovDisjointSeminorm_le_three_rpow_mul_overlapSeminorm_of_bddAbove
    Q s hp hq u hu.partialSeminorms_bddAbove

theorem cubeBesovDisjointSeminormTop_le_three_rpow_mul_overlapSeminormTop_of_overlapRegularity
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞}
    (hp : 0 < p.toReal) (u : Vec d → ℝ)
    (hu : CubeBesovOverlapRegularityTop Q s p u) :
    cubeBesovDisjointSeminormTop Q s p u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapSeminormTop Q s p u :=
  cubeBesovDisjointSeminormTop_le_three_rpow_mul_overlapSeminormTop_of_bddAbove
    Q s hp u hu.partialSeminorms_bddAbove

theorem cubeBesovDisjointNorm_le_three_rpow_mul_overlapNorm_of_overlapRegularity
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p q : ℝ≥0∞}
    (hp : 0 < p.toReal) (hq : 1 ≤ q.toReal) (u : Vec d → ℝ)
    (hu : CubeBesovOverlapRegularity Q s p q u) :
    cubeBesovDisjointNorm Q s p q u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapNorm Q s p q u :=
  cubeBesovDisjointNorm_le_three_rpow_mul_overlapNorm_of_bddAbove
    Q s hp hq u hu.partialSeminorms_bddAbove

theorem cubeBesovDisjointNormTop_le_three_rpow_mul_overlapNormTop_of_overlapRegularity
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞}
    (hp : 0 < p.toReal) (u : Vec d → ℝ)
    (hu : CubeBesovOverlapRegularityTop Q s p u) :
    cubeBesovDisjointNormTop Q s p u
      ≤ (3 : ℝ) ^ ((d : ℝ) / p.toReal) *
        cubeBesovOverlapNormTop Q s p u :=
  cubeBesovDisjointNormTop_le_three_rpow_mul_overlapNormTop_of_bddAbove
    Q s hp u hu.partialSeminorms_bddAbove

end

end Homogenization
