/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCube

/-! # Triadic Partition -/

namespace Homogenization

@[simp] theorem parentCube_scale {d : ℕ} (Q : TriadicCube d) :
    (parentCube Q).scale = Q.scale + 1 := rfl

@[simp] theorem childCube_scale {d : ℕ} (Q : TriadicCube d) (digits : Fin d → Fin 3) :
    ({ scale := Q.scale - 1
       index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } : TriadicCube d).scale = Q.scale - 1 :=
  rfl

theorem mem_childCubes_iff {d : ℕ} {Q R : TriadicCube d} :
    R ∈ childCubes Q ↔
      ∃ digits : Fin d → Fin 3,
        R =
          { scale := Q.scale - 1
            index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } := by
  constructor
  · intro hR
    rcases Finset.mem_image.mp hR with ⟨digits, -, rfl⟩
    exact ⟨digits, rfl⟩
  · rintro ⟨digits, rfl⟩
    exact Finset.mem_image.mpr ⟨digits, Finset.mem_univ _, rfl⟩

theorem childCube_parent {d : ℕ} (Q : TriadicCube d) (digits : Fin d → Fin 3) :
    parentCube
        ({ scale := Q.scale - 1
           index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } : TriadicCube d) = Q := by
  cases Q with
  | mk scale index =>
      unfold parentCube
      apply congrArg₂ TriadicCube.mk
      · simp
      · funext i
        calc
          ((3 * index i + (digits i : ℤ) - 1 + 1) / 3 : ℤ)
              = (((digits i : ℤ) + 3 * index i) / 3 : ℤ) := by ring_nf
          _ = ((digits i : ℤ) / 3 : ℤ) + index i := by
            have h3 : (3 : ℤ) ≠ 0 := by decide
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (Int.add_mul_ediv_left (a := (digits i : ℤ)) (b := (3 : ℤ)) (c := index i) h3)
          _ = index i := by
            have hdigits_nonneg : 0 ≤ (digits i : ℤ) := by
              exact_mod_cast (Nat.zero_le (digits i).val)
            have hdigits_lt : (digits i : ℤ) < (3 : ℤ) := by
              exact_mod_cast (digits i).isLt
            have hdigits_div : ((digits i : ℤ) / 3 : ℤ) = 0 := by
              exact Int.ediv_eq_zero_of_lt_abs hdigits_nonneg (by simp [hdigits_lt])
            rw [hdigits_div]
            simp

@[simp] theorem cubeScaleFactor_childCube {d : ℕ} (Q : TriadicCube d) (digits : Fin d → Fin 3) :
    cubeScaleFactor
      ({ scale := Q.scale - 1
         index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } : TriadicCube d) =
      cubeScaleFactor Q / 3 := by
  simp [cubeScaleFactor, sub_eq_add_neg, zpow_add₀, div_eq_mul_inv,
    show (3 : ℝ) ≠ 0 by norm_num]

theorem cubeSet_childCube_subset {d : ℕ} (Q : TriadicCube d) (digits : Fin d → Fin 3) :
    cubeSet
      ({ scale := Q.scale - 1
         index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } : TriadicCube d) ⊆
      cubeSet Q := by
  let child : TriadicCube d :=
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }
  intro x hx i
  change x ∈ cubeSet child at hx
  rcases hx i with ⟨hlo, hhi⟩
  have hscale : cubeScaleFactor child = cubeScaleFactor Q / 3 := by
    simp [child]
  rw [hscale] at hlo hhi
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hscale_div_nonneg : 0 ≤ cubeScaleFactor Q / 3 := by positivity
  have hd_nonneg : 0 ≤ ((digits i : ℤ) : ℝ) := by
    exact_mod_cast (Nat.zero_le (digits i).val)
  have hd_le_two : ((digits i : ℤ) : ℝ) ≤ 2 := by
    have hd_le_two_int : (digits i : ℤ) ≤ 2 := by
      exact_mod_cast (Nat.le_of_lt_succ (digits i).isLt)
    exact_mod_cast hd_le_two_int
  have hcast :
      ((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) =
        3 * (Q.index i : ℝ) + ((digits i : ℤ) : ℝ) - 1 := by
    norm_num
  have hlo' :
      ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (cubeScaleFactor Q / 3)) ≤
        x i := by
    simpa [child] using hlo
  have hhi' :
      x i <
        ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (cubeScaleFactor Q / 3)) := by
    simpa [child] using hhi
  have hcoeff_lower :
      3 * ((Q.index i : ℝ) - 1 / 2) ≤
        (((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) := by
    rw [hcast]
    linarith [hd_nonneg]
  have hcoeff_upper :
      (((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) ≤
        3 * ((Q.index i : ℝ) + 1 / 2) := by
    rw [hcast]
    linarith [hd_le_two]
  refine ⟨?_, ?_⟩
  · have hlower :
        ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q ≤
          ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (cubeScaleFactor Q / 3)) := by
      calc
        ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q
            = (3 * ((Q.index i : ℝ) - 1 / 2)) * (cubeScaleFactor Q / 3) := by ring
        _ ≤ (((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (cubeScaleFactor Q / 3) := by
          exact mul_le_mul_of_nonneg_right hcoeff_lower hscale_div_nonneg
    exact le_trans hlower hlo'
  · have hupper :
        ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (cubeScaleFactor Q / 3)) ≤
          ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by
      calc
        ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (cubeScaleFactor Q / 3))
            ≤ (3 * ((Q.index i : ℝ) + 1 / 2)) * (cubeScaleFactor Q / 3) := by
          exact mul_le_mul_of_nonneg_right hcoeff_upper hscale_div_nonneg
        _ = ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by ring
    exact lt_of_lt_of_le hhi' hupper

theorem openCubeSet_childCube_subset {d : ℕ} (Q : TriadicCube d) (digits : Fin d → Fin 3) :
    openCubeSet
      ({ scale := Q.scale - 1
         index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } : TriadicCube d) ⊆
      openCubeSet Q := by
  let child : TriadicCube d :=
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }
  intro x hx i
  change x ∈ openCubeSet child at hx
  rcases hx i with ⟨hlo, hhi⟩
  have hscale : cubeScaleFactor child = cubeScaleFactor Q / 3 := by
    simp [child]
  rw [hscale] at hlo hhi
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hscale_div_nonneg : 0 ≤ cubeScaleFactor Q / 3 := by positivity
  have hd_nonneg : 0 ≤ ((digits i : ℤ) : ℝ) := by
    exact_mod_cast (Nat.zero_le (digits i).val)
  have hd_le_two : ((digits i : ℤ) : ℝ) ≤ 2 := by
    have hd_le_two_int : (digits i : ℤ) ≤ 2 := by
      exact_mod_cast (Nat.le_of_lt_succ (digits i).isLt)
    exact_mod_cast hd_le_two_int
  have hcast :
      ((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) =
        3 * (Q.index i : ℝ) + ((digits i : ℤ) : ℝ) - 1 := by
    norm_num
  have hcoeff_lower :
      3 * ((Q.index i : ℝ) - 1 / 2) ≤
        (((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) := by
    rw [hcast]
    linarith [hd_nonneg]
  have hcoeff_upper :
      (((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) ≤
        3 * ((Q.index i : ℝ) + 1 / 2) := by
    rw [hcast]
    linarith [hd_le_two]
  refine ⟨?_, ?_⟩
  · have hlower :
        ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q ≤
          ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (cubeScaleFactor Q / 3)) := by
      calc
        ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q
            = (3 * ((Q.index i : ℝ) - 1 / 2)) * (cubeScaleFactor Q / 3) := by ring
        _ ≤ (((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (cubeScaleFactor Q / 3) := by
          exact mul_le_mul_of_nonneg_right hcoeff_lower hscale_div_nonneg
    exact lt_of_le_of_lt hlower hlo
  · have hupper :
        ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (cubeScaleFactor Q / 3)) ≤
          ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by
      calc
        ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (cubeScaleFactor Q / 3))
            ≤ (3 * ((Q.index i : ℝ) + 1 / 2)) * (cubeScaleFactor Q / 3) := by
          exact mul_le_mul_of_nonneg_right hcoeff_upper hscale_div_nonneg
        _ = ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by ring
    exact lt_of_lt_of_le hhi hupper

theorem childCubes_nonempty {d : ℕ} (Q : TriadicCube d) :
    (childCubes Q).Nonempty := by
  refine ⟨{ scale := Q.scale - 1, index := fun i => 3 * Q.index i + ((0 : Fin d → Fin 3) i : ℤ) - 1 }, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem childCubes_card {d : ℕ} (Q : TriadicCube d) :
    (childCubes Q).card = 3 ^ d := by
  classical
  unfold childCubes
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    funext i
    apply Fin.ext
    have hindex :
        3 * Q.index i + (a i : ℤ) - 1 = 3 * Q.index i + (b i : ℤ) - 1 := by
      simpa using congrArg (fun R : TriadicCube d => R.index i) hab
    have hcast : (a i : ℤ) = (b i : ℤ) := by
      linarith [hindex]
    exact Int.ofNat_inj.mp (by simpa using hcast)

/-- Translating a depth-`n` descendant by parent cube indices requires the
integer shift to be multiplied by `3^n`, because each descendant step lowers
the physical scale by a factor of three. -/
def descendantTranslationShift {d : ℕ} (n : ℕ) (z : Fin d → ℤ) : Fin d → ℤ :=
  fun i => (3 : ℤ) ^ n * z i

@[simp] theorem descendantTranslationShift_zero {d : ℕ} (z : Fin d → ℤ) :
    descendantTranslationShift 0 z = z := by
  funext i
  simp [descendantTranslationShift]

theorem descendantTranslationShift_succ {d : ℕ} (n : ℕ) (z : Fin d → ℤ) :
    descendantTranslationShift (n + 1) z =
      fun i => 3 * descendantTranslationShift n z i := by
  funext i
  simp [descendantTranslationShift, pow_succ, mul_left_comm, mul_comm]

theorem childCubes_translateCube {d : ℕ} (z : Fin d → ℤ) (Q : TriadicCube d) :
    childCubes (translateCube z Q) =
      (childCubes Q).image (translateCube fun i => 3 * z i) := by
  classical
  ext R
  constructor
  · intro hR
    rcases mem_childCubes_iff.mp hR with ⟨digits, rfl⟩
    let S : TriadicCube d :=
      { scale := Q.scale - 1
        index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }
    refine Finset.mem_image.mpr ⟨S, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨digits, Finset.mem_univ _, rfl⟩
    · apply congrArg₂ TriadicCube.mk
      · rfl
      · funext i
        simp [S, translateCube]
        ring
  · intro hR
    rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
    rcases mem_childCubes_iff.mp hS with ⟨digits, rfl⟩
    exact mem_childCubes_iff.mpr ⟨digits, by
      apply congrArg₂ TriadicCube.mk
      · rfl
      · funext i
        simp [translateCube]
        ring⟩

theorem disjoint_childCubes_of_ne {d : ℕ} {Q R : TriadicCube d} (hQR : Q ≠ R) :
    Disjoint (childCubes Q) (childCubes R) := by
  rw [Finset.disjoint_left]
  intro S hSQ hSR
  have hparentQ : parentCube S = Q := by
    rcases mem_childCubes_iff.mp hSQ with ⟨digits, rfl⟩
    exact childCube_parent Q digits
  have hparentR : parentCube S = R := by
    rcases mem_childCubes_iff.mp hSR with ⟨digits, rfl⟩
    exact childCube_parent R digits
  exact hQR (hparentQ.symm.trans hparentR)

@[simp] theorem descendantsAtDepth_zero {d : ℕ} (Q : TriadicCube d) :
    descendantsAtDepth Q 0 = ({Q} : Finset (TriadicCube d)) := rfl

@[simp] theorem descendantsAtDepth_succ {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    descendantsAtDepth Q (n + 1) = (descendantsAtDepth Q n).biUnion childCubes := rfl

@[simp] theorem descendantsAtDepth_one {d : ℕ} (Q : TriadicCube d) :
    descendantsAtDepth Q 1 = childCubes Q := by
  simp [descendantsAtDepth_succ]

theorem descendantsAtDepth_translateCube {d : ℕ} (z : Fin d → ℤ)
    (Q : TriadicCube d) :
    ∀ n : ℕ,
      descendantsAtDepth (translateCube z Q) n =
        (descendantsAtDepth Q n).image
          (translateCube (descendantTranslationShift n z))
  | 0 => by
      simp [descendantsAtDepth]
  | n + 1 => by
      rw [descendantsAtDepth_succ,
        descendantsAtDepth_translateCube z Q n,
        descendantsAtDepth_succ]
      rw [Finset.image_biUnion, Finset.biUnion_image]
      apply Finset.biUnion_congr rfl
      intro R _hR
      rw [childCubes_translateCube, descendantTranslationShift_succ]

theorem mem_descendantsAtDepth_succ_iff {d : ℕ} {Q R : TriadicCube d} {n : ℕ} :
    R ∈ descendantsAtDepth Q (n + 1) ↔
      ∃ S ∈ descendantsAtDepth Q n, R ∈ childCubes S := by
  rw [descendantsAtDepth_succ]
  constructor
  · intro hR
    rcases Finset.mem_biUnion.mp hR with ⟨S, hS, hR⟩
    exact ⟨S, hS, hR⟩
  · rintro ⟨S, hS, hR⟩
    exact Finset.mem_biUnion.mpr ⟨S, hS, hR⟩

/-- Converse to descendant-depth transitivity: a depth `m + n` descendant
factors through a depth-`m` ancestor. -/
theorem exists_descendant_ancestor_at_depth {d : ℕ}
    {Q R : TriadicCube d} (m n : ℕ)
    (hR : R ∈ descendantsAtDepth Q (m + n)) :
    ∃ U ∈ descendantsAtDepth Q m, R ∈ descendantsAtDepth U n := by
  induction n generalizing R with
  | zero =>
      exact ⟨R, by simpa using hR, by simp⟩
  | succ n ih =>
      have hRsucc : R ∈ descendantsAtDepth Q ((m + n) + 1) := by
        simpa [Nat.add_assoc] using hR
      rw [mem_descendantsAtDepth_succ_iff] at hRsucc
      rcases hRsucc with ⟨S, hS, hRS⟩
      rcases ih hS with ⟨U, hU, hSU⟩
      refine ⟨U, hU, ?_⟩
      rw [mem_descendantsAtDepth_succ_iff]
      exact ⟨S, hSU, hRS⟩

theorem descendantsAtDepth_nonempty {d : ℕ} (Q : TriadicCube d) :
    ∀ n : ℕ, (descendantsAtDepth Q n).Nonempty
  | 0 => by
      exact ⟨Q, by simp⟩
  | n + 1 => by
      rcases descendantsAtDepth_nonempty Q n with ⟨S, hS⟩
      rcases childCubes_nonempty S with ⟨R, hR⟩
      exact ⟨R, by
        rw [descendantsAtDepth_succ]
        exact Finset.mem_biUnion.mpr ⟨S, hS, hR⟩⟩

theorem descendantsAtDepth_card_succ {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (descendantsAtDepth Q (n + 1)).card = (descendantsAtDepth Q n).card * 3 ^ d := by
  classical
  rw [descendantsAtDepth_succ, Finset.card_biUnion]
  · simp [childCubes_card]
  · intro R hR S hS hRS
    exact disjoint_childCubes_of_ne hRS

theorem descendantsAtDepth_card {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (descendantsAtDepth Q n).card = (3 ^ d) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [descendantsAtDepth_card_succ, ih, pow_succ]

theorem descendantsAtScale_eq_descendantsAtDepth {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    descendantsAtScale Q k = descendantsAtDepth Q (Int.toNat (Q.scale - k)) := by
  simp [descendantsAtScale, hk]

theorem descendantsAtScale_eq_empty {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : Q.scale < k) :
    descendantsAtScale Q k = ∅ := by
  simp [descendantsAtScale, not_le_of_gt hk]

theorem descendantsAtScale_translateCube {d : ℕ} (z : Fin d → ℤ)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    descendantsAtScale (translateCube z Q) k =
      (descendantsAtScale Q k).image
        (translateCube (descendantTranslationShift (Int.toNat (Q.scale - k)) z)) := by
  have hk' : k ≤ (translateCube z Q).scale := by
    simpa [translateCube] using hk
  rw [descendantsAtScale_eq_descendantsAtDepth (translateCube z Q) hk',
    descendantsAtScale_eq_descendantsAtDepth Q hk,
    descendantsAtDepth_translateCube]
  simp [translateCube]

@[simp] theorem descendantsAtScale_self {d : ℕ} (Q : TriadicCube d) :
    descendantsAtScale Q Q.scale = ({Q} : Finset (TriadicCube d)) := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q le_rfl]
  simp

theorem mem_descendantsAtScale_iff {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) :
    R ∈ descendantsAtScale Q k ↔
      R ∈ descendantsAtDepth Q (Int.toNat (Q.scale - k)) := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]

theorem descendantsAtScale_nonempty {d : ℕ} (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    (descendantsAtScale Q k).Nonempty := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  exact descendantsAtDepth_nonempty Q (Int.toNat (Q.scale - k))

theorem not_mem_descendantsAtScale_of_lt {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hk : Q.scale < k) :
    R ∉ descendantsAtScale Q k := by
  rw [descendantsAtScale_eq_empty Q hk]
  simp

@[simp] theorem child_scale_of_mem_childCubes {d : ℕ} {Q R : TriadicCube d}
    (hR : R ∈ childCubes Q) : R.scale = Q.scale - 1 := by
  rcases (mem_childCubes_iff.mp hR) with ⟨digits, rfl⟩
  simp

@[simp] theorem parent_scale_of_mem_childCubes {d : ℕ} {Q R : TriadicCube d}
    (hR : R ∈ childCubes Q) : (parentCube R).scale = Q.scale := by
  simp [child_scale_of_mem_childCubes hR]

theorem cubeSet_subset_of_mem_childCubes {d : ℕ} {Q R : TriadicCube d}
    (hR : R ∈ childCubes Q) :
    cubeSet R ⊆ cubeSet Q := by
  rcases mem_childCubes_iff.mp hR with ⟨digits, rfl⟩
  exact cubeSet_childCube_subset Q digits

theorem openCubeSet_subset_of_mem_childCubes {d : ℕ} {Q R : TriadicCube d}
    (hR : R ∈ childCubes Q) :
    openCubeSet R ⊆ openCubeSet Q := by
  rcases mem_childCubes_iff.mp hR with ⟨digits, rfl⟩
  exact openCubeSet_childCube_subset Q digits

theorem disjoint_cubeSet_childCube_of_ne {d : ℕ} (Q : TriadicCube d)
    {digits₁ digits₂ : Fin d → Fin 3} (hneq : digits₁ ≠ digits₂) :
    Disjoint
      (cubeSet
        ({ scale := Q.scale - 1
           index := fun i => 3 * Q.index i + (digits₁ i : ℤ) - 1 } : TriadicCube d))
      (cubeSet
        ({ scale := Q.scale - 1
           index := fun i => 3 * Q.index i + (digits₂ i : ℤ) - 1 } : TriadicCube d)) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hdiff : ∃ i, digits₁ i ≠ digits₂ i := by
    by_contra h
    push Not at h
    apply hneq
    funext i
    exact h i
  rcases hdiff with ⟨i, hdi⟩
  have hx₁i := hx₁ i
  have hx₂i := hx₂ i
  change
      ((((3 * Q.index i + (digits₁ i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun j => 3 * Q.index j + (digits₁ j : ℤ) - 1 } : TriadicCube d) ≤
        x i) ∧
      (x i <
        ((((3 * Q.index i + (digits₁ i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun j => 3 * Q.index j + (digits₁ j : ℤ) - 1 } : TriadicCube d))) at hx₁i
  rw [cubeScaleFactor_childCube Q digits₁] at hx₁i
  change
      ((((3 * Q.index i + (digits₂ i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun j => 3 * Q.index j + (digits₂ j : ℤ) - 1 } : TriadicCube d) ≤
        x i) ∧
      (x i <
        ((((3 * Q.index i + (digits₂ i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun j => 3 * Q.index j + (digits₂ j : ℤ) - 1 } : TriadicCube d))) at hx₂i
  rw [cubeScaleFactor_childCube Q digits₂] at hx₂i
  have hscale_nonneg : 0 ≤ cubeScaleFactor Q / 3 := by
    have hscale_pos : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    exact div_nonneg hscale_pos.le (by norm_num)
  have hcast₁ :
      ((3 * Q.index i + (digits₁ i : ℤ) - 1 : ℤ) : ℝ) =
        3 * (Q.index i : ℝ) + ((digits₁ i : ℤ) : ℝ) - 1 := by
    norm_num
  have hcast₂ :
      ((3 * Q.index i + (digits₂ i : ℤ) - 1 : ℤ) : ℝ) =
        3 * (Q.index i : ℝ) + ((digits₂ i : ℤ) : ℝ) - 1 := by
    norm_num
  rcases Fin.lt_or_lt_of_ne hdi with hlt | hlt
  · have hdsep_nat : (digits₁ i).val + 1 ≤ (digits₂ i).val := by
      exact Nat.succ_le_of_lt (by simpa using hlt)
    have hdsep : ((digits₁ i : ℤ) : ℝ) + 1 ≤ ((digits₂ i : ℤ) : ℝ) := by
      exact_mod_cast hdsep_nat
    have hsep :
        (((((3 * Q.index i + (digits₁ i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) *
            (cubeScaleFactor Q / 3))) ≤
          ((((3 * Q.index i + (digits₂ i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) *
            (cubeScaleFactor Q / 3)) := by
      apply mul_le_mul_of_nonneg_right ?_ hscale_nonneg
      rw [hcast₁, hcast₂]
      linarith [hdsep]
    exact not_lt_of_ge (le_trans hsep hx₂i.1) hx₁i.2
  · have hdsep_nat : (digits₂ i).val + 1 ≤ (digits₁ i).val := by
      exact Nat.succ_le_of_lt (by simpa using hlt)
    have hdsep : ((digits₂ i : ℤ) : ℝ) + 1 ≤ ((digits₁ i : ℤ) : ℝ) := by
      exact_mod_cast hdsep_nat
    have hsep :
        (((((3 * Q.index i + (digits₂ i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) *
            (cubeScaleFactor Q / 3))) ≤
          ((((3 * Q.index i + (digits₁ i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) *
            (cubeScaleFactor Q / 3)) := by
      apply mul_le_mul_of_nonneg_right ?_ hscale_nonneg
      rw [hcast₁, hcast₂]
      linarith [hdsep]
    exact not_lt_of_ge (le_trans hsep hx₁i.1) hx₂i.2

theorem disjoint_cubeSet_of_ne_mem_childCubes {d : ℕ} {Q R S : TriadicCube d}
    (hR : R ∈ childCubes Q) (hS : S ∈ childCubes Q) (hneq : R ≠ S) :
    Disjoint (cubeSet R) (cubeSet S) := by
  rcases mem_childCubes_iff.mp hR with ⟨digits₁, rfl⟩
  rcases mem_childCubes_iff.mp hS with ⟨digits₂, rfl⟩
  have hdigits : digits₁ ≠ digits₂ := by
    intro hdigits
    apply hneq
    simp [hdigits]
  exact disjoint_cubeSet_childCube_of_ne Q hdigits

theorem pairwiseDisjoint_childCubes {d : ℕ} (Q : TriadicCube d) :
    (childCubes Q : Set (TriadicCube d)).PairwiseDisjoint cubeSet := by
  intro R hR S hS hneq
  exact disjoint_cubeSet_of_ne_mem_childCubes hR hS hneq

theorem pairwiseDisjoint_descendantsAtDepth {d : ℕ} (Q : TriadicCube d) :
    ∀ n : ℕ, (descendantsAtDepth Q n : Set (TriadicCube d)).PairwiseDisjoint cubeSet
  | 0 => by
      simp [descendantsAtDepth_zero]
  | n + 1 => by
      intro R hR S hS hneq
      rcases mem_descendantsAtDepth_succ_iff.mp hR with ⟨P, hP, hRchild⟩
      rcases mem_descendantsAtDepth_succ_iff.mp hS with ⟨T, hT, hSchild⟩
      by_cases hPT : P = T
      · subst hPT
        exact disjoint_cubeSet_of_ne_mem_childCubes hRchild hSchild hneq
      · exact (pairwiseDisjoint_descendantsAtDepth Q n hP hT hPT).mono
          (cubeSet_subset_of_mem_childCubes hRchild)
          (cubeSet_subset_of_mem_childCubes hSchild)

theorem cubeSet_subset_of_mem_descendantsAtDepth {d : ℕ} {Q R : TriadicCube d} :
    ∀ {n : ℕ}, R ∈ descendantsAtDepth Q n → cubeSet R ⊆ cubeSet Q
  | 0, hR => by
      rw [descendantsAtDepth_zero] at hR
      rcases Finset.mem_singleton.mp hR with rfl
      exact Set.Subset.rfl
  | n + 1, hR => by
      rw [descendantsAtDepth_succ] at hR
      rcases Finset.mem_biUnion.mp hR with ⟨S, hS, hR⟩
      have hRS : cubeSet R ⊆ cubeSet S := cubeSet_subset_of_mem_childCubes hR
      have hSQ : cubeSet S ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hS
      exact fun x hx => hSQ (hRS hx)

theorem openCubeSet_subset_of_mem_descendantsAtDepth {d : ℕ} {Q R : TriadicCube d} :
    ∀ {n : ℕ}, R ∈ descendantsAtDepth Q n → openCubeSet R ⊆ openCubeSet Q
  | 0, hR => by
      rw [descendantsAtDepth_zero] at hR
      rcases Finset.mem_singleton.mp hR with rfl
      exact Set.Subset.rfl
  | n + 1, hR => by
      rw [descendantsAtDepth_succ] at hR
      rcases Finset.mem_biUnion.mp hR with ⟨S, hS, hR⟩
      have hRS : openCubeSet R ⊆ openCubeSet S := openCubeSet_subset_of_mem_childCubes hR
      have hSQ : openCubeSet S ⊆ openCubeSet Q := openCubeSet_subset_of_mem_descendantsAtDepth hS
      exact fun x hx => hSQ (hRS hx)

theorem cubeSet_subset_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    cubeSet R ⊆ cubeSet Q := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
  exact cubeSet_subset_of_mem_descendantsAtDepth hR

theorem scale_eq_sub_of_mem_descendantsAtDepth {d : ℕ} {Q R : TriadicCube d} :
    ∀ {n : ℕ}, R ∈ descendantsAtDepth Q n → R.scale = Q.scale - n
  | 0, hR => by
      rw [descendantsAtDepth_zero] at hR
      simpa using congrArg TriadicCube.scale (Finset.mem_singleton.mp hR)
  | n + 1, hR => by
      rw [descendantsAtDepth_succ] at hR
      rcases Finset.mem_biUnion.mp hR with ⟨S, hS, hR⟩
      calc
        R.scale = S.scale - 1 := child_scale_of_mem_childCubes hR
        _ = (Q.scale - n) - 1 := by rw [scale_eq_sub_of_mem_descendantsAtDepth hS]
        _ = Q.scale - (n + 1) := by
            simp [sub_eq_add_neg, add_assoc, add_comm]

theorem cubeScaleFactor_descendant_eq_div_pow {d : ℕ}
    {Q R : TriadicCube d} {n : ℕ} (hR : R ∈ descendantsAtDepth Q n) :
    cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ n := by
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
  simp [cubeScaleFactor, hscale, zpow_sub₀, zpow_natCast]

theorem scale_eq_sub_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    R.scale = Q.scale - Int.toNat (Q.scale - k) := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
  exact scale_eq_sub_of_mem_descendantsAtDepth hR

theorem exists_mem_childCubes_of_mem_cubeSet {d : ℕ} {Q : TriadicCube d} {x : Vec d}
    (hx : x ∈ cubeSet Q) :
    ∃ R ∈ childCubes Q, x ∈ cubeSet R := by
  let s : ℝ := cubeScaleFactor Q
  let b1 : Fin d → ℝ := fun i => ((Q.index i : ℝ) - (1 / 6 : ℝ)) * s
  let b2 : Fin d → ℝ := fun i => ((Q.index i : ℝ) + (1 / 6 : ℝ)) * s
  let digits : Fin d → Fin 3 := fun i =>
    if h0 : x i < b1 i then 0
    else if h1 : x i < b2 i then 1
    else 2
  let R : TriadicCube d :=
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }
  refine ⟨R, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨digits, Finset.mem_univ _, by simp [R]⟩
  · intro i
    rcases hx i with ⟨hloQ, hhiQ⟩
    have hloQ' : ((Q.index i : ℝ) - 1 / 2) * s ≤ x i := by
      simpa [s] using hloQ
    have hhiQ' : x i < ((Q.index i : ℝ) + 1 / 2) * s := by
      simpa [s] using hhiQ
    have hscaleR : cubeScaleFactor R = s / 3 := by
      simp [R, s]
    rw [hscaleR]
    change
      ((((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (s / 3) ≤ x i) ∧
        (x i < (((3 * Q.index i + (digits i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (s / 3))
    have hcast0 :
        (((3 * Q.index i + (0 : ℤ) - 1 : ℤ) : ℝ)) = 3 * (Q.index i : ℝ) - 1 := by
      norm_num
    have hcast1 :
        (((3 * Q.index i + (1 : ℤ) - 1 : ℤ) : ℝ)) = 3 * (Q.index i : ℝ) := by
      norm_num
    have hcast2 :
        (((3 * Q.index i + (2 : ℤ) - 1 : ℤ) : ℝ)) = 3 * (Q.index i : ℝ) + 1 := by
      calc
        (((3 * Q.index i + (2 : ℤ) - 1 : ℤ) : ℝ))
            = (((1 + Q.index i * 3 : ℤ) : ℝ)) := by ring_nf
        _ = 1 + (Q.index i : ℝ) * 3 := by norm_num
        _ = 3 * (Q.index i : ℝ) + 1 := by ring_nf
    by_cases h0 : x i < b1 i
    · have h0' : x i < ((Q.index i : ℝ) - (1 / 6 : ℝ)) * s := by
        simpa [b1] using h0
      have hdz : (digits i : ℤ) = 0 := by simp [digits, h0]
      rw [hdz]
      refine ⟨?_, ?_⟩
      · calc
          ((((3 * Q.index i + (0 : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (s / 3))
              = ((Q.index i : ℝ) - 1 / 2) * s := by
                rw [hcast0]
                ring
          _ ≤ x i := hloQ'
      · calc
          x i < ((Q.index i : ℝ) - (1 / 6 : ℝ)) * s := h0'
          _ = (((3 * Q.index i + (0 : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (s / 3) := by
                rw [hcast0]
                ring
    · by_cases h1 : x i < b2 i
      · have h1' : x i < ((Q.index i : ℝ) + (1 / 6 : ℝ)) * s := by
          simpa [b2] using h1
        have hb1_le : ((Q.index i : ℝ) - (1 / 6 : ℝ)) * s ≤ x i := by
          exact le_of_not_gt (by simpa [b1] using h0)
        have hdz : (digits i : ℤ) = 1 := by simp [digits, h0, h1]
        rw [hdz]
        refine ⟨?_, ?_⟩
        · calc
            ((((3 * Q.index i + (1 : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (s / 3))
                = ((Q.index i : ℝ) - (1 / 6 : ℝ)) * s := by
                  rw [hcast1]
                  ring
            _ ≤ x i := hb1_le
        · calc
            x i < ((Q.index i : ℝ) + (1 / 6 : ℝ)) * s := h1'
            _ = (((3 * Q.index i + (1 : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (s / 3) := by
                  rw [hcast1]
                  ring
      · have hb2_le : ((Q.index i : ℝ) + (1 / 6 : ℝ)) * s ≤ x i := by
          exact le_of_not_gt (by simpa [b2] using h1)
        have hdz : (digits i : ℤ) = 2 := by simp [digits, h0, h1]
        rw [hdz]
        refine ⟨?_, ?_⟩
        · calc
            ((((3 * Q.index i + (2 : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * (s / 3))
                = ((Q.index i : ℝ) + (1 / 6 : ℝ)) * s := by
                  rw [hcast2]
                  ring
            _ ≤ x i := hb2_le
        · calc
            x i < ((Q.index i : ℝ) + 1 / 2) * s := hhiQ'
            _ = (((3 * Q.index i + (2 : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * (s / 3) := by
                  rw [hcast2]
                  ring

theorem cubeSet_subset_iUnion_childCubes {d : ℕ} (Q : TriadicCube d) :
    cubeSet Q ⊆ ⋃ R ∈ (childCubes Q : Set (TriadicCube d)), cubeSet R := by
  intro x hx
  rcases exists_mem_childCubes_of_mem_cubeSet hx with ⟨R, hR, hxR⟩
  exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hxR⟩⟩

theorem iUnion_childCubes_subset_cubeSet {d : ℕ} (Q : TriadicCube d) :
    (⋃ R ∈ (childCubes Q : Set (TriadicCube d)), cubeSet R) ⊆ cubeSet Q := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨R, hxR⟩
  rcases Set.mem_iUnion.mp hxR with ⟨hR, hxR⟩
  exact cubeSet_subset_of_mem_childCubes hR hxR

theorem cubeSet_eq_iUnion_childCubes {d : ℕ} (Q : TriadicCube d) :
    cubeSet Q = ⋃ R ∈ (childCubes Q : Set (TriadicCube d)), cubeSet R := by
  exact Set.Subset.antisymm (cubeSet_subset_iUnion_childCubes Q) (iUnion_childCubes_subset_cubeSet Q)

theorem exists_mem_descendantsAtDepth_of_mem_cubeSet {d : ℕ} {Q : TriadicCube d} {x : Vec d} :
    ∀ n : ℕ, x ∈ cubeSet Q → ∃ R ∈ descendantsAtDepth Q n, x ∈ cubeSet R
  | 0, hx => ⟨Q, by simp, hx⟩
  | n + 1, hx => by
      rcases exists_mem_descendantsAtDepth_of_mem_cubeSet n hx with ⟨S, hS, hxS⟩
      rcases exists_mem_childCubes_of_mem_cubeSet hxS with ⟨R, hR, hxR⟩
      refine ⟨R, ?_, hxR⟩
      rw [descendantsAtDepth_succ]
      exact Finset.mem_biUnion.mpr ⟨S, hS, hR⟩

theorem cubeSet_subset_iUnion_descendantsAtDepth {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    cubeSet Q ⊆ ⋃ R ∈ (descendantsAtDepth Q n : Set (TriadicCube d)), cubeSet R := by
  intro x hx
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet n hx with ⟨R, hR, hxR⟩
  exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hxR⟩⟩

theorem iUnion_descendantsAtDepth_subset_cubeSet {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (⋃ R ∈ (descendantsAtDepth Q n : Set (TriadicCube d)), cubeSet R) ⊆ cubeSet Q := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨R, hxR⟩
  rcases Set.mem_iUnion.mp hxR with ⟨hR, hxR⟩
  exact cubeSet_subset_of_mem_descendantsAtDepth hR hxR

theorem cubeSet_eq_iUnion_descendantsAtDepth {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    cubeSet Q = ⋃ R ∈ (descendantsAtDepth Q n : Set (TriadicCube d)), cubeSet R := by
  exact Set.Subset.antisymm
    (cubeSet_subset_iUnion_descendantsAtDepth Q n)
    (iUnion_descendantsAtDepth_subset_cubeSet Q n)

theorem cubeSet_subset_iUnion_descendantsAtScale {d : ℕ} (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    cubeSet Q ⊆ ⋃ R ∈ (descendantsAtScale Q k : Set (TriadicCube d)), cubeSet R := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  exact cubeSet_subset_iUnion_descendantsAtDepth Q (Int.toNat (Q.scale - k))

theorem iUnion_descendantsAtScale_subset_cubeSet {d : ℕ} (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    (⋃ R ∈ (descendantsAtScale Q k : Set (TriadicCube d)), cubeSet R) ⊆ cubeSet Q := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  exact iUnion_descendantsAtDepth_subset_cubeSet Q (Int.toNat (Q.scale - k))

theorem cubeSet_eq_iUnion_descendantsAtScale {d : ℕ} (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    cubeSet Q = ⋃ R ∈ (descendantsAtScale Q k : Set (TriadicCube d)), cubeSet R := by
  exact Set.Subset.antisymm
    (cubeSet_subset_iUnion_descendantsAtScale Q hk)
    (iUnion_descendantsAtScale_subset_cubeSet Q hk)

theorem pairwiseDisjoint_descendantsAtScale {d : ℕ} (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    (descendantsAtScale Q k : Set (TriadicCube d)).PairwiseDisjoint cubeSet := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  exact pairwiseDisjoint_descendantsAtDepth Q (Int.toNat (Q.scale - k))

end Homogenization
