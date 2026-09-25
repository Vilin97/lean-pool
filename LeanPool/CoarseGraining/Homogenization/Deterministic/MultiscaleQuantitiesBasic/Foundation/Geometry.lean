/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.GeometricOne

/-! # Geometry -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem isFiniteMeasureVolumeMeasureOnCubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
  let U : Set (Vec d) := cubeSet Q
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_cubeSet_lt_top Q⟩
  change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)
  infer_instance

instance instIsFiniteMeasureVolumeMeasureOnCubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
  isFiniteMeasureVolumeMeasureOnCubeSet Q

noncomputable def fullBlockMatRowAbsSqBound {d : ℕ} (M : FullBlockMat d) : ℝ :=
  ∑ i, (∑ j, |M i j|) ^ 2

theorem abs_fullBlockVec_le_one_of_fullBlockVecNormSq_eq_one {d : ℕ}
    {e : FullBlockVec d} (he : fullBlockVecNormSq e = 1) (i : BlockCoord d) :
    |e i| ≤ 1 := by
  have hnonneg : ∀ j : BlockCoord d, 0 ≤ e j ^ 2 := by
    intro j
    exact sq_nonneg (e j)
  have hle : e i ^ 2 ≤ ∑ j, e j ^ 2 := by
    simpa using
      (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i) :
        e i ^ 2 ≤ ∑ j : BlockCoord d, e j ^ 2)
  have hsquare : |e i| ^ 2 ≤ 1 := by
    calc
      |e i| ^ 2 = e i ^ 2 := by rw [sq_abs]
      _ ≤ ∑ j, e j ^ 2 := hle
      _ = 1 := by simpa [fullBlockVecNormSq] using he
  nlinarith

theorem fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one {d : ℕ}
    (M : FullBlockMat d) {e : FullBlockVec d} (he : fullBlockVecNormSq e = 1) :
    fullBlockVecNormSq (Matrix.mulVec M e) ≤ fullBlockMatRowAbsSqBound M := by
  unfold fullBlockVecNormSq fullBlockMatRowAbsSqBound
  refine Finset.sum_le_sum ?_
  intro i hi
  have hcoord :
      |Matrix.mulVec M e i| ≤ ∑ j, |M i j| := by
    calc
      |Matrix.mulVec M e i| = |∑ j, M i j * e j| := by
        simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, |M i j * e j| := by
        simpa using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : BlockCoord d => M i j * e j))
      _ ≤ ∑ j, |M i j| := by
        refine Finset.sum_le_sum ?_
        intro j hj
        calc
          |M i j * e j| = |M i j| * |e j| := by rw [abs_mul]
          _ ≤ |M i j| * 1 := by
            exact mul_le_mul_of_nonneg_left
              (abs_fullBlockVec_le_one_of_fullBlockVecNormSq_eq_one he j) (abs_nonneg _)
          _ = |M i j| := by ring
  have hsquare : (Matrix.mulVec M e i) ^ 2 ≤ (∑ j, |M i j|) ^ 2 := by
    have hrow_nonneg : 0 ≤ ∑ j, |M i j| := by positivity
    have habs :
        |Matrix.mulVec M e i| ≤ |(∑ j, |M i j|)| := by
      rw [abs_of_nonneg hrow_nonneg]
      exact hcoord
    have hsquareAbs : |Matrix.mulVec M e i| ^ 2 ≤ |(∑ j, |M i j|)| ^ 2 := by
      simpa [pow_two] using
        (mul_le_mul habs habs (abs_nonneg _) (abs_nonneg _))
    simpa [sq_abs, abs_of_nonneg hrow_nonneg] using hsquareAbs
  exact hsquare

theorem blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq {d : ℕ} (x : FullBlockVec d) :
    blockVecDot (ofFullBlockVec x) (ofFullBlockVec x) = fullBlockVecNormSq x := by
  rw [← dotProduct_toFullBlockVec (ofFullBlockVec x) (ofFullBlockVec x)]
  simp [fullBlockVecNormSq, dotProduct, pow_two]

theorem descendant_scale_le_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) :
    k ≤ Q.scale := by
  by_contra hk
  exact (not_mem_descendantsAtScale_of_lt (Q := Q) (R := R) (k := k) (lt_of_not_ge hk)) hR

theorem descendant_scale_eq_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hR : R ∈ descendantsAtScale Q k) :
    R.scale = k := by
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hdepth := scale_eq_sub_of_mem_descendantsAtScale hk hR
  have hnonneg : 0 ≤ Q.scale - k := sub_nonneg.mpr hk
  calc
    R.scale = Q.scale - (Int.toNat (Q.scale - k) : ℕ) := hdepth
    _ = Q.scale - (Q.scale - k) := by rw [Int.toNat_of_nonneg hnonneg]
    _ = k := sub_sub_cancel _ _

theorem openCubeSet_subset_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    openCubeSet R ⊆ openCubeSet Q := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
  exact openCubeSet_subset_of_mem_descendantsAtDepth hR

theorem mem_descendantsAtDepth_add_local {d : ℕ} {Q R S : TriadicCube d} {m n : ℕ}
    (hR : R ∈ descendantsAtDepth Q m) (hS : S ∈ descendantsAtDepth R n) :
    S ∈ descendantsAtDepth Q (m + n) := by
  induction n generalizing R S with
  | zero =>
      rw [descendantsAtDepth_zero] at hS
      simpa [Finset.mem_singleton.mp hS]
  | succ n ih =>
      rw [mem_descendantsAtDepth_succ_iff] at hS
      rcases hS with ⟨T, hT, hchild⟩
      have hTQ : T ∈ descendantsAtDepth Q (m + n) := ih hR hT
      have hSQ : S ∈ descendantsAtDepth Q ((m + n) + 1) := by
        rw [mem_descendantsAtDepth_succ_iff]
        exact ⟨T, hTQ, hchild⟩
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSQ

theorem mem_descendantsAtScale_trans {d : ℕ} {Q R S : TriadicCube d} {k l : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (hS : S ∈ descendantsAtScale R l) :
    S ∈ descendantsAtScale Q l := by
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hlR : l ≤ R.scale := descendant_scale_le_of_mem_descendantsAtScale hS
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hlk : l ≤ k := by simpa [hRscale] using hlR
  have hlQ : l ≤ Q.scale := le_trans hlk hk
  rw [descendantsAtScale_eq_descendantsAtDepth Q hlQ]
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
  rw [descendantsAtScale_eq_descendantsAtDepth R hlR] at hS
  have hdepth :
      Int.toNat (Q.scale - l) =
        Int.toNat (Q.scale - k) + Int.toNat (R.scale - l) := by
    rw [hRscale]
    have hk0 : 0 ≤ Q.scale - k := sub_nonneg.mpr hk
    have hlk0 : 0 ≤ k - l := sub_nonneg.mpr hlk
    have hsum : Q.scale - l = (Q.scale - k) + (k - l) := by ring
    rw [hsum, Int.toNat_add hk0 hlk0]
  rw [hdepth]
  exact mem_descendantsAtDepth_add_local hR hS

theorem OpenCubeDescendantDeterministicCoarseData.of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {a : CoeffField d} {l : ℤ}
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hlQ : l ≤ Q.scale) (hR : R ∈ descendantsAtScale Q l) :
    OpenCubeDescendantDeterministicCoarseData R a := by
  intro j hj S hS
  have hRscale : R.scale = l := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hjQ : j ≤ Q.scale := by
    exact le_trans (by simpa [hRscale] using hj) hlQ
  exact hData j hjQ S (mem_descendantsAtScale_trans hR hS)

theorem maxDescendantBBlockNormAtScale_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k l : ℤ} (a : CoeffField d)
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantBBlockNormAtScale R l a ≤ maxDescendantBBlockNormAtScale Q l a := by
  unfold maxDescendantBBlockNormAtScale finsetSsup
  have hne :
      ((fun S => coarseBBlockNorm S a) '' (↑(descendantsAtScale R l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty R hl with ⟨S, hS⟩
    exact ⟨coarseBBlockNorm S a, ⟨S, hS, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨S, hS, rfl⟩
  have hBdd :
      BddAbove ((fun T => coarseBBlockNorm T a) '' (↑(descendantsAtScale Q l) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun T => coarseBBlockNorm T a)).bddAbove
  exact le_csSup hBdd ⟨S, mem_descendantsAtScale_trans hR hS, rfl⟩

theorem maxDescendantSigmaStarInvNormAtScale_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k l : ℤ} (a : CoeffField d)
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantSigmaStarInvNormAtScale R l a ≤ maxDescendantSigmaStarInvNormAtScale Q l a := by
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  have hne :
      ((fun S => coarseSigmaStarInvBlockNorm S a) '' (↑(descendantsAtScale R l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty R hl with ⟨S, hS⟩
    exact ⟨coarseSigmaStarInvBlockNorm S a, ⟨S, hS, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨S, hS, rfl⟩
  have hBdd :
      BddAbove
        ((fun T => coarseSigmaStarInvBlockNorm T a) '' (↑(descendantsAtScale Q l) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun T => coarseSigmaStarInvBlockNorm T a)).bddAbove
  exact le_csSup hBdd ⟨S, mem_descendantsAtScale_trans hR hS, rfl⟩


end

end Homogenization
