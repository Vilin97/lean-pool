/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PartitionedCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedQuotients
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses

/-!
# Signed covariance updates with the constructed primary waves

The signed solve uses the existing primary square roots, pulse columns,
physical masks, covering powers, and angular phases.  Distinct labels are
separated by the constructed padded slots.  A signed square is retained as
a separate term; it is not included in the linear covariance identity.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SignedCovariance

open Set Function Filter MeasureTheory Matrix
open PartitionedCovariance
open scoped BigOperators Topology ContDiff

/-- Vec2: an abbreviation for `Fin 2 → ℝ`. -/
abbrev Vec2 := Fin 2 → ℝ
/-- Mat2: an abbreviation for `Matrix (Fin 2) (Fin 2) ℝ`. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane

/-- The numerator is the actual inverse-matrix solve. -/
noncomputable def increment (H : Mat2) (T R : Vec2) (j : Fin 2) : ℝ :=
  (H⁻¹.mulVec R) j / (2 * SmoothCovariance.amplitudes H T j)

theorem increment_eq_inverse (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) (j : Fin 2) :
    increment H T R j = (H⁻¹.mulVec R) j / (2 * Real.sqrt ((H⁻¹.mulVec T) j)) := by
  rw [increment, (amplitudes_are_inverse_weights hcone j).2]

private theorem edge_zero_one : FlatCutoff.edge 0 1 = 1 := by
  rw [FlatCutoff.edge_of_pos 0 (by norm_num : (0 : ℝ) < 1)]
  norm_num

private theorem edge_matrix_zero (H : Mat2) :
    FlatCovariance.edgeMatrix 0 (fun _ => H) 1 = H := by
  ext i j
  simp [FlatCovariance.edgeMatrix, FlatCovariance.columns, edge_zero_one]

private theorem edge_target_zero (R : Vec2) :
    FlatCovariance.edgeTarget 0 (fun _ => R) 1 = R := by
  ext i
  simp [FlatCovariance.edgeTarget, FlatCovariance.scaledTarget, edge_zero_one]

/-- The scalar solve is the already proved flat-edge solve at unit edge weight. -/
theorem increment_eq_flat (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) :
    increment H T R = FlatCovariance.signedAmplitude 0 0 0
      (fun _ => H) (fun _ => T) (fun _ => R) 1 := by
  funext j
  simp only [increment, FlatCovariance.signedAmplitude, FlatCovariance.primaryAmplitude,
    FlatCovariance.inverseCoefficients, edge_matrix_zero, edge_target_zero]
  rw [SmoothCovariance.inverse_formula H T hcone.det_ne_zero]
  rfl

/-- Exact two-sided covariance, reusing `FlatCovariance.signed_cross_reconstruct`. -/
theorem cross_reconstruct (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) :
    H.mulVec (fun j => 2 * SmoothCovariance.amplitudes H T j * increment H T R j) = R := by
  have he := FlatCovariance.signed_cross_reconstruct
    (σ := 0) (τ := 0) (κ := 0) (G := fun _ => H) (T := fun _ => T)
    (R := fun _ => R) (x := 1) hcone
  rw [← increment_eq_flat H T R hcone] at he
  simp only [FlatCovariance.primaryAmplitude, FlatCovariance.inverseCoefficients,
    edge_matrix_zero, edge_target_zero] at he
  rw [SmoothCovariance.inverse_formula H T hcone.det_ne_zero] at he
  exact he

/-- The signed square is a genuine additional covariance. -/
noncomputable def squareColumn (H : Mat2) (T R : Vec2) : Vec2 :=
  H.mulVec (fun j => increment H T R j ^ 2)

/-! ## A bilinear average of the actual waves -/

theorem wave_product_rescale (a b : ℝ) (n : ℕ) (f g : Plane → ℝ)
    (mode : ℤ) (phase : Plane → ℝ) (Y : Plane) (θ : ℝ) :
    wave a n f mode phase Y θ * wave b n g mode phase Y θ =
      (a * b) * (wave 1 n f mode phase Y θ * wave 1 n g mode phase Y θ) := by
  unfold wave
  ring

theorem angularMean_bilinear (a b : ℝ) (n : ℕ) (f g : Plane → ℝ)
    (mode : ℤ) (hmode : mode ≠ 0) (phase : Plane → ℝ) (Y : Plane) :
    SmoothLoop.angularMean (fun θ => wave a n f mode phase Y θ * wave b n g mode phase Y θ) =
      (a * b) * ((covered n f Y * covered n g Y) * (1 / 2)) := by
  rw [show (fun θ => wave a n f mode phase Y θ * wave b n g mode phase Y θ) =
    (fun θ => (a * b) * (wave 1 n f mode phase Y θ * wave 1 n g mode phase Y θ)) from
    funext (fun θ => wave_product_rescale a b n f g mode phase Y θ)]
  rw [SmoothLoop.angularMean_const_mul, angularMean_wave_product 1 n f g mode hmode phase]
  ring

theorem angularMean_bilinear_continuous (a b : ℝ) (n : ℕ) {f g : Plane → ℝ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (hg : Continuous g) (hcg : HasCompactSupport g)
    (mode : ℤ) (hmode : mode ≠ 0) (phase : Plane → ℝ) :
    Continuous (fun Y => SmoothLoop.angularMean
      (fun θ => wave a n f mode phase Y θ * wave b n g mode phase Y θ)) := by
  simp_rw [angularMean_bilinear a b n f g mode hmode phase]
  exact continuous_const.mul (((covered_continuous hf hcf n).mul
    (covered_continuous hg hcg n)).mul continuous_const)

/-- Both scalar coefficients multiply precisely the same native pulse. -/
theorem PairData.bilinear_diagonal {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (a b : ℝ) (j i : Fin 2) :
    doubleAverage (fun Y θ =>
      wave a (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) (P.modes j) (P.phases j) Y θ *
      wave b (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) (P.modes j) (P.phases j) Y θ)
          =
      a * b * P.matrix i j := by
  have heq : (fun Y θ =>
      wave a (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) (P.modes j) (P.phases j) Y θ *
      wave b (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) (P.modes j) (P.phases j) Y θ)
          =
      fun Y θ => (a * b) *
        (wave 1 (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) (P.modes j) (P.phases j) Y θ *
        wave 1 (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) (P.modes j) (P.phases j) Y
            θ) := by
    funext Y θ
    exact wave_product_rescale _ _ _ _ _ _ _ _ _
  rw [heq]
  rw [doubleAverage_const_mul]
  have hu := (P.pulses j).wave_covariance vr vt (slotCenter h (signedLabel U j)) hdet
    (P.ci j) sys.radius (P.ci_pos j) sys.radius_pos
    (slotSet h sys.radius vr vt (signedLabel U j)) (sys.injective _)
    (P.rawRadial_support hdet j) (fun i => P.rawTangent_support hdet j i)
    1 (SlotColoring.nativeIndex h U.1) (P.phases j) (P.modes j) (P.modes_ne j) i
  simpa only [PairData.rawRadial, PairData.rawTangent, PairData.matrix, pairMatrix,
    one_pow, one_mul] using congrArg (fun z : ℝ => a * b * z) hu

/-! ## The same physical masks, slots, and phases for arbitrary coefficients -/

/-- Radial with, given by `wave (outer * (Real.sqrt ε * a j * mask D U q x))
(SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) (P.modes j) (P.phases j)`. -/
noncomputable def radialWith {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (a : Vec2) (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) : Plane → ℝ → ℝ :=
  wave (outer * (Real.sqrt ε * a j * mask D U q x))
    (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) (P.modes j) (P.phases j)

/-- Tangent with, constructed using `wave`. -/
noncomputable def tangentWith {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (a : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) : Plane → ℝ → ℝ :=
  wave (outer * (Real.sqrt ε * a j * mask D U q x))
    (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) (P.modes j) (P.phases j)

theorem radialWith_primary {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) :
    radialWith P hdet outer ε (SmoothCovariance.amplitudes P.matrix T) q x j =
      P.radialWave hdet outer ε T q x j := rfl

theorem tangentWith_primary {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) :
    tangentWith P hdet outer ε (SmoothCovariance.amplitudes P.matrix T) q x j i =
      P.tangentWave hdet outer ε T q x j i := rfl

/-- Pointwise diagonal reduction uses padded-slot disjointness, including
when different labels carry the same angular harmonic. -/
theorem finite_product_diagonal {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (a b : UnsignedLabel → Vec2) (F : Finset UnsignedLabel)
    {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (i : Fin 2) (Y : Plane) (θ : ℝ) :
    (∑ v ∈ F.product (Finset.univ : Finset (Fin 2)),
      radialWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 Y θ) *
    (∑ v ∈ F.product (Finset.univ : Finset (Fin 2)),
      tangentWith (P v.1) hdet (outer v.1) (ε v.1) (b v.1) q x v.2 i Y θ) =
    ∑ v ∈ F.product (Finset.univ : Finset (Fin 2)),
      radialWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 Y θ *
      tangentWith (P v.1) hdet (outer v.1) (ε v.1) (b v.1) q x v.2 i Y θ := by
  apply sum_product_diagonal
  intro v hv w hw hvw
  have hz := sys.wave_cross_zero
    (L := signedTailLabel N v) (M := signedTailLabel N w)
    (by change 1 ≤ v.1.1 + N; omega) (by change 1 ≤ w.1.1 + N; omega)
    (fun he => hvw (signedTailLabel_injective N he))
    ((P v.1).rawRadial_support hdet v.2) ((P w.1).rawTangent_support hdet w.2 i)
    hq x Y θ (outer v.1 * Real.sqrt (ε v.1) * a v.1 v.2)
    (outer w.1 * Real.sqrt (ε w.1) * b w.1 w.2)
    ((P v.1).modes v.2) ((P w.1).modes w.2) ((P v.1).phases v.2) ((P w.1).phases w.2)
  simpa only [radialWith, tangentWith, signedTailLabel, physicalMask_signedLabel,
    signedLabel, physicalMask, mask, mul_assoc] using hz

theorem finite_bilinear_covariance {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (a b : UnsignedLabel → Vec2) (F : Finset UnsignedLabel)
    (hε : ∀ U ∈ F, 0 ≤ ε U) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (i : Fin 2) :
    doubleAverage (fun Y θ =>
      (∑ v ∈ F.product (Finset.univ : Finset (Fin 2)),
        radialWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 Y θ) *
      (∑ v ∈ F.product (Finset.univ : Finset (Fin 2)),
        tangentWith (P v.1) hdet (outer v.1) (ε v.1) (b v.1) q x v.2 i Y θ)) =
      ∑ U ∈ F, outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2 *
        ((P U).matrix.mulVec (fun j => a U j * b U j)) i := by
  simp_rw [finite_product_diagonal sys hdet N hN P outer ε a b F hq x i]
  rw [doubleAverage_sum]
  · apply (Finset.sum_product F Finset.univ _).trans
    apply Finset.sum_congr rfl
    intro U hU
    simp only [radialWith, tangentWith, PairData.bilinear_diagonal,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hs := Real.sq_sqrt (hε U hU)
    calc
      _ = outer U ^ 2 * (Real.sqrt (ε U)) ^ 2 * mask D (tailLabel N U) q x ^ 2 *
          ((P U).matrix i 0 * (a U 0 * b U 0) + (P U).matrix i 1 * (a U 1 * b U 1)) := by ring
      _ = _ := by rw [hs]
  · intro v hv Y
    exact (wave_continuous_theta _ _ _ _ _ _).mul (wave_continuous_theta _ _ _ _ _ _)
  · intro v hv
    exact angularMean_bilinear_continuous _ _ _ ((P v.1).rawRadial_continuous hdet v.2)
      ((P v.1).rawRadial_compact hdet v.2) ((P v.1).rawTangent_continuous hdet v.2 i)
      ((P v.1).rawTangent_compact hdet v.2 i) ((P v.1).modes v.2)
      ((P v.1).modes_ne v.2) ((P v.1).phases v.2)

/-- Assembled radial with, given by `∑ᶠ v : UnsignedLabel × Fin 2, radialWith (P v.1) hdet
(outer v.1) (ε v.1) (a v.1) q x v.2 Y θ`. -/
noncomputable def assembledRadialWith {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (Y : Plane) (θ : ℝ) : ℝ :=
  ∑ᶠ v : UnsignedLabel × Fin 2, radialWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 Y θ

/-- Assembled tangent with, given by `∑ᶠ v : UnsignedLabel × Fin 2, tangentWith (P v.1) hdet
(outer v.1) (ε v.1) (a v.1) q x v.2 i Y θ`. -/
noncomputable def assembledTangentWith {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N :
    ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (i : Fin 2) (Y : Plane) (θ : ℝ)
        : ℝ :=
  ∑ᶠ v : UnsignedLabel × Fin 2, tangentWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 i Y θ

theorem assembledRadialWith_finite {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (Y : Plane) (θ : ℝ)
        :
    assembledRadialWith P hdet outer ε a q x Y θ =
      ∑ v ∈ (finite_active_masks D N hq x).toFinset.product (Finset.univ : Finset (Fin 2)),
        radialWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 Y θ := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro v hv
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  apply (finite_active_masks D N hq x).mem_toFinset.mpr
  intro hm
  exact hv (by simp [radialWith, wave, hm])

theorem assembledTangentWith_finite {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (i : Fin 2) (Y : Plane) (θ : ℝ) :
    assembledTangentWith P hdet outer ε a q x i Y θ =
      ∑ v ∈ (finite_active_masks D N hq x).toFinset.product (Finset.univ : Finset (Fin 2)),
        tangentWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 i Y θ := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro v hv
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  apply (finite_active_masks D N hq x).mem_toFinset.mpr
  intro hm
  exact hv (by simp [tangentWith, wave, hm])

theorem assembled_bilinear_covariance {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (a b : UnsignedLabel → Vec2)
    {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (hε : ∀ U, mask D (tailLabel N U) q x ≠ 0 → 0 ≤ ε U) (i : Fin 2) :
    doubleAverage (fun Y θ => assembledRadialWith P hdet outer ε a q x Y θ *
      assembledTangentWith P hdet outer ε b q x i Y θ) =
      ∑ᶠ U : UnsignedLabel, outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2 *
        ((P U).matrix.mulVec (fun j => a U j * b U j)) i := by
  classical
  simp_rw [assembledRadialWith_finite P hdet outer ε a hq x,
    assembledTangentWith_finite P hdet outer ε b hq x i]
  rw [finite_bilinear_covariance sys hdet N hN P outer ε a b _
    (fun U hU => hε U ((finite_active_masks D N hq x).mem_toFinset.mp hU)) hq x i]
  symm
  apply finsum_eq_sum_of_support_subset
  intro U hU
  apply (finite_active_masks D N hq x).mem_toFinset.mpr
  intro hm
  exact hU (by simp [hm])

/-- Off-diagonal products vanish before either integral, so interchanging the
two scalar coefficient families leaves the product unchanged pointwise. -/
theorem assembled_bilinear_symmetry {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (a b : UnsignedLabel → Vec2)
    {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (i : Fin 2) (Y : Plane) (θ : ℝ) :
    assembledRadialWith P hdet outer ε a q x Y θ * assembledTangentWith P hdet outer ε b q x i Y θ =
      assembledRadialWith P hdet outer ε b q x Y θ * assembledTangentWith P hdet outer ε a q x i Y
          θ := by
  classical
  simp_rw [assembledRadialWith_finite P hdet outer ε _ hq x,
    assembledTangentWith_finite P hdet outer ε _ hq x i,
    finite_product_diagonal sys hdet N hN P outer ε _ _ _ hq x i]
  apply Finset.sum_congr rfl
  intro v hv
  unfold radialWith tangentWith wave
  ring

/-- Signed radial, given by `assembledRadialWith P hdet outer ε (fun U => increment (P U).matrix
(T U) (R U)) q x`. -/
noncomputable def signedRadial {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T R : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) : Plane → ℝ → ℝ :=
  assembledRadialWith P hdet outer ε (fun U => increment (P U).matrix (T U) (R U)) q x

/-- Signed tangent, given by `assembledTangentWith P hdet outer ε (fun U => increment (P
U).matrix (T U) (R U)) q x i`. -/
noncomputable def signedTangent {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T R : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (i : Fin 2) : Plane → ℝ → ℝ :=
  assembledTangentWith P hdet outer ε (fun U => increment (P U).matrix (T U) (R U)) q x i

theorem cross_reconstruct_component (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) (i : Fin 2) :
    2 * (H.mulVec (fun j => SmoothCovariance.amplitudes H T j * increment H T R j)) i = R i := by
  have hc := congrFun (cross_reconstruct H T R hcone) i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc ⊢
  calc
    _ = H i 0 * (2 * SmoothCovariance.amplitudes H T 0 * increment H T R 0) +
      H i 1 * (2 * SmoothCovariance.amplitudes H T 1 * increment H T R 1) := by ring
    _ = _ := hc

/-- The assembled two-sided primary/signed cross covariance.  Positivity is
required only for primary weights; the signed target is arbitrary. -/
theorem assembled_cross_covariance {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (T R : UnsignedLabel → Vec2)
    {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (hε : ∀ U, mask D (tailLabel N U) q x ≠ 0 → 0 ≤ ε U)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 → SmoothCovariance.StrictCone (P U).matrix (T U))
    (i : Fin 2) :
    doubleAverage (fun Y θ =>
      assembledRadial P hdet outer ε T q x Y θ * signedTangent P hdet outer ε T R q x i Y θ +
      signedRadial P hdet outer ε T R q x Y θ * assembledTangent P hdet outer ε T q x i Y θ) =
      ∑ᶠ U : UnsignedLabel, outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2 * R U i := by
  let a : UnsignedLabel → Vec2 := fun U => SmoothCovariance.amplitudes (P U).matrix (T U)
  let b : UnsignedLabel → Vec2 := fun U => increment (P U).matrix (T U) (R U)
  have heq : (fun Y θ =>
      assembledRadial P hdet outer ε T q x Y θ * signedTangent P hdet outer ε T R q x i Y θ +
      signedRadial P hdet outer ε T R q x Y θ * assembledTangent P hdet outer ε T q x i Y θ) =
      fun Y θ => 2 * (assembledRadialWith P hdet outer ε a q x Y θ *
        assembledTangentWith P hdet outer ε b q x i Y θ) := by
    funext Y θ
    change assembledRadialWith P hdet outer ε a q x Y θ * assembledTangentWith P hdet outer ε b q x
        i Y θ +
      assembledRadialWith P hdet outer ε b q x Y θ * assembledTangentWith P hdet outer ε a q x i Y
          θ = _
    rw [assembled_bilinear_symmetry sys hdet N hN P outer ε b a hq x i]
    ring
  rw [heq, doubleAverage_const_mul,
    assembled_bilinear_covariance sys hdet N hN P outer ε a b hq x hε i]
  have hf : (support (fun U : UnsignedLabel => outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2 *
      ((P U).matrix.mulVec (fun j => a U j * b U j)) i)).Finite := by
    apply (finite_active_masks D N hq x).subset
    intro U hU hm
    exact hU (by simp [hm])
  rw [mul_finsum _ 2]
  apply finsum_congr
  intro U
  by_cases hm : mask D (tailLabel N U) q x = 0
  · simp [hm]
  · calc
      _ = (outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2) *
          (2 * ((P U).matrix.mulVec (fun j => a U j * b U j)) i) := by ring
      _ = _ := by rw [cross_reconstruct_component (P U).matrix (T U) (R U) (hcone U hm) i]

/-- The signed-square covariance is retained exactly, with no sign restriction
on the prescribed stress. -/
theorem assembled_signed_square {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (T R : UnsignedLabel → Vec2)
    {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (hε : ∀ U, mask D (tailLabel N U) q x ≠ 0 → 0 ≤ ε U) (i : Fin 2) :
    doubleAverage (fun Y θ => signedRadial P hdet outer ε T R q x Y θ *
      signedTangent P hdet outer ε T R q x i Y θ) =
      ∑ᶠ U : UnsignedLabel, outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2 *
        squareColumn (P U).matrix (T U) (R U) i := by
  simpa only [signedRadial, signedTangent, squareColumn, pow_two] using
    assembled_bilinear_covariance sys hdet N hN P outer ε
      (fun U => increment (P U).matrix (T U) (R U))
      (fun U => increment (P U).matrix (T U) (R U)) hq x hε i

/-! ## The physical signed target -/

/-- Section 10.2's chart stress `Q^(2 A) σ / ε`. -/
noncomputable def chartStress (h : ℝ) (N : ℕ) (σ : Vec2) (U : UnsignedLabel) : Vec2 :=
  fun i => ChartScales.Q (U.1 + N) ^ (2 * velocityExponent h) * σ i /
    physicalViscosity h N U

theorem physical_signed_scale (h : ℝ) (N : ℕ) (σ : Vec2) (U : UnsignedLabel) (i : Fin 2) :
    physicalOuter h N U ^ 2 * physicalViscosity h N U * chartStress h N σ U i = σ i := by
  have hQ := ChartScales.Q_pos (U.1 + N)
  have hε := ChartScales.epsilon_pos h (U.1 + N)
  have hp : (ChartScales.Q (U.1 + N) ^ (-velocityExponent h)) ^ 2 *
      ChartScales.Q (U.1 + N) ^ (2 * velocityExponent h) = 1 := by
    rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_add hQ]
    have he : -velocityExponent h * (2 : ℝ) + 2 * velocityExponent h = 0 := by ring
    simp only [Nat.cast_ofNat, he, Real.rpow_zero]
  unfold physicalOuter chartStress
  change _ * ChartScales.epsilon h (U.1 + N) *
    (_ * σ i / ChartScales.epsilon h (U.1 + N)) = _
  calc
    _ = ((ChartScales.Q (U.1 + N) ^ (-velocityExponent h)) ^ 2 *
        ChartScales.Q (U.1 + N) ^ (2 * velocityExponent h)) * σ i := by
      field_simp
    _ = _ := by rw [hp, one_mul]

/-- The actual two-sided primary/signed covariance equals the prescribed
physical stress, for the same constructed squared partition as the primary. -/
theorem physical_signed_cross_covariance {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (T0 σ : Vec2)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (P U).matrix (chartTarget h q N T0 U)) (i : Fin 2) :
    doubleAverage (fun Y θ =>
      assembledRadial P hdet (physicalOuter h N) (physicalViscosity h N) (chartTarget h q N T0) q x
          Y θ *
        signedTangent P hdet (physicalOuter h N) (physicalViscosity h N)
          (chartTarget h q N T0) (chartStress h N σ) q x i Y θ +
      signedRadial P hdet (physicalOuter h N) (physicalViscosity h N)
          (chartTarget h q N T0) (chartStress h N σ) q x Y θ *
        assembledTangent P hdet (physicalOuter h N) (physicalViscosity h N) (chartTarget h q N T0)
            q x i Y θ) =
      σ i := by
  rw [assembled_cross_covariance sys hdet N hN P (physicalOuter h N) (physicalViscosity h N)
    (chartTarget h q N T0) (chartStress h N σ) hq x
    (fun U _ => (ChartScales.epsilon_pos h (U.1 + N)).le) hcone i]
  have heq (U : UnsignedLabel) : physicalOuter h N U ^ 2 * physicalViscosity h N U *
      mask D (tailLabel N U) q x ^ 2 * chartStress h N σ U i = mask D (tailLabel N U) q x ^ 2 * σ i
          := by
    calc
      _ = mask D (tailLabel N U) q x ^ 2 *
        (physicalOuter h N U ^ 2 * physicalViscosity h N U * chartStress h N σ U i) := by ring
      _ = _ := by rw [physical_signed_scale]
  simp_rw [heq]
  have hf : (support (fun U : UnsignedLabel => mask D (tailLabel N U) q x ^ 2)).Finite := by
    apply (finite_active_masks D N hq x).subset
    intro U hU hz
    exact hU (by simp [hz])
  rw [← finsum_mul _ _, physical_mask_tail_sum_sq D N hq hqN x, one_mul]

/-! ## Uniform weighted jets from input classes and a primary lower bound -/

open WeightedClasses

section Weighted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A polynomial reciprocal bound, imposed only on the positive primary
weight.  No regularity of a quotient by the envelope is assumed. -/
noncomputable def InverseControl (s : StripData E) (w g : ℕ → E → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain →
    w n x / g n x ≤ C * s.growth n x ^ p

theorem inverseControl_of_lower {s : StripData E} {w g : ℕ → E → ℝ}
    (hg : ∀ n x, x ∈ s.domain → 0 < g n x) {c : ℝ} (hc : 0 < c) (p : ℕ)
    (hlower : ∀ n x, x ∈ s.domain → c * w n x / s.growth n x ^ p ≤ g n x) :
    InverseControl s w g := by
  refine ⟨c⁻¹, (inv_pos.mpr hc).le, p, ?_⟩
  intro n x hx
  have hG : 0 < s.growth n x ^ p := pow_pos (zero_lt_one.trans_le (s.one_le_growth n x)) _
  have hl := (div_le_iff₀ hG).mp (hlower n x hx)
  apply (div_le_iff₀ (hg n x hx)).mpr
  calc
    w n x = c⁻¹ * (c * w n x) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * (g n x * s.growth n x ^ p) := mul_le_mul_of_nonneg_left hl (inv_pos.mpr hc).le
    _ = _ := by ring

/-- A common finite envelope for input jets and the positive lower bound,
uniform in the discrete band and every point of the strip. -/
theorem class_input_envelope {s : StripData E} {w g r : ℕ → E → ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hp : ∀ n x, x ∈ s.domain → 0 < g n x)
    (hg : MemClass s w 0 g) (hr : MemClass s w 0 r)
    (hlower : InverseControl s w g) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain →
      1 ≤ C * s.growth n x ^ p ∧
      w n x / (C * s.growth n x ^ p) ≤ g n x ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (g n) x‖ ≤ w n x * (C * s.growth n x ^ p)) ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (r n) x‖ ≤ w n x * (C * s.growth n x ^ p)) := by
  obtain ⟨Cg, hCg, pg, hgj⟩ := hg.bounds m
  obtain ⟨Cr, hCr, pr, hrj⟩ := hr.bounds m
  obtain ⟨C0, hC0, p0, hl⟩ := hlower
  let C := Cg + Cr + C0 + 1
  let p := pg + pr + p0
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, p, ?_⟩
  intro n x hx
  have hm (A : ℝ) (hA : 0 ≤ A) (hAC : A ≤ C) (k : ℕ) (hkp : k ≤ p) :
      A * s.growth n x ^ k ≤ C * s.growth n x ^ p := by
    exact mul_le_mul hAC (pow_le_pow_right₀ (s.one_le_growth n x) hkp)
      (pow_nonneg (s.growth_nonneg n x) k) (zero_le_one.trans hC)
  have hB : 1 ≤ C * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (s.one_le_growth n x))
  refine ⟨hB, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (zero_lt_one.trans_le hB)).mpr
    have hl' : w n x / g n x ≤ C * s.growth n x ^ p :=
      (hl n x hx).trans (hm C0 hC0 (by dsimp [C]; linarith) p0 (by dsimp [p]; omega))
    simpa only [mul_comm] using (div_le_iff₀ (hp n x hx)).mp hl'
  · intro j hj
    calc
      _ ≤ Cg * s.growth n x ^ pg * w n x := by
        simpa only [majorant, Real.rpow_zero, mul_one] using hgj n x hx j hj
      _ ≤ (C * s.growth n x ^ p) * w n x := mul_le_mul_of_nonneg_right
        (hm Cg hCg (by dsimp [C]; linarith) pg (by dsimp [p]; omega)) (hw n x hx).le
      _ = _ := by ring
  · intro j hj
    calc
      _ ≤ Cr * s.growth n x ^ pr * w n x := by
        simpa only [majorant, Real.rpow_zero, mul_one] using hrj n x hx j hj
      _ ≤ (C * s.growth n x ^ p) * w n x := mul_le_mul_of_nonneg_right
        (hm Cr hCr (by dsimp [C]; linarith) pr (by dsimp [p]; omega)) (hw n x hx).le
      _ = _ := by ring

/-- Signed jet cost, given by `WeightedQuotients.chooseSum j * WeightedQuotients.orderBound (-(1
/ 2 : ℝ)) j / 2`. -/
noncomputable def signedJetCost (j : ℕ) : ℝ :=
  WeightedQuotients.chooseSum j * WeightedQuotients.orderBound (-(1 / 2 : ℝ)) j / 2

/-- Prefix jet cost, given by `1 + ∑ j ∈ Finset.range (m + 1), |signedJetCost j|`. -/
noncomputable def prefixJetCost (m : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (m + 1), |signedJetCost j|

theorem prefixJetCost_pos (m : ℕ) : 0 < prefixJetCost m := by
  have hs := Finset.sum_nonneg (s := Finset.range (m + 1)) (fun j _ => abs_nonneg (signedJetCost j))
  dsimp [prefixJetCost]
  linarith

theorem signedJetCost_le {j m : ℕ} (hj : j ≤ m) : signedJetCost j ≤ prefixJetCost m := by
  have hs := Finset.single_le_sum (f := fun j => |signedJetCost j|)
    (fun k _ => abs_nonneg (signedJetCost k)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact (le_abs_self _).trans (hs.trans (by dsimp [prefixJetCost]; linarith))

theorem signedJetCost_nonneg (j : ℕ) : 0 ≤ signedJetCost j :=
  div_nonneg (mul_nonneg (WeightedQuotients.chooseSum_nonneg j)
    (WeightedQuotients.orderBound_nonneg _ _)) (by norm_num)

/-- Derive the all-order signed quotient class from weighted input jets.
The weight is never differentiated or divided out as a variable function. -/
theorem signed_quotient_class_zero {s : StripData E} {w g r : ℕ → E → ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hp : ∀ n x, x ∈ s.domain → 0 < g n x)
    (hg : MemClass s w 0 g) (hr : MemClass s w 0 r)
    (hlower : InverseControl s w g) :
    MemClass s (fun n x => Real.sqrt (w n x)) 0
      (fun n x => r n x / (2 * Real.sqrt (g n x))) := by
  have hsmooth (n : ℕ) : ContDiffOn ℝ ∞
      (fun x => r n x / (2 * Real.sqrt (g n x))) s.domain :=
    (hr.smooth n).div (contDiffOn_const.mul ((hg.smooth n).sqrt (fun x hx => (hp n x hx).ne')))
      (fun x hx => mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hp n x hx)).ne')
  refine ⟨fun n x hx => Real.sqrt_nonneg _, hsmooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, henv⟩ := class_input_envelope hw hp hg hr hlower m
  refine ⟨prefixJetCost m * C ^ (2 * m + 2),
    mul_nonneg (prefixJetCost_pos m).le (pow_nonneg (zero_le_one.trans hC) _), p * (2 * m + 2), ?_⟩
  intro n x hx j hj
  obtain ⟨hB, hlo, hgj, hrj⟩ := henv n x hx
  have hb := WeightedQuotients.signed_jet_bound s.isOpen_domain (hg.smooth n) (hr.smooth n)
    (hp n) hx (hw n x hx) hB j hlo (fun k hk => hgj k (hk.trans hj)) (fun k hk => hrj k (hk.trans
        hj))
  calc
    _ ≤ Real.sqrt (w n x) * signedJetCost j * (C * s.growth n x ^ p) ^ (2 * j + 2) := hb
    _ ≤ Real.sqrt (w n x) * prefixJetCost m * (C * s.growth n x ^ p) ^ (2 * m + 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (signedJetCost_le hj) (Real.sqrt_nonneg _)
      · exact pow_le_pow_right₀ hB (by omega)
      · exact pow_nonneg (zero_le_one.trans hB) _
      · exact mul_nonneg (Real.sqrt_nonneg _) (prefixJetCost_pos m).le
    _ = majorant s (fun n x => Real.sqrt (w n x)) 0
        (prefixJetCost m * C ^ (2 * m + 2)) (p * (2 * m + 2)) n x := by
      simp only [majorant, Real.rpow_zero, mul_one, mul_pow, pow_mul]
      ring

/-- Discrete powers of epsilon pass through the quotient without a jet loss. -/
theorem signed_quotient_class {s : StripData E} {w g r : ℕ → E → ℝ} {β : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hp : ∀ n x, x ∈ s.domain → 0 < g n x)
    (hg : MemClass s w 0 g) (hr : MemClass s w β r)
    (hlower : InverseControl s w g) :
    MemClass s (fun n x => Real.sqrt (w n x)) β
      (fun n x => r n x / (2 * Real.sqrt (g n x))) := by
  have hr0 : MemClass s w 0 (fun n x => s.epsilon n ^ (-β) * r n x) := by
    simpa only [smul_eq_mul, add_neg_cancel] using hr.band_smul (bandBound_rpow s (-β))
  have hq0 := signed_quotient_class_zero hw hp hg hr0 hlower
  have hq := hq0.band_smul (bandBound_rpow s β)
  have heq : (fun n x => s.epsilon n ^ β • (s.epsilon n ^ (-β) * r n x / (2 * Real.sqrt (g n x)))) =
      (fun n x => r n x / (2 * Real.sqrt (g n x))) := by
    funext n x
    simp only [smul_eq_mul, ← mul_div_assoc, ← mul_assoc,
      ← Real.rpow_add (s.epsilon_pos n), add_neg_cancel, Real.rpow_zero, one_mul]
  simpa only [zero_add, heq] using hq

/-- A companion primary square-root bound from the same genuine inputs. -/
theorem sqrt_class {s : StripData E} {w g : ℕ → E → ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hp : ∀ n x, x ∈ s.domain → 0 < g n x)
    (hg : MemClass s w 0 g) (hlower : InverseControl s w g) :
    MemClass s (fun n x => Real.sqrt (w n x)) 0 (fun n x => Real.sqrt (g n x)) := by
  have hq := signed_quotient_class_zero hw hp hg hg hlower
  have htwo : BandBound s 0 (fun _ => (2 : ℝ)) := by
    refine ⟨2, by norm_num, 0, ?_⟩
    intro n
    simp
  have heq : (fun n x => (2 : ℝ) • (g n x / (2 * Real.sqrt (g n x)))) =
      (fun n x => Real.sqrt (g n x)) := by
    funext n x
    simp only [smul_eq_mul]
    calc
      2 * (g n x / (2 * Real.sqrt (g n x))) = g n x / Real.sqrt (g n x) := by ring
      _ = _ := Real.div_sqrt
  simpa only [zero_add, heq] using hq.band_smul htwo

theorem memClass_congrOn {s : StripData E} {w f g : ℕ → E → ℝ} {β : ℝ}
    (hf : MemClass s w β f) (heq : ∀ n x, x ∈ s.domain → f n x = g n x) :
    MemClass s w β g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (fun x hx => (heq n x hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he : g n =ᶠ[𝓝 x] f n := by
    filter_upwards [s.isOpen_domain.mem_nhds hx] with y hy
    exact (heq n y hy).symm
  rw [WeightedQuotients.jet_congr he j]
  exact hb n x hx j hj

/-- The actual matrix-inverse signed coefficient has the half-weight class,
derived from the inverse numerator jets and positive primary inverse jets. -/
theorem increment_wave_class {s : StripData E} {H : ℕ → E → Mat2}
    {T R : ℕ → E → Vec2} {β : ℝ} (j : Fin 2)
    (hζ : ∀ x ∈ s.domain, 0 < s.zeta x)
    (hcone : ∀ n x, x ∈ s.domain → SmoothCovariance.StrictCone (H n x) (T n x))
    (hY : MeanClass s 0 (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hR : MeanClass s β (fun n x => ((H n x)⁻¹.mulVec (R n x)) j))
    (hlower : InverseControl s (fun _ x => s.zeta x)
      (fun n x => ((H n x)⁻¹.mulVec (T n x)) j)) :
    WaveClass s (fun _ _ => 1) β (fun n x => increment (H n x) (T n x) (R n x) j) := by
  have hq := signed_quotient_class (fun n x hx => hζ x hx)
    (fun n x hx => (amplitudes_are_inverse_weights (hcone n x hx) j).1) hY hR hlower
  have he := memClass_congrOn hq
    (fun n x hx => (increment_eq_inverse (H n x) (T n x) (R n x) (hcone n x hx) j).symm)
  simpa only [WaveClass, mul_one] using he

/-- Multiplying a signed coefficient by the original pulse envelope gives
the wave weight `sqrt ζ * P` with the expected epsilon exponent. -/
theorem increment_times_pulse_class {s : StripData E} {H : ℕ → E → Mat2}
    {T R : ℕ → E → Vec2} {β γ : ℝ} {P f : ℕ → E → ℝ} (j : Fin 2)
    (hζ : ∀ x ∈ s.domain, 0 < s.zeta x)
    (hcone : ∀ n x, x ∈ s.domain → SmoothCovariance.StrictCone (H n x) (T n x))
    (hY : MeanClass s 0 (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hR : MeanClass s β (fun n x => ((H n x)⁻¹.mulVec (R n x)) j))
    (hlower : InverseControl s (fun _ x => s.zeta x)
      (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hf : MemClass s P γ f) :
    WaveClass s P (β + γ)
      (fun n x => increment (H n x) (T n x) (R n x) j * f n x) := by
  have hc := increment_wave_class j hζ hcone hY hR hlower
  simpa only [WaveClass, mul_one] using (MemClass.mul hc hf)

/-- The exact signed-square column satisfies a mean-class estimate.  The
assumptions are estimates for the input inverse solves and actual columns. -/
theorem signed_square_class {s : StripData E} {H : ℕ → E → Mat2}
    {T R : ℕ → E → Vec2} {β : ℝ} (i : Fin 2)
    (hζ : ∀ x ∈ s.domain, 0 < s.zeta x)
    (hcone : ∀ n x, x ∈ s.domain → SmoothCovariance.StrictCone (H n x) (T n x))
    (hY : ∀ j, MeanClass s 0 (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hR : ∀ j, MeanClass s β (fun n x => ((H n x)⁻¹.mulVec (R n x)) j))
    (hlower : ∀ j, InverseControl s (fun _ x => s.zeta x)
      (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hH : ∀ j, UnweightedClass s 0 (fun n x => H n x i j)) :
    MeanClass s (2 * β) (fun n x => squareColumn (H n x) (T n x) (R n x) i) := by
  have ht (j : Fin 2) : MeanClass s (β + β) (fun n x =>
      H n x i j * (increment (H n x) (T n x) (R n x) j * increment (H n x) (T n x) (R n x) j)) := by
    have hc := increment_wave_class j hζ hcone (hY j) (hR j) (hlower j)
    have hsq := WeightedClasses.WaveClass.mul_mean hc hc (fun _ _ _ => zero_le_one) (fun _ _ _ =>
        le_rfl)
    simpa only [MeanClass, UnweightedClass, one_mul, zero_add] using (MemClass.mul (hH j) hsq)
  have hsum := MemClass.sum Finset.univ _ (fun n x hx => s.zeta_nonneg x hx) (fun j _ => ht j)
  simpa only [MeanClass, squareColumn, Matrix.mulVec, dotProduct, pow_two, two_mul] using hsum

/-- Native velocity amplitudes contain `sqrt ε`, so their signed-square
covariance is `ε H(δa²)` and has order `2B - 2loss`. -/
theorem native_signed_square_class {s : StripData E} {H : ℕ → E → Mat2}
    {T R : ℕ → E → Vec2} (B loss : ℝ) (i : Fin 2)
    (hζ : ∀ x ∈ s.domain, 0 < s.zeta x)
    (hcone : ∀ n x, x ∈ s.domain → SmoothCovariance.StrictCone (H n x) (T n x))
    (hY : ∀ j, MeanClass s 0 (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hR : ∀ j, MeanClass s (B - 1 / 2 - loss) (fun n x => ((H n x)⁻¹.mulVec (R n x)) j))
    (hlower : ∀ j, InverseControl s (fun _ x => s.zeta x)
      (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hH : ∀ j, UnweightedClass s 0 (fun n x => H n x i j)) :
    MeanClass s (2 * B - 2 * loss)
      (fun n x => s.epsilon n * squareColumn (H n x) (T n x) (R n x) i) := by
  have hc := signed_square_class i hζ hcone hY hR hlower hH
  have hb := hc.band_smul (bandBound_rpow s 1)
  have he : 2 * (B - 1 / 2 - loss) + 1 = 2 * B - 2 * loss := by ring
  unfold MeanClass
  simpa only [he, Real.rpow_one, smul_eq_mul] using hb

/-- This version keeps the flat weights of the individual columns.  The
column weight and its inverse-solve weight multiply back to the mean weight;
an exponentially singular inverse is therefore not assumed unweighted. -/
theorem balanced_signed_square_class {s : StripData E} {H : ℕ → E → Mat2}
    {T R : ℕ → E → Vec2} {w v : Fin 2 → ℕ → E → ℝ} {β : ℝ} (i : Fin 2)
    (hw : ∀ j n x, x ∈ s.domain → 0 < w j n x)
    (hcone : ∀ n x, x ∈ s.domain → SmoothCovariance.StrictCone (H n x) (T n x))
    (hY : ∀ j, MemClass s (w j) 0 (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hR : ∀ j, MemClass s (w j) β (fun n x => ((H n x)⁻¹.mulVec (R n x)) j))
    (hlower : ∀ j, InverseControl s (w j) (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hH : ∀ j, MemClass s (v j) 0 (fun n x => H n x i j))
    (hbalance : ∀ j n x, x ∈ s.domain → v j n x * w j n x ≤ s.zeta x) :
    MeanClass s (2 * β) (fun n x => squareColumn (H n x) (T n x) (R n x) i) := by
  have ht (j : Fin 2) : MeanClass s (β + β) (fun n x =>
      H n x i j * (increment (H n x) (T n x) (R n x) j * increment (H n x) (T n x) (R n x) j)) := by
    have hc := signed_quotient_class (hw j)
      (fun n x hx => (amplitudes_are_inverse_weights (hcone n x hx) j).1) (hY j) (hR j) (hlower j)
    have hi := memClass_congrOn hc
      (fun n x hx => (increment_eq_inverse (H n x) (T n x) (R n x) (hcone n x hx) j).symm)
    have hsq : MemClass s (w j) (β + β)
        (fun n x => increment (H n x) (T n x) (R n x) j * increment (H n x) (T n x) (R n x) j) := by
      apply (MemClass.mul hi hi).mono_weight (fun n x hx => (hw j n x hx).le)
      intro n x hx
      exact (Real.mul_self_sqrt (hw j n x hx).le).le
    have hh := (MemClass.mul (hH j) hsq).mono_weight (fun n x hx => s.zeta_nonneg x hx) (hbalance j)
    unfold MeanClass
    simpa only [zero_add] using hh
  have hsum := MemClass.sum Finset.univ _ (fun n x hx => s.zeta_nonneg x hx) (fun j _ => ht j)
  simpa only [MeanClass, squareColumn, Matrix.mulVec, dotProduct, pow_two, two_mul] using hsum

/-- Exact cancellation of the column's flat factor with the remaining
inverse-solve factor, including the zero edge. -/
theorem balanced_edge_weights (σ κ δ : ℝ) :
    FlatCutoff.edge κ δ * FlatCutoff.edge (σ - κ) δ = FlatCutoff.edge σ δ := by
  rw [FlatCovariance.edge_mul]
  congr 1
  ring

theorem balanced_native_signed_square_class {s : StripData E} {H : ℕ → E → Mat2}
    {T R : ℕ → E → Vec2} {w v : Fin 2 → ℕ → E → ℝ} (B loss : ℝ) (i : Fin 2)
    (hw : ∀ j n x, x ∈ s.domain → 0 < w j n x)
    (hcone : ∀ n x, x ∈ s.domain → SmoothCovariance.StrictCone (H n x) (T n x))
    (hY : ∀ j, MemClass s (w j) 0 (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hR : ∀ j, MemClass s (w j) (B - 1 / 2 - loss) (fun n x => ((H n x)⁻¹.mulVec (R n x)) j))
    (hlower : ∀ j, InverseControl s (w j) (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hH : ∀ j, MemClass s (v j) 0 (fun n x => H n x i j))
    (hbalance : ∀ j n x, x ∈ s.domain → v j n x * w j n x ≤ s.zeta x) :
    MeanClass s (2 * B - 2 * loss)
      (fun n x => s.epsilon n * squareColumn (H n x) (T n x) (R n x) i) := by
  have hc := balanced_signed_square_class i hw hcone hY hR hlower hH hbalance
  have hb := hc.band_smul (bandBound_rpow s 1)
  have he : 2 * (B - 1 / 2 - loss) + 1 = 2 * B - 2 * loss := by ring
  unfold MeanClass
  simpa only [he, Real.rpow_one, smul_eq_mul] using hb

end Weighted

/-! ## A quantitative bound for the complete assembled signed square -/

theorem increment_sq_bound (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) (j : Fin 2)
    {l d : ℝ} (hl : 0 < l) (_hd : 0 ≤ d)
    (hY : l ≤ (H⁻¹.mulVec T) j) (hR : |(H⁻¹.mulVec R) j| ≤ d) :
    increment H T R j ^ 2 ≤ d ^ 2 / (4 * l) := by
  have hpos := (amplitudes_are_inverse_weights hcone j).1
  have hr2 : ((H⁻¹.mulVec R) j) ^ 2 ≤ d ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hR 2
  rw [increment_eq_inverse H T R hcone j, div_pow, mul_pow, Real.sq_sqrt hpos.le]
  norm_num only [OfNat.ofNat, Nat.cast_ofNat]
  calc
    _ ≤ d ^ 2 / (4 * (H⁻¹.mulVec T) j) := div_le_div_of_nonneg_right hr2 (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg d) (by positivity) (by linarith)

theorem squareColumn_abs_bound (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) (i : Fin 2)
    {l d K : ℝ} (hl : 0 < l) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hY : ∀ j, l ≤ (H⁻¹.mulVec T) j) (hR : ∀ j, |(H⁻¹.mulVec R) j| ≤ d)
    (hH : ∀ j, |H i j| ≤ K) : |squareColumn H T R i| ≤ 2 * K * d ^ 2 / (4 * l) := by
  have hb (j : Fin 2) : |H i j * increment H T R j ^ 2| ≤ K * (d ^ 2 / (4 * l)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (increment H T R j))]
    exact mul_le_mul (hH j) (increment_sq_bound H T R hcone j hl hd (hY j) (hR j))
      (sq_nonneg _) hK
  unfold squareColumn
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc
    _ ≤ |H i 0 * increment H T R 0 ^ 2| + |H i 1 * increment H T R 1 ^ 2| := abs_add_le _ _
    _ ≤ K * (d ^ 2 / (4 * l)) + K * (d ^ 2 / (4 * l)) := add_le_add (hb 0) (hb 1)
    _ = _ := by ring

theorem mask_average_bound (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q)
    (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (f : UnsignedLabel → ℝ) (B : ℝ)
    (hb : ∀ U, mask D (tailLabel N U) q x ≠ 0 → |f U| ≤ B) :
    |∑ᶠ U : UnsignedLabel, mask D (tailLabel N U) q x ^ 2 * f U| ≤ B := by
  classical
  let F := (finite_active_masks D N hq x).toFinset
  have hz (U : UnsignedLabel) (hU : U ∉ F) : mask D (tailLabel N U) q x = 0 := by
    by_contra hm
    exact hU ((finite_active_masks D N hq x).mem_toFinset.mpr hm)
  have heq : (∑ᶠ U : UnsignedLabel, mask D (tailLabel N U) q x ^ 2 * f U) =
      ∑ U ∈ F, mask D (tailLabel N U) q x ^ 2 * f U := by
    apply finsum_eq_sum_of_support_subset
    intro U hU
    by_contra hn
    exact hU (by simp [hz U hn])
  have hs : (∑ U ∈ F, mask D (tailLabel N U) q x ^ 2) = 1 := by
    rw [← physical_mask_tail_sum_sq D N hq hqN x]
    symm
    apply finsum_eq_sum_of_support_subset
    intro U hU
    by_contra hn
    exact hU (by simp [hz U hn])
  rw [heq]
  calc
    _ ≤ ∑ U ∈ F, |mask D (tailLabel N U) q x ^ 2 * f U| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ U ∈ F, mask D (tailLabel N U) q x ^ 2 * B := by
      apply Finset.sum_le_sum
      intro U hU
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (hb U ((finite_active_masks D N hq x).mem_toFinset.mp hU)) (sq_nonneg _)
    _ = B := by rw [← Finset.sum_mul, hs, one_mul]

/-- A bound for the full actual averaged remainder, proved from the primary
inverse lower bound, signed inverse numerator bound, and actual column bound.
The number of active labels costs nothing because their squared masks sum to one. -/
theorem assembled_signed_square_bound {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (outer ε : UnsignedLabel → ℝ) (T R : UnsignedLabel → Vec2)
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position)
    (hε : ∀ U, mask D (tailLabel N U) q x ≠ 0 → 0 ≤ ε U)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 → SmoothCovariance.StrictCone (P U).matrix (T U))
    {l d K Λ : ℝ} (hl : 0 < l) (hd : 0 ≤ d) (hK : 0 ≤ K) (hΛ : 0 ≤ Λ)
    (hY : ∀ U, mask D (tailLabel N U) q x ≠ 0 → ∀ j, l ≤ ((P U).matrix⁻¹.mulVec (T U)) j)
    (hR : ∀ U, mask D (tailLabel N U) q x ≠ 0 → ∀ j, |((P U).matrix⁻¹.mulVec (R U)) j| ≤ d)
    (hH : ∀ U, mask D (tailLabel N U) q x ≠ 0 → ∀ i j, |(P U).matrix i j| ≤ K)
    (hscale : ∀ U, mask D (tailLabel N U) q x ≠ 0 → outer U ^ 2 * ε U ≤ Λ) (i : Fin 2) :
    |doubleAverage (fun Y θ => signedRadial P hdet outer ε T R q x Y θ *
      signedTangent P hdet outer ε T R q x i Y θ)| ≤ Λ * (2 * K * d ^ 2 / (4 * l)) := by
  rw [assembled_signed_square sys hdet N hN P outer ε T R hq x hε i]
  have heq : (fun U : UnsignedLabel => outer U ^ 2 * ε U * mask D (tailLabel N U) q x ^ 2 *
      squareColumn (P U).matrix (T U) (R U) i) =
      fun U => mask D (tailLabel N U) q x ^ 2 *
        (outer U ^ 2 * ε U * squareColumn (P U).matrix (T U) (R U) i) := by
    funext U
    ring
  rw [heq]
  apply mask_average_bound D N hq hqN x
  intro U hU
  rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hε U hU))]
  exact mul_le_mul (hscale U hU)
    (squareColumn_abs_bound (P U).matrix (T U) (R U) (hcone U hU) i hl hd hK (hY U hU) (hR U hU)
        (hH U hU i))
    (abs_nonneg _) hΛ

/-! ## Smooth edge extension of the actual inverse amplitudes -/

section Edge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extended increment, given by `FlatZeroExtension.zeroExtension (fun p => ((H p)⁻¹.mulVec (R
p)) j / (2 * Real.sqrt (((H p)⁻¹.mulVec (T p)) j)))`. -/
noncomputable def extendedIncrement (H : E × ℝ → Mat2) (T R : E × ℝ → Vec2)
    (j : Fin 2) : E × ℝ → ℝ :=
  FlatZeroExtension.zeroExtension (fun p => ((H p)⁻¹.mulVec (R p)) j /
    (2 * Real.sqrt (((H p)⁻¹.mulVec (T p)) j)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extendedIncrement_of_pos (H : E × ℝ → Mat2) (T R : E × ℝ → Vec2)
    (j : Fin 2) {p : E × ℝ} (hp : 0 < p.2) (hcone : SmoothCovariance.StrictCone (H p) (T p)) :
    extendedIncrement H T R j p = increment (H p) (T p) (R p) j := by
  rw [extendedIncrement, FlatZeroExtension.zeroExtension_of_pos _ hp,
    increment_eq_inverse _ _ _ hcone j]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extendedIncrement_of_nonpos (H : E × ℝ → Mat2) (T R : E × ℝ → Vec2)
    (j : Fin 2) {p : E × ℝ} (hp : p.2 ≤ 0) : extendedIncrement H T R j p = 0 :=
  FlatZeroExtension.zeroExtension_of_nonpos _ hp

/-- Joint smoothness, every parameter jet, and zero tensors at the edge,
from actual inverse-solve derivatives and the primary's weighted lower bound. -/
theorem extendedIncrement_regular {U : Set E} (hU : IsOpen U) {c : ℝ} (hc : 0 < c)
    {H : E × ℝ → Mat2} {T R : E × ℝ → Vec2} {S : E × ℝ → ℝ} (j : Fin 2)
    (hS : ∀ p ∈ WeightedQuotients.edgeStrip U, 1 ≤ S p)
    (hscale : WeightedQuotients.LocallyBoundedScale U S)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) (U ×ˢ Ioi 0))
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun p => T p i) (U ×ˢ Ioi 0))
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun p => R p i) (U ×ˢ Ioi 0))
    (hcone : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), SmoothCovariance.StrictCone (H p) (T p))
    (hlower : WeightedQuotients.PolyBound (WeightedQuotients.edgeStrip U) S (fun p => p.2⁻¹)
      (fun p => FlatCutoff.edge c p.2 / ((H p)⁻¹.mulVec (T p)) j))
    (hYjets : WeightedQuotients.WeightedJets c U S (fun p => ((H p)⁻¹.mulVec (T p)) j))
    (hRjets : WeightedQuotients.WeightedJets c U S (fun p => ((H p)⁻¹.mulVec (R p)) j)) :
    ContDiffOn ℝ ∞ (extendedIncrement H T R j) (U ×ˢ univ) ∧
      WeightedQuotients.WeightedJets (c / 2) U S (extendedIncrement H T R j) ∧
      ∀ m : ℕ, ∀ x ∈ U, iteratedFDeriv ℝ m (extendedIncrement H T R j) (x, 0) = 0 := by
  have hp : ∀ p ∈ U ×ˢ Ioi (0 : ℝ), 0 < ((H p)⁻¹.mulVec (T p)) j :=
    fun p hp => (amplitudes_are_inverse_weights (hcone p hp) j).1
  have hYs := SmoothCovariance.contDiffOn_inverse_solution hH hT
    (fun p hp => (hcone p hp).det_ne_zero) j
  have hRs := SmoothCovariance.contDiffOn_inverse_solution hH hR
    (fun p hp => (hcone p hp).det_ne_zero) j
  have he := WeightedQuotients.weighted_zero_extension hc hU hS hscale hp hYs hRs hlower hYjets
      hRjets
  refine ⟨he.2.1, ?_, fun m x hx => (he.2.2 m x hx).2⟩
  have hj := (WeightedQuotients.weighted_half_jets hU hS hp hYs hRs hlower hYjets hRjets).2
  intro m
  apply (hj m).mono
  intro p hp
  change ‖iteratedFDeriv ℝ m (FlatZeroExtension.zeroExtension _) p‖ / _ ≤ _
  rw [WeightedQuotients.jet_congr (FlatZeroExtension.zeroExtension_germ_pos _ hp.2.1) m]

/-- Masked extended increment, given by `mask D L (q p) (x p) * extendedIncrement H T R j p`. -/
noncomputable def maskedExtendedIncrement (D : ℝ) (L : UnsignedLabel)
    (q : E × ℝ → ℝ) (x : E × ℝ → SlotColoring.Position)
    (H : E × ℝ → Mat2) (T R : E × ℝ → Vec2) (j : Fin 2) (p : E × ℝ) : ℝ :=
  mask D L (q p) (x p) * extendedIncrement H T R j p

theorem physical_mask_smooth (D : ℝ) (L : UnsignedLabel) :
    ContDiff ℝ ∞ (fun p : ℝ × SlotColoring.Position => mask D L p.1 p.2) :=
  ((SquaredPartition.dyadicMask_smooth (L.1 : ℤ)).comp contDiff_fst).mul
    ((SquaredPartition.physicalSlowMask_smooth D L.1 L.2).comp contDiff_snd)

theorem physical_mask_compactSupport (D : ℝ) (L : UnsignedLabel) (hL : 1 ≤ L.1) :
    HasCompactSupport (fun p : ℝ × SlotColoring.Position => mask D L p.1 p.2) := by
  have hc : IsCompact (tsupport (SquaredPartition.dyadicMask (L.1 : ℤ)) ×ˢ
      tsupport (SquaredPartition.physicalSlowMask D L.1 L.2)) :=
    (SquaredPartition.dyadicMask_compactSupport _).prod
      (SquaredPartition.physicalSlowMask_compactSupport D hL L.2)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro p hp
  change SquaredPartition.dyadicMask (L.1 : ℤ) p.1 *
    SquaredPartition.physicalSlowMask D L.1 L.2 p.2 ≠ 0 at hp
  exact ⟨subset_closure (mul_ne_zero_iff.mp hp).1, subset_closure (mul_ne_zero_iff.mp hp).2⟩

theorem masked_physical_coefficient_compactSupport (D : ℝ) (L : UnsignedLabel) (hL : 1 ≤ L.1)
    (f : ℝ × SlotColoring.Position → ℝ) :
    HasCompactSupport (fun p => mask D L p.1 p.2 * f p) :=
  (physical_mask_compactSupport D L hL).mul_right

theorem masked_physical_coefficients_locallyFinite (D : ℝ) (N : ℕ)
    (f : UnsignedLabel → Ioi (0 : ℝ) × SlotColoring.Position → ℝ) :
    LocallyFinite (fun L => support (fun p : Ioi (0 : ℝ) × SlotColoring.Position =>
      mask D (tailLabel N L) p.1 p.2 * f L p)) := by
  apply ((mask_locallyFinite D).comp_injective (tailLabel_injective N)).subset
  intro L p hp
  exact (mul_ne_zero_iff.mp hp).1

theorem masked_physical_jet_support (D : ℝ) (L : UnsignedLabel)
    (f : ℝ × SlotColoring.Position → ℝ) (m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (fun p => mask D L p.1 p.2 * f p)) ⊆
      tsupport (fun p : ℝ × SlotColoring.Position => mask D L p.1 p.2) := by
  apply (tsupport_iteratedFDeriv_subset m).trans
  apply closure_mono
  intro p hp
  exact (mul_ne_zero_iff.mp hp).1

theorem maskedExtendedIncrement_smooth (D : ℝ) (L : UnsignedLabel)
    {U : Set E} {q : E × ℝ → ℝ} {x : E × ℝ → SlotColoring.Position}
    {H : E × ℝ → Mat2} {T R : E × ℝ → Vec2} (j : Fin 2)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ univ)) (hx : ContDiffOn ℝ ∞ x (U ×ˢ univ))
    (he : ContDiffOn ℝ ∞ (extendedIncrement H T R j) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (maskedExtendedIncrement D L q x H T R j) (U ×ˢ univ) :=
  (((physical_mask_smooth D L).comp_contDiffOn (hq.prodMk hx)).mul he)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The signed update cannot create support outside the original mask or
on the zero side of the edge.  Its inverse numerator also controls support. -/
theorem maskedExtendedIncrement_support (D : ℝ) (L : UnsignedLabel)
    (q : E × ℝ → ℝ) (x : E × ℝ → SlotColoring.Position)
    (H : E × ℝ → Mat2) (T R : E × ℝ → Vec2) (j : Fin 2) :
    support (maskedExtendedIncrement D L q x H T R j) ⊆
      {p | mask D L (q p) (x p) ≠ 0 ∧ 0 < p.2 ∧ ((H p)⁻¹.mulVec (R p)) j ≠ 0} := by
  intro p hp
  have hm := mul_ne_zero_iff.mp hp
  refine ⟨hm.1, ?_, ?_⟩
  · by_contra hn
    exact hm.2 (extendedIncrement_of_nonpos H T R j (le_of_not_gt hn))
  · intro hr
    apply hm.2
    by_cases hδ : 0 < p.2
    · simp [extendedIncrement, FlatZeroExtension.zeroExtension_of_pos _ hδ, hr]
    · exact extendedIncrement_of_nonpos H T R j (le_of_not_gt hδ)

end Edge

end NavierStokes.SignedCovariance
