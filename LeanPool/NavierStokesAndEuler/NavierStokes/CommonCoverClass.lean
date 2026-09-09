/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverSolve
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalGraphBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityHomogeneity

@[expose] public section

/-!
# Uniform stripped jets on a common cover

The input of the copy solve is evaluated on the common torus.  The two actual
argument maps below include the integration time as a variable.  Their affine
derivatives, the native time scale, and adjacent-band changes give estimates
whose constants precede the band, copy, and source.  No native periodicity of
the source is used.
-/

namespace NavierStokes.CommonCoverClass

noncomputable section

open Set Function
open scoped ContDiff BigOperators Topology
open TorusInverse

abbrev CCS := CommonCoverSolve.Geometry

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

section Envelopes

variable {X Y V W : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A point-dependent bound on a finite prefix of actual Fréchet jets. -/
def EnvelopeJets (m : ℕ) (f : X → V) (envelope : X → ℝ) : Prop :=
  ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ envelope x

theorem EnvelopeJets.nonneg {m : ℕ} {f : X → V} {e : X → ℝ}
    (hf : EnvelopeJets m f e) (x : X) : 0 ≤ e x :=
  (norm_nonneg _).trans (hf 0 (Nat.zero_le _) x)

theorem EnvelopeJets.mono {m : ℕ} {f : X → V} {e e' : X → ℝ}
    (hf : EnvelopeJets m f e) (he : ∀ x, e x ≤ e' x) : EnvelopeJets m f e' :=
  fun j hj x => (hf j hj x).trans (he x)

theorem affine_jet_bound {f : Y → V} (hf : ContDiff ℝ ∞ f)
    (L : X →L[ℝ] Y) (c : Y) {K : ℝ} (hK : 1 ≤ K) (hL : ‖L‖ ≤ K)
    (m : ℕ) (x : X) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (c + L x)‖ ≤ A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun z => f (c + L z)) x‖ ≤ A * K ^ m := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  intro j hj
  refine (CommonCoverSolve.norm_iteratedFDeriv_affine_le hf L c x j).trans ?_
  exact mul_le_mul (hb j hj)
    ((pow_le_pow_left₀ (norm_nonneg _) hL j).trans (pow_le_pow_right₀ hK hj))
    (pow_nonneg (norm_nonneg _) _) hA

theorem EnvelopeJets.affine {m : ℕ} {f : Y → V} {e : Y → ℝ}
    (hb : EnvelopeJets m f e) (hf : ContDiff ℝ ∞ f)
    (L : X →L[ℝ] Y) (c : Y) {K : ℝ} (hK : 1 ≤ K) (hL : ‖L‖ ≤ K) :
    EnvelopeJets m (fun x => f (c + L x)) (fun x => e (c + L x) * K ^ m) := by
  intro j hj x
  exact affine_jet_bound hf L c hK hL m x (fun i hi => hb i hi _) j hj

/-- The weight is evaluated at the same point in both factors; it need not
be differentiated in this bound. -/
theorem clm_apply_jet_bound {f : X → V →L[ℝ] W} {g : X → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (m : ℕ) (x : X)
    {A B : ℝ} (hA : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hB : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => f y (g y)) x‖ ≤ 2 ^ m * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  intro j hj
  refine (norm_iteratedFDeriv_clm_apply hf hg x (nat_le_infty j)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hA i (hij.trans hj)) (by positivity))
        (hB (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (mul_nonneg (by positivity) hA0)
    _ = 2 ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ m * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA0) hB0

theorem EnvelopeJets.clm_apply {m : ℕ} {f : X → V →L[ℝ] W} {g : X → V}
    {A B : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hA : EnvelopeJets m f A) (hB : EnvelopeJets m g B) :
    EnvelopeJets m (fun x => f x (g x)) (fun x => 2 ^ m * A x * B x) :=
  fun j hj x => clm_apply_jet_bound hf hg m x (fun i hi => hA i hi x)
    (fun i hi => hB i hi x) j hj

end Envelopes

section Arguments

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Joint slow/common-coordinate/integration-time space. -/
abbrev Joint (P : Type) := (P × Plane) × ℝ

noncomputable def nativeArgument (g : CCS) (k : Frequency) (w : Joint P) : P × Plane :=
  (w.1.1, ((g.coordinates k w.1.2).1, w.2))

noncomputable def sourceArgument (g : CCS) (k : Frequency) (w : Joint P) : P × Plane :=
  (w.1.1, g.path k w.1.2 w.2)

noncomputable def nativeLinear (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : CCS) : Joint P →L[ℝ] P × Plane :=
  ((ContinuousLinearMap.fst ℝ P Plane).comp (ContinuousLinearMap.fst ℝ (P × Plane) ℝ)).prod
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (g.coordinateLinear.comp ((ContinuousLinearMap.snd ℝ P Plane).comp
        (ContinuousLinearMap.fst ℝ (P × Plane) ℝ)))).prod
      (ContinuousLinearMap.snd ℝ (P × Plane) ℝ))

noncomputable def sourceLinear (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : CCS) : Joint P →L[ℝ] P × Plane :=
  ((ContinuousLinearMap.fst ℝ P Plane).comp (ContinuousLinearMap.fst ℝ (P × Plane) ℝ)).prod
    (g.pointLinear.comp ((ContinuousLinearMap.snd ℝ P Plane).comp (nativeLinear P g)))

@[simp] theorem nativeLinear_apply (g : CCS) (w : Joint P) :
    nativeLinear P g w = (w.1.1, ((g.coordinateLinear w.1.2).1, w.2)) := rfl

@[simp] theorem sourceLinear_apply (g : CCS) (w : Joint P) :
    sourceLinear P g w =
      (w.1.1, g.pointLinear ((g.coordinateLinear w.1.2).1, w.2)) := rfl

theorem nativeArgument_affine (g : CCS) (k : Frequency) (w : Joint P) :
    nativeArgument g k w = nativeArgument g k 0 + nativeLinear P g w := by
  simp only [nativeArgument, g.coordinates_eq_affine k w.1.2, nativeLinear_apply]
  ext <;> simp

theorem sourceArgument_affine (g : CCS) (k : Frequency) (w : Joint P) :
    sourceArgument g k w = sourceArgument g k 0 + sourceLinear P g w := by
  have ha : ((g.coordinates k w.1.2).1, w.2) =
      ((g.coordinates k 0).1, 0) + ((g.coordinateLinear w.1.2).1, w.2) := by
    rw [g.coordinates_eq_affine k w.1.2]
    ext <;> simp
  simp only [sourceArgument, CommonCoverSolve.Geometry.path, ha, g.point_add,
    sourceLinear_apply, CommonCoverSolve.Geometry.pointLinear,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  ext <;> simp

theorem nativeArgument_smooth (g : CCS) (k : Frequency) :
    ContDiff ℝ ∞ (nativeArgument (P := P) g k) := by
  have he : nativeArgument (P := P) g k =
      fun w => nativeArgument g k 0 + nativeLinear P g w :=
    funext (nativeArgument_affine g k)
  rw [he]
  exact contDiff_const.add (nativeLinear P g).contDiff

theorem sourceArgument_smooth (g : CCS) (k : Frequency) :
    ContDiff ℝ ∞ (sourceArgument (P := P) g k) := by
  have he : sourceArgument (P := P) g k =
      fun w => sourceArgument g k 0 + sourceLinear P g w :=
    funext (sourceArgument_affine g k)
  rw [he]
  exact contDiff_const.add (sourceLinear P g).contDiff

/-- One common affine cost for both maps. Its value is independent of the
copy index and of the slow parameter space. -/
noncomputable def argumentCost (g : CCS) : ℝ :=
  1 + ‖g.coordinateLinear‖ + ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖)

theorem one_le_argumentCost (g : CCS) : 1 ≤ argumentCost g := by
  unfold argumentCost
  have h : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
  linarith [norm_nonneg g.coordinateLinear]

theorem norm_nativeLinear_le (g : CCS) : ‖nativeLinear P g‖ ≤ argumentCost g := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (one_le_argumentCost g))
  intro w
  rw [nativeLinear_apply, Prod.norm_def, Prod.norm_def]
  have hcoord : ‖(g.coordinateLinear w.1.2).1‖ ≤ ‖g.coordinateLinear‖ * ‖w‖ :=
    (norm_fst_le _).trans ((g.coordinateLinear.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((norm_snd_le w.1).trans (norm_fst_le w)) (norm_nonneg _)))
  have hc : ‖g.coordinateLinear‖ ≤ argumentCost g := by
    unfold argumentCost
    have h : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
    linarith
  have h1 : ‖w‖ ≤ argumentCost g * ‖w‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (one_le_argumentCost g)
  exact max_le ((norm_fst_le w.1).trans ((norm_fst_le w).trans h1))
    (max_le (hcoord.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _)))
      ((norm_snd_le w).trans h1))

theorem norm_sourceLinear_le (g : CCS) : ‖sourceLinear P g‖ ≤ argumentCost g := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (one_le_argumentCost g))
  intro w
  rw [sourceLinear_apply, Prod.norm_def]
  have hcoord : ‖(g.coordinateLinear w.1.2).1‖ ≤ ‖g.coordinateLinear‖ * ‖w‖ :=
    (norm_fst_le _).trans ((g.coordinateLinear.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((norm_snd_le w.1).trans (norm_fst_le w)) (norm_nonneg _)))
  have hpair : ‖((g.coordinateLinear w.1.2).1, w.2)‖ ≤
      (1 + ‖g.coordinateLinear‖) * ‖w‖ := by
    rw [Prod.norm_def]
    apply max_le
    · exact hcoord.trans (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg g.coordinateLinear])
        (norm_nonneg _))
    · exact (norm_snd_le w).trans
        (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg g.coordinateLinear]))
  have h1 : ‖w‖ ≤ argumentCost g * ‖w‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (one_le_argumentCost g)
  apply max_le ((norm_fst_le w.1).trans ((norm_fst_le w).trans h1))
  calc
    _ ≤ ‖g.pointLinear‖ * ‖((g.coordinateLinear w.1.2).1, w.2)‖ := g.pointLinear.le_opNorm _
    _ ≤ ‖g.pointLinear‖ * ((1 + ‖g.coordinateLinear‖) * ‖w‖) :=
      mul_le_mul_of_nonneg_left hpair (norm_nonneg _)
    _ ≤ argumentCost g * ‖w‖ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      unfold argumentCost
      linarith [norm_nonneg g.coordinateLinear]

theorem nativeArgument_jet_bound (g : CCS) (k : Frequency) {f : P × Plane → V}
    (hf : ContDiff ℝ ∞ f) (m : ℕ) (w : Joint P) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (nativeArgument g k w)‖ ≤ A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun z => f (nativeArgument g k z)) w‖ ≤
      A * argumentCost g ^ m := by
  have he : (fun z => f (nativeArgument g k z)) =
      fun z => f (nativeArgument g k 0 + nativeLinear P g z) := by
    funext z; rw [nativeArgument_affine]
  rw [he]
  apply affine_jet_bound hf _ _ (one_le_argumentCost g) (norm_nativeLinear_le g) m w
  simpa only [← nativeArgument_affine] using hb

theorem sourceArgument_jet_bound (g : CCS) (k : Frequency) {f : P × Plane → V}
    (hf : ContDiff ℝ ∞ f) (m : ℕ) (w : Joint P) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (sourceArgument g k w)‖ ≤ A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun z => f (sourceArgument g k z)) w‖ ≤
      A * argumentCost g ^ m := by
  have he : (fun z => f (sourceArgument g k z)) =
      fun z => f (sourceArgument g k 0 + sourceLinear P g z) := by
    funext z; rw [sourceArgument_affine]
  rw [he]
  apply affine_jet_bound hf _ _ (one_le_argumentCost g) (norm_sourceLinear_le g) m w
  simpa only [← sourceArgument_affine] using hb

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] theorem sourceArgument_slow (g : CCS) (k : Frequency) (w : Joint P) :
    (sourceArgument g k w).1 = w.1.1 := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] theorem nativeArgument_slow (g : CCS) (k : Frequency) (w : Joint P) :
    (nativeArgument g k w).1 = w.1.1 := rfl

end Arguments

section BandGeometry

/-- The fixed native basis has columns `v_r,v_t`; only the second column is
multiplied by the actual time coefficient. -/
noncomputable def scaledBasis (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) :
    Plane ≃L[ℝ] Plane := (TorusAverages.transverseChart ci hci).trans B

theorem scaledBasis_apply (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) (z : Plane) :
    scaledBasis B ci hci z = B (z.1, ci * z.2) := by
  change B (TorusAverages.transverseChart ci hci z) = _
  rw [TorusAverages.transverseChart_apply]

theorem scaledBasis_transverse (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) :
    scaledBasis B ci hci (0, 1) = ci • B (0, 1) := by
  rw [scaledBasis_apply, ← map_smul]
  congr 1
  ext <;> simp

theorem norm_transverseChart_le {ci : ℝ} (hci : ci ≠ 0) (habs : |ci| ≤ 1) :
    ‖(TorusAverages.transverseChart ci hci : Plane →L[ℝ] Plane)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [ContinuousLinearEquiv.coe_coe, TorusAverages.transverseChart_apply, one_mul, Prod.norm_def]
  apply max_le (norm_fst_le z)
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right habs (norm_nonneg z.2)).trans (by simpa using norm_snd_le z)

theorem norm_inverse_transverseChart_le (ci : ℝ) (hci : ci ≠ 0) :
    ‖((TorusAverages.transverseChart ci hci).symm : Plane →L[ℝ] Plane)‖ ≤ 1 + |ci⁻¹| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [ContinuousLinearEquiv.coe_coe, TorusAverages.transverseChart_symm_apply, Prod.norm_def]
  apply max_le
  · exact (norm_fst_le z).trans
      (le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg (ci⁻¹)]))
  · rw [div_eq_mul_inv, norm_mul, Real.norm_eq_abs (ci⁻¹), mul_comm]
    exact (mul_le_mul_of_nonneg_left (norm_snd_le z) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith : |ci⁻¹| ≤ 1 + |ci⁻¹|) (norm_nonneg _))

theorem norm_scaledBasis_le (B : Plane ≃L[ℝ] Plane) {ci : ℝ}
    (hci : ci ≠ 0) (habs : |ci| ≤ 1) :
    ‖(scaledBasis B ci hci : Plane →L[ℝ] Plane)‖ ≤ ‖(B : Plane →L[ℝ] Plane)‖ := by
  change ‖(B : Plane →L[ℝ] Plane).comp
    (TorusAverages.transverseChart ci hci : Plane →L[ℝ] Plane)‖ ≤ _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left (norm_transverseChart_le hci habs) (norm_nonneg
      B.toContinuousLinearMap))

theorem norm_inverse_scaledBasis_le (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) :
    ‖((scaledBasis B ci hci).symm : Plane →L[ℝ] Plane)‖ ≤
      (1 + |ci⁻¹|) * ‖(B.symm : Plane →L[ℝ] Plane)‖ := by
  change ‖((TorusAverages.transverseChart ci hci).symm : Plane →L[ℝ] Plane).comp
    (B.symm : Plane →L[ℝ] Plane)‖ ≤ _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_inverse_transverseChart_le ci hci) (norm_nonneg _))

noncomputable def bandGeometry (B : Plane ≃L[ℝ] Plane) (h : ℝ) (n gap : ℕ)
    (center : Plane) : CCS where
  gap := gap
  basis := scaledBasis B (ChartScales.timeCoefficient h n) (ChartScales.timeCoefficient_pos h n).ne'
  center := center

theorem bandGeometry_path (B : Plane ≃L[ℝ] Plane) (h : ℝ) (n gap : ℕ)
    (center : Plane) (k : Frequency) (Y : Plane) (s : ℝ) :
    (bandGeometry B h n gap center).path k Y s =
      Y + (CommonCoverSolve.coverPower gap).symm
        ((ChartScales.timeCoefficient h n *
          (s - ((bandGeometry B h n gap center).coordinates k Y).2)) • B (0, 1)) := by
  rw [CommonCoverSolve.Geometry.path_eq_shift]
  change Y + (CommonCoverSolve.coverPower gap).symm
    ((s - _) • scaledBasis B _ _ (0, 1)) = _
  rw [scaledBasis_transverse, smul_smul, mul_comm]

noncomputable def geometryCost (B : Plane ≃L[ℝ] Plane) (D : ℕ) : ℝ :=
  1 + CommonCoverSolve.coveringBound D * ‖(B : Plane →L[ℝ] Plane)‖ +
    (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ * CommonCoverSolve.coveringBound D

theorem geometryCost_one_le (B : Plane ≃L[ℝ] Plane) (D : ℕ) : 1 ≤ geometryCost B D := by
  have h1 : 0 ≤ CommonCoverSolve.coveringBound D * ‖(B : Plane →L[ℝ] Plane)‖ :=
    mul_nonneg (CommonCoverSolve.coveringBound_pos D).le (norm_nonneg _)
  have h2 : 0 ≤ (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
      CommonCoverSolve.coveringBound D := by
    exact mul_nonneg (mul_nonneg (by linarith [ChartScales.Tg_pos]) (norm_nonneg _))
      (CommonCoverSolve.coveringBound_pos D).le
  unfold geometryCost
  linarith

/-- This constant depends on the fixed native basis and the covering-gap
budget, and is chosen before the band, center, copy, or source. -/
noncomputable def bandArgumentCost (B : Plane ≃L[ℝ] Plane) (D : ℕ) : ℝ :=
  (1 + geometryCost B D) ^ 2

theorem bandArgumentCost_one_le (B : Plane ≃L[ℝ] Plane) (D : ℕ) : 1 ≤ bandArgumentCost B D := by
  have h := geometryCost_one_le B D
  unfold bandArgumentCost
  nlinarith

theorem bandGeometry_argumentCost_le (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) :
    argumentCost (bandGeometry B h n gap center) ≤ bandArgumentCost B D * ChartScales.S n := by
  let g := bandGeometry B h n gap center
  have hS : 1 ≤ ChartScales.S n := PhysicalGraphBounds.S_ge_one (by omega)
  have hS0 : 0 < ChartScales.S n := zero_lt_one.trans_le hS
  have hci : |ChartScales.timeCoefficient h n| ≤ 1 := by
    rw [abs_of_pos (ChartScales.timeCoefficient_pos h n)]
    exact (ChartScales.timeCoefficient_bounds h hh hn).2.trans
      ((div_le_one hS0).mpr hS)
  have hinv : 1 + |(ChartScales.timeCoefficient h n)⁻¹| ≤
      (1 + ChartScales.Tg) * ChartScales.S n := by
    rw [abs_of_pos (inv_pos.mpr (ChartScales.timeCoefficient_pos h n))]
    have hb := ChartScales.timeCoefficient_inv_upper h hh hn
    nlinarith
  have hb : ‖(g.basis : Plane →L[ℝ] Plane)‖ ≤ ‖(B : Plane →L[ℝ] Plane)‖ :=
    norm_scaledBasis_le B _ hci
  have hbi : ‖(g.basis.symm : Plane →L[ℝ] Plane)‖ ≤
      ((1 + ChartScales.Tg) * ChartScales.S n) * ‖(B.symm : Plane →L[ℝ] Plane)‖ :=
    (norm_inverse_scaledBasis_le B _ _).trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have hC0 : 0 ≤ CommonCoverSolve.coveringBound D := (CommonCoverSolve.coveringBound_pos D).le
  have hK : 1 ≤ geometryCost B D := geometryCost_one_le B D
  have hK0 : 0 ≤ geometryCost B D := zero_le_one.trans hK
  have hcoeff : (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
      CommonCoverSolve.coveringBound D ≤ geometryCost B D := by
    unfold geometryCost
    linarith [mul_nonneg hC0 (norm_nonneg (B : Plane →L[ℝ] Plane))]
  have hpoint : ‖g.pointLinear‖ ≤ geometryCost B D := by
    refine (g.norm_pointLinear_le hd).trans ?_
    refine (mul_le_mul_of_nonneg_left hb hC0).trans ?_
    unfold geometryCost
    have ht : 0 ≤ (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
        CommonCoverSolve.coveringBound D := by
      exact mul_nonneg (mul_nonneg (by linarith [ChartScales.Tg_pos]) (norm_nonneg _)) hC0
    linarith
  have hcoord : ‖g.coordinateLinear‖ ≤ geometryCost B D * ChartScales.S n := by
    refine (g.norm_coordinateLinear_le hd).trans ?_
    calc
      _ ≤ (((1 + ChartScales.Tg) * ChartScales.S n) * ‖(B.symm : Plane →L[ℝ] Plane)‖) *
          CommonCoverSolve.coveringBound D := mul_le_mul_of_nonneg_right hbi hC0
      _ = ((1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
          CommonCoverSolve.coveringBound D) * ChartScales.S n := by ring
      _ ≤ geometryCost B D * ChartScales.S n := mul_le_mul_of_nonneg_right hcoeff hS0.le
  change 1 + ‖g.coordinateLinear‖ + ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) ≤ _
  calc
    _ ≤ 1 + geometryCost B D * ChartScales.S n +
        geometryCost B D * (1 + geometryCost B D * ChartScales.S n) := by
      exact add_le_add (add_le_add_right hcoord _) (mul_le_mul hpoint (add_le_add_right hcoord _)
        (by positivity) hK0)
    _ ≤ bandArgumentCost B D * ChartScales.S n := by
      unfold bandArgumentCost
      nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hS)]

end BandGeometry

section CurrentEvaluation

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reinsert the actual current slot time after solving the joint equation. -/
noncomputable def currentArgument (g : CCS) (k : Frequency) (p : P × Plane) : Joint P :=
  (p, (g.coordinates k p.2).2)

noncomputable def currentLinear (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : CCS) : P × Plane →L[ℝ] Joint P :=
  (ContinuousLinearMap.id ℝ (P × Plane)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P Plane)))

@[simp] theorem currentLinear_apply (g : CCS) (p : P × Plane) :
    currentLinear P g p = (p, (g.coordinateLinear p.2).2) := rfl

theorem currentArgument_affine (g : CCS) (k : Frequency) (p : P × Plane) :
    currentArgument g k p = currentArgument g k 0 + currentLinear P g p := by
  simp only [currentArgument, g.coordinates_eq_affine k p.2, currentLinear_apply]
  ext <;> simp

theorem currentArgument_smooth (g : CCS) (k : Frequency) :
    ContDiff ℝ ∞ (currentArgument (P := P) g k) := by
  have he : currentArgument (P := P) g k =
      fun p => currentArgument g k 0 + currentLinear P g p :=
    funext (currentArgument_affine g k)
  rw [he]
  exact contDiff_const.add (currentLinear P g).contDiff

theorem norm_currentLinear_le (g : CCS) : ‖currentLinear P g‖ ≤ argumentCost g := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (one_le_argumentCost g))
  intro p
  rw [currentLinear_apply, Prod.norm_def]
  refine max_le (le_mul_of_one_le_left (norm_nonneg _) (one_le_argumentCost g)) ?_
  have hc : ‖g.coordinateLinear‖ ≤ argumentCost g := by
    unfold argumentCost
    have hp : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
    linarith
  exact (norm_snd_le (g.coordinateLinear p.2)).trans ((g.coordinateLinear.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_snd_le p) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _))))

theorem currentArgument_jet_bound (g : CCS) (k : Frequency) {f : Joint P → V}
    (hf : ContDiff ℝ ∞ f) (m : ℕ) (p : P × Plane) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (currentArgument g k p)‖ ≤ A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun q => f (currentArgument g k q)) p‖ ≤
      A * argumentCost g ^ m := by
  have he : (fun q => f (currentArgument g k q)) =
      fun q => f (currentArgument g k 0 + currentLinear P g q) := by
    funext q; rw [currentArgument_affine]
  rw [he]
  apply affine_jet_bound hf _ _ (one_le_argumentCost g) (norm_currentLinear_le g) m p
  simpa only [← currentArgument_affine] using hb

end CurrentEvaluation

section BandInputs

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nativeArgument_band_jet_bound (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) (k : Frequency)
    {f : P × Plane → V} (hf : ContDiff ℝ ∞ f) (m : ℕ) (w : Joint P) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (nativeArgument (bandGeometry B h n gap center) k w)‖ ≤ A)
      :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j
      (fun z => f (nativeArgument (bandGeometry B h n gap center) k z)) w‖ ≤
        A * (bandArgumentCost B D * ChartScales.S n) ^ m := by
  intro j hj
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  exact (nativeArgument_jet_bound _ k hf m w hb j hj).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (one_le_argumentCost _))
      (bandGeometry_argumentCost_le B hh hn hd center) m) hA)

theorem sourceArgument_band_jet_bound (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) (k : Frequency)
    {f : P × Plane → V} (hf : ContDiff ℝ ∞ f) (m : ℕ) (w : Joint P) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (sourceArgument (bandGeometry B h n gap center) k w)‖ ≤ A)
      :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j
      (fun z => f (sourceArgument (bandGeometry B h n gap center) k z)) w‖ ≤
        A * (bandArgumentCost B D * ChartScales.S n) ^ m := by
  intro j hj
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  exact (sourceArgument_jet_bound _ k hf m w hb j hj).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (one_le_argumentCost _))
      (bandGeometry_argumentCost_le B hh hn hd center) m) hA)

theorem currentArgument_band_jet_bound (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) (k : Frequency)
    {f : Joint P → V} (hf : ContDiff ℝ ∞ f) (m : ℕ) (p : P × Plane) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (currentArgument (bandGeometry B h n gap center) k p)‖ ≤
      A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j
      (fun q => f (currentArgument (bandGeometry B h n gap center) k q)) p‖ ≤
        A * (bandArgumentCost B D * ChartScales.S n) ^ m := by
  intro j hj
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  exact (currentArgument_jet_bound _ k hf m p hb j hj).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (one_le_argumentCost _))
      (bandGeometry_argumentCost_le B hh hn hd center) m) hA)

theorem sourceArgument_envelope (g : CCS) (k : Frequency) {f : P × Plane → V}
    (hf : ContDiff ℝ ∞ f) {m : ℕ} {e : P × Plane → ℝ} (hb : EnvelopeJets m f e) :
    EnvelopeJets m (fun z => f (sourceArgument g k z))
      (fun z => e (sourceArgument g k z) * argumentCost g ^ m) :=
  fun j hj z => sourceArgument_jet_bound g k hf m z (fun i hi => hb i hi _) j hj

theorem nativeArgument_envelope (g : CCS) (k : Frequency) {f : P × Plane → V}
    (hf : ContDiff ℝ ∞ f) {m : ℕ} {e : P × Plane → ℝ} (hb : EnvelopeJets m f e) :
    EnvelopeJets m (fun z => f (nativeArgument g k z))
      (fun z => e (nativeArgument g k z) * argumentCost g ^ m) :=
  fun j hj z => nativeArgument_jet_bound g k hf m z (fun i hi => hb i hi _) j hj

/-- This is a bound on all joint input jets of the actual ODE coefficient. -/
theorem coefficientAlong_band_jet_bound (d : CommonCoverSolve.LinearData P V E)
    (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) (k : Frequency)
    (hf : ContDiff ℝ ∞ d.coefficient) (m : ℕ) (w : Joint P) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j d.coefficient
      (nativeArgument (bandGeometry B h n gap center) k w)‖ ≤ A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j
      (d.coefficientAlong (bandGeometry B h n gap center) k) w‖ ≤
        A * (bandArgumentCost B D * ChartScales.S n) ^ m :=
  nativeArgument_band_jet_bound B hh hn hd center k hf m w hb

/-- Both factors are evaluated at their correct, generally different,
arguments. In particular the source is not replaced by a native-periodic one. -/
theorem forcingAlong_band_jet_bound (d : CommonCoverSolve.LinearData P V E)
    (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) (k : Frequency)
    (hB : ContDiff ℝ ∞ d.forcingMap) (hf : ContDiff ℝ ∞ d.source)
    (m : ℕ) (w : Joint P) {A C : ℝ}
    (hA : ∀ j ≤ m, ‖iteratedFDeriv ℝ j d.forcingMap
      (nativeArgument (bandGeometry B h n gap center) k w)‖ ≤ A)
    (hC : ∀ j ≤ m, ‖iteratedFDeriv ℝ j d.source
      (sourceArgument (bandGeometry B h n gap center) k w)‖ ≤ C) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j
      (d.forcingAlong (bandGeometry B h n gap center) k) w‖ ≤
        2 ^ m * A * C * bandArgumentCost B D ^ (2 * m) * ChartScales.S n ^ (2 * m) := by
  intro j hj
  have hb := clm_apply_jet_bound
    (hB.comp (nativeArgument_smooth (bandGeometry B h n gap center) k))
    (hf.comp (sourceArgument_smooth (bandGeometry B h n gap center) k)) m w
    (nativeArgument_band_jet_bound B hh hn hd center k hB m w hA)
    (sourceArgument_band_jet_bound B hh hn hd center k hf m w hC) j hj
  convert! hb using 1
  simp only [mul_pow, two_mul, pow_add]
  ring

/-- Every radial and slow weight is unchanged by the source path. For each
requested jet prefix the only change is a fixed additional power of `S`.
This also applies with `weight = sqrt(zeta) * P` whenever `P` depends only
on the retained slow parameters. -/
theorem sourceArgument_band_stripped_bound (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) (k : Frequency)
    {f : P × Plane → V} (hf : ContDiff ℝ ∞ f) (m p q : ℕ)
    (A α : ℝ) (edge weight : P → ℝ)
    (hb : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤
      A * ChartScales.epsilon h n ^ α * ChartScales.S n ^ p * edge z.1 ^ q * weight z.1) :
    ∀ j ≤ m, ∀ w : Joint P, ‖iteratedFDeriv ℝ j
      (fun z => f (sourceArgument (bandGeometry B h n gap center) k z)) w‖ ≤
        (A * bandArgumentCost B D ^ m) * ChartScales.epsilon h n ^ α *
          ChartScales.S n ^ (p + m) * edge w.1.1 ^ q * weight w.1.1 := by
  intro j hj w
  have ha := sourceArgument_band_jet_bound B hh hn hd center k hf m w
    (fun i hi => hb i hi (sourceArgument (bandGeometry B h n gap center) k w)) j hj
  convert! ha using 1
  simp only [sourceArgument_slow, mul_pow, pow_add]
  ring

end BandInputs

section DyadicChanges

/-- The exact ratio `(Q_n / Q_m)^a`, written without a division. -/
noncomputable def bandRatio (a : ℝ) (n m : ℕ) : ℝ :=
  (2 : ℝ) ^ (((m : ℝ) - (n : ℝ)) * a)

theorem bandRatio_pos (a : ℝ) (n m : ℕ) : 0 < bandRatio a n m :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem bandRatio_eq_rpow (a : ℝ) (n m : ℕ) :
    bandRatio a n m = (ChartScales.Q n / ChartScales.Q m) ^ a := by
  rw [Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
  unfold bandRatio ChartScales.Q SlotColoring.dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem bandRatio_mul_scale (a : ℝ) (n m : ℕ) :
    bandRatio a n m * ChartScales.Q n ^ (-a) = ChartScales.Q m ^ (-a) := by
  rw [bandRatio_eq_rpow, Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
  calc
    _ = (ChartScales.Q n ^ a * ChartScales.Q n ^ (-a)) / ChartScales.Q m ^ a := by ring
    _ = (ChartScales.Q m ^ a)⁻¹ := by
      rw [← Real.rpow_add (ChartScales.Q_pos n)]
      simp
    _ = ChartScales.Q m ^ (-a) := (Real.rpow_neg (ChartScales.Q_pos m).le a).symm

theorem bandRatio_mul_power (a : ℝ) (n m : ℕ) :
    bandRatio a n m * ChartScales.Q m ^ a = ChartScales.Q n ^ a := by
  rw [bandRatio_eq_rpow, Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos (ChartScales.Q_pos m) a).ne'

theorem bandRatio_le (a : ℝ) {n m : ℕ} (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    bandRatio a n m ≤ (2 : ℝ) ^ (4 * |a|) := by
  have hdiff : |(m : ℝ) - (n : ℝ)| ≤ 4 := by
    have h1 : (n : ℝ) ≤ (m : ℝ) + 4 := by exact_mod_cast hnm
    have h2 : (m : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hmn
    rw [abs_le]
    constructor <;> linarith
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    ((m : ℝ) - (n : ℝ)) * a ≤ |((m : ℝ) - (n : ℝ)) * a| := le_abs_self _
    _ = |(m : ℝ) - (n : ℝ)| * |a| := abs_mul _ _
    _ ≤ 4 * |a| := mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)

/-- Transfer of the actual small-scale factor across overlapping bands.
The exponent is identical on both sides. -/
theorem epsilon_power_transfer (h α : ℝ) {n m : ℕ}
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    ChartScales.epsilon h n ^ α ≤
      (2 : ℝ) ^ (4 * |h * α|) * ChartScales.epsilon h m ^ α := by
  unfold ChartScales.epsilon
  rw [← Real.rpow_mul (ChartScales.Q_pos n).le, ← Real.rpow_mul (ChartScales.Q_pos m).le]
  rw [← bandRatio_mul_power (h * α) n m]
  exact mul_le_mul_of_nonneg_right (bandRatio_le (h * α) hnm hmn)
    (Real.rpow_pos_of_pos (ChartScales.Q_pos m) (h * α)).le

theorem slow_scale_transfer {n m : ℕ} (hm : 1 ≤ m) (hnm : n ≤ m + 4) :
    ChartScales.S n ≤ 25 * ChartScales.S m := by
  have h : (n : ℝ) ≤ 5 * (m : ℝ) := by exact_mod_cast (show n ≤ 5 * m by omega)
  have hs := mul_self_le_mul_self (Nat.cast_nonneg n) h
  unfold ChartScales.S
  nlinarith

theorem slow_power_transfer {n m : ℕ} (hm : 1 ≤ m) (hnm : n ≤ m + 4) (p : ℕ) :
    ChartScales.S n ^ p ≤ 25 ^ p * ChartScales.S m ^ p := by
  simpa only [mul_pow, ChartScales.S] using pow_le_pow_left₀ (sq_nonneg (n : ℝ))
    (slow_scale_transfer hm hnm) p

abbrev SlowPoint := ℝ × (ℝ × ℝ)

/-- Actual `(R,Z,T)` chart change from band `n` to band `m`. -/
noncomputable def bandChart (D : ℝ) (n m : ℕ) : SlowPoint →L[ℝ] SlowPoint :=
  (bandRatio (1 / 2) n m • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    ((bandRatio D n m • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))).prod
      (bandRatio 1 n m • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))

@[simp] theorem bandChart_apply (D : ℝ) (n m : ℕ) (x : SlowPoint) :
    bandChart D n m x = (bandRatio (1 / 2) n m * x.1,
      (bandRatio D n m * x.2.1, bandRatio 1 n m * x.2.2)) := rfl

theorem bandChart_formula (D : ℝ) (n m : ℕ) (x : SlowPoint) :
    bandChart D n m x = ((ChartScales.Q n / ChartScales.Q m) ^ (1 / 2 : ℝ) * x.1,
      ((ChartScales.Q n / ChartScales.Q m) ^ D * x.2.1,
        (ChartScales.Q n / ChartScales.Q m) * x.2.2)) := by
  simp only [bandChart_apply, bandRatio_eq_rpow, Real.rpow_one]

noncomputable def normalizedSlowChart (D : ℝ) (n : ℕ) (x : SlowPoint) : SlowPoint :=
  (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * x.1,
    (ChartScales.Q n ^ (-D) * x.2.1, ChartScales.Q n ^ (-1 : ℝ) * x.2.2))

theorem bandChart_normalizedSlowChart (D : ℝ) (n m : ℕ) (x : SlowPoint) :
    bandChart D n m (normalizedSlowChart D n x) = normalizedSlowChart D m x := by
  simp only [bandChart_apply, normalizedSlowChart, ← mul_assoc, bandRatio_mul_scale]

noncomputable def chartCost (D : ℝ) : ℝ := 1 + (2 : ℝ) ^ (4 * (1 + |D|))

theorem chartCost_one_le (D : ℝ) : 1 ≤ chartCost D := by
  unfold chartCost
  linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (4 * (1 + |D|))]

theorem bandRatio_le_chartCost {D a : ℝ} (ha : |a| ≤ 1 + |D|) {n m : ℕ}
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) : bandRatio a n m ≤ chartCost D := by
  refine (bandRatio_le a hnm hmn).trans ?_
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left ha (by
    norm_num))).trans ?_
  unfold chartCost
  linarith

theorem norm_bandChart_le (D : ℝ) {n m : ℕ} (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    ‖bandChart D n m‖ ≤ chartCost D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (chartCost_one_le D))
  intro x
  have hb (a y : ℝ) (ha : |a| ≤ 1 + |D|) (hy : ‖y‖ ≤ ‖x‖) :
      ‖bandRatio a n m * y‖ ≤ chartCost D * ‖x‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (bandRatio_pos _ _ _)]
    exact mul_le_mul (bandRatio_le_chartCost ha hnm hmn) hy (norm_nonneg _)
      (zero_le_one.trans (chartCost_one_le D))
  rw [bandChart_apply, Prod.norm_def, Prod.norm_def]
  apply max_le
  · exact hb (1 / 2) x.1 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith [abs_nonneg
    D])
      (norm_fst_le x)
  · apply max_le
    · exact hb D x.2.1 (by linarith) ((norm_fst_le x.2).trans (norm_snd_le x))
    · exact hb 1 x.2.2 (by rw [abs_one]; linarith [abs_nonneg D])
        ((norm_snd_le x.2).trans (norm_snd_le x))

theorem bandChart_jet_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SlowPoint → V} (hf : ContDiff ℝ ∞ f) (D : ℝ) {n m : ℕ}
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) (r : ℕ) (x : SlowPoint) {A : ℝ}
    (hb : ∀ j ≤ r, ‖iteratedFDeriv ℝ j f (bandChart D n m x)‖ ≤ A) :
    ∀ j ≤ r, ‖iteratedFDeriv ℝ j (fun y => f (bandChart D n m y)) x‖ ≤ A * chartCost D ^ r := by
  simpa only [zero_add] using affine_jet_bound hf (bandChart D n m) 0
    (chartCost_one_le D) (norm_bandChart_le D hnm hmn) r x (by simpa only [zero_add] using hb)

/-- Coarsest of a pair of simultaneously active levels. -/
noncomputable def commonIndex (h : ℝ) (n m : ℕ) : ℕ := min (ChartScales.nativeIndex h n)
  (ChartScales.nativeIndex h m)

theorem commonIndex_gap_le (h : ℝ) (hh : 0 ≤ h) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    ChartScales.nativeIndex h n - commonIndex h n m ≤ SlotColoring.nativeGap h ∧
      ChartScales.nativeIndex h m - commonIndex h n m ≤ SlotColoring.nativeGap h := by
  have hg := SlotColoring.nativeIndex_gap h hh hn hm hnm hmn
  simp only [commonIndex, ChartScales.nativeIndex]
  omega

theorem adjacent_commonIndex_gap_le (h : ℝ) (hh : 0 ≤ h) {D : ℝ}
    {L M : SlotColoring.Label} (hadj : SlotColoring.Adj D L M) :
    ChartScales.nativeIndex h L.1 - commonIndex h L.1 M.1 ≤ SlotColoring.nativeGap h ∧
      ChartScales.nativeIndex h M.1 - commonIndex h L.1 M.1 ≤ SlotColoring.nativeGap h :=
  commonIndex_gap_le h hh hadj.left_positive hadj.right_positive hadj.left_level_le
    hadj.right_level_le

end DyadicChanges

section ClassTransport

variable {X Y V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_affine_jet_le_on {f : Y → V} {U : Set Y} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (L : X →L[ℝ] Y) (c : Y) {x : X}
    (hx : c + L x ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z => f (c + L z)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (c + L x)‖ * ‖L‖ ^ j := by
  have hU' : IsOpen ((fun y : Y => c + y) ⁻¹' U) :=
    hU.preimage (continuous_const.add continuous_id)
  have hf' : ContDiffOn ℝ ∞ (fun y => f (c + y)) ((fun y : Y => c + y) ⁻¹' U) :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hy => hy)
  have hb := PhysicalGraphBounds.norm_jet_comp_linear hU' hf' L hx j
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_left] using hb

/-- All hypotheses other than the source class concern the actual affine
maps and the prescribed weights/scales. No derivative bound on the
pulled-back source is a premise. Polynomial map and edge costs do not change
the small-scale exponent. -/
theorem memClass_affine_transport
    (s : WeightedClasses.StripData Y) (t : WeightedClasses.StripData X)
    {w : ℕ → Y → ℝ} {v : ℕ → X → ℝ} {α : ℝ} {f : ℕ → Y → V}
    (hf : WeightedClasses.MemClass s w α f)
    (index : ℕ → ℕ) (L : ℕ → X →L[ℝ] Y) (c : ℕ → Y)
    (hmap : ∀ n x, x ∈ t.domain → c n + L n x ∈ s.domain)
    (hweight : ∀ n x, x ∈ t.domain → w (index n) (c n + L n x) = v n x)
    {Ce Cg CL : ℝ} (hCe : 0 ≤ Ce) (hCg : 1 ≤ Cg) (hCL : 1 ≤ CL) (r l : ℕ)
    (heps : ∀ n, s.epsilon (index n) ^ α ≤ Ce * t.epsilon n ^ α)
    (hgrowth : ∀ n x, x ∈ t.domain →
      s.growth (index n) (c n + L n x) ≤ Cg * t.growth n x ^ r)
    (hlinear : ∀ n x, x ∈ t.domain → ‖L n‖ ≤ CL * t.growth n x ^ l) :
    WeightedClasses.MemClass t v α (fun n x => f (index n) (c n + L n x)) := by
  have hv : ∀ n x, x ∈ t.domain → 0 ≤ v n x := by
    intro n x hx
    rw [← hweight n x hx]
    exact hf.weight_nonneg _ _ (hmap n x hx)
  refine ⟨hv, ?_, ?_⟩
  · intro n
    exact (hf.smooth (index n)).comp
      (contDiff_const.add (L n).contDiff).contDiffOn (hmap n)
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hf.bounds m
    refine ⟨A * Ce * Cg ^ p * CL ^ m, by positivity, r * p + l * m, ?_⟩
    intro n x hx j hj
    have htarget := t.growth_nonneg n x
    have hsource := s.growth_nonneg (index n) (c n + L n x)
    have hCL0 : 0 ≤ CL := zero_le_one.trans hCL
    have hCg0 : 0 ≤ Cg := zero_le_one.trans hCg
    have hpow : ‖L n‖ ^ j ≤ CL ^ m * t.growth n x ^ (l * m) := by
      calc
        _ ≤ (CL * t.growth n x ^ l) ^ j := pow_le_pow_left₀ (norm_nonneg _) (hlinear n x hx) j
        _ ≤ (CL * t.growth n x ^ l) ^ m :=
          pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hCL
            (one_le_pow₀ (t.one_le_growth n x))) hj
        _ = _ := by rw [mul_pow, ← pow_mul]
    have hgpow : s.growth (index n) (c n + L n x) ^ p ≤
        Cg ^ p * t.growth n x ^ (r * p) := by
      simpa only [mul_pow, ← pow_mul] using
        pow_le_pow_left₀ hsource (hgrowth n x hx) p
    have hstart := norm_affine_jet_le_on s.isOpen_domain (hf.smooth (index n))
      (L n) (c n) (hmap n x hx) j
    refine hstart.trans ?_
    calc
      _ ≤ WeightedClasses.majorant s w α A p (index n) (c n + L n x) * ‖L n‖ ^ j :=
        mul_le_mul_of_nonneg_right (hb _ _ (hmap n x hx) j hj) (pow_nonneg (norm_nonneg _) _)
      _ = (A * s.epsilon (index n) ^ α * s.growth (index n) (c n + L n x) ^ p * v n x) *
          ‖L n‖ ^ j := by rw [WeightedClasses.majorant, hweight n x hx]
      _ ≤ (A * (Ce * t.epsilon n ^ α) * (Cg ^ p * t.growth n x ^ (r * p)) * v n x) *
          (CL ^ m * t.growth n x ^ (l * m)) := by
        have hv0 := hv n x hx
        have htε : 0 ≤ t.epsilon n ^ α := (Real.rpow_pos_of_pos (t.epsilon_pos n) α).le
        gcongr
        exact heps n
      _ = WeightedClasses.majorant t v α (A * Ce * Cg ^ p * CL ^ m)
          (r * p + l * m) n x := by
        unfold WeightedClasses.majorant
        rw [pow_add]
        ring

/-- A strip over a linear parameter projection. Its weights are the actual
base weights, so retaining the parameter preserves them exactly. -/
noncomputable def parameterStrip (s : WeightedClasses.StripData Y) (L : X →L[ℝ] Y) :
    WeightedClasses.StripData X where
  domain := L ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage L.continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta x := s.delta (L x)
  delta_pos _ hx := s.delta_pos _ hx
  zeta x := s.zeta (L x)
  zeta_smooth := s.zeta_smooth.comp L.contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg _ hx := s.zeta_nonneg _ hx

@[simp] theorem parameterStrip_growth (s : WeightedClasses.StripData Y) (L : X →L[ℝ] Y)
    (n : ℕ) (x : X) : (parameterStrip s L).growth n x = s.growth n (L x) := rfl

end ClassTransport

section SourceClasses

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def sourceStrip (s : WeightedClasses.StripData P) : WeightedClasses.StripData (P ×
  Plane) :=
  parameterStrip s (ContinuousLinearMap.fst ℝ P Plane)

noncomputable def jointStrip (s : WeightedClasses.StripData P) : WeightedClasses.StripData (Joint
  P) :=
  parameterStrip s ((ContinuousLinearMap.fst ℝ P Plane).comp (ContinuousLinearMap.fst ℝ (P × Plane)
    ℝ))

/-- Actual all-order class transport along the common-cover path. The
indexed band map allows a tail such as `band n = n+4`. Constants are uniform
in all choices of centers and lifted copies. -/
theorem memClass_sourceArgument (s : WeightedClasses.StripData P)
    {w : ℕ → P → ℝ} {α : ℝ} {f : ℕ → P × Plane → V}
    (hf : WeightedClasses.MemClass (sourceStrip s) (fun n z => w n z.1) α f)
    (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h) (D : ℕ)
    (band gap : ℕ → ℕ) (center : ℕ → Plane) (copy : ℕ → Frequency)
    (hband : ∀ n, 4 ≤ band n) (hgap : ∀ n, gap n ≤ D)
    (hslow : ∀ n, s.slow n = ChartScales.S (band n)) :
    WeightedClasses.MemClass (jointStrip s) (fun n z => w n z.1.1) α
      (fun n z => f n (sourceArgument (bandGeometry B h (band n) (gap n) (center n)) (copy n) z))
        := by
  let g n := bandGeometry B h (band n) (gap n) (center n)
  have hpres (n : ℕ) (x : Joint P) :
      sourceArgument (g n) (copy n) 0 + sourceLinear P (g n) x = sourceArgument (g n) (copy n) x :=
    (sourceArgument_affine (g n) (copy n) x).symm
  have hmaps (n : ℕ) (x : Joint P) (hx : x ∈ (jointStrip s).domain) :
      sourceArgument (g n) (copy n) 0 + sourceLinear P (g n) x ∈ (sourceStrip s).domain := by
    rw [hpres]
    exact hx
  have hweights (n : ℕ) (x : Joint P) (_hx : x ∈ (jointStrip s).domain) :
      w n (sourceArgument (g n) (copy n) 0 + sourceLinear P (g n) x).1 = w n x.1.1 := by
    rw [hpres]
    rfl
  have heps (n : ℕ) : (sourceStrip s).epsilon n ^ α ≤ 1 * (jointStrip s).epsilon n ^ α := by
    simp [sourceStrip, jointStrip, parameterStrip]
  have hgrowth (n : ℕ) (x : Joint P) (_hx : x ∈ (jointStrip s).domain) :
      (sourceStrip s).growth n (sourceArgument (g n) (copy n) 0 + sourceLinear P (g n) x) ≤
        1 * (jointStrip s).growth n x ^ 1 := by
    rw [hpres]
    simp [sourceStrip, jointStrip, parameterStrip, WeightedClasses.StripData.growth, sourceArgument]
  have hlinear (n : ℕ) (x : Joint P) (_hx : x ∈ (jointStrip s).domain) :
      ‖sourceLinear P (g n)‖ ≤ bandArgumentCost B D * (jointStrip s).growth n x ^ 1 := by
    rw [pow_one]
    refine (norm_sourceLinear_le (g n)).trans ?_
    refine (bandGeometry_argumentCost_le B hh (hband n) (hgap n) (center n)).trans ?_
    rw [← hslow n]
    exact mul_le_mul_of_nonneg_left (s.slow_le_growth n x.1.1)
      (zero_le_one.trans (bandArgumentCost_one_le B D))
  have hout := memClass_affine_transport (sourceStrip s) (jointStrip s) hf id
    (fun n => sourceLinear P (g n)) (fun n => sourceArgument (g n) (copy n) 0)
    hmaps hweights (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
    (bandArgumentCost_one_le B D) 1 1 heps hgrowth hlinear
  simpa only [id_eq, hpres] using hout

end SourceClasses

section CommonBandChanges

/-- Either direction of a bounded covering change. The inverse is a map on
the universal cover; no extra periodicity is imposed on its input. -/
noncomputable def coverChange (forward : Bool) (d : ℕ) : Plane →L[ℝ] Plane :=
  if forward then (CommonCoverSolve.coverPower d : Plane →L[ℝ] Plane)
  else ((CommonCoverSolve.coverPower d).symm : Plane →L[ℝ] Plane)

theorem norm_coverChange_le (forward : Bool) {d D : ℕ} (hd : d ≤ D) :
    ‖coverChange forward d‖ ≤ CommonCoverSolve.coveringBound D := by
  cases forward
  · exact CommonCoverSolve.inverseCoveringNorm_le_bound hd
  · exact CommonCoverSolve.coveringNorm_le_bound hd

noncomputable def bandCommonChart (D : ℝ) (n m : ℕ) (forward : Bool) (gap : ℕ) :
    SlowPoint × Plane →L[ℝ] SlowPoint × Plane :=
  (bandChart D n m).prodMap (coverChange forward gap)

@[simp] theorem bandCommonChart_apply (D : ℝ) (n m : ℕ) (forward : Bool) (gap : ℕ)
    (x : SlowPoint × Plane) :
    bandCommonChart D n m forward gap x = (bandChart D n m x.1, coverChange forward gap x.2) := rfl

noncomputable def commonChartCost (D : ℝ) (gapBound : ℕ) : ℝ :=
  chartCost D + CommonCoverSolve.coveringBound gapBound

theorem commonChartCost_one_le (D : ℝ) (gapBound : ℕ) : 1 ≤ commonChartCost D gapBound := by
  unfold commonChartCost
  linarith [chartCost_one_le D, CommonCoverSolve.coveringBound_pos gapBound]

theorem norm_bandCommonChart_le (D : ℝ) {n m gap gapBound : ℕ}
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) (forward : Bool) (hgap : gap ≤ gapBound) :
    ‖bandCommonChart D n m forward gap‖ ≤ commonChartCost D gapBound := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (commonChartCost_one_le _ _))
  intro x
  rw [bandCommonChart_apply, Prod.norm_def]
  have hC : 0 ≤ CommonCoverSolve.coveringBound gapBound := (CommonCoverSolve.coveringBound_pos _).le
  have hD : 0 ≤ chartCost D := zero_le_one.trans (chartCost_one_le D)
  apply max_le
  · calc
      _ ≤ ‖bandChart D n m‖ * ‖x.1‖ := (bandChart D n m).le_opNorm _
      _ ≤ chartCost D * ‖x‖ := mul_le_mul (norm_bandChart_le D hnm hmn)
          (norm_fst_le x) (norm_nonneg _) hD
      _ ≤ commonChartCost D gapBound * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        unfold commonChartCost
        linarith
  · calc
      _ ≤ ‖coverChange forward gap‖ * ‖x.2‖ := (coverChange forward gap).le_opNorm _
      _ ≤ CommonCoverSolve.coveringBound gapBound * ‖x‖ :=
        mul_le_mul (norm_coverChange_le forward hgap) (norm_snd_le x) (norm_nonneg _) hC
      _ ≤ commonChartCost D gapBound * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        unfold commonChartCost
        linarith

theorem bandCommonChart_envelope {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : ℝ) {n m gap gapBound r : ℕ} (hnm : n ≤ m + 4) (hmn : m ≤ n + 4)
    (forward : Bool) (hgap : gap ≤ gapBound) {f : SlowPoint × Plane → V}
    (hf : ContDiff ℝ ∞ f) {e : SlowPoint × Plane → ℝ} (he : EnvelopeJets r f e) :
    EnvelopeJets r (fun x => f (bandCommonChart D n m forward gap x))
      (fun x => e (bandCommonChart D n m forward gap x) * commonChartCost D gapBound ^ r) := by
  simpa only [zero_add] using he.affine hf (bandCommonChart D n m forward gap) 0
    (commonChartCost_one_le D gapBound) (norm_bandCommonChart_le D hnm hmn forward hgap)

/-- Class transport under the actual simultaneous slow-chart and bounded
covering change. The weight/edge identities express the same physical
profile in the two charts; they are geometric identities, not jet bounds. -/
theorem memClass_bandCommonChart {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : WeightedClasses.StripData (SlowPoint × Plane))
    {w v : ℕ → SlowPoint × Plane → ℝ} {α h : ℝ} {f : ℕ → SlowPoint × Plane → V}
    (hf : WeightedClasses.MemClass s w α f) (D : ℝ) (gapBound : ℕ)
    (band index gap : ℕ → ℕ) (forward : ℕ → Bool)
    (hband : ∀ n, 1 ≤ band n)
    (hoverlap : ∀ n, band n ≤ band (index n) + 4 ∧ band (index n) ≤ band n + 4)
    (hgap : ∀ n, gap n ≤ gapBound)
    (hepsilon : ∀ n, s.epsilon n = ChartScales.epsilon h (band n))
    (hslow : ∀ n, s.slow n = ChartScales.S (band n))
    (hmap : ∀ n x, x ∈ s.domain →
      bandCommonChart D (band n) (band (index n)) (forward n) (gap n) x ∈ s.domain)
    (hdelta : ∀ n x, x ∈ s.domain →
      s.delta (bandCommonChart D (band n) (band (index n)) (forward n) (gap n) x) = s.delta x)
    (hweight : ∀ n x, x ∈ s.domain →
      w (index n) (bandCommonChart D (band n) (band (index n)) (forward n) (gap n) x) = v n x) :
    WeightedClasses.MemClass s v α
      (fun n x => f (index n) (bandCommonChart D (band n) (band (index n)) (forward n) (gap n) x))
        := by
  let L n := bandCommonChart D (band n) (band (index n)) (forward n) (gap n)
  have heps (n : ℕ) : s.epsilon (index n) ^ α ≤
      (2 : ℝ) ^ (4 * |h * α|) * s.epsilon n ^ α := by
    rw [hepsilon, hepsilon]
    exact epsilon_power_transfer h α (hoverlap n).2 (hoverlap n).1
  have hgrowth (n : ℕ) (x : SlowPoint × Plane) (hx : x ∈ s.domain) :
      s.growth (index n) (0 + L n x) ≤ 25 * s.growth n x ^ 1 := by
    simp only [zero_add, pow_one, WeightedClasses.StripData.growth]
    rw [hdelta n x hx, hslow, hslow]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (slow_scale_transfer (hband n) (hoverlap n).2)
      (show 0 ≤ max 1 (s.delta x)⁻¹ from zero_le_one.trans (le_max_left _ _))
  have hlin (n : ℕ) (x : SlowPoint × Plane) (_hx : x ∈ s.domain) :
      ‖L n‖ ≤ commonChartCost D gapBound * s.growth n x ^ 0 := by
    simpa only [pow_zero, mul_one] using norm_bandCommonChart_le D
      (hoverlap n).1 (hoverlap n).2 (forward n) (hgap n)
  have ht := memClass_affine_transport s s hf index L (fun _ => 0)
    (by simpa only [zero_add] using hmap)
    (by simpa only [zero_add] using hweight)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
    (by norm_num : (1 : ℝ) ≤ 25) (commonChartCost_one_le D gapBound) 1 0 heps hgrowth hlin
  simpa only [zero_add] using ht

end CommonBandChanges

section PhysicalProfileWeights

theorem bandChart_eq_transition (h : ℝ) (n m : ℕ) (x : SlowPoint) :
    bandChart (CoordinateAlgebra.D h) n m x =
      SimilarityHomogeneity.chartTransition h (ChartScales.Q n) (ChartScales.Q m) x :=
  bandChart_formula _ _ _ _

theorem profileX_bandChart {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n m : ℕ) {x : SlowPoint} (hx : 0 < x.2.2) :
    SimilarityHomogeneity.chartX h (bandChart (CoordinateAlgebra.D h) n m x) =
      SimilarityHomogeneity.chartX h x := by
  rw [bandChart_eq_transition]
  exact SimilarityHomogeneity.chartX_transition hh hh1 (ChartScales.Q_pos n) (ChartScales.Q_pos m)
    hx

theorem profileEta_bandChart {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n m : ℕ) {x : SlowPoint} (hx : 0 < x.2.2) :
    SimilarityHomogeneity.chartEta h (bandChart (CoordinateAlgebra.D h) n m x) =
      SimilarityHomogeneity.chartEta h x := by
  rw [bandChart_eq_transition]
  exact SimilarityHomogeneity.chartEta_transition hh hh1 (ChartScales.Q_pos n) (ChartScales.Q_pos
    m) hx

noncomputable def profileDomain (h a b : ℝ) : Set SlowPoint :=
  {x | x ∈ SimilarityHomogeneity.chartDomain ∧ SimilarityHomogeneity.chartX h x ∈ Ioo a b}

theorem profileX_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : SlowPoint} (hx : 0 < x.2.2) : ContDiffAt ℝ ∞ (SimilarityHomogeneity.chartX h) x :=
  (SimilarityHomogeneity.chartInner_smoothAt hh hh1 hx).fst

theorem isOpen_profileDomain {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (a b : ℝ) :
    IsOpen (profileDomain h a b) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.inter_mem (SimilarityHomogeneity.isOpen_chartDomain.mem_nhds hx.1)
    ((profileX_smoothAt hh hh1 hx.1.2).continuousAt (isOpen_Ioo.mem_nhds hx.2))

theorem profileDomain_bandChart {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n m : ℕ) {x : SlowPoint} (hx : x ∈ profileDomain h a b) :
    bandChart (CoordinateAlgebra.D h) n m x ∈ profileDomain h a b := by
  constructor
  · rw [bandChart_eq_transition]
    exact (SimilarityHomogeneity.chartTransition_mem_iff (ChartScales.Q_pos n) (ChartScales.Q_pos
      m) x).mpr hx.1
  · rw [profileX_bandChart hh hh1 n m hx.1.2]
    exact hx.2

/-- A concrete strip with the physical profile weight and logarithmic
distance. The independent index chooses the actual dyadic band. -/
noncomputable def profileSlowStrip {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (band : ℕ → ℕ) (hband : ∀ n, 1 ≤ band n)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζ0 : ∀ X ∈ Ioo a b, 0 ≤ ζ X) :
    WeightedClasses.StripData SlowPoint where
  domain := profileDomain h a b
  isOpen_domain := isOpen_profileDomain hh hh1 a b
  epsilon n := ChartScales.epsilon h (band n)
  epsilon_pos n := ChartScales.epsilon_pos h (band n)
  epsilon_le_one n := ChartScales.epsilon_le_one h hh.le (band n)
  slow n := ChartScales.S (band n)
  one_le_slow n := PhysicalGraphBounds.S_ge_one (hband n)
  delta := SimilarityHomogeneity.chartLogDistance h a b
  delta_pos _ hx := SimilarityHomogeneity.profileLogDistance_pos ha hx.2.1 hx.2.2
  zeta x := ζ (SimilarityHomogeneity.chartX h x)
  zeta_smooth x hx := (hζ.contDiffAt.comp x (profileX_smoothAt hh hh1 hx.1.2)).contDiffWithinAt
  zeta_nonneg _ hx := hζ0 _ hx.2

/-- Here the domain and the edge identity are proved from actual profile
homogeneity. Only the prescribed additional weight is transported. -/
theorem memClass_profile_bandCommonChart
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (band : ℕ → ℕ) (hband : ∀ n, 1 ≤ band n)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζ0 : ∀ X ∈ Ioo a b, 0 ≤ ζ X)
    {w v : ℕ → SlowPoint × Plane → ℝ} {α : ℝ} {f : ℕ → SlowPoint × Plane → V}
    (hf : WeightedClasses.MemClass
      (sourceStrip (profileSlowStrip hh hh1 ha band hband ζ hζ hζ0)) w α f)
    (gapBound : ℕ) (index gap : ℕ → ℕ) (forward : ℕ → Bool)
    (hoverlap : ∀ n, band n ≤ band (index n) + 4 ∧ band (index n) ≤ band n + 4)
    (hgap : ∀ n, gap n ≤ gapBound)
    (hweight : ∀ n x, x.1 ∈ profileDomain h a b →
      w (index n) (bandCommonChart (CoordinateAlgebra.D h) (band n) (band (index n))
        (forward n) (gap n) x) = v n x) :
    WeightedClasses.MemClass
      (sourceStrip (profileSlowStrip hh hh1 ha band hband ζ hζ hζ0)) v α
      (fun n x => f (index n) (bandCommonChart (CoordinateAlgebra.D h)
        (band n) (band (index n)) (forward n) (gap n) x)) := by
  apply memClass_bandCommonChart _ hf (CoordinateAlgebra.D h) gapBound band index gap forward
    hband hoverlap hgap (fun _ => rfl) (fun _ => rfl)
  · intro n x hx
    exact profileDomain_bandChart hh hh1 (band n) (band (index n)) hx
  · intro n x hx
    change SimilarityHomogeneity.chartLogDistance h a b
      (bandChart (CoordinateAlgebra.D h) (band n) (band (index n)) x.1) =
        SimilarityHomogeneity.chartLogDistance h a b x.1
    rw [SimilarityHomogeneity.chartLogDistance, SimilarityHomogeneity.chartLogDistance,
      profileX_bandChart hh hh1 (band n) (band (index n)) (x := x.1) hx.1.2]
  · exact hweight

/-- The actual mean class is preserved, with exactly the same small-scale
exponent, under all overlapping band/common-cover changes. -/
theorem meanClass_profile_bandCommonChart
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (band : ℕ → ℕ) (hband : ∀ n, 1 ≤ band n)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζ0 : ∀ X ∈ Ioo a b, 0 ≤ ζ X)
    {α : ℝ} {f : ℕ → SlowPoint × Plane → V}
    (hf : WeightedClasses.MeanClass
      (sourceStrip (profileSlowStrip hh hh1 ha band hband ζ hζ hζ0)) α f)
    (gapBound : ℕ) (index gap : ℕ → ℕ) (forward : ℕ → Bool)
    (hoverlap : ∀ n, band n ≤ band (index n) + 4 ∧ band (index n) ≤ band n + 4)
    (hgap : ∀ n, gap n ≤ gapBound) :
    WeightedClasses.MeanClass
      (sourceStrip (profileSlowStrip hh hh1 ha band hband ζ hζ hζ0)) α
      (fun n x => f (index n) (bandCommonChart (CoordinateAlgebra.D h)
        (band n) (band (index n)) (forward n) (gap n) x)) := by
  apply memClass_profile_bandCommonChart hh hh1 ha band hband ζ hζ hζ0 hf
    gapBound index gap forward hoverlap hgap
  intro n x hx
  change ζ (SimilarityHomogeneity.chartX h
    (bandChart (CoordinateAlgebra.D h) (band n) (band (index n)) x.1)) =
      ζ (SimilarityHomogeneity.chartX h x.1)
  rw [profileX_bandChart hh hh1 _ _ hx.1.2]

/-- The wave envelope is transported at its actual point. The radial
factor and edge distance are invariant; the slot profile is pulled back
exactly and is not replaced by another label's profile. -/
theorem waveClass_profile_bandCommonChart
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (band : ℕ → ℕ) (hband : ∀ n, 1 ≤ band n)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζ0 : ∀ X ∈ Ioo a b, 0 ≤ ζ X)
    (P : ℕ → SlowPoint × Plane → ℝ) {α : ℝ} {f : ℕ → SlowPoint × Plane → V}
    (hf : WeightedClasses.WaveClass
      (sourceStrip (profileSlowStrip hh hh1 ha band hband ζ hζ hζ0)) P α f)
    (gapBound : ℕ) (index gap : ℕ → ℕ) (forward : ℕ → Bool)
    (hoverlap : ∀ n, band n ≤ band (index n) + 4 ∧ band (index n) ≤ band n + 4)
    (hgap : ∀ n, gap n ≤ gapBound) :
    WeightedClasses.WaveClass
      (sourceStrip (profileSlowStrip hh hh1 ha band hband ζ hζ hζ0))
      (fun n x => P (index n) (bandCommonChart (CoordinateAlgebra.D h)
        (band n) (band (index n)) (forward n) (gap n) x)) α
      (fun n x => f (index n) (bandCommonChart (CoordinateAlgebra.D h)
        (band n) (band (index n)) (forward n) (gap n) x)) := by
  apply memClass_profile_bandCommonChart hh hh1 ha band hband ζ hζ hζ0 hf
    gapBound index gap forward hoverlap hgap
  intro n x hx
  change Real.sqrt (ζ (SimilarityHomogeneity.chartX h
    (bandChart (CoordinateAlgebra.D h) (band n) (band (index n)) x.1))) * _ =
      Real.sqrt (ζ (SimilarityHomogeneity.chartX h x.1)) * _
  rw [profileX_bandChart hh hh1 _ _ hx.1.2]

end PhysicalProfileWeights

section MeshChanges

/-- Normalized small slow-box coordinates, using the actual widths from
the coloring construction. -/
noncomputable def meshCoordinate (D : ℝ) (L : SlotColoring.Label)
    (x : SlotColoring.Position) : SlotColoring.Position :=
  fun j => (x j - SlotColoring.width D j L.1 * (L.2.1 j : ℝ)) / SlotColoring.width D j L.1

noncomputable def meshPoint (D : ℝ) (L : SlotColoring.Label)
    (x : SlotColoring.Position) : SlotColoring.Position :=
  fun j => SlotColoring.width D j L.1 * x j + SlotColoring.width D j L.1 * (L.2.1 j : ℝ)

noncomputable def meshLinear (D : ℝ) (L M : SlotColoring.Label) :
    SlotColoring.Position →L[ℝ] SlotColoring.Position :=
  ContinuousLinearMap.pi (fun j : Fin 3 =>
    (SlotColoring.width D j L.1 / SlotColoring.width D j M.1) •
      (ContinuousLinearMap.proj j : SlotColoring.Position →L[ℝ] ℝ))

noncomputable def meshOffset (D : ℝ) (L M : SlotColoring.Label) : SlotColoring.Position :=
  fun j => (SlotColoring.width D j L.1 * (L.2.1 j : ℝ) -
    SlotColoring.width D j M.1 * (M.2.1 j : ℝ)) / SlotColoring.width D j M.1

noncomputable def meshTransition (D : ℝ) (L M : SlotColoring.Label)
    (x : SlotColoring.Position) : SlotColoring.Position := meshOffset D L M + meshLinear D L M x

@[simp] theorem meshLinear_apply (D : ℝ) (L M : SlotColoring.Label)
    (x : SlotColoring.Position) (j : Fin 3) :
    meshLinear D L M x j = (SlotColoring.width D j L.1 / SlotColoring.width D j M.1) * x j := rfl

theorem meshTransition_eq_coordinate (D : ℝ) (L M : SlotColoring.Label)
    (x : SlotColoring.Position) : meshTransition D L M x = meshCoordinate D M (meshPoint D L x) :=
      by
  ext j
  simp only [meshTransition, Pi.add_apply, meshOffset, meshLinear_apply, meshCoordinate, meshPoint]
  ring

theorem mesh_ratioBound_pos (D : ℝ) : 0 < SlotColoring.ratioBound D := by
  unfold SlotColoring.ratioBound
  positivity

/-- Only physical-box adjacency is assumed; the normalized coordinate
change is bounded uniformly over all box indices and levels. -/
theorem norm_meshLinear_le {D : ℝ} {L M : SlotColoring.Label} (h : SlotColoring.Adj D L M) :
    ‖meshLinear D L M‖ ≤ SlotColoring.ratioBound D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mesh_ratioBound_pos D).le
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mesh_ratioBound_pos D).le (norm_nonneg x))).mpr
  intro j
  rw [meshLinear_apply, norm_mul, Real.norm_eq_abs,
    abs_of_pos (div_pos (SlotColoring.width_pos D j h.left_positive)
      (SlotColoring.width_pos D j h.right_positive))]
  exact mul_le_mul
    (SlotColoring.width_ratio_le D j h.left_positive h.right_positive h.left_level_le
      h.right_level_le)
    (norm_le_pi_norm x j) (norm_nonneg _) (mesh_ratioBound_pos D).le

/-- The translation is controlled by genuine support overlap. It is not
bounded by assuming the lattice copy indices themselves are bounded. -/
theorem norm_meshOffset_le {D : ℝ} {L M : SlotColoring.Label} (h : SlotColoring.Adj D L M) :
    ‖meshOffset D L M‖ ≤ 2 * (SlotColoring.ratioBound D + 1) := by
  apply (pi_norm_le_iff_of_nonneg (by linarith [mesh_ratioBound_pos D] :
    0 ≤ 2 * (SlotColoring.ratioBound D + 1))).mpr
  intro j
  have hM := SlotColoring.width_pos D j h.right_positive
  rw [Real.norm_eq_abs, meshOffset, abs_div, abs_of_pos hM]
  calc
    _ ≤ (2 * (SlotColoring.width D j L.1 + SlotColoring.width D j M.1)) /
        SlotColoring.width D j M.1 :=
      div_le_div_of_nonneg_right (SlotColoring.overlapping_centers D L M h.overlap j) hM.le
    _ = 2 * (SlotColoring.width D j L.1 / SlotColoring.width D j M.1 + 1) := by
      field_simp
    _ ≤ 2 * (SlotColoring.ratioBound D + 1) := by
      linarith [SlotColoring.width_ratio_le D j h.left_positive h.right_positive
        h.left_level_le h.right_level_le]

theorem meshTransition_smooth (D : ℝ) (L M : SlotColoring.Label) :
    ContDiff ℝ ∞ (meshTransition D L M) := contDiff_const.add (meshLinear D L M).contDiff

theorem meshTransition_jet_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {D : ℝ} {L M : SlotColoring.Label} (h : SlotColoring.Adj D L M)
    {f : SlotColoring.Position → V} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (x : SlotColoring.Position) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (meshTransition D L M x)‖ ≤ A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => f (meshTransition D L M y)) x‖ ≤
      A * (1 + SlotColoring.ratioBound D) ^ m := by
  apply affine_jet_bound hf (meshLinear D L M) (meshOffset D L M)
    (by linarith [mesh_ratioBound_pos D])
    ((norm_meshLinear_le h).trans (by linarith)) m x hb

theorem meshTransition_norm_le {D : ℝ} {L M : SlotColoring.Label} (h : SlotColoring.Adj D L M)
    {x : SlotColoring.Position} (hx : ‖x‖ ≤ 2) :
    ‖meshTransition D L M x‖ ≤ 4 * SlotColoring.ratioBound D + 2 := by
  have hlin : ‖meshLinear D L M x‖ ≤ SlotColoring.ratioBound D * 2 :=
    ((meshLinear D L M).le_opNorm x).trans
      (mul_le_mul (norm_meshLinear_le h) hx (norm_nonneg _) (mesh_ratioBound_pos D).le)
  exact (norm_add_le _ _).trans (by linarith [norm_meshOffset_le h])

/-- The covering budget used in the path estimate is now instantiated
from the actual adjacent labels and their coarsest common native index. -/
theorem adjacent_argumentCost_le (B : Plane ≃L[ℝ] Plane) {h D : ℝ} (hh : 0 ≤ h)
    {L M : SlotColoring.Label} (hadj : SlotColoring.Adj D L M) (hL : 4 ≤ L.1)
    (center : Plane) :
    argumentCost (bandGeometry B h L.1
      (ChartScales.nativeIndex h L.1 - commonIndex h L.1 M.1) center) ≤
        bandArgumentCost B (SlotColoring.nativeGap h) * ChartScales.S L.1 :=
  bandGeometry_argumentCost_le B hh hL (adjacent_commonIndex_gap_le h hh hadj).1 center

end MeshChanges

section NativeInstantiation

/-- The actual radial/time eigenvector basis, not an abstract invertible
basis supplied as an assumption. -/
noncomputable def nativeBasis : Plane ≃L[ℝ] Plane :=
  TorusAverages.slotChart PhysicalGraphBounds.radialDirection PhysicalGraphBounds.timeDirection
    (by
      unfold PhysicalGraphBounds.radialDirection PhysicalGraphBounds.timeDirection
      dsimp only
      nlinarith [sq_nonneg (Real.sqrt 2 - 1)])

theorem nativeBasis_radial : nativeBasis (1, 0) = PhysicalGraphBounds.radialDirection := by
  rw [nativeBasis, TorusAverages.slotChart_apply]
  simp

theorem nativeBasis_temporal : nativeBasis (0, 1) = PhysicalGraphBounds.timeDirection := by
  rw [nativeBasis, TorusAverages.slotChart_apply]
  simp

/-- The exact manuscript path, with the actual `c_i` and `v_t`. -/
theorem native_band_path (h : ℝ) (n gap : ℕ) (center : Plane) (k : Frequency)
    (Y : Plane) (s : ℝ) :
    (bandGeometry nativeBasis h n gap center).path k Y s =
      Y + (CommonCoverSolve.coverPower gap).symm
        ((ChartScales.timeCoefficient h n *
          (s - ((bandGeometry nativeBasis h n gap center).coordinates k Y).2)) •
            PhysicalGraphBounds.timeDirection) := by
  rw [bandGeometry_path, nativeBasis_temporal]

/-- Any finite collection of active levels with the geometric level-span
bound has a genuine coarsest member and a uniform covering budget to it. -/
theorem exists_coarsest_band (h : ℝ) (hh : 0 ≤ h) (levels : Finset ℕ)
    (hne : levels.Nonempty) (hpos : ∀ n ∈ levels, 1 ≤ n)
    (hspan : ∀ n ∈ levels, ∀ m ∈ levels, n ≤ m + 4) :
    ∃ c ∈ levels, ∀ n ∈ levels,
      ChartScales.nativeIndex h c ≤ ChartScales.nativeIndex h n ∧
        ChartScales.nativeIndex h n - ChartScales.nativeIndex h c ≤ SlotColoring.nativeGap h := by
  obtain ⟨c, hc, hmin⟩ := levels.exists_min_image (ChartScales.nativeIndex h) hne
  refine ⟨c, hc, ?_⟩
  intro n hn
  refine ⟨hmin n hn, ?_⟩
  have hg := SlotColoring.nativeIndex_gap h hh (hpos n hn) (hpos c hc)
    (hspan n hn c hc) (hspan c hc n hn)
  change SlotColoring.nativeIndex h n - SlotColoring.nativeIndex h c ≤ _
  omega

end NativeInstantiation

end

end NavierStokes.CommonCoverClass
