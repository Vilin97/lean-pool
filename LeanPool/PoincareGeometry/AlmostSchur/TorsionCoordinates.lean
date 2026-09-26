/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Torsion in the preferred tangent coordinates

The preferred tangent frame is locally the pullback of a constant frame on
the model space. Naturality of the actual manifold Lie bracket therefore
proves that these frame fields commute. The torsion identity then gives
symmetry of the actual connection coefficients, first on basis vectors and
then on arbitrary vectors by bilinearity.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Set VectorField
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)
/-- On the chart domain, an inverse-trivialization field is the pullback of
the constant model-space vector field, using the actual chart differential. -/
theorem tangent_symmL_eq_mpullback_const (c x : M)
    (hx : x ∈ (chartAt H c).source) (u : E) :
    (trivializationAt E TM c).symmL ℝ x u =
      mpullback I 𝓘(ℝ, E) (extChartAt I c) (fun _ ↦ u) x := by
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  rw [TangentBundle.symmL_trivializationAt hx]
  unfold mpullback
  rw [ContinuousLinearMap.inverse_eq
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hx')
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx')]
  rfl

variable [CompleteSpace E]
/-- Coordinate-constant tangent fields have zero genuine manifold Lie bracket.
No commutation property of a frame is assumed. -/
theorem mlieBracket_tangent_symmL_eq_zero (c x : M)
    (hx : x ∈ (chartAt H c).source) (u v : E) :
    mlieBracket I (fun y ↦ (trivializationAt E TM c).symmL ℝ y u)
      (fun y ↦ (trivializationAt E TM c).symmL ℝ y v) x = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  have heq (a : E) :
      (fun y ↦ (trivializationAt E TM c).symmL ℝ y a) =ᶠ[𝓝 x]
        mpullback I 𝓘(ℝ, E) (extChartAt I c) (fun _ ↦ a) := by
    filter_upwards [(chartAt H c).open_source.mem_nhds hx] with y hy
    exact tangent_symmL_eq_mpullback_const c y hy a
  have hb := (heq u).mlieBracketWithin_vectorField_eq_nhds (s := univ) (heq v)
  simp only [mlieBracketWithin_univ] at hb
  rw [hb, ← mpullback_mlieBracket (I := I) (I' := 𝓘(ℝ, E))
    (V := fun _ ↦ u) (W := fun _ ↦ v)
    (hV := (contMDiffAt_vectorSpace_iff_contDiffAt.mpr
      (contDiffAt_const (n := 1))).mdifferentiableAt (by simp))
    (hW := (contMDiffAt_vectorSpace_iff_contDiffAt.mpr
      (contDiffAt_const (n := 1))).mdifferentiableAt (by simp))
    (contMDiffAt_extChartAt' (n := 2) hx) (by simp)]
  have hz : mlieBracket 𝓘(ℝ, E) (fun _ : E ↦ u) (fun _ : E ↦ v) = 0 := by
    have hc : lieBracketWithin ℝ (fun _ : E ↦ u) (fun _ : E ↦ v) Set.univ =
        fun _ : E ↦ (0 : E) := by
      funext z
      simp [lieBracketWithin_eq]
    exact (mlieBracketWithin_univ (I := 𝓘(ℝ, E))
      (V := fun _ : E ↦ u) (W := fun _ : E ↦ v)).symm.trans
      (mlieBracketWithin_eq_lieBracketWithin.trans hc)
  rw [hz, mpullback_zero]
  rfl

variable [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- The local frame of the preferred tangent trivialization commutes. -/
theorem mlieBracket_preferred_localFrame_eq_zero {ι : Type*}
    (b : Module.Basis ι ℝ E) (c x : M) (hx : x ∈ (chartAt H c).source) (i j : ι) :
    mlieBracket I ((trivializationAt E TM c).localFrame b i)
      ((trivializationAt E TM c).localFrame b j) x = 0 := by
  have hi : (trivializationAt E TM c).localFrame b i =
      (fun y ↦ (trivializationAt E TM c).symmL ℝ y (b i)) := by
    funext y
    exact localFrame_eq_symmL _ b i y
  have hj : (trivializationAt E TM c).localFrame b j =
      (fun y ↦ (trivializationAt E TM c).symmL ℝ y (b j)) := by
    funext y
    exact localFrame_eq_symmL _ b j y
  rw [hi, hj]
  exact mlieBracket_tangent_symmL_eq_zero c x hx (b i) (b j)

/-- Torsion-freeness makes the coordinate connection coefficients symmetric
on the model basis. -/
theorem frameConnectionCoefficients_basis_symm
    (cov : CovariantDerivative I E TM) (ht : cov.torsion = 0)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (i j : ι) :
    frameConnectionCoefficients cov (trivializationAt E TM c) b x (b i) (b j) =
      frameConnectionCoefficients cov (trivializationAt E TM c) b x (b j) (b i) := by
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  have hd (k : ι) : MDiffAt (T% (e.localFrame b k)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b k hxe).mdifferentiableAt (by simp)
  have h := cov.torsion_eq_zero_iff.mp ht (hd i) (hd j)
  rw [mlieBracket_preferred_localFrame_eq_zero b c x hx i j] at h
  have hc := sub_eq_zero.mp h
  rw [frameConnectionCoefficients_basis, frameConnectionCoefficients_basis]
  simpa only [localFrame_eq_symmL] using congrArg (e.continuousLinearMapAt ℝ x) hc

/-- Symmetry of the actual preferred-chart connection coefficients on all
model vectors, deduced from torsion-freeness and coordinate-frame commutation. -/
theorem frameConnectionCoefficients_symm
    (cov : CovariantDerivative I E TM) (ht : cov.torsion = 0)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (u v : E) :
    frameConnectionCoefficients cov (trivializationAt E TM c) b x u v =
      frameConnectionCoefficients cov (trivializationAt E TM c) b x v u := by
  classical
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, sum_apply, map_smul, smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [frameConnectionCoefficients_basis_symm cov ht b c x hx, smul_comm]

/-- Integration-facing spelling of symmetry for a torsion-free connection. -/
theorem frameConnectionCoefficients_symmetric
    (cov : CovariantDerivative I E TM) (ht : cov.torsion = 0)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (u v : E) :
    frameConnectionCoefficients cov (trivializationAt E TM c) b x u v =
      frameConnectionCoefficients cov (trivializationAt E TM c) b x v u :=
  frameConnectionCoefficients_symm cov ht b c x hx u v

/-- Only vanishing of torsion at the evaluation point is needed for symmetry. -/
theorem frameConnectionCoefficients_symmetric_of_torsion_eq_zero_at
    (cov : CovariantDerivative I E TM)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (ht : cov.torsion x = 0)
    (hx : x ∈ (chartAt H c).source) (u v : E) :
    frameConnectionCoefficients cov (trivializationAt E TM c) b x u v =
      frameConnectionCoefficients cov (trivializationAt E TM c) b x v u := by
  classical
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  have hd (k : ι) : MDiffAt (T% (e.localFrame b k)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b k hxe).mdifferentiableAt (by simp)
  have hb (i j : ι) : frameConnectionCoefficients cov e b x (b i) (b j) =
      frameConnectionCoefficients cov e b x (b j) (b i) := by
    have h := cov.torsion_apply (hd i) (hd j)
    rw [ht, mlieBracket_preferred_localFrame_eq_zero b c x hx i j] at h
    have hc : cov (e.localFrame b j) x (e.localFrame b i x) =
        cov (e.localFrame b i) x (e.localFrame b j x) := by
      apply sub_eq_zero.mp
      simpa only [zero_apply, sub_zero] using h.symm
    rw [frameConnectionCoefficients_basis, frameConnectionCoefficients_basis]
    simpa only [localFrame_eq_symmL] using congrArg (e.continuousLinearMapAt ℝ x) hc
  change frameConnectionCoefficients cov e b x u v =
    frameConnectionCoefficients cov e b x v u
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, sum_apply, map_smul, smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hb, smul_comm]

end AlmostSchur
