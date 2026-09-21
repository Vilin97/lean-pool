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

import LeanPool.PoincareGeometry.BonnetMyers.ManifoldSineTest
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity

/-!
# Curvature regularity along global parallel fields

The geometric index calculation uses the actual curvature tensor sampled by a
global parallel field.  This module proves the missing analytic fact: that
scalar coefficient is continuous, hence its sine-weighted restriction to an
interval is integrable.  The proof is local in a tangent-bundle
trivialization.  It expands the two parallel/velocity vectors in a smooth
local frame and invokes the already proved regularity of the actual curvature
tensor in that frame.

This is only a regularity bridge.  It does not assert second variation or
nonnegativity of the index form.
-/

noncomputable section

open Bundle Manifold Set Filter
open MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal Topology RealInnerProductSpace BigOperators

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private lemma localFrameCoeff_total_eq
    [RiemannianBundle TM]
    [IsContMDiffRiemannianBundle I 1 E TM]
    {x : M} (e : Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} (b : Module.Basis ι ℝ E) (v : TM x)
    (hx : x ∈ e.baseSet) (i : ι) :
    e.localFrameCoeff I b i x v = b.repr (e (⟨x, v⟩ : Bundle.TotalSpace E TM)).2 i := by
  classical
  let s : Π y : M, TM y := Function.update (fun _ ↦ 0) x v
  have hs : s x = v := by simp [s]
  have h := e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := s) hx (i := i)
  simpa [hs] using h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private lemma eq_sum_localFrame_total
    [RiemannianBundle TM]
    [IsContMDiffRiemannianBundle I 1 E TM]
    {x : M} (e : Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (v : TM x)
    (hx : x ∈ e.baseSet) :
    v = ∑ i, b.repr (e (⟨x, v⟩ : Bundle.TotalSpace E TM)).2 i •
      e.localFrame b i x := by
  classical
  let s : Π y : M, TM y := Function.update (fun _ ↦ 0) x v
  have hs : s x = v := by simp [s]
  calc
    v = s x := hs.symm
    _ = ∑ i, e.localFrameCoeff I b i x (s x) • e.localFrame b i x :=
      e.eq_sum_localFrameCoeff_smul (I := I) (b := b) hx
    _ = ∑ i, b.repr (e (⟨x, v⟩ : Bundle.TotalSpace E TM)).2 i •
        e.localFrame b i x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hs]
      rw [localFrameCoeff_total_eq (I := I) e b v hx i]

private lemma clm3_sum_first
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {ι : Type*} [Fintype ι]
    (R : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (a : ι → ℝ) (x : ι → V) (y z : V) :
    R (∑ i, a i • x i) y z = ∑ i, a i • R (x i) y z := by
  letI : SeminormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  simp only [map_sum, map_smul, sum_apply, smul_apply]

private lemma clm2_sum_first
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι]
    (R : V →L[ℝ] V →L[ℝ] V)
    (a : ι → ℝ) (x : ι → V) (y : V) :
    R (∑ i, a i • x i) y = ∑ i, a i • R (x i) y := by
  simp only [map_sum, map_smul, sum_apply, smul_apply]

private lemma clm1_sum_first
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι]
    (R : V →L[ℝ] V)
    (a : ι → ℝ) (x : ι → V) :
    R (∑ i, a i • x i) = ∑ i, a i • R (x i) := by
  simp only [map_sum, map_smul]

private lemma expand_four_slots
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {ι : Type*} [Fintype ι]
    (R : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (a b c d : ι → ℝ) (x y z w : ι → V) :
    inner ℝ (∑ i, a i • x i)
      (R (∑ j, b j • y j) (∑ k, c k • z k) (∑ l, d l • w l)) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (a i * b j * c k * d l) * inner ℝ (x i) (R (y j) (z k) (w l)) := by
  classical
  rw [sum_inner]
  simp_rw [real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [clm3_sum_first R b y (∑ k, c k • z k) (∑ l, d l • w l), inner_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_right]
  rw [clm2_sum_first (R (y j)) c z (∑ l, d l • w l), inner_sum]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [real_inner_smul_right]
  rw [clm1_sum_first ((R (y j)) (z k)) d w, inner_sum]
  simp_rw [real_inner_smul_right]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

namespace IntrinsicGeodesic.GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The coefficient of the actual curvature tensor on a global parallel
field is continuous at every time.  The proof works in one local tangent
frame around the chosen time and expands all four curvature slots there. -/
theorem GlobalParallelField.continuousAt_curvatureCoefficient_curvature
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TangentSpace I (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) (t : ℝ) :
    ContinuousAt (fun s ↦ p.curvatureCoefficient
      (curvature (I := I) (M := M) cov) s) t := by
  classical
  letI : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun _ ↦ inferInstance
  letI : (x : M) → InnerProductSpace ℝ (TangentSpace I x) := fun _ ↦ inferInstance
  let q := shift γ t₀
  let e := trivializationAt E (TangentSpace I : M → Type _) (curve q t)
  let b := Module.finBasis ℝ E
  let pf : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _) :=
    fun s ↦ ⟨curve q s, p.field s⟩
  have hpf : ContinuousAt pf t := by
    simpa only [pf, q] using p.continuousAt_totalState t
  rw [FiberBundle.continuousAt_totalSpace E] at hpf
  have hpcoord : ContinuousAt (fun s ↦ (e (pf s)).2) t := by
    simpa only [e, pf] using hpf.2
  have hpcoeff (i : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun s ↦ b.repr (e (pf s)).2 i) t := by
    change ContinuousAt (fun s ↦ (b.coord i) ((e (pf s)).2)) t
    exact (b.coord i).toContinuousLinearMap.continuous.continuousAt.comp_of_eq
      hpcoord rfl
  have hx : curve q t ∈ e.baseSet := by
    simp only [e]
    exact FiberBundle.mem_baseSet_trivializationAt E
      (TangentSpace I : M → Type _) _
  have hframe (i : Fin (Module.finrank ℝ E)) :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x ↦ (⟨x, e.localFrame b i x⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := I) (n := 2) b i
  have hscalar (i j k l : Fin (Module.finrank ℝ E)) :
      ContMDiffAt I (𝓘(ℝ, ℝ)) 0
        (fun x ↦ inner ℝ (e.localFrame b i x)
          (cov.curvatureTensor x (e.localFrame b j x)
            (e.localFrame b k x) (e.localFrame b l x))) (curve q t) := by
    have hcurv := RicciFlow.curvatureTensor_contMDiffOn_frame_zero (cov := cov)
      e.open_baseSet (hframe j) (hframe k) (hframe l)
    have hscalarOn := @ContMDiffOn.inner_bundle
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ this
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ((hframe i).of_le (by simp)) hcurv
    exact hscalarOn.contMDiffAt (e.open_baseSet.mem_nhds hx)
  have hcomponent (i j k l : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun s ↦ inner ℝ (e.localFrame b i (curve q s))
        (cov.curvatureTensor (curve q s) (e.localFrame b j (curve q s))
          (e.localFrame b k (curve q s))
          (e.localFrame b l (curve q s)))) t := by
    have hcomp := (hscalar i j k l).comp t
      ((q.contMDiffAt_curve (I := I) (M := M) t).of_le (by simp))
    exact hcomp.continuousAt
  let vf : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _) := q.state
  have hvf : ContinuousAt vf t := by
    simpa only [vf] using q.continuousAt_state t
  rw [FiberBundle.continuousAt_totalSpace E] at hvf
  have hvcoord : ContinuousAt (fun s ↦ (e (vf s)).2) t := by
    simpa only [e, vf, curve, q] using hvf.2
  have hvcoeff (i : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun s ↦ b.repr (e (vf s)).2 i) t := by
    change ContinuousAt (fun s ↦ (b.coord i) ((e (vf s)).2)) t
    exact (b.coord i).toContinuousLinearMap.continuous.continuousAt.comp_of_eq
      hvcoord rfl
  have hbase : ∀ᶠ s in 𝓝 t, curve q s ∈ e.baseSet :=
    (q.contMDiffAt_curve (I := I) (M := M) t).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds hx)
  have hformula : (fun s ↦ p.curvatureCoefficient
      (curvature (I := I) (M := M) cov) s) =ᶠ[𝓝 t]
      fun s ↦ ∑ i, ∑ j, ∑ k, ∑ l,
        (b.repr (e (⟨curve q s, p.field s⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 i *
          b.repr (e (⟨curve q s, p.field s⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 j *
          b.repr (e (⟨curve q s, velocity q s⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 k *
          b.repr (e (⟨curve q s, velocity q s⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 l) *
          inner ℝ (e.localFrame b i (curve q s))
            (cov.curvatureTensor (curve q s) (e.localFrame b j (curve q s))
              (e.localFrame b k (curve q s))
              (e.localFrame b l (curve q s))) := by
    filter_upwards [hbase] with s hs
    have hp := eq_sum_localFrame_total (I := I) e b (p.field s) hs
    have hv := eq_sum_localFrame_total (I := I) e b (velocity q s) hs
    let P : TangentSpace I (curve q s) := ∑ i,
      b.repr (e (⟨curve q s, p.field s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 i •
        e.localFrame b i (curve q s)
    let V : TangentSpace I (curve q s) := ∑ i,
      b.repr (e (⟨curve q s, velocity q s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 i •
        e.localFrame b i (curve q s)
    have hp' : p.field s = P := by
      simpa only [P, q, curve] using hp
    have hv' : velocity q s = V := by
      simpa only [V] using hv
    unfold GlobalParallelField.curvatureCoefficient
    change inner ℝ (p.field s)
      (curvature (I := I) (M := M) cov (curve q s) (p.field s)
        (velocity q s) (velocity q s)) = _
    calc
      _ = inner ℝ P
          (curvature (I := I) (M := M) cov (curve q s) P V V) := by
        calc
          _ = inner ℝ P
              (curvature (I := I) (M := M) cov (curve q s) (p.field s)
                (velocity q s) (velocity q s)) :=
              congrArg (fun u ↦ inner ℝ u
                (curvature (I := I) (M := M) cov (curve q s) (p.field s)
                  (velocity q s) (velocity q s))) hp'
          _ = inner ℝ P
              (curvature (I := I) (M := M) cov (curve q s) P
                (velocity q s) (velocity q s)) :=
              congrArg (fun u ↦ inner ℝ P
                (curvature (I := I) (M := M) cov (curve q s) u
                  (velocity q s) (velocity q s))) hp'
          _ = inner ℝ P
              (curvature (I := I) (M := M) cov (curve q s) P V
                (velocity q s)) :=
              congrArg (fun u ↦ inner ℝ P
                (curvature (I := I) (M := M) cov (curve q s) P u
                  (velocity q s))) hv'
          _ = inner ℝ P
              (curvature (I := I) (M := M) cov (curve q s) P V V) :=
              congrArg (fun u ↦ inner ℝ P
                (curvature (I := I) (M := M) cov (curve q s) P V u)) hv'
      _ = _ := by
        dsimp only [P, V]
        rw [expand_four_slots]
        simp only [curvature_apply]
  have hpcoeff' (i : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun s ↦ b.repr (e (⟨curve q s, p.field s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 i) t := by
    simpa only [pf] using hpcoeff i
  have hvcoeff' (i : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun s ↦ b.repr (e (⟨curve q s, velocity q s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 i) t := by
    simpa only [vf, curve, velocity] using hvcoeff i
  have hsum : ContinuousAt (fun s ↦ ∑ i, ∑ j, ∑ k, ∑ l,
      (b.repr (e (⟨curve q s, p.field s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 i *
        b.repr (e (⟨curve q s, p.field s⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 j *
        b.repr (e (⟨curve q s, velocity q s⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 k *
        b.repr (e (⟨curve q s, velocity q s⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))).2 l) *
        inner ℝ (e.localFrame b i (curve q s))
          (cov.curvatureTensor (curve q s) (e.localFrame b j (curve q s))
            (e.localFrame b k (curve q s))
            (e.localFrame b l (curve q s)))) t := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_finsetSum
    intro k hk
    apply tendsto_finsetSum
    intro l hl
    exact ((((hpcoeff' i).mul (hpcoeff' j)).mul (hvcoeff' k)).mul
      (hvcoeff' l)).mul (hcomponent i j k l)
  exact hsum.congr_of_eventuallyEq hformula

/-- Globally, the actual curvature coefficient of a global parallel field is
continuous. -/
theorem GlobalParallelField.continuous_curvatureCoefficient_curvature
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TangentSpace I (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) :
    Continuous (fun s ↦ p.curvatureCoefficient
      (curvature (I := I) (M := M) cov) s) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact p.continuousAt_curvatureCoefficient_curvature t

/-- The sine-square-weighted actual curvature coefficient is interval
integrable, with no extra integrability hypothesis. -/
theorem GlobalParallelField.intervalIntegrable_sineTest_square_mul_curvatureCoefficient_curvature
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TangentSpace I (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (L a b : ℝ) :
    IntervalIntegrable
      (fun s ↦ sineTest L s ^ 2 * p.curvatureCoefficient
        (curvature (I := I) (M := M) cov) s) volume a b := by
  have hcont : Continuous (fun s ↦ sineTest L s ^ 2 *
      p.curvatureCoefficient (curvature (I := I) (M := M) cov) s) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact ((hasDerivAt_sineTest L s).continuousAt.pow 2).mul
      (p.continuousAt_curvatureCoefficient_curvature s)
  exact hcont.intervalIntegrable a b

end IntrinsicGeodesic.GlobalGeodesic

end BonnetMyersEntry
