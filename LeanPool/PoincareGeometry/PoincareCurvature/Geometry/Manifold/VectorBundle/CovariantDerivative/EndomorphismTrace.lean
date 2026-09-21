/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TensorDivergence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianCoordinate

/-!
# Trace and induced endomorphism connections

This file proves the local-frame trace formula needed to show that fibrewise
trace commutes with the connection induced on the endomorphism bundle.  That
compatibility is the abstract mechanism behind both curvature-to-Ricci and
Ricci-to-scalar differentiation.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] [IsManifold I 1 M]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 2 F V I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "VEnd" => (fun x : M => V x →L[ℝ] V x)

/-- Finite Leibniz expansion for a covariant derivative.  Keeping the sum as
a sum of genuine bundle sections avoids identifying distinct fibres. -/
theorem covariantDerivative_sum_smul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I F V)
    (c : ι → M → ℝ) (σ : ι → ∀ x : M, V x) {x : M}
    (hc : ∀ i, MDiffAt (c i) x) (hσ : ∀ i, MDiffAt (T% (σ i)) x)
    (u : TM x) :
    cov (∑ i : ι, c i • σ i) x u =
      ∑ i : ι, ((c i x) • cov (σ i) x u +
        mvfderiv (I := I) (c i) x u • σ i x) := by
  classical
  have hfinite (s : Finset ι) :
      cov (∑ i ∈ s, c i • σ i) x u =
        ∑ i ∈ s, ((c i x) • cov (σ i) x u +
          mvfderiv (I := I) (c i) x u • σ i x) := by
    induction s using Finset.induction_on with
    | empty =>
        have hz := cov.isCovariantDerivativeOn.zero (x := x)
        have hzu := congrArg (fun L : TM x →L[ℝ] V x => L u) hz
        simpa using hzu
    | @insert i s hi ih =>
        have hterm : MDiffAt (T% (c i • σ i)) x := (hc i).smul_section (hσ i)
        have hrest : MDiffAt (T% (∑ j ∈ s, c j • σ j)) x := by
          have hr := MDifferentiableAt.sum_section (s := s)
            (fun j _ => (hc j).smul_section (hσ j))
          convert hr using 1 <;> ext y <;> simp
        have hadd := cov.isCovariantDerivativeOn.add hterm hrest (x := x)
        have hleibniz := cov.isCovariantDerivativeOn.leibniz (hσ i) (hc i) (x := x)
        have hadd_u := congrArg (fun L : TM x →L[ℝ] V x => L u) hadd
        have hleibniz_u := congrArg (fun L : TM x →L[ℝ] V x => L u) hleibniz
        simp only [Finset.sum_insert hi]
        simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
          at hadd_u hleibniz_u
        rw [hadd_u, hleibniz_u, ih]
  simpa using hfinite Finset.univ

/-- Fibrewise trace of a continuous endomorphism section. -/
def endomorphismTrace (A : ∀ x : M, VEnd x) (x : M) : ℝ :=
  let _ : FiniteDimensional ℝ (V x) :=
    VectorBundle.finiteDimensional ℝ F V x
  LinearMap.trace ℝ (V x) (A x).toLinearMap

/-- Trace in an arbitrary genuine local frame. -/
theorem endomorphismTrace_eq_sum_localFrame
    (A : ∀ x : M, VEnd x)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F) {x : M} (hx : x ∈ e.baseSet) :
    endomorphismTrace (F := F) (V := V) A x =
      ∑ i : ι, (e.localFrameCoeff I b i x) (A x (e.localFrame b i x)) := by
  let _ : FiniteDimensional ℝ (V x) :=
    VectorBundle.finiteDimensional ℝ F V x
  rw [endomorphismTrace, LinearMap.trace_eq_matrix_trace ℝ (e.basisAt b hx)]
  apply Finset.sum_congr rfl
  intro i hi
  change LinearMap.toMatrix (e.basisAt b hx) (e.basisAt b hx) (A x).toLinearMap i i = _
  rw [LinearMap.toMatrix_apply]
  simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := b) hx] using
    (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
    (I := I) (e := e) (b := b) hx
    (fun y => A y (e.localFrame b i y)) i).symm

/-- Fibrewise trace is differentiable whenever the endomorphism section is.
This is proved in a genuine vector-bundle trivialization, rather than by
treating the varying tangent fibres as a fixed coordinate space. -/
theorem mdifferentiableAt_endomorphismTrace
    {A : ∀ x : M, VEnd x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (F →L[ℝ] F) (E := VEnd) y (A y)) x) :
    MDiffAt (endomorphismTrace (F := F) (V := V) A) x := by
  classical
  let e : Trivialization F (TotalSpace.proj : TotalSpace F V → M) :=
    trivializationAt F V x
  let b : Module.Basis (Fin (Module.finrank ℝ F)) ℝ F := Module.finBasis ℝ F
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hterm : ∀ i : Fin (Module.finrank ℝ F),
      MDiffAt (fun y =>
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    intro i
    have hframe : MDiffAt (T% (e.localFrame b i)) x :=
      (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := 1) (i := i) (hx := hx)).mdifferentiableAt
        one_ne_zero
    have happ : MDiffAt (T% (fun y => A y (e.localFrame b i y))) x :=
      hA.clm_bundle_apply hframe
    exact mdifferentiableAt_localFrameCoeff
      (I := I) (e := e) (b := b) (s := fun y => A y (e.localFrame b i y)) hx happ i
  have hsum : MDiffAt (fun y =>
      ∑ i : Fin (Module.finrank ℝ F),
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    have hs := MDifferentiableAt.sum (t := Finset.univ)
      (f := fun i y => (e.localFrameCoeff I b i y) (A y (e.localFrame b i y)))
      (fun i _ => hterm i)
    convert hs using 1 <;> ext y <;> simp
  apply hsum.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact endomorphismTrace_eq_sum_localFrame (I := I) (F := F) (V := V) A e b hy

/-- The directional derivative of fibrewise trace is the sum of the
directional derivatives of its diagonal coefficients in any genuine local
frame.  This is the coordinate bridge used before the connection terms are
shown to cancel. -/
theorem mvfderiv_endomorphismTrace_apply_eq_sum_localFrame
    {A : ∀ x : M, VEnd x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (F →L[ℝ] F) (E := VEnd) y (A y)) x)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F) (hx : x ∈ e.baseSet) (u : TM x) :
    mvfderiv (I := I) (endomorphismTrace (F := F) (V := V) A) x u =
      ∑ i : ι, mvfderiv (I := I) (fun y =>
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x u := by
  have hevent :
      endomorphismTrace (F := F) (V := V) A =ᶠ[nhds x]
        (fun y => ∑ i : ι,
          (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact endomorphismTrace_eq_sum_localFrame (I := I) (F := F) (V := V) A e b hy
  have hmv : mvfderiv (I := I)
      (endomorphismTrace (F := F) (V := V) A) x =
      mvfderiv (I := I) (fun y => ∑ i : ι,
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    unfold mvfderiv
    rw [hevent.eq_of_nhds, hevent.mfderiv_eq]
  rw [hmv]
  have hterm : ∀ i : ι, MDiffAt (fun y =>
      (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    intro i
    have hframe : MDiffAt (T% (e.localFrame b i)) x :=
      (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := 1) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
    have happ : MDiffAt (T% (fun y => A y (e.localFrame b i y))) x :=
      hA.clm_bundle_apply hframe
    exact mdifferentiableAt_localFrameCoeff
      (I := I) (e := e) (b := b) (s := fun y => A y (e.localFrame b i y)) hx happ i
  let term : ι → M → ℝ := fun i y =>
    (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))
  have hsumDiff (s : Finset ι) :
      MDiffAt (fun y => ∑ i ∈ s, term i y) x := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (mdifferentiableAt_const (c := (0 : ℝ)) (x := x))
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        convert (hterm i).add ih using 1 <;> ext y <;> rfl
  have hsum (s : Finset ι) :
      mvfderiv (I := I) (fun y => ∑ i ∈ s, term i y) x =
        ∑ i ∈ s, mvfderiv (I := I) (term i) x := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [mvfderiv_const]
    | @insert i s hi ih =>
        have hiDiff : MDiffAt (term i) x := hterm i
        have hsDiff : MDiffAt (fun y => ∑ j ∈ s, term j y) x := hsumDiff s
        simp only [Finset.sum_insert hi]
        rw [show (fun y => term i y + ∑ j ∈ s, term j y) =
          term i + (fun y => ∑ j ∈ s, term j y) by rfl]
        rw [mvfderiv_add (I := I) hiDiff hsDiff, ih]
  simpa [term] using congrArg (fun L => L u) (hsum Finset.univ)

/-- Local-frame expansion of the derivative of trace.  The first finite sum
is the trace of the covariant derivatives of the columns of `A`; the second
is the connection-coefficient correction that cancels against the source
connection in the induced endomorphism connection. -/
theorem mvfderiv_endomorphismTrace_apply_eq_sum_covariantDerivative_sub
    (cov : CovariantDerivative I F V)
    {A : ∀ x : M, VEnd x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (F →L[ℝ] F) (E := VEnd) y (A y)) x)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F) (hx : x ∈ e.baseSet) (u : TM x) :
    mvfderiv (I := I) (endomorphismTrace (F := F) (V := V) A) x u =
      (∑ i : ι, (e.localFrameCoeff I b i x)
        (cov (fun y => A y (e.localFrame b i y)) x u)) -
      ∑ i : ι, ∑ j : ι,
        (e.localFrameCoeff I b j x) (A x (e.localFrame b i x)) *
          (e.localFrameCoeff I b i x) (cov (e.localFrame b j) x u) := by
  rw [mvfderiv_endomorphismTrace_apply_eq_sum_localFrame
    (I := I) (F := F) (V := V) hA e b hx u]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hframe : MDiffAt (T% (e.localFrame b i)) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have happ : MDiffAt (T% (fun y => A y (e.localFrame b i y))) x :=
    hA.clm_bundle_apply hframe
  have hcoord := localFrameCoeff_covariantDerivative
    (I₀ := I) (e := e) (b := b) (cov := cov) hx happ u i
  simp only [LinearMap.piApply_apply] at hcoord
  exact eq_sub_iff_add_eq.mpr hcoord.symm

/-- If a differentiable section vanishes at a point, differentiating its
image under a differentiable endomorphism section has no derivative-of-`A`
term there.  This is the intrinsic bundle version of
`d(Aσ) = (dA)σ + A(dσ)` at `σ(x) = 0`. -/
theorem covariantDerivative_apply_endomorphism_of_section_eq_zero
    (cov : CovariantDerivative I F V)
    {A : ∀ x : M, VEnd x} {σ : ∀ x : M, V x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (F →L[ℝ] F) (E := VEnd) y (A y)) x)
    (hσ : MDiffAt (T% σ) x) (hσx : σ x = 0) (u : TM x) :
    cov (fun y => A y (σ y)) x u = A x (cov σ x u) := by
  classical
  let e : Trivialization F (TotalSpace.proj : TotalSpace F V → M) :=
    trivializationAt F V x
  let b : Module.Basis (Fin (Module.finrank ℝ F)) ℝ F := Module.finBasis ℝ F
  let c : Fin (Module.finrank ℝ F) → M → ℝ := fun i y =>
    (e.localFrameCoeff I b i y) (σ y)
  let frame : Fin (Module.finrank ℝ F) → ∀ y : M, V y := fun i => e.localFrame b i
  let imageFrame : Fin (Module.finrank ℝ F) → ∀ y : M, V y := fun i y =>
    A y (frame i y)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hframe : ∀ i, MDiffAt (T% (frame i)) x := by
    intro i
    exact (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have hc : ∀ i, MDiffAt (c i) x := by
    intro i
    exact mdifferentiableAt_localFrameCoeff
      (I := I) (e := e) (b := b) (s := σ) hx hσ i
  have hcx : ∀ i, c i x = 0 := by
    intro i
    simp [c, hσx]
  have himageFrame : ∀ i, MDiffAt (T% (imageFrame i)) x := by
    intro i
    exact hA.clm_bundle_apply (hframe i)
  have hsumFrame : MDiffAt (T% (∑ i, c i • frame i)) x := by
    have h := MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ F))))
      (fun i _ => (hc i).smul_section (hframe i))
    convert h using 1 <;> ext y <;> simp
  have hsumImageFrame : MDiffAt (T% (∑ i, c i • imageFrame i)) x := by
    have h := MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ F))))
      (fun i _ => (hc i).smul_section (himageFrame i))
    convert h using 1 <;> ext y <;> simp
  have heventσ : ∀ᶠ y in nhds x, σ y = (∑ i, c i • frame i) y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    simpa [c, frame] using
      (e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := σ) (x' := y) hy)
  have heventImage : ∀ᶠ y in nhds x,
      A y (σ y) = (∑ i, c i • imageFrame i) y := by
    filter_upwards [heventσ] with y hy
    rw [hy]
    simp [imageFrame, frame]
  have hAσ : MDiffAt (T% (fun y => A y (σ y))) x := hA.clm_bundle_apply hσ
  have hcovσ := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv) hσ hsumFrame
    (Filter.univ_mem) heventσ
  have hcovImage := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv) hAσ hsumImageFrame
    (Filter.univ_mem) heventImage
  have hsumσ := covariantDerivative_sum_smul_apply
    (I := I) cov c frame hc hframe u
  have hsumImage := covariantDerivative_sum_smul_apply
    (I := I) cov c imageFrame hc himageFrame u
  have hcovσu := congrArg (fun L : TM x →L[ℝ] V x => L u) hcovσ
  have hcovImageu := congrArg (fun L : TM x →L[ℝ] V x => L u) hcovImage
  rw [hcovImageu, hsumImage, hcovσu, hsumσ]
  simp [hcx, imageFrame, frame, map_sum]

/-- The connection induced on the endomorphism bundle satisfies the genuine
evaluation product rule.  The proof reduces an arbitrary section to its
canonical smooth extension plus a section vanishing at the base point, then
uses the preceding local-frame lemma on the vanishing remainder. -/
theorem inducedHomCovariantDerivative_apply_section
    [IsManifold I ∞ M] [∀ y : M, FiniteDimensional ℝ (V y)]
    (cov : CovariantDerivative I F V)
    {A : ∀ x : M, VEnd x} {σ : ∀ x : M, V x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (F →L[ℝ] F) (E := VEnd) y (A y)) x)
    (hσ : MDiffAt (T% σ) x) (u : TM x) :
    (inducedHomCovariantDerivative cov cov A x u) (σ x) =
      cov (fun y => A y (σ y)) x u - A x (cov σ x u) := by
  classical
  let q : ∀ y : M, V y :=
    smoothExtend (I := I) (F := F) (V := V) x (σ x)
  let δ : ∀ y : M, V y := σ - q
  have hq : MDiffAt (T% q) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x (σ x)).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hδ : MDiffAt (T% δ) x := mdifferentiableAt_sub_section hσ hq
  have hδx : δ x = 0 := by simp [δ, q, smoothExtend_apply]
  have hAq : MDiffAt (T% (fun y => A y (q y))) x := hA.clm_bundle_apply hq
  have hAδ : MDiffAt (T% (fun y => A y (δ y))) x := hA.clm_bundle_apply hδ
  have hAσ : MDiffAt (T% (fun y => A y (σ y))) x := hA.clm_bundle_apply hσ
  have hqδ : MDiffAt (T% (q + δ)) x := mdifferentiableAt_add_section hq hδ
  have hAqAδ : MDiffAt
      (T% ((fun y => A y (q y)) + fun y => A y (δ y))) x :=
    mdifferentiableAt_add_section hAq hAδ
  have heventσ : ∀ᶠ y in nhds x, (q + δ) y = σ y := by
    filter_upwards [] with y
    simp [δ]
  have heventA : ∀ᶠ y in nhds x,
      ((fun z => A z (q z)) + fun z => A z (δ z)) y = A y (σ y) := by
    filter_upwards [] with y
    simp [δ, map_sub]
  have hcovqδ := cov.isCovariantDerivativeOn.add hq hδ (x := x)
  have hcovAqAδ := cov.isCovariantDerivativeOn.add hAq hAδ (x := x)
  have hcovσeq := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv) hqδ hσ Filter.univ_mem heventσ
  have hcovAeq := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv) hAqAδ hAσ Filter.univ_mem heventA
  have hzero := covariantDerivative_apply_endomorphism_of_section_eq_zero
    (I := I) cov hA hδ hδx u
  have hcovqδu := congrArg (fun L : TM x →L[ℝ] V x => L u) hcovqδ
  have hcovAqAδu := congrArg (fun L : TM x →L[ℝ] V x => L u) hcovAqAδ
  have hcovσequ := congrArg (fun L : TM x →L[ℝ] V x => L u) hcovσeq
  have hcovAequ := congrArg (fun L : TM x →L[ℝ] V x => L u) hcovAeq
  rw [inducedHomCovariantDerivative_apply_of_mdifferentiableAt cov cov hA,
    inducedHomAtOfMDiff_apply]
  change cov (fun y => A y (q y)) x u - A x (cov q x u) = _
  simp only [add_apply] at hcovqδu hcovAqAδu
  rw [← hcovσequ, hcovqδu, ← hcovAequ, hcovAqAδu, map_add, hzero]
  abel

/-- The two double sums occurring in the trace computation agree after
interchanging their dummy frame indices. -/
theorem sum_mul_swap_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a Γ : ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, a j i * Γ i j) =
      ∑ i : ι, ∑ j : ι, Γ j i * a i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- Fibrewise trace commutes with the connection induced on the endomorphism
bundle.  This is the intrinsic contraction theorem needed to differentiate
Ricci and scalar curvature; all connection-coefficient terms are exhibited
in a genuine local frame and cancelled by reindexing. -/
theorem mvfderiv_endomorphismTrace_eq_trace_inducedHom
    [IsManifold I ∞ M] [∀ y : M, FiniteDimensional ℝ (V y)]
    (cov : CovariantDerivative I F V)
    {A : ∀ x : M, VEnd x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (F →L[ℝ] F) (E := VEnd) y (A y)) x)
    (u : TM x) :
    mvfderiv (I := I) (endomorphismTrace (F := F) (V := V) A) x u =
      LinearMap.trace ℝ (V x)
        ((inducedHomCovariantDerivative cov cov A x u).toLinearMap) := by
  classical
  let e : Trivialization F (TotalSpace.proj : TotalSpace F V → M) :=
    trivializationAt F V x
  let b : Module.Basis (Fin (Module.finrank ℝ F)) ℝ F := Module.finBasis ℝ F
  let frame : Fin (Module.finrank ℝ F) → ∀ y : M, V y := fun i => e.localFrame b i
  let nablaA : TM x →L[ℝ] VEnd x := inducedHomCovariantDerivative cov cov A x
  let a : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) → ℝ := fun i j =>
    (e.localFrameCoeff I b i x) (A x (frame j x))
  let Γ : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) → ℝ := fun i j =>
    (e.localFrameCoeff I b i x) (cov (frame j) x u)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hframe : ∀ i, MDiffAt (T% (frame i)) x := by
    intro i
    exact (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have hd := mvfderiv_endomorphismTrace_apply_eq_sum_covariantDerivative_sub
    (I := I) (F := F) (V := V) cov hA e b hx u
  have hproduct : ∀ i,
      cov (fun y => A y (frame i y)) x u =
        nablaA u (frame i x) + A x (cov (frame i) x u) := by
    intro i
    have h := inducedHomCovariantDerivative_apply_section
      (I := I) cov hA (hframe i) u
    exact (eq_sub_iff_add_eq.mp h).symm
  have hfirst :
      (∑ i, (e.localFrameCoeff I b i x)
        (cov (fun y => A y (frame i y)) x u)) =
      (∑ i, (e.localFrameCoeff I b i x) (nablaA u (frame i x))) +
        ∑ i, (e.localFrameCoeff I b i x) (A x (cov (frame i) x u)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hproduct i, map_add]
  have hdecompose : ∀ i,
      cov (frame i) x u = ∑ j, Γ j i • frame j x := by
    intro i
    let w : V x := cov (frame i) x u
    have hcoeff : ∀ j,
        (e.localFrameCoeff I b j x) w = (e.basisAt b hx).repr w j := by
      intro j
      simpa [smoothExtend_apply] using
        (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
          (I := I) (e := e) (b := b) hx
          (smoothExtend (I := I) (F := F) (V := V) x w) j)
    calc
      cov (frame i) x u = w := rfl
      _ = ∑ j, (e.basisAt b hx).repr w j • (e.basisAt b hx) j :=
        ((e.basisAt b hx).sum_repr w).symm
      _ = ∑ j, Γ j i • frame j x := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hcoeff j]
        simp only [Γ, w, frame]
        rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := e) (b := b) hx]
  have hconnection :
      (∑ i, (e.localFrameCoeff I b i x) (A x (cov (frame i) x u))) =
        ∑ i, ∑ j, Γ j i * a i j := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdecompose i, map_sum]
    simp [a, map_smul, smul_eq_mul]
  let B : ∀ y : M, VEnd y :=
    smoothExtend (I := I) (F := F →L[ℝ] F) (V := VEnd) x (nablaA u)
  have htrace := endomorphismTrace_eq_sum_localFrame
    (I := I) (F := F) (V := V) B e b hx
  have htrace' :
      LinearMap.trace ℝ (V x) (nablaA u).toLinearMap =
        ∑ i, (e.localFrameCoeff I b i x) (nablaA u (frame i x)) := by
    simpa [B, nablaA, frame, smoothExtend_apply, endomorphismTrace] using htrace
  rw [hd, hfirst, hconnection, ← htrace']
  rw [sum_mul_swap_eq a Γ]
  simp [a, Γ, nablaA, frame]

end CovariantDerivative
