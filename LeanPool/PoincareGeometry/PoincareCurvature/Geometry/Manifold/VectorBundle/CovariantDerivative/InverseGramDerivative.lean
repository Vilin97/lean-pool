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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLocalFrame

/-!
# Spatial derivatives of inverse local Gram matrices

This file records the inverse-metric derivative in a genuine local tangent
frame. The proof is entrywise, so it does not choose an ambient norm on the
matrix algebra.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Matrix Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)

omit [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
/-- Differentiating a local inverse relation entrywise gives the usual
inverse-matrix derivative, applied to the tangent vector `X`. -/
theorem matrix_inverse_mvfderiv_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : M → Matrix ι ι ℝ} {x : M}
    (hA : ∀ i j, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => A y i j) x)
    (hB : ∀ i j, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => B y i j) x)
    (hAB : ∀ᶠ y in 𝓝 x, A y * B y = 1)
    (hBA : B x * A x = 1)
    (X : TM x) :
    (show Matrix ι ι ℝ from fun i j => mvfderiv (I := I) (fun y => B y i j) x X) =
      -(B x *
        (show Matrix ι ι ℝ from fun i j => mvfderiv (I := I) (fun y => A y i j) x X) *
        B x) := by
  let Adot : Matrix ι ι ℝ := fun i j => mvfderiv (I := I) (fun y => A y i j) x X
  let Bdot : Matrix ι ι ℝ := fun i j => mvfderiv (I := I) (fun y => B y i j) x X
  have mvfderiv_eq_of_eventuallyEq_local
      {f g : M → ℝ} (hfg : f =ᶠ[𝓝 x] g) :
      mvfderiv (I := I) f x = mvfderiv (I := I) g x := by
    unfold mvfderiv
    rw [hfg.eq_of_nhds, hfg.mfderiv_eq]
  have hvariation : A x * Bdot + Adot * B x = 0 := by
    ext i j
    let term : ι → M → ℝ := fun k y => A y i k * B y k j
    have htermDiff : ∀ k : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (term k) x := by
      intro k
      change MDifferentiableAt I 𝓘(ℝ, ℝ)
        ((fun y : M => A y i k) * fun y : M => B y k j) x
      exact (hA i k).mul (hB k j)
    have hsumDiff (s : Finset ι) :
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ k ∈ s, term k y) x := by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using (mdifferentiableAt_const (c := (0 : ℝ)) (x := x))
      | @insert k s hks ih =>
          simp only [Finset.sum_insert hks]
          rw [show (fun y => term k y + ∑ l ∈ s, term l y) =
            term k + (fun y => ∑ l ∈ s, term l y) by rfl]
          exact (htermDiff k).add ih
    have hsum (s : Finset ι) :
        mvfderiv (I := I) (fun y => ∑ k ∈ s, term k y) x =
          ∑ k ∈ s, mvfderiv (I := I) (term k) x := by
      classical
      induction s using Finset.induction_on with
      | empty => simp [mvfderiv_const]
      | @insert k s hks ih =>
          have hkDiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (term k) x := htermDiff k
          have hsDiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
              (fun y => ∑ l ∈ s, term l y) x := hsumDiff s
          simp only [Finset.sum_insert hks]
          rw [show (fun y => term k y + ∑ l ∈ s, term l y) =
            term k + (fun y => ∑ l ∈ s, term l y) by rfl]
          rw [mvfderiv_add (I := I) hkDiff hsDiff, ih]
    have htermDeriv (k : ι) :
        mvfderiv (I := I) (term k) x X =
          A x i k * mvfderiv (I := I) (fun y => B y k j) x X +
            B x k j * mvfderiv (I := I) (fun y => A y i k) x X := by
      have hmul := congrArg (fun L : TM x →L[ℝ] ℝ => L X)
        (mvfderiv_mul (I := I) (hA i k) (hB k j))
      change mvfderiv (I := I)
        ((fun y : M => A y i k) * fun y : M => B y k j) x X = _
      simpa [smul_eq_mul] using hmul
    have heq : (fun y => (A y * B y) i j) =ᶠ[𝓝 x]
        (fun _ : M => (1 : Matrix ι ι ℝ) i j) := by
      filter_upwards [hAB] with y hy
      simp [hy]
    have hmv : mvfderiv (I := I) (fun y => (A y * B y) i j) x =
        mvfderiv (I := I) (fun _ : M => (1 : Matrix ι ι ℝ) i j) x := by
      exact mvfderiv_eq_of_eventuallyEq_local heq
    have hzero : mvfderiv (I := I) (fun y => (A y * B y) i j) x X = 0 := by
      calc
        mvfderiv (I := I) (fun y => (A y * B y) i j) x X =
            mvfderiv (I := I) (fun _ : M => (1 : Matrix ι ι ℝ) i j) x X :=
          congrArg (fun L : TM x →L[ℝ] ℝ => L X) hmv
        _ = 0 := by simp [mvfderiv_const]
    have hsumApply :
        mvfderiv (I := I) (fun y => ∑ k : ι, term k y) x X =
          ∑ k : ι, mvfderiv (I := I) (term k) x X := by
      simpa using congrArg (fun L : TM x →L[ℝ] ℝ => L X) (hsum Finset.univ)
    have hzeroSum :
        mvfderiv (I := I) (fun y => ∑ k : ι, term k y) x X = 0 := by
      simpa [term, Matrix.mul_apply] using hzero
    calc
      (A x * Bdot + Adot * B x) i j =
          ∑ k : ι,
            (A x i k * mvfderiv (I := I) (fun y => B y k j) x X +
              B x k j * mvfderiv (I := I) (fun y => A y i k) x X) := by
        change
          (∑ k : ι, A x i k * mvfderiv (I := I) (fun y => B y k j) x X) +
              ∑ k : ι, mvfderiv (I := I) (fun y => A y i k) x X * B x k j = _
        rw [Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k : ι, mvfderiv (I := I) (term k) x X := by
        apply Finset.sum_congr rfl
        intro k _
        exact (htermDeriv k).symm
      _ = mvfderiv (I := I) (fun y => ∑ k : ι, term k y) x X := hsumApply.symm
      _ = 0 := hzeroSum
  have hsolve : A x * Bdot = -(Adot * B x) :=
    eq_neg_of_add_eq_zero_left hvariation
  change Bdot = -(B x * Adot * B x)
  calc
    Bdot = (B x * A x) * Bdot := by rw [hBA, one_mul]
    _ = B x * (A x * Bdot) := by rw [mul_assoc]
    _ = B x * (-(Adot * B x)) := by rw [hsolve]
    _ = -(B x * Adot * B x) := by simp [mul_assoc]

omit [T2Space M] in
/-- In a genuine local tangent frame, the directional derivative of the
inverse Gram matrix is `-G⁻¹ (dG) G⁻¹`. -/
theorem mvfderiv_localFrameInverseGramMatrix_apply
    [RiemannianBundle TM]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (X : TM x) (i j : ι) :
    mvfderiv (I := I)
        (fun y => localFrameInverseGramMatrix (I := I) e b y i j) x X =
      (-(
        (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ *
          (show Matrix ι ι ℝ from fun k l => mvfderiv (I := I)
            (fun y => localFrameGramMatrix (I := I) e b y k l) x X) *
          (show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹)) i j := by
  let G : M → Matrix ι ι ℝ := fun y => localFrameGramMatrix (I := I) e b y
  let Ginv : M → Matrix ι ι ℝ := fun y => (G y)⁻¹
  have hGramEntry : ∀ k l, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => G y k l) x := by
    intro k l
    have hGram := contMDiffOn_localFrameGramMatrix (I := I) (E := E) e b
      e.open_baseSet (fun _ hy => hy)
    rw [contMDiffOn_pi_space] at hGram
    have hk := hGram k
    rw [contMDiffOn_pi_space] at hk
    exact (hk l x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
      |>.mdifferentiableAt (by norm_num)
  have hInvEntry : ∀ k l, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Ginv y k l) x := by
    intro k l
    have hInv := contMDiffOn_localFrameGramMatrix_inv (I := I) (E := E) e b
      e.open_baseSet (fun _ hy => hy)
    rw [contMDiffOn_pi_space] at hInv
    have hk := hInv k
    rw [contMDiffOn_pi_space] at hk
    exact (hk l x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
      |>.mdifferentiableAt (by norm_num)
  have hAB : ∀ᶠ y in 𝓝 x, G y * Ginv y = 1 := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact Matrix.mul_nonsing_inv (G y) (isUnit_iff_ne_zero.mpr
      (localFrameGramMatrix_det_ne_zero (I := I) (E := E) e b hy))
  have hBA : Ginv x * G x = 1 :=
    Matrix.nonsing_inv_mul (G x) (isUnit_iff_ne_zero.mpr
      (localFrameGramMatrix_det_ne_zero (I := I) (E := E) e b hx))
  have hformula := matrix_inverse_mvfderiv_apply hGramEntry hInvEntry hAB hBA X
  have hij := congrFun (congrFun hformula i) j
  simpa [G, Ginv, localFrameInverseGramMatrix] using hij

end CovariantDerivative
