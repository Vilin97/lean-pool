/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpaceCore
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Operator.Prod
/-!
# Higher parabolic Holder function spaces

This module starts the coordinate-level `C^{2+α,1+α/2}` side of the
Ricci-DeTurck analytic setup.  It records actual spatial and time derivative
witnesses together with the `ParabolicC0AlphaNormLe` controls that the matrix
RHS estimates consume.  It deliberately does not assert Schauder estimates.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous-linear packaging of two first-spatial derivative maps as the derivative of a
product-valued function. -/
def firstDerivativeProdLinearMap (X E F : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ((X →L[ℝ] E) × (X →L[ℝ] F)) →L[ℝ] (X →L[ℝ] E × F) :=
  ((ContinuousLinearMap.prodₗᵢ ℝ :
    ((X →L[ℝ] E) × (X →L[ℝ] F)) ≃ₗᵢ[ℝ] (X →L[ℝ] E × F)) :
      ((X →L[ℝ] E) × (X →L[ℝ] F)) →L[ℝ] (X →L[ℝ] E × F))

namespace ParabolicSecondJet

variable {u : ℝ × X → E} {s : Set (ℝ × X)}

/-- Constant parabolic second jet. -/
def const (c : E) : ParabolicSecondJet (fun _ : ℝ × X => c) s where
  timeDeriv := fun _ => 0
  spaceDeriv := fun _ => 0
  spaceSecondDeriv := fun _ => 0
  hasTimeDeriv := by
    intro z _hz
    simpa using hasDerivWithinAt_const (𝕜 := ℝ) z.1 (timeSliceDomain s z.2) c
  hasSpaceDeriv := by
    intro z _hz
    simpa using hasFDerivWithinAt_const (𝕜 := ℝ) c z.2 (spaceSliceDomain s z.1)
  hasSpaceSecondDeriv := by
    intro z _hz
    simpa using
      hasFDerivWithinAt_const (𝕜 := ℝ) (0 : X →L[ℝ] E) z.2 (spaceSliceDomain s z.1)

theorem timeDeriv_hasDerivWithinAt (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (J.timeDeriv z)
      (timeSliceDomain s z.2) z.1 :=
  J.hasTimeDeriv hz

theorem spaceDeriv_hasFDerivWithinAt (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    HasFDerivWithinAt (fun x : X => u (z.1, x)) (J.spaceDeriv z)
      (spaceSliceDomain s z.1) z.2 :=
  J.hasSpaceDeriv hz

theorem spaceSecondDeriv_hasFDerivWithinAt (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    HasFDerivWithinAt (fun x : X => J.spaceDeriv (z.1, x)) (J.spaceSecondDeriv z)
      (spaceSliceDomain s z.1) z.2 :=
  J.hasSpaceSecondDeriv hz

theorem timeDeriv_eq_derivWithin (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s)
    (hunique : UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1) :
    J.timeDeriv z = derivWithin (fun t : ℝ => u (t, z.2)) (timeSliceDomain s z.2) z.1 :=
  ((J.hasTimeDeriv hz).derivWithin hunique).symm

theorem spaceDeriv_eq_fderivWithin (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s)
    (hunique : UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    J.spaceDeriv z =
      fderivWithin ℝ (fun x : X => u (z.1, x)) (spaceSliceDomain s z.1) z.2 :=
  ((J.hasSpaceDeriv hz).fderivWithin hunique).symm

theorem spaceSecondDeriv_eq_fderivWithin (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s)
    (hunique : UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    J.spaceSecondDeriv z =
      fderivWithin ℝ (fun x : X => J.spaceDeriv (z.1, x))
        (spaceSliceDomain s z.1) z.2 :=
  ((J.hasSpaceSecondDeriv hz).fderivWithin hunique).symm

theorem timeDeriv_eq_of_unique (J K : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s)
    (hunique : UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1) :
    J.timeDeriv z = K.timeDeriv z :=
  hunique.eq_deriv _ (J.hasTimeDeriv hz) (K.hasTimeDeriv hz)

theorem spaceDeriv_eq_of_unique (J K : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s)
    (hunique : UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    J.spaceDeriv z = K.spaceDeriv z :=
  hunique.eq (J.hasSpaceDeriv hz) (K.hasSpaceDeriv hz)

theorem spaceDeriv_eqOn_of_unique (J K : ParabolicSecondJet u s) {t : ℝ}
    (hunique : ∀ ⦃x : X⦄, (t, x) ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s t) x) :
    EqOn (fun x : X => J.spaceDeriv (t, x)) (fun x : X => K.spaceDeriv (t, x))
      (spaceSliceDomain s t) := by
  intro x hx
  exact J.spaceDeriv_eq_of_unique K hx (hunique hx)

theorem spaceSecondDeriv_eq_of_unique (J K : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s)
    (hunique : ∀ ⦃x : X⦄, (z.1, x) ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) x) :
    J.spaceSecondDeriv z = K.spaceSecondDeriv z := by
  have hEqOn :
      EqOn (fun x : X => J.spaceDeriv (z.1, x))
        (fun x : X => K.spaceDeriv (z.1, x)) (spaceSliceDomain s z.1) :=
    J.spaceDeriv_eqOn_of_unique K hunique
  have hz_space : z.2 ∈ spaceSliceDomain s z.1 := by
    simpa [spaceSliceDomain] using hz
  have hK :
      HasFDerivWithinAt (fun x : X => J.spaceDeriv (z.1, x))
        (K.spaceSecondDeriv z) (spaceSliceDomain s z.1) z.2 :=
    (K.hasSpaceSecondDeriv hz).congr hEqOn (hEqOn hz_space)
  exact (hunique hz).eq (J.hasSpaceSecondDeriv hz) hK

/-- Sum of two parabolic second jets, with derivative witnesses added componentwise. -/
def add {v : ℝ × X → E} (Ju : ParabolicSecondJet u s) (Jv : ParabolicSecondJet v s) :
    ParabolicSecondJet (fun z : ℝ × X => u z + v z) s where
  timeDeriv := fun z => Ju.timeDeriv z + Jv.timeDeriv z
  spaceDeriv := fun z => Ju.spaceDeriv z + Jv.spaceDeriv z
  spaceSecondDeriv := fun z => Ju.spaceSecondDeriv z + Jv.spaceSecondDeriv z
  hasTimeDeriv := by
    intro z hz
    convert (Ju.hasTimeDeriv hz).add (Jv.hasTimeDeriv hz) using 1 <;> rfl
  hasSpaceDeriv := by
    intro z hz
    convert (Ju.hasSpaceDeriv hz).add (Jv.hasSpaceDeriv hz) using 1 <;> rfl
  hasSpaceSecondDeriv := by
    intro z hz
    convert (Ju.hasSpaceSecondDeriv hz).add (Jv.hasSpaceSecondDeriv hz) using 1 <;> rfl

/-- Negation of a parabolic second jet. -/
def neg (J : ParabolicSecondJet u s) :
    ParabolicSecondJet (fun z : ℝ × X => -u z) s where
  timeDeriv := fun z => -J.timeDeriv z
  spaceDeriv := fun z => -J.spaceDeriv z
  spaceSecondDeriv := fun z => -J.spaceSecondDeriv z
  hasTimeDeriv := by
    intro z hz
    simpa using (J.hasTimeDeriv hz).fun_neg
  hasSpaceDeriv := by
    intro z hz
    simpa using (J.hasSpaceDeriv hz).fun_neg
  hasSpaceSecondDeriv := by
    intro z hz
    simpa using (J.hasSpaceSecondDeriv hz).fun_neg

/-- Scalar multiplication of a parabolic second jet. -/
def smul (c : ℝ) (J : ParabolicSecondJet u s) :
    ParabolicSecondJet (fun z : ℝ × X => c • u z) s where
  timeDeriv := fun z => c • J.timeDeriv z
  spaceDeriv := fun z => c • J.spaceDeriv z
  spaceSecondDeriv := fun z => c • J.spaceSecondDeriv z
  hasTimeDeriv := by
    intro z hz
    simpa using HasDerivWithinAt.fun_const_smul c (J.hasTimeDeriv hz)
  hasSpaceDeriv := by
    intro z hz
    simpa using (J.hasSpaceDeriv hz).fun_const_smul c
  hasSpaceSecondDeriv := by
    intro z hz
    simpa [Pi.smul_apply] using (J.hasSpaceSecondDeriv hz).fun_const_smul c

/-- Difference of two parabolic second jets, with derivative witnesses subtracted
componentwise. -/
def sub {v : ℝ × X → E} (Ju : ParabolicSecondJet u s) (Jv : ParabolicSecondJet v s) :
    ParabolicSecondJet (fun z : ℝ × X => u z - v z) s where
  timeDeriv := fun z => Ju.timeDeriv z - Jv.timeDeriv z
  spaceDeriv := fun z => Ju.spaceDeriv z - Jv.spaceDeriv z
  spaceSecondDeriv := fun z => Ju.spaceSecondDeriv z - Jv.spaceSecondDeriv z
  hasTimeDeriv := by
    intro z hz
    convert (Ju.hasTimeDeriv hz).sub (Jv.hasTimeDeriv hz) using 1 <;> rfl
  hasSpaceDeriv := by
    intro z hz
    convert (Ju.hasSpaceDeriv hz).sub (Jv.hasSpaceDeriv hz) using 1 <;> rfl
  hasSpaceSecondDeriv := by
    intro z hz
    convert (Ju.hasSpaceSecondDeriv hz).sub (Jv.hasSpaceSecondDeriv hz) using 1 <;> rfl

/-- Product of two parabolic second jets, with derivative witnesses paired componentwise. -/
def prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {v : ℝ × X → F}
    (Ju : ParabolicSecondJet u s) (Jv : ParabolicSecondJet v s) :
    ParabolicSecondJet (fun z : ℝ × X => (u z, v z)) s where
  timeDeriv := fun z => (Ju.timeDeriv z, Jv.timeDeriv z)
  spaceDeriv := fun z =>
    firstDerivativeProdLinearMap X E F (Ju.spaceDeriv z, Jv.spaceDeriv z)
  spaceSecondDeriv := fun z =>
    (firstDerivativeProdLinearMap X E F).comp
      ((Ju.spaceSecondDeriv z).prod (Jv.spaceSecondDeriv z))
  hasTimeDeriv := by
    intro z hz
    exact HasDerivWithinAt.prodMk (Ju.hasTimeDeriv hz) (Jv.hasTimeDeriv hz)
  hasSpaceDeriv := by
    intro z hz
    convert (Ju.hasSpaceDeriv hz).prodMk (Jv.hasSpaceDeriv hz) using 1
    all_goals try rfl
  hasSpaceSecondDeriv := by
    intro z hz
    let Lprod : ((X →L[ℝ] E) × (X →L[ℝ] F)) →L[ℝ] (X →L[ℝ] E × F) :=
      firstDerivativeProdLinearMap X E F
    have hpair :
        HasFDerivWithinAt
          (fun x : X => (Ju.spaceDeriv (z.1, x), Jv.spaceDeriv (z.1, x)))
          ((Ju.spaceSecondDeriv z).prod (Jv.spaceSecondDeriv z))
          (spaceSliceDomain s z.1) z.2 := by
      exact (Ju.hasSpaceSecondDeriv hz).prodMk (Jv.hasSpaceSecondDeriv hz)
    have hcomp := Lprod.hasFDerivAt.comp_hasFDerivWithinAt z.2 hpair
    convert hcomp using 1 <;> rfl

/-- Compose a parabolic second jet with a continuous linear value map. -/
def continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (J : ParabolicSecondJet u s) :
    ParabolicSecondJet (fun z : ℝ × X => L (u z)) s where
  timeDeriv := fun z => L (J.timeDeriv z)
  spaceDeriv := fun z => L.comp (J.spaceDeriv z)
  spaceSecondDeriv := fun z =>
    (ContinuousLinearMap.compL ℝ X (X →L[ℝ] E) (X →L[ℝ] F)
      (ContinuousLinearMap.compL ℝ X E F L)) (J.spaceSecondDeriv z)
  hasTimeDeriv := by
    intro z hz
    have hcomp :=
      L.hasFDerivAt.comp_hasFDerivWithinAt z.1 (J.hasTimeDeriv hz).hasFDerivWithinAt
    convert hcomp.hasDerivWithinAt using 1
    all_goals try rfl
    simp
  hasSpaceDeriv := by
    intro z hz
    have hcomp := L.hasFDerivAt.comp_hasFDerivWithinAt z.2 (J.hasSpaceDeriv hz)
    convert hcomp using 1 <;> rfl
  hasSpaceSecondDeriv := by
    intro z hz
    let A : (X →L[ℝ] E) →L[ℝ] (X →L[ℝ] F) :=
      ContinuousLinearMap.compL ℝ X E F L
    have hcomp := A.hasFDerivAt.comp_hasFDerivWithinAt z.2 (J.hasSpaceSecondDeriv hz)
    convert hcomp using 1 <;> rfl

end ParabolicSecondJet

namespace ParabolicC2AlphaNormLe

variable {N N' α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}

theorem const (c : E) :
    ParabolicC2AlphaNormLe ‖c‖ α (fun _ : ℝ × X => c) s := by
  refine ⟨ParabolicSecondJet.const (X := X) (s := s) c, ‖c‖, norm_nonneg c,
    0, le_rfl, 0, le_rfl, 0, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · exact ParabolicC0AlphaNormLe.const (X := X) (α := α) (s := s) c
  · exact ParabolicC0AlphaNormLe.zero (X := X) (E := X →L[ℝ] E) (α := α) (s := s)
  · exact
      ParabolicC0AlphaNormLe.zero
        (X := X) (E := X →L[ℝ] (X →L[ℝ] E)) (α := α) (s := s)
  · exact ParabolicC0AlphaNormLe.zero (X := X) (E := E) (α := α) (s := s)

theorem zero :
    ParabolicC2AlphaNormLe 0 α (fun _ : ℝ × X => (0 : E)) s := by
  simpa using (const (X := X) (E := E) (α := α) (s := s) (0 : E))

theorem mono_set {t : Set (ℝ × X)} (h : ParabolicC2AlphaNormLe N α u s) (hst : t ⊆ s) :
    ParabolicC2AlphaNormLe N α u t := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J.restrict hst, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum,
    hu.mono_set hst, hx.mono_set hst, hxx.mono_set hst, ht.mono_set hst⟩

theorem add {v : ℝ × X → E} {M : ℝ}
    (hu : ParabolicC2AlphaNormLe N α u s) (hv : ParabolicC2AlphaNormLe M α v s) :
    ParabolicC2AlphaNormLe (N + M) α (fun z : ℝ × X => u z + v z) s := by
  rcases hu with
    ⟨Ju, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsumu, huu, hxu, hxxu, htu⟩
  rcases hv with
    ⟨Jv, Mu, hMu, Mx, hMx, Mxx, hMxx, Mt, hMt, hsumv, huv, hxv, hxxv, htv⟩
  refine ⟨Ju.add Jv, Nu + Mu, add_nonneg hNu hMu, Nx + Mx, add_nonneg hNx hMx,
    Nxx + Mxx, add_nonneg hNxx hMxx, Nt + Mt, add_nonneg hNt hMt, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · simpa using huu.add huv
  · simpa [ParabolicSecondJet.add] using hxu.add hxv
  · simpa [ParabolicSecondJet.add] using hxxu.add hxxv
  · simpa [ParabolicSecondJet.add] using htu.add htv

theorem finset_sum {ι : Type*} (S : Finset ι) {N : ι → ℝ}
    {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC2AlphaNormLe (N i) α (u i) s) :
    ParabolicC2AlphaNormLe (∑ i ∈ S, N i) α
      (fun z => ∑ i ∈ S, u i z) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (zero (X := X) (E := E) (α := α) (s := s))
  | insert a S ha ih =>
      have ha_ctrl : ParabolicC2AlphaNormLe (N a) α (u a) s := h a (by simp)
      have hS_ctrl : ParabolicC2AlphaNormLe (∑ i ∈ S, N i) α
          (fun z => ∑ i ∈ S, u i z) s := by
        exact ih fun i hi => h i (by simp [hi])
      have hadd := add ha_ctrl hS_ctrl
      simpa [Finset.sum_insert, ha] using hadd

theorem neg (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaNormLe N α (fun z : ℝ × X => -u z) s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J.neg, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum,
    hu.neg, by simpa [ParabolicSecondJet.neg] using hx.neg,
    by simpa [ParabolicSecondJet.neg] using hxx.neg,
    by simpa [ParabolicSecondJet.neg] using ht.neg⟩

theorem sub {v : ℝ × X → E} {M : ℝ}
    (hu : ParabolicC2AlphaNormLe N α u s) (hv : ParabolicC2AlphaNormLe M α v s) :
    ParabolicC2AlphaNormLe (N + M) α (fun z : ℝ × X => u z - v z) s := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

theorem smul (c : ℝ) (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaNormLe (‖c‖ * N) α (fun z : ℝ × X => c • u z) s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  refine ⟨J.smul c, ‖c‖ * Nu, mul_nonneg (norm_nonneg c) hNu,
    ‖c‖ * Nx, mul_nonneg (norm_nonneg c) hNx,
    ‖c‖ * Nxx, mul_nonneg (norm_nonneg c) hNxx,
    ‖c‖ * Nt, mul_nonneg (norm_nonneg c) hNt, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      ‖c‖ * Nu + ‖c‖ * Nx + ‖c‖ * Nxx + ‖c‖ * Nt =
          ‖c‖ * (Nu + Nx + Nxx + Nt) := by ring
      _ ≤ ‖c‖ * N := mul_le_mul_of_nonneg_left hsum (norm_nonneg c)
  · simpa using hu.smul (𝕜 := ℝ) c
  · simpa [ParabolicSecondJet.smul] using hx.smul (𝕜 := ℝ) c
  · simpa [ParabolicSecondJet.smul] using hxx.smul (𝕜 := ℝ) c
  · simpa [ParabolicSecondJet.smul] using ht.smul (𝕜 := ℝ) c

/-- Radius multiplier for product-valued higher parabolic functions.  The value and time
components and the first spatial derivative use the product isometry directly; the second
spatial derivative only pays for postcomposition by the first-derivative product map. -/
def prodRadius {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] : ℝ :=
  1 + 1 + ‖firstDerivativeProdLinearMap X E F‖ + 1

/-- The product-valued higher parabolic radius multiplier is nonnegative. -/
theorem prodRadius_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    0 ≤ prodRadius (X := X) (E := E) (F := F) := by
  unfold prodRadius
  positivity

theorem prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : ℝ × X → F} {M : ℝ}
    (hu : ParabolicC2AlphaNormLe N α u s) (hv : ParabolicC2AlphaNormLe M α v s) :
    ParabolicC2AlphaNormLe (prodRadius (X := X) (E := E) (F := F) * (N + M)) α
      (fun z : ℝ × X => (u z, v z)) s := by
  rcases hu with
    ⟨Ju, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsumu, huu, hxu, hxxu, htu⟩
  rcases hv with
    ⟨Jv, Mu, hMu, Mx, hMx, Mxx, hMxx, Mt, hMt, hsumv, huv, hxv, hxxv, htv⟩
  let LxIso : ((X →L[ℝ] E) × (X →L[ℝ] F)) ≃ₗᵢ[ℝ]
      (X →L[ℝ] E × F) :=
    ContinuousLinearMap.prodₗᵢ ℝ
  let LxxIso :
      ((X →L[ℝ] (X →L[ℝ] E)) × (X →L[ℝ] (X →L[ℝ] F))) ≃ₗᵢ[ℝ]
        (X →L[ℝ] (X →L[ℝ] E) × (X →L[ℝ] F)) :=
    ContinuousLinearMap.prodₗᵢ ℝ
  let Lx : ((X →L[ℝ] E) × (X →L[ℝ] F)) →L[ℝ] (X →L[ℝ] E × F) :=
    firstDerivativeProdLinearMap X E F
  refine ⟨Ju.prod Jv, Nu + Mu, add_nonneg hNu hMu,
    Nx + Mx, add_nonneg hNx hMx,
    ‖Lx‖ * (Nxx + Mxx),
      mul_nonneg (norm_nonneg Lx) (add_nonneg hNxx hMxx),
    Nt + Mt, add_nonneg hNt hMt, ?_, ?_, ?_, ?_, ?_⟩
  · have hsum_all : (Nu + Mu) + (Nx + Mx) + (Nxx + Mxx) + (Nt + Mt) ≤ N + M := by
      linarith
    have hx₁_le : Nu + Mu ≤ N + M := by linarith
    have hx₂_le : Nx + Mx ≤ N + M := by linarith
    have hx₃_le : Nxx + Mxx ≤ N + M := by linarith
    have hx₄_le : Nt + Mt ≤ N + M := by linarith
    have h₁ : Nu + Mu ≤ 1 * (N + M) := by simpa using hx₁_le
    have h₂ : Nx + Mx ≤ 1 * (N + M) := by simpa using hx₂_le
    have h₃ : ‖Lx‖ * (Nxx + Mxx) ≤ ‖Lx‖ * (N + M) :=
      mul_le_mul_of_nonneg_left hx₃_le (norm_nonneg Lx)
    have h₄ : Nt + Mt ≤ 1 * (N + M) := by simpa using hx₄_le
    calc
      (Nu + Mu) + (Nx + Mx) + ‖Lx‖ * (Nxx + Mxx) + (Nt + Mt)
          ≤ 1 * (N + M) + 1 * (N + M) + ‖Lx‖ * (N + M) + 1 * (N + M) := by
            linarith
      _ = prodRadius (X := X) (E := E) (F := F) * (N + M) := by
            simp [prodRadius, Lx]
            ring
  · simpa using
      ParabolicC0AlphaNormLe.prod (X := X) (E := E) (F := F) huu huv
  · have hx_pair : ParabolicC0AlphaNormLe (Nx + Mx) α
        (fun z : ℝ × X => (Ju.spaceDeriv z, Jv.spaceDeriv z)) s :=
      ParabolicC0AlphaNormLe.prod (X := X) (E := X →L[ℝ] E) (F := X →L[ℝ] F)
        hxu hxv
    have hx_prod :=
      ParabolicC0AlphaNormLe.linearIsometryEquiv (X := X)
        (E := (X →L[ℝ] E) × (X →L[ℝ] F)) (F := X →L[ℝ] E × F)
        LxIso hx_pair
    simpa [ParabolicSecondJet.prod, firstDerivativeProdLinearMap, LxIso] using hx_prod
  · have hxx_pair : ParabolicC0AlphaNormLe (Nxx + Mxx) α
        (fun z : ℝ × X => (Ju.spaceSecondDeriv z, Jv.spaceSecondDeriv z)) s :=
      ParabolicC0AlphaNormLe.prod (X := X)
        (E := X →L[ℝ] (X →L[ℝ] E)) (F := X →L[ℝ] (X →L[ℝ] F)) hxxu hxxv
    have hxx_prod_pair :=
      ParabolicC0AlphaNormLe.linearIsometryEquiv (X := X)
        (E := (X →L[ℝ] (X →L[ℝ] E)) × (X →L[ℝ] (X →L[ℝ] F)))
        (F := X →L[ℝ] (X →L[ℝ] E) × (X →L[ℝ] F)) LxxIso hxx_pair
    have hxx_prod : ParabolicC0AlphaNormLe (‖Lx‖ * (Nxx + Mxx)) α
        (fun z : ℝ × X => Lx.comp (LxxIso (Ju.spaceSecondDeriv z, Jv.spaceSecondDeriv z)))
        s := by
      rcases hxx_prod_pair with ⟨Bxx, hBxx, Hxx, hHxx, hxx_sum, hxx_ctrl⟩
      refine ⟨‖Lx‖ * Bxx, mul_nonneg (norm_nonneg Lx) hBxx,
        ‖Lx‖ * Hxx, mul_nonneg (norm_nonneg Lx) hHxx, ?_, ?_⟩
      · calc
          ‖Lx‖ * Bxx + ‖Lx‖ * Hxx = ‖Lx‖ * (Bxx + Hxx) := by ring
          _ ≤ ‖Lx‖ * (Nxx + Mxx) :=
            mul_le_mul_of_nonneg_left hxx_sum (norm_nonneg Lx)
      · constructor
        · intro p hp
          exact (Lx.opNorm_comp_le (LxxIso (Ju.spaceSecondDeriv p, Jv.spaceSecondDeriv p))).trans
            (mul_le_mul_of_nonneg_left (hxx_ctrl.1 hp) (norm_nonneg Lx))
        · intro p hp q hq
          calc
            ‖Lx.comp (LxxIso (Ju.spaceSecondDeriv p, Jv.spaceSecondDeriv p)) -
                Lx.comp (LxxIso (Ju.spaceSecondDeriv q, Jv.spaceSecondDeriv q))‖ =
                ‖Lx.comp
                  (LxxIso (Ju.spaceSecondDeriv p, Jv.spaceSecondDeriv p) -
                    LxxIso (Ju.spaceSecondDeriv q, Jv.spaceSecondDeriv q))‖ := by
              congr 1
            _ ≤ ‖Lx‖ *
                ‖LxxIso (Ju.spaceSecondDeriv p, Jv.spaceSecondDeriv p) -
                  LxxIso (Ju.spaceSecondDeriv q, Jv.spaceSecondDeriv q)‖ :=
              Lx.opNorm_comp_le
                (LxxIso (Ju.spaceSecondDeriv p, Jv.spaceSecondDeriv p) -
                  LxxIso (Ju.spaceSecondDeriv q, Jv.spaceSecondDeriv q))
            _ ≤ ‖Lx‖ * (Hxx * (parabolicDistance p q) ^ α) :=
              mul_le_mul_of_nonneg_left (hxx_ctrl.2 hp hq) (norm_nonneg Lx)
            _ = (‖Lx‖ * Hxx) * (parabolicDistance p q) ^ α := by ring
    convert hxx_prod using 1
    all_goals try rfl
  · simpa [ParabolicSecondJet.prod] using
      ParabolicC0AlphaNormLe.prod (X := X) (E := E) (F := F) htu htv

theorem prod_sub_prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u' : ℝ × X → E} {v v' : ℝ × X → F} {Nu Nv : ℝ}
    (hu : ParabolicC2AlphaNormLe Nu α (fun z : ℝ × X => u z - u' z) s)
    (hv : ParabolicC2AlphaNormLe Nv α (fun z : ℝ × X => v z - v' z) s) :
    ParabolicC2AlphaNormLe (prodRadius (X := X) (E := E) (F := F) * (Nu + Nv)) α
      (fun z : ℝ × X => (u z, v z) - (u' z, v' z)) s := by
  simpa using hu.prod hv

/-- Radius multiplier for composing a higher parabolic function with a continuous linear
value map.  The spatial first- and second-derivative components both use postcomposition by
`L` on `X →L[ℝ] E`. -/
def continuousLinearMapRadius {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) : ℝ :=
  ‖L‖ + ‖ContinuousLinearMap.compL ℝ X E F L‖ +
    ‖ContinuousLinearMap.compL ℝ X E F L‖ + ‖L‖

/-- The higher parabolic radius multiplier for a continuous linear value map is nonnegative. -/
theorem continuousLinearMapRadius_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) :
    0 ≤ continuousLinearMapRadius (X := X) (E := E) L := by
  unfold continuousLinearMapRadius
  positivity

theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaNormLe
      (continuousLinearMapRadius (X := X) (E := E) L * N) α
      (fun z : ℝ × X => L (u z)) s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  let Lx : (X →L[ℝ] E) →L[ℝ] X →L[ℝ] F :=
    ContinuousLinearMap.compL ℝ X E F L
  have hxx_comp : ParabolicC0AlphaNormLe (‖Lx‖ * Nxx) α
      (fun z : ℝ × X => Lx.comp (J.spaceSecondDeriv z)) s := by
    rcases hxx with ⟨Bxx, hBxx, Hxx, hHxx, hxx_sum, hxx_ctrl⟩
    refine ⟨‖Lx‖ * Bxx, mul_nonneg (norm_nonneg Lx) hBxx,
      ‖Lx‖ * Hxx, mul_nonneg (norm_nonneg Lx) hHxx, ?_, ?_⟩
    · calc
        ‖Lx‖ * Bxx + ‖Lx‖ * Hxx = ‖Lx‖ * (Bxx + Hxx) := by ring
        _ ≤ ‖Lx‖ * Nxx := mul_le_mul_of_nonneg_left hxx_sum (norm_nonneg Lx)
    · constructor
      · intro p hp
        exact (Lx.opNorm_comp_le (J.spaceSecondDeriv p)).trans
          (mul_le_mul_of_nonneg_left (hxx_ctrl.bounded hp) (norm_nonneg Lx))
      · intro p hp q hq
        calc
          ‖Lx.comp (J.spaceSecondDeriv p) - Lx.comp (J.spaceSecondDeriv q)‖ =
              ‖Lx.comp (J.spaceSecondDeriv p - J.spaceSecondDeriv q)‖ := by
            congr 1
            ext x y
            simp [Pi.sub_apply]
          _ ≤ ‖Lx‖ * ‖J.spaceSecondDeriv p - J.spaceSecondDeriv q‖ :=
            Lx.opNorm_comp_le (J.spaceSecondDeriv p - J.spaceSecondDeriv q)
          _ ≤ ‖Lx‖ * (Hxx * (parabolicDistance p q) ^ α) :=
            mul_le_mul_of_nonneg_left (hxx_ctrl.holder hp hq) (norm_nonneg Lx)
          _ = (‖Lx‖ * Hxx) * (parabolicDistance p q) ^ α := by ring
  refine ⟨J.continuousLinearMap L, ‖L‖ * Nu, mul_nonneg (norm_nonneg L) hNu,
    ‖Lx‖ * Nx, mul_nonneg (norm_nonneg Lx) hNx,
    ‖Lx‖ * Nxx, mul_nonneg (norm_nonneg Lx) hNxx,
    ‖L‖ * Nt, mul_nonneg (norm_nonneg L) hNt, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      ‖L‖ * Nu + ‖Lx‖ * Nx + ‖Lx‖ * Nxx + ‖L‖ * Nt ≤
          ‖L‖ * N + ‖Lx‖ * N + ‖Lx‖ * N + ‖L‖ * N := by
        have hNu_le : Nu ≤ N := by linarith
        have hNx_le : Nx ≤ N := by linarith
        have hNxx_le : Nxx ≤ N := by linarith
        have hNt_le : Nt ≤ N := by linarith
        have hNu_bound : ‖L‖ * Nu ≤ ‖L‖ * N :=
          mul_le_mul_of_nonneg_left hNu_le (norm_nonneg L)
        have hNx_bound : ‖Lx‖ * Nx ≤ ‖Lx‖ * N :=
          mul_le_mul_of_nonneg_left hNx_le (norm_nonneg Lx)
        have hNxx_bound : ‖Lx‖ * Nxx ≤ ‖Lx‖ * N :=
          mul_le_mul_of_nonneg_left hNxx_le (norm_nonneg Lx)
        have hNt_bound : ‖L‖ * Nt ≤ ‖L‖ * N :=
          mul_le_mul_of_nonneg_left hNt_le (norm_nonneg L)
        linarith
      _ = continuousLinearMapRadius (X := X) (E := E) L * N := by
        simp [continuousLinearMapRadius, Lx]
        ring
  · simpa using hu.continuousLinearMap L
  · exact (by
      have hxL : ParabolicC0AlphaNormLe (‖Lx‖ * Nx) α (fun z => Lx (J.spaceDeriv z)) s :=
        hx.continuousLinearMap Lx
      simpa [ParabolicSecondJet.continuousLinearMap, Lx] using hxL)
  · exact (by
      simpa [ParabolicSecondJet.continuousLinearMap, Lx, ContinuousLinearMap.comp_apply]
        using hxx_comp)
  · simpa [ParabolicSecondJet.continuousLinearMap] using ht.continuousLinearMap L

/-- Entrywise full higher parabolic controls assemble into a finite Pi-valued
full higher parabolic norm ball by inserting coordinates and summing them. -/
theorem pi {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ι → ℝ} {u : ℝ × X → ι → F}
    (h : ∀ i, ParabolicC2AlphaNormLe (N i) α (fun z => u z i) s) :
    ParabolicC2AlphaNormLe
      (∑ i,
        continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * N i) α u s := by
  classical
  let L : ι → F →L[ℝ] ι → F := fun i =>
    ContinuousLinearMap.single ℝ (fun _ : ι => F) i
  have hsum := finset_sum (X := X) (E := ι → F) (α := α) (s := s)
    (S := Finset.univ)
    (N := fun i : ι => continuousLinearMapRadius (X := X) (E := F) (L i) * N i)
    (u := fun i z => L i (u z i)) ?_
  · have hfun : (fun z : ℝ × X => ∑ i, L i (u z i)) = u := by
      funext z
      simpa [L] using
        (ContinuousLinearMap.sum_comp_single (R := ℝ) (φ := fun _ : ι => F)
          (ContinuousLinearMap.id ℝ (ι → F)) (u z))
    simpa [L] using (hfun ▸ hsum)
  · intro i _hi
    exact (h i).continuousLinearMap (L i)

/-- Entrywise full higher parabolic controls for a finite Pi-valued difference
assemble into a Pi-valued full higher parabolic difference bound. -/
theorem pi_sub_pi {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ι → ℝ} {u v : ℝ × X → ι → F}
    (h : ∀ i, ParabolicC2AlphaNormLe (N i) α (fun z => u z i - v z i) s) :
    ParabolicC2AlphaNormLe
      (∑ i,
        continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * N i) α
      (fun z : ℝ × X => u z - v z) s := by
  classical
  simpa [Pi.sub_apply] using
    pi (X := X) (α := α) (s := s) (N := N)
      (u := fun z : ℝ × X => u z - v z) h

/-- Finite Pi-valued higher difference controls whose component radii are linear in a
shared scalar assemble into a single linear-radius higher difference bound. -/
theorem pi_sub_pi_mul_radius {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : ι → ℝ} {R : ℝ} {u v : ℝ × X → ι → F}
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    ParabolicC2AlphaNormLe
      ((∑ i,
        continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R) α
      (fun z : ℝ × X => u z - v z) s := by
  classical
  have hpi := pi_sub_pi (X := X) (α := α) (s := s)
    (N := fun i => K i * R) (u := u) (v := v) h
  convert hpi using 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- A full higher parabolic norm ball for a finite Pi-valued function projects to each
coordinate as a full higher parabolic norm ball. -/
theorem pi_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × X → ι → F} (h : ParabolicC2AlphaNormLe N α u s) (i : ι) :
    ParabolicC2AlphaNormLe
      (continuousLinearMapRadius (X := X) (E := ι → F)
        (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F) * N) α
      (fun z : ℝ × X => u z i) s := by
  simpa using h.continuousLinearMap (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)

theorem value_c0AlphaNormLe (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ Nu ≥ 0, ParabolicC0AlphaNormLe Nu α u s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨Nu, hNu, hu⟩

theorem value_c0AlphaNormLe_self (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe N α u s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  have hNu_le : Nu ≤ N := by linarith
  exact hu.mono_const hNu_le

/-- A higher single-radius bound supplies one chosen second jet whose value and derivative
components are all controlled by the same higher radius at the `C^{0,α}` level. -/
theorem exists_secondJet_c0AlphaNormLe_self (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      ParabolicC0AlphaNormLe N α u s ∧
        ParabolicC0AlphaNormLe N α J.spaceDeriv s ∧
          ParabolicC0AlphaNormLe N α J.spaceSecondDeriv s ∧
            ParabolicC0AlphaNormLe N α J.timeDeriv s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  have hNu_le : Nu ≤ N := by linarith
  have hNx_le : Nx ≤ N := by linarith
  have hNxx_le : Nxx ≤ N := by linarith
  have hNt_le : Nt ≤ N := by linarith
  exact ⟨J, hu.mono_const hNu_le, hx.mono_const hNx_le,
    hxx.mono_const hNxx_le, ht.mono_const hNt_le⟩

/-- On unique-differentiability slices, the higher norm-ball derivative controls may be
transported from the existentially chosen second jet to any caller-supplied second jet. -/
theorem secondJet_c0AlphaNormLe_self_of_unique (h : ParabolicC2AlphaNormLe N α u s)
    (J : ParabolicSecondJet u s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ParabolicC0AlphaNormLe N α u s ∧
      ParabolicC0AlphaNormLe N α J.spaceDeriv s ∧
        ParabolicC0AlphaNormLe N α J.spaceSecondDeriv s ∧
          ParabolicC0AlphaNormLe N α J.timeDeriv s := by
  rcases h.exists_secondJet_c0AlphaNormLe_self with ⟨K, hu, hx, hxx, ht⟩
  refine ⟨hu, ?_, ?_, ?_⟩
  · exact hx.congr fun z hz => J.spaceDeriv_eq_of_unique K hz (hspace hz)
  · exact hxx.congr fun z hz =>
      J.spaceSecondDeriv_eq_of_unique K hz (fun {x} hx => hspace (z := (z.1, x)) hx)
  · exact ht.congr fun z hz => J.timeDeriv_eq_of_unique K hz (htime hz)

/-- On unique-differentiability slices, a higher norm-ball bound on a difference controls the
componentwise differences of any caller-supplied second jets for the two functions. -/
theorem secondJet_sub_c0AlphaNormLe_self_of_unique {v : ℝ × X → E}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (Ju : ParabolicSecondJet u s) (Jv : ParabolicSecondJet v s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ParabolicC0AlphaNormLe N α (fun z => u z - v z) s ∧
      ParabolicC0AlphaNormLe N α (fun z => Ju.spaceDeriv z - Jv.spaceDeriv z) s ∧
        ParabolicC0AlphaNormLe N α
          (fun z => Ju.spaceSecondDeriv z - Jv.spaceSecondDeriv z) s ∧
          ParabolicC0AlphaNormLe N α (fun z => Ju.timeDeriv z - Jv.timeDeriv z) s := by
  rcases h.secondJet_c0AlphaNormLe_self_of_unique (Ju.sub Jv) htime hspace with
    ⟨huv, hx, hxx, ht⟩
  refine ⟨huv, ?_, ?_, ?_⟩
  · simpa [ParabolicSecondJet.sub, ParabolicSecondJet.add, ParabolicSecondJet.neg,
      sub_eq_add_neg] using hx
  · simpa [ParabolicSecondJet.sub, ParabolicSecondJet.add, ParabolicSecondJet.neg,
      sub_eq_add_neg] using hxx
  · simpa [ParabolicSecondJet.sub, ParabolicSecondJet.add, ParabolicSecondJet.neg,
      sub_eq_add_neg] using ht

/-- A higher single-radius bound supplies one chosen second jet whose value and
derivative components are pointwise bounded by the same higher radius. -/
theorem exists_secondJet_norm_le_self (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖u z‖ ≤ N) ∧
        (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceDeriv z‖ ≤ N) ∧
          (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceSecondDeriv z‖ ≤ N) ∧
            (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.timeDeriv z‖ ≤ N) := by
  rcases h.exists_secondJet_c0AlphaNormLe_self with ⟨J, hu, hx, hxx, ht⟩
  exact ⟨J,
    (fun {_z} hz ↦ hu.norm_le hz),
    (fun {_z} hz ↦ hx.norm_le hz),
    (fun {_z} hz ↦ hxx.norm_le hz),
    (fun {_z} hz ↦ ht.norm_le hz)⟩

/-- The higher single radius controls the pointwise value norm on the domain. -/
theorem norm_le (h : ParabolicC2AlphaNormLe N α u s) ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖u z‖ ≤ N :=
  h.value_c0AlphaNormLe_self.norm_le hz

/-- A higher single-radius bound gives value-level time-slice Holder control with the parabolic
half exponent. -/
theorem time_slice_half_exponent (h : ParabolicC2AlphaNormLe N α u s)
    {t τ : ℝ} {x : X} (ht : (t, x) ∈ s) (hτ : (τ, x) ∈ s) :
    ‖u (t, x) - u (τ, x)‖ ≤ N * |t - τ| ^ (α / 2) :=
  h.value_c0AlphaNormLe_self.time_slice_half_exponent ht hτ

/-- A higher single-radius bound restricts to value-level spatial Holder control on each fixed
time slice. -/
theorem space_slice (h : ParabolicC2AlphaNormLe N α u s)
    {t : ℝ} {x y : X} (hx : (t, x) ∈ s) (hy : (t, y) ∈ s) :
    ‖u (t, x) - u (t, y)‖ ≤ N * (dist x y) ^ α :=
  h.value_c0AlphaNormLe_self.space_slice hx hy

/-- Product-domain pointwise value readout of a higher single-radius bound. -/
theorem norm_le_of_prod_subset (h : ParabolicC2AlphaNormLe N α u s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    ‖u (t, x)‖ ≤ N :=
  h.value_c0AlphaNormLe_self.norm_le_of_prod_subset hst ht hx

/-- Product-domain time-slice value readout of a higher single-radius bound. -/
theorem time_slice_half_exponent_of_prod_subset (h : ParabolicC2AlphaNormLe N α u s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t τ : ℝ} (ht : t ∈ timeSet) (hτ : τ ∈ timeSet)
    {x : X} (hx : x ∈ spaceSet) :
    ‖u (t, x) - u (τ, x)‖ ≤ N * |t - τ| ^ (α / 2) :=
  h.value_c0AlphaNormLe_self.time_slice_half_exponent_of_prod_subset hst ht hτ hx

/-- Product-domain fixed-time spatial Holder value readout of a higher single-radius bound. -/
theorem space_slice_of_prod_subset (h : ParabolicC2AlphaNormLe N α u s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x y : X} (hx : x ∈ spaceSet) (hy : y ∈ spaceSet) :
    ‖u (t, x) - u (t, y)‖ ≤ N * (dist x y) ^ α :=
  h.value_c0AlphaNormLe_self.space_slice_of_prod_subset hst ht hx hy

/-- A higher single-radius bound on a difference gives the corresponding pointwise value
distance bound. -/
theorem dist_le_of_sub {v : ℝ × X → E}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    dist (u z) (v z) ≤ N :=
  h.value_c0AlphaNormLe_self.dist_le_of_sub hz

/-- A higher single-radius difference bound puts each value in the closed ball
around the corresponding comparison value. -/
theorem mem_closedBall_of_sub {v : ℝ × X → E}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    u z ∈ Metric.closedBall (v z) N :=
  h.value_c0AlphaNormLe_self.mem_closedBall_of_sub hz

/-- Symmetric closed-ball readout from a higher single-radius difference bound. -/
theorem mem_closedBall_symm_of_sub {v : ℝ × X → E}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    v z ∈ Metric.closedBall (u z) N :=
  h.value_c0AlphaNormLe_self.mem_closedBall_symm_of_sub hz

/-- Product-domain pointwise distance readout of a higher single-radius
difference bound. -/
theorem dist_le_of_sub_prod_subset {v : ℝ × X → E}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    dist (u (t, x)) (v (t, x)) ≤ N :=
  h.value_c0AlphaNormLe_self.dist_le_of_sub_prod_subset hst ht hx

/-- Product-domain closed-ball readout of a higher single-radius difference
bound. -/
theorem mem_closedBall_of_sub_prod_subset {v : ℝ × X → E}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    u (t, x) ∈ Metric.closedBall (v (t, x)) N :=
  h.value_c0AlphaNormLe_self.mem_closedBall_of_sub_prod_subset hst ht hx

/-- Componentwise higher difference controls with radii linear in a shared scalar give a
pointwise finite-Pi norm difference bound with the summed component radius. -/
theorem pi_norm_sub_le_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖u z - v z‖ ≤ (∑ i, K i) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, K i :=
    Finset.sum_nonneg fun i _hi => hK i
  have htarget_nonneg : 0 ≤ (∑ i, K i) * R :=
    mul_nonneg hsum_nonneg hR
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i => ?_
  have hentry : ‖u z i - v z i‖ ≤ K i * R := by
    simpa [dist_eq_norm] using (h i).dist_le_of_sub hz
  have hentry_le_sum : K i ≤ ∑ i, K i :=
    Finset.single_le_sum (fun i' _hi' => hK i') (Finset.mem_univ i)
  exact (by
    simpa [Pi.sub_apply] using hentry.trans (mul_le_mul_of_nonneg_right hentry_le_sum hR))

/-- Componentwise higher difference controls with radii linear in a shared scalar give a
pointwise finite-Pi distance bound with the summed component radius. -/
theorem pi_dist_le_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    dist (u z) (v z) ≤ (∑ i, K i) * R := by
  simpa [dist_eq_norm] using
    pi_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) hK hR h hz

/-- Product-domain finite-Pi distance bound from componentwise higher difference controls
with radii linear in a shared scalar. -/
theorem pi_dist_le_sum_mul_of_entries_prod_subset {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    dist (u (t, x)) (v (t, x)) ≤ (∑ i, K i) * R :=
  pi_dist_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) hK hR h (hst ⟨ht, hx⟩)

/-- Componentwise higher difference controls with radii linear in a shared
scalar give a finite-Pi closed-ball membership bound. -/
theorem pi_mem_closedBall_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    u z ∈ Metric.closedBall (v z) ((∑ i, K i) * R) := by
  simpa [Metric.mem_closedBall] using
    pi_dist_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) hK hR h hz

/-- Componentwise higher difference controls with radii linear in a shared
scalar give the symmetric finite-Pi closed-ball membership bound. -/
theorem pi_mem_closedBall_symm_sum_mul_of_entries {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    v z ∈ Metric.closedBall (u z) ((∑ i, K i) * R) := by
  simpa [Metric.mem_closedBall, dist_comm] using
    pi_dist_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) hK hR h hz

/-- Product-domain finite-Pi closed-ball membership bound from componentwise
higher difference controls. -/
theorem pi_mem_closedBall_sum_mul_of_entries_prod_subset {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    u (t, x) ∈ Metric.closedBall (v (t, x)) ((∑ i, K i) * R) :=
  pi_mem_closedBall_sum_mul_of_entries
    (X := X) (α := α) (s := s) hK hR h (hst ⟨ht, hx⟩)

/-- Product-domain symmetric finite-Pi closed-ball membership bound from componentwise
higher difference controls. -/
theorem pi_mem_closedBall_symm_sum_mul_of_entries_prod_subset {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ} {u v : ℝ × X → ι → F}
    (hK : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    {timeSet : Set ℝ} {spaceSet : Set X} (hst : timeSet ×ˢ spaceSet ⊆ s)
    {t : ℝ} (ht : t ∈ timeSet) {x : X} (hx : x ∈ spaceSet) :
    v (t, x) ∈ Metric.closedBall (u (t, x)) ((∑ i, K i) * R) :=
  pi_mem_closedBall_symm_sum_mul_of_entries
    (X := X) (α := α) (s := s) hK hR h (hst ⟨ht, hx⟩)

/-- Continuous-linear value readouts of a higher single-radius norm ball inherit value-level
`C^{0,α}` control. -/
theorem value_continuousLinearMap_c0AlphaNormLe {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe (‖L‖ * N) α (fun z => L (u z)) s :=
  h.value_c0AlphaNormLe_self.continuousLinearMap L

/-- Positive-exponent higher norm-ball control gives value-level continuity on the domain. -/
theorem continuousOn (h : ParabolicC2AlphaNormLe N α u s) (hα : 0 < α) :
    ContinuousOn u s :=
  h.value_c0AlphaNormLe_self.continuousOn hα

/-- Positive-exponent higher norm-ball control gives value-level uniform continuity on the
domain. -/
theorem uniformContinuousOn (h : ParabolicC2AlphaNormLe N α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.value_c0AlphaNormLe_self.uniformContinuousOn hα

theorem exists_secondJet (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      (∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α J.spaceDeriv s) ∧
      (∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s) ∧
      (∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α J.timeDeriv s) := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J, ⟨Nx, hNx, hx⟩, ⟨Nxx, hNxx, hxx⟩, ⟨Nt, hNt, ht⟩⟩

theorem value_c0AlphaOn (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC0AlphaOn α u s := by
  exact h.value_c0AlphaNormLe_self.c0AlphaOn

theorem exists_timeDeriv (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α Dt s := by
  rcases h.exists_secondJet with ⟨J, _hx, _hxx, ⟨Nt, hNt, ht⟩⟩
  exact ⟨J.timeDeriv, J.hasTimeDeriv, Nt, hNt, ht⟩

theorem exists_spaceDeriv (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α Dx s := by
  rcases h.exists_secondJet with ⟨J, ⟨Nx, hNx, hx⟩, _hxx, _ht⟩
  exact ⟨J.spaceDeriv, J.hasSpaceDeriv, Nx, hNx, hx⟩

theorem exists_spaceSecondDeriv (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      ∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s := by
  rcases h.exists_secondJet with ⟨J, _hx, ⟨Nxx, hNxx, hxx⟩, _ht⟩
  exact ⟨J, Nxx, hNxx, hxx⟩

end ParabolicC2AlphaNormLe

/-- Coordinate parabolic `C^{2+α,1+α/2}` membership with some finite single-radius control. -/
def ParabolicC2AlphaOn (α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ N ≥ 0, ParabolicC2AlphaNormLe N α u s

namespace ParabolicC2AlphaOn

variable {α : ℝ} {u v : ℝ × X → E} {s : Set (ℝ × X)}

theorem of_normLe {N : ℝ} (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaOn α u s :=
  ⟨N, h.nonneg, h⟩

theorem c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ParabolicC0AlphaOn α u s := by
  rcases h with ⟨N, _hN, hN⟩
  exact hN.value_c0AlphaOn

theorem continuousOn (h : ParabolicC2AlphaOn α u s) (hα : 0 < α) :
    ContinuousOn u s :=
  h.c0AlphaOn.continuousOn hα

theorem uniformContinuousOn (h : ParabolicC2AlphaOn α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.c0AlphaOn.uniformContinuousOn hα

theorem exists_secondJet (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s,
      (∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α J.spaceDeriv s) ∧
      (∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s) ∧
      (∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α J.timeDeriv s) := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_secondJet

/-- Higher parabolic membership supplies one chosen second jet whose value and derivative
components are all `C^{0,α}`. -/
theorem exists_secondJet_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s,
      ParabolicC0AlphaOn α u s ∧
        ParabolicC0AlphaOn α J.spaceDeriv s ∧
          ParabolicC0AlphaOn α J.spaceSecondDeriv s ∧
            ParabolicC0AlphaOn α J.timeDeriv s := by
  rcases h with ⟨N, _hN, hNu⟩
  rcases hNu.exists_secondJet_c0AlphaNormLe_self with ⟨J, hu, hx, hxx, ht⟩
  exact ⟨J, hu.c0AlphaOn, hx.c0AlphaOn, hxx.c0AlphaOn, ht.c0AlphaOn⟩

/-- Higher parabolic membership supplies one chosen second jet and one common
finite bound for the value, spatial derivative, second spatial derivative, and
time derivative components. -/
theorem exists_secondJet_norm_le (h : ParabolicC2AlphaOn α u s) :
    ∃ N ≥ 0, ∃ J : ParabolicSecondJet u s,
      (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖u z‖ ≤ N) ∧
        (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceDeriv z‖ ≤ N) ∧
          (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceSecondDeriv z‖ ≤ N) ∧
            (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.timeDeriv z‖ ≤ N) := by
  rcases h with ⟨N, hN, hNu⟩
  rcases hNu.exists_secondJet_norm_le_self with ⟨J, hu, hx, hxx, ht⟩
  exact ⟨N, hN, J, hu, hx, hxx, ht⟩

theorem exists_timeDeriv (h : ParabolicC2AlphaOn α u s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α Dt s := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_timeDeriv

theorem exists_spaceDeriv (h : ParabolicC2AlphaOn α u s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α Dx s := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_spaceDeriv

theorem exists_spaceSecondDeriv (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s,
      ∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_spaceSecondDeriv

theorem exists_timeDeriv_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ParabolicC0AlphaOn α Dt s := by
  rcases h.exists_timeDeriv with ⟨Dt, hDt, Nt, _hNt, hNt⟩
  exact ⟨Dt, hDt, hNt.c0AlphaOn⟩

theorem exists_spaceDeriv_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ParabolicC0AlphaOn α Dx s := by
  rcases h.exists_spaceDeriv with ⟨Dx, hDx, Nx, _hNx, hNx⟩
  exact ⟨Dx, hDx, hNx.c0AlphaOn⟩

theorem exists_spaceSecondDeriv_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s, ParabolicC0AlphaOn α J.spaceSecondDeriv s := by
  rcases h.exists_spaceSecondDeriv with ⟨J, Nxx, _hNxx, hNxx⟩
  exact ⟨J, hNxx.c0AlphaOn⟩

theorem const (c : E) : ParabolicC2AlphaOn α (fun _ : ℝ × X => c) s :=
  of_normLe (ParabolicC2AlphaNormLe.const (X := X) (α := α) (s := s) c)

theorem zero : ParabolicC2AlphaOn α (fun _ : ℝ × X => (0 : E)) s :=
  of_normLe (ParabolicC2AlphaNormLe.zero (X := X) (E := E) (α := α) (s := s))

theorem add (hu : ParabolicC2AlphaOn α u s) (hv : ParabolicC2AlphaOn α v s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => u z + v z) s := by
  rcases hu with ⟨Nu, hNu, huN⟩
  rcases hv with ⟨Nv, hNv, hvN⟩
  exact ⟨Nu + Nv, add_nonneg hNu hNv, huN.add hvN⟩

theorem finset_sum {ι : Type*} (S : Finset ι) {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC2AlphaOn α (u i) s) :
    ParabolicC2AlphaOn α (fun z => ∑ i ∈ S, u i z) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (zero (X := X) (E := E) (α := α) (s := s))
  | insert a S ha ih =>
      have ha_ctrl : ParabolicC2AlphaOn α (u a) s := h a (by simp)
      have hS_ctrl : ParabolicC2AlphaOn α (fun z => ∑ i ∈ S, u i z) s := by
        exact ih fun i hi => h i (by simp [hi])
      have hadd := add ha_ctrl hS_ctrl
      simpa [Finset.sum_insert, ha] using hadd

theorem neg (hu : ParabolicC2AlphaOn α u s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => -u z) s := by
  rcases hu with ⟨N, hN, huN⟩
  exact ⟨N, hN, huN.neg⟩

theorem sub (hu : ParabolicC2AlphaOn α u s) (hv : ParabolicC2AlphaOn α v s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => u z - v z) s := by
  rcases hu with ⟨Nu, hNu, huN⟩
  rcases hv with ⟨Nv, hNv, hvN⟩
  exact ⟨Nu + Nv, add_nonneg hNu hNv, huN.sub hvN⟩

theorem smul (c : ℝ) (hu : ParabolicC2AlphaOn α u s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => c • u z) s := by
  rcases hu with ⟨N, hN, huN⟩
  exact ⟨‖c‖ * N, mul_nonneg (norm_nonneg c) hN, huN.smul c⟩

theorem prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : ℝ × X → F} (hu : ParabolicC2AlphaOn α u s)
    (hv : ParabolicC2AlphaOn α v s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => (u z, v z)) s := by
  rcases hu with ⟨N, hN, huN⟩
  rcases hv with ⟨M, hM, hvN⟩
  exact ⟨_, (huN.prod hvN).nonneg, huN.prod hvN⟩

theorem prod_sub_prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u' : ℝ × X → E} {v v' : ℝ × X → F}
    (hu : ParabolicC2AlphaOn α (fun z : ℝ × X => u z - u' z) s)
    (hv : ParabolicC2AlphaOn α (fun z : ℝ × X => v z - v' z) s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => (u z, v z) - (u' z, v' z)) s := by
  simpa using hu.prod hv

theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicC2AlphaOn α u s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => L (u z)) s := by
  rcases hu with ⟨N, hN, huN⟩
  exact ⟨_, (huN.continuousLinearMap L).nonneg, huN.continuousLinearMap L⟩

/-- Entrywise higher parabolic membership assembles into finite Pi-valued higher
parabolic membership. -/
theorem pi {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × X → ι → F}
    (h : ∀ i, ParabolicC2AlphaOn α (fun z => u z i) s) :
    ParabolicC2AlphaOn α u s := by
  classical
  choose N _hN hN using h
  exact of_normLe (ParabolicC2AlphaNormLe.pi
    (X := X) (α := α) (s := s) (N := N) (u := u) hN)

/-- Entrywise higher parabolic membership for a finite Pi-valued difference
assembles into Pi-valued higher parabolic membership. -/
theorem pi_sub_pi {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u v : ℝ × X → ι → F}
    (h : ∀ i, ParabolicC2AlphaOn α (fun z => u z i - v z i) s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => u z - v z) s := by
  classical
  simpa [Pi.sub_apply] using
    pi (X := X) (α := α) (s := s)
      (u := fun z : ℝ × X => u z - v z) h

/-- A finite Pi-valued higher parabolic function projects to each coordinate as a higher
parabolic function. -/
theorem pi_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × X → ι → F} (hu : ParabolicC2AlphaOn α u s) (i : ι) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => u z i) s := by
  simpa using hu.continuousLinearMap (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)

theorem mono_set {t : Set (ℝ × X)} (h : ParabolicC2AlphaOn α u s) (hst : t ⊆ s) :
    ParabolicC2AlphaOn α u t := by
  rcases h with ⟨N, hN, hNu⟩
  exact ⟨N, hN, hNu.mono_set hst⟩

end ParabolicC2AlphaOn

/-- Coordinate parabolic `C^{2+α,1+α/2}` functions form a real submodule of all time-space
functions. -/
def parabolicC2AlphaSubmodule
    (X E : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (s : Set (ℝ × X)) : Submodule ℝ ((ℝ × X) → E) where
  carrier := {u | ParabolicC2AlphaOn α u s}
  zero_mem' := by
    change ParabolicC2AlphaOn α (fun _ : ℝ × X => (0 : E)) s
    exact ParabolicC2AlphaOn.zero (X := X) (E := E) (α := α) (s := s)
  add_mem' := by
    intro u v hu hv
    change ParabolicC2AlphaOn α (fun z : ℝ × X => u z + v z) s
    exact ParabolicC2AlphaOn.add (X := X) (E := E) (α := α) (s := s) hu hv
  smul_mem' := by
    intro c u hu
    change ParabolicC2AlphaOn α (fun z : ℝ × X => c • u z) s
    exact ParabolicC2AlphaOn.smul (X := X) (E := E) (α := α) (s := s) c hu

namespace parabolicC2AlphaSubmodule

variable {α : ℝ} {s : Set (ℝ × X)}

instance :
    CoeFun (parabolicC2AlphaSubmodule X E α s) (fun _ => (ℝ × X) → E) :=
  ⟨fun u => u.1⟩

@[simp]
theorem mem_iff {u : (ℝ × X) → E} :
    u ∈ parabolicC2AlphaSubmodule X E α s ↔ ParabolicC2AlphaOn α u s :=
  Iff.rfl

/-- Compose coordinate parabolic `C^{2+α,1+α/2}` functions with a continuous linear value map. -/
def continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] parabolicC2AlphaSubmodule X F α s where
  toFun u := ⟨fun z => L (u z), ParabolicC2AlphaOn.continuousLinearMap L u.2⟩
  map_add' := by
    intro u v
    ext z
    simp
  map_smul' := by
    intro c u
    ext z
    simp

@[simp]
theorem continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    continuousLinearMap (X := X) (E := E) (α := α) (s := s) L u z = L (u z) :=
  rfl

/-- Product-valued pairing of two coordinate parabolic `C^{2+α,1+α/2}` submodule elements. -/
def prodLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    parabolicC2AlphaSubmodule X E α s × parabolicC2AlphaSubmodule X F α s →ₗ[ℝ]
      parabolicC2AlphaSubmodule X (E × F) α s where
  toFun u :=
    ⟨fun z => (u.1 z, u.2 z), ParabolicC2AlphaOn.prod u.1.2 u.2.2⟩
  map_add' := by
    intro u v
    ext z <;> rfl
  map_smul' := by
    intro c u
    ext z <;> rfl

@[simp]
theorem prodLinearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : parabolicC2AlphaSubmodule X E α s × parabolicC2AlphaSubmodule X F α s)
    (z : ℝ × X) :
    prodLinearMap (X := X) (E := E) (α := α) (s := s) u z = (u.1 z, u.2 z) :=
  rfl

/-- Coordinate projection from a finite Pi-valued higher parabolic submodule. -/
def piApplyLinearMap {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : ι) :
    parabolicC2AlphaSubmodule X (ι → F) α s →ₗ[ℝ]
      parabolicC2AlphaSubmodule X F α s :=
  continuousLinearMap (X := X) (E := ι → F) (α := α) (s := s)
    (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)

@[simp]
theorem piApplyLinearMap_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (i : ι) (u : parabolicC2AlphaSubmodule X (ι → F) α s)
    (z : ℝ × X) :
    piApplyLinearMap (X := X) (α := α) (s := s) i u z = u z i :=
  rfl

/-- Assemble finite Pi-valued higher parabolic submodule elements from their components. -/
def piOfComponentsLinearMap {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ι → parabolicC2AlphaSubmodule X F α s) →ₗ[ℝ]
      parabolicC2AlphaSubmodule X (ι → F) α s where
  toFun u := ⟨fun z i => u i z,
    ParabolicC2AlphaOn.pi (X := X) (α := α) (s := s) fun i => (u i).2⟩
  map_add' := by
    intro u v
    ext z i
    rfl
  map_smul' := by
    intro c u
    ext z i
    rfl

@[simp]
theorem piOfComponentsLinearMap_apply {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ι → parabolicC2AlphaSubmodule X F α s) (z : ℝ × X) (i : ι) :
    piOfComponentsLinearMap (X := X) (α := α) (s := s) u z i = u i z :=
  rfl

theorem c0AlphaOn (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicC0AlphaOn α (u : (ℝ × X) → E) s :=
  u.2.c0AlphaOn

/-- A higher submodule element has a chosen second jet whose value and derivative components
are all `C^{0,α}`. -/
theorem exists_secondJet_c0AlphaOn (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ J : ParabolicSecondJet (u : (ℝ × X) → E) s,
      ParabolicC0AlphaOn α (u : (ℝ × X) → E) s ∧
        ParabolicC0AlphaOn α J.spaceDeriv s ∧
          ParabolicC0AlphaOn α J.spaceSecondDeriv s ∧
            ParabolicC0AlphaOn α J.timeDeriv s :=
  u.2.exists_secondJet_c0AlphaOn

/-- A noncanonical coherent second jet chosen for a higher parabolic submodule element.  On
unique-differentiability slices this agrees with any other chosen jet by the uniqueness lemmas
above. -/
noncomputable def chosenSecondJet (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicSecondJet (u : (ℝ × X) → E) s :=
  Classical.choose (exists_secondJet_c0AlphaOn (X := X) (E := E) (α := α) (s := s) u)

theorem chosenSecondJet_spec (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicC0AlphaOn α (u : (ℝ × X) → E) s ∧
      ParabolicC0AlphaOn α (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv s ∧
        ParabolicC0AlphaOn α
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv s ∧
          ParabolicC0AlphaOn α
            (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv s :=
  Classical.choose_spec
    (exists_secondJet_c0AlphaOn (X := X) (E := E) (α := α) (s := s) u)

theorem chosenSecondJet_value_c0AlphaOn (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicC0AlphaOn α (u : (ℝ × X) → E) s :=
  (chosenSecondJet_spec (X := X) (E := E) (α := α) (s := s) u).1

theorem chosenSecondJet_spaceDeriv_c0AlphaOn (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicC0AlphaOn α
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv s :=
  (chosenSecondJet_spec (X := X) (E := E) (α := α) (s := s) u).2.1

theorem chosenSecondJet_spaceSecondDeriv_c0AlphaOn
    (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicC0AlphaOn α
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv s :=
  (chosenSecondJet_spec (X := X) (E := E) (α := α) (s := s) u).2.2.1

theorem chosenSecondJet_timeDeriv_c0AlphaOn (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicC0AlphaOn α
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv s :=
  (chosenSecondJet_spec (X := X) (E := E) (α := α) (s := s) u).2.2.2

/-- The chosen spatial derivative as a lower parabolic `C^{0,α}` submodule element. -/
noncomputable def chosenSpaceDerivC0AlphaSubmodule
    (u : parabolicC2AlphaSubmodule X E α s) :
    parabolicC0AlphaSubmodule X (X →L[ℝ] E) α s :=
  ⟨(chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv,
    chosenSecondJet_spaceDeriv_c0AlphaOn (X := X) (E := E) (α := α) (s := s) u⟩

@[simp]
theorem chosenSpaceDerivC0AlphaSubmodule_apply
    (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    chosenSpaceDerivC0AlphaSubmodule (X := X) (E := E) (α := α) (s := s) u z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv z :=
  rfl

/-- The chosen second spatial derivative as a lower parabolic `C^{0,α}` submodule element. -/
noncomputable def chosenSpaceSecondDerivC0AlphaSubmodule
    (u : parabolicC2AlphaSubmodule X E α s) :
    parabolicC0AlphaSubmodule X (X →L[ℝ] (X →L[ℝ] E)) α s :=
  ⟨(chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv,
    chosenSecondJet_spaceSecondDeriv_c0AlphaOn
      (X := X) (E := E) (α := α) (s := s) u⟩

@[simp]
theorem chosenSpaceSecondDerivC0AlphaSubmodule_apply
    (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    chosenSpaceSecondDerivC0AlphaSubmodule (X := X) (E := E) (α := α) (s := s) u z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv z :=
  rfl

/-- The chosen time derivative as a lower parabolic `C^{0,α}` submodule element. -/
noncomputable def chosenTimeDerivC0AlphaSubmodule
    (u : parabolicC2AlphaSubmodule X E α s) :
    parabolicC0AlphaSubmodule X E α s :=
  ⟨(chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv,
    chosenSecondJet_timeDeriv_c0AlphaOn (X := X) (E := E) (α := α) (s := s) u⟩

@[simp]
theorem chosenTimeDerivC0AlphaSubmodule_apply
    (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    chosenTimeDerivC0AlphaSubmodule (X := X) (E := E) (α := α) (s := s) u z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv z :=
  rfl

/-- Compact-piece readout of the chosen spatial derivative. -/
noncomputable def chosenSpaceDerivToContinuousMap
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : C(K, X →L[ℝ] E) :=
  parabolicC0AlphaSubmodule.toContinuousMap
    (X := X) (E := X →L[ℝ] E) (α := α) (s := s) hK hα
    (chosenSpaceDerivC0AlphaSubmodule (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem chosenSpaceDerivToContinuousMap_apply
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (z : K) :
    chosenSpaceDerivToContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv z.1 :=
  rfl

/-- Compact-piece readout of the chosen second spatial derivative. -/
noncomputable def chosenSpaceSecondDerivToContinuousMap
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : C(K, X →L[ℝ] (X →L[ℝ] E)) :=
  parabolicC0AlphaSubmodule.toContinuousMap
    (X := X) (E := X →L[ℝ] (X →L[ℝ] E)) (α := α) (s := s) hK hα
    (chosenSpaceSecondDerivC0AlphaSubmodule
      (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem chosenSpaceSecondDerivToContinuousMap_apply
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (z : K) :
    chosenSpaceSecondDerivToContinuousMap
        (X := X) (E := E) (α := α) (s := s) hK hα u z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv z.1 :=
  rfl

/-- Compact-piece readout of the chosen time derivative. -/
noncomputable def chosenTimeDerivToContinuousMap
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : C(K, E) :=
  parabolicC0AlphaSubmodule.toContinuousMap
    (X := X) (E := E) (α := α) (s := s) hK hα
    (chosenTimeDerivC0AlphaSubmodule (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem chosenTimeDerivToContinuousMap_apply
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (z : K) :
    chosenTimeDerivToContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv z.1 :=
  rfl

/-- Compact-family readout of the chosen spatial derivative. -/
noncomputable def chosenSpaceDerivToCompactCoordFamily {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : ∀ i, C(Kc i, X →L[ℝ] E) :=
  parabolicC0AlphaSubmodule.toCompactCoordFamily
    (X := X) (E := X →L[ℝ] E) (α := α) (s := s) Kc hKc hα
    (chosenSpaceDerivC0AlphaSubmodule (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem chosenSpaceDerivToCompactCoordFamily_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (i : κ) (z : Kc i) :
    chosenSpaceDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv z.1 :=
  rfl

/-- Compact-family readout of the chosen second spatial derivative. -/
noncomputable def chosenSpaceSecondDerivToCompactCoordFamily {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) :
    ∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E)) :=
  parabolicC0AlphaSubmodule.toCompactCoordFamily
    (X := X) (E := X →L[ℝ] (X →L[ℝ] E)) (α := α) (s := s) Kc hKc hα
    (chosenSpaceSecondDerivC0AlphaSubmodule
      (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem chosenSpaceSecondDerivToCompactCoordFamily_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (i : κ) (z : Kc i) :
    chosenSpaceSecondDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv z.1 :=
  rfl

/-- Compact-family readout of the chosen time derivative. -/
noncomputable def chosenTimeDerivToCompactCoordFamily {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : ∀ i, C(Kc i, E) :=
  parabolicC0AlphaSubmodule.toCompactCoordFamily
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    (chosenTimeDerivC0AlphaSubmodule (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem chosenTimeDerivToCompactCoordFamily_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (i : κ) (z : Kc i) :
    chosenTimeDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z =
      (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv z.1 :=
  rfl

/-- On compact pieces contained in uniquely differentiable spatial slices, the chosen spatial
derivative compact-family readout is linear. -/
noncomputable def chosenSpaceDerivToCompactCoordFamilyLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] (∀ i, C(Kc i, X →L[ℝ] E)) where
  toFun := chosenSpaceDerivToCompactCoordFamily
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  map_add' := by
    intro u v
    apply funext
    intro i
    apply ContinuousMap.ext
    intro z
    have hz : z.1 ∈ s := hKc i z.2
    have hEq :
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s)
          (u + v)).spaceDeriv z.1 =
        ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).add
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v)).spaceDeriv z.1 :=
      ParabolicSecondJet.spaceDeriv_eq_of_unique
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s) (u + v))
        ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).add
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v))
        hz (hspace hz)
    convert hEq using 1 <;> rfl
  map_smul' := by
    intro c u
    apply funext
    intro i
    apply ContinuousMap.ext
    intro z
    have hz : z.1 ∈ s := hKc i z.2
    have hEq :
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s)
          (c • u)).spaceDeriv z.1 =
        (ParabolicSecondJet.smul c
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u)).spaceDeriv z.1 :=
      ParabolicSecondJet.spaceDeriv_eq_of_unique
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s) (c • u))
        (ParabolicSecondJet.smul c
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u))
        hz (hspace hz)
    convert hEq using 1 <;> rfl

@[simp]
theorem chosenSpaceDerivToCompactCoordFamilyLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u =
      chosenSpaceDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u :=
  rfl

local instance chosenSpaceSecondDerivContinuousAdd :
    ContinuousAdd (X →L[ℝ] (X →L[ℝ] E)) :=
  inferInstance

local instance chosenSpaceSecondDerivContinuousSMul :
    ContinuousSMul ℝ (X →L[ℝ] (X →L[ℝ] E)) :=
  inferInstance

/-- On compact pieces contained in uniquely differentiable spatial slices, the chosen second
spatial derivative compact-family readout is linear. -/
noncomputable def chosenSpaceSecondDerivToCompactCoordFamilyLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ]
      (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) where
  toFun := chosenSpaceSecondDerivToCompactCoordFamily
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  map_add' := by
    intro u v
    apply funext
    intro i
    apply ContinuousMap.ext
    intro z
    have hz : z.1 ∈ s := hKc i z.2
    have hEq :
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s)
          (u + v)).spaceSecondDeriv z.1 =
        ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).add
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v)).spaceSecondDeriv
          z.1 :=
      ParabolicSecondJet.spaceSecondDeriv_eq_of_unique
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s) (u + v))
        ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).add
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v))
        hz (fun {x} hx => hspace (z := (z.1.1, x)) hx)
    convert hEq using 1 <;> rfl
  map_smul' := by
    intro c u
    apply funext
    intro i
    apply ContinuousMap.ext
    intro z
    have hz : z.1 ∈ s := hKc i z.2
    have hEq :
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s)
          (c • u)).spaceSecondDeriv z.1 =
        (ParabolicSecondJet.smul c
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u)).spaceSecondDeriv
          z.1 :=
      ParabolicSecondJet.spaceSecondDeriv_eq_of_unique
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s) (c • u))
        (ParabolicSecondJet.smul c
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u))
        hz (fun {x} hx => hspace (z := (z.1.1, x)) hx)
    convert hEq using 1 <;> rfl

@[simp]
theorem chosenSpaceSecondDerivToCompactCoordFamilyLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u =
      chosenSpaceSecondDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u :=
  rfl

/-- On compact pieces contained in uniquely differentiable time slices, the chosen time derivative
compact-family readout is linear. -/
noncomputable def chosenTimeDerivToCompactCoordFamilyLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] (∀ i, C(Kc i, E)) where
  toFun := chosenTimeDerivToCompactCoordFamily
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  map_add' := by
    intro u v
    apply funext
    intro i
    apply ContinuousMap.ext
    intro z
    have hz : z.1 ∈ s := hKc i z.2
    have hEq :
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s)
          (u + v)).timeDeriv z.1 =
        ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).add
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v)).timeDeriv z.1 :=
      ParabolicSecondJet.timeDeriv_eq_of_unique
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s) (u + v))
        ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).add
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v))
        hz (htime hz)
    convert hEq using 1 <;> rfl
  map_smul' := by
    intro c u
    apply funext
    intro i
    apply ContinuousMap.ext
    intro z
    have hz : z.1 ∈ s := hKc i z.2
    have hEq :
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s)
          (c • u)).timeDeriv z.1 =
        (ParabolicSecondJet.smul c
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u)).timeDeriv z.1 :=
      ParabolicSecondJet.timeDeriv_eq_of_unique
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s) (c • u))
        (ParabolicSecondJet.smul c
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u))
        hz (htime hz)
    convert hEq using 1 <;> rfl

@[simp]
theorem chosenTimeDerivToCompactCoordFamilyLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (u : parabolicC2AlphaSubmodule X E α s) :
    chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u =
      chosenTimeDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u :=
  rfl

/-- Under unique-differentiability of the time and spatial slices, any higher norm ball
controls the noncanonically chosen second jet as well. -/
theorem chosenSecondJet_c0AlphaNormLe_self_of_unique
    (u : parabolicC2AlphaSubmodule X E α s) {N : ℝ}
    (h : ParabolicC2AlphaNormLe N α (u : (ℝ × X) → E) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ParabolicC0AlphaNormLe N α (u : (ℝ × X) → E) s ∧
      ParabolicC0AlphaNormLe N α
        (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv s ∧
        ParabolicC0AlphaNormLe N α
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv s ∧
          ParabolicC0AlphaNormLe N α
            (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv s :=
  h.secondJet_c0AlphaNormLe_self_of_unique
    (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u) htime hspace

/-- Under unique-differentiability of slices, a higher norm ball on a difference controls
the componentwise differences of the two chosen second jets. -/
theorem chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ParabolicC0AlphaNormLe N α (fun z => u z - v z) s ∧
      ParabolicC0AlphaNormLe N α
        (fun z =>
          (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv z -
            (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v).spaceDeriv z) s ∧
        ParabolicC0AlphaNormLe N α
          (fun z =>
            (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceSecondDeriv z -
              (chosenSecondJet
                (X := X) (E := E) (α := α) (s := s) v).spaceSecondDeriv z) s ∧
          ParabolicC0AlphaNormLe N α
            (fun z =>
              (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv z -
                (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v).timeDeriv z) s :=
  h.secondJet_sub_c0AlphaNormLe_self_of_unique
    (chosenSecondJet (X := X) (E := E) (α := α) (s := s) u)
    (chosenSecondJet (X := X) (E := E) (α := α) (s := s) v) htime hspace

/-- A higher norm-ball difference controls compact-coordinate values of chosen spatial
derivatives, provided the derivative choice is unique on the slices. -/
theorem norm_chosenSpaceDerivToContinuousMap_sub_apply_le_of_normLe_unique
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (z : K) :
    ‖chosenSpaceDerivToContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z -
        chosenSpaceDerivToContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v z‖
      ≤ N := by
  have hderiv := (chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    (X := X) (E := E) (α := α) (s := s) h htime hspace).2.1
  simpa using hderiv.norm_le (hK z.2)

/-- A higher norm-ball difference controls compact-coordinate values of chosen second spatial
derivatives, provided the derivative choice is unique on the slices. -/
theorem norm_chosenSpaceSecondDerivToContinuousMap_sub_apply_le_of_normLe_unique
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (z : K) :
    ‖chosenSpaceSecondDerivToContinuousMap
        (X := X) (E := E) (α := α) (s := s) hK hα u z -
      chosenSpaceSecondDerivToContinuousMap
        (X := X) (E := E) (α := α) (s := s) hK hα v z‖ ≤ N := by
  have hderiv := (chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    (X := X) (E := E) (α := α) (s := s) h htime hspace).2.2.1
  simpa using hderiv.norm_le (hK z.2)

/-- A higher norm-ball difference controls compact-coordinate values of chosen time derivatives,
provided the derivative choice is unique on the slices. -/
theorem norm_chosenTimeDerivToContinuousMap_sub_apply_le_of_normLe_unique
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (z : K) :
    ‖chosenTimeDerivToContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z -
        chosenTimeDerivToContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v z‖
      ≤ N := by
  have hderiv := (chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    (X := X) (E := E) (α := α) (s := s) h htime hspace).2.2.2
  simpa using hderiv.norm_le (hK z.2)

/-- A higher norm-ball difference controls finite-family compact-coordinate values of chosen
spatial derivatives, provided the derivative choice is unique on the slices. -/
theorem norm_chosenSpaceDerivToCompactCoordFamily_sub_apply_le_of_normLe_unique
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (i : κ) (z : Kc i) :
    ‖chosenSpaceDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z -
      chosenSpaceDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i z‖ ≤ N := by
  have hderiv := (chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    (X := X) (E := E) (α := α) (s := s) h htime hspace).2.1
  simpa using hderiv.norm_le (hKc i z.2)

/-- A higher norm-ball difference controls finite-family compact-coordinate values of chosen
second spatial derivatives, provided the derivative choice is unique on the slices. -/
theorem norm_chosenSpaceSecondDerivToCompactCoordFamily_sub_apply_le_of_normLe_unique
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (i : κ) (z : Kc i) :
    ‖chosenSpaceSecondDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z -
      chosenSpaceSecondDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i z‖ ≤ N := by
  have hderiv := (chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    (X := X) (E := E) (α := α) (s := s) h htime hspace).2.2.1
  simpa using hderiv.norm_le (hKc i z.2)

/-- A higher norm-ball difference controls finite-family compact-coordinate values of chosen
time derivatives, provided the derivative choice is unique on the slices. -/
theorem norm_chosenTimeDerivToCompactCoordFamily_sub_apply_le_of_normLe_unique
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (i : κ) (z : Kc i) :
    ‖chosenTimeDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z -
      chosenTimeDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i z‖ ≤ N := by
  have hderiv := (chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    (X := X) (E := E) (α := α) (s := s) h htime hspace).2.2.2
  simpa using hderiv.norm_le (hKc i z.2)

noncomputable local instance chosenSpaceSecondDerivContinuousMapPseudoMetricSpace
    {K : TopologicalSpace.Compacts (ℝ × X)} :
    PseudoMetricSpace C(K, X →L[ℝ] (X →L[ℝ] E)) :=
  @ContinuousMap.instPseudoMetricSpace K (X →L[ℝ] (X →L[ℝ] E))
    inferInstance inferInstance inferInstance

noncomputable local instance chosenSpaceSecondDerivContinuousMapSeminormedAddCommGroup
    {K : TopologicalSpace.Compacts (ℝ × X)} :
    SeminormedAddCommGroup C(K, X →L[ℝ] (X →L[ℝ] E)) :=
  @ContinuousMap.instSeminormedAddCommGroup K (X →L[ℝ] (X →L[ℝ] E))
    inferInstance inferInstance inferInstance

noncomputable local instance chosenSpaceSecondDerivContinuousMapNormedSpace
    {K : TopologicalSpace.Compacts (ℝ × X)} :
    NormedSpace ℝ C(K, X →L[ℝ] (X →L[ℝ] E)) :=
  @ContinuousMap.normedSpace K (X →L[ℝ] (X →L[ℝ] E))
    inferInstance inferInstance inferInstance ℝ inferInstance inferInstance

/-- Pairwise higher difference estimates give a Lipschitz estimate for the finite compact-family
readout of chosen spatial derivatives, provided the derivative choice is unique on the slices. -/
theorem lipschitzOnWith_chosenSpaceDerivToCompactCoordFamily_of_normLe_sub_unique
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α
        (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul
    (β := ∀ i, C(Kc i, X →L[ℝ] E))
    (f := fun u : Y =>
      chosenSpaceDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u)) ?_
  intro u hu v hv
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  refine (dist_pi_le_iff hC).2 fun i => ?_
  refine (ContinuousMap.dist_le hC).2 fun z => ?_
  have hnorm := norm_chosenSpaceDerivToCompactCoordFamily_sub_apply_le_of_normLe_unique
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv) htime hspace i z
  simpa [dist_eq_norm] using hnorm

/-- Pairwise higher difference estimates give a Lipschitz estimate for the finite compact-family
readout of chosen second spatial derivatives, provided the derivative choice is unique on the
slices. -/
theorem lipschitzOnWith_chosenSpaceSecondDerivToCompactCoordFamily_of_normLe_sub_unique
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α
        (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul
    (β := ∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E)))
    (f := fun u : Y =>
      chosenSpaceSecondDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u)) ?_
  intro u hu v hv
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  refine (dist_pi_le_iff hC).2 fun i => ?_
  refine (ContinuousMap.dist_le hC).2 fun z => ?_
  have hnorm := norm_chosenSpaceSecondDerivToCompactCoordFamily_sub_apply_le_of_normLe_unique
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv) htime hspace i z
  simpa [dist_eq_norm] using hnorm

/-- Pairwise higher difference estimates give a Lipschitz estimate for the finite compact-family
readout of chosen time derivatives, provided the derivative choice is unique on the slices. -/
theorem lipschitzOnWith_chosenTimeDerivToCompactCoordFamily_of_normLe_sub_unique
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α
        (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul
    (β := ∀ i, C(Kc i, E))
    (f := fun u : Y =>
      chosenTimeDerivToCompactCoordFamily
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u)) ?_
  intro u hu v hv
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  refine (dist_pi_le_iff hC).2 fun i => ?_
  refine (ContinuousMap.dist_le hC).2 fun z => ?_
  have hnorm := norm_chosenTimeDerivToCompactCoordFamily_sub_apply_le_of_normLe_unique
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv) htime hspace i z
  simpa [dist_eq_norm] using hnorm

/-- A finite compact-family chosen-spatial-derivative Lipschitz estimate gives pointwise
compact-coordinate distance estimates. -/
theorem forall_compactCoord_dist_le_of_chosenSpaceDerivToCompactCoordFamily_lipschitzOnWith
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : LipschitzOnWith L
      (fun u : Y =>
        chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kc i),
      dist
        (chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u) i z)
        (chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v) i z)
        ≤ (L : ℝ) * dist u v := by
  intro u hu v hv i z
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist :
      dist
        (chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
        (chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v))
        ≤ (L : ℝ) * dist u v :=
    LipschitzOnWith.dist_le_mul
      (β := ∀ i, C(Kc i, X →L[ℝ] E)) (K := L) (s := stateSet)
      (f := fun u : Y =>
        chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      h u hu v hv
  have hi :
      dist
        (chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u) i)
        (chosenSpaceDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v) i)
        ≤ (L : ℝ) * dist u v :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi z

/-- A finite compact-family chosen-second-spatial-derivative Lipschitz estimate gives pointwise
compact-coordinate distance estimates. -/
theorem forall_compactCoord_dist_le_of_chosenSpaceSecondDerivToCompactCoordFamily_lipschitzOnWith
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : LipschitzOnWith L
      (fun u : Y =>
        chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kc i),
      dist
        (chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u) i z)
        (chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v) i z)
        ≤ (L : ℝ) * dist u v := by
  intro u hu v hv i z
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist :
      dist
        (chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
        (chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v))
        ≤ (L : ℝ) * dist u v :=
    LipschitzOnWith.dist_le_mul
      (β := ∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) (K := L) (s := stateSet)
      (f := fun u : Y =>
        chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      h u hu v hv
  have hi :
      dist
        (chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u) i)
        (chosenSpaceSecondDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v) i)
        ≤ (L : ℝ) * dist u v :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi z

/-- A finite compact-family chosen-time-derivative Lipschitz estimate gives pointwise
compact-coordinate distance estimates. -/
theorem forall_compactCoord_dist_le_of_chosenTimeDerivToCompactCoordFamily_lipschitzOnWith
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : LipschitzOnWith L
      (fun u : Y =>
        chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kc i),
      dist
        (chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u) i z)
        (chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v) i z)
        ≤ (L : ℝ) * dist u v := by
  intro u hu v hv i z
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist :
      dist
        (chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
        (chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v))
        ≤ (L : ℝ) * dist u v :=
    LipschitzOnWith.dist_le_mul
      (β := ∀ i, C(Kc i, E)) (K := L) (s := stateSet)
      (f := fun u : Y =>
        chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      h u hu v hv
  have hi :
      dist
        (chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u) i)
        (chosenTimeDerivToCompactCoordFamily
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A v) i)
        ≤ (L : ℝ) * dist u v :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi z

theorem exists_timeDeriv (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ParabolicC0AlphaOn α Dt s :=
  u.2.exists_timeDeriv_c0AlphaOn

theorem exists_spaceDeriv (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ParabolicC0AlphaOn α Dx s :=
  u.2.exists_spaceDeriv_c0AlphaOn

theorem exists_spaceSecondDeriv (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ J : ParabolicSecondJet (u : (ℝ × X) → E) s,
      ParabolicC0AlphaOn α J.spaceSecondDeriv s :=
  u.2.exists_spaceSecondDeriv_c0AlphaOn

/-- Forget a coordinate parabolic `C^{2+α,1+α/2}` function to its value-level
`C^{0,α}` function. -/
def toC0AlphaSubmoduleLinearMap :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] parabolicC0AlphaSubmodule X E α s where
  toFun u := ⟨u.1, u.2.c0AlphaOn⟩
  map_add' := by
    intro u v
    ext z
    rfl
  map_smul' := by
    intro c u
    ext z
    rfl

@[simp]
theorem toC0AlphaSubmoduleLinearMap_apply
    (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) u z = u z :=
  rfl

/-- Read a coordinate parabolic `C^{2+α,1+α/2}` function as a continuous map on a compact
time-space piece, using its value-level `C^{0,α}` component. -/
def toContinuousMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : C(K, E) :=
  parabolicC0AlphaSubmodule.toContinuousMap
    (X := X) (E := E) (α := α) (s := s) hK hα
    (toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem toContinuousMap_apply {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (z : K) :
    toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z = u z.1 :=
  rfl

/-- Compact-piece value readout of a coordinate parabolic `C^{2+α,1+α/2}` function as a
linear map. -/
def toContinuousMapLinearMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] C(K, E) where
  toFun := toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα
  map_add' := by
    intro u v
    ext z
    rfl
  map_smul' := by
    intro c u
    ext z
    rfl

@[simp]
theorem toContinuousMapLinearMap_apply {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) :
    toContinuousMapLinearMap (X := X) (E := E) (α := α) (s := s) hK hα u =
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u :=
  rfl

/-- A single-radius `C^{2+α,1+α/2}` bound on a difference controls the compact value
readout sup norm. -/
theorem norm_toContinuousMap_sub_le_of_normLe {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v‖ ≤ N := by
  have h0 :
      ParabolicC0AlphaNormLe N α
        (fun z =>
          toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) u z -
            toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) v z) s := by
    simpa using h.value_c0AlphaNormLe_self
  simpa [toContinuousMap] using
    parabolicC0AlphaSubmodule.norm_toContinuousMap_sub_le_of_normLe
      (X := X) (E := E) (α := α) (s := s) hK hα h0

/-- Componentwise higher difference controls with radii linear in a shared scalar control the
compact readout sup norm of a finite Pi-valued higher parabolic function. -/
theorem norm_toContinuousMap_pi_sub_le_sum_mul_of_entries
    {Kc : TopologicalSpace.Compacts (ℝ × X)}
    (hKc : (Kc : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    ‖toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα u -
        toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα v‖ ≤
      (∑ i, K i) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, K i :=
    Finset.sum_nonneg fun i _hi => hK_nonneg i
  have htarget_nonneg : 0 ≤ (∑ i, K i) * R :=
    mul_nonneg hsum_nonneg hR
  refine (ContinuousMap.norm_le
    (f := toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα u -
      toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα v)
    htarget_nonneg).mpr ?_
  intro z
  have hz : z.1 ∈ s := hKc z.2
  calc
    ‖(toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα u -
        toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα v) z‖ =
        ‖u z.1 - v z.1‖ := by
          rfl
    _ ≤ (∑ i, K i) * R :=
        ParabolicC2AlphaNormLe.pi_norm_sub_le_sum_mul_of_entries
          (X := X) (α := α) (s := s) hK_nonneg hR h hz

/-- Pairwise single-radius `C^{2+α,1+α/2}` difference estimates give a Lipschitz estimate
for one compact value readout. -/
theorem lipschitzOnWith_toContinuousMap_of_normLe_sub {Y : Type*} [PseudoMetricSpace Y]
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y => toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) hK hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Componentwise higher difference estimates with finite Pi constants give a Lipschitz
estimate for one compact value readout of a finite Pi-valued higher parabolic function. -/
theorem lipschitzOnWith_toContinuousMap_pi_of_component_normLe_sub
    {Y ι F : Type*} [PseudoMetricSpace Y] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Kc : TopologicalSpace.Compacts (ℝ × X)}
    (hKc : (Kc : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} (K : ι → ℝ≥0)
    {A : Y → parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC2AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    LipschitzOnWith (∑ i, K i)
      (fun u : Y =>
        toContinuousMap (X := X) (E := ι → F) (α := α) (s := s) hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_pi_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) hKc hα
    (K := fun i => (K i : ℝ)) (R := dist u v)
    (fun i => NNReal.coe_nonneg (K i)) dist_nonneg (fun i => h hu hv i)
  simpa [dist_eq_norm, NNReal.coe_sum] using hnorm

/-- Read a coordinate parabolic `C^{2+α,1+α/2}` function on every compact piece of a chosen
cover, using its value-level `C^{0,α}` component. -/
def toCompactCoordFamily {κ : Type*} (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : ∀ i, C(Kc i, E) :=
  fun i => toContinuousMap (X := X) (E := E) (α := α) (s := s) (hKc i) hα u

@[simp]
theorem toCompactCoordFamily_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (i : κ) (z : Kc i) :
    toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z =
      u z.1 :=
  rfl

/-- Finite-cover value readout as a linear map from coordinate parabolic
`C^{2+α,1+α/2}` functions into compact continuous-map pieces. -/
def toCompactCoordFamilyLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] (∀ i, C(Kc i, E)) where
  toFun := toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  map_add' := by
    intro u v
    ext i z
    rfl
  map_smul' := by
    intro c u
    ext i z
    rfl

@[simp]
theorem toCompactCoordFamilyLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) :
    toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u =
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u :=
  rfl

/-- A single-radius `C^{2+α,1+α/2}` difference bound controls each compact-family value
readout. -/
theorem norm_toCompactCoordFamily_sub_le_of_normLe {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) (i : κ) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i‖ ≤ N :=
  norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) (hKc i) hα h

/-- A single-radius `C^{2+α,1+α/2}` difference bound controls the finite product of
compact-family value readouts in the product sup norm. -/
theorem norm_toCompactCoordFamily_family_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v‖ ≤ N := by
  refine (pi_norm_le_iff_of_nonneg h.nonneg).2 fun i => ?_
  exact norm_toCompactCoordFamily_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h i

/-- Componentwise higher difference controls with radii linear in a shared scalar control the
finite product of compact-family value readouts for finite Pi-valued higher parabolic functions. -/
theorem norm_toCompactCoordFamily_pi_family_sub_le_sum_mul_of_entries {κ ι F : Type*}
    [Fintype κ] [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    ‖toCompactCoordFamily (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamily (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα v‖ ≤
      (∑ i, K i) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, K i :=
    Finset.sum_nonneg fun i _hi => hK_nonneg i
  have htarget_nonneg : 0 ≤ (∑ i, K i) * R :=
    mul_nonneg hsum_nonneg hR
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i => ?_
  exact norm_toContinuousMap_pi_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) (hKc i) hα hK_nonneg hR h

/-- Pairwise single-radius `C^{2+α,1+α/2}` difference estimates give a Lipschitz estimate
for the finite product of compact-family value readouts. -/
theorem lipschitzOnWith_toCompactCoordFamily_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Componentwise higher difference estimates with finite Pi constants give a Lipschitz
estimate for the finite compact-family value readout of a finite Pi-valued higher parabolic
function. -/
theorem lipschitzOnWith_toCompactCoordFamily_pi_of_component_normLe_sub
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} (K : ι → ℝ≥0)
    {A : Y → parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC2AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    LipschitzOnWith (∑ i, K i)
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := ι → F) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_pi_family_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) Kc hKc hα
    (K := fun i => (K i : ℝ)) (R := dist u v)
    (fun i => NNReal.coe_nonneg (K i)) dist_nonneg (fun i => h hu hv i)
  simpa [dist_eq_norm, NNReal.coe_sum] using hnorm

/-- A finite compact-family value-readout Lipschitz estimate gives pointwise compact-coordinate
distance estimates. -/
theorem forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kc i),
      dist
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u) i z)
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A v) i z)
        ≤ (L : ℝ) * dist u v := by
  intro u hu v hv i z
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist := h.dist_le_mul u hu v hv
  have hi :
      dist
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u) i)
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A v) i)
        ≤ (L : ℝ) * dist u v :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi z

/-- Pointwise compact-coordinate estimates on time-space compact pieces give fixed-time spatial
readout estimates for higher parabolic functions whenever those pieces cover the requested time
slices. -/
theorem forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le {Y κ ι : Type*}
    [PseudoMetricSpace Y]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {K : ℝ}
    {A : ℝ → Y → parabolicC2AlphaSubmodule X E α s}
    (hcompact : ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet →
      ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ j (z : Kdom j),
        dist
          (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ u) j z)
          (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ v) j z)
          ≤ K * dist u v)
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A τ u (τ, x.1)) (A τ v (τ, x.1)) ≤ K * dist u v := by
  intro τ hτ u hu v hv i x
  rcases hcover τ hτ i x with ⟨j, hzmem⟩
  let z : Kdom j := ⟨(τ, x.1), hzmem⟩
  have hz := hcompact τ hτ hu hv j z
  simpa [z] using hz

/-- A time-dependent finite compact-family higher-parabolic readout Lipschitz estimate gives
fixed-time spatial readout estimates whenever the time-space compact pieces cover each requested
time slice. -/
theorem forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    {Y κ ι : Type*} [PseudoMetricSpace Y] [Fintype ι]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {L : ℝ≥0}
    {A : ℝ → Y → parabolicC2AlphaSubmodule X E α s}
    (hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun u : Y =>
          toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
            Kdom hKdom hα (A τ u))
        stateSet)
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist (A τ u (τ, x.1)) (A τ v (τ, x.1)) ≤ (L : ℝ) * dist u v := by
  refine forall_timeSlice_spatial_dist_le_of_forall_compactCoord_dist_le
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx
    (A := A) (K := (L : ℝ)) ?_ hcover
  intro τ hτ
  exact forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (hLip τ hτ)

/-- A time-dependent finite compact-family chosen-spatial-derivative readout Lipschitz estimate
gives fixed-time spatial readout estimates whenever the time-space compact pieces cover each
requested time slice. -/
theorem forall_timeSlice_spatial_dist_le_of_chosenSpaceDerivToCompactCoordFamily_lipschitzOnWith
    {Y κ ι : Type*} [PseudoMetricSpace Y] [Fintype ι]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {L : ℝ≥0}
    {A : ℝ → Y → parabolicC2AlphaSubmodule X E α s}
    (hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun u : Y =>
          chosenSpaceDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (A τ u))
        stateSet)
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist
          ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
            (A τ u)).spaceDeriv (τ, x.1))
          ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
            (A τ v)).spaceDeriv (τ, x.1)) ≤
          (L : ℝ) * dist u v := by
  intro τ hτ u hu v hv i x
  rcases hcover τ hτ i x with ⟨j, hzmem⟩
  let z : Kdom j := ⟨(τ, x.1), hzmem⟩
  have hz :=
    forall_compactCoord_dist_le_of_chosenSpaceDerivToCompactCoordFamily_lipschitzOnWith
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (hLip τ hτ)
      hu hv j z
  simpa [z] using hz

/-- A time-dependent finite compact-family chosen-second-spatial-derivative readout Lipschitz
estimate gives fixed-time spatial readout estimates whenever the time-space compact pieces cover
each requested time slice. -/
theorem forall_timeSlice_spatial_dist_le_of_chosenSpaceSecondDerivToCompactCoordFamily_lipschitzOnWith
    {Y κ ι : Type*} [PseudoMetricSpace Y] [Fintype ι]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {L : ℝ≥0}
    {A : ℝ → Y → parabolicC2AlphaSubmodule X E α s}
    (hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun u : Y =>
          chosenSpaceSecondDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (A τ u))
        stateSet)
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist
          ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
            (A τ u)).spaceSecondDeriv (τ, x.1))
          ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
            (A τ v)).spaceSecondDeriv (τ, x.1)) ≤
          (L : ℝ) * dist u v := by
  intro τ hτ u hu v hv i x
  rcases hcover τ hτ i x with ⟨j, hzmem⟩
  let z : Kdom j := ⟨(τ, x.1), hzmem⟩
  have hz :=
    forall_compactCoord_dist_le_of_chosenSpaceSecondDerivToCompactCoordFamily_lipschitzOnWith
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (hLip τ hτ)
      hu hv j z
  simpa [z] using hz

/-- A time-dependent finite compact-family chosen-time-derivative readout Lipschitz estimate gives
fixed-time spatial readout estimates whenever the time-space compact pieces cover each requested
time slice. -/
theorem forall_timeSlice_spatial_dist_le_of_chosenTimeDerivToCompactCoordFamily_lipschitzOnWith
    {Y κ ι : Type*} [PseudoMetricSpace Y] [Fintype ι]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : κ → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ} {stateSet : Set Y} {L : ℝ≥0}
    {A : ℝ → Y → parabolicC2AlphaSubmodule X E α s}
    (hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun u : Y =>
          chosenTimeDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (A τ u))
        stateSet)
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ i (x : Kx i),
        dist
          ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
            (A τ u)).timeDeriv (τ, x.1))
          ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
            (A τ v)).timeDeriv (τ, x.1)) ≤
          (L : ℝ) * dist u v := by
  intro τ hτ u hu v hv i x
  rcases hcover τ hτ i x with ⟨j, hzmem⟩
  let z : Kdom j := ⟨(τ, x.1), hzmem⟩
  have hz :=
    forall_compactCoord_dist_le_of_chosenTimeDerivToCompactCoordFamily_lipschitzOnWith
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα (hLip τ hτ)
      hu hv j z
  simpa [z] using hz

/-- The linear compact-family value readout inherits the same finite product sup-norm
estimate from `C^{2+α,1+α/2}` difference control. -/
theorem norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v‖ ≤ N := by
  simpa using norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- The linear finite-cover value readout inherits the finite-Pi componentwise
summed-radius estimate. -/
theorem norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα v‖ ≤
      (∑ i, K i) * R := by
  simpa using norm_toCompactCoordFamily_pi_family_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- Pairwise single-radius `C^{2+α,1+α/2}` difference estimates give a Lipschitz estimate
for the linear finite-cover value readout. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Componentwise higher difference estimates with finite Pi constants give a Lipschitz
estimate for the linear finite-cover value readout of a finite Pi-valued higher parabolic
function. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_pi_of_component_normLe_sub
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} (K : ι → ℝ≥0)
    {A : Y → parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC2AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    LipschitzOnWith (∑ i, K i)
      (fun u : Y =>
        toCompactCoordFamilyLinearMap (X := X) (E := ι → F) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
    (X := X) (α := α) (s := s) Kc hKc hα
    (K := fun i => (K i : ℝ)) (R := dist u v)
    (fun i => NNReal.coe_nonneg (K i)) dist_nonneg (fun i => h hu hv i)
  simpa [dist_eq_norm, NNReal.coe_sum] using hnorm

/-- Equality of all compact-piece value readouts identifies two coordinate parabolic
`C^{2+α,1+α/2}` functions on any covered subset. -/
theorem eqOn_subset_of_toCompactCoordFamily_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    {t : Set (ℝ × X)} (hcover : t ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC2AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v) :
    EqOn u v t := by
  intro z hz
  rcases mem_iUnion.mp (hcover hz) with ⟨i, hzi⟩
  have hz_eq :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i ⟨z, hzi⟩ =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i ⟨z, hzi⟩ := by
    rw [h]
  simpa using hz_eq

/-- Equality of all compact-piece value readouts identifies two coordinate parabolic
`C^{2+α,1+α/2}` functions on the covered set. -/
theorem eqOn_of_toCompactCoordFamily_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    (hcover : s ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC2AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v) :
    EqOn u v s :=
  eqOn_subset_of_toCompactCoordFamily_eq
    (X := X) (E := E) (α := α) (s := s) hcover h

/-- Product compact value readouts determine higher parabolic functions on `Kt × U` whenever `U`
is covered by the spatial compact family. -/
theorem eqOn_timeSpaceProduct_of_toCompactCoordFamily_eq {κ : Type*}
    (Kt : TopologicalSpace.Compacts ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {hKc : ∀ i, (timeSpaceProductCompactFamily Kt Kx i : Set (ℝ × X)) ⊆ s}
    {hα : 0 < α} {U : Set X} (hU : U ⊆ ⋃ i, (Kx i : Set X))
    {u v : parabolicC2AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceProductCompactFamily Kt Kx) hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceProductCompactFamily Kt Kx) hKc hα v) :
    EqOn u v ((Kt : Set ℝ) ×ˢ U) :=
  eqOn_subset_of_toCompactCoordFamily_eq
    (X := X) (E := E) (α := α) (s := s)
    (Kc := timeSpaceProductCompactFamily Kt Kx) (hKc := hKc) (hα := hα)
    (timeSpaceProductCompactFamily_product_subset_iUnion_of_subset Kt Kx hU) h

/-- Interval product compact value readouts determine higher parabolic functions on
`Icc t₀ T × U` whenever `U` is covered by the spatial compact family. -/
theorem eqOn_timeSpaceIccProduct_of_toCompactCoordFamily_eq {κ : Type*}
    (t₀ T : ℝ) (Kx : κ → TopologicalSpace.Compacts X)
    {hKc : ∀ i, (timeSpaceIccCompactFamily t₀ T Kx i : Set (ℝ × X)) ⊆ s}
    {hα : 0 < α} {U : Set X} (hU : U ⊆ ⋃ i, (Kx i : Set X))
    {u v : parabolicC2AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceIccCompactFamily t₀ T Kx) hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          (timeSpaceIccCompactFamily t₀ T Kx) hKc hα v) :
    EqOn u v (Icc t₀ T ×ˢ U) :=
  eqOn_timeSpaceProduct_of_toCompactCoordFamily_eq
    (X := X) (E := E) (α := α) (s := s)
    (timeIccCompact t₀ T) Kx (hKc := hKc) (hα := hα) hU h

/-- Compact value readout is injective on coordinate parabolic `C^{2+α,1+α/2}` functions
when the chosen compact pieces cover all time-space. -/
theorem toCompactCoordFamily_injective_of_iUnion_eq_univ {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    Function.Injective
      (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα) := by
  intro u v h
  ext z
  have hzcover : z ∈ ⋃ i, (Kc i : Set (ℝ × X)) := by
    simp [hcover]
  rcases mem_iUnion.mp hzcover with ⟨i, hzi⟩
  have hz_eq :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i ⟨z, hzi⟩ =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i ⟨z, hzi⟩ := by
    rw [h]
  simpa using hz_eq

/-- The finite compact-family value readout induces a seminormed additive-group structure on the
higher parabolic submodule.  This is the finite-cover value norm inherited from the lower
`C^{0,α}` readout; it does not yet encode derivative Holder seminorms or Schauder completeness. -/
@[reducible] noncomputable def finiteCoverValueSeminormedAddCommGroup {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
  SeminormedAddCommGroup.induced
    (parabolicC2AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα)

/-- The same finite compact-family value readout makes the higher parabolic submodule a seminormed
real vector space. -/
@[reducible] noncomputable def finiteCoverValueNormedSpace {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    @NormedSpace ℝ (parabolicC2AlphaSubmodule X E α s) _
      (finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα) :=
  NormedSpace.induced ℝ
    (parabolicC2AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα)

/-- If the compact pieces cover all time-space, the finite compact-family value readout norm is
separated on higher parabolic functions. -/
@[reducible] noncomputable def finiteCoverValueNormedAddCommGroupOfCover {κ : Type*}
    [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
  NormedAddCommGroup.induced
    (parabolicC2AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα)
    (toCompactCoordFamily_injective_of_iUnion_eq_univ
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover)

/-- The real vector-space structure paired with
`finiteCoverValueNormedAddCommGroupOfCover`. -/
@[reducible] noncomputable def finiteCoverValueNormedSpaceOfCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    @NormedSpace ℝ (parabolicC2AlphaSubmodule X E α s) _
      (finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover).toSeminormedAddCommGroup :=
  finiteCoverValueNormedSpace (X := X) (E := E) (α := α) (s := s) Kc hKc hα

/-- With the finite-cover seminormed structure, the higher value norm is definitionally the
compact-family readout norm. -/
theorem finiteCoverValue_norm_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    ‖u‖ =
      ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u‖ :=
  rfl

/-- With the finite-cover seminormed structure, higher value distance is definitionally the
compact-family readout distance. -/
theorem finiteCoverValue_dist_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    dist u v =
      dist
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u)
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα v) :=
  rfl

/-- With the separated all-cover finite-cover value normed structure, the higher value norm is
definitionally the compact-family readout norm. -/
theorem finiteCoverValue_norm_eq_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    ‖u‖ =
      ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u‖ :=
  rfl

/-- With the separated all-cover finite-cover value normed structure, higher value distance is
definitionally the compact-family readout distance. -/
theorem finiteCoverValue_dist_eq_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    dist u v =
      dist
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u)
        (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα v) :=
  rfl

/-- A higher norm-ball difference controls the induced finite-cover value distance. -/
theorem finiteCoverValue_dist_le_of_normLe_sub {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    dist u v ≤ N := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  rw [finiteCoverValue_dist_eq (X := X) (E := E) (α := α) (s := s)
    Kc hKc hα u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- A higher norm-ball difference gives induced finite-cover value closed-ball membership. -/
theorem finiteCoverValue_mem_closedBall_of_normLe_sub {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    u ∈ Metric.closedBall v N := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_of_normLe_sub
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- Symmetric induced finite-cover value closed-ball membership from a higher difference bound. -/
theorem finiteCoverValue_mem_closedBall_symm_of_normLe_sub {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    v ∈ Metric.closedBall u N := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_of_normLe_sub
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- Componentwise higher finite-Pi difference controls with finite-Pi constants control the
induced finite-cover value distance. -/
theorem finiteCoverValue_dist_le_pi_of_component_normLe_sub
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    dist u v ≤ (∑ i, K i) * R := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  rw [finiteCoverValue_dist_eq (X := X) (E := ι → F) (α := α) (s := s)
    Kc hKc hα u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- Componentwise higher finite-Pi bounds give induced finite-cover value closed-ball
membership. -/
theorem finiteCoverValue_mem_closedBall_pi_of_component_normLe_sub
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    u ∈ Metric.closedBall v ((∑ i, K i) * R) := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- Symmetric induced finite-cover value closed-ball membership from componentwise higher
finite-Pi bounds. -/
theorem finiteCoverValue_mem_closedBall_symm_pi_of_component_normLe_sub
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    v ∈ Metric.closedBall u ((∑ i, K i) * R) := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- A higher norm-ball difference controls the separated all-cover finite-cover value distance. -/
theorem finiteCoverValue_dist_le_of_normLe_sub_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    dist u v ≤ N := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  rw [finiteCoverValue_dist_eq_ofCover (X := X) (E := E) (α := α) (s := s)
    Kc hKc hα hcover u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- A higher norm-ball difference gives separated all-cover finite-cover value closed-ball
membership. -/
theorem finiteCoverValue_mem_closedBall_of_normLe_sub_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    u ∈ Metric.closedBall v N := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_of_normLe_sub_ofCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover h

/-- Symmetric separated all-cover finite-cover value closed-ball membership from a higher
difference bound. -/
theorem finiteCoverValue_mem_closedBall_symm_of_normLe_sub_ofCover {κ : Type*}
    [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
    v ∈ Metric.closedBall u N := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_of_normLe_sub_ofCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hcover h

/-- Componentwise higher finite-Pi difference controls with finite-Pi constants control the
separated all-cover finite-cover value distance. -/
theorem finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    dist u v ≤ (∑ i, K i) * R := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  rw [finiteCoverValue_dist_eq_ofCover (X := X) (E := ι → F) (α := α) (s := s)
    Kc hKc hα hcover u v]
  simpa [dist_eq_norm] using
    norm_toCompactCoordFamilyLinearMap_pi_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) Kc hKc hα hK_nonneg hR h

/-- Componentwise higher finite-Pi bounds give separated all-cover finite-cover value closed-ball
membership. -/
theorem finiteCoverValue_mem_closedBall_pi_of_component_normLe_sub_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    u ∈ Metric.closedBall v ((∑ i, K i) * R) := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα hcover hK_nonneg hR h

/-- Symmetric separated all-cover finite-cover value closed-ball membership from componentwise
higher finite-Pi bounds. -/
theorem finiteCoverValue_mem_closedBall_symm_pi_of_component_normLe_sub_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (hK_nonneg : ∀ i, 0 ≤ K i) (hR : 0 ≤ R)
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    v ∈ Metric.closedBall u ((∑ i, K i) * R) := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα hcover hK_nonneg hR h

/-- Pairwise componentwise higher estimates give a Lipschitz estimate in the induced
finite-cover value seminorm. -/
theorem lipschitzOnWith_finiteCoverValue_pi_of_component_normLe_sub
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {K : ι → ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC2AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
    LipschitzOnWith (∑ i, K i) A stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hdist :
      dist (A u) (A v) ≤ (∑ i, (K i : ℝ)) * dist u v :=
    finiteCoverValue_dist_le_pi_of_component_normLe_sub
      (X := X) (α := α) (s := s) Kc hKc hα
      (R := dist u v) (K := fun i => (K i : ℝ)) (u := A u) (v := A v)
      (fun i => (K i).2) dist_nonneg (h hu hv)
  simpa [NNReal.coe_sum] using hdist

/-- Pairwise componentwise higher estimates give a Lipschitz estimate in the separated all-cover
finite-cover value norm. -/
theorem lipschitzOnWith_finiteCoverValue_pi_of_component_normLe_sub_ofCover
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {stateSet : Set Y} {K : ι → ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC2AlphaNormLe ((K i : ℝ) * dist u v) α
        (fun z => A u z i - A v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverValueNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
    LipschitzOnWith (∑ i, K i) A stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverValueNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hcover
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hdist :
      dist (A u) (A v) ≤ (∑ i, (K i : ℝ)) * dist u v :=
    finiteCoverValue_dist_le_pi_of_component_normLe_sub_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα hcover
      (R := dist u v) (K := fun i => (K i : ℝ)) (u := A u) (v := A v)
      (fun i => (K i).2) dist_nonneg (h hu hv)
  simpa [NNReal.coe_sum] using hdist

/-- The finite compact-family chosen spatial-derivative readout induces a seminormed additive
group structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenSpaceDerivSeminormedAddCommGroup
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
  SeminormedAddCommGroup.induced
    (parabolicC2AlphaSubmodule X E α s) (∀ i, C(Kc i, X →L[ℝ] E))
    (chosenSpaceDerivToCompactCoordFamilyLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace)

/-- The finite compact-family chosen spatial-derivative readout induces a seminormed real vector
space structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenSpaceDerivNormedSpace
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    @NormedSpace ℝ (parabolicC2AlphaSubmodule X E α s) _
      (finiteCoverChosenSpaceDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace) :=
  NormedSpace.induced ℝ
    (parabolicC2AlphaSubmodule X E α s) (∀ i, C(Kc i, X →L[ℝ] E))
    (chosenSpaceDerivToCompactCoordFamilyLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace)

/-- With the finite-cover chosen-spatial-derivative seminormed structure, the norm is
definitionally the chosen derivative compact-family readout norm. -/
theorem finiteCoverChosenSpaceDeriv_norm_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSpaceDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace
    ‖u‖ =
      ‖chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u‖ :=
  rfl

/-- With the finite-cover chosen-spatial-derivative seminormed structure, distance is
definitionally the chosen derivative compact-family readout distance. -/
theorem finiteCoverChosenSpaceDeriv_dist_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSpaceDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace
    dist u v =
      dist
        (chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
        (chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v) :=
  rfl

/-- The finite compact-family chosen second-spatial-derivative readout induces a seminormed
additive-group structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenSpaceSecondDerivSeminormedAddCommGroup
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
  SeminormedAddCommGroup.induced
    (parabolicC2AlphaSubmodule X E α s)
    (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E)))
    (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace)

/-- The finite compact-family chosen second-spatial-derivative readout induces a seminormed real
vector-space structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenSpaceSecondDerivNormedSpace
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    @NormedSpace ℝ (parabolicC2AlphaSubmodule X E α s) _
      (finiteCoverChosenSpaceSecondDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace) :=
  NormedSpace.induced ℝ
    (parabolicC2AlphaSubmodule X E α s)
    (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E)))
    (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace)

/-- With the finite-cover chosen-second-spatial-derivative seminormed structure, the norm is
definitionally the chosen derivative compact-family readout norm. -/
theorem finiteCoverChosenSpaceSecondDeriv_norm_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSpaceSecondDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace
    ‖u‖ =
      ‖chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u‖ :=
  rfl

/-- With the finite-cover chosen-second-spatial-derivative seminormed structure, distance is
definitionally the chosen derivative compact-family readout distance. -/
theorem finiteCoverChosenSpaceSecondDeriv_dist_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSpaceSecondDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace
    dist u v =
      dist
        (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
        (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v) :=
  rfl

/-- The finite compact-family chosen time-derivative readout induces a seminormed additive-group
structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenTimeDerivSeminormedAddCommGroup
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1) :
    SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
  SeminormedAddCommGroup.induced
    (parabolicC2AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (chosenTimeDerivToCompactCoordFamilyLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime)

/-- The finite compact-family chosen time-derivative readout induces a seminormed real vector-space
structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenTimeDerivNormedSpace
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1) :
    @NormedSpace ℝ (parabolicC2AlphaSubmodule X E α s) _
      (finiteCoverChosenTimeDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime) :=
  NormedSpace.induced ℝ
    (parabolicC2AlphaSubmodule X E α s) (∀ i, C(Kc i, E))
    (chosenTimeDerivToCompactCoordFamilyLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime)

/-- With the finite-cover chosen-time-derivative seminormed structure, the norm is definitionally
the chosen derivative compact-family readout norm. -/
theorem finiteCoverChosenTimeDeriv_norm_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenTimeDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime
    ‖u‖ =
      ‖chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u‖ :=
  rfl

/-- With the finite-cover chosen-time-derivative seminormed structure, distance is definitionally
the chosen derivative compact-family readout distance. -/
theorem finiteCoverChosenTimeDeriv_dist_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenTimeDerivSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime
    dist u v =
      dist
        (chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u)
        (chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime v) :=
  rfl

/-- The chosen spatial-derivative finite-cover readout target is complete when
the value model is complete. This records target-space completeness only, not
closedness of any induced readout image. -/
theorem finiteCoverChosenSpaceDerivReadoutTarget_completeSpace
    {κ : Type*} [Fintype κ] [CompleteSpace E]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    CompleteSpace (∀ i, C(Kc i, X →L[ℝ] E)) := by
  letI : CompleteSpace (X →L[ℝ] E) := inferInstance
  exact
    parabolicC0AlphaSubmodule.finiteCoverValueReadoutTarget_completeSpace
      (X := X) (E := X →L[ℝ] E) Kc

/-- The chosen second-spatial-derivative finite-cover readout target is complete
when the value model is complete. This records target-space completeness only,
not closedness of any induced readout image. -/
theorem finiteCoverChosenSpaceSecondDerivReadoutTarget_completeSpace
    {κ : Type*} [Fintype κ] [CompleteSpace E]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    CompleteSpace (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := by
  letI : CompleteSpace (X →L[ℝ] E) := inferInstance
  letI : CompleteSpace (X →L[ℝ] (X →L[ℝ] E)) := inferInstance
  exact
    parabolicC0AlphaSubmodule.finiteCoverValueReadoutTarget_completeSpace
      (X := X) (E := X →L[ℝ] (X →L[ℝ] E)) Kc

/-- The chosen time-derivative finite-cover readout target is complete when the
value model is complete. This records target-space completeness only, not
closedness of any induced readout image. -/
theorem finiteCoverChosenTimeDerivReadoutTarget_completeSpace
    {κ : Type*} [Fintype κ] [CompleteSpace E]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    CompleteSpace (∀ i, C(Kc i, E)) :=
  parabolicC0AlphaSubmodule.finiteCoverValueReadoutTarget_completeSpace
    (X := X) (E := E) Kc

/-- Product target for finite-cover readouts of a value and its chosen parabolic second jet.  This
is still a compact-family sup readout, not a full parabolic Hölder norm. -/
abbrev chosenSecondJetFiniteCoverReadoutTarget {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :=
  ((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) ×
    ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E)))

local instance chosenSecondJetFiniteCoverReadoutTargetModule {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    Module ℝ (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc) := by
  dsimp [chosenSecondJetFiniteCoverReadoutTarget]
  letI : Module ℝ (∀ i, C(Kc i, E)) := inferInstance
  letI : Module ℝ (∀ i, C(Kc i, X →L[ℝ] E)) := inferInstance
  letI : Module ℝ (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := inferInstance
  letI : Module ℝ ((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) :=
    inferInstance
  letI : Module ℝ
      ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E))) :=
    inferInstance
  infer_instance

noncomputable local instance chosenSecondJetFiniteCoverReadoutTargetSeminormedAddCommGroup
    {κ : Type*} [Fintype κ] (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    SeminormedAddCommGroup
      (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc) := by
  dsimp [chosenSecondJetFiniteCoverReadoutTarget]
  letI : SeminormedAddCommGroup (∀ i, C(Kc i, E)) := inferInstance
  letI : SeminormedAddCommGroup (∀ i, C(Kc i, X →L[ℝ] E)) := inferInstance
  letI : SeminormedAddCommGroup
      (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := inferInstance
  letI : SeminormedAddCommGroup
      ((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) :=
    inferInstance
  letI : SeminormedAddCommGroup
      ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E))) :=
    inferInstance
  infer_instance

noncomputable local instance chosenSecondJetFiniteCoverReadoutTargetNormedAddCommGroup
    {κ : Type*} [Fintype κ] (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    NormedAddCommGroup
      (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc) := by
  dsimp [chosenSecondJetFiniteCoverReadoutTarget]
  letI : (i : κ) → NormedAddCommGroup C(Kc i, E) := fun _ => inferInstance
  letI : (i : κ) → NormedAddCommGroup C(Kc i, X →L[ℝ] E) := fun _ =>
    inferInstance
  letI : (i : κ) → NormedAddCommGroup C(Kc i, X →L[ℝ] (X →L[ℝ] E)) :=
    fun i => @ContinuousMap.instNormedAddCommGroup (Kc i) inferInstance inferInstance
      (X →L[ℝ] (X →L[ℝ] E)) inferInstance
  letI : NormedAddCommGroup (∀ i, C(Kc i, E)) := Pi.normedAddCommGroup
  letI : NormedAddCommGroup (∀ i, C(Kc i, X →L[ℝ] E)) := Pi.normedAddCommGroup
  letI : NormedAddCommGroup
      (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := Pi.normedAddCommGroup
  letI : NormedAddCommGroup
      ((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) :=
    inferInstance
  letI : NormedAddCommGroup
      ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E))) :=
    inferInstance
  exact Prod.normedAddCommGroup

noncomputable local instance chosenSecondJetFiniteCoverReadoutTargetNormedSpace
    {κ : Type*} [Fintype κ] (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    NormedSpace ℝ (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc) := by
  dsimp [chosenSecondJetFiniteCoverReadoutTarget]
  letI : Module ℝ (∀ i, C(Kc i, E)) := inferInstance
  letI : Module ℝ (∀ i, C(Kc i, X →L[ℝ] E)) := inferInstance
  letI : Module ℝ (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := inferInstance
  letI : SeminormedAddCommGroup (∀ i, C(Kc i, E)) := inferInstance
  letI : SeminormedAddCommGroup (∀ i, C(Kc i, X →L[ℝ] E)) := inferInstance
  letI : SeminormedAddCommGroup
      (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := inferInstance
  letI : NormedSpace ℝ (∀ i, C(Kc i, E)) := inferInstance
  letI : NormedSpace ℝ (∀ i, C(Kc i, X →L[ℝ] E)) := inferInstance
  letI : NormedSpace ℝ
      (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := inferInstance
  letI : Module ℝ ((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) :=
    inferInstance
  letI : Module ℝ
      ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E))) :=
    inferInstance
  letI : SeminormedAddCommGroup
      ((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) :=
    inferInstance
  letI : SeminormedAddCommGroup
      ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E))) :=
    inferInstance
  letI : NormedSpace ℝ
      ((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) :=
    inferInstance
  letI : NormedSpace ℝ
      ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E))) :=
    inferInstance
  letI : Module ℝ
      (((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) ×
        ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E)))) :=
    inferInstance
  letI : SeminormedAddCommGroup
      (((∀ i, C(Kc i, E)) × (∀ i, C(Kc i, X →L[ℝ] E))) ×
        ((∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) × (∀ i, C(Kc i, E)))) :=
    inferInstance
  exact Prod.normedSpace (𝕜 := ℝ)

/-- The finite-cover target of the combined chosen second-jet readout is complete when the
fiber model is complete.  This records completeness of the ambient product target only; it
does not assert closedness of the readout image in that product. -/
theorem chosenSecondJetFiniteCoverReadoutTarget_completeSpace
    {κ : Type*} [Fintype κ] [CompleteSpace E]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    CompleteSpace (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc) := by
  dsimp [chosenSecondJetFiniteCoverReadoutTarget]
  letI : (i : κ) → NormedAddCommGroup C(Kc i, E) := fun _ => inferInstance
  letI : (i : κ) → NormedAddCommGroup C(Kc i, X →L[ℝ] E) := fun _ =>
    inferInstance
  letI : (i : κ) → NormedAddCommGroup C(Kc i, X →L[ℝ] (X →L[ℝ] E)) :=
    fun i => @ContinuousMap.instNormedAddCommGroup (Kc i) inferInstance inferInstance
      (X →L[ℝ] (X →L[ℝ] E)) inferInstance
  letI : NormedAddCommGroup (∀ i, C(Kc i, E)) := Pi.normedAddCommGroup
  letI : NormedAddCommGroup (∀ i, C(Kc i, X →L[ℝ] E)) := Pi.normedAddCommGroup
  letI : NormedAddCommGroup
      (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) := Pi.normedAddCommGroup
  letI : CompleteSpace (X →L[ℝ] E) := inferInstance
  letI : CompleteSpace (X →L[ℝ] (X →L[ℝ] E)) := inferInstance
  letI : CompleteSpace (∀ i, C(Kc i, E)) :=
    parabolicC0AlphaSubmodule.finiteCoverValueReadoutTarget_completeSpace
      (X := X) (E := E) Kc
  letI : CompleteSpace (∀ i, C(Kc i, X →L[ℝ] E)) :=
    finiteCoverChosenSpaceDerivReadoutTarget_completeSpace
      (X := X) (E := E) Kc
  letI : CompleteSpace (∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E))) :=
    finiteCoverChosenSpaceSecondDerivReadoutTarget_completeSpace
      (X := X) (E := E) Kc
  infer_instance

noncomputable local instance chosenSecondJetFiniteCoverReadoutTargetCompleteSpace
    {κ : Type*} [Fintype κ] [CompleteSpace E]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X)) :
    CompleteSpace (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc) :=
  chosenSecondJetFiniteCoverReadoutTarget_completeSpace (X := X) (E := E) Kc

/-- Combined finite-cover readout of a higher parabolic function and its chosen second-jet
components as a linear map, under unique-differentiability of the slices. -/
noncomputable def chosenSecondJetFiniteCoverReadoutLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ]
      chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc where
  toFun u :=
    ((toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u,
        chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u),
      (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u,
        chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u))
  map_add' := by
    intro u v
    apply Prod.ext
    · apply Prod.ext
      · exact (toCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα).map_add u v
      · exact (chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace).map_add u v
    · apply Prod.ext
      · exact (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace).map_add u v
      · exact (chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime).map_add u v
  map_smul' := by
    intro c u
    apply Prod.ext
    · apply Prod.ext
      · exact (toCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα).map_smul c u
      · exact (chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace).map_smul c u
    · apply Prod.ext
      · exact (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace).map_smul c u
      · exact (chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime).map_smul c u

@[simp]
theorem chosenSecondJetFiniteCoverReadoutLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u =
      ((toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
            Kc hKc hα u,
          chosenSpaceDerivToCompactCoordFamilyLinearMap
            (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u),
        (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
            (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u,
          chosenTimeDerivToCompactCoordFamilyLinearMap
            (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u)) :=
  rfl

/-- The combined finite-cover chosen second-jet readout induces a seminormed additive-group
structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenSecondJetSeminormedAddCommGroup
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
  SeminormedAddCommGroup.induced
    (parabolicC2AlphaSubmodule X E α s)
    (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc)
    (chosenSecondJetFiniteCoverReadoutLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace)

/-- The combined finite-cover chosen second-jet readout induces a seminormed real vector-space
structure on the higher parabolic submodule. -/
@[reducible] noncomputable def finiteCoverChosenSecondJetNormedSpace
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    @NormedSpace ℝ (parabolicC2AlphaSubmodule X E α s) _
      (finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace) :=
  NormedSpace.induced ℝ
    (parabolicC2AlphaSubmodule X E α s)
    (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc)
    (chosenSecondJetFiniteCoverReadoutLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace)

/-- Equality of the combined finite-cover chosen second-jet readouts identifies the underlying
higher parabolic functions on any subset covered by the compact pieces. -/
theorem eqOn_subset_of_chosenSecondJetFiniteCoverReadout_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    {htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1}
    {hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2}
    {t : Set (ℝ × X)} (hcover : t ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC2AlphaSubmodule X E α s}
    (h :
      chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u =
        chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v) :
    EqOn u v t := by
  refine eqOn_subset_of_toCompactCoordFamily_eq
    (X := X) (E := E) (α := α) (s := s)
    (Kc := Kc) (hKc := hKc) (hα := hα) hcover ?_
  have hvalue := congrArg (fun w =>
    ((w : chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc).1.1)) h
  simpa [chosenSecondJetFiniteCoverReadoutLinearMap_apply] using hvalue

/-- Equality of the combined finite-cover chosen second-jet readouts identifies the underlying
higher parabolic functions on the covered domain. -/
theorem eqOn_of_chosenSecondJetFiniteCoverReadout_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    {htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1}
    {hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2}
    (hcover : s ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC2AlphaSubmodule X E α s}
    (h :
      chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u =
        chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v) :
    EqOn u v s :=
  eqOn_subset_of_chosenSecondJetFiniteCoverReadout_eq
    (X := X) (E := E) (α := α) (s := s) hcover h

/-- If the compact pieces cover all time-space, the combined finite-cover chosen second-jet
readout is injective.  The value component already separates functions on such a cover. -/
theorem chosenSecondJetFiniteCoverReadout_injective_of_iUnion_eq_univ
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    Function.Injective
      (chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace) := by
  intro u v huv
  ext z
  exact eqOn_subset_of_chosenSecondJetFiniteCoverReadout_eq
    (X := X) (E := E) (α := α) (s := s)
    (t := Set.univ) (by simp [hcover]) huv (Set.mem_univ z)

/-- If the compact pieces cover all time-space, the combined finite-cover chosen second-jet
readout induces a separated normed additive-group structure. -/
@[reducible] noncomputable def finiteCoverChosenSecondJetNormedAddCommGroupOfCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
  NormedAddCommGroup.induced
    (parabolicC2AlphaSubmodule X E α s)
    (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc)
    (chosenSecondJetFiniteCoverReadoutLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace)
    (chosenSecondJetFiniteCoverReadout_injective_of_iUnion_eq_univ
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover)

/-- The real vector-space structure paired with
`finiteCoverChosenSecondJetNormedAddCommGroupOfCover`. -/
@[reducible] noncomputable def finiteCoverChosenSecondJetNormedSpaceOfCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    @NormedSpace ℝ (parabolicC2AlphaSubmodule X E α s) _
      (finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover).toSeminormedAddCommGroup :=
  NormedSpace.induced ℝ
    (parabolicC2AlphaSubmodule X E α s)
    (chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc)
    (chosenSecondJetFiniteCoverReadoutLinearMap
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace)

/-- With the separated all-cover combined finite-cover chosen second-jet normed structure, the
norm is definitionally the combined compact-family readout norm. -/
theorem finiteCoverChosenSecondJet_norm_eq_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    ‖u‖ =
      ‖chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u‖ :=
  rfl

/-- With the separated all-cover combined finite-cover chosen second-jet normed structure,
distance is definitionally the combined compact-family readout distance. -/
theorem finiteCoverChosenSecondJet_dist_eq_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist u v =
      dist
        (chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u)
        (chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v) :=
  rfl

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the value
compact-family norm is bounded by the chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_value_norm_le_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u‖ ≤ ‖u‖ := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_norm_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).1.1‖ ≤ ‖R u‖
  exact (norm_fst_le (R u).1).trans (norm_fst_le (R u))

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the chosen
spatial-derivative compact-family norm is bounded by the chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_norm_le_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    ‖chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u‖ ≤ ‖u‖ := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_norm_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).1.2‖ ≤ ‖R u‖
  exact (norm_snd_le (R u).1).trans (norm_fst_le (R u))

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the chosen
second-spatial-derivative compact-family norm is bounded by the chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_norm_le_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    ‖chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u‖ ≤ ‖u‖ := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_norm_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).2.1‖ ≤ ‖R u‖
  exact (norm_fst_le (R u).2).trans (norm_snd_le (R u))

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the chosen
time-derivative compact-family norm is bounded by the chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_timeDeriv_norm_le_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    ‖chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u‖ ≤ ‖u‖ := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_norm_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).2.2‖ ≤ ‖R u‖
  exact (norm_snd_le (R u).2).trans (norm_snd_le (R u))

/-- For the separated all-cover norm, the combined finite-cover chosen second-jet readout is an
isometry. -/
theorem finiteCoverChosenSecondJet_readout_isometry_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    Isometry
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u) := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  exact Isometry.of_dist_eq fun u v =>
    (finiteCoverChosenSecondJet_dist_eq_ofCover
      (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα htime hspace hcover u v).symm

/-- For the separated all-cover norm, the combined finite-cover chosen second-jet readout is
nonexpansive. -/
theorem finiteCoverChosenSecondJet_readout_dist_le_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist
      (chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u)
      (chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v) ≤
      dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the value
compact-family distance is bounded by the chosen second-jet distance. -/
theorem finiteCoverChosenSecondJet_value_dist_le_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u)
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).1.1 (R v).1.1 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the chosen
spatial-derivative compact-family distance is bounded by the chosen second-jet distance. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_dist_le_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist
      (chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      (chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).1.2 (R v).1.2 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_left _ _)

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the chosen
second-spatial-derivative compact-family distance is bounded by the chosen second-jet
distance. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_dist_le_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist
      (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).2.1 (R v).2.1 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- For the separated all-cover combined finite-cover chosen second-jet norm, the chosen
time-derivative compact-family distance is bounded by the chosen second-jet distance. -/
theorem finiteCoverChosenSecondJet_timeDeriv_dist_le_ofCover {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist
      (chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u)
      (chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime v) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).2.2 (R v).2.2 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- For the separated all-cover norm, the combined finite-cover chosen second-jet readout is
`1`-Lipschitz on any state set. -/
theorem finiteCoverChosenSecondJet_readout_lipschitzOnWith_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u)
      stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s)
    (β := chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc)
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u) ?_
  intro u _hu v _hv
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  simp

/-- For the separated all-cover norm, the value compact-family readout is `1`-Lipschitz on any
state set. -/
theorem finiteCoverChosenSecondJet_value_lipschitzOnWith_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        toCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα u)
      stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      toCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u) ?_
  intro u _hu v _hv
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).1.1 (R v).1.1 ≤ (1 : ℝ) * dist (R u) (R v)
  rw [one_mul, Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- For the separated all-cover norm, the chosen spatial-derivative compact-family readout is
`1`-Lipschitz on any state set. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_lipschitzOnWith_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, X →L[ℝ] E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u) ?_
  intro u _hu v _hv
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).1.2 (R v).1.2 ≤ (1 : ℝ) * dist (R u) (R v)
  rw [one_mul, Prod.dist_eq, Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_left _ _)

/-- For the separated all-cover norm, the chosen second-spatial-derivative compact-family readout
is `1`-Lipschitz on any state set. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_lipschitzOnWith_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s)
    (β := ∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E)))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u) ?_
  intro u _hu v _hv
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).2.1 (R v).2.1 ≤ (1 : ℝ) * dist (R u) (R v)
  rw [one_mul, Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- For the separated all-cover norm, the chosen time-derivative compact-family readout is
`1`-Lipschitz on any state set. -/
theorem finiteCoverChosenSecondJet_timeDeriv_lipschitzOnWith_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u)
      stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u) ?_
  intro u _hu v _hv
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).2.2 (R v).2.2 ≤ (1 : ℝ) * dist (R u) (R v)
  rw [one_mul, Prod.dist_eq, Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- With the combined finite-cover chosen second-jet seminormed structure, the norm is
definitionally the combined compact-family readout norm. -/
theorem finiteCoverChosenSecondJet_norm_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    ‖u‖ =
      ‖chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u‖ :=
  rfl

/-- With the combined finite-cover chosen second-jet seminormed structure, distance is
definitionally the combined compact-family readout distance. -/
theorem finiteCoverChosenSecondJet_dist_eq {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    dist u v =
      dist
        (chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u)
        (chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v) :=
  rfl

/-- A higher norm-ball difference controls the combined finite-cover chosen second-jet readout
in the product sup norm, after the slice derivatives are unique. -/
theorem norm_chosenSecondJetFiniteCoverReadoutLinearMap_sub_le_of_normLe_unique
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ‖chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u -
      chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v‖ ≤ N := by
  have hparts := chosenSecondJet_sub_c0AlphaNormLe_self_of_unique
    (X := X) (E := E) (α := α) (s := s) h htime hspace
  have hvalue :
      ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα u -
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα v‖ ≤ N :=
    norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h
  have hD :
      ‖chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u -
        chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v‖ ≤ N := by
    have hread :=
      parabolicC0AlphaSubmodule.norm_toCompactCoordFamily_family_sub_le_of_normLe
        (X := X) (E := X →L[ℝ] E) (α := α) (s := s) Kc hKc hα
        (u := chosenSpaceDerivC0AlphaSubmodule
          (X := X) (E := E) (α := α) (s := s) u)
        (v := chosenSpaceDerivC0AlphaSubmodule
          (X := X) (E := E) (α := α) (s := s) v)
        hparts.2.1
    simpa [chosenSpaceDerivToCompactCoordFamilyLinearMap_apply,
      chosenSpaceDerivToCompactCoordFamily] using hread
  have hH :
      ‖chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u -
        chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v‖ ≤ N := by
    have hread :=
      parabolicC0AlphaSubmodule.norm_toCompactCoordFamily_family_sub_le_of_normLe
        (X := X) (E := X →L[ℝ] (X →L[ℝ] E)) (α := α) (s := s) Kc hKc hα
        (u := chosenSpaceSecondDerivC0AlphaSubmodule
          (X := X) (E := E) (α := α) (s := s) u)
        (v := chosenSpaceSecondDerivC0AlphaSubmodule
          (X := X) (E := E) (α := α) (s := s) v)
        hparts.2.2.1
    simpa [chosenSpaceSecondDerivToCompactCoordFamilyLinearMap_apply,
      chosenSpaceSecondDerivToCompactCoordFamily] using hread
  have ht :
      ‖chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u -
        chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime v‖ ≤ N := by
    have hread :=
      parabolicC0AlphaSubmodule.norm_toCompactCoordFamily_family_sub_le_of_normLe
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα
        (u := chosenTimeDerivC0AlphaSubmodule
          (X := X) (E := E) (α := α) (s := s) u)
        (v := chosenTimeDerivC0AlphaSubmodule
          (X := X) (E := E) (α := α) (s := s) v)
        hparts.2.2.2
    simpa [chosenTimeDerivToCompactCoordFamilyLinearMap_apply,
      chosenTimeDerivToCompactCoordFamily] using hread
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖R u - R v‖ ≤ N
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [Prod.norm_def]
    refine max_le ?_ ?_
    · simpa [R, chosenSecondJetFiniteCoverReadoutLinearMap_apply] using hvalue
    · simpa [R, chosenSecondJetFiniteCoverReadoutLinearMap_apply] using hD
  · rw [Prod.norm_def]
    refine max_le ?_ ?_
    · simpa [R, chosenSecondJetFiniteCoverReadoutLinearMap_apply] using hH
    · simpa [R, chosenSecondJetFiniteCoverReadoutLinearMap_apply] using ht

/-- A higher norm-ball difference controls the combined finite-cover chosen second-jet readout
distance, after the slice derivatives are unique. -/
theorem dist_chosenSecondJetFiniteCoverReadoutLinearMap_le_of_normLe_unique
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    dist
        (chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u)
        (chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v) ≤ N := by
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u) (R v) ≤ N
  have hnorm : ‖R u - R v‖ ≤ N := by
    simpa [R] using
      norm_chosenSecondJetFiniteCoverReadoutLinearMap_sub_le_of_normLe_unique
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα h htime hspace
  calc
    dist (R u) (R v) = ‖-(R u) + R v‖ := SeminormedAddCommGroup.dist_eq (R u) (R v)
    _ = ‖R u - R v‖ := by
      rw [← norm_neg (R u - R v)]
      congr 1
      abel
    _ ≤ N := hnorm

/-- A higher norm-ball difference controls the induced combined finite-cover chosen second-jet
seminorm. -/
theorem finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    dist u v ≤ N := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_dist_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v]
  exact dist_chosenSecondJetFiniteCoverReadoutLinearMap_le_of_normLe_unique
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h htime hspace

/-- A higher norm-ball difference controls the separated all-cover combined finite-cover chosen
second-jet normed distance. -/
theorem finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist u v ≤ N := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  rw [finiteCoverChosenSecondJet_dist_eq_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover u v]
  exact dist_chosenSecondJetFiniteCoverReadoutLinearMap_le_of_normLe_unique
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h htime hspace

/-- A higher norm-ball difference gives closed-ball membership for the induced combined
finite-cover chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_of_normLe_sub_unique
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    u ∈ Metric.closedBall v N := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  simpa [Metric.mem_closedBall] using
    finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h htime hspace

/-- Symmetric closed-ball membership for the induced combined finite-cover chosen second-jet
seminorm from a higher norm-ball difference. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_symm_of_normLe_sub_unique
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    v ∈ Metric.closedBall u N := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα h htime hspace

/-- A higher norm-ball difference gives closed-ball membership for the separated all-cover
combined finite-cover chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_of_normLe_sub_unique_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    u ∈ Metric.closedBall v N := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  simpa [Metric.mem_closedBall] using
    finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique_ofCover
      (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα htime hspace hcover h

/-- Symmetric closed-ball membership for the separated all-cover combined finite-cover chosen
second-jet norm from a higher norm-ball difference. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_symm_of_normLe_sub_unique_ofCover
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    v ∈ Metric.closedBall u N := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique_ofCover
      (X := X) (E := E) (α := α) (s := s)
      Kc hKc hα htime hspace hcover h

/-- Componentwise finite-Pi higher difference controls assemble into a combined finite-cover
chosen second-jet distance bound. The radius records the coordinate-insertion constants needed
to turn the component bounds into one Pi-valued higher norm ball. -/
theorem finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique
    {κ ι F : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
    dist u v ≤
      (∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R := by
  classical
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
  have hpi :
      ParabolicC2AlphaNormLe
        ((∑ i,
          ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
            (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R) α
        (fun z : ℝ × X => u z - v z) s :=
    ParabolicC2AlphaNormLe.pi_sub_pi_mul_radius
      (X := X) (α := α) (s := s) (K := K) (R := R)
      (u := fun z : ℝ × X => u z) (v := fun z : ℝ × X => v z) h
  simpa using
    finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα hpi htime hspace

/-- Componentwise finite-Pi higher difference controls give closed-ball membership for the
combined finite-cover chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_pi_of_component_normLe_sub_unique
    {κ ι F : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
    u ∈ Metric.closedBall v
      ((∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R) := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
  simpa [Metric.mem_closedBall] using
    finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique
      (X := X) (α := α) (s := s) Kc hKc hα h htime hspace

/-- Symmetric closed-ball membership for the combined finite-cover chosen second-jet seminorm
from componentwise finite-Pi higher difference controls. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_symm_pi_of_component_normLe_sub_unique
    {κ ι F : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
    v ∈ Metric.closedBall u
      ((∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R) := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique
      (X := X) (α := α) (s := s) Kc hKc hα h htime hspace

/-- Componentwise finite-Pi higher difference controls assemble into a separated all-cover
combined finite-cover chosen second-jet distance bound. -/
theorem finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    dist u v ≤
      (∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R := by
  classical
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace hcover
  have hpi :
      ParabolicC2AlphaNormLe
        ((∑ i,
          ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
            (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R) α
        (fun z : ℝ × X => u z - v z) s :=
    ParabolicC2AlphaNormLe.pi_sub_pi_mul_radius
      (X := X) (α := α) (s := s) (K := K) (R := R)
      (u := fun z : ℝ × X => u z) (v := fun z : ℝ × X => v z) h
  simpa using
    finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique_ofCover
      (X := X) (E := ι → F) (α := α) (s := s)
      Kc hKc hα htime hspace hcover hpi

/-- Componentwise finite-Pi higher difference controls give closed-ball membership for the
separated all-cover combined finite-cover chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_pi_of_component_normLe_sub_unique_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    u ∈ Metric.closedBall v
      ((∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R) := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace hcover
  simpa [Metric.mem_closedBall] using
    finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα htime hspace hcover h

/-- Symmetric closed-ball membership for the separated all-cover combined finite-cover chosen
second-jet norm from componentwise finite-Pi higher difference controls. -/
theorem finiteCoverChosenSecondJet_mem_closedBall_symm_pi_of_component_normLe_sub_unique_ofCover
    {κ ι F : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {R : ℝ} {K : ι → ℝ}
    {u v : parabolicC2AlphaSubmodule X (ι → F) α s}
    (h : ∀ i, ParabolicC2AlphaNormLe (K i * R) α
      (fun z => u z i - v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    v ∈ Metric.closedBall u
      ((∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * R) := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace hcover
  simpa [Metric.mem_closedBall, dist_comm] using
    finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα htime hspace hcover h

/-- Pairwise finite-coordinate higher difference controls give a Lipschitz estimate in the
combined finite-cover chosen second-jet seminorm, once an aggregate Lipschitz constant bounds
the coordinate-insertion radius sum. -/
theorem lipschitzOnWith_finiteCoverChosenSecondJet_pi_of_component_normLe_sub_unique
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {K : ι → ℝ}
    {A : Y → parabolicC2AlphaSubmodule X (ι → F) α s}
    (hL :
      (∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) ≤ (L : ℝ))
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC2AlphaNormLe (K i * dist u v) α
        (fun z => A u z i - A v z i) s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
    LipschitzOnWith L A stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hdist :
      dist (A u) (A v) ≤
        (∑ i,
          ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
            (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * dist u v :=
    finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique
      (X := X) (α := α) (s := s) Kc hKc hα
      (R := dist u v) (K := K) (u := A u) (v := A v)
      (h hu hv) htime hspace
  exact hdist.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)

/-- Pairwise finite-coordinate higher difference controls give a Lipschitz estimate in the
separated all-cover combined finite-cover chosen second-jet norm, once an aggregate Lipschitz
constant bounds the coordinate-insertion radius sum. -/
theorem lipschitzOnWith_finiteCoverChosenSecondJet_pi_of_component_normLe_sub_unique_ofCover
    {Y κ ι F : Type*} [PseudoMetricSpace Y] [Fintype κ] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    {stateSet : Set Y} {L : ℝ≥0} {K : ι → ℝ}
    {A : Y → parabolicC2AlphaSubmodule X (ι → F) α s}
    (hL :
      (∑ i,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
          (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) ≤ (L : ℝ))
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i,
      ParabolicC2AlphaNormLe (K i * dist u v) α
        (fun z => A u z i - A v z i) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := ι → F) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    LipschitzOnWith L A stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X (ι → F) α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := ι → F) (α := α) (s := s) Kc hKc hα htime hspace hcover
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hdist :
      dist (A u) (A v) ≤
        (∑ i,
          ParabolicC2AlphaNormLe.continuousLinearMapRadius (X := X) (E := F)
            (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) * K i) * dist u v :=
    finiteCoverChosenSecondJet_dist_le_pi_of_component_normLe_sub_unique_ofCover
      (X := X) (α := α) (s := s) Kc hKc hα htime hspace hcover
      (R := dist u v) (K := K) (u := A u) (v := A v) (h hu hv)
  exact hdist.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)

/-- Pairwise higher difference estimates give a Lipschitz estimate in the induced combined
finite-cover chosen second-jet seminorm. -/
theorem lipschitzOnWith_finiteCoverChosenSecondJet_of_normLe_sub_unique
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α
        (fun z => A u z - A v z) s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    LipschitzOnWith L A stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  refine LipschitzOnWith.of_dist_le_mul
    (α := Y) (β := parabolicC2AlphaSubmodule X E α s)
    (K := L) (s := stateSet) (f := A) ?_
  intro u hu v hv
  exact finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv) htime hspace

/-- Pairwise higher difference estimates give a Lipschitz estimate in the separated all-cover
combined finite-cover chosen second-jet normed structure. -/
theorem lipschitzOnWith_finiteCoverChosenSecondJet_of_normLe_sub_unique_ofCover
    {Y κ : Type*} [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0}
    {A : Y → parabolicC2AlphaSubmodule X E α s}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ)
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α
        (fun z => A u z - A v z) s) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα htime hspace hcover
    LipschitzOnWith L A stateSet := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover
  refine LipschitzOnWith.of_dist_le_mul
    (α := Y) (β := parabolicC2AlphaSubmodule X E α s)
    (K := L) (s := stateSet) (f := A) ?_
  intro u hu v hv
  exact finiteCoverChosenSecondJet_dist_le_of_normLe_sub_unique_ofCover
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace hcover (h hu hv)

/-- The value compact-family norm is bounded by the combined finite-cover chosen second-jet
seminorm. -/
theorem finiteCoverChosenSecondJet_value_norm_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u‖ ≤ ‖u‖ := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_norm_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).1.1‖ ≤ ‖R u‖
  exact (norm_fst_le (R u).1).trans (norm_fst_le (R u))

/-- The chosen spatial-derivative compact-family norm is bounded by the combined finite-cover
chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_norm_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    ‖chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u‖ ≤ ‖u‖ := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_norm_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).1.2‖ ≤ ‖R u‖
  exact (norm_snd_le (R u).1).trans (norm_fst_le (R u))

/-- The chosen second-spatial-derivative compact-family norm is bounded by the combined
finite-cover chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_norm_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    ‖chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u‖ ≤ ‖u‖ := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_norm_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).2.1‖ ≤ ‖R u‖
  exact (norm_fst_le (R u).2).trans (norm_snd_le (R u))

/-- The chosen time-derivative compact-family norm is bounded by the combined finite-cover chosen
second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_timeDeriv_norm_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    ‖chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u‖ ≤ ‖u‖ := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_norm_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change ‖(R u).2.2‖ ≤ ‖R u‖
  exact (norm_snd_le (R u).2).trans (norm_snd_le (R u))

/-- The value compact-family distance is bounded by the combined finite-cover chosen second-jet
distance. -/
theorem finiteCoverChosenSecondJet_value_dist_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    dist
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u)
      (toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_dist_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).1.1 (R v).1.1 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- The chosen spatial-derivative compact-family distance is bounded by the combined finite-cover
chosen second-jet distance. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_dist_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    dist
      (chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      (chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_dist_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).1.2 (R v).1.2 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_left _ _)

/-- The chosen second-spatial-derivative compact-family distance is bounded by the combined
finite-cover chosen second-jet distance. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_dist_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    dist
      (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      (chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace v) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_dist_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).2.1 (R v).2.1 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- The chosen time-derivative compact-family distance is bounded by the combined finite-cover
chosen second-jet distance. -/
theorem finiteCoverChosenSecondJet_timeDeriv_dist_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    dist
      (chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u)
      (chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime v) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_dist_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v]
  let R := chosenSecondJetFiniteCoverReadoutLinearMap
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  change dist (R u).2.2 (R v).2.2 ≤ dist (R u) (R v)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- The combined finite-cover chosen second-jet readout is an isometry for its induced seminormed
structure. -/
theorem finiteCoverChosenSecondJet_readout_isometry {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    Isometry
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u) := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  exact Isometry.of_dist_eq fun u v =>
    (finiteCoverChosenSecondJet_dist_eq
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v).symm

/-- The combined finite-cover chosen second-jet readout is nonexpansive for its induced
seminormed structure. -/
theorem finiteCoverChosenSecondJet_readout_dist_le {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (u v : parabolicC2AlphaSubmodule X E α s) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    dist
      (chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u)
      (chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace v) ≤
      dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  rw [finiteCoverChosenSecondJet_dist_eq
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v]

/-- The combined finite-cover chosen second-jet readout is `1`-Lipschitz on any state set for its
induced seminormed structure. -/
theorem finiteCoverChosenSecondJet_readout_lipschitzOnWith {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSecondJetFiniteCoverReadoutLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u)
      stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s)
    (β := chosenSecondJetFiniteCoverReadoutTarget (X := X) (E := E) Kc)
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenSecondJetFiniteCoverReadoutLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u) ?_
  intro u _hu v _hv
  simpa [one_mul] using
    finiteCoverChosenSecondJet_readout_dist_le
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v

/-- The value compact-family readout is `1`-Lipschitz for the combined finite-cover chosen
second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_value_lipschitzOnWith {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        toCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα u)
      stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      toCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα u) ?_
  intro u _hu v _hv
  simpa [one_mul] using
    finiteCoverChosenSecondJet_value_dist_le
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v

/-- The chosen spatial-derivative compact-family readout is `1`-Lipschitz for the combined
finite-cover chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_lipschitzOnWith {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSpaceDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, X →L[ℝ] E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenSpaceDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u) ?_
  intro u _hu v _hv
  simpa [one_mul] using
    finiteCoverChosenSecondJet_spaceDeriv_dist_le
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v

/-- The chosen second-spatial-derivative compact-family readout is `1`-Lipschitz for the combined
finite-cover chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_lipschitzOnWith
    {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u)
      stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s)
    (β := ∀ i, C(Kc i, X →L[ℝ] (X →L[ℝ] E)))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenSpaceSecondDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα hspace u) ?_
  intro u _hu v _hv
  simpa [one_mul] using
    finiteCoverChosenSecondJet_spaceSecondDeriv_dist_le
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v

/-- The chosen time-derivative compact-family readout is `1`-Lipschitz for the combined
finite-cover chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_timeDeriv_lipschitzOnWith {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
    LipschitzOnWith 1
      (fun u : parabolicC2AlphaSubmodule X E α s =>
        chosenTimeDerivToCompactCoordFamilyLinearMap
          (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u)
      stateSet := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace
  refine LipschitzOnWith.of_dist_le_mul
    (α := parabolicC2AlphaSubmodule X E α s) (β := ∀ i, C(Kc i, E))
    (K := (1 : ℝ≥0)) (s := stateSet)
    (f := fun u : parabolicC2AlphaSubmodule X E α s =>
      chosenTimeDerivToCompactCoordFamilyLinearMap
        (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime u) ?_
  intro u _hu v _hv
  simpa [one_mul] using
    finiteCoverChosenSecondJet_timeDeriv_dist_le
      (X := X) (E := E) (α := α) (s := s) Kc hKc hα htime hspace u v

/-- Fixed-time spatial value readout estimate for the combined finite-cover chosen second-jet
seminorm, after the time-space compact pieces cover the requested spatial slices. -/
theorem finiteCoverChosenSecondJet_value_timeSlice_spatial_dist_le
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i), dist (u (τ, x.1)) (v (τ, x.1)) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          toCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_value_lipschitzOnWith
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace stateSet
  have h := forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcover
  simpa [one_mul] using h

/-- Fixed-time spatial chosen-spatial-derivative readout estimate for the combined finite-cover
chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_timeSlice_spatial_dist_le
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i),
          dist
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv
              (τ, x.1))
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) v).spaceDeriv
              (τ, x.1)) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          chosenSpaceDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_spaceDeriv_lipschitzOnWith
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace stateSet
  have h := forall_timeSlice_spatial_dist_le_of_chosenSpaceDerivToCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcover
  simpa [one_mul] using h

/-- Fixed-time spatial chosen-second-spatial-derivative readout estimate for the combined
finite-cover chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_timeSlice_spatial_dist_le
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i),
          dist
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
              u).spaceSecondDeriv (τ, x.1))
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
              v).spaceSecondDeriv (τ, x.1)) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          chosenSpaceSecondDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_spaceSecondDeriv_lipschitzOnWith
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace stateSet
  have h :=
    forall_timeSlice_spatial_dist_le_of_chosenSpaceSecondDerivToCompactCoordFamily_lipschitzOnWith
      (X := X) (E := E) (α := α) (s := s)
      Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
      (A := fun _τ u => u) hLip hcover
  simpa [one_mul] using h

/-- Fixed-time spatial chosen-time-derivative readout estimate for the combined finite-cover
chosen second-jet seminorm. -/
theorem finiteCoverChosenSecondJet_timeDeriv_timeSlice_spatial_dist_le
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s))
    (hcover : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X))) :
    letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetSeminormedAddCommGroup
        (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i),
          dist
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv
              (τ, x.1))
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) v).timeDeriv
              (τ, x.1)) ≤ dist u v := by
  letI : SeminormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetSeminormedAddCommGroup
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          chosenTimeDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_timeDeriv_lipschitzOnWith
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace stateSet
  have h := forall_timeSlice_spatial_dist_le_of_chosenTimeDerivToCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcover
  simpa [one_mul] using h

/-- Fixed-time spatial value readout estimate for the separated all-cover combined finite-cover
chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_value_timeSlice_spatial_dist_le_ofCover
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i), dist (u (τ, x.1)) (v (τ, x.1)) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace hcover
  have hcoverSlices : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X)) :=
    parabolicC0AlphaSubmodule.timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          toCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_value_lipschitzOnWith_ofCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover stateSet
  have h := forall_timeSlice_spatial_dist_le_of_toCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcoverSlices
  simpa [one_mul] using h

/-- Fixed-time spatial chosen-spatial-derivative estimate for the separated all-cover combined
finite-cover chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_spaceDeriv_timeSlice_spatial_dist_le_ofCover
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i),
          dist
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).spaceDeriv
              (τ, x.1))
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) v).spaceDeriv
              (τ, x.1)) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace hcover
  have hcoverSlices : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X)) :=
    parabolicC0AlphaSubmodule.timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          chosenSpaceDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_spaceDeriv_lipschitzOnWith_ofCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover stateSet
  have h := forall_timeSlice_spatial_dist_le_of_chosenSpaceDerivToCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcoverSlices
  simpa [one_mul] using h

/-- Fixed-time spatial chosen-second-spatial-derivative estimate for the separated all-cover
combined finite-cover chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_spaceSecondDeriv_timeSlice_spatial_dist_le_ofCover
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i),
          dist
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
              u).spaceSecondDeriv (τ, x.1))
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s)
              v).spaceSecondDeriv (τ, x.1)) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace hcover
  have hcoverSlices : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X)) :=
    parabolicC0AlphaSubmodule.timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          chosenSpaceSecondDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_spaceSecondDeriv_lipschitzOnWith_ofCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover stateSet
  have h :=
    forall_timeSlice_spatial_dist_le_of_chosenSpaceSecondDerivToCompactCoordFamily_lipschitzOnWith
      (X := X) (E := E) (α := α) (s := s)
      Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
      (A := fun _τ u => u) hLip hcoverSlices
  simpa [one_mul] using h

/-- Fixed-time spatial chosen-time-derivative estimate for the separated all-cover combined
finite-cover chosen second-jet norm. -/
theorem finiteCoverChosenSecondJet_timeDeriv_timeSlice_spatial_dist_le_ofCover
    {η κ : Type*} [Fintype κ]
    (Kdom : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ j, (Kdom j : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (Kx : η → TopologicalSpace.Compacts X)
    {timeSet : Set ℝ}
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2)
    (hcover : (⋃ j, (Kdom j : Set (ℝ × X))) = Set.univ)
    (stateSet : Set (parabolicC2AlphaSubmodule X E α s)) :
    letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
      finiteCoverChosenSecondJetNormedAddCommGroupOfCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover
    ∀ τ, τ ∈ timeSet → ∀ ⦃u : parabolicC2AlphaSubmodule X E α s⦄,
      u ∈ stateSet → ∀ ⦃v : parabolicC2AlphaSubmodule X E α s⦄, v ∈ stateSet →
        ∀ i (x : Kx i),
          dist
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) u).timeDeriv
              (τ, x.1))
            ((chosenSecondJet (X := X) (E := E) (α := α) (s := s) v).timeDeriv
              (τ, x.1)) ≤ dist u v := by
  letI : NormedAddCommGroup (parabolicC2AlphaSubmodule X E α s) :=
    finiteCoverChosenSecondJetNormedAddCommGroupOfCover
      (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα htime hspace hcover
  have hcoverSlices : ∀ τ, τ ∈ timeSet → ∀ i (x : Kx i),
      ∃ j, (τ, x.1) ∈ (Kdom j : Set (ℝ × X)) :=
    parabolicC0AlphaSubmodule.timeSlice_spatial_cover_of_iUnion_eq_univ
      (X := X) Kdom Kx (timeSet := timeSet) hcover
  have hLip : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith (1 : ℝ≥0)
        (fun u : parabolicC2AlphaSubmodule X E α s =>
          chosenTimeDerivToCompactCoordFamily
            (X := X) (E := E) (α := α) (s := s) Kdom hKdom hα u)
        stateSet := by
    intro _τ _hτ
    simpa using
      finiteCoverChosenSecondJet_timeDeriv_lipschitzOnWith_ofCover
        (X := X) (E := E) (α := α) (s := s)
        Kdom hKdom hα htime hspace hcover stateSet
  have h := forall_timeSlice_spatial_dist_le_of_chosenTimeDerivToCompactCoordFamily_lipschitzOnWith
    (X := X) (E := E) (α := α) (s := s)
    Kdom hKdom hα Kx (timeSet := timeSet) (stateSet := stateSet)
    (A := fun _τ u => u) hLip hcoverSlices
  simpa [one_mul] using h

/-- Restriction to a smaller set as a linear map between coordinate parabolic
`C^{2+α,1+α/2}` spaces. -/
def restrictLinearMap {t : Set (ℝ × X)} (hst : t ⊆ s) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] parabolicC2AlphaSubmodule X E α t where
  toFun u := ⟨u.1, u.2.mono_set hst⟩
  map_add' := by
    intro u v
    ext z
    rfl
  map_smul' := by
    intro c u
    ext z
    rfl

@[simp]
theorem restrictLinearMap_apply {t : Set (ℝ × X)} (hst : t ⊆ s)
    (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    restrictLinearMap (X := X) (E := E) (α := α) hst u z = u z :=
  rfl

end parabolicC2AlphaSubmodule

end AnalyticPDE
end RicciFlow
