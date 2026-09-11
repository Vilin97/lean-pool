/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolev
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2ScalingContinuity
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketParity
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionData
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionParity
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.FlowL2Transport
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalContinuity
public import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketVolumeDivergence
public import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowGevrey
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedGradientSpace
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import LeanPool.NavierStokesAndEuler.Euler.LpDominatedConvergence

/-! The recursive physical state consists of the actual Euler solution,
its all-order Sobolev fields, its particle-label bounds, and its symmetry.
Restriction and the exact packet construction preserve these data. -/

section

/-! Spatial Sobolev paths for the actual inverse parent flow. Its
measure preservation, smoothness, derivative bounds and jet continuity
are all derived from the source deformation and inverse identities. -/

section

/-! Strong Sobolev continuity under genuine varying volume-preserving
maps. Faà di Bruno gives actual derivative tensors, and dominated
convergence handles the bounded, pointwise continuous coefficients. -/

section

/-! Bounded pointwise operator fields act on actual L² classes. Joint
continuity of the coefficients, with a uniform bound, gives strong
continuity even when uniform convergence of coefficients is unavailable. -/

@[expose] public section

noncomputable section

namespace EulerLpPointwiseMultiplier

open MeasureTheory Filter
open scoped Topology

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure X) (A : X → E →L[ℝ] F)
  (hA : AEStronglyMeasurable A μ) (C : ℝ) (hC : ∀ x, ‖A x‖ ≤ C)

include hA hC in
theorem apply_memLp (u : Lp E 2 μ) : MemLp (fun x => A x (u x)) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := C)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable u))
  · exact Eventually.of_forall (fun x => ((A x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (u x))))

/-- Apply Lᵖ, given by `(apply_memLp μ A hA C hC u).toLp (fun x => A x (u x))`. -/
def applyLp (u : Lp E 2 μ) : Lp F 2 μ :=
  (apply_memLp μ A hA C hC u).toLp (fun x => A x (u x))

theorem applyLp_ae (u : Lp E 2 μ) :
    (applyLp μ A hA C hC u : X → F) =ᵐ[μ] fun x => A x (u x) :=
  (apply_memLp μ A hA C hC u).coeFn_toLp

theorem applyLp_norm_le (u : Lp E 2 μ) :
    ‖applyLp μ A hA C hC u‖ ≤ C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyLp_ae μ A hA C hC u] with x hx
  rw [hx]
  exact ((A x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (u x)))

/-- Linear, bundling `toFun`, `map_add`, `map_smul`. -/
def linear : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun := applyLp μ A hA C hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [applyLp_ae μ A hA C hC (u+v), applyLp_ae μ A hA C hC u,
      applyLp_ae μ A hA C hC v, Lp.coeFn_add u v,
      Lp.coeFn_add (applyLp μ A hA C hC u) (applyLp μ A hA C hC v)]
      with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h5,h4,h2,h3,map_add]
  map_smul' r u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [applyLp_ae μ A hA C hC (r • u), applyLp_ae μ A hA C hC u,
      Lp.coeFn_smul r u,Lp.coeFn_smul r (applyLp μ A hA C hC u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    rw [h1,h4,h3,h2,map_smul]

/-- Operator, given by `(linear μ A hA C hC).mkContinuous C (applyLp_norm_le μ A hA C hC)`. -/
def operator : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (linear μ A hA C hC).mkContinuous C (applyLp_norm_le μ A hA C hC)

theorem operator_ae (u : Lp E 2 μ) :
    (operator μ A hA C hC u : X → F) =ᵐ[μ] fun x => A x (u x) :=
  applyLp_ae μ A hA C hC u

theorem operator_bound (u : Lp E 2 μ) : ‖operator μ A hA C hC u‖ ≤ C*‖u‖ :=
  applyLp_norm_le μ A hA C hC u

variable {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
  (B : K → X → E →L[ℝ] F) (hB : ∀ t, AEStronglyMeasurable (B t) μ)
  (hBt : ∀ x, Continuous (fun t => B t x)) (hBC : ∀ t x, ‖B t x‖ ≤ C)

include hBt in
theorem operator_strongly_continuous (u : Lp E 2 μ) :
    Continuous (fun t => operator μ (B t) (hB t) C (hBC t) u) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply EulerLpConvergence.tendsto_of_dominated μ
    (fun t => operator μ (B t) (hB t) C (hBC t) u)
    (operator μ (B t₀) (hB t₀) C (hBC t₀) u)
    (fun t x => B t x (u x)) (fun x => B t₀ x (u x))
    (fun t => operator_ae μ (B t) (hB t) C (hBC t) u)
    (operator_ae μ (B t₀) (hB t₀) C (hBC t₀) u)
    (fun x => (2*C)*‖u x‖) ((Lp.memLp u).norm.const_mul (2*C))
  · apply Eventually.of_forall
    intro t
    apply Eventually.of_forall
    intro x
    calc
      _ ≤ ‖B t x (u x)‖ + ‖B t₀ x (u x)‖ := norm_sub_le _ _
      _ ≤ C*‖u x‖ + C*‖u x‖ := add_le_add
        (((B t x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBC t x) (norm_nonneg _)))
        (((B t₀ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBC t₀ x) (norm_nonneg _)))
      _ = _ := by ring
  · exact Eventually.of_forall (fun x => ((hBt x).clm_apply continuous_const).tendsto t₀)

include hBt in
theorem operator_path_continuous (u : K → Lp E 2 μ) (hu : Continuous u) :
    Continuous (fun t => operator μ (B t) (hB t) C (hBC t) (u t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h₁ : Tendsto (fun t => C*‖u t-u t₀‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,mul_zero] using ((hu.tendsto t₀).sub_const (u
        t₀)).norm.const_mul C
  have h₂ : Tendsto (fun t => ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
      operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero] using
      (((operator_strongly_continuous μ C B hB hBt hBC (u t₀)).tendsto t₀).sub_const
        (operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀))).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa only [add_zero] using h₁.add h₂)
  intro t
  calc
    _ ≤ ‖operator μ (B t) (hB t) C (hBC t) (u t) -
        operator μ (B t) (hB t) C (hBC t) (u t₀)‖ +
      ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
        operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C*‖u t-u t₀‖ +
      ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
        operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖ := add_le_add (by
      rw [← map_sub]
      exact operator_bound μ (B t) (hB t) C (hBC t) (u t-u t₀)) le_rfl

end EulerLpPointwiseMultiplier

end
end

end

@[expose] public section

noncomputable section

namespace EulerVolumeSobolevPath

open MeasureTheory Filter EulerLiftedGradientSpace
  EulerLpPointwiseMultiplier
open scoped Topology ContDiff

/-- Tensor: an abbreviation for `Vector3 [×n]→L[ℝ] Vector3`. -/
abbrev Tensor (n : ℕ) := Vector3 [×n]→L[ℝ] Vector3

/-- Cache the standard `NormedAddCommGroup (Tensor n)` instance to shorten typeclass synthesis. -/
local instance instVolumeSobolevPath1 (n : ℕ) : NormedAddCommGroup (Tensor n) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Tensor n)` instance to shorten typeclass synthesis. -/
local instance instVolumeSobolevPath2 (n : ℕ) : NormedSpace ℝ (Tensor n) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Tensor a →L[ℝ] Tensor b)` instance to shorten
typeclass synthesis. -/
local instance instVolumeSobolevPath3 (a b : ℕ) : NormedAddCommGroup (Tensor a →L[ℝ] Tensor b) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Tensor a →L[ℝ] Tensor b)` instance to shorten typeclass
synthesis. -/
local instance instVolumeSobolevPath4 (a b : ℕ) : NormedSpace ℝ (Tensor a →L[ℝ] Tensor b) :=
    inferInstance
local instance instVolumeSobolevPath5 (a b : ℕ) : SecondCountableTopologyEither Vector3 (Tensor a
    →L[ℝ] Tensor b)
    :=
  ⟨Or.inl inferInstance⟩

variable {K : Type*} [TopologicalSpace K]
  (Y : C(K, C(Vector3, Vector3))) (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (u : ∀ i : ℕ, C(K, Lp (Tensor i) 2 (volume : Measure Vector3)))

/-- Pulled jet path, bundling `toFun`, `continuous_toFun`. -/
def pulledJetPath (i : ℕ) : C(K,Lp (Tensor i) 2 (volume : Measure Vector3)) where
  toFun t := Lp.compMeasurePreserving (Y t) (hmp t) (u i t)
  continuous_toFun := (u i).continuous.compMeasurePreservingLp Y.continuous hmp (by norm_num)

theorem pulledJetPath_ae (g : K → Vector3 → Vector3)
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t))
    (i : ℕ) (t : K) :
    (pulledJetPath Y hmp u i t : Vector3 → Tensor i) =ᵐ[volume]
      fun x => iteratedFDeriv ℝ i (g t) (Y t x) :=
  (Lp.coeFn_compMeasurePreserving (u i t) (hmp t)).trans
    ((hmp t).quasiMeasurePreserving.ae_eq_comp (hu i t))

variable {n : ℕ}

/-- Partition coefficient, given by `(c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3
Vector3).flipMultilinear (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x)`. -/
def partitionCoefficient (c : OrderedFinpartition n) (t : K) (x : Vector3) :
    Tensor c.length →L[ℝ] Tensor n :=
  (c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3 Vector3).flipMultilinear
    (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x)

theorem partitionCoefficient_apply (c : OrderedFinpartition n) (t : K) (x : Vector3)
    (v : Tensor c.length) :
    partitionCoefficient Y c t x v = c.compAlongOrderedFinpartition v
      (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) := rfl

/-- Partition bound, given by `∏ i : Fin c.length, D^(c.partSize i)`. -/
def partitionBound (D : ℝ) (c : OrderedFinpartition n) : ℝ :=
  ∏ i : Fin c.length, D^(c.partSize i)

variable (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : K × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D ^ i)

include hJ in
theorem partitionCoefficient_continuous (c : OrderedFinpartition n) :
    Continuous (Function.uncurry (partitionCoefficient Y c)) := by
  exact (c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3 Vector3).flipMultilinear.cont.comp
    (continuous_pi (fun i => hJ (c.partSize i) (c.partSize_pos i) (c.partSize_le i)))

include hD hB in
theorem partitionCoefficient_bound (c : OrderedFinpartition n) (t : K) (x : Vector3) :
    ‖partitionCoefficient Y c t x‖ ≤ partitionBound D c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg (fun i _ => pow_nonneg hD _))
  intro v
  rw [partitionCoefficient_apply]
  calc
    _ ≤ ‖v‖ * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) (Y t) x‖ :=
      c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ ‖v‖ * partitionBound D c := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => hB (c.partSize i) (c.partSize_pos i) (c.partSize_le i) t x)) (norm_nonneg _)
    _ = _ := mul_comm _ _

variable [FirstCountableTopology K]

/-- Partition path, bundling `toFun`, `continuous_toFun`. -/
def partitionPath (c : OrderedFinpartition n) :
    C(K,Lp (Tensor n) 2 (volume : Measure Vector3)) where
  toFun t := operator volume (partitionCoefficient Y c t)
    ((partitionCoefficient_continuous Y hJ c).uncurry_left t).aestronglyMeasurable
    (partitionBound D c) (partitionCoefficient_bound Y D hD hB c t) (pulledJetPath Y hmp u c.length
        t)
  continuous_toFun := operator_path_continuous volume (partitionBound D c) (partitionCoefficient Y
      c)
    (fun t => ((partitionCoefficient_continuous Y hJ c).uncurry_left t).aestronglyMeasurable)
    (fun _ => (partitionCoefficient_continuous Y hJ c).comp (continuous_id.prodMk continuous_const))
    (partitionCoefficient_bound Y D hD hB c) _ (pulledJetPath Y hmp u c.length).continuous

theorem partitionPath_ae (g : K → Vector3 → Vector3)
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t))
    (c : OrderedFinpartition n) (t : K) :
    (partitionPath Y hmp u D hD hJ hB c t : Vector3 → Tensor n) =ᵐ[volume]
      fun x => c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (g t) (Y t x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) := by
  have h := operator_ae volume (partitionCoefficient Y c t)
    ((partitionCoefficient_continuous Y hJ c).uncurry_left t).aestronglyMeasurable
    (partitionBound D c) (partitionCoefficient_bound Y D hD hB c t) (pulledJetPath Y hmp u c.length
        t)
  filter_upwards [h,pulledJetPath_ae Y hmp u g hu c.length t] with x hx hy
  exact hx.trans (by rw [hy,partitionCoefficient_apply])

/-- Tensor path, given by `∑ c : OrderedFinpartition n, partitionPath Y hmp u D hD hJ hB c`. -/
def tensorPath : C(K,Lp (Tensor n) 2 (volume : Measure Vector3)) :=
  ∑ c : OrderedFinpartition n, partitionPath Y hmp u D hD hJ hB c

theorem tensorPath_ae (g : K → Vector3 → Vector3)
    (hg : ∀ t, ContDiff ℝ ∞ (g t)) (hY : ∀ t, ContDiff ℝ ∞ (Y t))
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t)) (t : K) :
    (tensorPath Y hmp u D hD hJ hB t : Vector3 → Tensor n) =ᵐ[volume]
      iteratedFDeriv ℝ n (g t ∘ Y t) := by
  have hterms : ∀ᵐ x ∂volume, ∀ c : OrderedFinpartition n,
      (partitionPath Y hmp u D hD hJ hB c t) x =
      c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (g t) (Y t x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) :=
    ae_all_iff.mpr (fun c => partitionPath_ae Y hmp u D hD hJ hB g hu c t)
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun c : OrderedFinpartition n =>
    partitionPath Y hmp u D hD hJ hB c t)
  filter_upwards [hterms,hsum] with x hx hs
  simp only [tensorPath,ContinuousMap.sum_apply]
  rw [hs]
  simp only [Finset.sum_apply]
  rw [iteratedFDeriv_comp (i := n) ((hg t).contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp))
    ((hY t).contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp)) le_rfl]
  simp only [FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition,
    ftaylorSeries]
  exact Finset.sum_congr rfl (fun c _ => hx c)

end EulerVolumeSobolevPath

end
end

end

section

/-! Actual all-order field towers retain their spatial Sobolev regularity
after a smooth volume-preserving change of coordinates. -/

section

/-! Actual Sobolev integrability under a smooth volume-preserving change
of variables, with an explicit finite-order composition constant. -/

@[expose] public section

noncomputable section

namespace EulerVolumeSobolevComposition

open Set MeasureTheory EulerLiftedGradientSpace
open scoped ContDiff NNReal ENNReal

variable (f g : Vector3 → Vector3) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
  (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
  (hjet : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i)

include hf hg hjet in
theorem compositionTensor_pointwise (x : Vector3) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      ((n.factorial : ℝ)*D^n) * ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖ := by
  have h := norm_iteratedFDeriv_comp_le hg hf (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω)) x
    (C := ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) (D := D)
    (fun i hi => Finset.single_le_sum
      (f := fun j : Fin (n+1) => ‖iteratedFDeriv ℝ j.val g (f x)‖)
      (fun _ _ => norm_nonneg _)
      (Finset.mem_univ (⟨i,by omega⟩ : Fin (n+1))))
    (fun i h1 hi => hjet i h1 hi x)
  exact h.trans_eq (by ring)

variable (hmp : MeasurePreserving f volume volume)
  (hLp : ∀ i, i ≤ n → MemLp (iteratedFDeriv ℝ i g) 2 volume)

include hmp hLp in
theorem composedJetNorm_memLp (i : Fin (n + 1)) :
    MemLp (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume :=
  ((hLp i (by omega)).norm).comp_measurePreserving hmp

include hf hg hD hjet hmp hLp in
theorem compositionTensor_memLp :
    MemLp (iteratedFDeriv ℝ n (g ∘ f)) 2 volume := by
  have hs : MemLp (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume :=
    memLp_finsetSum _ (fun i _ => composedJetNorm_memLp f g n hmp hLp i)
  have hc : Continuous (iteratedFDeriv ℝ n (g ∘ f)) :=
    (hg.comp hf).continuous_iteratedFDeriv (by simp)
  apply (hs.const_mul ((n.factorial : ℝ)*D^n)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))]
  exact compositionTensor_pointwise f g hf hg n D hjet x

/-- Composition tensor Lᵖ, given by `(compositionTensor_memLp f g hf hg n D hD hjet hmp
hLp).toLp (iteratedFDeriv ℝ n (g ∘ f))`. -/
def compositionTensorLp :
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3) :=
  (compositionTensor_memLp f g hf hg n D hD hjet hmp hLp).toLp (iteratedFDeriv ℝ n (g ∘ f))

theorem compositionTensorLp_norm_le :
    ‖compositionTensorLp f g hf hg n D hD hjet hmp hLp‖ ≤
      ((n.factorial : ℝ)*D^n) * ∑ i : Fin (n+1),
        (eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume).toReal := by
  let β : ℝ≥0 := ⟨(n.factorial : ℝ)*D^n,by positivity⟩
  have hA : eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 volume ≤
      (β : ℝ≥0∞)*eLpNorm (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    filter_upwards [] with x
    apply NNReal.coe_le_coe.mp
    change ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ ((n.factorial : ℝ)*D^n) *
      ‖∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖‖
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact compositionTensor_pointwise f g hf hg n D hjet x
  have he : (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) =
      ∑ i : Fin (n+1), (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he] at hA
  have hB := eLpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) =>
    (composedJetNorm_memLp f g n hmp hLp i).aestronglyMeasurable)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hc (i : Fin (n+1)) : eLpNorm (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume =
      eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume := by
    change eLpNorm ((fun y => ‖iteratedFDeriv ℝ i.val g y‖) ∘ f) 2 volume = _
    rw [eLpNorm_comp_measurePreserving (hLp i (by
        omega)).aestronglyMeasurable.norm hmp,eLpNorm_norm]
  simp_rw [hc] at hB
  have hAB : eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 volume ≤
      (β : ℝ≥0∞)*∑ i : Fin (n+1), eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume := by
    exact hA.trans (mul_le_mul le_rfl hB (by positivity) (by positivity))
  have hfin : (β : ℝ≥0∞)*∑ i : Fin (n+1),
      eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.sum_ne_top.2 (fun i _ => (hLp i (by omega)).eLpNorm_ne_top))
  have hR := ENNReal.toReal_mono hfin hAB
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun (i : Fin (n+1)) _ => (hLp i.val (by omega)).eLpNorm_ne_top)] at hR
  have hβ : (β : ℝ) = (n.factorial : ℝ)*D^n := rfl
  rw [hβ] at hR
  simpa only [compositionTensorLp,Lp.norm_toLp] using hR

end EulerVolumeSobolevComposition

end
end

end

@[expose] public section

noncomputable section

namespace EulerVolumeSobolevPath

open MeasureTheory EulerVolumeSobolevComposition EulerMetricTransport EulerLiftedGradientSpace
open scoped ContDiff

variable {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
  (Y : C(K, C(Vector3, Vector3))) (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (u : ∀ i : ℕ, C(K, Lp (Tensor i) 2 (volume : Measure Vector3))) {n : ℕ}
  (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : K × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D ^ i)

theorem tensorPath_norm_le (g : K → Vector3 → Vector3)
    (hg : ∀ t, ContDiff ℝ ∞ (g t)) (hY : ∀ t, ContDiff ℝ ∞ (Y t))
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t)) (t : K) :
    ‖tensorPath Y hmp u D hD hJ hB t‖ ≤
      ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1), ‖u i.val t‖ := by
  have hLp : ∀ i, i ≤ n → MemLp (iteratedFDeriv ℝ i (g t)) 2 volume :=
    fun i _ => (memLp_congr_ae (hu i t)).mp (Lp.memLp (u i t))
  let V := compositionTensorLp (Y t) (g t) (hY t) (hg t) n D hD
    (fun i h1 hi => hB i h1 hi t) (hmp t) hLp
  have he : tensorPath Y hmp u D hD hJ hB t = V := by
    apply Lp.ext
    exact (tensorPath_ae Y hmp u D hD hJ hB g hg hY hu t).trans
      (compositionTensor_memLp (Y t) (g t) (hY t) (hg t) n D hD
        (fun i h1 hi => hB i h1 hi t) (hmp t) hLp).coeFn_toLp.symm
  rw [he]
  calc
    ‖V‖ ≤ ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1),
        (eLpNorm (iteratedFDeriv ℝ i.val (g t)) 2 volume).toReal :=
      compositionTensorLp_norm_le (Y t) (g t) (hY t) (hg t) n D hD
        (fun i h1 hi => hB i h1 hi t) (hmp t) hLp
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Lp.norm_def,eLpNorm_congr_ae (hu i.val t)]

end EulerVolumeSobolevPath

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerMetricTransport EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
  EulerLiftedGradientSpace
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)
  (k : ℝ) (m : Vector3)
  (Y : C(Icc (0 : ℝ) T, C(Vector3, Vector3)))
  (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : Icc (0 : ℝ) T × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D ^ i)

/-- Volume point field, given by `A.physicalPointField k m t ∘ Y t`. -/
def volumePointField (t : Icc (0 : ℝ) T) : Vector3 → Vector3 :=
  A.physicalPointField k m t ∘ Y t

/-- Volume tensor path, given by `EulerVolumeSobolevPath.tensorPath Y hmp (fun i =>
A.physicalTensorPath k m i) D hD hJ hB`. -/
def volumeTensorPath : C(Icc (0 : ℝ) T,
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3)) :=
  EulerVolumeSobolevPath.tensorPath Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB

theorem volumePointField_smooth (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (A.volumePointField k m Y t) :=
  (A.physicalPointField_smooth k m t).comp (hY t)

theorem volumeTensorPath_ae (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    (A.volumeTensorPath k m Y hmp n D hD hJ hB t : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (A.volumePointField k m Y t) :=
  EulerVolumeSobolevPath.tensorPath_ae Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB
    (A.physicalPointField k m) (A.physicalPointField_smooth k m) hY
    (A.physicalTensorPath_ae k m) t

theorem volumeTensorPath_norm_le (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    ‖A.volumeTensorPath k m Y hmp n D hD hJ hB t‖ ≤
      ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1),
        frequencyFactor k m^i.val*(4 : ℝ)^i.val*Real.sqrt (2/P+2*P)*‖A.realization (i.val+1) t‖ :=
            by
  have h := EulerVolumeSobolevPath.tensorPath_norm_le Y hmp (fun i => A.physicalTensorPath k m i)
    D hD hJ hB (A.physicalPointField k m) (A.physicalPointField_smooth k m) hY
    (A.physicalTensorPath_ae k m) t
  exact h.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => A.physicalTensorValue_norm_le k m i.val t)) (by positivity))

end EulerAllOrderCorrectionData.FieldTower

end
end

end

section

/-! A finite-order Sobolev composition constant obtained from the actual
parent deformation. No inverse-flow derivative budget is assumed. -/

@[expose] public section

noncomputable section

namespace EulerPacketInverseFlowGevrey

open Set EulerSmoothLimit EulerGevrey EulerPacketPiola
open scoped ContDiff BoundedContinuousFunction

/-- Finite order constant, given by `1+9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2`. -/
def finiteOrderConstant (C R : ℝ) (n : ℕ) : ℝ :=
  1+9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2

theorem sourceInverseRadius_one_le (C R : ℝ) (hR : 0 ≤ R) :
    1 ≤ sourceInverseRadius C R := by
  unfold sourceInverseRadius
  have h : 0 ≤ 18*C^2*R := by positivity
  linarith

theorem finiteOrderConstant_one_le (C R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    1 ≤ finiteOrderConstant C R n := by
  have hL := (sourceInverseRadius_pos C R hR).le
  unfold finiteOrderConstant
  have h : 0 ≤ 9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2 := by positivity
  linarith

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)

include hX hY hXY hR hC hdet hF in
theorem inverseFlow_finiteOrderBound (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ (finiteOrderConstant C R n)^i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hjn : j ≤ n := by omega
  have hL := sourceInverseRadius_one_le C R hR
  have hD := finiteOrderConstant_one_le C R hR n
  have hfac : (j.factorial : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hjn
  have hbound : 9*C^2*(sourceInverseRadius C R)^j*(j.factorial : ℝ)^2 ≤
      9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2 := by
    gcongr
  calc
    _ ≤ 9*C^2*(sourceInverseRadius C R)^j*(j.factorial : ℝ)^2 :=
      inverseFlow_gevrey D X Y hX hY hXY R C hR hC hdet hF j t x
    _ ≤ finiteOrderConstant C R n := by
      exact hbound.trans (by unfold finiteOrderConstant; linarith)
    _ = (finiteOrderConstant C R n)^1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ hD hi

end EulerPacketInverseFlowGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketSourceVolumeSobolev

open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerFlowL2Transport EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  (Z : FieldTower P D.T) (k : ℝ) (m : Space)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hYjoint : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)

include hX hYX hXY hYjoint hdet in
theorem inversePath_volume (t : Icc (0 : ℝ) D.T) :
    MeasurePreserving (inversePath Y hYjoint t) volume volume := by
  apply inversePath_measurePreserving X Y (fun s x => D.F.field s x) hX hYX hXY hYjoint
  intro s x
  rw [← EulerPacketVolumeDivergence.operatorMatrix_det]
  exact hdet s x

/-- Tensor path, constructed using `Z.volumeTensorPath`. -/
def tensorPath (n : ℕ) :
    C(Icc (0 : ℝ) D.T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  Z.volumeTensorPath k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)

theorem tensorPath_ae (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t :
      Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n (fun x => Z.pointField t (cylinderGraph P k m (Y t x))) :=
  Z.volumeTensorPath_ae k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)
    (continuousInverse_contDiff D X Y hX hXY hYjoint) t

theorem tensorPath_norm_le (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    ‖tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t‖ ≤
      ((n.factorial : ℝ)*(finiteOrderConstant C R n)^n)*∑ i : Fin (n+1),
        frequencyFactor k m^i.val*(4 : ℝ)^i.val*Real.sqrt (2/P+2*P)*‖Z.realization (i.val+1) t‖ :=
  Z.volumeTensorPath_norm_le k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)
    (continuousInverse_contDiff D X Y hX hXY hYjoint) t

end EulerPacketSourceVolumeSobolev

end
end

end

section

/-! Actual Eulerian reconstructions have every spatial derivative in L²,
continuously in time. Sobolev embedding also supplies bounded smooth
coefficient paths for the velocity and pressure force. -/

section

/-! Reconstruction W=κFz is a genuine all-order field tower. Its graph
restriction and its actual inverse-flow pullback are continuous spatial L²
paths, with no independent integrability assumption on the perturbation. -/

@[expose] public section

noncomputable section

namespace EulerPacketPhysicalField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerAllOrderCorrectionData EulerPacketCorrectionCoefficients
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerFlowL2Transport

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (κ : ℝ) (Z : FieldTower P D.T)

/-- Reconstructed tower, given by `(Z.multiply ((frameCoefficient D).toCoefficientTower P)).smul
κ`. -/
def reconstructedTower : FieldTower P D.T :=
  (Z.multiply ((frameCoefficient D).toCoefficientTower P)).smul κ

theorem reconstructedTower_pointField (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (reconstructedTower D P κ Z).pointField t x =
      κ • D.F.field t x.1 (Z.pointField t x) := by
  rw [reconstructedTower,FieldTower.smul_pointField,FieldTower.multiply_pointField]
  rfl

/-- Graph path, given by `(reconstructedTower D P κ Z).canonicalGraphWordPath (physicalPhase P k
D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0`. -/
def graphPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).canonicalGraphWordPath
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0

theorem graphPath_ae (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (graphPath D P κ Z k t : Space → Space) =ᵐ[volume]
      fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x)) := by
  have h := (reconstructedTower D P κ Z).canonicalGraphWordPath_ae
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0 t
  simpa only [graphPath,EulerCylinderSobolev.iteratedFieldDerivative_zero,
    reconstructedTower_pointField,physicalPhase,cylinderGraph] using h

/-- Graph tensor path, given by `(reconstructedTower D P κ Z).physicalTensorPath k D.m₀ n`. -/
def graphTensorPath (k : ℝ) (n : ℕ) :
    C(Icc (0 : ℝ) D.T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).physicalTensorPath k D.m₀ n

theorem graphTensorPath_ae (k : ℝ) (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (graphTensorPath D P κ Z k n t : Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n
        (fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x))) := by
  have h := (reconstructedTower D P κ Z).physicalTensorPath_ae k D.m₀ n t
  have he : (reconstructedTower D P κ Z).physicalPointField k D.m₀ t =
      fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x)) :=
    funext (fun x => reconstructedTower_pointField D P κ Z t (cylinderGraph P k D.m₀ x))
  rw [he] at h
  exact h

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (D.F.field t x).det = 1)

/-- Eulerian path, given by `transportPath X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet
(graphPath D P κ Z k)`. -/
def eulerianPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  transportPath X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet (graphPath D P κ Z k)

theorem eulerianPath_ae (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (eulerianPath D P κ Z X Y hX hYX hXY hY hdet k t : Space → Space) =ᵐ[volume]
      fun x => κ • D.F.field t (Y t x)
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  transportPath_ae X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet
    (graphPath D P κ Z k) _ (graphPath_ae D P κ Z k) t

theorem eulerianPath_norm (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    ‖eulerianPath D P κ Z X Y hX hYX hXY hY hdet k t‖ = ‖graphPath D P κ Z k t‖ :=
  transportPath_norm X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet (graphPath D P κ Z k) t

end EulerPacketPhysicalField

end
end

end

section

/-! The actual source-flow pullback is a smooth spatial L² field at
every time. Its tensor paths also give a bounded smooth coefficient
path, with continuity in the uniform norm at every spatial order. -/

@[expose] public section

noncomputable section

namespace EulerPacketSourceVolumeSobolev

open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerFlowL2Transport EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerGevrey
  EulerLpTranslation EulerMeanCoefficients
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  (Z : FieldTower P D.T) (k : ℝ) (m : Space)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hYjoint : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)

/-- Smooth field, bundling `field`, `smooth`, `integrable`. -/
def smoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space where
  field x := Z.pointField t (cylinderGraph P k m (Y t x))
  smooth := (Z.physicalPointField_smooth k m t).comp
    (continuousInverse_contDiff D X Y hX hXY hYjoint t)
  integrable n :=
    (Lp.memLp (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t)).ae_eq
      (tensorPath_ae D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t)

theorem smoothField_jetLp (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF t).jetLp n =
      tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t := by
  apply Lp.ext
  exact (SmoothL2Field.jetLp_ae _ n).trans
    (tensorPath_ae D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t).symm

theorem smoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF t).jetLp n)
        := by
  simp only [smoothField_jetLp]
  exact (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n).continuous

/-- Smooth coefficient path, constructed using `EulerMeanSobolevBoundedField.coefficientPath`. -/
def smoothCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerMeanSobolevBoundedField.coefficientPath
    (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF)
    (smoothField_jetLp_continuous D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF)

theorem smoothCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (smoothCoefficientPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF).field t x =
      Z.pointField t (cylinderGraph P k m (Y t x)) :=
  EulerMeanSobolevBoundedField.coefficientPath_apply _ _ t x

end EulerPacketSourceVolumeSobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketPhysicalField

open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerPacketCorrectionCoefficients EulerGraphPressurePotential EulerGevrey
  EulerLpTranslation EulerMeanCoefficients EulerPacketPiola

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (κ : ℝ) (Z : FieldTower P D.T)

/-- Pressure force tower, given by `(Z.multiply ((inverseCoefficient
D).adjoint.toCoefficientTower P)).smul κ`. -/
def pressureForceTower : FieldTower P D.T :=
  (Z.multiply ((inverseCoefficient D).adjoint.toCoefficientTower P)).smul κ

theorem pressureForceTower_pointField (t : Icc (0 : ℝ) D.T)
    (x : EulerLiftedGradientSpace.LiftDomain P) :
    (pressureForceTower D P κ Z).pointField t x =
      κ • (D.FInv.field t x.1).adjoint (Z.pointField t x) := by
  rw [pressureForceTower, FieldTower.smul_pointField, FieldTower.multiply_pointField]
  rfl

variable (k : ℝ) (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)

/-- Eulerian smooth field, given by `EulerPacketSourceVolumeSobolev.smoothField D
(reconstructedTower D P κ Z) k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF t`. -/
def eulerianSmoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space :=
  EulerPacketSourceVolumeSobolev.smoothField D (reconstructedTower D P κ Z) k D.m₀
    X Y hX hYX hXY hY R C hR hC hdet hF t

theorem eulerianSmoothField_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (eulerianSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).field x =
      κ • D.F.field t (Y t x) (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  reconstructedTower_pointField D P κ Z t (cylinderGraph P k D.m₀ (Y t x))

theorem eulerianSmoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t =>
      (eulerianSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).jetLp n) :=
  EulerPacketSourceVolumeSobolev.smoothField_jetLp_continuous D (reconstructedTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF n

/-- Eulerian coefficient path, given by `EulerPacketSourceVolumeSobolev.smoothCoefficientPath D
(reconstructedTower D P κ Z) k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF`. -/
def eulerianCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (reconstructedTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF

theorem eulerianCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (eulerianCoefficientPath D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF).field t x =
      κ • D.F.field t (Y t x) (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) := by
  rw [eulerianCoefficientPath, EulerPacketSourceVolumeSobolev.smoothCoefficientPath_apply,
    reconstructedTower_pointField]
  rfl

/-- Pressure force smooth field, given by `EulerPacketSourceVolumeSobolev.smoothField D
(pressureForceTower D P κ Z) k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF t`. -/
def pressureForceSmoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space :=
  EulerPacketSourceVolumeSobolev.smoothField D (pressureForceTower D P κ Z) k D.m₀
    X Y hX hYX hXY hY R C hR hC hdet hF t

theorem pressureForceSmoothField_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (pressureForceSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).field x =
      κ • (D.FInv.field t (Y t x)).adjoint
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  pressureForceTower_pointField D P κ Z t (cylinderGraph P k D.m₀ (Y t x))

theorem pressureForceSmoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t =>
      (pressureForceSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).jetLp n) :=
  EulerPacketSourceVolumeSobolev.smoothField_jetLp_continuous D (pressureForceTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF n

/-- Pressure force coefficient path, given by
`EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (pressureForceTower D P κ Z) k D.m₀
X Y hX hYX hXY hY R C hR hC hdet hF`. -/
def pressureForceCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (pressureForceTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF

theorem pressureForceCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (pressureForceCoefficientPath D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF).field t x =
      κ • (D.FInv.field t (Y t x)).adjoint
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) := by
  rw [pressureForceCoefficientPath, EulerPacketSourceVolumeSobolev.smoothCoefficientPath_apply,
    pressureForceTower_pointField]
  rfl

end EulerPacketPhysicalField

end
end

end

section

/-! Actual odd parent fields supply the parity data for both initialized
packet branches. The resulting corrected coefficient, and hence the
actual next particle map, retain oddness without a new symmetry premise. -/

section

/-! The actual corrected lifted velocity is odd when its prescribed
correction data have the checked parity. Passing from L² symmetry to
the canonical point field supplies symmetry of the real flow coefficient. -/

@[expose] public section

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set EulerLiftedGradientSpace EulerCylinderReflection EulerCorrectionAssembly

variable {P T : ℝ} [Fact (0 < P)] (A : FieldTower P T)

theorem pointField_odd
    (ho : ∀ t, -reflection P (A.field t) = A.field t) (t : Icc (0 : ℝ) T) :
    Function.Odd (A.pointField t) :=
  continuous_representative_odd P (A.field t) (A.pointField t) (ho t)
    (Continuous.uncurry_left t A.pointField_joint_continuous) (A.pointField_ae t)

end EulerAllOrderCorrectionData.FieldTower

namespace EulerAllOrderDriftCorrection

open Set EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerCylinderReflection
  EulerCorrectionAssembly EulerPacketCylinderField EulerPacketProfileRecursion
  EulerMetricTransport EulerLiftedSmoothTimeField

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A)

theorem Budget.correctedFieldTower_odd (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    -reflection P ((B.correctedFieldTower P).field t)=(B.correctedFieldTower P).field t := by
  change -reflection P (A.approximation.field t+B.commonPath P t) =
    A.approximation.field t+B.commonPath P t
  rw [map_add,neg_add,E.approximation,B.commonPath_odd P E]

theorem Budget.liftedPacketCoefficient_odd {raw : VectorField}
    (G : Field P T raw) (hG : A.approximation = G.toFieldTower)
    (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    Function.Odd ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) := by
  intro z
  rw [B.liftedPacketCoefficient_eq_corrected P G hG,
    B.liftedPacketCoefficient_eq_corrected P G hG]
  have hc : coveringMap P (-z) = -coveringMap P z := by
    simp only [coveringMap,Prod.fst_neg,Prod.snd_neg,AddCircle.coe_neg,Prod.neg_mk]
  rw [hc,(B.correctedFieldTower P).pointField_odd (B.correctedFieldTower_odd P E) t]
  exact (EulerLiftedTransportTrace.transportLinear A.κ A.direction).map_neg _

end EulerAllOrderDriftCorrection

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.OddData

open Set EulerSmoothLimit EulerSpatialCutoffs EulerPacketTerminalDatum
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCorrectionAssembly
  EulerTimeIntervalRestriction EulerGraphInvariantFlow EulerAllOrderCorrectionData
  EulerAllOrderDriftCorrection

variable {A : Parent} (O : OddData A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ S) (α : ℝ)

include O hSym

theorem forwardCorrectionParity (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ParityData period
      (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm R S hS H) N hN k hk) :=
  forwardInitializedCorrectionParityData (A.meanData H) (A.transverseData m hm R S hS) rfl
    δ hδ ξ hs α (O.meanEvenData H) hSym O.frame_even O.strain_even
    (A.sourceAgreement m hm R S hS H) N hN k hk

theorem joinedCorrectionParity (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ParityData period
      (initializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS) rfl
        τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
        (A.sourceAgreement m hm R S hS H) N hN k hk) := by
  apply initializedCorrectionParityData (A.meanData H) (A.transverseData m hm R S hS) rfl
    τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
    (O.meanEvenData H) hSym O.frame_even O.strain_even
    _ (A.sourceAgreement m hm R S hS H) N hN k hk
  intro t x
  exact O.curvature_even (initialInclusion A.T τ hτT.le t) x

omit hSym [CompleteSpace U] in
theorem childOfPacket {P : ℝ} [Fact (0 < P)] {C : EulerAllOrderCorrectionData.Data P A.T}
    (B : Budget P A.T_pos C) (E : ParityData P C)
    {raw : VectorField} (V : Field P A.T raw) (hV : C.approximation = V.toFieldTower)
    (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
    (k : ℝ) (hgraph : ∀ t z, graphConstraint k C.direction (G.A.field t z) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1) :
    OddData (A.child G k C.direction hgraph nextEll hnext hnext1) := by
  apply O.child G _ k C.direction hgraph nextEll hnext hnext1
  intro t
  rw [hG]
  exact B.liftedPacketCoefficient_odd P V hV E t

end EulerParentPacketFrames.OddData

end
end

end

section

/-! Actual physical L² fields of a packet over a parent. The genuine
inverse and the proved parent label bound supply all reconstruction
regularity, and the physical spatial scale is retained exactly. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPacketPhysicalField EulerAllOrderCorrectionData EulerPacketParentLabelBounds
  EulerTransverseFrameCoordinates EulerGraphPressurePotential

namespace ParticleInverse

variable {A : Parent} (I : ParticleInverse A)

theorem normalized_scaled (t : Icc (0 : ℝ) A.T) (x : Space) :
    I.normalized t (A.ell⁻¹ • x)=A.ell⁻¹ • I.field t x := by
  simp only [normalized,Parent.packetInverse,projIcc_of_mem A.T_pos.le t.property,
    smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]

end ParticleInverse

namespace LabelData

variable {A : Parent} (L : LabelData A) (I : ParticleInverse A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (P : ℝ) [Fact (0 < P)] (κ : ℝ) (Z : FieldTower P A.T) (k : ℝ)

/-- Packet velocity field, constructed using `scaleField`. -/
def packetVelocityField (t : Icc (0 : ℝ) A.T) : SmoothL2Field Space :=
  scaleField A.ell A.ell_pos
    (eulerianSmoothField (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound t)

/-- Packet force field, constructed using `scaleField`. -/
def packetForceField (t : Icc (0 : ℝ) A.T) : SmoothL2Field Space :=
  scaleField A.ell A.ell_pos
    (pressureForceSmoothField (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound t)

theorem packetVelocityField_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    (L.packetVelocityField I m hm J support hSupport P κ Z k t).field x =
      A.ell • (κ • A.frame.field t (A.ell⁻¹ • I.field t x)
        (Z.pointField t (cylinderGraph P k m (A.ell⁻¹ • I.field t x)))) := by
  rw [packetVelocityField,scaleField_apply]
  erw [eulerianSmoothField_apply,I.normalized_scaled]
  rfl

theorem packetForceField_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    (L.packetForceField I m hm J support hSupport P κ Z k t).field x =
      A.ell • (κ • (A.inverse.field t (A.ell⁻¹ • I.field t x)).adjoint
        (Z.pointField t (cylinderGraph P k m (A.ell⁻¹ • I.field t x)))) := by
  rw [packetForceField,scaleField_apply]
  erw [pressureForceSmoothField_apply,I.normalized_scaled]
  rfl

theorem packetVelocityField_continuous (n : ℕ) :
    Continuous (fun t => (L.packetVelocityField I m hm J support hSupport P κ Z k t).jetLp n) :=
  continuous_jetLp_scaleField A.ell A.ell_pos A.ell_le_one _
    (eulerianSmoothField_jetLp_continuous (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound) n

theorem packetForceField_continuous (n : ℕ) :
    Continuous (fun t => (L.packetForceField I m hm J support hSupport P κ Z k t).jetLp n) :=
  continuous_jetLp_scaleField A.ell A.ell_pos A.ell_le_one _
    (pressureForceSmoothField_jetLp_continuous (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound) n

end LabelData
end EulerParentPacketFrames

end
end

end

section

/-! The constructed child Euler evolution remains in the actual
all-order spatial Sobolev class. Its fields are the parent fields plus
the very same exact packet used in the particle-map construction. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.SobolevData

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerLpTranslation EulerLpTranslation.SmoothL2Field

variable {A : Parent} {E : Evolution A} (F : SobolevData E) (L : LabelData A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- Child, bundling `velocity`, `force`, `velocity_match`, `force_match` and the required
compatibility proofs. -/
def child : SobolevData
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1) where
  velocity t := addField (F.velocity t)
    (L.packetVelocityField E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).velocity k t)
  force t := addField (F.force t)
    (L.packetForceField E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).pressure k t)
  velocity_match t x := by
    erw [Evolution.child_velocity,A.exactPacketVelocity_eq_corrected]
    erw [addField_field,L.packetVelocityField_apply]
    change E.velocity (t,x)+_=(F.velocity t).field x+_
    erw [F.velocity_match]
    rfl
  force_match t x := by
    erw [Evolution.child_force]
    erw [Parent.exactPacketForce,addField_field,F.force_match,L.packetForceField_apply]
    simp only [ExactLiftedPacket.graphPressure,map_smul]
    rfl
  velocity_continuous := continuous_jetLp_addField _ _ F.velocity_continuous
    (L.packetVelocityField_continuous E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).velocity k)
  force_continuous := continuous_jetLp_addField _ _ F.force_continuous
    (L.packetForceField_continuous E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).pressure k)

end EulerParentPacketFrames.SobolevData

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerCorrectionAssembly

/-- Smooth state data, collecting `evolution`, `regularity`, `labels`, `odd`. -/
structure SmoothState (A : Parent) where
  /-- Evolution of `SmoothState`, of type `Evolution A`. -/
  evolution : Evolution A
  /-- Regularity of `SmoothState`, of type `SobolevData evolution`. -/
  regularity : SobolevData evolution
  /-- Label type of `SmoothState`, of type `LabelData A`. -/
  labels : LabelData A
  odd : OddData A

namespace SmoothState

variable {A : Parent} (S : SmoothState A)

/-- Restrict time, bundling `evolution`, `regularity`, `labels`, `odd`. -/
def restrictTime (T : ℝ) (hT : 0 < T) (hTA : T ≤ A.T) :
    SmoothState (A.restrictTime T hT hTA) where
  evolution := S.evolution.restrictTime T hT hTA
  regularity := S.regularity.restrictTime T hT hTA
  labels := S.labels.restrictTime T hT hTA
  odd := S.odd.restrictTime T hT hTA

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (symmetry : ParityData P (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- Packet child, bundling `evolution`, `regularity`, `labels`, `odd`. -/
def packetChild (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1)) :
    SmoothState (A.child G k m hgraph nextEll hnext hnext1) where
  evolution := S.evolution.child m hm J support hSupport B residual V hV G hG k hk hgraph
    nextEll hnext hnext1
  regularity := S.regularity.child S.labels m hm J support hSupport B residual V hV G hG k hk hgraph
    nextEll hnext hnext1
  labels := labels
  odd := S.odd.childOfPacket B symmetry V hV G hG k hgraph nextEll hnext hnext1

end SmoothState
end EulerParentPacketFrames
