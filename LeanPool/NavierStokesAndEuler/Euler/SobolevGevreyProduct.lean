/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevProduct
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
public import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearProduct
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure
import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder
import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearPressure
import LeanPool.NavierStokesAndEuler.Euler.HeatAllOrders
import LeanPool.NavierStokesAndEuler.Euler.UnshiftedProducts

/-! The actual complete Sobolev product obeys the finite Gevrey H⁶ algebra bound, including
nonsmooth inputs. -/

@[expose] public section


noncomputable section

namespace EulerSobolevGevreyProduct

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerSobolevL2Product EulerH6Nonlinear
  EulerH6Pressure EulerJetProductBounds EulerPacketWeights EulerSobolevHeat EulerVectorCylinder
open scoped Topology ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance gevreySobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance gevreySobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The external Hq block is a continuous function of the actual finite Sobolev class. -/
theorem continuous_blockNorm {s q n : ℕ} (h : n + q ≤ s) :
    Continuous (fun u : SobolevSpace period s => blockNorm period (toJet period u) q n) := by
  unfold blockNorm
  apply continuous_finsetSum
  intro r hr
  have hnr : n+r ≤ s := by have := Finset.mem_range.mp hr; omega
  simp only [levelNorm_eq_words]
  apply continuous_finsetSum
  intro w _
  have he : (fun u : SobolevSpace period s => ‖(toJet period u).word w‖) =
      fun u => ‖wordOperator period (q := s) ⟨⟨n+r, Nat.lt_succ_of_le hnr⟩, w⟩ u‖ := by
    funext u
    rw [toJet_word period u hnr]
    rfl
  rw [he]
  exact (wordOperator period (q := s) ⟨⟨n+r, Nat.lt_succ_of_le hnr⟩, w⟩).continuous.norm

/-- Every truncated weighted block norm is continuous on its genuine Sobolev domain. -/
theorem continuous_weighted_blockNorm {s q : ℕ} (N : ℕ) (h : N + q ≤ s) (ρ : ℝ) :
    Continuous (fun u : SobolevSpace period s =>
      ∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period u) q n) := by
  apply continuous_finsetSum
  intro n hn
  exact (continuous_blockNorm period (by
      have := Finset.mem_range.mp hn; omega : n+q ≤ s)).const_mul _

/-- On actual smooth H∞ representatives, the complete product has the cutoff-independent weighted H⁶
bound. -/
theorem product_weighted_bound_smooth {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period s) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
        period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
        period)) :
    (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period (productHq period hs L
        hL u v)) 6 n) ≤
      productConstant period 3 * (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet
          period u) 6 n) *
        (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period v) 6 n) := by
  have hLf := postcomp_smooth period L f hf
  have hLfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w (L ∘ f)) 2
      (liftMeasure period) :=
    fun j w => postcomp_word_memLp period (le_refl j) L f hf (fun r _ a => hfL r a) w
  have hp : (value period (productHq period hs L hL u v) : LiftDomain period → Vector3)
      =ᵐ[liftMeasure period]
      (fun x => L (f x) • g x) := by
    filter_upwards [productHq_ae period hs L hL u v, hu, hv] with x hx hux hvx
    rw [hx, hux, hvx]
  have hps : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => L (f x) • g x) x) :=
    fun x => (hLf x).smul (hg x)
  have heq (a : SobolevSpace period s) (b : LiftDomain period → Vector3)
      (ha : (value period a : LiftDomain period → Vector3) =ᵐ[liftMeasure period] b)
      (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x)) :
      (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period a) 6 n) =
        ∑ n ∈ Finset.range (N+1), weight ρ n * wordSobolevNorm period 6 n b := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [blockNorm_eq_classical period (toJet period a) (by
        have := Finset.mem_range.mp hn; omega) b ha hb]
  rw [heq _ _ hp hps, heq u f hu hf, heq v g hv hg]
  apply (product_unshifted_weighted_bound period 3 N ρ hρ (L ∘ f) g hLf hg hLfL hgL).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun n _ =>
    mul_nonneg (weight_pos hρ n).le (wordSobolevNorm_nonneg period 6 n g))
  apply mul_le_mul_of_nonneg_left _ (productConstant_nonneg period 3)
  apply Finset.sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_left (wordSobolevNorm_postcomp_le period 6 n L hL f hf hfL)
      (weight_pos hρ n).le

/-- Continuity of the actual product in both finite-Sobolev inputs. -/
theorem continuous_product {s : ℕ} (hs : 6 ≤ s) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    Continuous (fun p : SobolevSpace period s × SobolevSpace period s => productHq period hs L hL
        p.1 p.2) :=
  (productHqBilinear period hs L hL).continuous₂

/-- The cutoff-independent Gevrey product bound holds for actual finite Sobolev inputs, by genuine
H∞ approximation and continuity. -/
theorem product_weighted_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period s) :
    (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period (productHq period hs L
        hL u v)) 6 n) ≤
      productConstant period 3 * (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet
          period u) 6 n) *
        (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period (toJet period v) 6 n) := by
  let U : ℕ → SobolevSpace period s := fun n => restrictOperator period (by
      omega : s ≤ s+3) (smoothApprox period s n u)
  let V : ℕ → SobolevSpace period s := fun n => restrictOperator period (by
      omega : s ≤ s+3) (smoothApprox period s n v)
  let W := fun a : SobolevSpace period s => ∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period
      (toJet period a) 6 n
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto V Filter.atTop (𝓝 v) := smoothApprox_tendsto period v
  have hW : Continuous W := continuous_weighted_blockNorm period N hN ρ
  have hp : Filter.Tendsto (fun n => productHq period hs L hL (U n) (V n)) Filter.atTop
      (𝓝 (productHq period hs L hL u v)) :=
    by
      have hpairs : Filter.Tendsto (fun n => (U n, V n)) Filter.atTop (𝓝 (u,v)) := hU.prodMk_nhds hV
      have hcont : Filter.Tendsto
          (fun p : SobolevSpace period s × SobolevSpace period s => productHq period hs L hL p.1
              p.2)
          (𝓝 (u,v)) (𝓝 (productHq period hs L hL u v)) := (continuous_product period hs L
              hL).tendsto (u,v)
      have hcomp := hcont.comp hpairs
      exact hcomp
  have hleft : Filter.Tendsto (fun n => W (productHq period hs L hL (U n) (V n))) Filter.atTop
      (𝓝 (W (productHq period hs L hL u v))) := (hW.tendsto _).comp hp
  have hright : Filter.Tendsto (fun n => productConstant period 3 * W (U n) * W (V n)) Filter.atTop
      (𝓝 (productConstant period 3 * W u * W v)) :=
    ((hW.tendsto u |>.comp hU).const_mul (productConstant period 3)).mul (hW.tendsto v |>.comp hV)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨f,hf,hfs,hfL⟩ := smoothApprox_representative_all period n u
  obtain ⟨g,hg,hgs,hgL⟩ := smoothApprox_representative_all period n v
  exact product_weighted_bound_smooth period hs N hN ρ hρ L hL (U n) (V n) f g hf hg hfs hgs hfL hgL

end EulerSobolevGevreyProduct
