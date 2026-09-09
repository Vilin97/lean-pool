/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureJetIdentities
import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators

/-! Genuine one-derivative L² smoothing lifts to the complete cylinder Sobolev scale. -/

@[expose] public section


noncomputable section

namespace EulerSobolevSmoothing

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

variable (A : LiftL2 period →L[ℝ] LiftL2 period) (C : ℝ)
variable (hD : ∀ i : Fin 4, ∀ f : LiftL2 period, ∃ g : LiftL2 period,
  HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f)) g
      0 ∧
    ‖g‖ ≤ C * ‖f‖)

/-- The uniquely determined strong derivative of a genuinely smoothing L² operator. -/
def smoothingDerivative (i : Fin 4) (f : LiftL2 period) : LiftL2 period :=
  Classical.choose (hD i f)

/-- The chosen derivative is the actual strong derivative of the translated output. -/
theorem smoothingDerivative_hasDerivAt (i : Fin 4) (f : LiftL2 period) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f))
      (smoothingDerivative period A C hD i f) 0 := (Classical.choose_spec (hD i f)).1

/-- The actual derivative obeys the given L² smoothing estimate. -/
theorem smoothingDerivative_bound (i : Fin 4) (f : LiftL2 period) :
    ‖smoothingDerivative period A C hD i f‖ ≤ C * ‖f‖ := (Classical.choose_spec (hD i f)).2

/-- Uniqueness of strong derivatives proves additivity of the smoothing derivative. -/
theorem smoothingDerivative_add (i : Fin 4) (f g : LiftL2 period) :
    smoothingDerivative period A C hD i (f + g) =
      smoothingDerivative period A C hD i f + smoothingDerivative period A C hD i g := by
  apply (smoothingDerivative_hasDerivAt period A C hD i (f + g)).unique
  simpa only [map_add] using
    (smoothingDerivative_hasDerivAt period A C hD i f).fun_add
      (smoothingDerivative_hasDerivAt period A C hD i g)

/-- Uniqueness of strong derivatives proves homogeneity of the smoothing derivative. -/
theorem smoothingDerivative_smul (i : Fin 4) (r : ℝ) (f : LiftL2 period) :
    smoothingDerivative period A C hD i (r • f) = r • smoothingDerivative period A C hD i f := by
  apply (smoothingDerivative_hasDerivAt period A C hD i (r • f)).unique
  simpa only [map_smul, Pi.smul_def] using
    (smoothingDerivative_hasDerivAt period A C hD i f).const_smul r

/-- Each derivative of the smoothing operator is a bounded linear L² operator. -/
def smoothingDerivativeOperator (i : Fin 4) : LiftL2 period →L[ℝ] LiftL2 period :=
  LinearMap.mkContinuous
    { toFun := smoothingDerivative period A C hD i
      map_add' := smoothingDerivative_add period A C hD i
      map_smul' := smoothingDerivative_smul period A C hD i }
    C (smoothingDerivative_bound period A C hD i)

/-- The bounded derivative operator retains its actual strong-derivative characterization. -/
theorem smoothingDerivativeOperator_hasDerivAt (i : Fin 4) (f : LiftL2 period) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f))
      (smoothingDerivativeOperator period A C hD i f) 0 :=
  smoothingDerivative_hasDerivAt period A C hD i f

/-- The bounded derivative operator retains the actual smoothing estimate. -/
theorem smoothingDerivativeOperator_bound (i : Fin 4) (f : LiftL2 period) :
    ‖smoothingDerivativeOperator period A C hD i f‖ ≤ C * ‖f‖ :=
  smoothingDerivative_bound period A C hD i f

/-- Differentiating a translation-commuting smoothing operator preserves translation commutation. -/
theorem smoothingDerivative_translation
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (i : Fin 4) (a : LiftDomain period) (f : LiftL2 period) :
    translation period a (smoothingDerivativeOperator period A C hD i f) =
      smoothingDerivativeOperator period A C hD i (translation period a f) := by
  have hd := (translation period a).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (smoothingDerivative_hasDerivAt period A C hD i f)
  have he : (fun t => translation period a
      (translation period (translationPath period (standardDirection i) t) (A f))) =
      fun t => translation period (translationPath period (standardDirection i) t)
        (A (translation period a f)) := by
    funext t
    rw [hA]
    exact translations_commute period a _ _
  change HasDerivAt (fun t => translation period a
    (translation period (translationPath period (standardDirection i) t) (A f)))
    (translation period a (smoothingDerivative period A C hD i f)) 0 at hd
  rw [he] at hd
  exact hd.unique (smoothingDerivative_hasDerivAt period A C hD i (translation period a f))

/-- A true smoothing operator adds one complete level to any finite strong derivative jet. -/
def gainJet {q : ℕ} {f : LiftL2 period}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (J : SpatialJet period standardDirection q f) : SpatialJet period standardDirection (q + 1) (A
        f) :=
  .succ (fun i => smoothingDerivativeOperator period A C hD i f)
    (fun i => EulerPressureJetIdentities.SpatialJet.map
      (smoothingDerivativeOperator period A C hD i)
      (smoothingDerivative_translation period A C hD hA i) J)
    (fun i => smoothingDerivativeOperator_hasDerivAt period A C hD i f)

/-- The Sobolev element obtained by actual one-derivative smoothing. -/
def gain {q : ℕ}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : SobolevSpace period (q + 1) :=
  ofJet period (gainJet period A C hD hA (toJet period u))

/-- Smoothing on the Sobolev scale has exactly the original L² output. -/
@[simp]
theorem gain_value {q : ℕ}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : value period (gain period A C hD hA u) = A (value period u) :=
  value_ofJet period _

/-- The Sobolev derivative gain has an explicit bound independent of the derivative order. -/
theorem gain_bound {q : ℕ} (hC : 0 ≤ C)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : ‖gain period A C hD hA u‖ ≤ max ‖A‖ C * ‖u‖ := by
  change ‖(gain period A C hD hA u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_max_of_le_left (norm_nonneg A)) (norm_nonneg
      u))).mpr
  rintro ⟨⟨n, hn⟩, w⟩
  cases n with
  | zero =>
    change ‖(gainJet period A C hD hA (toJet period u)).word w‖ ≤ _
    rw [SpatialJet.word_zero]
    exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (value_norm_le period u) (norm_nonneg
        A)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u)))
  | succ n =>
    change ‖(gainJet period A C hD hA (toJet period u)).word w‖ ≤ _
    rw [gainJet, SpatialJet.word_succ, EulerPressureJetIdentities.SpatialJet.map_word]
    have h := smoothingDerivativeOperator_bound period A C hD (w (Fin.last n))
      ((toJet period u).word (Fin.init w))
    rw [toJet_word period u (by omega)] at h
    rw [toJet_word period u (by omega)]
    exact h.trans ((mul_le_mul_of_nonneg_left
      (word_norm_le period u ⟨⟨n, by omega⟩, Fin.init w⟩) hC).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg u)))

/-- The actual Sobolev smoothing construction is linear. -/
def gainLinearMap (q : ℕ)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f)) :
    SobolevSpace period q →ₗ[ℝ] SobolevSpace period (q + 1) where
  toFun := gain period A C hD hA
  map_add' := by
    intro u v
    apply value_injective period
    change value period (gain period A C hD hA (u + v)) =
      value period (gain period A C hD hA u) + value period (gain period A C hD hA v)
    simp only [gain_value]
    exact map_add A _ _
  map_smul' := by
    intro r u
    apply value_injective period
    change value period (gain period A C hD hA (r • u)) = r • value period (gain period A C hD hA u)
    simp only [gain_value]
    exact map_smul A r _

/-- A genuine bounded map H^q to H^(q+1), obtained from actual L² smoothing derivatives. -/
def gainOperator (q : ℕ) (hC : 0 ≤ C)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f)) :
    SobolevSpace period q →L[ℝ] SobolevSpace period (q + 1) :=
  (gainLinearMap period A C hD q hA).mkContinuous (max ‖A‖ C) (gain_bound period A C hD hC hA)

end EulerSobolevSmoothing
