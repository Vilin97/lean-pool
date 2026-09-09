/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! Finite sums of genuine Hilbert metric energies, with viscosity and explicit norm comparison. -/

@[expose] public section


noncomputable section

namespace EulerFiniteMetricEnergy

open InnerProductSpace Real EulerMetricEnergyEvolution
open scoped Topology

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The square of the Hilbert norm of a finite family. -/
def familySquaredNorm (v : ι → H) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The Hilbert norm of a finite family, expressed without choosing a product-space model. -/
def familyNorm (v : ι → H) : ℝ := √(familySquaredNorm v)

/-- The actual sum of metric quadratic energies of a finite family. -/
def familyEnergy (K : H →L[ℝ] H) (v : ι → H) : ℝ := ∑ i, ⟪K (v i), v i⟫_ℝ

/-- The source's square root of the sum of all base-word metric energies. -/
def familyMetricNorm (K : H →L[ℝ] H) (v : ι → H) : ℝ := √(familyEnergy K v)

omit [InnerProductSpace ℝ H] in
theorem familySquaredNorm_nonneg (v : ι → H) : 0 ≤ familySquaredNorm v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [InnerProductSpace ℝ H] in
theorem familyNorm_nonneg (v : ι → H) : 0 ≤ familyNorm v := sqrt_nonneg _

omit [InnerProductSpace ℝ H] in
theorem familyNorm_sq (v : ι → H) : familyNorm v ^ 2 = familySquaredNorm v :=
  sq_sqrt (familySquaredNorm_nonneg v)

omit [InnerProductSpace ℝ H] in
/-- Cauchy-Schwarz for the actual component norms of two finite Hilbert families. -/
theorem family_cauchy_schwarz (v w : ι → H) :
    (∑ i, ‖v i‖ * ‖w i‖) ≤ familyNorm v * familyNorm w :=
  Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖v i‖) (fun i => ‖w i‖)

omit [InnerProductSpace ℝ H] in
/-- The root-of-squares norm is bounded by the sum of component norms. -/
theorem familyNorm_le_sum_norm (v : ι → H) : familyNorm v ≤ ∑ i, ‖v i‖ := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨Finset.sum_nonneg (fun i _ => norm_nonneg (v i)),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (v i))⟩

omit [InnerProductSpace ℝ H] in
/-- The reverse finite-dimensional comparison has only the fixed square-root cardinality loss. -/
theorem sum_norm_le_card_sqrt_familyNorm (v : ι → H) :
    (∑ i, ‖v i‖) ≤ √(Fintype.card ι : ℝ) * familyNorm v := by
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      familyNorm, familySquaredNorm]
    using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1 : ℝ)) (fun i => ‖v i‖)

/-- Pointwise operator coercivity sums exactly over a finite family. -/
theorem familyEnergy_coercive (K : H →L[ℝ] H) (v : ι → H) (c : ℝ)
    (hK : ∀ u, c ^ 2 * ‖u‖ ^ 2 ≤ ⟪K u, u⟫_ℝ) :
    c ^ 2 * familySquaredNorm v ≤ familyEnergy K v := by
  simpa only [familySquaredNorm, familyEnergy, Finset.mul_sum] using
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hK (v i))

/-- The metric energy has the exact operator-norm upper bound. -/
theorem familyEnergy_upper (K : H →L[ℝ] H) (v : ι → H) :
    familyEnergy K v ≤ ‖K‖ * familySquaredNorm v := by
  unfold familyEnergy familySquaredNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ‖K (v i)‖ * ‖v i‖ := real_inner_le_norm _ _
    _ ≤ (‖K‖ * ‖v i‖) * ‖v i‖ :=
      mul_le_mul_of_nonneg_right (K.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

/-- Coercivity makes the root-of-sum metric norm uniformly equivalent to the finite Hilbert norm. -/
theorem familyMetricNorm_lower (K : H →L[ℝ] H) (v : ι → H) (c : ℝ) (hc : 0 ≤ c)
    (hK : ∀ u, c ^ 2 * ‖u‖ ^ 2 ≤ ⟪K u, u⟫_ℝ) :
    c * familyNorm v ≤ familyMetricNorm K v := by
  have hl := familyEnergy_coercive K v c hK
  have hq : 0 ≤ familyEnergy K v :=
    (mul_nonneg (sq_nonneg c) (familySquaredNorm_nonneg v)).trans hl
  have hsq := sq_sqrt hq
  have hn := familyNorm_sq v
  have hE := sqrt_nonneg (familyEnergy K v)
  have hN := mul_nonneg hc (familyNorm_nonneg v)
  change c * familyNorm v ≤ √(familyEnergy K v)
  nlinarith

/-- The upper metric comparison is independent of the number of external derivatives. -/
theorem familyMetricNorm_upper (K : H →L[ℝ] H) (v : ι → H) :
    familyMetricNorm K v ≤ √‖K‖ * familyNorm v := by
  exact (sqrt_le_sqrt (familyEnergy_upper K v)).trans_eq
    (sqrt_mul (norm_nonneg K) (familySquaredNorm v))

/-- The exact derivative of the finite quadratic energy for a transport-pressure-heat system. -/
theorem family_energy_hasDerivAt (K : ℝ → H →L[ℝ] H) (e : ι → ℝ → H)
    (t ν : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing lap : ι → H)
    (hK : HasDerivAt K K' t) (he : ∀ i, HasDerivAt (e i) (e' i) t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : ∀ i, e' i + transport i + pressure i = forcing i + ν • lap i)
    (hp : ∀ i, ⟪K t (e i t), pressure i⟫_ℝ = 0) :
    HasDerivAt (fun s => familyEnergy (K s) (fun i => e i s))
      (∑ i, (⟪K' (e i t), e i t⟫_ℝ + 2 * ⟪K t (e i t), forcing i + ν • lap i⟫_ℝ -
        2 * ⟪K t (e i t), transport i⟫_ℝ)) t :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    metric_energy_evolution K (e i) t K' (e' i) (transport i) (pressure i)
      (forcing i + ν • lap i) hK (he i) hsym (heq i) (hp i))

/-- The finite energy estimate keeps forcing in the Hilbert sum norm and treats heat through its
proved quadratic bound. -/
theorem family_energy_derivative_bound (K K' : H →L[ℝ] H)
    (e transport forcing lap : ι → H) (B C ν : ℝ)
    (hB : 0 ≤ B) (hν : 0 ≤ ν)
    (ht : ∀ i, |⟪K (e i), transport i⟫_ℝ| ≤ B * ‖e i‖ ^ 2)
    (hheat : ∀ i, ⟪K (e i), lap i⟫_ℝ ≤ C * ‖e i‖ ^ 2) :
    (∑ i, (⟪K' (e i), e i⟫_ℝ + 2 * ⟪K (e i), forcing i + ν • lap i⟫_ℝ -
      2 * ⟪K (e i), transport i⟫_ℝ)) ≤
      (‖K'‖ + 2 * B + 2 * ν * C) * familySquaredNorm e +
        2 * ‖K‖ * familyNorm e * familyNorm forcing := by
  have hcomp (i : ι) : ⟪K' (e i), e i⟫_ℝ + 2 * ⟪K (e i), forcing i + ν • lap i⟫_ℝ -
      2 * ⟪K (e i), transport i⟫_ℝ ≤
      (‖K'‖ + 2 * B + 2 * ν * C) * ‖e i‖ ^ 2 + 2 * ‖K‖ * (‖e i‖ * ‖forcing i‖) := by
    have hb := energy_derivative_bound K K' (e i) (transport i) (forcing i) B hB (ht i)
    have hh := mul_le_mul_of_nonneg_left (hheat i) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hν)
    rw [inner_add_right, real_inner_smul_right]
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hcomp i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hcs := mul_le_mul_of_nonneg_left (family_cauchy_schwarz e forcing)
    (show 0 ≤ 2 * ‖K‖ by positivity)
  change _ ≤ _ * familySquaredNorm e + _ at hs
  exact hs.trans (by dsimp [familySquaredNorm]; nlinarith)

/-- Regularized root energy for a finite family, with constants independent of its cardinality. -/
theorem family_regularized_energy_evolution (K : ℝ → H →L[ℝ] H) (e : ι → ℝ → H)
    (t δ c B C ν : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing lap : ι → H)
    (hδ : 0 < δ) (hc : 0 < c) (hB : 0 ≤ B) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hcoercive : ∀ u, c ^ 2 * ‖u‖ ^ 2 ≤ ⟪K t u, u⟫_ℝ)
    (hK : HasDerivAt K K' t) (he : ∀ i, HasDerivAt (e i) (e' i) t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : ∀ i, e' i + transport i + pressure i = forcing i + ν • lap i)
    (hp : ∀ i, ⟪K t (e i t), pressure i⟫_ℝ = 0)
    (ht : ∀ i, |⟪K t (e i t), transport i⟫_ℝ| ≤ B * ‖e i t‖ ^ 2)
    (hheat : ∀ i, ⟪K t (e i t), lap i⟫_ℝ ≤ C * ‖e i t‖ ^ 2) :
    deriv (fun s => √(familyEnergy (K s) (fun i => e i s) + δ ^ 2)) t ≤
      ((‖K'‖ + 2 * B + 2 * ν * C) / (2 * c ^ 2)) *
        √(familyEnergy (K t) (fun i => e i t) + δ ^ 2) +
      (‖K t‖ / c) * familyNorm forcing := by
  let v := fun i => e i t
  let E := √(familyEnergy (K t) v + δ ^ 2)
  have hcoer := familyEnergy_coercive (K t) v c hcoercive
  have hq : 0 ≤ familyEnergy (K t) v :=
    (mul_nonneg (sq_nonneg c) (familySquaredNorm_nonneg v)).trans hcoer
  have hE : 0 < E := sqrt_pos.mpr (by nlinarith)
  have hE2 : E ^ 2 = familyEnergy (K t) v + δ ^ 2 := sq_sqrt (by nlinarith)
  have hN2 := familyNorm_sq v
  have hN : familyNorm v ≤ E / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [familyNorm_nonneg v]
  have hN2bound : familySquaredNorm v ≤ E ^ 2 / c ^ 2 := by
    rw [← hN2, ← div_pow]
    exact pow_le_pow_left₀ (familyNorm_nonneg v) hN 2
  have hdiff := family_energy_hasDerivAt K e t ν K' e' transport pressure forcing lap hK he hsym
      heq hp
  have hroot := HasDerivAt.sqrt (hdiff.add_const (δ ^ 2))
    (by nlinarith : familyEnergy (K t) v + δ ^ 2 ≠ 0)
  rw [hroot.deriv]
  change _ / (2 * E) ≤ _
  apply (div_le_iff₀ (by positivity : 0 < 2 * E)).mpr
  have hb := family_energy_derivative_bound (K t) K' v transport forcing lap B C ν hB hν ht hheat
  have h1 := mul_le_mul_of_nonneg_left hN2bound
    (show 0 ≤ ‖K'‖ + 2 * B + 2 * ν * C by positivity)
  have h2 := mul_le_mul_of_nonneg_left hN
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg (K t)))
      (familyNorm_nonneg forcing))
  calc
    _ ≤ (‖K'‖ + 2 * B + 2 * ν * C) * familySquaredNorm v +
        2 * ‖K t‖ * familyNorm v * familyNorm forcing := hb
    _ ≤ (‖K'‖ + 2 * B + 2 * ν * C) * (E ^ 2 / c ^ 2) +
        2 * ‖K t‖ * (E / c) * familyNorm forcing := by nlinarith
    _ = _ := by dsimp [E, v]; field_simp

end EulerFiniteMetricEnergy
