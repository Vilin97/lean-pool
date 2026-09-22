/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.DoubledPhase

/-!
# Finite reciprocal multipliers

This file is the public face of the finite reciprocal multiplier development: it
carries the certificate built from an exact reciprocal orbit interpolation, the
two-by-two real obstruction that forces the doubled route, the status map of the
landscape, and the final Ky Fan estimates.  The three parts it imports supply the
orbit algebra, the Fourier interpolation, and the doubled phase realization.

Importing this module gives the whole development, as it did before the split.

The operator-theoretic theorem is factored through one simultaneous finite
interpolation certificate.  For fixed orthonormal coordinates and separated real
arrays `α` and `β`, the certificate supplies one finite family of left/right
unitaries whose orbit action realizes the reciprocal multiplier on every
coordinate matrix unit at once, with coefficient mass at most `π / 2`.  Once that
certificate is available, the passage to an arbitrary rectangular map is finite
linear algebra: expand the map in coordinate matrix units, use the entrywise
Sylvester equation, and recombine the common orbit action.

Literature bridge:

* `prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`
  reconstructs the separated-spectrum Fourier representation, the `pi / 2`
  provenance chain, the finite interpolation reduction, and the real-field
  descent that remains to be supplied.

## Provenance

*Split, not restated.*  Until 2026-07-29 this file held the whole development in
2887 lines — the largest module in the library, nearly 3x Tau Ceti's stated
1000-line limit for a new file (`ForTauCeti/README.md` §4).  The file was divided
it along its four mathematical seams into
`…ReciprocalMultiplier.{OrbitAction, Fourier, DoubledPhase}` and this
root.  **No statement, signature, proof, attribute or declaration name changed**;
the split is a file boundary plus the imports it forces, and the
`set_option linter.style.longFile 2900` it used to need is gone.

That file in turn was
`DavisKahan/FiniteDimensional/Sylvester/Internal/ReciprocalMultiplier.lean`
before the whole remaining sin-Θ closure moved into the staging layer;
Y3(b2) and Y3(b3) are what made that possible, since before them this import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

public section

namespace TauCeti

open TauCeti
open scoped InnerProductSpace BigOperators ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### The two-by-two real obstruction

The following theorems refute the exact *undoubled* real reciprocal orbit
interpolation at mass `π / 2`.  The frequency data is `α = (-1, 1)`,
`β = (0, 2)`, `δ = 1`, so the separation hypothesis holds with gap one, yet
any real certificate has coefficient mass at least `5 / 3 > π / 2`.

The reduction extracts, from the operator identity on each coordinate matrix
unit, the scalar identities `M i j = ∑ r, a r * u r i * v r j`, where
`u r i` and `v r j` are the diagonal matrix coefficients of the arbitrary
real orthogonal factors, hence bounded by one in absolute value.  Testing
the entrywise-reciprocal matrix `M = ![![-1, -1/3], ![1, -1]]` against the
functional `L X = (-X₀₀ - X₀₁ + X₁₀ - X₁₁) / 2`, whose value on every
rank-one atom `u vᵀ` with `‖u‖∞, ‖v‖∞ ≤ 1` is at most one while
`L M = 5 / 3`, forces the mass bound.  Because only diagonal matrix
coefficients of arbitrary orthogonal operators are used, no choice of
non-basis-diagonal real rotations can evade the argument. -/

/-- Left frequency array of the two-by-two obstruction: `(-1, 1)`. -/
def obstructionAlpha {n : ℕ} (i : Fin n) : ℝ :=
  if (i : ℕ) = 0 then -1 else 1

/-- Right frequency array of the two-by-two obstruction: `(0, 2)`. -/
def obstructionBeta {n : ℕ} (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then 0 else 2

/-- The obstruction data satisfies the unit separation hypothesis, so it is
admissible input for any claimed generic interpolation theorem. -/
theorem obstruction_gap {n : ℕ} (i j : Fin n) :
    1 ≤ |obstructionAlpha i - obstructionBeta j| := by
  unfold obstructionAlpha obstructionBeta
  by_cases hi : (i : ℕ) = 0 <;> by_cases hj : (j : ℕ) = 0
  · rw [ite_eq_left hi, ite_eq_left hj, le_abs]
    right
    norm_num
  · rw [ite_eq_left hi, ite_eq_right hj, le_abs]
    right
    norm_num
  · rw [ite_eq_right hi, ite_eq_left hj, le_abs]
    left
    norm_num
  · rw [ite_eq_right hi, ite_eq_right hj, le_abs]
    right
    norm_num

/-- **A unitary's diagonal matrix entry has modulus at most one.**  For a linear
isometry equivalence `W` and an orthonormal basis vector `e i`, Cauchy--Schwarz
and `‖W (e i)‖ = ‖e i‖ = 1` give `|⟪e i, W (e i)⟫| ≤ 1`.

Both diagonal families in `real_reciprocalOrbitInterpolation_mass_lower_bound`
are bounded by this one statement; it was written out twice there, once for each
side of the orbit action. -/
private theorem abs_real_inner_isometryEquiv_diag_le_one
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ G) (W : G ≃ₗᵢ[ℝ] G) (i : ι) :
    |⟪e i, W.toLinearMap (e i)⟫_ℝ| ≤ 1 := by
  have hnorm : ‖W.toLinearMap (e i)‖ = 1 := by
    -- names the application so `W.norm_map` applies to it directly.
    change ‖W (e i)‖ = 1
    rw [W.norm_map, e.norm_eq_one]
  calc
    |⟪e i, W.toLinearMap (e i)⟫_ℝ| ≤ ‖e i‖ * ‖W.toLinearMap (e i)‖ :=
      abs_real_inner_le_norm _ _
    _ = 1 := by rw [hnorm, e.norm_eq_one, one_mul]

/-- **Mass obstruction.**  Every undoubled real reciprocal orbit interpolation
certificate for the two-by-two obstruction data has coefficient mass at least
`5 / 3`. -/
theorem real_reciprocalOrbitInterpolation_mass_lower_bound
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    
    (e : OrthonormalBasis (Fin (Module.finrank ℝ G)) ℝ G)
    (h2 : Module.finrank ℝ G = 2)
    {mass : ℝ}
    (hcert : HasReciprocalOrbitInterpolation e e
      obstructionAlpha obstructionBeta 1 mass) :
    (5 : ℝ) / 3 ≤ mass := by
  classical
  obtain ⟨n, a, U, V, hinterp, hmass⟩ := hcert
  let u : Fin n → Fin (Module.finrank ℝ G) → ℝ := fun r i =>
    ⟪e i, (U r).toLinearMap (e i)⟫_ℝ
  let v : Fin n → Fin (Module.finrank ℝ G) → ℝ := fun r j =>
    ⟪e j, (V r).toLinearMap (e j)⟫_ℝ
  have hu_le (r : Fin n) (i : Fin (Module.finrank ℝ G)) : |u r i| ≤ 1 :=
    abs_real_inner_isometryEquiv_diag_le_one e (U r) i
  have hv_le (r : Fin n) (j : Fin (Module.finrank ℝ G)) : |v r j| ≤ 1 :=
    abs_real_inner_isometryEquiv_diag_le_one e (V r) j
  have hterm (r : Fin n) (i j : Fin (Module.finrank ℝ G)) :
      ⟪e i, (unitaryOrbitAction (U r) (V r))
        (basisMatrixUnit e e i j) (e j)⟫_ℝ = u r i * v r j := by
    -- states the goal as the inner-product identity the structure lemma expects.
    change ⟪e i, (U r).toLinearMap
      ((basisMatrixUnit e e i j) ((V r).toLinearMap (e j)))⟫_ℝ = _
    rw [basisMatrixUnit_apply, map_smul, real_inner_smul_right]
    exact mul_comm _ _
  have hscalar (i j : Fin (Module.finrank ℝ G)) :
      (1 : ℝ) = (obstructionAlpha i - obstructionBeta j) *
        ∑ r, a r * (u r i * v r j) := by
    have h := congrArg (fun T : G →ₗ[ℝ] G => ⟪e i, T (e j)⟫_ℝ) (hinterp i j)
    simp only [LinearMap.smul_apply, real_inner_smul_right, basisMatrixUnit_apply,
      e.inner_eq_one, one_smul, LinearMap.sum_apply, inner_sum,
      RCLike.ofReal_real_eq_id, id_eq] at h
    -- `simp only` reaches further than the old `rw` chain did: it pulls `a r` out of the
    -- inner product and collapses `1 * 1`, so `h` already *is* the first calc step.
    calc
      (1 : ℝ) = (obstructionAlpha i - obstructionBeta j) *
          ∑ r, a r * ⟪e i, (unitaryOrbitAction (U r) (V r))
            (basisMatrixUnit e e i j) (e j)⟫_ℝ := h
      _ = (obstructionAlpha i - obstructionBeta j) *
          ∑ r, a r * (u r i * v r j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        rw [hterm r i j]
  have hzero : (0 : ℕ) < Module.finrank ℝ G := by omega
  have hone : (1 : ℕ) < Module.finrank ℝ G := by omega
  set i₀ : Fin (Module.finrank ℝ G) := ⟨0, hzero⟩ with hi₀
  set i₁ : Fin (Module.finrank ℝ G) := ⟨1, hone⟩ with hi₁
  -- `hscalar` says `1 = g * S` with `g` the gap at that entry, so `S = 1 / g` at every
  -- entry; the four values below are that one identity at `g = -1, -3, 1, -1`.
  have hS (i j : Fin (Module.finrank ℝ G)) (g : ℝ)
      (hg : obstructionAlpha i - obstructionBeta j = g) (hg0 : g ≠ 0) :
      (∑ r, a r * (u r i * v r j)) = 1 / g := by
    have h := hscalar i j
    rw [hg] at h
    -- `eq_div_iff` rather than `field_simp`: the latter reassociates the summand to
    -- `a r * u r i * v r j`, which makes the sum a different atom from the one in `h`.
    rw [eq_div_iff hg0]
    linarith
  have hS00 : (∑ r, a r * (u r i₀ * v r i₀)) = -1 := by
    rw [hS i₀ i₀ (-1) (by simp [obstructionAlpha, obstructionBeta, hi₀]) (by norm_num)]
    norm_num
  have hS01 : (∑ r, a r * (u r i₀ * v r i₁)) = -(1 / 3) := by
    rw [hS i₀ i₁ (-3) (by simp [obstructionAlpha, obstructionBeta, hi₀, hi₁]; norm_num)
      (by norm_num)]
    norm_num
  have hS10 : (∑ r, a r * (u r i₁ * v r i₀)) = 1 := by
    rw [hS i₁ i₀ 1 (by simp [obstructionAlpha, obstructionBeta, hi₀, hi₁]) (by norm_num)]
    norm_num
  have hS11 : (∑ r, a r * (u r i₁ * v r i₁)) = -1 := by
    rw [hS i₁ i₁ (-1) (by simp [obstructionAlpha, obstructionBeta, hi₁]; norm_num)
      (by norm_num)]
    norm_num
  let ℓ : Fin n → ℝ := fun r =>
    (u r i₁ * (v r i₀ - v r i₁) - u r i₀ * (v r i₀ + v r i₁)) / 2
  have hLval : (∑ r, a r * ℓ r) = 5 / 3 := by
    have hsplit : (∑ r, a r * ℓ r) =
        ((∑ r, a r * (u r i₁ * v r i₀)) - (∑ r, a r * (u r i₁ * v r i₁)) -
          (∑ r, a r * (u r i₀ * v r i₀)) -
          (∑ r, a r * (u r i₀ * v r i₁))) / 2 := by
      rw [eq_div_iff (two_ne_zero (α := ℝ)), Finset.sum_mul,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      simp only [ℓ]
      ring
    rw [hsplit, hS00, hS01, hS10, hS11]
    norm_num
  have hℓ_le (r : Fin n) : |ℓ r| ≤ 1 := by
    obtain ⟨hv0l, hv0r⟩ := abs_le.mp (hv_le r i₀)
    obtain ⟨hv1l, hv1r⟩ := abs_le.mp (hv_le r i₁)
    have hsum2 : |v r i₀ - v r i₁| + |v r i₀ + v r i₁| ≤ 2 := by
      rcases abs_cases (v r i₀ - v r i₁) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases abs_cases (v r i₀ + v r i₁) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
          rw [e1, e2] <;> linarith
    have hnum : |u r i₁ * (v r i₀ - v r i₁) - u r i₀ * (v r i₀ + v r i₁)| ≤ 2 := by
      calc
        |u r i₁ * (v r i₀ - v r i₁) - u r i₀ * (v r i₀ + v r i₁)| ≤
            |u r i₁ * (v r i₀ - v r i₁)| + |u r i₀ * (v r i₀ + v r i₁)| :=
          abs_sub _ _
        _ = |u r i₁| * |v r i₀ - v r i₁| + |u r i₀| * |v r i₀ + v r i₁| := by
          rw [abs_mul, abs_mul]
        _ ≤ 1 * |v r i₀ - v r i₁| + 1 * |v r i₀ + v r i₁| := by
          gcongr
          · exact hu_le r i₁
          · exact hu_le r i₀
        _ = |v r i₀ - v r i₁| + |v r i₀ + v r i₁| := by ring
        _ ≤ 2 := hsum2
    simp only [ℓ]
    rw [abs_div, abs_two, div_le_one (by norm_num : (0 : ℝ) < 2)]
    exact hnum
  have habs : |∑ r, a r * ℓ r| ≤ ∑ r, |a r| := by
    calc
      |∑ r, a r * ℓ r| ≤ ∑ r, |a r * ℓ r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, |a r| := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hℓ_le r)
  rw [hLval] at habs
  have hmass' : (∑ r, |a r|) ≤ mass := by
    calc
      (∑ r, |a r|) = ∑ r, ‖a r‖ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Real.norm_eq_abs]
      _ ≤ mass := hmass
  calc
    (5 : ℝ) / 3 = |(5 : ℝ) / 3| := by norm_num
    _ ≤ ∑ r, |a r| := habs
    _ ≤ mass := hmass'

/-- **The exact undoubled real reciprocal orbit interpolation at mass `π / 2`
is refuted.**  The separation hypotheses are satisfiable (`obstruction_gap`
with `δ = 1 > 0`), yet no certificate of mass `π / 2` exists because
`π / 2 < 5 / 3`. -/
theorem not_real_reciprocalOrbitInterpolation_pi_div_two
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    
    (e : OrthonormalBasis (Fin (Module.finrank ℝ G)) ℝ G)
    (h2 : Module.finrank ℝ G = 2) :
    ¬ HasReciprocalOrbitInterpolation e e
      obstructionAlpha obstructionBeta 1 (Real.pi / 2) := by
  intro hcert
  have h53 := real_reciprocalOrbitInterpolation_mass_lower_bound e h2 hcert
  nlinarith [Real.pi_lt_d2]

/-- The concrete two-dimensional Euclidean orthonormal basis witnessing the
obstruction. -/
noncomputable def obstructionBasis :
    OrthonormalBasis (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))) ℝ
      (EuclideanSpace ℝ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).reindex
    (finCongr finrank_euclideanSpace_fin.symm)

/-- Fully concrete refutation on `EuclideanSpace ℝ (Fin 2)`: the hypotheses
of the previously conjectured generic undoubled interpolation are satisfied,
but its conclusion fails. -/
theorem not_hasReciprocalOrbitInterpolation_pi_div_two_euclidean :
    ¬ HasReciprocalOrbitInterpolation obstructionBasis obstructionBasis
      obstructionAlpha obstructionBeta 1 (Real.pi / 2) :=
  not_real_reciprocalOrbitInterpolation_pi_div_two obstructionBasis
    finrank_euclideanSpace_fin

/-! ### Status map of the reciprocal interpolation landscape

This note records, durably, which reciprocal-multiplier representations are
true, which are refuted, and which carry the sharp generic theory.  Any
future strengthening work should consult it before touching this seam.

1. **False: exact undoubled real reciprocal orbit interpolation at mass
   `π / 2`.**  A universal statement asserting
   `HasReciprocalOrbitInterpolation eF eE α β δ (Real.pi / 2)` for every
   separated frequency data over every `RCLike` field is refuted over `ℝ`
   already in dimension two: see
   `real_reciprocalOrbitInterpolation_mass_lower_bound` (mass at least
   `5 / 3`) and `not_hasReciprocalOrbitInterpolation_pi_div_two_euclidean`.
   The obstruction bounds the diagonal matrix coefficients of arbitrary
   orthogonal factors, so neither compactness/Carathéodory arguments nor
   more general real rotations can rescue the exact undoubled statement.
   No declaration asserting it may be reintroduced.

2. **True: complex phase interpolation.**  Over `ℂ`, diagonal phase
   unitaries realize every finite Fourier character, giving
   `hasReciprocalOrbitInterpolation_of_finiteFourierInterpolation` at mass
   `π / 2 + ε` for every positive `ε` from the Haagerup--Zsidó kernel.
   Whether exact complex attainment at `π / 2` holds is not needed by any
   current consumer and is left unexplored.

3. **True: doubled phase realization over every `RCLike` field.**  The
   rotation `[[cos θ, -sin θ], [sin θ, cos θ]]` with real entries embedded
   in `𝕜` realizes each phase on two orthogonal copies:
   `hasDoubledReciprocalOrbitInterpolation_of_finiteFourierInterpolation`.
   This is the correct generic replacement for item 1.

4. **True: sharp real and complex Ky Fan inequalities.**  Singular-value
   duplication on `orthogonalBlockSum` cancels the doubling, so the
   generic estimate `kyFan_reciprocalMultiplier_le` holds with the exact constant
   `π / 2` and no open obligation.  Inequalities need only the `π / 2 + ε`
   certificates, not exact endpoint attainment.

5. **Still possible: exact finite orbit certificates for a particular
   Sylvester solution.**  The obstruction refutes only the universal
   multiplier representation acting correctly on every matrix unit at once.
   Fan dominance and orbit convexity still produce the solution-specific
   exact certificates
   `sylvester_barycentricOrbitRepresentation_of_spectralDistance` and
   `sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance` at
   exact mass `π / 2`, which is weaker than item 1 and sufficient for all
   downstream finite theory. -/

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Convert the basis orientation used by the coordinate expansion into the
orientation used by the Sylvester coefficient equation. -/
private theorem basisFirst_coefficient_equation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F}
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜)
    (i : Fin (Module.finrank 𝕜 F))
    (j : Fin (Module.finrank 𝕜 E)) :
    (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
        ⟪eF i, X (eE j)⟫_𝕜 =
      ⟪eF i, C (eE j)⟫_𝕜 := by
  simpa only [map_mul, map_sub, RCLike.conj_ofReal, inner_conj_symm] using
    congrArg (starRingEnd 𝕜) (hcoeff i j)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- A simultaneous reciprocal orbit interpolation turns the entrywise
Sylvester relation into an exact finite two-sided unitary-orbit certificate. -/
theorem finiteUnitaryOrbitCertificate_of_reciprocalInterpolation
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F} {δ mass : ℝ}
    (hinterp : HasReciprocalOrbitInterpolation eF eE α β δ mass)
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜) :
    UnitarilyInvariantSeminorm.HasFiniteUnitaryOrbitCertificate
      mass (((δ : 𝕜)) • X) C := by
  classical
  rcases hinterp with ⟨n, a, U, V, hinterp, hmass⟩
  let S : (E →ₗ[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) :=
    ∑ r, a r • unitaryOrbitAction (U r) (V r)
  have hS_unit (i : Fin (Module.finrank 𝕜 F))
      (j : Fin (Module.finrank 𝕜 E)) :
      ((δ : 𝕜)) • basisMatrixUnit eF eE i j =
        ((((α i - β j : ℝ) : 𝕜)) •
          S (basisMatrixUnit eF eE i j)) := by
    exact hinterp i j
  have hcoeff' (i : Fin (Module.finrank 𝕜 F))
      (j : Fin (Module.finrank 𝕜 E)) :
      ((((α i - β j : ℝ) : 𝕜)) *
          ⟪eF i, X (eE j)⟫_𝕜) =
        ⟪eF i, C (eE j)⟫_𝕜 := by
    simpa only [RCLike.ofReal_sub] using
      basisFirst_coefficient_equation eF eE α β hcoeff i j
  refine ⟨n, a, U, V, ?_, hmass⟩
  have hX := sum_basisMatrixUnit eF eE X
  have hC := sum_basisMatrixUnit eF eE C
  calc
    ((δ : 𝕜)) • X =
        ((δ : 𝕜)) •
          (∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
            basisMatrixUnit eF eE i j) := by rw [← hX]
    _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
          (((δ : 𝕜)) • basisMatrixUnit eF eE i j) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul, smul_smul, mul_comm]
    _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_𝕜 •
          (((((α i - β j : ℝ) : 𝕜)) •
            S (basisMatrixUnit eF eE i j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hS_unit i j]
    _ = ∑ i, ∑ j, ⟪eF i, C (eE j)⟫_𝕜 •
          S (basisMatrixUnit eF eE i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hcoeff' i j]
      rw [smul_smul, mul_comm]
    _ = S (∑ i, ∑ j, ⟪eF i, C (eE j)⟫_𝕜 •
          basisMatrixUnit eF eE i j) := by
      simp only [map_sum, map_smul]
    _ = S C := by rw [← hC]
    _ = ∑ r, a r •
        ((U r).toLinearMap ∘ₗ C ∘ₗ (V r).toLinearMap) := by
      simp only [S, LinearMap.sum_apply, LinearMap.smul_apply,
        unitaryOrbitAction_apply]

/-- A doubled-real reciprocal interpolation recombines from matrix units into
an exact finite orthogonal-orbit certificate for arbitrary real maps. -/
theorem finiteUnitaryOrbitCertificate_orthogonalBlockSum_of_reciprocalInterpolation
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
    
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR]
    
    (eF : OrthonormalBasis (Fin (Module.finrank ℝ FR)) ℝ FR)
    (eE : OrthonormalBasis (Fin (Module.finrank ℝ ER)) ℝ ER)
    (alpha : Fin (Module.finrank ℝ FR) → ℝ)
    (beta : Fin (Module.finrank ℝ ER) → ℝ)
    {X C : ER →ₗ[ℝ] FR} {delta mass : ℝ}
    (hinterp : HasDoubledRealReciprocalOrbitInterpolation
      eF eE alpha beta delta mass)
    (hcoeff : ∀ i j,
      (alpha i - beta j) * ⟪X (eE j), eF i⟫_ℝ =
        ⟪C (eE j), eF i⟫_ℝ) :
    UnitarilyInvariantSeminorm.HasFiniteUnitaryOrbitCertificate
      mass
      (delta • UnitarilyInvariantSeminorm.orthogonalBlockSum X X)
      (UnitarilyInvariantSeminorm.orthogonalBlockSum C C) := by
  classical
  rcases hinterp with ⟨q, w, U, V, hinterp, hmass⟩
  let S :
      (WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR)) →ₗ[ℝ]
        (WithLp 2 (ER × ER) →ₗ[ℝ] WithLp 2 (FR × FR)) :=
    ∑ r, w r • unitaryOrbitAction (U r) (V r)
  have hunit (i : Fin (Module.finrank ℝ FR))
      (j : Fin (Module.finrank ℝ ER)) :
      delta • UnitarilyInvariantSeminorm.orthogonalBlockSum
          (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) =
        (alpha i - beta j) •
          S (UnitarilyInvariantSeminorm.orthogonalBlockSum
            (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
    exact hinterp i j
  have hcoeff' (i : Fin (Module.finrank ℝ FR))
      (j : Fin (Module.finrank ℝ ER)) :
      (alpha i - beta j) * ⟪eF i, X (eE j)⟫_ℝ =
        ⟪eF i, C (eE j)⟫_ℝ := by
    simpa only [real_inner_comm] using hcoeff i j
  let blockDiagonal := UnitarilyInvariantSeminorm.orthogonalBlockSumDiagonal
    (𝕜 := ℝ) (E₁ := ER) (F₁ := FR)
  have hblock (A : ER →ₗ[ℝ] FR) :
      UnitarilyInvariantSeminorm.orthogonalBlockSum A A =
        ∑ i, ∑ j, ⟪eF i, A (eE j)⟫_ℝ •
          UnitarilyInvariantSeminorm.orthogonalBlockSum
            (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change blockDiagonal A = _
    conv_lhs => rw [sum_basisMatrixUnit eF eE A]
    simp only [map_sum, map_smul, blockDiagonal]
    rfl
  refine ⟨q, w, U, V, ?_, ?_⟩
  · calc
      delta • UnitarilyInvariantSeminorm.orthogonalBlockSum X X =
          delta • ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_ℝ •
            UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j) := by
        rw [hblock X]
      _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_ℝ •
            (delta • UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul, smul_smul, mul_comm]
      _ = ∑ i, ∑ j, ⟪eF i, X (eE j)⟫_ℝ •
            ((alpha i - beta j) •
              S (UnitarilyInvariantSeminorm.orthogonalBlockSum
                (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hunit i j]
      _ = ∑ i, ∑ j, ⟪eF i, C (eE j)⟫_ℝ •
            S (UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [← hcoeff' i j, smul_smul, mul_comm]
      _ = S (∑ i, ∑ j, ⟪eF i, C (eE j)⟫_ℝ •
            UnitarilyInvariantSeminorm.orthogonalBlockSum
              (basisMatrixUnit eF eE i j) (basisMatrixUnit eF eE i j)) := by
        simp only [map_sum, map_smul]
      _ = S (UnitarilyInvariantSeminorm.orthogonalBlockSum C C) := by
        rw [← hblock C]
      _ = ∑ r, w r • ((U r).toLinearMap ∘ₗ
          UnitarilyInvariantSeminorm.orthogonalBlockSum C C ∘ₗ
            (V r).toLinearMap) := by
        simp only [S, LinearMap.sum_apply, LinearMap.smul_apply,
          unitaryOrbitAction_apply]
  · simpa only [Real.norm_eq_abs] using hmass

/-- **Every finite reciprocal multiplier with gap `δ` satisfies the sharp
simultaneous Ky Fan prefix estimate**, over every `RCLike` scalar field.

The proof is unconditional: the explicit Haagerup--Zsidó kernel supplies
finite Fourier interpolations of mass `π / 2 + ε`, the generic doubled phase
rotations realize them on two orthogonal copies of the spaces, and
singular-value duplication removes the doubling at the level of every Ky Fan
prefix.  No exact undoubled orbit certificate is used; that statement is
refuted over `ℝ` by the two-by-two obstruction above. -/
theorem kyFan_reciprocalMultiplier_le
    (eF : OrthonormalBasis (Fin (Module.finrank 𝕜 F)) 𝕜 F)
    (eE : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E)
    (α : Fin (Module.finrank 𝕜 F) → ℝ)
    (β : Fin (Module.finrank 𝕜 E) → ℝ)
    {X C : E →ₗ[𝕜] F} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i j, δ ≤ |α i - β j|)
    (hcoeff : ∀ i j,
      (((α i : ℝ) : 𝕜) - ((β j : ℝ) : 𝕜)) *
          ⟪X (eE j), eF i⟫_𝕜 =
        ⟪C (eE j), eF i⟫_𝕜)
    (k : ℕ) :
    δ * TauCeti.kyFanSum k X ≤
      (Real.pi / 2) *
        TauCeti.kyFanSum k C :=
  kyFan_reciprocalMultiplier_le_of_integrableKernel eF eE α β hδ hgap
    hasIntegrableReciprocalFourierKernel_pi_div_two hcoeff k

end TauCeti
