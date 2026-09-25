/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
public import LeanPool.Stafford38.Stafford38.Geometry.RetractionSpecialization


/-!
# Tangency of the formal-arc velocity

If a power-series arc annihilates an affine ideal coefficientwise, its formal
derivative and the residues of arbitrary derivation directions are Zariski
tangent vectors at the constant point.  The result is deliberately
independent of any projective closure or normalization: it consumes an actual
power-series arc and produces actual tangent data for the scalar-extended
base ideal.

The file does not construct the arc or identify its tangent data with a
projective component.  Those chart, normalization, frame-independence, and
dimension arguments remain separate geometric obligations.
-/

@[expose] public section

namespace Stafford38.Geometry.PowerSeriesArcTangency

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u

variable {k : Type u} [Field k]

/-! ## The formal chain rule -/

/-- Chain rule for a derivation of a field-valued polynomial evaluation. -/
theorem derivation_eval₂
    {S : Type*} [CommSemiring S] [Algebra k S]
    (D : Derivation k S S)
    {m : ℕ} (f : MvPolynomial (Fin m) k)
    (q : Fin m → S) :
    D (MvPolynomial.eval₂ (algebraMap k S) q f) =
      ∑ i, MvPolynomial.eval₂ (algebraMap k S) q
          (MvPolynomial.pderiv i f) * D (q i) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp []
  | add f g hf hg =>
      simp only [MvPolynomial.eval₂_add, D.map_add, map_add, hf, hg,
        Finset.sum_add_distrib, add_mul]
  | mul_X f i hf =>
      simp only [MvPolynomial.eval₂_mul, D.leibniz, smul_eq_mul, hf,
        MvPolynomial.pderiv_mul,  add_mul, Finset.sum_add_distrib,
        MvPolynomial.eval₂_add, MvPolynomial.eval₂_X,
         MvPolynomial.pderiv_X,
        Pi.single_apply]
      simp? [Finset.mul_sum,   mul_comm,
        mul_left_comm, mul_assoc]
      have hsecond :
          (∑ x : Fin m,
            MvPolynomial.eval₂ (algebraMap k S) q f *
              (MvPolynomial.eval₂ (algebraMap k S) q
                (if i = x then 1 else 0) * D (q x))) =
            MvPolynomial.eval₂ (algebraMap k S) q f * D (q i) := by
        classical
        rw [← Finset.mul_sum]
        congr 1
        simpa using
          (Finset.sum_eq_single (s := Finset.univ)
            (f := fun x : Fin m ↦
              MvPolynomial.eval₂ (algebraMap k S)
                  q (if i = x then 1 else 0) * D (q x)) i
            (by
              intro b hb hbi
              simp [ Ne.symm hbi])
            (by
              intro hi
              exact (hi (Finset.mem_univ i)).elim))
      rw [hsecond]
      ring

/-! ## Derivation directions of extended ideal loci -/

/-- A derivation of an evaluation point is tangent to the scalar extension of
an ideal that vanishes at that point.  This is the coefficient-direction
analogue of the power-series arc theorem below; it is stated for an arbitrary
field extension and an arbitrary derivation, so no chart or completeness
hypothesis is hidden in the result. -/
theorem derivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
    {S : Type*} [Field S] [Algebra k S]
    (D : Derivation k S S)
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → S)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k S) q f = 0) :
    (fun i ↦ D (q i)) ∈
      zariskiTangentSpace q
        (I.map (MvPolynomial.map (algebraMap k S))) := by
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator]
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨g, rfl⟩
      have hmap :
          ∀ h : MvPolynomial (Fin m) S,
            h ∈ I.map (MvPolynomial.map (algebraMap k S)) →
              MvPolynomial.eval q h = 0 ∧
                differentialCovector q h (fun i ↦ D (q i)) = 0 := by
        intro h hh
        rw [Ideal.map] at hh
        induction hh using Submodule.span_induction with
        | mem h hh =>
            rcases hh with ⟨g, hg, rfl⟩
            constructor
            · rw [MvPolynomial.eval_map]
              exact hq g hg
            · have hderiv := derivation_eval₂ D g q
              rw [hq g hg] at hderiv
              simpa [differentialCovector, differentialAt,
                MvPolynomial.pderiv_map, MvPolynomial.eval_map] using
                hderiv.symm
        | zero =>
            simp [differentialCovector, differentialAt]
        | add h₁ h₂ hh₁ hh₂ ih₁ ih₂ =>
            constructor
            · rw [MvPolynomial.eval_add, ih₁.1, ih₂.1, add_zero]
            · have hi := congrArg₂ (· + ·) ih₁.2 ih₂.2
              change ∑ i, MvPolynomial.eval q
                  (MvPolynomial.pderiv i (h₁ + h₂)) * D (q i) = 0
              simp only [map_add,  add_mul]
              rw [Finset.sum_add_distrib]
              simpa [differentialCovector, differentialAt] using hi
        | smul a h hh ih =>
            constructor
            · simp [smul_eq_mul, ih.1]
            · have ihD :
                  ∑ i, MvPolynomial.eval q
                      (MvPolynomial.pderiv i h) * D (q i) = 0 := by
                simpa [differentialCovector, differentialAt] using ih.2
              have hprod :
                  differentialCovector q (a * h) (fun i ↦ D (q i)) =
                    MvPolynomial.eval q h *
                        differentialCovector q a (fun i ↦ D (q i)) +
                      MvPolynomial.eval q a *
                  differentialCovector q h (fun i ↦ D (q i)) := by
                simp only [differentialCovector_apply, differentialAt,
                  MvPolynomial.pderiv_mul,
                  MvPolynomial.eval_add, MvPolynomial.eval_mul, add_mul,
                  Finset.sum_add_distrib]
                simp [Finset.mul_sum,   mul_comm,
                  mul_left_comm]
              rw [show (a • h : MvPolynomial (Fin m) S) = a * h by rfl]
              rw [hprod]
              simp [ih.1, ih.2]
      exact hmap g.1 g.2 |>.2
  | zero => simp
  | add φ ψ hφ hψ ihφ ihψ =>
      simp [ihφ, ihψ]
  | smul a φ hφ ihφ =>
      simp [ihφ]

/-- Constant-term evaluation commutes with evaluating a base-field
polynomial in a power-series point. -/
theorem constantCoeff_eval₂
    {K : Type u} [Field K] [Algebra k K]
    {m : ℕ} (f : MvPolynomial (Fin m) k)
    (q : Fin m → PowerSeries K) :
    PowerSeries.constantCoeff
        (MvPolynomial.eval₂ (algebraMap k (PowerSeries K)) q f) =
      MvPolynomial.eval₂ (algebraMap k K)
        (fun i ↦ PowerSeries.constantCoeff (q i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂_C]
      rw [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf]

/-- The residue of an arbitrary derivation direction on an annihilating
power-series arc is tangent to the scalar-extended base ideal.  The
derivation need not preserve the coefficient field: the ideal-span argument
handles the coefficient terms because every base equation already vanishes
along the arc. -/
theorem residueDerivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
    {K : Type u} [Field K] [Algebra k K]
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries K)
    (D : Derivation k (PowerSeries K) (PowerSeries K))
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries K)) q f = 0) :
    (fun i ↦ PowerSeries.constantCoeff (D (q i))) ∈
      zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i))
        (I.map (MvPolynomial.map (algebraMap k K))) := by
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator]
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨g, rfl⟩
      have hmap :
          ∀ h : MvPolynomial (Fin m) K,
            h ∈ I.map (MvPolynomial.map (algebraMap k K)) →
              MvPolynomial.eval
                  (fun i ↦ PowerSeries.constantCoeff (q i)) h = 0 ∧
                differentialCovector
                    (fun i ↦ PowerSeries.constantCoeff (q i)) h
                    (fun i ↦ PowerSeries.constantCoeff (D (q i))) = 0 := by
        intro h hh
        rw [Ideal.map] at hh
        induction hh using Submodule.span_induction with
        | mem h hh =>
            rcases hh with ⟨g, hg, rfl⟩
            have hzero := congrArg (PowerSeries.constantCoeff) (hq g hg)
            rw [constantCoeff_eval₂] at hzero
            constructor
            · rw [MvPolynomial.eval_map]
              exact hzero
            · have hderiv := derivation_eval₂ D g q
              rw [hq g hg] at hderiv
              have hconst :=
                congrArg (PowerSeries.constantCoeff) hderiv.symm
              simpa [differentialCovector, differentialAt,
                MvPolynomial.pderiv_map, MvPolynomial.eval_map,
                constantCoeff_eval₂] using hconst
        | zero =>
            simp [differentialCovector, differentialAt]
        | add h₁ h₂ hh₁ hh₂ ih₁ ih₂ =>
            constructor
            · rw [MvPolynomial.eval_add, ih₁.1, ih₂.1, add_zero]
            · have hi := congrArg₂ (· + ·) ih₁.2 ih₂.2
              change ∑ i, MvPolynomial.eval
                  (fun i ↦ PowerSeries.constantCoeff (q i))
                  (MvPolynomial.pderiv i (h₁ + h₂)) *
                    PowerSeries.constantCoeff (D (q i)) = 0
              simp only [map_add,  add_mul]
              rw [Finset.sum_add_distrib]
              simpa [differentialCovector, differentialAt] using hi
        | smul a h hh ih =>
            constructor
            · simp [smul_eq_mul, ih.1]
            · have hprod :
                  differentialCovector
                      (fun i ↦ PowerSeries.constantCoeff (q i))
                      (a * h)
                      (fun i ↦ PowerSeries.constantCoeff (D (q i))) =
                    MvPolynomial.eval
                        (fun i ↦ PowerSeries.constantCoeff (q i)) h *
                        differentialCovector
                          (fun i ↦ PowerSeries.constantCoeff (q i)) a
                          (fun i ↦ PowerSeries.constantCoeff (D (q i))) +
                      MvPolynomial.eval
                          (fun i ↦ PowerSeries.constantCoeff (q i)) a *
                        differentialCovector
                          (fun i ↦ PowerSeries.constantCoeff (q i)) h
                          (fun i ↦ PowerSeries.constantCoeff (D (q i))) := by
                simp only [differentialCovector_apply, differentialAt,
                  MvPolynomial.pderiv_mul, MvPolynomial.eval_add,
                  MvPolynomial.eval_mul, add_mul, Finset.sum_add_distrib]
                simp [Finset.mul_sum,  mul_assoc, mul_comm]
              rw [show (a • h : MvPolynomial (Fin m) K) = a * h by rfl]
              rw [hprod]
              simp [ih.1, ih.2]
      exact hmap g.1 g.2 |>.2
  | zero => simp
  | add φ ψ hφ hψ ihφ ihψ =>
      simp [ihφ, ihψ]
  | smul a φ hφ ihφ =>
      simp [ihφ]

/-- The uniformizer member of the power-series frame is tangent after
residue specialization whenever the arc annihilates the base ideal. -/
theorem residueFrameVector_uniformizer_mem_zariskiTangentSpace_of_eval₂_eq_zero
    {K : Type u} [Field K] [Algebra k K]
    {m κ : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries K)
    (D : Fin κ → Derivation k K K)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries K)) q f = 0) :
    residueFrameVector (k := k) (K := K) q D none ∈
      zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i))
        (I.map (MvPolynomial.map (algebraMap k K))) := by
  have hD :=
    residueDerivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
      (k := k) (K := K) I q
        (uniformizerDerivation (k := k) (K := K)) hq
  change (fun i ↦ PowerSeries.constantCoeff
      (uniformizerDerivation (k := k) (K := K) (q i))) ∈ _
  exact hD

/-- Every coefficient-field derivation direction of an annihilating
power-series arc is tangent at its constant point to the scalar-extended
base ideal. -/
theorem residueFrameVector_coefficient_mem_zariskiTangentSpace_of_eval₂_eq_zero
    {K : Type u} [Field K] [Algebra k K]
    {m κ : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries K)
    (D : Fin κ → Derivation k K K)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries K)) q f = 0)
    (j : Fin κ) :
    residueFrameVector (k := k) (K := K) q D (some j) ∈
      zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i))
        (I.map (MvPolynomial.map (algebraMap k K))) := by
  have hD :=
    residueDerivationVector_mem_zariskiTangentSpace_of_eval₂_eq_zero
      (k := k) (K := K) I q
        (coefficientwiseDerivation (D j)) hq
  change (fun i ↦ PowerSeries.constantCoeff
      (coefficientwiseDerivation (D j) (q i))) ∈ _
  exact hD

/-- Formal chain rule for evaluating a polynomial along a power-series arc. -/
theorem derivative_eval_map
    {m : ℕ} (f : MvPolynomial (Fin m) k)
    (q : Fin m → PowerSeries k) :
    PowerSeries.derivative
        (MvPolynomial.eval q (MvPolynomial.map (PowerSeries.C) f)) =
      ∑ i, MvPolynomial.eval q
          (MvPolynomial.map (PowerSeries.C) (MvPolynomial.pderiv i f)) *
        PowerSeries.derivative (q i) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
      simp only [map_add,
        hf, hg, Finset.sum_add_distrib, add_mul]
  | mul_X f i hf =>
      simp only [map_mul,  Derivation.leibniz,
        smul_eq_mul, map_add, hf,  add_mul,
        Finset.sum_add_distrib]
      simp [Pi.single_apply, Finset.mul_sum, mul_comm,
        mul_assoc]

/-! ## Tangency at the closed point -/

/-- The velocity of a power-series arc at its constant term. -/
def arcVelocity {m : ℕ} (q : Fin m → PowerSeries k) : Fin m → k :=
  fun i ↦ PowerSeries.constantCoeff (PowerSeries.derivative (q i))

@[simp]
theorem arcVelocity_eq_residueFrameVector
    {m κ : ℕ} (q : Fin m → PowerSeries k)
    (D : Fin κ → Derivation k k k) :
    arcVelocity q = residueFrameVector q D none :=
  rfl

/-- The formal-arc velocity annihilates the differential of every polynomial
that vanishes identically along the arc. -/
theorem differentialCovector_arcVelocity_eq_zero_of_eval_eq_zero
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries k)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval q (MvPolynomial.map (PowerSeries.C) f) = 0) :
    ∀ f ∈ I,
      differentialCovector (fun i ↦ PowerSeries.constantCoeff (q i)) f
        (arcVelocity q) = 0 := by
  intro f hf
  have hderiv := derivative_eval_map f q
  rw [hq f hf, map_zero] at hderiv
  have hconst :
      (0 : k) =
        ∑ i, PowerSeries.constantCoeff
            (MvPolynomial.eval q
              (MvPolynomial.map (PowerSeries.C)
                (MvPolynomial.pderiv i f))) *
          PowerSeries.constantCoeff
            (PowerSeries.derivative (q i)) := by
    simpa only [map_zero, map_sum, map_mul] using
      congrArg (PowerSeries.constantCoeff) hderiv
  simp_rw [residue_eval_map] at hconst
  have hres : residueColumn q =
      (fun i ↦ PowerSeries.constantCoeff (q i)) := rfl
  rw [hres] at hconst
  simpa [differentialCovector, differentialAt, arcVelocity,
    ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_mul, Finset.sum_apply, Finset.sum_mul] using hconst.symm

/-- An actual power-series arc supplies the uniformizer tangent vector needed
by the higher-dimensional conormal consumer. -/
theorem arcVelocity_mem_zariskiTangentSpace_of_eval_eq_zero
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries k)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval q (MvPolynomial.map (PowerSeries.C) f) = 0) :
    arcVelocity q ∈
      zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i)) I := by
  rw [zariskiTangentSpace, Submodule.mem_dualCoannihilator]
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨g, rfl⟩
      exact differentialCovector_arcVelocity_eq_zero_of_eval_eq_zero I q hq
        g.1 g.2
  | zero => simp
  | add φ ψ hφ hψ ihφ ihψ =>
      simp [ihφ, ihψ]
  | smul a φ hφ ihφ =>
      simp [ihφ]

@[simp]
theorem residueFrameVector_none_mem_zariskiTangentSpace_of_eval_eq_zero
    {m κ : ℕ} (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries k) (D : Fin κ → Derivation k k k)
    (hq : ∀ f ∈ I,
      MvPolynomial.eval q (MvPolynomial.map (PowerSeries.C) f) = 0) :
    residueFrameVector q D none ∈
      zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i)) I := by
  rw [← arcVelocity_eq_residueFrameVector q D]
  exact arcVelocity_mem_zariskiTangentSpace_of_eval_eq_zero I q hq


end

end Stafford38.Geometry.PowerSeriesArcTangency
