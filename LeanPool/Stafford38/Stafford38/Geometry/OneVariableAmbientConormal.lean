/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalBaseVariety
public import LeanPool.Stafford38.Stafford38.Geometry.OneVariablePrimeConormal
public import Mathlib.FieldTheory.Perfect


/-!
# Ambient rank-one conormal production

In one base variable, passing from a radical ambient ideal to one of its
prime components loses the direction needed for conormal containment: if
`I ≤ P`, then the equation-conormal space of `I` is contained in that of `P`,
not conversely.  This file avoids that invalid transfer.

Instead, the radical ambient ideal is principal after identifying the
one-variable multivariate polynomial ring with `k[X]`.  Its nonzero generator
is squarefree.  At every zero, separability therefore makes the derivative
nonzero, so the ambient equation itself spans the unique cotangent direction.
This produces the Laurent conormal axis for the ambient ideal directly.
-/

@[expose] public section

namespace Stafford38.Geometry.OneVariableAmbientConormal

open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

private def finOnePolynomialEquiv (k : Type u) [Field k] :
    MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
  (MvPolynomial.renameEquiv k (Equiv.equivPUnit.{1, 1} (Fin 1))).trans
    (MvPolynomial.uniqueAlgEquiv k PUnit.{1})

private theorem finOnePolynomialEquiv_eval
    {k : Type u} [Field k] (f : MvPolynomial (Fin 1) k) (y : Fin 1 → k) :
    Polynomial.eval (y 0) (finOnePolynomialEquiv k f) =
      MvPolynomial.eval y f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [finOnePolynomialEquiv]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    fin_cases i
    simp only [map_mul,
       Polynomial.eval_mul]
    rw [hp]
    simp [finOnePolynomialEquiv]

private theorem finOnePolynomialEquiv_pderiv
    {k : Type u} [Field k] (f : MvPolynomial (Fin 1) k) :
    finOnePolynomialEquiv k (MvPolynomial.pderiv (0 : Fin 1) f) =
      (finOnePolynomialEquiv k f).derivative := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [finOnePolynomialEquiv]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    fin_cases i
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, map_add, map_mul, Polynomial.derivative_mul]
    rw [hp]
    simp [finOnePolynomialEquiv]

/-- A radical ambient ideal in one variable which avoids the origin has, at
each supplied zero, an ambient equation with nonzero differential.  The
equation is the pullback of a principal generator after identifying the ring
with `k[X]`. -/
theorem exists_ambientEquation_differential_ne_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin 1) k))
    (hIrad : I.IsRadical)
    (y : Fin 1 → k)
    (hy : ∀ f ∈ I, MvPolynomial.eval y f = 0)
    (havoid : ∀ z : Fin 1 → k,
      (∀ f ∈ I, MvPolynomial.eval z f = 0) → z 0 ≠ 0) :
    ∃ f ∈ I, differentialAt y f 0 ≠ 0 := by
  let e := finOnePolynomialEquiv k
  let Q : Ideal (Polynomial k) := I.map e
  have hIne : I ≠ ⊥ := by
    intro hI
    have hzero : ∀ f ∈ I,
        MvPolynomial.eval (fun _ : Fin 1 ↦ (0 : k)) f = 0 := by
      intro f hf
      have hf0 : f = 0 := by
        rw [hI] at hf
        simpa using hf
      simp [hf0]
    exact (havoid (fun _ ↦ 0) hzero) rfl
  have hQrad : Q.IsRadical := by
    have hQeq : Q = I.comap e.symm := by
      ext q
      constructor
      · intro hq
        obtain ⟨f, hf, hef⟩ :=
          (Ideal.mem_map_iff_of_surjective e e.surjective).mp hq
        change e.symm q ∈ I
        simpa [← hef] using hf
      · intro hq
        apply (Ideal.mem_map_iff_of_surjective e e.surjective).mpr
        exact ⟨e.symm q, hq, by simp⟩
    rw [hQeq]
    exact hIrad.comap e.symm
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hIne
    exact (Ideal.map_eq_bot_iff_of_injective e.injective).mp hQ
  let g : Polynomial k := Submodule.IsPrincipal.generator Q
  have hgQ : g ∈ Q := Submodule.IsPrincipal.generator_mem Q
  have hg0 : g ≠ 0 := by
    intro hg
    apply hQne
    rw [← Ideal.span_singleton_generator Q]
    have hgenerator : Submodule.IsPrincipal.generator Q = 0 := by
      simpa [g] using hg
    rw [hgenerator, Ideal.span_singleton_eq_bot]
  have hgrad : IsRadical g := by
    rw [isRadical_iff_span_singleton]
    have hspan : Ideal.span ({g} : Set (Polynomial k)) = Q := by
      simp [g]
    rw [hspan]
    exact hQrad
  have hgsq : Squarefree g :=
    (isRadical_iff_squarefree_of_ne_zero hg0).mp hgrad
  have hgsep : g.Separable :=
    PerfectField.separable_iff_squarefree.mpr hgsq
  let f : MvPolynomial (Fin 1) k := e.symm g
  have hfI : f ∈ I := by
    have : e.symm g ∈ I := by
      obtain ⟨f', hf', hef'⟩ :=
        (Ideal.mem_map_iff_of_surjective e e.surjective).mp hgQ
      simpa [← hef'] using hf'
    exact this
  have hgeval : Polynomial.eval (y 0) g = 0 := by
    rw [show g = e f by simp [f, e]]
    exact (finOnePolynomialEquiv_eval f y).trans (hy f hfI)
  have hgderiv : Polynomial.eval (y 0) g.derivative ≠ 0 :=
    hgsep.eval₂_derivative_ne_zero (RingHom.id k) (by simpa using hgeval)
  refine ⟨f, hfI, ?_⟩
  change MvPolynomial.eval y (MvPolynomial.pderiv 0 f) ≠ 0
  rw [← finOnePolynomialEquiv_eval (MvPolynomial.pderiv 0 f) y,
    finOnePolynomialEquiv_pderiv]
  simpa [f, e] using hgderiv

/-- In rank one, one ambient equation with nonzero differential spans the
entire cotangent line. -/
theorem pureAxis_mem_affineConormalSpace_of_differential_ne_zero
    {k : Type u} [Field k]
    (I : Ideal (MvPolynomial (Fin 1) k))
    (y : Fin 1 → k) (f : MvPolynomial (Fin 1) k)
    (hf : f ∈ I) (hdf : differentialAt y f 0 ≠ 0) :
    coordinateCovector (fun _ : Fin 1 ↦ 1) ∈ affineConormalSpace y I := by
  rw [affineConormalSpace_eq_equationCovectorSpan]
  have hgenerator : differentialCovector y f ∈ equationCovectorSpan y I := by
    apply Submodule.subset_span
    exact ⟨⟨f, hf⟩, rfl⟩
  have hscaled := (equationCovectorSpan y I).smul_mem (differentialAt y f 0)⁻¹ hgenerator
  convert hscaled using 1
  apply LinearMap.ext
  intro v
  simp [differentialCovector, coordinateCovector, hdf]

/-- A radical ambient rank-one ideal with a zero and with origin avoidance
produces the exact Laurent conormal axis required by the terminal projected
consumer.  No prime-component conormal is transferred to the ambient ideal. -/
theorem exists_laurentConormalAxis_of_radical_ambient_axis_avoidance
    {k : Type u} [Field k] [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin 1) k))
    (hIrad : I.IsRadical)
    (hexists : ∃ y : Fin 1 → k,
      ∀ f ∈ I, MvPolynomial.eval y f = 0)
    (havoid : ∀ y : Fin 1 → k,
      (∀ f ∈ I, MvPolynomial.eval y f = 0) → y 0 ≠ 0) :
    ∃ (yL : Fin 1 → LaurentSeries k)
      (xi : Fin 1 → PowerSeries k),
      Sum.elim yL
          (fun j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi j)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin 1))) ∧
      residueColumn xi = (fun _ : Fin 1 ↦ 1) := by
  obtain ⟨y, hy⟩ := hexists
  obtain ⟨f, hf, hdf⟩ :=
    exists_ambientEquation_differential_ne_zero I hIrad y hy havoid
  let yL : Fin 1 → LaurentSeries k :=
    fun j ↦ algebraMap k (LaurentSeries k) (y j)
  let xi : Fin 1 → PowerSeries k := fun _ ↦ PowerSeries.C 1
  let IL := I.map
    (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin 1))
  have hyL : ∀ g ∈ IL, MvPolynomial.eval yL g = 0 := by
    rw [show (∀ g ∈ IL, MvPolynomial.eval yL g = 0) ↔
        yL ∈ MvPolynomial.zeroLocus (LaurentSeries k) IL by rfl]
    rw [mem_zeroLocus_map_iff]
    intro g hg
    change MvPolynomial.eval₂ (algebraMap k (LaurentSeries k))
      ((algebraMap k (LaurentSeries k)) ∘ y) g = 0
    rw [← MvPolynomial.eval₂_comp, hy g hg, map_zero]
  have hfIL : scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin 1) f ∈ IL :=
    Ideal.mem_map_of_mem _ hf
  have hdfL : differentialAt yL
      (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin 1) f) 0 ≠ 0 := by
    rw [differentialAt_scalarPolynomialMap]
    change MvPolynomial.eval₂ (algebraMap k (LaurentSeries k))
      ((algebraMap k (LaurentSeries k)) ∘ y)
        (MvPolynomial.pderiv 0 f) ≠ 0
    rw [← MvPolynomial.eval₂_comp]
    simpa [differentialAt] using
      (algebraMap k (LaurentSeries k)).injective.ne hdf
  have haxisL : coordinateCovector (fun _ : Fin 1 ↦ (1 : LaurentSeries k)) ∈
      affineConormalSpace yL IL :=
    pureAxis_mem_affineConormalSpace_of_differential_ne_zero IL yL _ hfIL hdfL
  refine ⟨yL, xi, ?_, ?_⟩
  · refine ⟨hyL, ?_⟩
    simpa [xi] using haxisL
  · funext j
    simp [xi, residueColumn]

/-- Canonical rank-one integration.  Phase-space axis avoidance and nonempty
support provide exactly the ambient base hypotheses; radicality of the
canonical contracted base ideal then supplies the Laurent conormal axis. -/
theorem exists_canonical_rankOne_laurentConormalAxis
    {k : Type u} [Field k] [IsAlgClosed k]
    (I : RightIdeal (PresentedWeyl k 1))
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin 1))} :
          Set (SymbolRing k 1))))
    (hsupp : (orderCharacteristicSupport k I).Nonempty) :
    ∃ (yL : Fin 1 → LaurentSeries k)
      (xi : Fin 1 → PowerSeries k),
      Sum.elim yL
          (fun j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi j)) ∈
        equationConormalLocus
          ((reducedOrderBaseIdeal k I).map
            (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin 1))) ∧
      residueColumn xi = (fun _ : Fin 1 ↦ 1) := by
  obtain ⟨hexists, havoid⟩ :=
    exists_baseZero_and_all_coordinate_ne_zero I (0 : Fin 1) hdisjoint hsupp
  exact exists_laurentConormalAxis_of_radical_ambient_axis_avoidance
    (reducedOrderBaseIdeal k I)
    (reducedOrderBaseIdeal_isRadical k I) hexists havoid


end

end Stafford38.Geometry.OneVariableAmbientConormal
