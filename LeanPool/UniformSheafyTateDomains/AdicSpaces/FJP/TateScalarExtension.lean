/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Finite scalar extension of Tate algebras

([hrw-decomposition] Tate leaf 12, main.) For a finite normed field extension
`L/K` with `‖algebraMap c‖ = ‖c‖`, the Tate algebra `L⟨T⟩ = P L m` splits as a
finite free module over `K⟨T⟩ = P K m`, coefficientwise along any `K`-basis of
`L`: coordinate functionals are continuous in finite dimension, so they
preserve restrictedness.
-/

@[expose] public section

open scoped Classical

open Filter

namespace FiniteJet.GraphKoszul

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [Algebra K L] [FiniteDimensional K L]
variable {m : ℕ}

/-- The Gauss weight of the unit polyradius is one. -/
theorem weight_one (t : Fin m →₀ ℕ) :
    (t.prod fun i k => (fun _ : Fin m => (1 : ℝ)) i ^ k) = 1 := by
  simp [Finsupp.prod]

/-- The underlying-series projection as a ring hom (the `Restricted` coe is a
def, opaque to generic subobject lemmas). -/
noncomputable def seriesP : P L m →+* MvPowerSeries (Fin m) L where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem seriesP_apply (x : P L m) : seriesP (m := m) x = x.1 := rfl

section MapP

variable (hext : ∀ c : K, ‖algebraMap K L c‖ = ‖c‖)

include hext in
/-- Coefficientwise base change preserves restrictedness when the norm
extends. -/
theorem isRestrictedGauss_map {f : MvPowerSeries (Fin m) K}
    (hf : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) f) :
    MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ))
      (MvPowerSeries.map (algebraMap K L) f) := by
  have hfun : (fun t : Fin m →₀ ℕ =>
      ‖MvPowerSeries.coeff t (MvPowerSeries.map (algebraMap K L) f)‖ *
        t.prod fun i k => (fun _ : Fin m => (1 : ℝ)) i ^ k) =
      fun t : Fin m →₀ ℕ => ‖MvPowerSeries.coeff t f‖ *
        t.prod fun i k => (fun _ : Fin m => (1 : ℝ)) i ^ k := by
    funext t
    rw [MvPowerSeries.coeff_map, hext]
  show Filter.Tendsto _ _ _
  rw [hfun]
  exact hf

/-- **Coefficientwise base change** of restricted power series along a
norm-extending embedding. -/
noncomputable def mapP : P K m →+* P L m where
  toFun x := ⟨MvPowerSeries.map (algebraMap K L) x.1,
    isRestrictedGauss_map hext x.2⟩
  map_one' := Subtype.ext (by
    show MvPowerSeries.map (algebraMap K L) (1 : MvPowerSeries (Fin m) K) = 1
    exact map_one _)
  map_mul' x y := Subtype.ext (by
    show MvPowerSeries.map (algebraMap K L) (x.1 * y.1) = _
    exact map_mul (MvPowerSeries.map (algebraMap K L)) x.1 y.1)
  map_zero' := Subtype.ext (by
    show MvPowerSeries.map (algebraMap K L) (0 : MvPowerSeries (Fin m) K) = 0
    exact map_zero _)
  map_add' x y := Subtype.ext (by
    show MvPowerSeries.map (algebraMap K L) (x.1 + y.1) = _
    exact map_add (MvPowerSeries.map (algebraMap K L)) x.1 y.1)

theorem mapP_coe (x : P K m) :
    (mapP (m := m) hext x).1 = MvPowerSeries.map (algebraMap K L) x.1 := rfl

end MapP

section Coordinates

/-- The coordinate series of a restricted series along a boundedly
`K`-linear functional: coefficientwise application preserves restrictedness
by the given bound. -/
noncomputable def coordSeries (φ : L →ₗ[K] K) {C : ℝ}
    (hC : ∀ x : L, ‖φ x‖ ≤ C * ‖x‖) (F : P L m) : P K m :=
  ⟨fun t => φ (MvPowerSeries.coeff t F.1), by
    show Filter.Tendsto (fun t : Fin m →₀ ℕ =>
      ‖(fun s : Fin m →₀ ℕ => φ (MvPowerSeries.coeff s F.1)) t‖ *
        t.prod fun i k => (fun _ : Fin m => (1 : ℝ)) i ^ k)
      cofinite (nhds 0)
    have hF : Filter.Tendsto (fun t : Fin m →₀ ℕ =>
        ‖MvPowerSeries.coeff t F.1‖ *
          t.prod fun i k => (fun _ : Fin m => (1 : ℝ)) i ^ k)
        cofinite (nhds 0) := F.2
    simp only [weight_one, mul_one] at hF ⊢
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => hC _) ?_
    simpa using hF.const_mul C⟩

theorem coordSeries_coeff (φ : L →ₗ[K] K) {C : ℝ}
    (hC : ∀ x : L, ‖φ x‖ ≤ C * ‖x‖) (F : P L m) (t : Fin m →₀ ℕ) :
    MvPowerSeries.coeff t ((coordSeries (m := m) φ hC F).1) =
      φ (MvPowerSeries.coeff t F.1) := rfl

end Coordinates

section Split

variable (hext : ∀ c : K, ‖algebraMap K L c‖ = ‖c‖)
variable {ι : Type*} [Fintype ι]

/-- The assembly map from coordinate tuples to the extended Tate algebra. -/
noncomputable def piToP (b : ι → L) :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    (ι → P K m) →ₗ[P K m] P L m :=
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  { toFun := fun G => ∑ j, mapP hext (G j) * polyToP (MvPolynomial.C (b j))
    map_add' := fun G H => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Pi.add_apply, map_add, add_mul]
    map_smul' := fun c G => by
      show ∑ j, mapP hext (c * G j) * polyToP (MvPolynomial.C (b j)) =
        c • ∑ j, mapP hext (G j) * polyToP (MvPolynomial.C (b j))
      have h1 : (c • ∑ j, mapP hext (G j) *
          polyToP (MvPolynomial.C (b j)) : P L m) =
          mapP hext c * ∑ j, mapP hext (G j) *
            polyToP (MvPolynomial.C (b j)) := rfl
      rw [h1]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_)
        (Finset.mul_sum _ _ _).symm
      rw [map_mul, mul_assoc] }

/-- Per-coefficient description of the assembly map. -/
theorem coeff_piToP (b : ι → L) (G : ι → P K m) (t : Fin m →₀ ℕ) :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    MvPowerSeries.coeff t ((piToP (m := m) hext b G : P L m)).1 =
      ∑ j, algebraMap K L (MvPowerSeries.coeff t ((G j).1)) * b j := by
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  have h1 : ((piToP (m := m) hext b G : P L m)).1 =
      seriesP (∑ j, mapP hext (G j) * polyToP (MvPolynomial.C (b j))) := rfl
  rw [h1, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : seriesP (mapP hext (G j) * polyToP (MvPolynomial.C (b j))) =
      MvPowerSeries.map (algebraMap K L) ((G j).1) *
        (MvPowerSeries.C (b j) : MvPowerSeries (Fin m) L) := by
    rw [map_mul, seriesP_apply, seriesP_apply, mapP_coe]
    rw [show (polyToP (E := L) (m := m) (MvPolynomial.C (b j))).1 =
      (MvPowerSeries.C (b j) : MvPowerSeries (Fin m) L) from
      MvPolynomial.coe_C (b j)]
  rw [h2, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_map]

include hext in
theorem piToP_surjective (b : Module.Basis ι K L) :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    Function.Surjective (piToP (m := m) hext (fun j => b j)) := by
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  letI : NormedAlgebra K L :=
    { (inferInstance : Algebra K L) with
      norm_smul_le := fun c x =>
        le_of_eq (by rw [Algebra.smul_def, norm_mul, hext]) }
  haveI : IsBoundedSMul K L := IsBoundedSMul.of_norm_smul_le
    NormedSpace.norm_smul_le
  haveI : ContinuousSMul K L := IsBoundedSMul.continuousSMul
  have hcont : ∀ j : ι, Continuous (b.coord j) := fun j =>
    LinearMap.continuous_of_finiteDimensional _
  have hbound : ∀ j : ι, ∃ C : ℝ, ∀ x : L, ‖(b.coord j) x‖ ≤ C * ‖x‖ := by
    intro j
    obtain ⟨C, -, hC⟩ :=
      SemilinearMapClass.bound_of_continuous (b.coord j) (hcont j)
    exact ⟨C, hC⟩
  choose Cf hCf using hbound
  intro F
  refine ⟨fun j => coordSeries (b.coord j) (hCf j) F, ?_⟩
  refine Subtype.ext (MvPowerSeries.ext fun t => ?_)
  rw [coeff_piToP]
  have h2 : ∀ j : ι, algebraMap K L (MvPowerSeries.coeff t
      ((coordSeries (b.coord j) (hCf j) F).1)) * b j =
      b.repr (MvPowerSeries.coeff t F.1) j • b j := by
    intro j
    rw [coordSeries_coeff]
    rw [show (b.coord j) (MvPowerSeries.coeff t F.1) =
      b.repr (MvPowerSeries.coeff t F.1) j from b.coord_apply _ _]
    rw [Algebra.smul_def]
  rw [Finset.sum_congr rfl fun j _ => h2 j]
  exact b.sum_repr (MvPowerSeries.coeff t F.1)

include hext in
theorem piToP_injective (b : Module.Basis ι K L) :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    Function.Injective (piToP (m := m) hext (fun j => b j)) := by
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  have hker : ∀ G : ι → P K m,
      piToP (m := m) hext (fun j => b j) G = 0 → G = 0 := by
    intro G hG
    funext j
    refine Subtype.ext (MvPowerSeries.ext fun t => ?_)
    have h3 : MvPowerSeries.coeff t
        ((piToP (m := m) hext (fun j => b j) G : P L m)).1 =
        MvPowerSeries.coeff t ((0 : P L m)).1 :=
      congrArg (fun z : P L m => MvPowerSeries.coeff t z.1) hG
    rw [coeff_piToP] at h3
    have h4 : ((∑ i, algebraMap K L (MvPowerSeries.coeff t ((G i).1)) *
        b i : L)) = 0 := by
      rw [h3]
      show MvPowerSeries.coeff t ((0 : P L m)).1 = 0
      rw [show ((0 : P L m)).1 = 0 from rfl, map_zero]
    have h5 : ∑ i, MvPowerSeries.coeff t ((G i).1) • b i = (0 : L) := by
      rw [← h4]
      exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _)
    have h6 := (Fintype.linearIndependent_iff.mp b.linearIndependent)
      (fun i => MvPowerSeries.coeff t ((G i).1)) h5 j
    rw [h6]
    show MvPowerSeries.coeff t ((0 : P K m)).1 = 0
    rw [show ((0 : P K m)).1 = 0 from rfl, map_zero]
  intro G H hGH
  have h7 : piToP (m := m) hext (fun j => b j) (G - H) = 0 := by
    rw [map_sub, hGH, sub_self]
  exact sub_eq_zero.mp (hker _ h7)

/-- **Leaf 12**: the extended Tate algebra is linearly a coordinate power of
the base Tate algebra. -/
noncomputable def scalarExtensionEquiv (b : Module.Basis ι K L) :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    (ι → P K m) ≃ₗ[P K m] P L m :=
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  LinearEquiv.ofBijective (piToP (m := m) hext (fun j => b j))
    ⟨piToP_injective hext b, piToP_surjective hext b⟩

include hext in
/-- The extended Tate algebra is module-finite over the base Tate algebra. -/
theorem module_finite_mapP :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    Module.Finite (P K m) (P L m) := by
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  exact Module.Finite.equiv
    (scalarExtensionEquiv (m := m) hext (Module.finBasis K L))

include hext in
/-- The extended Tate algebra is free over the base Tate algebra. -/
theorem module_free_mapP :
    letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
    Module.Free (P K m) (P L m) := by
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  exact Module.Free.of_equiv
    (scalarExtensionEquiv (m := m) hext (Module.finBasis K L))

end Split

end FiniteJet.GraphKoszul
