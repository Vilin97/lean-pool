/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings

/-!
# The spectral norm package for finite extensions

([hrw-decomposition] Tate leaf 12a/12b.) For `K` a complete ultrametric
nontrivially normed field and `L/K` finite, mathlib's spectral norm makes `L`
a complete ultrametric nontrivially normed field extending the norm of `K`.
Elements satisfying a monic relation over the unit ball have norm at most one
(a direct ultrametric bound — no minimal-polynomial descent).
-/

@[expose] public section

@[expose] public section

open scoped Classical

namespace FiniteJet.SpectralExtension

section Bound

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

/-- **The ultrametric integrality bound**: a root of a monic combination with
unit-ball coefficients lies in the unit ball. -/
theorem norm_le_one_of_pow_eq_sum {n : ℕ} (hn : 0 < n) {c : ℕ → F}
    (hc : ∀ i, ‖c i‖ ≤ 1) {x : F}
    (hx : x ^ n = ∑ i ∈ Finset.range n, c i * x ^ i) : ‖x‖ ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  have hx1 : (1 : ℝ) ≤ ‖x‖ := hgt.le
  have h1 : ‖x ^ n‖ ≤ ‖x‖ ^ (n - 1) := by
    rw [hx]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    calc ‖c i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul_of_nonneg_right (hc i) (by positivity)
      _ = ‖x‖ ^ i := one_mul _
      _ ≤ ‖x‖ ^ (n - 1) :=
          pow_le_pow_right₀ hx1 (Nat.le_pred_of_lt (Finset.mem_range.mp hi))
  rw [norm_pow] at h1
  have h2 : ‖x‖ ^ (n - 1) < ‖x‖ ^ n :=
    pow_lt_pow_right₀ hgt (Nat.sub_lt hn one_pos)
  linarith

end Bound

section Extension

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The spectral normed-field structure on a finite extension. -/
noncomputable def extNormedField : NormedField L :=
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  spectralNorm.normedField K L

/-- The spectral norm on a finite extension is ultrametric. -/
theorem extUltrametric :
    letI := extNormedField K L
    IsUltrametricDist L := by
  letI := extNormedField K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  refine ⟨fun x y z => ?_⟩
  have h1 : dist x z = spectralNorm K L (x - z) := rfl
  have h2 : dist x y = spectralNorm K L (x - y) := rfl
  have h3 : dist y z = spectralNorm K L (y - z) := rfl
  rw [h1, h2, h3, show x - z = (x - y) + (y - z) by ring]
  exact isNonarchimedean_spectralNorm _ _

/-- A finite spectral extension is complete. -/
theorem extCompleteSpace :
    letI := extNormedField K L
    CompleteSpace L := by
  letI := extNormedField K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NormedSpace K L := spectralNorm.normedSpace K L
  haveI : IsUniformAddGroup L := SeminormedAddCommGroup.to_isUniformAddGroup
  haveI : IsBoundedSMul K L := IsBoundedSMul.of_norm_smul_le
    NormedSpace.norm_smul_le
  haveI : ContinuousSMul K L := IsBoundedSMul.continuousSMul
  exact FiniteDimensional.complete K L

/-- The spectral norm makes a finite extension a normed `K`-space. -/
noncomputable def extNormedSpace :
    letI := extNormedField K L
    NormedSpace K L :=
  letI := extNormedField K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  spectralNorm.normedSpace K L

/-- The spectral norm makes a finite extension a topological `K`-module. -/
theorem extContinuousSMul :
    letI := extNormedField K L
    ContinuousSMul K L := by
  letI := extNormedField K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NormedSpace K L := spectralNorm.normedSpace K L
  haveI : IsBoundedSMul K L := IsBoundedSMul.of_norm_smul_le
    NormedSpace.norm_smul_le
  exact IsBoundedSMul.continuousSMul

/-- **A continuous injection out of a finite spectral extension is bounded
below**: if a finite extension `L/K` injects, compatibly with `K`, into a
normed `K`-algebra `M` whose scalars are norm-nonincreasing, then the spectral
norm of `L` is dominated by the norm of the image.  (Finite-dimensional normed
spaces have a unique topology: `LinearMap.exists_antilipschitzWith`.) -/
theorem exists_norm_le_mul_norm_map (M : Type*) [NormedCommRing M]
    [Algebra K M] (hM : ∀ (c : K) (x : M), ‖algebraMap K M c * x‖ ≤ ‖c‖ * ‖x‖)
    (f : L →+* M) (hf : ∀ c : K, f (algebraMap K L c) = algebraMap K M c)
    (hinj : Function.Injective ⇑f) :
    letI := extNormedField K L
    ∃ C : ℝ, 0 < C ∧ ∀ x : L, ‖x‖ ≤ C * ‖f x‖ := by
  letI := extNormedField K L
  letI : NormedSpace K L := extNormedSpace K L
  letI : NormedSpace K M :=
    { norm_smul_le := fun c x => by rw [Algebra.smul_def]; exact hM c x }
  haveI hfdL : FiniteDimensional K L := ‹FiniteDimensional K L›
  set g : L →ₗ[K] M :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hf] } with hgdef
  obtain ⟨C, hCpos, hanti⟩ :=
    @LinearMap.exists_antilipschitzWith K _ L _ _ M _ _ _ hfdL g
      (LinearMap.ker_eq_bot.mpr hinj)
  exact ⟨C, hCpos, fun x => ZeroHomClass.bound_of_antilipschitz g hanti x⟩

/-- The spectral norm extends the base norm. -/
theorem ext_norm_algebraMap (c : K) :
    letI := extNormedField K L
    ‖algebraMap K L c‖ = ‖c‖ := by
  letI := extNormedField K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  show spectralNorm K L (algebraMap K L c) = ‖c‖
  exact spectralNorm_extends c

/-- **Leaf 12b**: a root of a monic polynomial over the unit ball lies in the
unit ball of the spectral norm. -/
theorem ext_norm_le_one_of_monic_poly {x : L}
    {p : Polynomial ↥(FiniteJet.unitBall K)} (hp : p.Monic)
    (hev : Polynomial.eval₂
      ((algebraMap K L).comp (FiniteJet.unitBall K).subtype) x p = 0) :
    letI := extNormedField K L
    ‖x‖ ≤ 1 := by
  letI := extNormedField K L
  haveI := extUltrametric K L
  set f : ↥(FiniteJet.unitBall K) →+* L :=
    (algebraMap K L).comp (FiniteJet.unitBall K).subtype with hf
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hn
  · exfalso
    have hone : p = 1 := hp.natDegree_eq_zero.mp h0
    rw [hone, Polynomial.eval₂_one] at hev
    exact one_ne_zero hev
  have hsum := Polynomial.eval₂_eq_sum_range (p := p) f x
  rw [hev] at hsum
  rw [Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hsum
  have hx : x ^ p.natDegree = ∑ i ∈ Finset.range p.natDegree,
      (f (-(p.coeff i))) * x ^ i := by
    have h4 : x ^ p.natDegree =
        -∑ i ∈ Finset.range p.natDegree, f (p.coeff i) * x ^ i := by
      linear_combination -hsum
    rw [h4, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_neg]; ring
  refine norm_le_one_of_pow_eq_sum hn (fun i => ?_) hx
  have h5 : f (-(p.coeff i)) = algebraMap K L
      (((-(p.coeff i) : ↥(FiniteJet.unitBall K)) : K)) := rfl
  rw [h5]
  have h6 : ‖algebraMap K L
      (((-(p.coeff i) : ↥(FiniteJet.unitBall K)) : K))‖ =
      ‖((-(p.coeff i) : ↥(FiniteJet.unitBall K)) : K)‖ :=
    ext_norm_algebraMap K L _
  rw [h6]
  exact (FiniteJet.mem_unitBall_iff _ _).mp (-(p.coeff i)).2

end Extension

end FiniteJet.SpectralExtension
