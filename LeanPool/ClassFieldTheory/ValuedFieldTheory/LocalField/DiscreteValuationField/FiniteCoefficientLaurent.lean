/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Finite
/-!
# Coefficient-field descent for Laurent series

This file starts the remaining equal-characteristic descent in the local-field structure classification: a finite coefficient field `k` of characteristic `p` gives a canonical
coefficientwise map from `F_p((X))` to `k((X))`.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace FiniteCoefficientLaurent

open scoped LaurentSeries PowerSeries

section PowerSeriesFinite

variable {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]

/-- If the coefficient field extension `A/R` is finite-dimensional, then
`A⟦X⟧` is finitely generated over `R⟦X⟧`.  A finite `R`-basis of `A` gives
generators by embedding basis vectors as constant power series. -/
theorem powerSeries_moduleFinite_of_finiteDimensional
    [FiniteDimensional R A] :
    Module.Finite R⟦X⟧ A⟦X⟧ := by
  classical
  let b : Module.Basis (Fin (Module.finrank R A)) R A := Module.finBasis R A
  let gens : Finset A⟦X⟧ :=
    Finset.univ.image fun i : Fin (Module.finrank R A) =>
      PowerSeries.C (b i)
  refine ⟨gens, ?_⟩
  rw [eq_top_iff]
  intro f _hf
  let coord : Fin (Module.finrank R A) → R⟦X⟧ :=
    fun i => PowerSeries.mk fun n => b.repr (PowerSeries.coeff n f) i
  have hsum :
      (∑ i : Fin (Module.finrank R A),
          coord i • PowerSeries.C (b i)) = f := by
    apply PowerSeries.ext
    intro n
    calc
      PowerSeries.coeff n
          (∑ i : Fin (Module.finrank R A),
            coord i • PowerSeries.C (b i)) =
          ∑ i : Fin (Module.finrank R A),
            algebraMap R A (b.repr (PowerSeries.coeff n f) i) * b i := by
        simp [coord, Algebra.smul_def, PowerSeries.algebraMap_apply'',
          PowerSeries.coeff_map]
      _ = PowerSeries.coeff n f := by
        simpa [Algebra.smul_def] using
          (b.sum_repr (PowerSeries.coeff n f))
  rw [← hsum]
  exact
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (coord i) <|
        Submodule.subset_span (by
          simp [gens])

end PowerSeriesFinite

variable (p : ℕ) (k : Type u) [Fact p.Prime] [Field k] [CharP k p]

/-- A finite field of characteristic `p` is finite-dimensional over its prime
field `ZMod p`. -/
theorem zmod_finiteDimensional_of_finite [Finite k] :
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    FiniteDimensional (ZMod p) k := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : Fintype k := Fintype.ofFinite k
  exact Module.finite_def.2 <| by
    simpa using
    (Submodule.fg_span (R := ZMod p) (M := k)
      (s := Set.univ) (Set.finite_univ : (Set.univ : Set k).Finite))

/-- Finite generation of `k⟦X⟧` over `F_p⟦X⟧`, for a finite coefficient
field `k` of characteristic `p`. -/
theorem zmodPowerSeries_moduleFinite [Finite k] :
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    Module.Finite (ZMod p)⟦X⟧ k⟦X⟧ := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : FiniteDimensional (ZMod p) k :=
    zmod_finiteDimensional_of_finite p k
  exact powerSeries_moduleFinite_of_finiteDimensional (R := ZMod p) (A := k)

/-- Coefficientwise map on power series induced by the prime-field embedding
`ZMod p -> k`. -/
noncomputable def zmodPowerSeriesCoeffMap :
    (ZMod p)⟦X⟧ →+* k⟦X⟧ := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  exact PowerSeries.map (algebraMap (ZMod p) k)

/--
Establishes the identity `zmodPowerSeriesCoeffMap p k (PowerSeries.C a) = PowerSeries.C
((ZMod.castHom (m := p) dvd_rfl k) a)`.
-/
@[simp]
theorem zmodPowerSeriesCoeffMap_C (a : ZMod p) :
    zmodPowerSeriesCoeffMap p k (PowerSeries.C a) =
      PowerSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  rw [zmodPowerSeriesCoeffMap, PowerSeries.map_C]
  change PowerSeries.C ((algebraMap (ZMod p) k) a) =
    PowerSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a)
  rfl

/-- Establishes the identity `zmodPowerSeriesCoeffMap p k PowerSeries.X = PowerSeries.X`. -/
@[simp]
theorem zmodPowerSeriesCoeffMap_X :
    zmodPowerSeriesCoeffMap p k PowerSeries.X = PowerSeries.X := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  simp [zmodPowerSeriesCoeffMap]

/-- The coefficientwise power-series map is finite when the coefficient field
extension `k / F_p` is finite. -/
theorem zmodPowerSeriesCoeffMap_finite [Finite k] :
    (zmodPowerSeriesCoeffMap p k).Finite := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change Module.Finite (ZMod p)⟦X⟧ k⟦X⟧
  exact zmodPowerSeries_moduleFinite p k

/-- The image of `X` under the coefficientwise power-series map is invertible
after passing to Laurent series. -/
theorem zmodPowerSeriesCoeffMap_X_isUnit :
    IsUnit
      ((algebraMap k⟦X⟧ k⸨X⸩).comp (zmodPowerSeriesCoeffMap p k)
        (PowerSeries.X : (ZMod p)⟦X⟧)) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  simp [zmodPowerSeriesCoeffMap]

/-- Coefficientwise Laurent-series map induced from `ZMod p -> k`. -/
noncomputable def zmodLaurentCoeffMap :
    (ZMod p)⸨X⸩ →+* k⸨X⸩ := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let φ : ZMod p →+* k := algebraMap (ZMod p) k
  exact
  { toFun := fun f => f.map φ
    map_zero' := by
      change HahnSeries.map (0 : (ZMod p)⸨X⸩) φ.toZeroHom = 0
      exact HahnSeries.map_zero (Γ := ℤ) (R := ZMod p) (S := k) φ.toZeroHom
    map_one' := by
      change HahnSeries.map (1 : (ZMod p)⸨X⸩) φ.toMonoidWithZeroHom = 1
      exact
        HahnSeries.map_one (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toMonoidWithZeroHom
    map_add' := by
      intro x y
      change
        HahnSeries.map (x + y) φ.toAddMonoidHom =
          HahnSeries.map x φ.toAddMonoidHom +
            HahnSeries.map y φ.toAddMonoidHom
      exact
        HahnSeries.map_add (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toAddMonoidHom
    map_mul' := by
      intro x y
      change
        HahnSeries.map (x * y) φ.toNonUnitalRingHom =
          HahnSeries.map x φ.toNonUnitalRingHom *
            HahnSeries.map y φ.toNonUnitalRingHom
      exact
        HahnSeries.map_mul (Γ := ℤ) (R := ZMod p) (S := k)
          φ.toNonUnitalRingHom }

/--
Establishes the identity `(zmodLaurentCoeffMap p k f).coeff n = (ZMod.castHom (m := p) dvd_rfl k)
(f.coeff n)`.
-/
@[simp]
theorem zmodLaurentCoeffMap_coeff (f : (ZMod p)⸨X⸩) (n : ℤ) :
    (zmodLaurentCoeffMap p k f).coeff n =
      (ZMod.castHom (m := p) dvd_rfl k) (f.coeff n) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change (HahnSeries.map f (algebraMap (ZMod p) k)).coeff n =
    (ZMod.castHom (m := p) dvd_rfl k) (f.coeff n)
  have hφ :
      algebraMap (ZMod p) k = ZMod.castHom (m := p) dvd_rfl k := rfl
  rw [hφ]
  rfl

/--
Establishes the identity `zmodLaurentCoeffMap p k (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩) =
(HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) : k⸨X⸩)`.
-/
@[simp]
theorem zmodLaurentCoeffMap_C (a : ZMod p) :
    zmodLaurentCoeffMap p k (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩) =
      (HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) :
        k⸨X⸩) := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  change
    HahnSeries.map (HahnSeries.C (Γ := ℤ) a : (ZMod p)⸨X⸩)
        (algebraMap (ZMod p) k) =
      (HahnSeries.C (Γ := ℤ) ((ZMod.castHom (m := p) dvd_rfl k) a) :
        k⸨X⸩)
  rw [HahnSeries.map_C]
  change
    HahnSeries.C ((algebraMap (ZMod p) k) a) =
      (HahnSeries.C ((ZMod.castHom (m := p) dvd_rfl k) a) : k⸨X⸩)
  rfl

/--
Establishes the identity `(zmodLaurentCoeffMap p k).comp (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩) =
(algebraMap k⟦X⟧ k⸨X⸩).comp (zmodPowerSeriesCoeffMap p k)`.
-/
theorem zmodLaurentCoeffMap_comp_powerSeries :
    (zmodLaurentCoeffMap p k).comp
        (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩) =
      (algebraMap k⟦X⟧ k⸨X⸩).comp
        (zmodPowerSeriesCoeffMap p k) := by
  ext f n
  cases n with
  | ofNat n =>
      simp [zmodLaurentCoeffMap, zmodPowerSeriesCoeffMap,
        LaurentSeries.coe_algebraMap, LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_map]
  | negSucc n =>
      simp [zmodLaurentCoeffMap, zmodPowerSeriesCoeffMap,
        LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]

/--
Establishes the identity `zmodLaurentCoeffMap p k ((algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩)
(PowerSeries.X : (ZMod p)⟦X⟧)) = (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧)`.
-/
@[simp]
theorem zmodLaurentCoeffMap_powerSeries_X :
    zmodLaurentCoeffMap p k
        ((algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩)
          (PowerSeries.X : (ZMod p)⟦X⟧)) =
      (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧) := by
  change
    ((zmodLaurentCoeffMap p k).comp
        (algebraMap (ZMod p)⟦X⟧ (ZMod p)⸨X⸩))
      (PowerSeries.X : (ZMod p)⟦X⟧) =
    (algebraMap k⟦X⟧ k⸨X⸩) (PowerSeries.X : k⟦X⟧)
  rw [zmodLaurentCoeffMap_comp_powerSeries]
  simp

/-- The induced algebra structure of `k((X))` over `F_p((X))`. -/
@[reducible]
noncomputable def zmodLaurentCoeffAlgebra :
    Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
  RingHom.toAlgebra (zmodLaurentCoeffMap p k)

/-- The algebra map from `F_p((X))` to `k((X))` is the coefficientwise extension map. -/
theorem zmodLaurentCoeffAlgebra_algebraMap :
    letI : Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
      zmodLaurentCoeffAlgebra p k
    algebraMap ((ZMod p)⸨X⸩) (k⸨X⸩) =
      zmodLaurentCoeffMap p k := by
  rfl

/-- The Laurent series whose coefficients are one coordinate of the coefficients
of `f` with respect to a fixed `ZMod p`-basis of `k`. -/
noncomputable def zmodLaurentCoeffCoord {ι : Type*} [Algebra (ZMod p) k]
    (b : Module.Basis ι (ZMod p) k) (f : k⸨X⸩) (i : ι) :
    (ZMod p)⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun n : ℤ => b.repr (f.coeff n) i)
    (by
      refine ⟨f.order, ?_⟩
      intro n hn
      by_contra hlt
      have hzero : f.coeff n = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_order (not_le.mp hlt)
      exact hn (by simp [hzero]))

omit [CharP k p] in
/--
Establishes the identity `(zmodLaurentCoeffCoord (p := p) (k := k) b f i).coeff n = b.repr
(f.coeff n) i`.
-/
@[simp]
theorem zmodLaurentCoeffCoord_coeff {ι : Type*} [Algebra (ZMod p) k]
    (b : Module.Basis ι (ZMod p) k) (f : k⸨X⸩) (i : ι) (n : ℤ) :
    (zmodLaurentCoeffCoord (p := p) (k := k) b f i).coeff n =
      b.repr (f.coeff n) i := by
  exact congrFun
    (HahnSeries.coeff_ofSuppBddBelow
      (f := fun m : ℤ => b.repr (f.coeff m) i))
    n

/-- Finite generation of `k((X))` as a module over `F_p((X))`. -/
theorem zmodLaurent_moduleFinite [Finite k] :
    letI : Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
      zmodLaurentCoeffAlgebra p k
    Module.Finite ((ZMod p)⸨X⸩) (k⸨X⸩) := by
  classical
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : FiniteDimensional (ZMod p) k :=
    zmod_finiteDimensional_of_finite p k
  let : Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
    zmodLaurentCoeffAlgebra p k
  let b : Module.Basis (Fin (Module.finrank (ZMod p) k)) (ZMod p) k :=
    Module.finBasis (ZMod p) k
  let gens : Finset k⸨X⸩ :=
    Finset.univ.image fun i : Fin (Module.finrank (ZMod p) k) =>
      (HahnSeries.C (Γ := ℤ) (b i) : k⸨X⸩)
  refine ⟨gens, ?_⟩
  rw [eq_top_iff]
  intro f _hf
  let coord : Fin (Module.finrank (ZMod p) k) → (ZMod p)⸨X⸩ :=
    fun i => zmodLaurentCoeffCoord (p := p) (k := k) b f i
  have hsum :
      (∑ i : Fin (Module.finrank (ZMod p) k),
          coord i • (HahnSeries.C (Γ := ℤ) (b i) : k⸨X⸩)) = f := by
    ext n
    rw [HahnSeries.coeff_sum]
    calc
      (∑ i : Fin (Module.finrank (ZMod p) k),
          (coord i • (HahnSeries.C (Γ := ℤ) (b i) : k⸨X⸩) :
            k⸨X⸩).coeff n) =
        ∑ i : Fin (Module.finrank (ZMod p) k),
          algebraMap (ZMod p) k (b.repr (f.coeff n) i) * b i := by
          apply Finset.sum_congr rfl
          intro i _
          change
            ((HahnSeries.map
                (zmodLaurentCoeffCoord (p := p) (k := k) b f i)
                (algebraMap (ZMod p) k)) *
              (HahnSeries.C (Γ := ℤ) (b i) : k⸨X⸩)).coeff n = _
          rw [mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
            HahnSeries.map_coeff, zmodLaurentCoeffCoord_coeff]
          exact mul_comm _ _
      _ = f.coeff n := by
        simpa [Algebra.smul_def] using (b.sum_repr (f.coeff n))
  rw [← hsum]
  exact
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (coord i) <|
        Submodule.subset_span (by
          change (HahnSeries.C (Γ := ℤ) (b i) : k⸨X⸩) ∈
            (gens : Set k⸨X⸩)
          simp [gens])

/-- The Laurent-series coefficient map `F_p((X)) -> k((X))` is finite when
`k` is finite. -/
theorem zmodLaurentCoeffMap_finite [Finite k] :
    (zmodLaurentCoeffMap p k).Finite := by
  let : Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
    zmodLaurentCoeffAlgebra p k
  change Module.Finite ((ZMod p)⸨X⸩) (k⸨X⸩)
  exact zmodLaurent_moduleFinite p k

/-- Finite-dimensionality of `k((X))` over the literal prime-field Laurent
series `F_p((X))`. -/
theorem zmodLaurent_finiteDimensional [Finite k] :
    letI : Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
      zmodLaurentCoeffAlgebra p k
    FiniteDimensional ((ZMod p)⸨X⸩) (k⸨X⸩) := by
  let : Algebra ((ZMod p)⸨X⸩) (k⸨X⸩) :=
    zmodLaurentCoeffAlgebra p k
  exact zmodLaurent_moduleFinite p k

end FiniteCoefficientLaurent
end LocalFieldTheory.DiscreteValuationField
