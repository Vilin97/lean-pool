/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.CompletedDVRCoefficientSection
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.DiscreteValuationRing.Basic


/-!
# A chosen-coordinate power-series map to a completed DVR

For a discrete valuation ring `V`, choose an actual uniformizer `pi`, not an
arbitrary nonzero nonunit.  A residue-field section in the maximal-ideal adic
completion then gives a map depending on those choices

`(ResidueField V)[[X]] -> AdicCompletion (maximalIdeal V) V`

by evaluating the `n`-th truncation modulo the `n`-th power of the maximal
ideal.  This file constructs that map directly from the inverse-limit
coordinates and proves its coefficient and uniformizer formulas.

No Cohen structure theorem is invoked.  In particular, an equivalence is
constructed only from a separately proved surjectivity statement.
-/

@[expose] public section

namespace Stafford38.Geometry.CompletedDVRPowerSeries

open IsLocalRing
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.CompletedDVRCoefficientSection
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RetainedDVR

noncomputable section


universe u

section NilpotentEvaluation

variable {K S : Type u} [CommRing K] [CommRing S]

/-- Polynomials agreeing below degree `n` have the same value at an element
whose `n`-th power vanishes. -/
private theorem eval₂_eq_of_coeff_eq_of_pow_eq_zero
    (c : K →+* S) (x : S) (n : ℕ) (hx : x ^ n = 0)
    {p q : Polynomial K}
    (hcoeff : ∀ d < n, p.coeff d = q.coeff d) :
    Polynomial.eval₂ c x p = Polynomial.eval₂ c x q := by
  have hdvd : (Polynomial.X : Polynomial K) ^ n ∣ p - q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    simp [hcoeff d hd]
  obtain ⟨r, hr⟩ := hdvd
  have hzero : Polynomial.eval₂ c x (p - q) = 0 := by
    rw [hr, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, hx, zero_mul]
  rw [Polynomial.eval₂_sub, sub_eq_zero] at hzero
  exact hzero

/-- Evaluation of a power series at an `n`-nilpotent element, using its
degree-`< n` truncation. -/
def nilpotentPowerSeriesEval
    (c : K →+* S) (x : S) (n : ℕ) (hx : x ^ n = 0) :
    PowerSeries K →+* S where
  toFun f := Polynomial.eval₂ c x (PowerSeries.trunc n f)
  map_zero' := by simp
  map_add' f g := by simp
  map_one' := by
    cases n with
    | zero =>
        have hsub : Subsingleton S := by
          apply subsingleton_iff_zero_eq_one.mp
          simpa using hx.symm
        exact Subsingleton.elim _ _
    | succ n => simp
  map_mul' f g := by
    rw [← Polynomial.eval₂_mul]
    apply eval₂_eq_of_coeff_eq_of_pow_eq_zero c x n hx
    intro d hd
    rw [PowerSeries.coeff_trunc, ite_eq_left hd]
    calc
      (PowerSeries.coeff d) (f * g) =
          (PowerSeries.coeff d)
            ((PowerSeries.trunc n f : PowerSeries K) *
              (PowerSeries.trunc n g : PowerSeries K)) :=
        PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hd
      _ = (PowerSeries.trunc n f * PowerSeries.trunc n g).coeff d := by
        rw [← Polynomial.coe_mul]
        exact Polynomial.coeff_coe
          (PowerSeries.trunc n f * PowerSeries.trunc n g) d

@[simp]
theorem nilpotentPowerSeriesEval_C
    (c : K →+* S) (x : S) (n : ℕ) (hx : x ^ n = 0) (a : K) :
    nilpotentPowerSeriesEval c x n hx (PowerSeries.C a) = c a := by
  cases n with
  | zero =>
      have hone : (1 : S) = 0 := by simpa using hx
      have hsub : Subsingleton S :=
        subsingleton_iff_zero_eq_one.mp hone.symm
      exact Subsingleton.elim _ _
  | succ n => simp [nilpotentPowerSeriesEval]

@[simp]
theorem nilpotentPowerSeriesEval_X
    (c : K →+* S) (x : S) (n : ℕ) (hx : x ^ n = 0) :
    nilpotentPowerSeriesEval c x n hx PowerSeries.X = x := by
  cases n with
  | zero =>
      have hone : (1 : S) = 0 := by simpa using hx
      have hsub : Subsingleton S :=
        subsingleton_iff_zero_eq_one.mp hone.symm
      exact Subsingleton.elim _ _
  | succ n =>
      cases n with
      | zero =>
          have hx0 : x = 0 := by simpa using hx
          simp [nilpotentPowerSeriesEval,  hx0]
      | succ n =>
          simp [nilpotentPowerSeriesEval]

/-- Truncated evaluation is independent of a larger truncation once the
smaller nilpotence exponent has been reached. -/
private theorem nilpotentPowerSeriesEval_truncation_independent
    (c : K →+* S) (x : S) {m n : ℕ} (hmn : m ≤ n)
    (hx : x ^ m = 0) (f : PowerSeries K) :
    Polynomial.eval₂ c x (PowerSeries.trunc n f) =
      Polynomial.eval₂ c x (PowerSeries.trunc m f) := by
  apply eval₂_eq_of_coeff_eq_of_pow_eq_zero c x m hx
  intro d hd
  rw [PowerSeries.coeff_trunc, ite_eq_left (lt_of_lt_of_le hd hmn),
    PowerSeries.coeff_trunc, ite_eq_left hd]

end NilpotentEvaluation

section CompleteDVR

variable (E V : Type u)
variable [Field E] [CommRing V] [IsDomain V]
variable [IsDiscreteValuationRing V] [Algebra E V]

private abbrev K := ResidueField V
private abbrev m : Ideal V := maximalIdeal V

/-- A fixed genuine uniformizer of the DVR. -/
def chosenUniformizer : V :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible V)

/-- The chosen element is irreducible. -/
theorem chosenUniformizer_irreducible :
    Irreducible (chosenUniformizer V) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible V)

/-- Consequently the chosen element generates the maximal ideal. -/
theorem maximalIdeal_eq_span_chosenUniformizer :
    maximalIdeal V = Ideal.span {chosenUniformizer V} :=
  (chosenUniformizer_irreducible V).maximalIdeal_eq

/-- The chosen uniformizer in the `n`-th raw completion coordinate. -/
def uniformizerCoordinate (n : ℕ) :
    V ⧸ ((m V) ^ n • ⊤ : Ideal V) :=
  Ideal.Quotient.mk _ (chosenUniformizer V)

/-- Its `n`-th power vanishes in the `n`-th coordinate. -/
theorem uniformizerCoordinate_pow_eq_zero (n : ℕ) :
    uniformizerCoordinate V n ^ n = 0 := by
  rw [uniformizerCoordinate, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  simpa using Ideal.pow_mem_pow
    (show chosenUniformizer V ∈ m V by
      change chosenUniformizer V ∈ maximalIdeal V
      rw [maximalIdeal_eq_span_chosenUniformizer V]
      exact Ideal.mem_span_singleton_self _) n

/-- Evaluation of a power series in one coordinate of the completed DVR. -/
def powerSeriesCoordinateMap
    (hsep : Algebra.IsSeparable E (K V)) (n : ℕ) :
    PowerSeries (K V) →+* V ⧸ ((m V) ^ n • ⊤ : Ideal V) :=
  nilpotentPowerSeriesEval
    (completionCoordinateSection E V hsep n).toRingHom
    (uniformizerCoordinate V n) n
    (uniformizerCoordinate_pow_eq_zero V n)

/-- Coordinate maps commute with every inverse-limit transition. -/
theorem powerSeriesCoordinateMap_compatible
    (hsep : Algebra.IsSeparable E (K V)) {a b : ℕ} (hab : a ≤ b)
    (f : PowerSeries (K V)) :
    AdicCompletion.transitionMap (m V) V hab
        (powerSeriesCoordinateMap E V hsep b f) =
      powerSeriesCoordinateMap E V hsep a f := by
  let T := (AdicCompletion.transitionMapₐ (m V) hab).toRingHom
  change T (Polynomial.eval₂
      (completionCoordinateSection E V hsep b).toRingHom
      (uniformizerCoordinate V b) (PowerSeries.trunc b f)) =
    Polynomial.eval₂
      (completionCoordinateSection E V hsep a).toRingHom
      (uniformizerCoordinate V a) (PowerSeries.trunc a f)
  rw [Polynomial.hom_eval₂]
  have hc :
      T.comp (completionCoordinateSection E V hsep b).toRingHom =
        (completionCoordinateSection E V hsep a).toRingHom := by
    ext z
    exact completionCoordinateSection_compatible E V hsep hab z
  have hx : T (uniformizerCoordinate V b) = uniformizerCoordinate V a := by
    rfl
  rw [hc, hx]
  exact nilpotentPowerSeriesEval_truncation_independent
    (completionCoordinateSection E V hsep a).toRingHom
    (uniformizerCoordinate V a) hab
    (uniformizerCoordinate_pow_eq_zero V a) f

/-- The actual chosen-coordinate power-series map to the maximal-ideal adic
completion. -/
def completedDVRPowerSeriesMap
    (hsep : Algebra.IsSeparable E (K V)) :
    PowerSeries (K V) →+* AdicCompletion (m V) V where
  toFun f :=
    ⟨fun n ↦ powerSeriesCoordinateMap E V hsep n f,
      fun hab ↦ powerSeriesCoordinateMap_compatible E V hsep hab f⟩
  map_zero' := AdicCompletion.ext fun n ↦
    (powerSeriesCoordinateMap E V hsep n).map_zero
  map_one' := AdicCompletion.ext fun n ↦
    (powerSeriesCoordinateMap E V hsep n).map_one
  map_add' f g := AdicCompletion.ext fun n ↦
    (powerSeriesCoordinateMap E V hsep n).map_add f g
  map_mul' f g := AdicCompletion.ext fun n ↦
    (powerSeriesCoordinateMap E V hsep n).map_mul f g

/-- Evaluation of the completed map at coordinate `n` is its truncated
polynomial evaluation there. -/
theorem eval_completedDVRPowerSeriesMap
    (hsep : Algebra.IsSeparable E (K V)) (n : ℕ)
    (f : PowerSeries (K V)) :
    (completedDVRPowerSeriesMap E V hsep f).val n =
      powerSeriesCoordinateMap E V hsep n f :=
  rfl

/-- Constant series map to the completed residue-field section. -/
@[simp]
theorem completedDVRPowerSeriesMap_C
    (hsep : Algebra.IsSeparable E (K V)) (a : K V) :
    completedDVRPowerSeriesMap E V hsep (PowerSeries.C a) =
      completedCoefficientSection E V hsep a := by
  apply AdicCompletion.ext
  intro n
  exact nilpotentPowerSeriesEval_C
    (completionCoordinateSection E V hsep n).toRingHom
    (uniformizerCoordinate V n) n
    (uniformizerCoordinate_pow_eq_zero V n) a

/-- The series variable maps to the chosen uniformizer in every completion
coordinate. -/
@[simp]
theorem completedDVRPowerSeriesMap_X
    (hsep : Algebra.IsSeparable E (K V)) :
    completedDVRPowerSeriesMap E V hsep PowerSeries.X =
      ⟨fun n ↦ uniformizerCoordinate V n,
        fun hab ↦ by rfl⟩ := by
  apply AdicCompletion.ext
  intro n
  exact nilpotentPowerSeriesEval_X
    (completionCoordinateSection E V hsep n).toRingHom
    (uniformizerCoordinate V n) n
    (uniformizerCoordinate_pow_eq_zero V n)

/-- A coefficient-section value cannot be killed by the matching power of
the uniformizer one level too early. -/
private theorem coefficient_eq_zero_of_mul_uniformizer_pow_eq_zero
    (hsep : Algebra.IsSeparable E (K V)) (n : ℕ) (a : K V)
    (hzero :
      completionCoordinateSection E V hsep (n + 1) a *
          uniformizerCoordinate V (n + 1) ^ n = 0) :
    a = 0 := by
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective
    (completionCoordinateSection E V hsep (n + 1) a)
  have hmem : v * chosenUniformizer V ^ n ∈ (m V) ^ (n + 1) := by
    have hraw :
        Ideal.Quotient.mk ((m V) ^ (n + 1) • ⊤ : Ideal V)
            (v * chosenUniformizer V ^ n) = 0 := by
      rw [map_mul, map_pow, hv]
      change completionCoordinateSection E V hsep (n + 1) a *
          uniformizerCoordinate V (n + 1) ^ n = 0
      exact hzero
    rw [Ideal.Quotient.eq_zero_iff_mem] at hraw
    simpa using hraw
  have hpowspan :
      (m V) ^ (n + 1) =
        Ideal.span {chosenUniformizer V ^ (n + 1)} := by
    change (maximalIdeal V) ^ (n + 1) = _
    rw [maximalIdeal_eq_span_chosenUniformizer V,
      Ideal.span_singleton_pow]
  rw [hpowspan, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  have hvfactor : v = b * chosenUniformizer V := by
    apply mul_right_cancel₀ (pow_ne_zero n
      (chosenUniformizer_irreducible V).ne_zero)
    calc
      v * chosenUniformizer V ^ n =
          b * chosenUniformizer V ^ (n + 1) := hb.symm
      _ = (b * chosenUniformizer V) * chosenUniformizer V ^ n := by
        rw [pow_succ']
        ring
  have hvmax : v ∈ maximalIdeal V := by
    rw [maximalIdeal_eq_span_chosenUniformizer V,
      Ideal.mem_span_singleton']
    exact ⟨b, hvfactor.symm⟩
  have hvres : residue V v = a := by
    have hab : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hv1 := congrArg
      (AdicCompletion.transitionMap (m V) V hab) hv
    rw [AdicCompletion.transitionMap_ideal_mk,
      completionCoordinateSection_compatible E V hsep hab a] at hv1
    let rawResidue :
        (V ⧸ ((m V) ^ 1 • ⊤ : Ideal V)) →+* K V :=
      Ideal.Quotient.lift _ (residue V) (by
        intro z hz
        rw [residue_eq_zero_iff]
        simpa using hz)
    have hres := congrArg rawResidue hv1
    change residue V v = rawResidue
      (completionCoordinateSection E V hsep 1 a) at hres
    rw [hres]
    have ha := DFunLike.congr_fun
      (adicJetResidue_comp_adicJetCoefficientSection E V hsep 0) a
    change adicJetResidue E V 0
        (adicJetCoefficientSection E V hsep 0 a) = a at ha
    calc
      rawResidue (completionCoordinateSection E V hsep 1 a) =
          adicJetResidue E V 0
            (adicJetCoefficientSection E V hsep 0 a) := by
        simp only [rawResidue, completionCoordinateSection, adicJetResidue,
          AlgHom.comp_apply]
        generalize hz : adicJetCoefficientSection E V hsep 0 a = z
        obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
        rfl
      _ = a := ha
  have hvzero : residue V v = 0 :=
    (IsLocalRing.residue_eq_zero_iff v).mpr hvmax
  rw [hvzero] at hvres
  exact hvres.symm

/-- If all earlier coefficients vanish, vanishing of coordinate `n+1`
forces the `n`-th coefficient to vanish. -/
private theorem coeff_eq_zero_of_coordinate_eq_zero
    (hsep : Algebra.IsSeparable E (K V)) (f : PowerSeries (K V)) (n : ℕ)
    (hprev : ∀ i < n, PowerSeries.coeff i f = 0)
    (hcoord : powerSeriesCoordinateMap E V hsep (n + 1) f = 0) :
    PowerSeries.coeff n f = 0 := by
  have hsum :
      ∑ i ∈ Finset.range (n + 1),
          completionCoordinateSection E V hsep (n + 1)
              (PowerSeries.coeff i f) *
            uniformizerCoordinate V (n + 1) ^ i = 0 := by
    simpa [powerSeriesCoordinateMap, nilpotentPowerSeriesEval,
      PowerSeries.eval₂_trunc_eq_sum_range] using hcoord
  have hsingle :
      completionCoordinateSection E V hsep (n + 1)
            (PowerSeries.coeff n f) *
          uniformizerCoordinate V (n + 1) ^ n = 0 := by
    rw [Finset.sum_eq_single n] at hsum
    · exact hsum
    · intro i hi hin
      rw [Finset.mem_range] at hi
      have hil : i < n := Nat.lt_of_le_of_ne
        (Nat.le_of_lt_succ hi) hin
      rw [hprev i hil, map_zero, zero_mul]
    · simp
  exact coefficient_eq_zero_of_mul_uniformizer_pow_eq_zero
    E V hsep n _ hsingle

/-- The chosen-coordinate map is injective.  The proof detects the first nonzero
coefficient in the quotient modulo the next uniformizer power. -/
theorem completedDVRPowerSeriesMap_injective
    (hsep : Algebra.IsSeparable E (K V)) :
    Function.Injective (completedDVRPowerSeriesMap E V hsep) := by
  intro f g hfg
  rw [← sub_eq_zero]
  apply PowerSeries.ext
  intro n
  have hmap : completedDVRPowerSeriesMap E V hsep (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hcoeff : ∀ r : ℕ,
      PowerSeries.coeff r (f - g) = 0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        apply coeff_eq_zero_of_coordinate_eq_zero E V hsep (f - g) r ih
        have := congrArg (fun z ↦ z.val (r + 1)) hmap
        change powerSeriesCoordinateMap E V hsep (r + 1) (f - g) = 0 at this
        exact this
  exact hcoeff n

/-- The kernel of the transition from level `n + 1` to level `n` consists of
one residue-field coefficient times the `n`-th uniformizer power. -/
private theorem exists_coefficient_mul_uniformizer_pow_eq
    (hsep : Algebra.IsSeparable E (K V)) (n : ℕ)
    (y : V ⧸ ((m V) ^ (n + 1) • ⊤ : Ideal V))
    (hy : AdicCompletion.transitionMap (m V) V (Nat.le_succ n) y = 0) :
    ∃ a : K V,
      y = completionCoordinateSection E V hsep (n + 1) a *
        uniformizerCoordinate V (n + 1) ^ n := by
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hvpow : v ∈ (m V) ^ n := by
    rw [AdicCompletion.transitionMap_ideal_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hy
    simpa using hy
  have hpowspan :
      (m V) ^ n = Ideal.span {chosenUniformizer V ^ n} := by
    change (maximalIdeal V) ^ n = _
    rw [maximalIdeal_eq_span_chosenUniformizer V,
      Ideal.span_singleton_pow]
  rw [hpowspan, Ideal.mem_span_singleton'] at hvpow
  obtain ⟨c, rfl⟩ := hvpow
  let a : K V := residue V c
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    (completionCoordinateSection E V hsep (n + 1) a)
  have hsres : residue V s = a := by
    have hlevel : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hs1 := congrArg
      (AdicCompletion.transitionMap (m V) V hlevel) hs
    rw [AdicCompletion.transitionMap_ideal_mk,
      completionCoordinateSection_compatible E V hsep hlevel a] at hs1
    let rawResidue :
        (V ⧸ ((m V) ^ 1 • ⊤ : Ideal V)) →+* K V :=
      Ideal.Quotient.lift _ (residue V) (by
        intro z hz
        rw [residue_eq_zero_iff]
        simpa using hz)
    have hres := congrArg rawResidue hs1
    change residue V s = rawResidue
      (completionCoordinateSection E V hsep 1 a) at hres
    rw [hres]
    have ha := DFunLike.congr_fun
      (adicJetResidue_comp_adicJetCoefficientSection E V hsep 0) a
    change adicJetResidue E V 0
        (adicJetCoefficientSection E V hsep 0 a) = a at ha
    calc
      rawResidue (completionCoordinateSection E V hsep 1 a) =
          adicJetResidue E V 0
            (adicJetCoefficientSection E V hsep 0 a) := by
        simp only [rawResidue, completionCoordinateSection, adicJetResidue,
          AlgHom.comp_apply]
        generalize hz : adicJetCoefficientSection E V hsep 0 a = z
        obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
        rfl
      _ = a := ha
  have hdiff : c - s ∈ m V := by
    change c - s ∈ maximalIdeal V
    rw [← residue_eq_zero_iff, map_sub, hsres]
    exact sub_self a
  refine ⟨a, ?_⟩
  rw [← hs, map_mul, map_pow]
  apply Ideal.Quotient.eq.mpr
  change c * chosenUniformizer V ^ n -
      s * chosenUniformizer V ^ n ∈ (m V) ^ (n + 1) • ⊤
  have hpow : chosenUniformizer V ^ n ∈ (m V) ^ n :=
    Ideal.pow_mem_pow
      (show chosenUniformizer V ∈ m V by
        change chosenUniformizer V ∈ maximalIdeal V
        rw [maximalIdeal_eq_span_chosenUniformizer V]
        exact Ideal.mem_span_singleton_self _) n
  have hmul := Ideal.mul_mem_mul hdiff hpow
  simpa [sub_mul, pow_succ, mul_comm] using hmul

/-- Successive approximants matching one more adic coordinate at each step. -/
private noncomputable def powerSeriesApproximant
    (hsep : Algebra.IsSeparable E (K V))
    (z : AdicCompletion (m V) V) :
    (n : ℕ) → { f : PowerSeries (K V) //
      powerSeriesCoordinateMap E V hsep n f = z.val n }
  | 0 => by
      have htop : ((m V) ^ 0 • ⊤ : Ideal V) = ⊤ := by simp
      letI : Subsingleton (V ⧸ ((m V) ^ 0 • ⊤ : Ideal V)) := by
        rw [htop]
        infer_instance
      exact ⟨0, Subsingleton.elim _ _⟩
  | n + 1 => by
      let f := powerSeriesApproximant hsep z n
      let y := z.val (n + 1) - powerSeriesCoordinateMap E V hsep (n + 1) f
      have hy :
          AdicCompletion.transitionMap (m V) V (Nat.le_succ n) y = 0 := by
        change AdicCompletion.transitionMap (m V) V (Nat.le_succ n)
            (z.val (n + 1) - powerSeriesCoordinateMap E V hsep (n + 1) f) = 0
        rw [map_sub, z.property (Nat.le_succ n),
          powerSeriesCoordinateMap_compatible E V hsep (Nat.le_succ n) f,
          f.property, sub_self]
      let a := Classical.choose
        (exists_coefficient_mul_uniformizer_pow_eq E V hsep n y hy)
      have ha := Classical.choose_spec
        (exists_coefficient_mul_uniformizer_pow_eq E V hsep n y hy)
      refine ⟨f.1 + PowerSeries.C a * PowerSeries.X ^ n, ?_⟩
      rw [map_add, map_mul, map_pow]
      have hC : powerSeriesCoordinateMap E V hsep (n + 1)
          (PowerSeries.C a) =
          completionCoordinateSection E V hsep (n + 1) a :=
        nilpotentPowerSeriesEval_C
          (completionCoordinateSection E V hsep (n + 1)).toRingHom
          (uniformizerCoordinate V (n + 1)) (n + 1)
          (uniformizerCoordinate_pow_eq_zero V (n + 1)) a
      have hX : powerSeriesCoordinateMap E V hsep (n + 1) PowerSeries.X =
          uniformizerCoordinate V (n + 1) :=
        nilpotentPowerSeriesEval_X
          (completionCoordinateSection E V hsep (n + 1)).toRingHom
          (uniformizerCoordinate V (n + 1)) (n + 1)
          (uniformizerCoordinate_pow_eq_zero V (n + 1))
      rw [hC, hX]
      rw [← ha]
      change powerSeriesCoordinateMap E V hsep (n + 1) f +
          (z.val (n + 1) - powerSeriesCoordinateMap E V hsep (n + 1) f) =
        z.val (n + 1)
      abel

/-- Passing to the next approximant does not change any earlier coefficient. -/
private theorem powerSeriesApproximant_succ_coeff
    (hsep : Algebra.IsSeparable E (K V))
    (z : AdicCompletion (m V) V) (n i : ℕ) (hi : i < n) :
    PowerSeries.coeff i (powerSeriesApproximant E V hsep z (n + 1)).1 =
      PowerSeries.coeff i (powerSeriesApproximant E V hsep z n).1 := by
  change PowerSeries.coeff i
      ((powerSeriesApproximant E V hsep z n).1 +
        PowerSeries.C _ * PowerSeries.X ^ n) = _
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    ite_eq_right hi.ne, mul_zero, add_zero]

/-- All coefficients below level `a` are stable in every later approximant. -/
private theorem powerSeriesApproximant_coeff_stable
    (hsep : Algebra.IsSeparable E (K V))
    (z : AdicCompletion (m V) V) {a b i : ℕ} (hab : a ≤ b) (hi : i < a) :
    PowerSeries.coeff i (powerSeriesApproximant E V hsep z b).1 =
      PowerSeries.coeff i (powerSeriesApproximant E V hsep z a).1 := by
  induction b with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      omega
  | succ b ih =>
      by_cases hab' : a = b + 1
      · subst a
        rfl
      · have hab0 : a ≤ b := Nat.le_of_lt_succ (lt_of_le_of_ne hab hab')
        calc
          PowerSeries.coeff i
              (powerSeriesApproximant E V hsep z (b + 1)).1 =
              PowerSeries.coeff i
                (powerSeriesApproximant E V hsep z b).1 :=
            powerSeriesApproximant_succ_coeff E V hsep z b i
              (lt_of_lt_of_le hi hab0)
          _ = PowerSeries.coeff i
                (powerSeriesApproximant E V hsep z a).1 := ih hab0

/-- The power series obtained by taking the stable coefficient at every
stage of the successive approximation. -/
private noncomputable def powerSeriesExpansion
    (hsep : Algebra.IsSeparable E (K V))
    (z : AdicCompletion (m V) V) : PowerSeries (K V) :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff n (powerSeriesApproximant E V hsep z (n + 1))

/-- The assembled expansion has the same first `n` coefficients as the
`n`-th approximant. -/
private theorem powerSeriesExpansion_coeff_eq_approximant
    (hsep : Algebra.IsSeparable E (K V))
    (z : AdicCompletion (m V) V) {n i : ℕ} (hi : i < n) :
    PowerSeries.coeff i (powerSeriesExpansion E V hsep z) =
      PowerSeries.coeff i (powerSeriesApproximant E V hsep z n).1 := by
  rw [powerSeriesExpansion, PowerSeries.coeff_mk]
  exact (powerSeriesApproximant_coeff_stable E V hsep z
    (a := i + 1) (b := n) (i := i)
    (Nat.succ_le_iff.mpr hi) (Nat.lt_succ_self i)).symm

/-- Every compatible adic family admits an expansion in the chosen
uniformizer with coefficients in the completed residue-field section. -/
def CompletedDVRPowerSeriesSurjectivity
    (hsep : Algebra.IsSeparable E (K V)) : Prop :=
  Function.Surjective (completedDVRPowerSeriesMap E V hsep)

/-- Successive approximation supplies the expansion theorem. -/
theorem completedDVRPowerSeriesMap_surjective
    (hsep : Algebra.IsSeparable E (K V)) :
    CompletedDVRPowerSeriesSurjectivity E V hsep := by
  intro z
  refine ⟨powerSeriesExpansion E V hsep z, ?_⟩
  apply AdicCompletion.ext
  intro n
  rw [eval_completedDVRPowerSeriesMap]
  change Polynomial.eval₂
      (completionCoordinateSection E V hsep n).toRingHom
      (uniformizerCoordinate V n)
      (PowerSeries.trunc n (powerSeriesExpansion E V hsep z)) = z.val n
  calc
    Polynomial.eval₂
        (completionCoordinateSection E V hsep n).toRingHom
        (uniformizerCoordinate V n)
        (PowerSeries.trunc n (powerSeriesExpansion E V hsep z)) =
      Polynomial.eval₂
        (completionCoordinateSection E V hsep n).toRingHom
        (uniformizerCoordinate V n)
        (PowerSeries.trunc n (powerSeriesApproximant E V hsep z n)) := by
          apply eval₂_eq_of_coeff_eq_of_pow_eq_zero
            (completionCoordinateSection E V hsep n).toRingHom
            (uniformizerCoordinate V n) n
            (uniformizerCoordinate_pow_eq_zero V n)
          intro d hd
          rw [PowerSeries.coeff_trunc, ite_eq_left hd,
            PowerSeries.coeff_trunc, ite_eq_left hd]
          exact powerSeriesExpansion_coeff_eq_approximant E V hsep z hd
    _ = powerSeriesCoordinateMap E V hsep n
          (powerSeriesApproximant E V hsep z n) := rfl
    _ = z.val n := (powerSeriesApproximant E V hsep z n).property

/-- A supplied surjectivity proof turns the constructed map into the literal
power-series equivalence. -/
def completedDVRPowerSeriesEquivOfSurjective
    (hsep : Algebra.IsSeparable E (K V))
    (hsurj : CompletedDVRPowerSeriesSurjectivity E V hsep) :
    PowerSeries (K V) ≃+* AdicCompletion (m V) V :=
  RingEquiv.ofBijective (completedDVRPowerSeriesMap E V hsep)
    ⟨completedDVRPowerSeriesMap_injective E V hsep, hsurj⟩

end CompleteDVR

section RetainedDVR

private abbrev SourceDVR (E : Type u) [Field E] :=
  CoordinateZeroLocalRing E

/-- The chosen-coordinate power-series map for the retained DVR place. -/
def retainedCompletedDVRPowerSeriesMap
    (E : Type u) [Field E] [CharZero E]
    {L : Type u} [Field L] [Algebra (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
    letI : Algebra E D.valuation.toSubring :=
      (relativeCoefficientMap E D).toAlgebra
    PowerSeries (ResidueField D.valuation.toSubring) →+*
      AdicCompletion (maximalIdeal D.valuation.toSubring)
        D.valuation.toSubring := by
  letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
  letI : Algebra E D.valuation.toSubring :=
    (relativeCoefficientMap E D).toAlgebra
  exact completedDVRPowerSeriesMap E D.valuation.toSubring
    (relativeResidue_isSeparable E D)

/-- The retained completed-DVR power-series map is injective. -/
theorem retainedCompletedDVRPowerSeriesMap_injective
    (E : Type u) [Field E] [CharZero E]
    {L : Type u} [Field L] [Algebra (SourceDVR E) L]
    {a : SourceDVR E}
    (D : RetainedDVRPlace (SourceDVR E) (L := L) a) :
    letI : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
    letI : Algebra E D.valuation.toSubring :=
      (relativeCoefficientMap E D).toAlgebra
    Function.Injective (retainedCompletedDVRPowerSeriesMap E D) := by
  let : IsDiscreteValuationRing D.valuation.toSubring := D.isDiscrete
  let : Algebra E D.valuation.toSubring :=
    (relativeCoefficientMap E D).toAlgebra
  exact completedDVRPowerSeriesMap_injective E D.valuation.toSubring
    (relativeResidue_isSeparable E D)

end RetainedDVR


end

end Stafford38.Geometry.CompletedDVRPowerSeries
