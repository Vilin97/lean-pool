/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.ParabolicFibers
public import LeanPool.MarkoffModP.BGS.Markoff.Core.TraceClassification

/-!
# Explicit parametrizations of normalized Markoff fibers

This module formalizes the split and nonsplit parametrizations underlying Lemmas 4 and 5 of
Bourgain--Gamburd--Sarnak.  The trace-zero fiber is deliberately kept visible: although its
rotation is semisimple, its conic is singular, so the paper's claimed single-torus
parametrization needs the additional hypothesis that the fixed normalized trace is nonzero.
-/

@[expose] public section

namespace BGS.Markoff

universe u

section SplitFiber

variable {F : Type u} [Field F]

/-- The scalar product of the two eigen-coordinates on a nonparabolic normalized fiber. -/
def splitFiberProduct (w : Fˣ) : F :=
  splitTorusTrace w ^ 2 / (splitTorusTrace w ^ 2 - 4)

/-- The point on the normalized fiber obtained from a nonzero first eigen-coordinate. -/
def splitFiberPoint (w s : Fˣ) : NormalizedPoint F :=
  ⟨splitTorusTrace w,
    (s : F) + splitFiberProduct w * ((s⁻¹ : Fˣ) : F),
    (s : F) * (w : F) +
      splitFiberProduct w * ((s⁻¹ : Fˣ) : F) * ((w⁻¹ : Fˣ) : F)⟩

/-- The first eigen-coordinate recovered from a point in the fixed-trace plane. -/
def splitFiberFirstEigenCoordinate (w : Fˣ) (x : NormalizedPoint F) : F :=
  (x.u3 - ((w⁻¹ : Fˣ) : F) * x.u2) /
    ((w : F) - ((w⁻¹ : Fˣ) : F))

/-- The second eigen-coordinate recovered from a point in the fixed-trace plane. -/
def splitFiberSecondEigenCoordinate (w : Fˣ) (x : NormalizedPoint F) : F :=
  ((w : F) * x.u2 - x.u3) /
    ((w : F) - ((w⁻¹ : Fˣ) : F))

theorem splitTorusTrace_sq_sub_four (w : Fˣ) :
    splitTorusTrace w ^ 2 - 4 =
      ((w : F) - ((w⁻¹ : Fˣ) : F)) ^ 2 := by
  simp [splitTorusTrace]
  field_simp
  ring

theorem splitEigenvalueDifference_ne_zero (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    (w : F) - ((w⁻¹ : Fˣ) : F) ≠ 0 := by
  intro h
  apply hw
  have hinv : ((w⁻¹ : Fˣ) : F) = (w : F) := by
    exact (sub_eq_zero.mp h).symm
  rw [pow_two]
  calc
    (w : F) * (w : F) = ((w⁻¹ : Fˣ) : F) * (w : F) := by rw [hinv]
    _ = 1 := by simp

theorem splitFiberProduct_ne_zero (w : Fˣ)
    (hw : (w : F) ^ 2 ≠ 1) (htrace : splitTorusTrace w ≠ 0) :
    splitFiberProduct w ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero 2 htrace
  · rw [splitTorusTrace_sq_sub_four]
    exact pow_ne_zero 2 (splitEigenvalueDifference_ne_zero w hw)

theorem normalizedPolynomial_splitEigenCoordinates (w : Fˣ) (a b : F) :
    normalizedPolynomial
        (⟨splitTorusTrace w, a + b,
          a * (w : F) + b * ((w⁻¹ : Fˣ) : F)⟩ : NormalizedPoint F) =
      splitTorusTrace w ^ 2 + (4 - splitTorusTrace w ^ 2) * a * b := by
  simp [normalizedPolynomial, splitTorusTrace]
  field_simp
  ring

theorem splitFiberPoint_mem (w s : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    splitFiberPoint w s ∈ normalizedFiber1 (splitTorusTrace w) := by
  constructor
  · change normalizedPolynomial (splitFiberPoint w s) = 0
    change normalizedPolynomial
      (⟨splitTorusTrace w,
        (s : F) + splitFiberProduct w * ((s⁻¹ : Fˣ) : F),
        (s : F) * (w : F) +
          (splitFiberProduct w * ((s⁻¹ : Fˣ) : F)) * ((w⁻¹ : Fˣ) : F)⟩ :
        NormalizedPoint F) = 0
    rw [normalizedPolynomial_splitEigenCoordinates]
    rw [splitFiberProduct, splitTorusTrace_sq_sub_four]
    have hdifference := splitEigenvalueDifference_ne_zero w hw
    field_simp
    simp [splitTorusTrace]
    right
    field_simp
    ring
  · rfl

theorem splitFiberFirstEigenCoordinate_point (w s : Fˣ)
    (hw : (w : F) ^ 2 ≠ 1) :
    splitFiberFirstEigenCoordinate w (splitFiberPoint w s) = (s : F) := by
  rw [splitFiberFirstEigenCoordinate, splitFiberPoint]
  have hdifference := splitEigenvalueDifference_ne_zero w hw
  simp only [mul_assoc]
  simp
  field_simp
  ring

theorem splitFiberEigenCoordinates_add (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1)
    (x : NormalizedPoint F) :
    splitFiberFirstEigenCoordinate w x + splitFiberSecondEigenCoordinate w x = x.u2 := by
  rw [splitFiberFirstEigenCoordinate, splitFiberSecondEigenCoordinate]
  have hdifference := splitEigenvalueDifference_ne_zero w hw
  field_simp
  ring

theorem splitFiberEigenCoordinates_weighted_add
    (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) (x : NormalizedPoint F) :
    splitFiberFirstEigenCoordinate w x * (w : F) +
        splitFiberSecondEigenCoordinate w x * ((w⁻¹ : Fˣ) : F) = x.u3 := by
  rw [splitFiberFirstEigenCoordinate, splitFiberSecondEigenCoordinate]
  have hdifference := splitEigenvalueDifference_ne_zero w hw
  field_simp
  simp
  ring

theorem splitFiberEigenCoordinates_product (w : Fˣ)
    (hw : (w : F) ^ 2 ≠ 1)
    (x : ↑(normalizedFiber1 (splitTorusTrace w))) :
    splitFiberFirstEigenCoordinate w x * splitFiberSecondEigenCoordinate w x =
      splitFiberProduct w := by
  have hpoint :
      (x : NormalizedPoint F) =
        ⟨splitTorusTrace w,
          splitFiberFirstEigenCoordinate w x + splitFiberSecondEigenCoordinate w x,
          splitFiberFirstEigenCoordinate w x * (w : F) +
            splitFiberSecondEigenCoordinate w x * ((w⁻¹ : Fˣ) : F)⟩ := by
    ext
    · exact x.property.2
    · exact (splitFiberEigenCoordinates_add w hw x).symm
    · exact (splitFiberEigenCoordinates_weighted_add w hw x).symm
  have hpolynomial : normalizedPolynomial (x : NormalizedPoint F) = 0 := x.property.1
  rw [hpoint, normalizedPolynomial_splitEigenCoordinates] at hpolynomial
  rw [show 4 - splitTorusTrace w ^ 2 = -(splitTorusTrace w ^ 2 - 4) by ring,
    splitTorusTrace_sq_sub_four] at hpolynomial
  rw [splitFiberProduct, splitTorusTrace_sq_sub_four]
  have hdifference := splitEigenvalueDifference_ne_zero w hw
  field_simp
  linear_combination -hpolynomial

theorem splitFiberFirstEigenCoordinate_ne_zero (w : Fˣ)
    (hw : (w : F) ^ 2 ≠ 1) (htrace : splitTorusTrace w ≠ 0)
    (x : ↑(normalizedFiber1 (splitTorusTrace w))) :
    splitFiberFirstEigenCoordinate w x ≠ 0 := by
  intro hzero
  have hproduct := splitFiberEigenCoordinates_product w hw x
  rw [hzero, zero_mul] at hproduct
  exact splitFiberProduct_ne_zero w hw htrace hproduct.symm

/-- The split semisimple normalized fiber, away from trace zero, is explicitly equivalent to
the multiplicative group of the base field. -/
noncomputable def splitFiberEquiv (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1)
    (htrace : splitTorusTrace w ≠ 0) :
    Fˣ ≃ ↑(normalizedFiber1 (splitTorusTrace w)) where
  toFun s := ⟨splitFiberPoint w s, splitFiberPoint_mem w s hw⟩
  invFun x := Units.mk0 (splitFiberFirstEigenCoordinate w x)
    (splitFiberFirstEigenCoordinate_ne_zero w hw htrace x)
  left_inv s := by
    apply Units.ext
    exact splitFiberFirstEigenCoordinate_point w s hw
  right_inv x := by
    apply Subtype.ext
    let a := splitFiberFirstEigenCoordinate w x
    let b := splitFiberSecondEigenCoordinate w x
    have ha : a ≠ 0 := splitFiberFirstEigenCoordinate_ne_zero w hw htrace x
    have hab : a * b = splitFiberProduct w := splitFiberEigenCoordinates_product w hw x
    have hb : splitFiberProduct w * a⁻¹ = b := by
      rw [← hab]
      field_simp
    ext
    · exact x.property.2.symm
    · change a + splitFiberProduct w * a⁻¹ = x.val.u2
      rw [hb]
      exact splitFiberEigenCoordinates_add w hw x
    · change a * (w : F) + splitFiberProduct w * a⁻¹ * ((w⁻¹ : Fˣ) : F) =
        x.val.u3
      rw [hb]
      exact splitFiberEigenCoordinates_weighted_add w hw x

/-- Under the explicit split-fiber parametrization, normalized rotation is multiplication by
the chosen eigenvalue. -/
theorem normalizedRotate1_splitFiberPoint (w s : Fˣ) :
    normalizedRotate1 (splitFiberPoint w s) = splitFiberPoint w (s * w) := by
  ext
  · rfl
  · simp [normalizedRotate1, splitFiberPoint, splitTorusTrace]
    field_simp
  · simp [normalizedRotate1, splitFiberPoint, splitTorusTrace]
    field_simp
    ring

/-- Every iterate of the split-fiber rotation multiplies the eigen-coordinate by the matching
power of the eigenvalue. -/
theorem iterate_normalizedRotate1_splitFiberPoint (w s : Fˣ) (n : ℕ) :
    (normalizedRotate1^[n]) (splitFiberPoint w s) = splitFiberPoint w (s * w ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, normalizedRotate1_splitFiberPoint]
      congr 1
      rw [pow_succ, mul_assoc]

theorem iterate_normalizedRotate1_splitFiberPoint_eq_self_iff
    (w s : Fˣ) (hw : (w : F) ^ 2 ≠ 1) (n : ℕ) :
    (normalizedRotate1^[n]) (splitFiberPoint w s) = splitFiberPoint w s ↔ w ^ n = 1 := by
  rw [iterate_normalizedRotate1_splitFiberPoint]
  constructor
  · intro hpoint
    have hcoordinate := congrArg (splitFiberFirstEigenCoordinate w) hpoint
    rw [splitFiberFirstEigenCoordinate_point w (s * w ^ n) hw,
      splitFiberFirstEigenCoordinate_point w s hw] at hcoordinate
    have hunit : s * w ^ n = s * 1 := by
      apply Units.ext
      simpa using hcoordinate
    exact mul_left_cancel hunit
  · intro hpower
    rw [hpower, mul_one]

/-- The finite cycle obtained from one full split rotation period. -/
noncomputable def splitRotationCycle (w s : Fˣ) : Finset (NormalizedPoint F) := by
  classical
  exact (Finset.range (orderOf w)).image fun n =>
    (normalizedRotate1^[n]) (splitFiberPoint w s)

/-- The split rotation cycle has exactly the multiplicative order of its eigenvalue. -/
theorem splitRotationCycle_card (w s : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    (splitRotationCycle w s).card = orderOf w := by
  classical
  let f : ℕ → NormalizedPoint F := fun n =>
    (normalizedRotate1^[n]) (splitFiberPoint w s)
  have hinjective : Set.InjOn f (Finset.range (orderOf w)) := by
    intro n hn m hm hequal
    have hn' : n < orderOf w := by simpa using hn
    have hm' : m < orderOf w := by simpa using hm
    change (normalizedRotate1^[n]) (splitFiberPoint w s) =
      (normalizedRotate1^[m]) (splitFiberPoint w s) at hequal
    rw [iterate_normalizedRotate1_splitFiberPoint,
      iterate_normalizedRotate1_splitFiberPoint] at hequal
    have hcoordinate := congrArg (splitFiberFirstEigenCoordinate w) hequal
    rw [splitFiberFirstEigenCoordinate_point w (s * w ^ n) hw,
      splitFiberFirstEigenCoordinate_point w (s * w ^ m) hw] at hcoordinate
    have hpowers : w ^ n = w ^ m := by
      have hunit : s * w ^ n = s * w ^ m := by
        apply Units.ext
        simpa using hcoordinate
      exact mul_left_cancel hunit
    exact pow_injOn_Iio_orderOf hn' hm' hpowers
  calc
    (splitRotationCycle w s).card = ((Finset.range (orderOf w)).image f).card := by
      rfl
    _ = (Finset.range (orderOf w)).card := Finset.card_image_iff.mpr hinjective
    _ = orderOf w := Finset.card_range _

/-- Replacing the eigenvalue order by the already-proved matrix rotation order connects the
explicit split cycle to the project's canonical `rotationOrder`. -/
theorem splitRotationCycle_card_eq_rotationOrder
    (w s : Fˣ) (hw : (w : F) ^ 2 ≠ 1) :
    (splitRotationCycle w s).card = rotationOrder (splitTorusTrace w) := by
  rw [splitRotationCycle_card w s hw, rotationOrder_splitTorusTrace w hw]

/-- Consequently a finite split fiber with nonzero trace has exactly one fewer point than the
base field. -/
theorem splitFiber_card
    [Finite F] (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1)
    (htrace : splitTorusTrace w ≠ 0) :
    Nat.card ↑(normalizedFiber1 (splitTorusTrace w)) = Nat.card F - 1 := by
  rw [← Nat.card_units]
  exact Nat.card_congr (splitFiberEquiv w hw htrace).symm

theorem splitNormalizedFiber_zmod_natCard
    (p : ℕ) [Fact p.Prime] (w : (ZMod p)ˣ)
    (hw : (w : ZMod p) ^ 2 ≠ 1) (htrace : splitTorusTrace w ≠ 0) :
    Nat.card ↑(normalizedFiber1 (splitTorusTrace w)) = p - 1 := by
  rw [splitFiber_card w hw htrace, Nat.card_zmod]

end SplitFiber

section TraceZeroObstruction

/-- The punctured normalized fiber used by the paper's conic sections. -/
def normalizedPuncturedFiber1 {R : Type u} [CommRing R] (a : R) :
    Set (NormalizedPoint R) :=
  normalizedFiber1 a \ {normalizedOrigin}

/-- A computable finite presentation of a normalized fixed-coordinate fiber. -/
def normalizedFiber1Finset (R : Type u) [CommRing R] [Fintype R] [DecidableEq R]
    (a : R) : Finset (NormalizedPoint R) :=
  Finset.univ.filter fun x => normalizedPolynomial x = 0 ∧ x.u1 = a

/-- A computable finite presentation of a punctured normalized fixed-coordinate fiber. -/
def normalizedPuncturedFiber1Finset
    (R : Type u) [CommRing R] [Fintype R] [DecidableEq R] (a : R) :
    Finset (NormalizedPoint R) :=
  (normalizedFiber1Finset R a).erase normalizedOrigin

@[simp]
theorem mem_normalizedFiber1Finset_iff
    {R : Type u} [CommRing R] [Fintype R] [DecidableEq R]
    {a : R} {x : NormalizedPoint R} :
    x ∈ normalizedFiber1Finset R a ↔ x ∈ normalizedFiber1 a := by
  simp [normalizedFiber1Finset, normalizedFiber1, IsNormalizedMarkoff]

@[simp]
theorem mem_normalizedPuncturedFiber1Finset_iff
    {R : Type u} [CommRing R] [Fintype R] [DecidableEq R]
    {a : R} {x : NormalizedPoint R} :
    x ∈ normalizedPuncturedFiber1Finset R a ↔ x ∈ normalizedPuncturedFiber1 a := by
  simp [normalizedPuncturedFiber1Finset, normalizedPuncturedFiber1, and_comm]

/-- The set-theoretic and computable-finset presentations have the same elements. -/
def normalizedPuncturedFiber1EquivFinset
    (R : Type u) [CommRing R] [Fintype R] [DecidableEq R] (a : R) :
    ↑(normalizedPuncturedFiber1 a) ≃ ↑(normalizedPuncturedFiber1Finset R a) where
  toFun x := ⟨x, mem_normalizedPuncturedFiber1Finset_iff.mpr x.property⟩
  invFun x := ⟨x, mem_normalizedPuncturedFiber1Finset_iff.mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At the split semisimple trace zero over `ZMod 5`, the full affine fiber has nine points. -/
theorem normalizedFiber1_zero_zmod_five_card :
    (normalizedFiber1Finset (ZMod 5) 0).card = 9 := by
  decide

/-- Removing the singular origin leaves eight points, not the four predicted by the paper's
uniform `p - 1` assertion for split semisimple fibers. -/
theorem normalizedPuncturedFiber1_zero_zmod_five_card :
    (normalizedPuncturedFiber1Finset (ZMod 5) 0).card = 8 := by
  decide

/-- Thus the trace-zero punctured fiber cannot be equivalent to the multiplicative group, which
has four elements.  This is the exact obstruction requiring the nonzero-trace hypothesis above. -/
theorem no_split_torus_equiv_normalizedPuncturedFiber1_zero_zmod_five :
    ¬ Nonempty ((ZMod 5)ˣ ≃ ↑(normalizedPuncturedFiber1 (0 : ZMod 5))) := by
  rintro ⟨e⟩
  let e' := e.trans (normalizedPuncturedFiber1EquivFinset (ZMod 5) 0)
  have hcard := Fintype.card_congr e'
  have hunits : Fintype.card (ZMod 5)ˣ = 4 := by decide
  rw [hunits, Fintype.card_coe,
    normalizedPuncturedFiber1_zero_zmod_five_card] at hcard
  omega

end TraceZeroObstruction

section QuadraticNormFiber

variable (p : ℕ) [Fact p.Prime]

/-- The norm homomorphism on units of the canonical quadratic extension. -/
noncomputable def quadraticNormUnitsHom :
    (quadraticFiniteField p)ˣ →* (ZMod p)ˣ :=
  Units.map (Algebra.norm (ZMod p) (S := quadraticFiniteField p))

/-- A nonzero norm fiber in the canonical quadratic extension. -/
noncomputable def quadraticNormFiber (k : (ZMod p)ˣ) :
    Set (quadraticFiniteField p)ˣ :=
  quadraticNormUnitsHom p ⁻¹' {k}

/-- Every nonzero norm fiber is a torsor for the concrete quadratic norm-one torus. -/
noncomputable def quadraticNormFiberEquivNormOne (k : (ZMod p)ˣ) :
    ↑(quadraticNormFiber p k) ≃ quadraticNormOneTorus p := by
  change ↑((quadraticNormUnitsHom p) ⁻¹' {k}) ≃
    (quadraticNormUnitsHom p).ker
  exact MonoidHom.fiberEquivKerOfSurjective
    (FiniteField.unitsMap_norm_surjective (ZMod p) (quadraticFiniteField p)) k

/-- The equality-form fiber used by `Equiv.sigmaFiberEquiv` is the same norm torsor. -/
noncomputable def quadraticNormEquationFiberEquivNormOne (k : (ZMod p)ˣ) :
    {s : (quadraticFiniteField p)ˣ // quadraticNormUnitsHom p s = k} ≃
      quadraticNormOneTorus p := by
  let equationToSet :
      {s : (quadraticFiniteField p)ˣ // quadraticNormUnitsHom p s = k} ≃
        ↑(quadraticNormFiber p k) :=
    { toFun := fun s => ⟨s, by
        change quadraticNormUnitsHom p s ∈ ({k} : Set (ZMod p)ˣ)
        simpa using s.property⟩
      invFun := fun s => ⟨s, by
        have hs := s.property
        change quadraticNormUnitsHom p s ∈ ({k} : Set (ZMod p)ˣ) at hs
        simpa using hs⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact equationToSet.trans (quadraticNormFiberEquivNormOne p k)

/-- The multiplicative group of the quadratic field is a product of the base-field units and
the norm-one torus, after making the canonical finite-field norm-fiber choices. -/
noncomputable def quadraticUnitsEquivBaseUnitsProdNormOne :
    (quadraticFiniteField p)ˣ ≃ (ZMod p)ˣ × quadraticNormOneTorus p :=
  (Equiv.sigmaFiberEquiv (quadraticNormUnitsHom p)).symm.trans <|
    Equiv.sigmaEquivProdOfEquiv fun k => quadraticNormEquationFiberEquivNormOne p k

/-- The concrete quadratic norm-one torus has exactly `p + 1` elements. -/
theorem quadraticNormOneTorus_natCard : Nat.card (quadraticNormOneTorus p) = p + 1 := by
  have hcard := Nat.card_congr (quadraticUnitsEquivBaseUnitsProdNormOne p)
  rw [Nat.card_units, Nat.card_prod, Nat.card_units,
    GaloisField.card p (n := 2) (by norm_num), Nat.card_zmod] at hcard
  have hpPositive : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  apply Nat.eq_of_mul_eq_mul_left hpPositive
  calc
    (p - 1) * Nat.card (quadraticNormOneTorus p) = p ^ 2 - 1 := hcard.symm
    _ = (p - 1) * (p + 1) := by
      rw [show p ^ 2 - 1 = (p + 1) * (p - 1) by
        simpa using (sq_tsub_sq p 1)]
      ring

/-- Every nonzero quadratic norm fiber has `p + 1` points. -/
theorem quadraticNormFiber_natCard (k : (ZMod p)ˣ) :
    Nat.card ↑(quadraticNormFiber p k) = p + 1 := by
  rw [Nat.card_congr (quadraticNormFiberEquivNormOne p k)]
  exact quadraticNormOneTorus_natCard p

private theorem quadraticFiniteField_finrank :
    Module.finrank (ZMod p) (quadraticFiniteField p) = 2 :=
  GaloisField.finrank p (n := 2) (by norm_num)

/-- The quadratic field trace is the sum of an element and its `p`-power Frobenius conjugate. -/
theorem algebraMap_quadraticTrace (x : quadraticFiniteField p) :
    algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p) x) =
      x + x ^ p := by
  have h := FiniteField.algebraMap_trace_eq_sum_pow
    (ZMod p) (quadraticFiniteField p) x
  rw [quadraticFiniteField_finrank p, Nat.card_zmod] at h
  simpa [Finset.sum_range_succ] using h

/-- The quadratic field norm is the product of an element and its `p`-power Frobenius
conjugate. -/
theorem algebraMap_quadraticNorm (x : quadraticFiniteField p) :
    algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.norm (ZMod p) x) = x * x ^ p := by
  have h := FiniteField.algebraMap_norm_eq_prod_pow
    (ZMod p) (quadraticFiniteField p) x
  rw [quadraticFiniteField_finrank p, Nat.card_zmod] at h
  simpa [Finset.prod_range_succ] using h

/-- Frobenius acts on a norm-one eigenvalue by inversion. -/
theorem quadraticNormOne_frobenius_eq_inv (w : quadraticNormOneTorus p) :
    (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ p) =
      (((w : (quadraticFiniteField p)ˣ)⁻¹ : (quadraticFiniteField p)ˣ) :
        quadraticFiniteField p) := by
  have hwNorm : Algebra.norm (ZMod p)
      ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) = 1 := by
    exact congrArg Units.val w.property
  have hnorm := algebraMap_quadraticNorm p
    ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)
  rw [hwNorm, map_one] at hnorm
  have hscalar :
      (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ p) =
        (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)⁻¹) := by
    apply (mul_eq_one_iff_eq_inv₀
      (show ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ≠ 0 by
        exact Units.ne_zero _)).mp
    rw [mul_comm]
    exact hnorm.symm
  simpa using hscalar

/-- Frobenius on a nonzero norm fiber is multiplication by the prescribed norm followed by
inversion. -/
theorem quadraticNormFiber_frobenius_eq_norm_mul_inv
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k)) :
    ((s.1 : quadraticFiniteField p) ^ p) =
      algebraMap (ZMod p) (quadraticFiniteField p) (k : ZMod p) *
        ((s.1 : quadraticFiniteField p)⁻¹) := by
  have hsNormUnits : quadraticNormUnitsHom p s.1 = k := by
    have hs := s.property
    change quadraticNormUnitsHom p s.1 ∈ ({k} : Set (ZMod p)ˣ) at hs
    simpa only [Set.mem_singleton_iff] using hs
  have hsNorm : Algebra.norm (ZMod p) (s.1 : quadraticFiniteField p) = (k : ZMod p) :=
    congrArg Units.val hsNormUnits
  have hnorm := algebraMap_quadraticNorm p (s.1 : quadraticFiniteField p)
  rw [hsNorm] at hnorm
  field_simp
  simpa [mul_comm] using hnorm.symm

/-- The scalar `t²/(t²-4)` controlling either eigen-coordinate parametrization. -/
noncomputable def quadraticFiberProduct (t : ZMod p) : ZMod p :=
  t ^ 2 / (t ^ 2 - 4)

theorem quadraticFiberProduct_ne_zero (t : ZMod p)
    (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0) : quadraticFiberProduct p t ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 ht0) (sub_ne_zero.mpr ht)

/-- The nonzero scalar as a unit, used to index its norm fiber. -/
noncomputable def quadraticFiberProductUnit
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0) :
    (ZMod p)ˣ :=
  Units.mk0 (quadraticFiberProduct p t) (quadraticFiberProduct_ne_zero p t ht ht0)

/-- The norm fiber occurring in the paper's nonsplit conic parametrization. -/
noncomputable def quadraticConicNormFiber
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0) :
    Set (quadraticFiniteField p)ˣ :=
  quadraticNormFiber p (quadraticFiberProductUnit p t ht ht0)

/-- Coordinatewise scalar extension of a normalized point. -/
noncomputable def algebraMapNormalizedPoint (x : NormalizedPoint (ZMod p)) :
    NormalizedPoint (quadraticFiniteField p) :=
  ⟨algebraMap (ZMod p) (quadraticFiniteField p) x.u1,
    algebraMap (ZMod p) (quadraticFiniteField p) x.u2,
    algebraMap (ZMod p) (quadraticFiniteField p) x.u3⟩

theorem normalizedPolynomial_algebraMapNormalizedPoint
    (x : NormalizedPoint (ZMod p)) :
    normalizedPolynomial (algebraMapNormalizedPoint p x) =
      algebraMap (ZMod p) (quadraticFiniteField p) (normalizedPolynomial x) := by
  simp [normalizedPolynomial, algebraMapNormalizedPoint]

/-- Trace coordinates turn a point of the prescribed norm fiber into a normalized base-field
point. -/
noncomputable def quadraticNormFiberPoint
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) : NormalizedPoint (ZMod p) :=
  ⟨t,
    Algebra.trace (ZMod p) (quadraticFiniteField p)
      (s.1 : quadraticFiniteField p),
    Algebra.trace (ZMod p) (quadraticFiniteField p)
      ((s.1 : quadraticFiniteField p) *
        ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p))⟩

theorem algebraMap_quadraticFiberProduct
    (t : ZMod p) (w : quadraticNormOneTorus p)
    (htrace : quadraticNormOneTrace p w = t) :
    algebraMap (ZMod p) (quadraticFiniteField p) (quadraticFiberProduct p t) =
      splitFiberProduct (w : (quadraticFiniteField p)ˣ) := by
  have htraceExtension :
      algebraMap (ZMod p) (quadraticFiniteField p) t =
        splitTorusTrace (w : (quadraticFiniteField p)ˣ) := by
    rw [← htrace]
    exact algebraMap_quadraticNormOneTrace p w
  simp [quadraticFiberProduct, splitFiberProduct, htraceExtension, map_ofNat]

theorem algebraMap_quadraticNormFiberPoint
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    algebraMapNormalizedPoint p (quadraticNormFiberPoint p t ht ht0 w s) =
      splitFiberPoint (w : (quadraticFiniteField p)ˣ) s.1 := by
  let k := quadraticFiberProductUnit p t ht ht0
  have hsFrobenius := quadraticNormFiber_frobenius_eq_norm_mul_inv p k s
  have hwFrobenius := quadraticNormOne_frobenius_eq_inv p w
  have hk :
      algebraMap (ZMod p) (quadraticFiniteField p) (k : ZMod p) =
        splitFiberProduct (w : (quadraticFiniteField p)ˣ) := by
    exact algebraMap_quadraticFiberProduct p t w htrace
  ext
  · change algebraMap (ZMod p) (quadraticFiniteField p) t =
      splitTorusTrace (w : (quadraticFiniteField p)ˣ)
    rw [← htrace]
    exact algebraMap_quadraticNormOneTrace p w
  · change algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
          (s.1 : quadraticFiniteField p)) = _
    rw [algebraMap_quadraticTrace, hsFrobenius, hk]
    simp [splitFiberPoint]
  · change algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
          ((s.1 : quadraticFiniteField p) *
            ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p))) = _
    rw [algebraMap_quadraticTrace, mul_pow, hsFrobenius, hwFrobenius, hk]
    simp [splitFiberPoint]

theorem quadraticNormFiberPoint_mem
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    quadraticNormFiberPoint p t ht ht0 w s ∈ normalizedFiber1 t := by
  constructor
  · change normalizedPolynomial (quadraticNormFiberPoint p t ht ht0 w s) = 0
    apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
    rw [← normalizedPolynomial_algebraMapNormalizedPoint]
    rw [algebraMap_quadraticNormFiberPoint p t ht ht0 w htrace s]
    rw [map_zero]
    simpa only [IsNormalizedMarkoff] using
      (splitFiberPoint_mem (w : (quadraticFiniteField p)ˣ) s.1 hw).1
  · rfl

/-- Multiplication by a norm-one element preserves every nonzero norm fiber. -/
noncomputable def quadraticNormFiberMulNormOne
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k))
    (g : quadraticNormOneTorus p) : ↑(quadraticNormFiber p k) := by
  refine ⟨s.1 * (g : (quadraticFiniteField p)ˣ), ?_⟩
  have hs := s.property
  change quadraticNormUnitsHom p s.1 ∈ ({k} : Set (ZMod p)ˣ) at hs
  have hg := g.property
  change quadraticNormUnitsHom p (g : (quadraticFiniteField p)ˣ) = 1 at hg
  change quadraticNormUnitsHom p (s.1 * (g : (quadraticFiniteField p)ˣ)) ∈
    ({k} : Set (ZMod p)ˣ)
  rw [Set.mem_singleton_iff, map_mul, Set.mem_singleton_iff.mp hs, hg, mul_one]

theorem algebraMapNormalizedPoint_injective :
    Function.Injective (algebraMapNormalizedPoint p) := by
  intro x y h
  ext
  · apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
    exact congrArg NormalizedPoint.u1 h
  · apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
    exact congrArg NormalizedPoint.u2 h
  · apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
    exact congrArg NormalizedPoint.u3 h

theorem algebraMapNormalizedPoint_normalizedRotate1 (x : NormalizedPoint (ZMod p)) :
    algebraMapNormalizedPoint p (normalizedRotate1 x) =
      normalizedRotate1 (algebraMapNormalizedPoint p x) := by
  ext <;> simp [algebraMapNormalizedPoint, normalizedRotate1]

theorem algebraMap_zmod_pow_card (a : ZMod p) :
    (algebraMap (ZMod p) (quadraticFiniteField p) a) ^ p =
      algebraMap (ZMod p) (quadraticFiniteField p) a := by
  rw [← map_pow, ZMod.pow_card]

/-- A base-field fiber point, viewed on the diagonalized fiber in the quadratic extension. -/
noncomputable def algebraMapNormalizedFiberPoint
    (t : ZMod p) (w : quadraticNormOneTorus p)
    (htrace : quadraticNormOneTrace p w = t)
    (x : ↑(normalizedFiber1 t)) :
    ↑(normalizedFiber1 (splitTorusTrace (w : (quadraticFiniteField p)ˣ))) := by
  refine ⟨algebraMapNormalizedPoint p x, ?_⟩
  constructor
  · change normalizedPolynomial (algebraMapNormalizedPoint p x) = 0
    rw [normalizedPolynomial_algebraMapNormalizedPoint]
    rw [x.property.1]
    exact map_zero _
  · change algebraMap (ZMod p) (quadraticFiniteField p) x.val.u1 =
      splitTorusTrace (w : (quadraticFiniteField p)ˣ)
    rw [x.property.2, ← htrace]
    exact algebraMap_quadraticNormOneTrace p w

/-- For a base-field point, Frobenius exchanges its two eigen-coordinates in the quadratic
extension. -/
theorem quadraticFiberFirstEigenCoordinate_frobenius
    (t : ZMod p) (w : quadraticNormOneTorus p)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (x : ↑(normalizedFiber1 t)) :
    (splitFiberFirstEigenCoordinate (w : (quadraticFiniteField p)ˣ)
        (algebraMapNormalizedPoint p x)) ^ p =
      splitFiberSecondEigenCoordinate (w : (quadraticFiniteField p)ˣ)
        (algebraMapNormalizedPoint p x) := by
  have hwFrobenius := quadraticNormOne_frobenius_eq_inv p w
  have hwInverseFrobenius :
      ((((w : (quadraticFiniteField p)ˣ)⁻¹ : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p) ^ p) =
        ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) := by
    have hwFrobeniusScalar :
        (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ p) =
          (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)⁻¹) := by
      simpa using hwFrobenius
    have hscalar :
        ((((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)⁻¹) ^ p) =
          ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) := by
      rw [inv_pow, hwFrobeniusScalar, inv_inv]
    simpa using hscalar
  rw [splitFiberFirstEigenCoordinate, splitFiberSecondEigenCoordinate, div_pow,
    sub_pow_char, mul_pow, sub_pow_char]
  change
    ((algebraMap (ZMod p) (quadraticFiniteField p) x.val.u3) ^ p -
        ((((w : (quadraticFiniteField p)ˣ)⁻¹ : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p) ^ p) *
          (algebraMap (ZMod p) (quadraticFiniteField p) x.val.u2) ^ p) /
      (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ p -
        ((((w : (quadraticFiniteField p)ˣ)⁻¹ : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p) ^ p)) = _
  rw [algebraMap_zmod_pow_card, algebraMap_zmod_pow_card,
    hwFrobenius, hwInverseFrobenius]
  have hdifference := splitEigenvalueDifference_ne_zero
    (w : (quadraticFiniteField p)ˣ) hw
  simp only [algebraMapNormalizedPoint]
  rw [show (((w : (quadraticFiniteField p)ˣ)⁻¹ : (quadraticFiniteField p)ˣ) :
        quadraticFiniteField p) -
      ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) =
      -(((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) -
        (((w : (quadraticFiniteField p)ˣ)⁻¹ : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p)) by ring]
  field_simp [hdifference]
  ring

/-- Recover the first extension-field eigen-coordinate from a base-field conic point and prove
that it lies in the prescribed norm fiber. -/
noncomputable def quadraticNormFiberParameter
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (x : ↑(normalizedFiber1 t)) :
    ↑(quadraticConicNormFiber p t ht ht0) := by
  let extensionPoint := algebraMapNormalizedFiberPoint p t w htrace x
  have htraceExtension :
      splitTorusTrace (w : (quadraticFiniteField p)ˣ) ≠ 0 := by
    rw [← algebraMap_quadraticNormOneTrace p w, htrace]
    simpa using (algebraMap (ZMod p) (quadraticFiniteField p)).injective.ne ht0
  let parameterValue := splitFiberFirstEigenCoordinate
    (w : (quadraticFiniteField p)ˣ) extensionPoint
  have hparameterValue : parameterValue ≠ 0 :=
    splitFiberFirstEigenCoordinate_ne_zero
      (w : (quadraticFiniteField p)ˣ) hw htraceExtension extensionPoint
  let parameterUnit : (quadraticFiniteField p)ˣ :=
    Units.mk0 parameterValue hparameterValue
  refine ⟨parameterUnit, ?_⟩
  change parameterUnit ∈ quadraticNormFiber p (quadraticFiberProductUnit p t ht ht0)
  change quadraticNormUnitsHom p parameterUnit ∈
    ({quadraticFiberProductUnit p t ht ht0} : Set (ZMod p)ˣ)
  rw [Set.mem_singleton_iff]
  apply Units.ext
  change Algebra.norm (ZMod p) parameterValue = quadraticFiberProduct p t
  apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
  rw [algebraMap_quadraticNorm]
  rw [show parameterValue ^ p =
      splitFiberSecondEigenCoordinate (w : (quadraticFiniteField p)ˣ)
        (algebraMapNormalizedPoint p x) by
    exact quadraticFiberFirstEigenCoordinate_frobenius p t w hw x]
  rw [algebraMap_quadraticFiberProduct p t w htrace]
  exact splitFiberEigenCoordinates_product
    (w : (quadraticFiniteField p)ˣ) hw extensionPoint

theorem quadraticNormFiberParameter_point
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    quadraticNormFiberParameter p t ht ht0 w htrace hw
        ⟨quadraticNormFiberPoint p t ht ht0 w s,
          quadraticNormFiberPoint_mem p t ht ht0 w htrace hw s⟩ = s := by
  apply Subtype.ext
  apply Units.ext
  change splitFiberFirstEigenCoordinate (w : (quadraticFiniteField p)ˣ)
      (algebraMapNormalizedPoint p (quadraticNormFiberPoint p t ht ht0 w s)) =
    (s.1 : quadraticFiniteField p)
  rw [algebraMap_quadraticNormFiberPoint p t ht ht0 w htrace s]
  exact splitFiberFirstEigenCoordinate_point
    (w : (quadraticFiniteField p)ˣ) s.1 hw

theorem quadraticNormFiberPoint_parameter
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (x : ↑(normalizedFiber1 t)) :
    quadraticNormFiberPoint p t ht ht0 w
        (quadraticNormFiberParameter p t ht ht0 w htrace hw x) = x := by
  apply algebraMapNormalizedPoint_injective p
  erw [algebraMap_quadraticNormFiberPoint p t ht ht0 w htrace]
  let extensionPoint := algebraMapNormalizedFiberPoint p t w htrace x
  have htraceExtension :
      splitTorusTrace (w : (quadraticFiniteField p)ˣ) ≠ 0 := by
    rw [← algebraMap_quadraticNormOneTrace p w, htrace]
    simpa using (algebraMap (ZMod p) (quadraticFiniteField p)).injective.ne ht0
  have hright := (splitFiberEquiv
    (w : (quadraticFiniteField p)ˣ) hw htraceExtension).apply_symm_apply extensionPoint
  exact congrArg Subtype.val hright

/-- The nonsplit nonzero normalized fiber is explicitly equivalent to its quadratic norm fiber. -/
noncomputable def quadraticNormFiberEquiv
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1)) :
    ↑(quadraticConicNormFiber p t ht ht0) ≃ ↑(normalizedFiber1 t) where
  toFun s := ⟨quadraticNormFiberPoint p t ht ht0 w s,
    quadraticNormFiberPoint_mem p t ht ht0 w htrace hw s⟩
  invFun := quadraticNormFiberParameter p t ht ht0 w htrace hw
  left_inv := quadraticNormFiberParameter_point p t ht ht0 w htrace hw
  right_inv x := by
    apply Subtype.ext
    exact quadraticNormFiberPoint_parameter p t ht ht0 w htrace hw x

/-- Consequently the nonsplit nonzero normalized fiber has exactly `p + 1` points. -/
theorem nonsplitNormalizedFiber_natCard
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1)) :
    Nat.card ↑(normalizedFiber1 t) = p + 1 := by
  rw [← Nat.card_congr (quadraticNormFiberEquiv p t ht ht0 w htrace hw)]
  exact quadraticNormFiber_natCard p (quadraticFiberProductUnit p t ht ht0)

/-- On the nonsplit norm-fiber parametrization, normalized rotation is multiplication by its
norm-one eigenvalue. -/
theorem normalizedRotate1_quadraticNormFiberPoint
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    normalizedRotate1 (quadraticNormFiberPoint p t ht ht0 w s) =
      quadraticNormFiberPoint p t ht ht0 w
        (quadraticNormFiberMulNormOne p (quadraticFiberProductUnit p t ht ht0) s w) := by
  apply algebraMapNormalizedPoint_injective p
  rw [algebraMapNormalizedPoint_normalizedRotate1]
  rw [algebraMap_quadraticNormFiberPoint p t ht ht0 w htrace s]
  erw [algebraMap_quadraticNormFiberPoint p t ht ht0 w htrace]
  rw [normalizedRotate1_splitFiberPoint]
  rfl

theorem quadraticNormFiberMulNormOne_assoc
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k))
    (g h : quadraticNormOneTorus p) :
    quadraticNormFiberMulNormOne p k (quadraticNormFiberMulNormOne p k s g) h =
      quadraticNormFiberMulNormOne p k s (g * h) := by
  apply Subtype.ext
  simp [quadraticNormFiberMulNormOne, mul_assoc]

theorem quadraticNormFiberMulNormOne_one
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k)) :
    quadraticNormFiberMulNormOne p k s 1 = s := by
  apply Subtype.ext
  simp [quadraticNormFiberMulNormOne]

theorem quadraticNormFiberMulNormOne_pow
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k))
    (g : quadraticNormOneTorus p) (n : ℕ) :
    (quadraticNormFiberMulNormOne p k s (g ^ n)).1 =
      s.1 * (g : (quadraticFiniteField p)ˣ) ^ n := by
  rfl

theorem quadraticNormFiberPoint_injective
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1)) :
    Function.Injective (quadraticNormFiberPoint p t ht ht0 w) := by
  intro s r hpoint
  have hextension := congrArg (algebraMapNormalizedPoint p) hpoint
  rw [algebraMap_quadraticNormFiberPoint p t ht ht0 w htrace s,
    algebraMap_quadraticNormFiberPoint p t ht ht0 w htrace r] at hextension
  have hcoordinate := congrArg
    (splitFiberFirstEigenCoordinate (w : (quadraticFiniteField p)ˣ)) hextension
  rw [splitFiberFirstEigenCoordinate_point (w : (quadraticFiniteField p)ˣ) s.1 hw,
    splitFiberFirstEigenCoordinate_point (w : (quadraticFiniteField p)ˣ) r.1 hw] at hcoordinate
  apply Subtype.ext
  apply Units.ext
  exact hcoordinate

theorem iterate_normalizedRotate1_quadraticNormFiberPoint
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) (n : ℕ) :
    (normalizedRotate1^[n]) (quadraticNormFiberPoint p t ht ht0 w s) =
      quadraticNormFiberPoint p t ht ht0 w
        (quadraticNormFiberMulNormOne p (quadraticFiberProductUnit p t ht ht0) s (w ^ n)) := by
  induction n with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      congr 1
      exact (quadraticNormFiberMulNormOne_one p _ s).symm
  | succ n ih =>
      erw [Function.iterate_succ_apply', ih,
        normalizedRotate1_quadraticNormFiberPoint p t ht ht0 w htrace]
      congr 1
      erw [quadraticNormFiberMulNormOne_assoc, pow_succ]

theorem iterate_normalizedRotate1_quadraticNormFiberPoint_eq_self_iff
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (s : ↑(quadraticConicNormFiber p t ht ht0)) (n : ℕ) :
    (normalizedRotate1^[n]) (quadraticNormFiberPoint p t ht ht0 w s) =
        quadraticNormFiberPoint p t ht ht0 w s ↔ w ^ n = 1 := by
  rw [iterate_normalizedRotate1_quadraticNormFiberPoint p t ht ht0 w htrace]
  constructor
  · intro hpoint
    have hparameter := quadraticNormFiberPoint_injective p t ht ht0 w htrace hw hpoint
    have hunit : s.1 * ((w ^ n : quadraticNormOneTorus p) :
        (quadraticFiniteField p)ˣ) = s.1 * 1 := by
      simpa [quadraticNormFiberMulNormOne] using congrArg Subtype.val hparameter
    apply Subtype.ext
    exact mul_left_cancel hunit
  · intro hpower
    erw [hpower, quadraticNormFiberMulNormOne_one]

/-- One full nonsplit rotation cycle, represented in the base-field conic. -/
noncomputable def quadraticNormFiberRotationCycle
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    Finset (NormalizedPoint (ZMod p)) := by
  classical
  exact (Finset.range (orderOf w)).image fun n =>
    (normalizedRotate1^[n]) (quadraticNormFiberPoint p t ht ht0 w s)

theorem quadraticNormFiberRotationCycle_card
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    (quadraticNormFiberRotationCycle p t ht ht0 w s).card = orderOf w := by
  classical
  let f : ℕ → NormalizedPoint (ZMod p) := fun n =>
    (normalizedRotate1^[n]) (quadraticNormFiberPoint p t ht ht0 w s)
  have hinjective : Set.InjOn f (Finset.range (orderOf w)) := by
    intro n hn m hm hequal
    have hn' : n < orderOf w := by simpa using hn
    have hm' : m < orderOf w := by simpa using hm
    change (normalizedRotate1^[n]) (quadraticNormFiberPoint p t ht ht0 w s) =
      (normalizedRotate1^[m]) (quadraticNormFiberPoint p t ht ht0 w s) at hequal
    rw [iterate_normalizedRotate1_quadraticNormFiberPoint p t ht ht0 w htrace,
      iterate_normalizedRotate1_quadraticNormFiberPoint p t ht ht0 w htrace] at hequal
    have hparameter := quadraticNormFiberPoint_injective p t ht ht0 w htrace hw hequal
    have hpowers : w ^ n = w ^ m := by
      apply Subtype.ext
      have hunit : s.1 * ((w ^ n : quadraticNormOneTorus p) :
          (quadraticFiniteField p)ˣ) =
          s.1 * ((w ^ m : quadraticNormOneTorus p) : (quadraticFiniteField p)ˣ) :=
        by simpa [quadraticNormFiberMulNormOne] using congrArg Subtype.val hparameter
      exact mul_left_cancel hunit
    exact pow_injOn_Iio_orderOf hn' hm' hpowers
  calc
    (quadraticNormFiberRotationCycle p t ht ht0 w s).card =
        ((Finset.range (orderOf w)).image f).card := by rfl
    _ = (Finset.range (orderOf w)).card := Finset.card_image_iff.mpr hinjective
    _ = orderOf w := Finset.card_range _

theorem quadraticNormFiberRotationCycle_card_eq_rotationOrder
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    (quadraticNormFiberRotationCycle p t ht ht0 w s).card = rotationOrder t := by
  rw [quadraticNormFiberRotationCycle_card p t ht ht0 w htrace hw s]
  rw [← htrace, rotationOrder_quadraticNormOneTrace p w hw]

end QuadraticNormFiber

section RotationCycles

variable {F : Type u} [Field F]

/-- The canonical finite cycle cut out by one full matrix rotation period. -/
noncomputable def normalizedRotationCycle (t : F) (x : NormalizedPoint F) :
    Finset (NormalizedPoint F) := by
  classical
  exact (Finset.range (rotationOrder t)).image fun n => (normalizedRotate1^[n]) x

/-- Every point of a nonzero split semisimple fiber has orbit-cycle cardinality equal to the
canonical matrix rotation order. -/
theorem normalizedRotationCycle_card_split
    (w : Fˣ) (hw : (w : F) ^ 2 ≠ 1) (htrace : splitTorusTrace w ≠ 0)
    (x : ↑(normalizedFiber1 (splitTorusTrace w))) :
    (normalizedRotationCycle (splitTorusTrace w) x).card =
      rotationOrder (splitTorusTrace w) := by
  let s := (splitFiberEquiv w hw htrace).symm x
  have hx : splitFiberPoint w s = x :=
    congrArg Subtype.val ((splitFiberEquiv w hw htrace).apply_symm_apply x)
  simpa [normalizedRotationCycle, splitRotationCycle, hx,
    rotationOrder_splitTorusTrace w hw] using
    splitRotationCycle_card w s hw

end RotationCycles

section QuadraticRotationCycles

variable (p : ℕ) [Fact p.Prime]

/-- Every point of a nonzero nonsplit semisimple fiber has orbit-cycle cardinality equal to the
canonical matrix rotation order. -/
theorem normalizedRotationCycle_card_nonsplit
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (w : quadraticNormOneTorus p) (htrace : quadraticNormOneTrace p w = t)
    (hw : (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1))
    (x : ↑(normalizedFiber1 t)) :
    (normalizedRotationCycle t x).card = rotationOrder t := by
  let s := (quadraticNormFiberEquiv p t ht ht0 w htrace hw).symm x
  have hx : quadraticNormFiberPoint p t ht ht0 w s = x :=
    congrArg Subtype.val
      ((quadraticNormFiberEquiv p t ht ht0 w htrace hw).apply_symm_apply x)
  have horder : rotationOrder t = orderOf w := by
    rw [← htrace, rotationOrder_quadraticNormOneTrace p w hw]
  have hcycle : normalizedRotationCycle t x =
      quadraticNormFiberRotationCycle p t ht ht0 w s := by
    classical
    ext y
    simp [normalizedRotationCycle, quadraticNormFiberRotationCycle, hx, horder]
  rw [hcycle]
  exact quadraticNormFiberRotationCycle_card_eq_rotationOrder
    p t ht ht0 w htrace hw s

end QuadraticRotationCycles

section ClassifiedRotationCycles

/-- Every point of a nonzero nonparabolic normalized fiber has rotation-cycle cardinality equal
to the canonical matrix rotation order.  The split/nonsplit classification is consumed here to
obtain the explicit eigenvalue witness required by the two parametrization kernels. -/
theorem normalizedRotationCycle_card_of_nonzero_nonparabolic
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (x : ↑(normalizedFiber1 t)) :
    (normalizedRotationCycle t x).card = rotationOrder t := by
  rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨w, htrace, hw⟩ | ⟨w, htrace, hw⟩
  · let xw : ↑(normalizedFiber1 (splitTorusTrace w)) :=
      ⟨x.1, x.property.1, by simpa [htrace] using x.property.2⟩
    simpa [htrace, xw] using normalizedRotationCycle_card_split w hw
      (by simpa [htrace] using ht0) xw
  · exact normalizedRotationCycle_card_nonsplit p t ht ht0 w htrace hw x

end ClassifiedRotationCycles

section ParabolicRotationCycles

/-- An even number of trace-`-2` rotations stays on the same parabolic line and translates its
parameter by a multiple of `-4i`. -/
theorem iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo
    {R : Type u} [CommRing R] (k : ℕ) (i t : R) :
    (normalizedRotate1^[2 * k]) (parabolicLineAtNegTwo i t) =
      parabolicLineAtNegTwo i (t - (k : R) * (4 * i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega,
        Function.iterate_add_apply, ih]
      change normalizedRotate1
        (normalizedRotate1 (parabolicLineAtNegTwo i (t - (k : R) * (4 * i)))) = _
      rw [normalizedRotate1_twice_parabolicLineAtNegTwo]
      congr 1
      push_cast
      ring

/-- An odd number of trace-`-2` rotations lands on the opposite parabolic line. -/
theorem iterate_two_mul_add_one_normalizedRotate1_parabolicLineAtNegTwo
    {R : Type u} [CommRing R] (k : ℕ) (i t : R) :
    (normalizedRotate1^[2 * k + 1]) (parabolicLineAtNegTwo i t) =
      parabolicLineAtNegTwo (-i) (-(t - (k : R) * (4 * i)) + 2 * i) := by
  rw [Function.iterate_succ_apply',
    iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo,
    normalizedRotate1_parabolicLineAtNegTwo]

/-- Every point on either trace-`2` parabolic line has a full rotation cycle of cardinality
`p`, matching the separately computed unipotent matrix order. -/
theorem normalizedRotationCycle_card_parabolicLineAtTwo
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (i t : ZMod p) (hi : i ^ 2 = -1) :
    (normalizedRotationCycle (2 : ZMod p) (parabolicLineAtTwo i t)).card =
      rotationOrder (2 : ZMod p) := by
  classical
  let f : ℕ → NormalizedPoint (ZMod p) := fun n =>
    (normalizedRotate1^[n]) (parabolicLineAtTwo i t)
  have hi0 : i ≠ 0 := by
    intro hzero
    subst i
    norm_num at hi
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hstep : (2 : ZMod p) * i ≠ 0 := mul_ne_zero htwo hi0
  have hinjective : Set.InjOn f (Finset.range p) := by
    intro n hn m hm hequal
    have hn' : n < p := by simpa using hn
    have hm' : m < p := by simpa using hm
    change (normalizedRotate1^[n]) (parabolicLineAtTwo i t) =
      (normalizedRotate1^[m]) (parabolicLineAtTwo i t) at hequal
    rw [iterate_normalizedRotate1_parabolicLineAtTwo,
      iterate_normalizedRotate1_parabolicLineAtTwo] at hequal
    have hparameter := congrArg NormalizedPoint.u2 hequal
    change t + (n : ZMod p) * (2 * i) = t + (m : ZMod p) * (2 * i) at hparameter
    have hproducts : (n : ZMod p) * (2 * i) = (m : ZMod p) * (2 * i) := by
      exact add_left_cancel hparameter
    have hcasts : (n : ZMod p) = (m : ZMod p) :=
      mul_right_cancel₀ hstep hproducts
    rw [ZMod.natCast_eq_natCast_iff'] at hcasts
    simpa [Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt hm'] using hcasts
  have horder : rotationOrder (2 : ZMod p) = p := rotationOrder_two p
  have hcycle : normalizedRotationCycle (2 : ZMod p) (parabolicLineAtTwo i t) =
      (Finset.range p).image f := by
    ext y
    simp [normalizedRotationCycle, f, horder]
  calc
    (normalizedRotationCycle (2 : ZMod p) (parabolicLineAtTwo i t)).card =
        ((Finset.range p).image f).card := congrArg Finset.card hcycle
    _ = (Finset.range p).card := Finset.card_image_iff.mpr hinjective
    _ = p := Finset.card_range _
    _ = rotationOrder (2 : ZMod p) := horder.symm

/-- Every point on either trace-`-2` parabolic line has a full cycle of cardinality `2p`,
matching the separately computed matrix order. -/
theorem normalizedRotationCycle_card_parabolicLineAtNegTwo
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (i t : ZMod p) (hi : i ^ 2 = -1) :
    (normalizedRotationCycle (-2 : ZMod p) (parabolicLineAtNegTwo i t)).card =
      rotationOrder (-2 : ZMod p) := by
  classical
  let f : ℕ → NormalizedPoint (ZMod p) := fun n =>
    (normalizedRotate1^[n]) (parabolicLineAtNegTwo i t)
  have hi0 : i ≠ 0 := by
    intro hzero
    subst i
    norm_num at hi
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  have hfour : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = (2 : ZMod p) ^ 2 by norm_num]
    exact pow_ne_zero 2 htwo
  have hstep : (4 : ZMod p) * i ≠ 0 := mul_ne_zero hfour hi0
  have hdisjoint := parabolicLineAtNegTwo_disjoint i hstep
  have hinjective : Set.InjOn f (Finset.range (2 * p)) := by
    intro n hn m hm hequal
    have hn' : n < 2 * p := by simpa using hn
    have hm' : m < 2 * p := by simpa using hm
    rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
    · rcases m.even_or_odd' with ⟨l, rfl | rfl⟩
      · have hk : k < p := by omega
        have hl : l < p := by omega
        change (normalizedRotate1^[2 * k]) (parabolicLineAtNegTwo i t) =
          (normalizedRotate1^[2 * l]) (parabolicLineAtNegTwo i t) at hequal
        rw [iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo,
          iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo] at hequal
        have hparameter := congrArg NormalizedPoint.u2 hequal
        change t - (k : ZMod p) * (4 * i) =
          t - (l : ZMod p) * (4 * i) at hparameter
        have hproducts : (k : ZMod p) * (4 * i) = (l : ZMod p) * (4 * i) := by
          linear_combination -hparameter
        have hcasts : (k : ZMod p) = (l : ZMod p) :=
          mul_right_cancel₀ hstep hproducts
        rw [ZMod.natCast_eq_natCast_iff'] at hcasts
        have hkl : k = l := by
          simpa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] using hcasts
        omega
      · change (normalizedRotate1^[2 * k]) (parabolicLineAtNegTwo i t) =
          (normalizedRotate1^[2 * l + 1]) (parabolicLineAtNegTwo i t) at hequal
        rw [iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo,
          iterate_two_mul_add_one_normalizedRotate1_parabolicLineAtNegTwo] at hequal
        exfalso
        exact Set.disjoint_left.mp hdisjoint
          ⟨_, rfl⟩ ⟨_, hequal.symm⟩
    · rcases m.even_or_odd' with ⟨l, rfl | rfl⟩
      · change (normalizedRotate1^[2 * k + 1]) (parabolicLineAtNegTwo i t) =
          (normalizedRotate1^[2 * l]) (parabolicLineAtNegTwo i t) at hequal
        rw [iterate_two_mul_add_one_normalizedRotate1_parabolicLineAtNegTwo,
          iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo] at hequal
        exfalso
        exact Set.disjoint_left.mp hdisjoint
          ⟨_, rfl⟩ ⟨_, hequal⟩
      · have hk : k < p := by omega
        have hl : l < p := by omega
        change (normalizedRotate1^[2 * k + 1]) (parabolicLineAtNegTwo i t) =
          (normalizedRotate1^[2 * l + 1]) (parabolicLineAtNegTwo i t) at hequal
        rw [iterate_two_mul_add_one_normalizedRotate1_parabolicLineAtNegTwo,
          iterate_two_mul_add_one_normalizedRotate1_parabolicLineAtNegTwo] at hequal
        have hparameter := congrArg NormalizedPoint.u2 hequal
        change -(t - (k : ZMod p) * (4 * i)) + 2 * i =
          -(t - (l : ZMod p) * (4 * i)) + 2 * i at hparameter
        have hproducts : (k : ZMod p) * (4 * i) = (l : ZMod p) * (4 * i) := by
          linear_combination hparameter
        have hcasts : (k : ZMod p) = (l : ZMod p) :=
          mul_right_cancel₀ hstep hproducts
        rw [ZMod.natCast_eq_natCast_iff'] at hcasts
        have hkl : k = l := by
          simpa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] using hcasts
        omega
  have horder : rotationOrder (-2 : ZMod p) = 2 * p := rotationOrder_neg_two p hpTwo
  have hcycle : normalizedRotationCycle (-2 : ZMod p) (parabolicLineAtNegTwo i t) =
      (Finset.range (2 * p)).image f := by
    ext y
    simp [normalizedRotationCycle, f, horder]
  calc
    (normalizedRotationCycle (-2 : ZMod p) (parabolicLineAtNegTwo i t)).card =
        ((Finset.range (2 * p)).image f).card := congrArg Finset.card hcycle
    _ = (Finset.range (2 * p)).card := Finset.card_image_iff.mpr hinjective
    _ = 2 * p := Finset.card_range _
    _ = rotationOrder (-2 : ZMod p) := horder.symm

end ParabolicRotationCycles

end BGS.Markoff
