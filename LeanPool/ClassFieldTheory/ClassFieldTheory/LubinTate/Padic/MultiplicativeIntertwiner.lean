/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries
/-!
# Comparing the standard and multiplicative Lubin--Tate series over `ℚ_p`

The characteristic-independent same-uniformizer recursion supplies the
canonical series with linear coefficient `1` satisfying

`[(1 + X)^p - 1](H(X)) = H([pX + X^p](X))`.

Consequently, evaluation of `H` carries standard Lubin--Tate division points
to multiplicative division points.  This file constructs that series directly;
it does not identify the two actions from equality of their kernels.
-/

@[expose] public section

noncomputable
section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The canonical linear-term-one intertwiner carrying standard Lubin--Tate
division points over `ℚ_p` to multiplicative division points. -/
noncomputable def padicStandardToMultiplicativeIntertwiner
    (p : ℕ) [Fact p.Prime] :
    PowerSeries (padicLocalField p).valuationSubring :=
  recursiveIntertwiner
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (padicMultiplicativeLubinTateSeries p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (fun _ : Unit => 1)

/-- The standard-to-multiplicative intertwiner has linear coefficient `1`
and no constant term. -/
theorem padicStandardToMultiplicativeIntertwiner_hasLinearTerm
    (p : ℕ) [Fact p.Prime] :
    HasLinearTerm (padicStandardToMultiplicativeIntertwiner p)
      (fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring)) :=
  recursiveIntertwiner_hasLinearTerm
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (padicMultiplicativeLubinTateSeries p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (fun _ : Unit => 1)

/-- The canonical series satisfies the literal same-uniformizer equation
from the multiplicative series to the standard series. -/
theorem padicStandardToMultiplicativeIntertwiner_intertwines
    (p : ℕ) [Fact p.Prime] :
    Intertwines
      (padicMultiplicativeLubinTateSeries p)
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (padicStandardToMultiplicativeIntertwiner p) :=
  recursiveIntertwiner_intertwines
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (padicMultiplicativeLubinTateSeries p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (fun _ : Unit => 1)

/-- One-variable form of the intertwining equation:
the multiplicative series after `H` equals `H` after the standard series. -/
theorem padicStandardToMultiplicativeIntertwiner_functionalEquation
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      PowerSeries.subst
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries
        (padicStandardToMultiplicativeIntertwiner p) := by
  have h :=
    padicStandardToMultiplicativeIntertwiner_intertwines p
  calc
    PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
        MvPowerSeries.subst
          (fun i : Unit =>
            inVariable
              (standardLubinTateSeries
                (padicMultiplicativeLubinTateSeries_isUniformizer p)) i)
          (padicStandardToMultiplicativeIntertwiner p) :=
      h
    _ =
        PowerSeries.subst
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries
          (padicStandardToMultiplicativeIntertwiner p) := by
      rw [PowerSeries.subst_def]
      congr 1
      funext i
      cases i
      exact
        PowerSeries.X_subst
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries

/-- The intertwiner has zero constant coefficient, hence admits formal
substitution. -/
theorem padicStandardToMultiplicativeIntertwiner_hasSubst
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.HasSubst
      (padicStandardToMultiplicativeIntertwiner p) :=
  (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p).hasSubst

/-- The coefficient of `X` in the canonical intertwiner is `1`. -/
@[simp]
theorem padicStandardToMultiplicativeIntertwiner_coeff_one
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.coeff 1
        (padicStandardToMultiplicativeIntertwiner p) =
      1 :=
  (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p).coeff_single ()

/-- Conjugating a standard scalar endomorphism through the canonical
comparison gives the unique multiplicative-series endomorphism with the
same scalar linear coefficient. -/
theorem padicStandardToMultiplicativeIntertwiner_endomorphism
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (standardLubinTateEndomorphism
          (padicMultiplicativeLubinTateSeries_isUniformizer p) a)
        (padicStandardToMultiplicativeIntertwiner p) =
      PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let E := padicMultiplicativeLubinTateSeries p
  let Ebar := standardLubinTateSeries hπ
  let H := padicStandardToMultiplicativeIntertwiner p
  let S := standardLubinTateEndomorphism hπ a
  let M :=
    recursiveIntertwiner hπ E E (fun _ : Unit => a)
  have hH :
      HasLinearTerm H
        (fun _ : Unit =>
          (1 : (padicLocalField p).valuationSubring)) :=
    padicStandardToMultiplicativeIntertwiner_hasLinearTerm p
  have hS :
      HasLinearTerm S (fun _ : Unit => a) :=
    standardLubinTateEndomorphism_hasLinearTerm hπ a
  have hM :
      HasLinearTerm M (fun _ : Unit => a) :=
    recursiveIntertwiner_hasLinearTerm hπ E E (fun _ : Unit => a)
  have hleftLinearRaw :=
    hH.subst
      (G := fun _ : Unit => S)
      (M := fun _ : Unit => fun _ : Unit => a)
      (fun _ => hS)
  have hleftLinear :
      HasLinearTerm (PowerSeries.subst S H)
        (fun _ : Unit => a) := by
    simpa [PowerSeries.subst_def] using hleftLinearRaw
  have hrightLinearRaw :=
    hM.subst
      (G := fun _ : Unit => H)
      (M := fun _ : Unit => fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring))
      (fun _ => hH)
  have hrightLinear :
      HasLinearTerm (PowerSeries.subst H M)
        (fun _ : Unit => a) := by
    simpa [PowerSeries.subst_def] using hrightLinearRaw
  have hHIntertwines :
      Intertwines E Ebar H :=
    padicStandardToMultiplicativeIntertwiner_intertwines p
  have hSIntertwines :
      Intertwines Ebar Ebar S :=
    standardLubinTateEndomorphism_intertwines hπ a
  have hMIntertwines :
      Intertwines E E M :=
    recursiveIntertwiner_intertwines hπ E E (fun _ : Unit => a)
  have hleftIntertwines :
      Intertwines E Ebar (PowerSeries.subst S H) :=
    hHIntertwines.powerSeries_subst hH.hasSubst
      hSIntertwines hS.hasSubst
  have hrightIntertwines :
      Intertwines E Ebar (PowerSeries.subst H M) :=
    hMIntertwines.powerSeries_subst hM.hasSubst
      hHIntertwines hH.hasSubst
  exact
    eq_of_hasLinearTerm_of_intertwines hπ E Ebar
      (fun _ : Unit => a)
      hleftLinear hleftIntertwines
      hrightLinear hrightIntertwines

/-- The canonical inverse-direction intertwiner carrying multiplicative
division points to standard Lubin--Tate division points. -/
noncomputable def padicMultiplicativeToStandardIntertwiner
    (p : ℕ) [Fact p.Prime] :
    PowerSeries (padicLocalField p).valuationSubring :=
  recursiveIntertwiner
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (padicMultiplicativeLubinTateSeries p)
    (fun _ : Unit => 1)

/-- The multiplicative-to-standard intertwiner also has linear coefficient
`1` and no constant term. -/
theorem padicMultiplicativeToStandardIntertwiner_hasLinearTerm
    (p : ℕ) [Fact p.Prime] :
    HasLinearTerm (padicMultiplicativeToStandardIntertwiner p)
      (fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring)) :=
  recursiveIntertwiner_hasLinearTerm
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (padicMultiplicativeLubinTateSeries p)
    (fun _ : Unit => 1)

/-- The inverse-direction canonical series satisfies its literal
same-uniformizer equation. -/
theorem padicMultiplicativeToStandardIntertwiner_intertwines
    (p : ℕ) [Fact p.Prime] :
    Intertwines
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeToStandardIntertwiner p) :=
  recursiveIntertwiner_intertwines
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (padicMultiplicativeLubinTateSeries p)
    (fun _ : Unit => 1)

/-- One-variable form of the inverse-direction intertwining equation. -/
theorem padicMultiplicativeToStandardIntertwiner_functionalEquation
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.subst
        (padicMultiplicativeToStandardIntertwiner p)
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries =
      PowerSeries.subst
        (padicMultiplicativeLubinTateSeries p).toPowerSeries
        (padicMultiplicativeToStandardIntertwiner p) := by
  have h :=
    padicMultiplicativeToStandardIntertwiner_intertwines p
  calc
    PowerSeries.subst
        (padicMultiplicativeToStandardIntertwiner p)
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries =
        MvPowerSeries.subst
          (fun i : Unit =>
            inVariable (padicMultiplicativeLubinTateSeries p) i)
          (padicMultiplicativeToStandardIntertwiner p) :=
      h
    _ =
        PowerSeries.subst
          (padicMultiplicativeLubinTateSeries p).toPowerSeries
          (padicMultiplicativeToStandardIntertwiner p) := by
      rw [PowerSeries.subst_def]
      congr 1
      funext i
      cases i
      exact
        PowerSeries.X_subst
          (padicMultiplicativeLubinTateSeries p).toPowerSeries

/-- The inverse-direction intertwiner admits formal substitution. -/
theorem padicMultiplicativeToStandardIntertwiner_hasSubst
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.HasSubst
      (padicMultiplicativeToStandardIntertwiner p) :=
  (padicMultiplicativeToStandardIntertwiner_hasLinearTerm p).hasSubst

/-- Composing the standard-to-multiplicative comparison after its reverse
is the identity on the multiplicative coordinate. -/
theorem padicStandardToMultiplicativeIntertwiner_subst_reverse
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.subst
        (padicMultiplicativeToStandardIntertwiner p)
        (padicStandardToMultiplicativeIntertwiner p) =
      PowerSeries.X := by
  have hcomp :=
    (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p).subst
      (G := fun _ : Unit =>
        padicMultiplicativeToStandardIntertwiner p)
      (M := fun _ : Unit => fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring))
      (fun _ =>
        padicMultiplicativeToStandardIntertwiner_hasLinearTerm p)
  have hcomp' :
      HasLinearTerm
        (PowerSeries.subst
          (padicMultiplicativeToStandardIntertwiner p)
          (padicStandardToMultiplicativeIntertwiner p))
        (fun _ : Unit =>
          (1 : (padicLocalField p).valuationSubring)) := by
    simpa [PowerSeries.subst_def] using hcomp
  have hIcomp :=
    (padicStandardToMultiplicativeIntertwiner_intertwines p).powerSeries_subst
      (padicStandardToMultiplicativeIntertwiner_hasSubst p)
      (padicMultiplicativeToStandardIntertwiner_intertwines p)
      (padicMultiplicativeToStandardIntertwiner_hasSubst p)
  have hX :
      HasLinearTerm
        (PowerSeries.X :
          PowerSeries (padicLocalField p).valuationSubring)
        (fun _ : Unit => 1) := by
    simpa [PowerSeries.X] using
      (hasLinearTerm_X
        (R := (padicLocalField p).valuationSubring) ())
  exact
    eq_of_hasLinearTerm_of_intertwines
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => 1)
      hcomp' hIcomp hX
      (intertwines_X (padicMultiplicativeLubinTateSeries p) ())

/-- Composing the reverse comparison after the standard-to-multiplicative
series is the identity on the standard coordinate. -/
theorem padicMultiplicativeToStandardIntertwiner_subst_reverse
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (padicMultiplicativeToStandardIntertwiner p) =
      PowerSeries.X := by
  have hcomp :=
    (padicMultiplicativeToStandardIntertwiner_hasLinearTerm p).subst
      (G := fun _ : Unit =>
        padicStandardToMultiplicativeIntertwiner p)
      (M := fun _ : Unit => fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring))
      (fun _ =>
        padicStandardToMultiplicativeIntertwiner_hasLinearTerm p)
  have hcomp' :
      HasLinearTerm
        (PowerSeries.subst
          (padicStandardToMultiplicativeIntertwiner p)
          (padicMultiplicativeToStandardIntertwiner p))
        (fun _ : Unit =>
          (1 : (padicLocalField p).valuationSubring)) := by
    simpa [PowerSeries.subst_def] using hcomp
  have hIcomp :=
    (padicMultiplicativeToStandardIntertwiner_intertwines p).powerSeries_subst
      (padicMultiplicativeToStandardIntertwiner_hasSubst p)
      (padicStandardToMultiplicativeIntertwiner_intertwines p)
      (padicStandardToMultiplicativeIntertwiner_hasSubst p)
  have hX :
      HasLinearTerm
        (PowerSeries.X :
          PowerSeries (padicLocalField p).valuationSubring)
        (fun _ : Unit => 1) := by
    simpa [PowerSeries.X] using
      (hasLinearTerm_X
        (R := (padicLocalField p).valuationSubring) ())
  exact
    eq_of_hasLinearTerm_of_intertwines
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (fun _ : Unit => 1)
      hcomp' hIcomp hX
      (intertwines_X
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)) ())

end LubinTate

end
