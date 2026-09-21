/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Trace
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Lift` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

/-- States the theorem `principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ`. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n,
      principalUnitsSuccQuotMk K n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x) =
        principalUnitsSuccQuotMk K n y := by
  obtain ⟨q, hq⟩ :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_surjective
      K L n hn (principalUnitsSuccQuotMk K n y)
  obtain ⟨x, rfl⟩ := principalUnitsSuccQuotMk_surjective L n q
  refine ⟨x, ?_⟩
  simpa [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk]
    using hq

/-- Actual integral-closure one-step correction form: the remaining error
after dividing the target by the chosen norm lies in the next principal-unit
filtration step. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n,
      y / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x ∈
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  obtain ⟨x, hx⟩ :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ K L n hn y
  refine ⟨x, ?_⟩
  exact (principalUnitsSuccQuotMk_eq_iff_div_mem K n y
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x)).1 hx.symm

/-- Actual integral-closure finite-depth iteration of the one-step
principal-unit norm correction.  For every `d`, a target in `U_K^n` can be
matched by the norm of an element of `U_L^n` up to an error in `U_K^(n+d)`.

This is the finite approximation stage of principal-unit norm surjectivity. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_approx_mem_add
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n d : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n,
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d) := by
  induction d with
  | zero =>
      refine ⟨1, ?_⟩
      change (y : 𝒪[K]ˣ) / normIntegerUnits K L (1 : 𝒪[L]ˣ) ∈
        principalUnits K (n + 0)
      rw [(normIntegerUnits K L).map_one, div_one, Nat.add_zero]
      exact y.2
  | succ d ih =>
      obtain ⟨x, hx⟩ := ih
      let r : principalUnits K (n + d) :=
        ⟨(y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ), hx⟩
      have hnd : 1 ≤ n + d := le_trans hn (Nat.le_add_right n d)
      obtain ⟨z, hz⟩ :=
        principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
          K L (n + d) hnd r
      let x' : principalUnits L n :=
        ⟨(x : 𝒪[L]ˣ) * (z : 𝒪[L]ˣ),
          (principalUnits L n).mul_mem x.2
            (principalUnits_antitone L (Nat.le_add_right n d) z.2)⟩
      refine ⟨x', ?_⟩
      have hzUnit :
          (((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
              (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) ∈
            principalUnits K ((n + d) + 1)) := hz
      have hresEq :
          (y : 𝒪[K]ˣ) / normIntegerUnits K L ((x' : principalUnits L n) :
              𝒪[L]ˣ) =
            ((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
                (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) := by
        change
          (y : 𝒪[K]ˣ) / normIntegerUnits K L ((x' : principalUnits L n) :
              𝒪[L]ˣ) =
            (r : 𝒪[K]ˣ) /
              ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
                  (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ)
        simp only [x', r, principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply,
          (normIntegerUnits K L).map_mul]
        simp [div_eq_mul_inv, mul_assoc, mul_comm]
      rw [hresEq]
      simpa [Nat.add_assoc] using hzUnit

/-- Actual integral-closure correction term selected from the current finite
approximation error. -/
noncomputable def chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    principalUnits L (n + d) :=
  let r : principalUnits K (n + d) :=
    ⟨(y : 𝒪[K]ˣ) / normIntegerUnits K L (s.1 : 𝒪[L]ˣ), s.2⟩
  have hnd : 1 ≤ n + d := le_trans hn (Nat.le_add_right n d)
  Classical.choose
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
      K L (n + d) hnd r)

/-- Actual integral-closure coherent update step for finite principal-unit
norm approximations. -/
noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    {x : principalUnits L n //
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + (d + 1))} := by
  let r : principalUnits K (n + d) :=
    ⟨(y : 𝒪[K]ˣ) / normIntegerUnits K L (s.1 : 𝒪[L]ˣ), s.2⟩
  let z : principalUnits L (n + d) :=
    chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
      K L n hn y d s
  let x' : principalUnits L n :=
    ⟨(s.1 : 𝒪[L]ˣ) * (z : 𝒪[L]ˣ),
      (principalUnits L n).mul_mem s.1.2
        (principalUnits_antitone L (Nat.le_add_right n d) z.2)⟩
  have hz :
      (((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
          (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) ∈
        principalUnits K ((n + d) + 1)) :=
    by
      have hnd : 1 ≤ n + d := le_trans hn (Nat.le_add_right n d)
      dsimp [z, chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection]
      exact Classical.choose_spec
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
          K L (n + d) hnd r)
  refine ⟨x', ?_⟩
  have hresEq :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x' : 𝒪[L]ˣ) =
        ((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
            (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) := by
    change
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x' : 𝒪[L]ˣ) =
        (r : 𝒪[K]ˣ) /
          ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
              (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ)
    simp only [x', r, principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply,
      (normIntegerUnits K L).map_mul]
    exact div_mul_eq_div_div _ _ _
  rw [hresEq]
  simpa [Nat.add_assoc] using hz

/-- The quotient between successive actual integral-closure approximation
states lies in the expected depth. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep_div_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep
          K L n hn y d s).1 : 𝒪[L]ˣ) /
        (s.1 : 𝒪[L]ˣ)) ∈ principalUnits L (n + d) := by
  let z : principalUnits L (n + d) :=
    chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
      K L n hn y d s
  change (((s.1 : 𝒪[L]ˣ) * (z : 𝒪[L]ˣ)) / (s.1 : 𝒪[L]ˣ)) ∈
    principalUnits L (n + d)
  rw [mul_div_cancel_left]
  exact z.2

/-- Actual integral-closure coherent finite principal-unit norm
approximations. -/
noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    (d : Nat) →
      {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}
  | 0 => by
      refine ⟨1, ?_⟩
      change (y : 𝒪[K]ˣ) / normIntegerUnits K L (1 : 𝒪[L]ˣ) ∈
        principalUnits K (n + 0)
      rw [(normIntegerUnits K L).map_one, div_one, Nat.add_zero]
      exact y.2
  | d + 1 =>
      principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep K L n hn y d
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d)

/-- Consecutive actual integral-closure approximation states differ by a
correction term in the expected depth. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_succ_div_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ)) ∈
      principalUnits L (n + d) := by
  change
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep K L n hn y d
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d)).1 : 𝒪[L]ˣ) /
        ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : 𝒪[L]ˣ)) ∈ principalUnits L (n + d)
  exact principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep_div_mem
    K L n hn y d
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y d)

/-- The actual integral-closure correction sequence encoded by consecutive
coherent approximation states. -/
noncomputable def chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∀ d : Nat, principalUnits L (n + d) :=
  fun d =>
    ⟨(((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ),
      principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_succ_div_mem
        K L n hn y d⟩

/-- The finite product of the actual integral-closure correction sequence is
the corresponding coherent approximation state. -/
theorem principalUnitsCorrectionProduct_approxCorrectionSeqOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    principalUnitsCorrectionProduct L n
        (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
          K L n hn y) d =
      (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) := by
  induction d with
  | zero =>
      simp [principalUnitsCorrectionProduct_zero,
        principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState]
  | succ d ih =>
      rw [principalUnitsCorrectionProduct_succ, ih]
      change
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) *
            ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
              (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
                K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ)) =
          (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ)
      rw [mul_comm, div_mul_cancel]

/-- The actual integral-closure coherent finite approximation states have a
principal-unit limit.  This is the unramified infinite-product step specialized
to the actual correction terms generated above. -/
theorem exists_tendsto_principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n, Filter.Tendsto
      (fun d : Nat =>
        ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))
      Filter.atTop (nhds (((x : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L])) := by
  obtain ⟨x, hx⟩ :=
    exists_tendsto_principalUnitsCorrectionProduct_principalUnit L n hn
      (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
        K L n hn y)
  refine ⟨x, ?_⟩
  have hseq :
      (fun d : Nat =>
        ((principalUnitsCorrectionProduct L n
            (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
              K L n hn y) d : 𝒪[L]ˣ) : 𝒪[L])) =
        (fun d : Nat =>
          ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L])) := by
    funext d
    rw [principalUnitsCorrectionProduct_approxCorrectionSeqOfIsIntegralClosure
      K L n hn y d]
  simpa [hseq] using hx

/-- The actual integral-closure coherent approximation state has the
advertised finite-depth error bound. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_error_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    ((y : 𝒪[K]ˣ) /
        normIntegerUnits K L
          ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : 𝒪[L]ˣ)) ∈
      principalUnits K (n + d) :=
  (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    K L n hn y d).2

/-- Actual integral-closure norm-continuity form used in principal-unit norm lifting.
It is derived from multiplicativity of the integer-unit norm and
the actual proof that the unramified norm preserves principal-unit levels. -/
theorem eventually_normIntegerUnits_div_mem_principalUnits_of_tendsto_units_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    {f : Nat → 𝒪[L]ˣ} {x : 𝒪[L]ˣ} (n : Nat)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    ∀ᶠ d in atTop,
      normIntegerUnits K L (f d) / normIntegerUnits K L x ∈ principalUnits K n := by
  have hdiv := eventually_div_mem_principalUnits_of_tendsto_units L n hf
  filter_upwards [hdiv] with d hd
  have hnorm : normIntegerUnits K L (f d / x) ∈ principalUnits K n :=
    normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
      K L n (f d / x) hd
  simpa [(normIntegerUnits K L).map_div] using hnorm

/-- The limit of the actual integral-closure coherent approximation states
preserves all finite-depth error bounds. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_limit_error_mem_add_all
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n)
    (x : principalUnits L n)
    (hx : Tendsto
      (fun d : Nat =>
        ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))
      atTop (nhds (((x : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))) :
    ∀ d : Nat,
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d) := by
  intro d
  let f : Nat → 𝒪[L]ˣ := fun i =>
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y i).1 : principalUnits L n) : 𝒪[L]ˣ)
  have hnormEv : ∀ᶠ i in atTop,
      normIntegerUnits K L (f i) / normIntegerUnits K L (x : 𝒪[L]ˣ) ∈
        principalUnits K (n + d) := by
    exact
      eventually_normIntegerUnits_div_mem_principalUnits_of_tendsto_units_of_isIntegralClosure
        K L (n + d) hx
  have hge : ∀ᶠ i : Nat in atTop, d ≤ i := eventually_ge_atTop d
  rcases (hnormEv.and hge).exists with ⟨i, hboth⟩
  rcases hboth with ⟨hnorm, hdi⟩
  have herrDeep :
      ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) ∈
        principalUnits K (n + i) :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_error_mem
      K L n hn y i
  have herr :
      ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d) :=
    principalUnits_antitone K (Nat.add_le_add_left hdi n) herrDeep
  have heq :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ) =
        ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) *
        (normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ) /
          normIntegerUnits K L (x : 𝒪[L]ˣ)) := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [heq]
  exact (principalUnits K (n + d)).mul_mem herr (by simpa [f] using hnorm)

/-- Actual integral-closure separatedness step: if the error of a candidate
principal-unit norm lift lies in every deeper principal-unit subgroup, the
candidate is exact. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_eq_of_error_mem_add_all
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (y : principalUnits K n) (x : principalUnits L n)
    (h : ∀ d : Nat,
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d)) :
    (y : 𝒪[K]ˣ) = normIntegerUnits K L (x : 𝒪[L]ˣ) := by
  have hOne :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ) = 1 :=
    principalUnits_eq_one_of_mem_add_all K n
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) h
  exact div_eq_one.mp hOne

/-- Principal-unit norm surjectivity for actual integral closures: in a finite
unramified valuation extension, the integer-unit norm is
surjective on every `U^n`, `n ≥ 1`. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n) := by
  intro y
  obtain ⟨x, hx⟩ :=
    exists_tendsto_principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y
  refine ⟨x, ?_⟩
  have hmem :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_limit_error_mem_add_all
      K L n hn y x hx
  have hEq :
      (y : 𝒪[K]ˣ) = normIntegerUnits K L (x : 𝒪[L]ˣ) :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_eq_of_error_mem_add_all
      K L n y x hmem
  apply Subtype.ext
  simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply] using hEq.symm

end LocalClassFieldTheory
