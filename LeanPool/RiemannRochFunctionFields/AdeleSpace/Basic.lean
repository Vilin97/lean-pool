/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.RRspace.Basic
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# K-valued adele space of a function field
Definitions and basic structure for Stichtenoth's adele space.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero
open Filter

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

/-- The classical decidable equality on `k(X)` used by the coordinate places. -/
local instance instDecidableEqRatFuncAdele : DecidableEq k⟮X⟯ := Classical.decEq _
/-- The classical decidable equality on coordinate places used for adele surgery. -/
local instance instDecidableEqPlaceAAdele : DecidableEq (PlaceA k K) := Classical.decEq _

/-- The `k`-submodule of the full product consisting of tuples integral at all but finitely many
places. -/
def adeleSubmodule : Submodule k (PlaceA k K → K) where
  carrier := {α | ∀ᶠ v in cofinite, α v ∈ placeValuationSubring k K v}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ∀ᶠ v in cofinite, a v ∈ placeValuationSubring k K v at ha
    change ∀ᶠ v in cofinite, b v ∈ placeValuationSubring k K v at hb
    change ∀ᶠ v in cofinite, (a + b) v ∈ placeValuationSubring k K v
    exact (ha.and hb).mono fun _ h => add_mem h.1 h.2
  smul_mem' c a ha := by
    change ∀ᶠ v in cofinite, a v ∈ placeValuationSubring k K v at ha
    change ∀ᶠ v in cofinite, (c • a) v ∈ placeValuationSubring k K v
    filter_upwards [ha] with v hv
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem (by
      change placeValuation k K v (algebraMap k K c) ≤ 1
      exact placeValuation_algebraMap_le_one k K v c) hv

omit [Algebra k K] [IsScalarTower k k[X] K] in
/-- Every element of `K` is integral at all but finitely many coordinate places. -/
theorem eventually_mem_placeValuationSubring (f : K) :
    ∀ᶠ v : PlaceA k K in cofinite, f ∈ placeValuationSubring k K v := by
  rw [Filter.eventually_cofinite]
  refine ((IsDedekindDomain.HeightOneSpectrum.Support.finite
      (R := ringOfIntegers k K) f).image Sum.inl).union
        ((IsDedekindDomain.HeightOneSpectrum.Support.finite
          (R := infiniteIntegers k K) f).image Sum.inr) |>.subset ?_
  intro v hv
  rcases v with v | v
  · left
    refine ⟨v, ?_, rfl⟩
    simpa [IsDedekindDomain.HeightOneSpectrum.Support, placeValuationSubring,
      placeValuation, not_le] using hv
  · right
    refine ⟨v, ?_, rfl⟩
    simpa [IsDedekindDomain.HeightOneSpectrum.Support, placeValuationSubring,
      placeValuation, not_le] using hv

/-- The K-valued adele space `A_K = Πʳ_{v} [K, O_v]`. -/
abbrev AdeleSpace := adeleSubmodule k K

/-- Pointwise multiplication of an adele by an element of `K`. -/
def smulAdele (x : K) (a : AdeleSpace k K) : AdeleSpace k K := ⟨fun v => x * a.val v, by
  have hx := eventually_mem_placeValuationSubring k K x
  have ha := a.property
  change ∀ᶠ v : PlaceA k K in cofinite, a.val v ∈ placeValuationSubring k K v at ha
  change ∀ᶠ v : PlaceA k K in cofinite, x * a.val v ∈ placeValuationSubring k K v
  exact (hx.and ha).mono fun _ h => mul_mem h.1 h.2⟩

instance : SMul K (AdeleSpace k K) := ⟨smulAdele k K⟩

instance : Module K (AdeleSpace k K) :=
  Module.ofMinimalAxioms
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_add _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => add_mul _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_assoc _ _ _)
    (fun _ => Subtype.ext <| funext fun _ => one_mul _)

/-- Multiplication by `x ∈ K` as a `k`-linear endomorphism of the adele space. -/
def mulAdeleLinear (x : K) : AdeleSpace k K →ₗ[k] AdeleSpace k K where
  toFun a := x • a
  map_add' _ _ := smul_add x _ _
  map_smul' c a := by
    ext v
    change x * (c • a.val v) = c • (x * a.val v)
    simp only [Algebra.smul_def]
    ring

/-- An adele lies in the filtration piece `A(D)` when its component at every place `v` has
valuation at most `WithZero.exp (D v)`. -/
def memAdeleFilt (D : DivisorA k K) (α : AdeleSpace k K) : Prop :=
  ∀ v, placeValuation k K v (α.val v) ≤ WithZero.exp (D v)

/-- The filtration piece `A(D)` of the adele space. -/
def adeleFilt (D : DivisorA k K) : Submodule k (AdeleSpace k K) where
  carrier := {a | memAdeleFilt k K D a}
  zero_mem' := fun v => by simp
  add_mem' {a b} ha hb := by
    change memAdeleFilt k K D a at ha
    change memAdeleFilt k K D b at hb
    change memAdeleFilt k K D (a + b)
    exact fun v => (Valuation.map_add _ (a.val v) (b.val v)).trans (max_le (ha v) (hb v))
  smul_mem' c a ha := by
    change memAdeleFilt k K D a at ha
    change memAdeleFilt k K D (c • a)
    intro v
    change placeValuation k K v (c • a.val v) ≤ _
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_mul' (placeValuation_algebraMap_le_one k K v c) (ha v)).trans_eq
      (one_mul _)

/-- The diagonal embedding `K → A_K` of principal adeles. -/
def diagonal : K →ₗ[k] AdeleSpace k K where
  toFun f := ⟨fun _ => f, by
    simpa [adeleSubmodule] using
      eventually_mem_placeValuationSubring k K f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The image `diag(K)` of the diagonal embedding. -/
def diagonalSubmodule : Submodule k (AdeleSpace k K) := LinearMap.range (diagonal k K)

theorem adeleFilt_inf_diagonal (D : DivisorA k K) :
    adeleFilt k K D ⊓ diagonalSubmodule k K =
      Submodule.map (diagonal k K : K →ₗ[k] AdeleSpace k K) (RRspace k K D) := by
  ext a
  constructor
  · rintro ⟨ha, f, rfl⟩
    exact ⟨f, ha, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨hf, ⟨f, rfl⟩⟩

/-- The adele filtration is monotone in the divisor. -/
theorem adeleFilt_mono {D D' : DivisorA k K} (h : D ≤ D') :
    adeleFilt k K D ≤ adeleFilt k K D' := by
  intro a ha v
  exact (ha v).trans (WithZero.exp_le_exp.mpr (h v))

/-- `A(D)` as a submodule of `A(D')`, for `D ≤ D'`. -/
def adeleFiltWithin (D D' : DivisorA k K) :
    Submodule k (adeleFilt k K D') :=
  Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D)

/-- Finite-rank increment `finrank k (A(D') ⧸ A(D))`. -/
noncomputable def finrankAdeleFiltDiff (D D' : DivisorA k K) : ℕ := by
  letI : AddCommGroup (adeleFilt k K D') := Submodule.addCommGroup _
  letI : Module k (adeleFilt k K D') := Submodule.module _
  exact Module.finrank k <|
    (adeleFilt k K D') ⧸
      Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D)

/-- Rank of `(A(D') + diag(K)) ⧸ (A(D) + diag(K))` from the sandwich bookkeeping. -/
noncomputable def sandwichRank (D D' : DivisorA k K) : ℤ :=
  by
  letI : AddCommGroup (adeleFilt k K D' + diagonalSubmodule k K) :=
    Submodule.addCommGroup _
  letI : Module k (adeleFilt k K D' + diagonalSubmodule k K) := Submodule.module _
  exact Int.ofNat (Module.finrank k <|
    (adeleFilt k K D' + diagonalSubmodule k K) ⧸
      Submodule.comap (adeleFilt k K D' + diagonalSubmodule k K).subtype
        (adeleFilt k K D + diagonalSubmodule k K))

/-- Component update for adele surgery (`A(D₁ ⊔ D₂) = A(D₁) + A(D₂)`). -/
def adeleUpdate (α : AdeleSpace k K) (v : PlaceA k K) (a : K) : AdeleSpace k K :=
  ⟨Function.update α.val v a, by
    change ∀ᶠ w : PlaceA k K in cofinite,
      Function.update α.val v a w ∈ placeValuationSubring k K w
    filter_upwards [α.property, Filter.eventually_cofinite_ne v] with w hw hwv
    simpa [Function.update_of_ne hwv] using hw⟩

theorem adeleFilt_sup_eq_add {D₁ D₂ : DivisorA k K} :
    adeleFilt k K (D₁ ⊔ D₂) = adeleFilt k K D₁ + adeleFilt k K D₂ := by
  classical
  rw [Submodule.add_eq_sup]
  apply le_antisymm
  · intro a ha
    have haevent := a.property
    change ∀ᶠ v : PlaceA k K in cofinite,
      a.val v ∈ placeValuationSubring k K v at haevent
    let a₁ : AdeleSpace k K := ⟨fun v => if D₂ v ≤ D₁ v then a.val v else 0, by
      simpa [adeleSubmodule] using haevent.mono fun v hv => by
        by_cases h : D₂ v ≤ D₁ v
        · rw [ite_eq_left h]
          exact hv
        · rw [ite_eq_right h]
          exact zero_mem _⟩
    let a₂ : AdeleSpace k K := ⟨fun v => if D₂ v ≤ D₁ v then 0 else a.val v, by
      simpa [adeleSubmodule] using haevent.mono fun v hv => by
        by_cases h : D₂ v ≤ D₁ v
        · rw [ite_eq_left h]
          exact zero_mem _
        · rw [ite_eq_right h]
          exact hv⟩
    have ha₁ : a₁ ∈ adeleFilt k K D₁ := by
      change memAdeleFilt k K D₁ a₁
      intro v
      by_cases h : D₂ v ≤ D₁ v
      · change placeValuation k K v (if D₂ v ≤ D₁ v then a.val v else 0) ≤ _
        rw [ite_eq_left h]
        simpa [Finsupp.sup_apply, sup_eq_left.mpr h] using ha v
      · simp [a₁, h]
    have ha₂ : a₂ ∈ adeleFilt k K D₂ := by
      change memAdeleFilt k K D₂ a₂
      intro v
      by_cases h : D₂ v ≤ D₁ v
      · simp [a₂, h]
      · have hv : D₁ v ≤ D₂ v := le_of_not_ge h
        change placeValuation k K v (if D₂ v ≤ D₁ v then 0 else a.val v) ≤ _
        rw [ite_eq_right h]
        simpa [Finsupp.sup_apply, sup_eq_right.mpr hv] using ha v
    refine Submodule.mem_sup.mpr ⟨a₁, ha₁, a₂, ha₂, ?_⟩
    ext v
    by_cases h : D₂ v ≤ D₁ v <;> simp [a₁, a₂, h]
  · apply sup_le
    · intro a ha
      change memAdeleFilt k K (D₁ ⊔ D₂) a
      intro v
      exact (ha v).trans (WithZero.exp_le_exp.mpr le_sup_left)
    · intro a ha
      change memAdeleFilt k K (D₁ ⊔ D₂) a
      intro v
      exact (ha v).trans (WithZero.exp_le_exp.mpr le_sup_right)

end FunctionField.Chart

end
