/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. Mittag-Leffler principal-part data (Forster §17.1-17.2).
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.PrincipalPart
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Mittag-Leffler principal-part distributions (residue-calculus)

`RS.PrincipalPartData U` is a Mittag-Leffler datum: at finitely many points of `U ⊆ ℂ`, a finite
tail of negative-exponent Laurent coefficients. Implemented as a `Submodule ℂ (ℂ → (ℤ →₀ ℂ))`
subtype (so the `AddCommGroup`/`Module ℂ` structure comes for free), with named accessors
`coeff`/`coeff_neg`/`mem_of_ne_zero`/`finite_support` matching the design's structure fields.

`RS.PrincipalPartData.Realizes f D` says `f` is meromorphic on `U` with exactly the principal
parts `D`. `RS.PrincipalPartData.ofMeromorphicOn` extracts the datum from a meromorphic function
with finitely many poles on `U`.

Main exports: `RS.PrincipalPartData`, `RS.PrincipalPartData.Realizes`,
`RS.PrincipalPartData.toFun`, `RS.PrincipalPartData.totalRes`,
`RS.PrincipalPartData.ofMeromorphicOn`, `RS.PrincipalPartData.realizes_ofMeromorphicOn`,
`RS.PrincipalPartData.Realizes.add`, `RS.PrincipalPartData.Realizes.smul`,
`RS.PrincipalPartData.Realizes.sub_orderAt_nonneg`, `RS.PrincipalPartData.realizes_zero_iff`.

**Semi-frozen** (per the design doc): laurent-tails' designer may extend, not change, this
interface.
-/

open Filter Topology Metric Function

namespace RS

variable {U : Set ℂ}

/-- The underlying submodule of coefficient assignments: pure principal parts (negative
exponents only), supported in `U`, with finitely many nonzero points. -/
def principalPartCarrier (U : Set ℂ) : Submodule ℂ (ℂ → (ℤ →₀ ℂ)) where
  carrier := {c | (∀ p, ∀ k ∈ (c p).support, k < 0) ∧ (∀ p, c p ≠ 0 → p ∈ U) ∧
    {p | c p ≠ 0}.Finite}
  zero_mem' := ⟨fun _ _ hk => by simp at hk, fun p h => by simp at h,
    by simp⟩
  add_mem' {c d} hc hd := by
    obtain ⟨hc1, hc2, hc3⟩ := hc
    obtain ⟨hd1, hd2, hd3⟩ := hd
    refine ⟨fun p k hk => ?_, fun p h => ?_, ?_⟩
    · rcases Finset.mem_union.mp (Finsupp.support_add hk) with h | h
      · exact hc1 p k h
      · exact hd1 p k h
    · by_contra hp
      have h1 : c p = 0 := by by_contra hc0; exact hp (hc2 p hc0)
      have h2 : d p = 0 := by by_contra hd0; exact hp (hd2 p hd0)
      exact h (by rw [Pi.add_apply, h1, h2, add_zero])
    · apply Set.Finite.subset (hc3.union hd3)
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      by_contra hp'
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hp'
      exact hp (by rw [Pi.add_apply, hp'.1, hp'.2, add_zero])
  smul_mem' c₀ x hx := by
    obtain ⟨hx1, hx2, hx3⟩ := hx
    refine ⟨fun p k hk => hx1 p k (Finsupp.support_smul hk), fun p h => ?_, ?_⟩
    · apply hx2 p
      intro hc0
      exact h (by rw [Pi.smul_apply, hc0, smul_zero])
    · apply Set.Finite.subset hx3
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      by_contra hp'
      exact hp (by rw [Pi.smul_apply, hp', smul_zero])

/-- A Mittag-Leffler datum of principal parts on `U ⊆ ℂ`: at finitely many points, a finite tail
of negative-exponent Laurent coefficients. -/
def PrincipalPartData (U : Set ℂ) : Type := ↥(principalPartCarrier U)

namespace PrincipalPartData

noncomputable instance : AddCommGroup (PrincipalPartData U) :=
  inferInstanceAs (AddCommGroup ↥(principalPartCarrier U))

noncomputable instance : Module ℂ (PrincipalPartData U) :=
  inferInstanceAs (Module ℂ ↥(principalPartCarrier U))

/-- Coefficient tail at each point. -/
def coeff (D : PrincipalPartData U) : ℂ → (ℤ →₀ ℂ) := D.1

theorem coeff_neg (D : PrincipalPartData U) : ∀ p, ∀ k ∈ (D.coeff p).support, k < 0 := D.2.1

theorem mem_of_ne_zero (D : PrincipalPartData U) : ∀ p, D.coeff p ≠ 0 → p ∈ U := D.2.2.1

theorem finite_support (D : PrincipalPartData U) : {p | D.coeff p ≠ 0}.Finite := D.2.2.2

/-- Constructor matching the structure-literal API. -/
def mk' (coeff : ℂ → (ℤ →₀ ℂ)) (coeff_neg : ∀ p, ∀ k ∈ (coeff p).support, k < 0)
    (mem_of_ne_zero : ∀ p, coeff p ≠ 0 → p ∈ U) (finite_support : {p | coeff p ≠ 0}.Finite) :
    PrincipalPartData U :=
  ⟨coeff, coeff_neg, mem_of_ne_zero, finite_support⟩

@[simp] theorem coeff_mk' (coeff) (coeff_neg) (mem_of_ne_zero) (finite_support) :
    (mk' coeff coeff_neg mem_of_ne_zero finite_support : PrincipalPartData U).coeff = coeff := rfl

@[simp] theorem coeff_zero : (0 : PrincipalPartData U).coeff = 0 := rfl
@[simp] theorem coeff_add (D E : PrincipalPartData U) :
    (D + E).coeff = D.coeff + E.coeff := rfl
@[simp] theorem coeff_neg_fun (D : PrincipalPartData U) : (-D).coeff = -D.coeff := rfl
@[simp] theorem coeff_smul (c : ℂ) (D : PrincipalPartData U) :
    (c • D).coeff = c • D.coeff := rfl

/-- `f` realizes the datum on `U`: meromorphic with exactly these principal parts. -/
def Realizes (f : ℂ → ℂ) (D : PrincipalPartData U) : Prop :=
  MeromorphicOn f U ∧ ∀ p ∈ U, ∀ k < 0, laurentCoeffAt f p k = D.coeff p k

/-- The associated function: sum of the finite tails (junk-free honest function). -/
noncomputable def toFun (D : PrincipalPartData U) : ℂ → ℂ := fun z =>
  ∑ᶠ p, ∑ k ∈ (D.coeff p).support, D.coeff p k * (z - p) ^ k

/-- Total residue of the datum. -/
noncomputable def totalRes (D : PrincipalPartData U) : ℂ := ∑ᶠ p, D.coeff p (-1)

open Classical in
/-- The raw coefficient assignment underlying `ofMeromorphicOn`: at each `p ∈ U`, the negative
Laurent tail of `f` at `p` (as a `Finsupp` on `Finset.Icc (order.untop₀) (-1)`); `0` off `U`. -/
noncomputable def mlCoeff (f : ℂ → ℂ) (U : Set ℂ) (p : ℂ) : ℤ →₀ ℂ :=
  Finsupp.onFinset
    (if p ∈ U then Finset.Icc (meromorphicOrderAt f p).untop₀ (-1) else ∅)
    (fun k => if p ∈ U ∧ k < 0 then laurentCoeffAt f p k else 0)
    (by
      intro k hk
      by_cases hp : p ∈ U
      · simp only [hp, true_and] at hk
        by_cases hk0 : k < 0
        · simp only [hk0, if_true] at hk
          simp only [hp, if_true, Finset.mem_Icc]
          refine ⟨?_, by omega⟩
          by_contra hlt
          rw [not_le] at hlt
          apply hk
          by_cases htop : meromorphicOrderAt f p = ⊤
          · exact laurentCoeffAt_of_order_eq_top htop k
          · apply laurentCoeffAt_eq_zero_of_lt_order
            rw [← WithTop.coe_untop₀_of_ne_top htop]
            exact_mod_cast hlt
        · simp [hk0] at hk
      · simp [hp] at hk)

open scoped Classical in
theorem mlCoeff_apply {f : ℂ → ℂ} {U : Set ℂ} (p : ℂ) (k : ℤ) :
    mlCoeff f U p k = if p ∈ U ∧ k < 0 then laurentCoeffAt f p k else 0 :=
  Finsupp.onFinset_apply

theorem mlCoeff_coeff_neg (f : ℂ → ℂ) (U : Set ℂ) :
    ∀ p, ∀ k ∈ (mlCoeff f U p).support, k < 0 := by
  intro p k hk
  rw [Finsupp.mem_support_iff, mlCoeff_apply] at hk
  by_contra hk0
  exact hk (by simp [hk0])

theorem mlCoeff_mem_of_ne_zero (f : ℂ → ℂ) (U : Set ℂ) :
    ∀ p, mlCoeff f U p ≠ 0 → p ∈ U := by
  intro p h
  by_contra hpU
  apply h
  ext k
  rw [mlCoeff_apply]
  simp [hpU]

theorem mlCoeff_finite_support {f : ℂ → ℂ} {U : Set ℂ}
    (hfin : {p ∈ U | meromorphicOrderAt f p < 0}.Finite) :
    {p | mlCoeff f U p ≠ 0}.Finite := by
  apply Set.Finite.subset hfin
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  by_contra hp'
  simp only [Set.mem_ofPred_eq, not_and, not_lt] at hp'
  apply hp
  ext k
  rw [mlCoeff_apply]
  by_cases hpU : p ∈ U
  · have horder := hp' hpU
    by_cases hk0 : k < 0
    · simp only [hpU, hk0, and_self, if_true, Finsupp.coe_zero, Pi.zero_apply]
      apply laurentCoeffAt_eq_zero_of_lt_order
      calc (k : WithTop ℤ) < (0 : WithTop ℤ) := by exact_mod_cast hk0
        _ ≤ meromorphicOrderAt f p := horder
    · simp [hpU, hk0]
  · simp [hpU]

/-- Extraction from a meromorphic function with finitely many poles. -/
noncomputable def ofMeromorphicOn {f : ℂ → ℂ} (_hf : MeromorphicOn f U)
    (hfin : {p ∈ U | meromorphicOrderAt f p < 0}.Finite) : PrincipalPartData U :=
  mk' (mlCoeff f U) (mlCoeff_coeff_neg f U) (mlCoeff_mem_of_ne_zero f U)
    (mlCoeff_finite_support hfin)

theorem realizes_ofMeromorphicOn {f : ℂ → ℂ} (hf : MeromorphicOn f U)
    (hfin : {p ∈ U | meromorphicOrderAt f p < 0}.Finite) :
    Realizes f (ofMeromorphicOn hf hfin) := by
  refine ⟨hf, fun p hp k hk => ?_⟩
  change laurentCoeffAt f p k = mlCoeff f U p k
  rw [mlCoeff_apply, if_pos ⟨hp, hk⟩]

theorem Realizes.add {f g : ℂ → ℂ} {D E : PrincipalPartData U} (hf : Realizes f D)
    (hg : Realizes g E) : Realizes (f + g) (D + E) := by
  obtain ⟨hfmero, hfeq⟩ := hf
  obtain ⟨hgmero, hgeq⟩ := hg
  refine ⟨fun p hp => (hfmero p hp).add (hgmero p hp), fun p hp k hk => ?_⟩
  rw [laurentCoeffAt_add (hfmero p hp) (hgmero p hp), hfeq p hp k hk, hgeq p hp k hk,
    coeff_add, Pi.add_apply, Finsupp.add_apply]

theorem Realizes.smul {f : ℂ → ℂ} {D : PrincipalPartData U} (c : ℂ) (hf : Realizes f D) :
    Realizes (fun z => c * f z) (c • D) := by
  obtain ⟨hfmero, hfeq⟩ := hf
  refine ⟨fun p hp => (MeromorphicAt.const c p).mul (hfmero p hp), fun p hp k hk => ?_⟩
  rw [laurentCoeffAt_const_mul, hfeq p hp k hk, coeff_smul, Pi.smul_apply, Finsupp.smul_apply,
    smul_eq_mul]

/-- Two realizations differ by a pole-free function (the ML gluing atom: differences of
solutions are holomorphic-after-repair). -/
theorem Realizes.sub_orderAt_nonneg {f g : ℂ → ℂ} {D : PrincipalPartData U} (hf : Realizes f D)
    (hg : Realizes g D) : ∀ p ∈ U, 0 ≤ meromorphicOrderAt (fun z => f z - g z) p := by
  obtain ⟨hfmero, hfeq⟩ := hf
  obtain ⟨hgmero, hgeq⟩ := hg
  intro p hp
  have hsub : MeromorphicAt (fun z => f z - g z) p := (hfmero p hp).sub (hgmero p hp)
  apply (forall_neg_laurentCoeffAt_eq_zero_iff hsub).mp
  intro k hk
  rw [laurentCoeffAt_sub (hfmero p hp) (hgmero p hp), hfeq p hp k hk, hgeq p hp k hk, sub_self]

/-- Realizing the zero datum = no poles on `U`. -/
theorem realizes_zero_iff {f : ℂ → ℂ} (hf : MeromorphicOn f U) :
    Realizes f (0 : PrincipalPartData U) ↔ ∀ p ∈ U, 0 ≤ meromorphicOrderAt f p := by
  constructor
  · intro hR p hp
    apply (forall_neg_laurentCoeffAt_eq_zero_iff (hf p hp)).mp
    intro k hk
    rw [hR.2 p hp k hk, coeff_zero]
    rfl
  · intro horder
    refine ⟨hf, fun p hp k hk => ?_⟩
    rw [laurentCoeffAt_eq_zero_of_lt_order
      (lt_of_lt_of_le (by exact_mod_cast hk) (horder p hp))]
    rfl

end PrincipalPartData

end RS
