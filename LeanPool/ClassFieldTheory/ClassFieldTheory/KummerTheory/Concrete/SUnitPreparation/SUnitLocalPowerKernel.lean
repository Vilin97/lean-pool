/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation
/-!
# The local-power kernel of S-units

The localization map on `S`-units, its kernel, its quotient by
  global powers, and the associated Kummer radical.
-/

@[expose] public section

open scoped NumberField IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

open scoped Classical in
/-- The diagonal localization map
`Kˢ → ∏ v ∈ T, K_vˣ / K_vˣⁿ`. -/
noncomputable def sUnitLocalPowerMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S →*
      ∀ v : T,
        ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range :=
  (IdeleGroup.principalLocalQuotientMap
      (K := K) T
      (fun v =>
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletion K)ˣ →*
            (v.1.adicCompletion K)ˣ).range)).comp
    (SUnitGroup (K := K) S).subtype

open scoped Classical in
/-- The subgroup `Δ` of `S`-units which are local `n`-th powers at every
place in `T`. -/
def sUnitLocalPowerKernel
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SUnitGroup (K := K) S) :=
  MonoidHom.ker (sUnitLocalPowerMap (K := K) n S T)

open scoped Classical in
/-- Elementwise description of the local-power kernel `Δ`. -/
theorem mem_sUnitLocalPowerKernel_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (x : SUnitGroup (K := K) S) :
    x ∈ sUnitLocalPowerKernel (K := K) n S T ↔
      ∀ v : T,
        Units.map
            (algebraMap K
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)).toMonoidHom
            (x : Kˣ) ∈
          (powMonoidHom (n : ℕ) :
            ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range := by
  rw [sUnitLocalPowerKernel, MonoidHom.mem_ker]
  constructor
  · intro hx v
    have hv := congrFun hx v
    rw [Pi.one_apply] at hv
    exact (QuotientGroup.eq_one_iff _).mp hv
  · intro hx
    funext v
    exact (QuotientGroup.eq_one_iff _).mpr (hx v)

open scoped Classical in
/-- Global `n`-th powers are local `n`-th powers at every place. -/
theorem nthPowerSubgroup_le_sUnitLocalPowerKernel
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) S →*
          SUnitGroup (K := K) S).range ≤
      sUnitLocalPowerKernel (K := K) n S T := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := SUnitGroup (K := K) S)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [sUnitLocalPowerKernel, MonoidHom.mem_ker, map_pow]
  change (sUnitLocalPowerMap (K := K) n S T y) ^ (n : ℕ) = 1
  funext v
  exact (QuotientGroup.eq_one_iff _).mpr
    ((MonoidHom.mem_range
      (G :=
        ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)).mpr
      ⟨_, by rw [powMonoidHom_apply]⟩)

open scoped Classical in
/-- The copy of `Kˢⁿ` inside the local-power kernel `Δ`. -/
def sUnitLocalPowerKernelNthPowers
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (sUnitLocalPowerKernel (K := K) n S T) :=
  ((powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) S →*
        SUnitGroup (K := K) S).range).comap
    (sUnitLocalPowerKernel (K := K) n S T).subtype

open scoped Classical in
/-- The canonical map `Δ / Kˢⁿ → Kˢ / Kˢⁿ`. -/
def sUnitLocalPowerKernelQuotientMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitLocalPowerKernel (K := K) n S T ⧸
        sUnitLocalPowerKernelNthPowers (K := K) n S T →*
      SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range :=
  QuotientGroup.map
    (sUnitLocalPowerKernelNthPowers (K := K) n S T)
    (powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) S →*
        SUnitGroup (K := K) S).range
    (sUnitLocalPowerKernel (K := K) n S T).subtype
    (by
      intro x hx
      exact hx)

open scoped Classical in
/-- Inclusion of `Δ` induces an injection on quotients by `Kˢⁿ`. -/
theorem sUnitLocalPowerKernelQuotientMap_injective
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (sUnitLocalPowerKernelQuotientMap (K := K) n S T) := by
  intro q r hqr
  induction q using QuotientGroup.induction_on' with
  | _ x =>
      induction r using QuotientGroup.induction_on' with
      | _ y =>
          apply (QuotientGroup.eq_iff_div_mem).2
          change
            (x.1 / y.1) ∈
              (powMonoidHom (n : ℕ) :
                SUnitGroup (K := K) S →*
                  SUnitGroup (K := K) S).range
          apply (QuotientGroup.eq_iff_div_mem).1
          exact hqr

open scoped Classical in
/-- The restricted radical quotient `Δ / Kˢⁿ` is finite. -/
noncomputable instance finite_sUnitLocalPowerKernelQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite
      (sUnitLocalPowerKernel (K := K) n S T ⧸
        sUnitLocalPowerKernelNthPowers (K := K) n S T) :=
  Finite.of_injective
    (sUnitLocalPowerKernelQuotientMap (K := K) n S T)
    (sUnitLocalPowerKernelQuotientMap_injective
      (K := K) n S T)

open scoped Classical in
/-- The restricted radical quotient has cardinality at most `n ^ s`. -/
theorem card_sUnitLocalPowerKernelQuotient_le
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (sUnitLocalPowerKernel (K := K) n S T ⧸
          sUnitLocalPowerKernelNthPowers (K := K) n S T) ≤
      (n : ℕ) ^ totalPlaceCard (K := K) S := by
  rw [← card_sUnit_nthPowerQuotient (K := K) S n hmu]
  exact Nat.card_le_card_of_injective
    (sUnitLocalPowerKernelQuotientMap (K := K) n S T)
    (sUnitLocalPowerKernelQuotientMap_injective
      (K := K) n S T)

open scoped Classical in
/-- The local-power kernel, regarded as an actual subgroup of `Kˣ`. -/
def sUnitLocalPowerRadical
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  (sUnitLocalPowerKernel (K := K) n S T).map
    (SUnitGroup (K := K) S).subtype

open scoped Classical in
/-- Membership in the local-power radical is membership in the kernel
through the canonical `S`-unit inclusion. -/
theorem mem_sUnitLocalPowerRadical_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) :
    x ∈ sUnitLocalPowerRadical (K := K) n S T ↔
      ∃ hx : x ∈ SUnitGroup (K := K) S,
        (⟨x, hx⟩ : SUnitGroup (K := K) S) ∈
          sUnitLocalPowerKernel (K := K) n S T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hlocal⟩
    exact ⟨⟨x, hx⟩, hlocal, rfl⟩

end KummerTheory
