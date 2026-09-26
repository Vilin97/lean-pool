/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.ClampedObservable
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.CarrierObservable
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.EfronSteinAE

/-!
# The Efron–Stein bound for the fixed-phase observable

The capstone.  Combining the product-measurable clamped observable
(`ClampedObservable`) with the landed a.e.-measurable Efron–Stein transfer
(`efronStein_transfer_ae_restriction`), we obtain the Efron–Stein variance bound for the
fixed-phase observable `F_σ` in the **two-field surgery** (`patchCore`) form that
the fixed-phase variance assembly consumes.

The two evaluation-point identities are *exact* tuple identities (no a.e.
reasoning): with `patchCore` the two-field core surgery,
`Function.update (R a) k (a'|_{coreBox k}) = R (patchCore k a a')`, so the
resampled observable is literally the diagonal observable of the surgered field.
All a.e. reasoning is confined to the single truncation-congruence layer:
`clampedPhaseObservable (R b) = F_σ(b)` for measurable, a.e.-elliptic `b`
(`clampedPhaseObservable_restrict_eq_of_field`), instantiated at `b = a` and at
`b = patchCore k a a'` under `ThetaEllipticLaw` for both draws.
-/

@[expose] public section

open Homogenization
open scoped MeasureTheory ProbabilityTheory BigOperators
open MeasureTheory ProbabilityTheory

namespace Homogenization

variable {d : ℕ}

/-! ## The two-field core surgery -/

/-- The two-field core surgery: `a'` on the core `coreBox ℓ σ j`, `a` off it. -/
noncomputable def patchCore (ℓ : ℝ) (σ : Vec d) (j : Fin d → ℤ) (a a' : CoeffField d) :
    CoeffField d := by
  classical
  exact fun x => if x ∈ coreBox ℓ σ j then a' x else a x

@[simp] theorem patchCore_apply_of_mem {ℓ : ℝ} {σ : Vec d} {j : Fin d → ℤ}
    {a a' : CoeffField d} {x : Vec d} (hx : x ∈ coreBox ℓ σ j) :
    patchCore ℓ σ j a a' x = a' x := by simp [patchCore, hx]

@[simp] theorem patchCore_apply_of_not_mem {ℓ : ℝ} {σ : Vec d} {j : Fin d → ℤ}
    {a a' : CoeffField d} {x : Vec d} (hx : x ∉ coreBox ℓ σ j) :
    patchCore ℓ σ j a a' x = a x := by simp [patchCore, hx]

theorem measurable_patchCore_entry {ℓ : ℝ} {σ : Vec d} {j : Fin d → ℤ}
    {a a' : CoeffField d}
    (ha : ∀ i j' : Fin d, Measurable fun x : Vec d => a x i j')
    (ha' : ∀ i j' : Fin d, Measurable fun x : Vec d => a' x i j') :
    ∀ i j' : Fin d, Measurable fun x : Vec d => patchCore ℓ σ j a a' x i j' := by
  classical
  intro i j'
  have hrw : (fun x : Vec d => patchCore ℓ σ j a a' x i j')
      = fun x : Vec d => if x ∈ coreBox ℓ σ j then a' x i j' else a x i j' := by
    funext x
    by_cases hx : x ∈ coreBox ℓ σ j
    · rw [patchCore_apply_of_mem hx, if_pos hx]
    · rw [patchCore_apply_of_not_mem hx, if_neg hx]
  rw [hrw]
  exact Measurable.ite (measurableSet_coreBox ℓ σ j) (ha' i j') (ha i j')

theorem ae_isEllipticMatrix_patchCore {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {j : Fin d → ℤ}
    {a a' : CoeffField d}
    (ha : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x))
    (ha' : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a' x)) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (patchCore ℓ σ j a a' x) := by
  filter_upwards [ha, ha'] with x hxa hxa'
  by_cases hx : x ∈ coreBox ℓ σ j
  · rw [patchCore_apply_of_mem hx]; exact hxa'
  · rw [patchCore_apply_of_not_mem hx]; exact hxa

/-! ## The exact update identity -/

theorem restrictCoeffField_congr {U : Set (Vec d)} {f g : CoeffField d}
    (h : ∀ x ∈ U, f x = g x) : restrictCoeffField U f = restrictCoeffField U g := by
  funext x
  by_cases hx : x ∈ U
  · rw [restrictCoeffField_apply_of_mem hx, restrictCoeffField_apply_of_mem hx, h x hx]
  · rw [restrictCoeffField_apply_of_not_mem hx, restrictCoeffField_apply_of_not_mem hx]

/-- **Exact update identity.**  Updating the `k`-th coordinate of the diagonal
restriction tuple by a fresh core-restriction of `a'` equals the diagonal
restriction tuple of the surgered field `patchCore k a a'` (using core
disjointness off `k`). -/
theorem update_restrict_eq_restrict_patchCore {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {σ : Vec d}
    {K : Finset (Fin d → ℤ)} (k : {k // k ∈ K}) (a a' : CoeffField d) :
    Function.update
        (fun k' : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k'.val) a) k
        (restrictCoeffField (coreBox ℓ σ k.val) a')
      = fun k' : {k // k ∈ K} =>
          restrictCoeffField (coreBox ℓ σ k'.val) (patchCore ℓ σ k.val a a') := by
  classical
  funext k'
  rcases eq_or_ne k' k with rfl | hkk'
  · rw [Function.update_self]
    refine restrictCoeffField_congr (fun x hx => ?_)
    rw [patchCore_apply_of_mem hx]
  · rw [Function.update_of_ne hkk']
    refine restrictCoeffField_congr (fun x hx => ?_)
    have hne : k.val ≠ k'.val := fun h => hkk' (Subtype.ext h.symm)
    have hxnk : x ∉ coreBox ℓ σ k.val := not_mem_coreBox_of_mem hℓ σ hne hx
    rw [patchCore_apply_of_not_mem hxnk]

/-! ## The Efron–Stein bound -/

/-- **Abstract Efron–Stein patch transfer (opaque-observable core).**  For an
abstract bounded measurable product observable `G` on carrier tuples whose
diagonal agrees a.e. with `Φ` and whose single-coordinate resampling agrees
a.e. (on the product) with the two-field surgery values `Ψ`, the Efron–Stein
transfer yields the variance bound in surgery form.  Keeping `G`, `Φ`, `Ψ`
opaque here keeps elaboration at default heartbeats; the fixed-phase
instantiation is below. -/
theorem efronStein_patch_abstract
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : ι → Set (Vec d)} (hC : ∀ i, MeasurableSet (C i))
    (hsep : Pairwise fun i j => AreUnitSeparated (C i) (C j))
    {L : Measure (RegCoeffField d)} [IsProbabilityMeasure L]
    (hURD : IsRestrictionUnitRangeDependentR L)
    {G : (ι → RegCoeffField d) → ℝ} (hG : Measurable G)
    {M : ℝ} (hMG : ∀ y, |G y| ≤ M)
    {Φ : RegCoeffField d → ℝ} {Ψ : ι → RegCoeffField d → RegCoeffField d → ℝ}
    (hdiag : (G ∘ fun a i => restrictReg (C i) (hC i) a) =ᵐ[L] Φ)
    (hupd : ∀ i : ι, ∀ᵐ p ∂(L.prod L),
      G (Function.update ((fun a j => restrictReg (C j) (hC j) a) p.1) i
          (restrictReg (C i) (hC i) p.2))
        = Ψ i p.1 p.2) :
    Var[Φ; L]
      ≤ (1 / 2) * ∑ i : ι, ∫ a, ∫ a', (Ψ i a a' - Φ a) ^ 2 ∂L ∂L := by
  classical
  set R : RegCoeffField d → (ι → RegCoeffField d) :=
    fun a i => restrictReg (C i) (hC i) a with hRdef
  have key := efronStein_transfer_restriction hC hsep hURD hG hMG R hRdef
  have hRae_prod : ∀ᵐ p ∂(L.prod L), G (R p.1) = Φ p.1 :=
    (Measure.quasiMeasurePreserving_fst).ae hdiag
  have hterm : ∀ i : ι,
      (∫ a, ∫ a', (G (Function.update (R a) i (restrictReg (C i) (hC i) a'))
          - G (R a)) ^ 2 ∂L ∂L)
        = ∫ a, ∫ a', (Ψ i a a' - Φ a) ^ 2 ∂L ∂L := by
    intro i
    have hprodae :
        (fun p : RegCoeffField d × RegCoeffField d =>
          (G (Function.update (R p.1) i (restrictReg (C i) (hC i) p.2))
            - G (R p.1)) ^ 2)
          =ᵐ[L.prod L]
        (fun p : RegCoeffField d × RegCoeffField d =>
          (Ψ i p.1 p.2 - Φ p.1) ^ 2) := by
      filter_upwards [hupd i, hRae_prod] with p h1 h2
      rw [h1, h2]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hprodae] with a haa
    exact integral_congr_ae haa
  calc Var[Φ; L]
      = Var[G ∘ R; L] := (variance_congr hdiag).symm
    _ ≤ (1 / 2) * ∑ i : ι, ∫ a, ∫ a',
          (G (Function.update (R a) i (restrictReg (C i) (hC i) a'))
            - G (R a)) ^ 2 ∂L ∂L := key
    _ = (1 / 2) * ∑ i : ι, ∫ a, ∫ a', (Ψ i a a' - Φ a) ^ 2 ∂L ∂L := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hterm i)

/-- The diagonal a.e. identity for the carrier clamped observable, in the
composed form consumed by `efronStein_patch_abstract`. -/
theorem clampedPhaseObservableR_diag_ae [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ) (P : BlockVec d)
    {L : Measure (RegCoeffField d)} (hL : ThetaEllipticLaw Θ L)
    (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K) :
    ((fun y : {k // k ∈ K} → RegCoeffField d => clampedPhaseObservableR ℓ σ Θ m P K y) ∘
        fun a k => restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) a)
      =ᵐ[L] fun a => phaseObservable ℓ σ m P a.toFun := by
  filter_upwards [hL] with a ha
  exact clampedPhaseObservableR_restrict_eq_of_field hℓ hΘ P K hK a ha

/-- The single-coordinate resampling identity for the carrier clamped
observable: a.e. on the product it equals the fixed-phase observable of the
two-field core surgery. -/
theorem clampedPhaseObservableR_update_ae [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ) (P : BlockVec d)
    {L : Measure (RegCoeffField d)} [IsProbabilityMeasure L]
    (hL : ThetaEllipticLaw Θ L)
    (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K)
    (k : {k // k ∈ K}) :
    ∀ᵐ p ∂(L.prod L),
      clampedPhaseObservableR ℓ σ Θ m P K
          (Function.update
            ((fun a j => restrictReg (coreBox ℓ σ j.val)
              (measurableSet_coreBox ℓ σ j.val) a) p.1) k
            (restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) p.2))
        = phaseObservable ℓ σ m P (patchCore ℓ σ k.val p.1.toFun p.2.toFun) := by
  classical
  have hL1 : ∀ᵐ p ∂(L.prod L),
      ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.1 x) :=
    (Measure.quasiMeasurePreserving_fst).ae hL
  have hL2 : ∀ᵐ p ∂(L.prod L),
      ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.2 x) :=
    (Measure.quasiMeasurePreserving_snd).ae hL
  filter_upwards [hL1, hL2] with p hp1 hp2
  -- every coordinate of the updated tuple lies in its good event
  have hy : ∀ k' : {k // k ∈ K},
      (Function.update
          (fun k'' : {k // k ∈ K} => restrictReg (coreBox ℓ σ k''.val)
            (measurableSet_coreBox ℓ σ k''.val) p.1) k
          (restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) p.2)) k'
        ∈ coreGoodSet ℓ σ Θ k'.1 m := by
    intro k'
    rcases eq_or_ne k' k with rfl | hkk'
    · rw [Function.update_self]
      exact restrictReg_mem_coreGoodSet hp2
    · rw [Function.update_of_ne hkk']
      exact restrictReg_mem_coreGoodSet hp1
  -- the raw tuple of the updated carrier tuple is the updated raw tuple
  have htoFun :
      (fun k' : {k // k ∈ K} =>
        ((Function.update
            (fun k'' : {k // k ∈ K} => restrictReg (coreBox ℓ σ k''.val)
              (measurableSet_coreBox ℓ σ k''.val) p.1) k
            (restrictReg (coreBox ℓ σ k.val)
              (measurableSet_coreBox ℓ σ k.val) p.2)) k').toFun)
        = Function.update
            (fun k' : {k // k ∈ K} =>
              restrictCoeffField (coreBox ℓ σ k'.val) p.1.toFun) k
            (restrictCoeffField (coreBox ℓ σ k.val) p.2.toFun) := by
    funext k'
    rcases eq_or_ne k' k with rfl | hkk'
    · rw [Function.update_self, Function.update_self]
      exact restrictReg_toFun_eq _ _ p.2
    · rw [Function.update_of_ne hkk', Function.update_of_ne hkk']
      exact restrictReg_toFun_eq _ _ p.1
  exact (clampedPhaseObservableR_eq_of_good P hy).trans
    ((congrArg (clampedPhaseObservable ℓ σ Θ m P K)
        (htoFun.trans
          (update_restrict_eq_restrict_patchCore hℓ.le k p.1.toFun p.2.toFun))).trans
      (clampedPhaseObservable_restrict_eq_of_field hℓ hΘ P K hK
        (patchCore ℓ σ k.val p.1.toFun p.2.toFun)
        (measurable_patchCore_entry (fun i j => p.1.entry_measurable i j)
          (fun i j => p.2.entry_measurable i j))
        (ae_isEllipticMatrix_patchCore hp1 hp2)))

/-- **Efron–Stein for the fixed-phase observable.**
Under a restriction-unit-range-dependent, `Θ`-elliptic probability law on the
carrier, the
variance of the fixed-phase observable is controlled by the sum, over the cores
meeting the cube, of the two-field core-resampling energies — the `patchCore`
form consumed by the fixed-phase variance assembly.  The product-measurable
witness is the genuinely carrier-measurable clamped observable
`clampedPhaseObservableR` (`CarrierObservable.lean`), so the *genuine*
`efronStein_transfer_restriction` applies (no a.e.-measurability relaxation
needed). -/
theorem efronStein_phaseObservable [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ) (P : BlockVec d)
    {L : Measure (RegCoeffField d)} [IsProbabilityMeasure L]
    (hURD : IsRestrictionUnitRangeDependentR L) (hL : ThetaEllipticLaw Θ L)
    (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K) :
    Var[fun a => phaseObservable ℓ σ m P a.toFun; L]
      ≤ (1 / 2) * ∑ k : {k // k ∈ K},
          ∫ a, ∫ a',
            (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a.toFun a'.toFun)
              - phaseObservable ℓ σ m P a.toFun) ^ 2 ∂L ∂L := by
  classical
  have hsep : Pairwise fun i j : {k // k ∈ K} =>
      AreUnitSeparated (coreBox ℓ σ i.val) (coreBox ℓ σ j.val) :=
    pairwise_areUnitSeparated_coreBox hℓ.le σ (Subtype.val_injective)
  exact efronStein_patch_abstract
    (C := fun i : {k // k ∈ K} => coreBox ℓ σ i.val)
    (fun i => measurableSet_coreBox ℓ σ i.val) hsep hURD
    (measurable_clampedPhaseObservableR hΘ P K)
    (abs_clampedPhaseObservableR_le hΘ P K)
    (clampedPhaseObservableR_diag_ae hℓ hΘ P hL K hK)
    (fun k => clampedPhaseObservableR_update_ae hℓ hΘ P hL K hK k)

end Homogenization
