/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization project
-/
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.TateAlgebraTopology
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornBanachTheorem

/-!
# The Tate topology on the multivariate restricted power series ring `A⟨X₁,…,Xₙ⟩`

This file equips `restrictedMvPowerSeriesSubring n A` (the ring `A⟨X₁,…,Xₙ⟩` of restricted
power series in `n` variables, for arbitrary `n : ℕ`) with its Tate-ring topology, generalizing
the `n = 1` stack (`TateAlgebra A`, `TateAlgebraTopology.lean`) and the `n = 2` stack
(`TateAlgebra₂`) to a free index `n`.

Following **Wedhorn, *Adic Spaces*, Proposition 6.21(2)** (p. 52): if `A` is a Tate ring with ring
of definition `B = A₀` and finitely generated ideal of definition `I`, then `A⟨X⟩` is again a Tate
ring, with ring of definition `B⟨X⟩ = A₀⟨X⟩` (restricted power series with `A₀`-coefficients) and
finitely generated ideal of definition `I⟨X⟩ = I · A₀⟨X⟩`.

## Main definitions (this file, building up)

* `MvTateAlgebra.mvPairSubring n P`: the ring of definition `A₀⟨X₁,…,Xₙ⟩` — restricted power
  series all of whose coefficients lie in `P.A₀`.
* `MvTateAlgebra.mvPairIdeal n P`: the ideal of definition `I · A₀⟨X₁,…,Xₙ⟩`.

## References

* Wedhorn, *Adic Spaces* (arXiv:1910.05934), Proposition 6.21(2), p. 52.
* `n = 1` template: `Adic spaces/TateAlgebraTopology.lean` (`TateAlgebra.pairSubring`,
  `TateAlgebra.pairIdeal`).
-/

@[expose] public section

open Filter Topology Pointwise

universe u

namespace MvTateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [NonarchimedeanRing A] [IsTopologicalRing A]

/-- The subring of `A⟨X₁,…,Xₙ⟩` consisting of restricted power series whose coefficients all lie
in `P.A₀`. This is the "ring of definition" `A₀⟨X₁,…,Xₙ⟩` for the multivariate Tate algebra
(Wedhorn, Prop 6.21(2): `B⟨X⟩` is a ring of definition). Generalizes `TateAlgebra.pairSubring`
from `Fin 1` to `Fin n`. -/
noncomputable def mvPairSubring (n : ℕ) (P : PairOfDefinition A) :
    Subring ↥(restrictedMvPowerSeriesSubring n A) where
  carrier := {f | ∀ s : Fin n →₀ ℕ, MvPowerSeries.coeff s f.val ∈ P.A₀}
  mul_mem' {f g} hf hg s := by
    simp only [Subring.coe_mul, MvPowerSeries.coeff_mul]
    exact P.A₀.toSubsemiring.sum_mem
      fun p _ => P.A₀.mul_mem (hf p.1) (hg p.2)
  one_mem' s := by
    simp only [OneMemClass.coe_one, MvPowerSeries.coeff_one]
    split
    · exact P.A₀.one_mem
    · exact P.A₀.zero_mem
  add_mem' {f g} hf hg s := by
    simp only [Subring.coe_add, map_add]
    exact P.A₀.add_mem (hf s) (hg s)
  zero_mem' s := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact P.A₀.zero_mem
  neg_mem' {f} hf s := by
    simp only [NegMemClass.coe_neg, map_neg]
    exact P.A₀.neg_mem (hf s)

omit [IsTopologicalRing A] in
/-- Membership in `mvPairSubring n P` means all coefficients lie in `P.A₀`. -/
theorem mem_mvPairSubring (n : ℕ) (P : PairOfDefinition A)
    (f : ↥(restrictedMvPowerSeriesSubring n A)) :
    f ∈ mvPairSubring n P ↔
      ∀ s : Fin n →₀ ℕ, MvPowerSeries.coeff s f.val ∈ P.A₀ :=
  Iff.rfl

/-- The constant power series embedding `P.A₀ →+* A₀⟨X₁,…,Xₙ⟩`.
Sends `a ∈ A₀` to the constant restricted power series `C(a)`. Generalizes
`TateAlgebra.pairConstantHom`. -/
noncomputable def mvPairConstantHom (n : ℕ) (P : PairOfDefinition A) :
    P.A₀ →+* mvPairSubring n P where
  toFun a := ⟨⟨MvPowerSeries.C a.val,
      MvPowerSeries.IsRestricted_algebraMap a.val⟩, by
    intro s; classical
    simp only [MvPowerSeries.coeff_C]
    split
    · exact a.2
    · exact P.A₀.zero_mem⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_mul, map_mul]))
  map_zero' := Subtype.ext (Subtype.ext (map_zero _))
  map_add' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_add, map_add]))

/-- The ideal `I · A₀⟨X₁,…,Xₙ⟩` inside `A₀⟨X₁,…,Xₙ⟩`, defined as the image of `P.I` under the
constant power series embedding. This is the ideal of definition for `A₀⟨X⟩` (Wedhorn, Prop
6.21(2): `I⟨X⟩ = I · B⟨X⟩`). Generalizes `TateAlgebra.pairIdeal`. -/
noncomputable def mvPairIdeal (n : ℕ) (P : PairOfDefinition A) :
    Ideal (mvPairSubring n P) :=
  Ideal.map (mvPairConstantHom n P) P.I

omit [IsTopologicalRing A] in
/-- The ideal `I · A₀⟨X₁,…,Xₙ⟩` is finitely generated (because `I` is). -/
theorem mvPairIdeal_fg (n : ℕ) (P : PairOfDefinition A) :
    (mvPairIdeal n P).FG :=
  P.fg.map _

/-! ### T-MVT-2: The natural Tate topology on `A⟨X₁,…,Xₙ⟩` (Wedhorn Prop 6.21(2))

This section ports the entire `n = 1` topology+completeness construction
(`Adic spaces/TateAlgebraTopology.lean`, declarations `tateAlgNhd` …
`tateAlgebraTopology'_completeSpace`) from `Fin 1` to a free index `n : ℕ`.

Following **Wedhorn, *Adic Spaces*, Proposition 6.21(2)** (p. 52): the `n`-variable Tate
algebra `A⟨X⟩` is again a Tate ring, with ring of definition `B⟨X⟩ = A₀⟨X⟩` and finitely
generated ideal of definition `I⟨X⟩ = I · A₀⟨X⟩`.

Per the project's design directive, we do **not** install global topology/uniform-space
instances (that would create a topology diamond at `n = 1`, where `TateAlgebra A` is an
`abbrev` for `restrictedMvPowerSeriesSubring 1 A`). Instead we expose `def`/`theorem`
forms that take the topology/uniform-space as `@`-applied explicit arguments. -/

/-- The `n`-th basic neighborhood of `0` in `A⟨X₁,…,Xₙ⟩`: the set-image of
`(mvPairIdeal n P)^k` under the inclusion `mvPairSubring n P ↪ A⟨X⟩`, viewed as an additive
subgroup. Generalizes `TateAlgebra.tateAlgNhd` (TateAlgebraTopology.lean) from `Fin 1`
to `Fin n`; Wedhorn Prop 6.21(2). -/
noncomputable def mvTateAlgNhd (n : ℕ) (P : PairOfDefinition A) (k : ℕ) :
    AddSubgroup ↥(restrictedMvPowerSeriesSubring n A) :=
  ((mvPairIdeal n P) ^ k).toAddSubgroup.map
    (mvPairSubring n P).subtype.toAddMonoidHom

omit [IsTopologicalRing A] in
/-- The neighborhoods are antitone in `k`. Generalizes `TateAlgebra.tateAlgNhd_antitone`
from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTateAlgNhd_antitone (n : ℕ) (P : PairOfDefinition A) :
    Antitone (mvTateAlgNhd n P) :=
  fun _ _ h ↦ AddSubgroup.map_mono
    (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

omit [IsTopologicalRing A] in
/-- `0 ∈ mvTateAlgNhd n P k` for all `k`. Generalizes `TateAlgebra.zero_mem_tateAlgNhd`
from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem zero_mem_mvTateAlgNhd (n : ℕ) (P : PairOfDefinition A) (k : ℕ) :
    (0 : ↥(restrictedMvPowerSeriesSubring n A)) ∈ mvTateAlgNhd n P k :=
  ⟨0, ((mvPairIdeal n P) ^ k).zero_mem, map_zero _⟩

/-- Auxiliary ideal: elements of `mvPairSubring n P` all of whose coefficients lie in the
image of a given ideal `I : Ideal P.A₀` under the inclusion `P.A₀ ↪ A`. Generalizes
`TateAlgebra.coeffInIdealIdeal` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
noncomputable def mvCoeffInIdealIdeal (n : ℕ) (P : PairOfDefinition A) (I : Ideal P.A₀) :
    Ideal ↥(mvPairSubring n P) where
  carrier := {z | ∀ l, ∃ b : P.A₀, b ∈ I ∧ (b : A) = MvPowerSeries.coeff l z.val.val}
  zero_mem' l := ⟨0, I.zero_mem, by simp⟩
  add_mem' {z w} hz hw l := by
    obtain ⟨b_z, hb_z, heq_z⟩ := hz l
    obtain ⟨b_w, hb_w, heq_w⟩ := hw l
    refine ⟨b_z + b_w, I.add_mem hb_z hb_w, ?_⟩
    change ((b_z + b_w : P.A₀) : A) = MvPowerSeries.coeff l (z + w).val.val
    push_cast
    rw [heq_z, heq_w, ← map_add]
  smul_mem' r z hz l := by
    classical
    have hr : ∀ l_1, MvPowerSeries.coeff l_1 r.val.val ∈ P.A₀ := r.property
    let f : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) → P.A₀ := fun p =>
      ⟨MvPowerSeries.coeff p.1 r.val.val, hr p.1⟩ *
        (hz p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · refine I.sum_mem fun p _ => ?_
      exact I.mul_mem_left _ (hz p.2).choose_spec.1
    · change ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (r • z).val.val
      push_cast [f]
      change (∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 r.val.val * ((hz p.2).choose : A)) =
        MvPowerSeries.coeff l (r • z).val.val
      rw [show (r • z).val.val = r.val.val * z.val.val from rfl, MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(hz p.2).choose_spec.2]

omit [IsTopologicalRing A] in
/-- Constant series from `P.I^k` have their unique nonzero coefficient in `P.I^k`.
Generalizes `TateAlgebra.pairConstantHom_mem_coeffInIdeal` from `Fin 1` to `Fin n`;
Wedhorn Prop 6.21(2). -/
private theorem mvPairConstantHom_mem_coeffInIdeal (n : ℕ) (P : PairOfDefinition A) {k : ℕ}
    (c : P.A₀) (hc : c ∈ P.I ^ k) :
    mvPairConstantHom n P c ∈ mvCoeffInIdealIdeal n P (P.I ^ k) := by
  intro l
  classical
  by_cases hl : l = 0
  · refine ⟨c, hc, ?_⟩
    subst hl
    change (c : A) = MvPowerSeries.coeff 0 (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_zero_C]
  · refine ⟨0, (P.I ^ k).zero_mem, ?_⟩
    change (0 : A) = MvPowerSeries.coeff l (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_C, if_neg hl]

omit [IsTopologicalRing A] in
/-- `mvPairIdeal n P ⊆ mvCoeffInIdealIdeal n P P.I`. Generalizes
`TateAlgebra.pairIdeal_le_coeffInIdeal` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvPairIdeal_le_coeffInIdeal (n : ℕ) (P : PairOfDefinition A) :
    mvPairIdeal n P ≤ mvCoeffInIdealIdeal n P P.I := by
  unfold mvPairIdeal
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  change mvPairConstantHom n P c ∈ mvCoeffInIdealIdeal n P P.I
  have h1 : c ∈ P.I ^ 1 := by rw [pow_one]; exact hc
  have := mvPairConstantHom_mem_coeffInIdeal n P (k := 1) c h1
  convert this using 1
  rw [pow_one]

omit [IsTopologicalRing A] in
/-- The auxiliary ideal is compatible with ideal multiplication in `P.A₀`. Generalizes
`TateAlgebra.coeffInIdealIdeal_mul_mono` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvCoeffInIdealIdeal_mul_mono (n : ℕ) (P : PairOfDefinition A) {I₁ I₂ : Ideal P.A₀}
    {J₁ J₂ : Ideal ↥(mvPairSubring n P)}
    (h₁ : J₁ ≤ mvCoeffInIdealIdeal n P I₁) (h₂ : J₂ ≤ mvCoeffInIdealIdeal n P I₂) :
    J₁ * J₂ ≤ mvCoeffInIdealIdeal n P (I₁ * I₂) := by
  intro z hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb l
    classical
    have ha' : a ∈ mvCoeffInIdealIdeal n P I₁ := h₁ ha
    have hb' : b ∈ mvCoeffInIdealIdeal n P I₂ := h₂ hb
    let f : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) → P.A₀ := fun p =>
      (ha' p.1).choose * (hb' p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · refine (I₁ * I₂).sum_mem fun p _ => ?_
      exact Ideal.mul_mem_mul (ha' p.1).choose_spec.1 (hb' p.2).choose_spec.1
    · change ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (a * b).val.val
      push_cast [f]
      change (∑ p ∈ Finset.antidiagonal l,
          ((ha' p.1).choose : A) * ((hb' p.2).choose : A)) =
        MvPowerSeries.coeff l (a * b).val.val
      rw [show (a * b).val.val = a.val.val * b.val.val from rfl, MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(ha' p.1).choose_spec.2, (hb' p.2).choose_spec.2]
  · intro z₁ z₂ h₁' h₂' l
    obtain ⟨b₁, hb₁, heq₁⟩ := h₁' l
    obtain ⟨b₂, hb₂, heq₂⟩ := h₂' l
    refine ⟨b₁ + b₂, (I₁ * I₂).add_mem hb₁ hb₂, ?_⟩
    change ((b₁ : A) + (b₂ : A)) = MvPowerSeries.coeff l (z₁ + z₂).val.val
    rw [show (z₁ + z₂).val.val = z₁.val.val + z₂.val.val from rfl, map_add,
      ← heq₁, ← heq₂]

omit [IsTopologicalRing A] in
/-- `(mvPairIdeal n P)^k ⊆ mvCoeffInIdealIdeal n P (P.I^k)`. Generalizes
`TateAlgebra.pairIdeal_pow_le_coeffInIdeal` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvPairIdeal_pow_le_coeffInIdeal (n : ℕ) (P : PairOfDefinition A) (k : ℕ) :
    (mvPairIdeal n P) ^ k ≤ mvCoeffInIdealIdeal n P (P.I ^ k) := by
  induction k with
  | zero =>
    intro z _ l
    refine ⟨⟨MvPowerSeries.coeff l z.val.val, z.property l⟩, ?_, rfl⟩
    simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mvCoeffInIdealIdeal_mul_mono n P ih (mvPairIdeal_le_coeffInIdeal n P)

omit [IsTopologicalRing A] in
/-- If `y ∈ mvTateAlgNhd n P k`, then every coefficient of `y` lies in the image of `P.I^k`
under `Subtype.val`. Generalizes `TateAlgebra.tateAlgNhd_coeff_mem` from `Fin 1` to `Fin n`;
Wedhorn Prop 6.21(2). -/
theorem mvTateAlgNhd_coeff_mem (n : ℕ) (P : PairOfDefinition A) (k : ℕ)
    {y : ↥(restrictedMvPowerSeriesSubring n A)} (hy : y ∈ mvTateAlgNhd n P k) (l : Fin n →₀ ℕ) :
    ∃ b : P.A₀, b ∈ P.I ^ k ∧ (b : A) = MvPowerSeries.coeff l y.val := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact mvPairIdeal_pow_le_coeffInIdeal n P k hz l

omit [IsTopologicalRing A] in
/-- The product `mvTateAlgNhd n P k · mvTateAlgNhd n P k ⊆ mvTateAlgNhd n P i`. Generalizes
`TateAlgebra.tateAlgNhd_mul` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
private theorem mvTateAlgNhd_mul (n : ℕ) (P : PairOfDefinition A) (i : ℕ) :
    ∃ j, (mvTateAlgNhd n P j : Set ↥(restrictedMvPowerSeriesSubring n A)) *
      (mvTateAlgNhd n P j : Set ↥(restrictedMvPowerSeriesSubring n A)) ⊆
        (mvTateAlgNhd n P i : Set ↥(restrictedMvPowerSeriesSubring n A)) := by
  refine ⟨i, ?_⟩
  rintro _ ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨d₂, hd₂, rfl⟩, rfl⟩
  refine ⟨d₁ * d₂, ?_, MulMemClass.coe_mul ..⟩
  exact Ideal.pow_le_pow_right (Nat.le_add_left i i)
    (pow_add (mvPairIdeal n P) i i ▸ Ideal.mul_mem_mul hd₁ hd₂)

omit [NonarchimedeanRing A] in
/-- For any `a ∈ A` and any `k`, there exists `m` such that `a · b ∈ image P.I^k` whenever
`b ∈ image P.I^m`. Generalizes `TateAlgebra.exists_mul_pow_subset_pow` from `Fin 1` to
`Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvExists_mul_pow_subset_pow (P : PairOfDefinition A) (a : A) (k : ℕ) :
    ∃ m : ℕ, ∀ b : P.A₀, b ∈ P.I ^ m →
      ∃ c : P.A₀, c ∈ P.I ^ k ∧ (c : A) = a * (b : A) := by
  have hU : (Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀)) ∈ nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  have hcont : Continuous fun b : A => a * b := continuous_const.mul continuous_id
  have hV : (fun b : A => a * b) ⁻¹' (Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀)) ∈
      nhds (0 : A) :=
    hcont.continuousAt.preimage_mem_nhds (by
      rw [show (a * (0 : A)) = (0 : A) from mul_zero a]
      exact hU)
  obtain ⟨m, -, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp hV
  refine ⟨m, fun b hb => ?_⟩
  have hbA : (b : A) ∈ (Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀)) :=
    ⟨b, hb, rfl⟩
  have := hm hbA
  simp only [Set.mem_preimage, Set.mem_image] at this
  exact this

/-- For `x ∈ A⟨X⟩` and `k`, eventually every coefficient of `x` lies in `image P.I^k`.
Generalizes `TateAlgebra.tateAlgebra_coeff_eventually_in_pow` from `Fin 1` to `Fin n`;
Wedhorn Prop 6.21(2). -/
theorem mvTateAlgebra_coeff_eventually_in_pow (n : ℕ) (P : PairOfDefinition A)
    (x : ↥(restrictedMvPowerSeriesSubring n A)) (k : ℕ) :
    ∀ᶠ (l : Fin n →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) : Set A) := by
  have hres : Filter.Tendsto
      (fun l : Fin n →₀ ℕ => MvPowerSeries.coeff l x.val)
      Filter.cofinite (nhds (0 : A)) := x.property
  have hU : (Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) : Set A) ∈ nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  exact hres hU

omit [IsTopologicalRing A] in
/-- Reverse coefficient characterization (principal case): if `P.I = (π)` for `π` a unit in
`A`, and `y ∈ mvPairSubring n P` has all coefficients in `image P.I^k`, then
`y ∈ mvTateAlgNhd n P k`. Generalizes `TateAlgebra.tateAlgNhd_of_coeff_mem_principal` from
`Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTateAlgNhd_of_coeff_mem_principal (n : ℕ) (P : PairOfDefinition A) (k : ℕ)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    {y : ↥(restrictedMvPowerSeriesSubring n A)} (hy_pair : y ∈ mvPairSubring n P)
    (hy_coeff : ∀ l : Fin n →₀ ℕ, ∃ b : P.A₀, b ∈ P.I ^ k ∧
      (b : A) = MvPowerSeries.coeff l y.val) :
    y ∈ mvTateAlgNhd n P k := by
  classical
  let πinv : A := ↑hπ_unit.unit⁻¹
  have hπinv_mul : (π : A) * πinv = 1 := hπ_unit.mul_val_inv
  have hπinv_pow : (π : A) ^ k * πinv ^ k = 1 := by
    rw [← mul_pow, hπinv_mul, one_pow]
  have hpow : (P.I ^ k : Ideal P.A₀) = Ideal.span {π ^ k} := by
    rw [hπ_gen, Ideal.span_singleton_pow]
  let g_val : ↥(restrictedMvPowerSeriesSubring n A) :=
    algebraMap A ↥(restrictedMvPowerSeriesSubring n A) (πinv ^ k) * y
  have hg_in : g_val ∈ mvPairSubring n P := by
    intro l
    have hcoeff_g : MvPowerSeries.coeff l g_val.val =
        πinv ^ k * MvPowerSeries.coeff l y.val := by
      change MvPowerSeries.coeff l
        ((MvPowerSeries.C (πinv ^ k) : MvPowerSeries (Fin n) A) * y.val) = _
      rw [MvPowerSeries.coeff_C_mul]
    change MvPowerSeries.coeff l g_val.val ∈ P.A₀
    rw [hcoeff_g]
    obtain ⟨b, hb_mem, hb_eq⟩ := hy_coeff l
    rw [← hb_eq]
    rw [hpow] at hb_mem
    obtain ⟨a, ha_eq⟩ := Ideal.mem_span_singleton.mp hb_mem
    rw [ha_eq]
    change πinv ^ k * ((π ^ k * a : P.A₀) : A) ∈ P.A₀
    have : πinv ^ k * ((π ^ k * a : P.A₀) : A) = (a : A) := by
      push_cast
      rw [show πinv ^ k * ((π : A) ^ k * (a : A)) = ((π : A) ^ k * πinv ^ k) * (a : A) by ring,
        hπinv_pow, one_mul]
    rw [this]
    exact a.property
  let g_in_subring : ↥(mvPairSubring n P) := ⟨g_val, hg_in⟩
  have hy_eq : (⟨y, hy_pair⟩ : ↥(mvPairSubring n P)) =
      mvPairConstantHom n P (π ^ k) * g_in_subring := by
    refine Subtype.ext (Subtype.ext ?_)
    ext l
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l ((MvPowerSeries.C ((π : A) ^ k)) *
        ((MvPowerSeries.C (πinv ^ k)) * y.val))
    rw [← mul_assoc, ← map_mul, hπinv_pow, map_one, one_mul]
  refine ⟨⟨y, hy_pair⟩, ?_, rfl⟩
  rw [hy_eq]
  have hπ_in : mvPairConstantHom n P π ∈ mvPairIdeal n P := by
    unfold mvPairIdeal
    exact Ideal.mem_map_of_mem _
      (by rw [hπ_gen]; exact Ideal.mem_span_singleton_self π)
  have hπn_in : mvPairConstantHom n P (π ^ k) ∈ (mvPairIdeal n P) ^ k := by
    rw [map_pow]
    exact Ideal.pow_mem_pow hπ_in k
  exact ((mvPairIdeal n P) ^ k).mul_mem_right g_in_subring hπn_in

omit [IsTopologicalRing A] in
/-- Easy case of leftMul: when `x ∈ mvPairSubring n P`, multiplication by `x` preserves the
basic neighborhoods. Generalizes `TateAlgebra.tateAlgNhd_leftMul_of_mem` from `Fin 1` to
`Fin n`; Wedhorn Prop 6.21(2). -/
private theorem mvTateAlgNhd_leftMul_of_mem (n : ℕ) (P : PairOfDefinition A)
    {x : ↥(restrictedMvPowerSeriesSubring n A)} (hx : x ∈ mvPairSubring n P) (i : ℕ) :
    (mvTateAlgNhd n P i : Set ↥(restrictedMvPowerSeriesSubring n A)) ⊆
      (x * ·) ⁻¹' (mvTateAlgNhd n P i : Set ↥(restrictedMvPowerSeriesSubring n A)) := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨x, hx⟩ * y, ?_, ?_⟩
  · exact ((mvPairIdeal n P) ^ i).mul_mem_left ⟨x, hx⟩ hy
  · exact MulMemClass.coe_mul ..

/-- The leftMul condition for a principal pair. Generalizes
`TateAlgebra.tateAlgNhd_leftMul_of_principal` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTateAlgNhd_leftMul_of_principal [IsTateRing A] (n : ℕ) (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(restrictedMvPowerSeriesSubring n A)) (i : ℕ) :
    ∃ j, (mvTateAlgNhd n P j : Set ↥(restrictedMvPowerSeriesSubring n A)) ⊆
      (x * ·) ⁻¹' (mvTateAlgNhd n P i : Set ↥(restrictedMvPowerSeriesSubring n A)) := by
  classical
  have hS : ∀ᶠ (l : Fin n →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A) :=
    mvTateAlgebra_coeff_eventually_in_pow n P x i
  set S : Set (Fin n →₀ ℕ) := {l |
    MvPowerSeries.coeff l x.val ∉
      (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A)} with hS_def
  have hS_finite : S.Finite := hS
  let m_fn : (Fin n →₀ ℕ) → ℕ := fun (l : Fin n →₀ ℕ) =>
    (mvExists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose
  have hm_spec : ∀ (l : Fin n →₀ ℕ), ∀ b : P.A₀, b ∈ P.I ^ (m_fn l) →
      ∃ c : P.A₀, c ∈ P.I ^ i ∧ (c : A) = MvPowerSeries.coeff l x.val * (b : A) :=
    fun l => (mvExists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose_spec
  let j : ℕ := max i (hS_finite.toFinset.sup m_fn)
  have hj_ge_i : i ≤ j := le_max_left _ _
  have hj_ge_m : ∀ l ∈ hS_finite.toFinset, m_fn l ≤ j := fun l hl =>
    le_max_of_le_right (Finset.le_sup hl)
  refine ⟨j, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  change (x * (mvPairSubring n P).subtype y) ∈ mvTateAlgNhd n P i
  have hy_coeff : ∀ l, ∃ b : P.A₀, b ∈ P.I ^ j ∧
      (b : A) = MvPowerSeries.coeff l ((mvPairSubring n P).subtype y).val :=
    mvPairIdeal_pow_le_coeffInIdeal n P j hy
  set xy : ↥(restrictedMvPowerSeriesSubring n A) :=
    x * (mvPairSubring n P).subtype y with hxy_def
  have hterm : ∀ p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ),
      ∃ c : P.A₀, c ∈ P.I ^ i ∧
        (c : A) = MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
    intro p
    obtain ⟨b_p, hb_p_mem, hb_p_eq⟩ := hy_coeff p.2
    by_cases hp : p.1 ∈ S
    · have hb_lower : b_p ∈ P.I ^ (m_fn p.1) := by
        have hle : m_fn p.1 ≤ j := hj_ge_m p.1 (hS_finite.mem_toFinset.mpr hp)
        exact Ideal.pow_le_pow_right hle hb_p_mem
      obtain ⟨c, hc_mem, hc_eq⟩ := hm_spec p.1 b_p hb_lower
      refine ⟨c, hc_mem, ?_⟩
      rw [hc_eq, hb_p_eq]
      rfl
    · rw [hS_def] at hp
      simp only [Set.mem_setOf_eq, not_not] at hp
      obtain ⟨a, ha_mem, ha_eq⟩ := hp
      refine ⟨a * b_p, Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hj_ge_i hb_p_mem), ?_⟩
      push_cast
      rw [ha_eq, hb_p_eq]
      rfl
  have hxy_coeff : ∀ l, ∃ c : P.A₀, c ∈ P.I ^ i ∧
      (c : A) = MvPowerSeries.coeff l xy.val := by
    intro l
    have hcoeff : MvPowerSeries.coeff l xy.val =
        ∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
      change MvPowerSeries.coeff l (x.val * y.val.val) = _
      rw [MvPowerSeries.coeff_mul]
    refine ⟨∑ p ∈ Finset.antidiagonal l, (hterm p).choose, ?_, ?_⟩
    · exact (P.I ^ i).sum_mem fun p _ => (hterm p).choose_spec.1
    · rw [hcoeff]
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      exact (hterm p).choose_spec.2
  have hxy_pair : xy ∈ mvPairSubring n P := by
    intro l
    obtain ⟨c, _, hc_eq⟩ := hxy_coeff l
    rw [← hc_eq]
    exact c.property
  exact mvTateAlgNhd_of_coeff_mem_principal n P i π hπ_gen hπ_unit hxy_pair hxy_coeff

omit [IsTopologicalRing A] in
/-- The leftMul condition. Generalizes `TateAlgebra.tateAlgNhd_leftMul` from `Fin 1` to
`Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTateAlgNhd_leftMul [IsTateRing A] (n : ℕ) (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(restrictedMvPowerSeriesSubring n A)) (i : ℕ) :
    ∃ j, (mvTateAlgNhd n P j : Set ↥(restrictedMvPowerSeriesSubring n A)) ⊆
      (x * ·) ⁻¹' (mvTateAlgNhd n P i : Set ↥(restrictedMvPowerSeriesSubring n A)) :=
  mvTateAlgNhd_leftMul_of_principal n P π hπ_gen hπ_unit x i

/-- The `RingSubgroupsBasis` for the natural Tate topology on `A⟨X₁,…,Xₙ⟩`. Requires a
principal pair of definition. Generalizes `TateAlgebra.tateAlgBasis` from `Fin 1` to
`Fin n`; Wedhorn Prop 6.21(2). -/
noncomputable def mvTateAlgBasis [IsTateRing A] (n : ℕ) (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    RingSubgroupsBasis (mvTateAlgNhd n P) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (mvTateAlgNhd_antitone n P (le_max_left i j))
        (mvTateAlgNhd_antitone n P (le_max_right i j))⟩)
    (mvTateAlgNhd_mul n P)
    (mvTateAlgNhd_leftMul n P π hπ_gen hπ_unit)

/-- The natural Tate topology on `A⟨X₁,…,Xₙ⟩`, with `0`-neighborhoods `{set-image of
`(mvPairIdeal n P)^k}`. Requires a principal pair of definition. Generalizes
`TateAlgebra.tateAlgebraTopology` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
@[reducible] noncomputable def mvTateAlgebraTopology [IsTateRing A] (n : ℕ)
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
  (mvTateAlgBasis n P π hπ_gen hπ_unit).topology

omit [IsTopologicalRing A] in
/-- The natural Tate topology is a ring topology. Generalizes
`TateAlgebra.tateAlgebraTopology_isTopologicalRing` from `Fin 1` to `Fin n`;
Wedhorn Prop 6.21(2). -/
theorem mvTateAlgebraTopology_isTopologicalRing [IsTateRing A] (n : ℕ)
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    @IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A)
      (mvTateAlgebraTopology n P π hπ_gen hπ_unit) _ :=
  (mvTateAlgBasis n P π hπ_gen hπ_unit).toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `mvTateAlgNhd n P k` (as a set) is contained in `mvPairSubring n P`. Generalizes
`TateAlgebra.tateAlgNhd_le_pairSubring` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTateAlgNhd_le_pairSubring (n : ℕ) (P : PairOfDefinition A) (k : ℕ) :
    (mvTateAlgNhd n P k : Set ↥(restrictedMvPowerSeriesSubring n A)) ⊆
      (mvPairSubring n P : Set ↥(restrictedMvPowerSeriesSubring n A)) := by
  rintro _ ⟨y, _, rfl⟩
  exact y.property

omit [IsTopologicalRing A] in
/-- `mvPairSubring n P` is open in `A⟨X⟩` with the natural Tate topology. Generalizes
`TateAlgebra.pairSubring_isOpen` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvPairSubring_isOpen [IsTateRing A] (n : ℕ) (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π}) (hπ_unit : IsUnit ((π : A))) :
    @IsOpen ↥(restrictedMvPowerSeriesSubring n A) (mvTateAlgebraTopology n P π hπ_gen hπ_unit)
      ((mvPairSubring n P : Subring ↥(restrictedMvPowerSeriesSubring n A)) :
        Set ↥(restrictedMvPowerSeriesSubring n A)) := by
  letI : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology n P π hπ_gen hπ_unit
  haveI := mvTateAlgebraTopology_isTopologicalRing n P π hπ_gen hπ_unit
  refine (mvPairSubring n P).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
  refine Filter.mem_of_superset
    ((mvTateAlgBasis n P π hπ_gen hπ_unit).hasBasis_nhds_zero.mem_of_mem (i := 1) trivial) ?_
  exact mvTateAlgNhd_le_pairSubring n P 1

/-- The canonical `RingSubgroupsBasis` for the natural Tate topology on `A⟨X₁,…,Xₙ⟩`, using
`IsTateRing.principalPair` via Wedhorn 6.14. Generalizes `TateAlgebra.tateAlgBasis'` from
`Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
noncomputable def mvTateAlgBasis' [IsTateRing A] (n : ℕ) :
    RingSubgroupsBasis (mvTateAlgNhd n (IsTateRing.principalPair A).toPairOfDefinition) :=
  let P := IsTateRing.principalPair A
  mvTateAlgBasis n P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

/-- The canonical natural Tate topology on `A⟨X₁,…,Xₙ⟩` for any Tate ring `A`. Uses the
canonical principal pair of definition `IsTateRing.principalPair A` (Wedhorn 6.14).
Generalizes `TateAlgebra.tateAlgebraTopology'` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2).

This is a plain `def` (not a global `instance`): installing a global topology on
`restrictedMvPowerSeriesSubring n A` would clash at `n = 1` with the canonical Tate topology
on `TateAlgebra A` (an `abbrev` for `restrictedMvPowerSeriesSubring 1 A`). -/
@[reducible] noncomputable def mvTateAlgebraTopology' [IsTateRing A] (n : ℕ) :
    TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) :=
  (mvTateAlgBasis' n).topology

omit [IsTopologicalRing A] in
/-- The canonical natural Tate topology is a ring topology. Generalizes
`TateAlgebra.tateAlgebraTopology'_isTopologicalRing` from `Fin 1` to `Fin n`;
Wedhorn Prop 6.21(2). -/
theorem mvTateAlgebraTopology'_isTopologicalRing [IsTateRing A] (n : ℕ) :
    @IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) (mvTateAlgebraTopology' n) _ :=
  (mvTateAlgBasis' n).toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `mvPairSubring n (IsTateRing.principalPair A).toPairOfDefinition` is open in the canonical
natural Tate topology. Generalizes `TateAlgebra.pairSubring_principalPair_isOpen'` from
`Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvPairSubring_principalPair_isOpen' [IsTateRing A] (n : ℕ) :
    @IsOpen ↥(restrictedMvPowerSeriesSubring n A) (mvTateAlgebraTopology' n)
      ((mvPairSubring n (IsTateRing.principalPair A).toPairOfDefinition :
        Subring ↥(restrictedMvPowerSeriesSubring n A)) :
        Set ↥(restrictedMvPowerSeriesSubring n A)) :=
  let P := IsTateRing.principalPair A
  mvPairSubring_isOpen n P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

/-! ### T2, uniform space, completeness on `A⟨X₁,…,Xₙ⟩` (def/theorem forms) -/

/-- The canonical uniform space on `A⟨X₁,…,Xₙ⟩` for a Tate ring, induced by the canonical
natural Tate topology via the right uniformity of the additive group. Generalizes
`TateAlgebra.instUniformSpaceTateAlgebra` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2).
Exposed as a `def` (not a global `instance`) to avoid a uniform-space diamond at `n = 1`. -/
@[reducible] noncomputable def mvTateUniformSpace [IsTateRing A] (n : ℕ) :
    UniformSpace ↥(restrictedMvPowerSeriesSubring n A) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (mvTateAlgebraTopology' n)
    (@IsTopologicalRing.to_topologicalAddGroup _ _
      (mvTateAlgebraTopology' n) (mvTateAlgebraTopology'_isTopologicalRing n))

omit [IsTopologicalRing A] in
/-- The canonical uniform space is a uniform additive group. Generalizes
`TateAlgebra.instIsUniformAddGroupTateAlgebra` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTate_isUniformAddGroup [IsTateRing A] (n : ℕ) :
    @IsUniformAddGroup ↥(restrictedMvPowerSeriesSubring n A) (mvTateUniformSpace n) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (mvTateAlgebraTopology' n)
    (@IsTopologicalRing.to_topologicalAddGroup _ _
      (mvTateAlgebraTopology' n) (mvTateAlgebraTopology'_isTopologicalRing n))

omit [IsTopologicalRing A] [NonarchimedeanRing A] in
/-- In a Hausdorff adic ring, the intersection of all powers of the ideal is zero.
Generalizes `TateAlgebra.pairIdeal_iInter_eq_zero` (no index dependence); Wedhorn Prop 6.21(2). -/
private theorem mvPairIdeal_iInter_eq_zero [T2Space A] (P : PairOfDefinition A) :
    ∀ b : ↥P.A₀, (∀ k : ℕ, b ∈ P.I ^ k) → b = 0 := by
  have hHausdorff : IsHausdorff P.I ↥P.A₀ :=
    (IsAdic.isHausdorff_iff P.isAdic).mpr inferInstance
  intro b hb_all
  apply hHausdorff.haus'
  intro k
  rw [SModEq.zero]
  change b ∈ P.I ^ k • (⊤ : Submodule ↥P.A₀ ↥P.A₀)
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact hb_all k

omit [IsTopologicalRing A] in
/-- `A⟨X₁,…,Xₙ⟩` is T2 (Hausdorff) whenever `A` is T2, with the canonical Tate topology.
Generalizes `TateAlgebra.instT2SpaceTateAlgebra` from `Fin 1` to `Fin n`; Wedhorn Prop
6.21(2). Exposed as a `theorem` against `mvTateAlgebraTopology' n` (not a global instance). -/
theorem mvTate_t2Space [IsTateRing A] [T2Space A] (n : ℕ) :
    @T2Space ↥(restrictedMvPowerSeriesSubring n A) (mvTateAlgebraTopology' n) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  haveI : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology'_isTopologicalRing n
  haveI : IsTopologicalAddGroup ↥(restrictedMvPowerSeriesSubring n A) :=
    IsTopologicalRing.to_topologicalAddGroup
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro y hy_ne
  obtain ⟨l, hl⟩ : ∃ l, MvPowerSeries.coeff l y.val ≠ 0 := by
    contrapose! hy_ne
    refine Subtype.ext (MvPowerSeries.ext fun l => ?_)
    simpa using hy_ne l
  suffices h : ∃ k, MvPowerSeries.coeff l y.val ∉
      (Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) by
    obtain ⟨k, hk⟩ := h
    refine ⟨(mvTateAlgNhd n P k : Set _),
      (mvTateAlgBasis' n).hasBasis_nhds_zero.mem_of_mem (i := k) trivial, ?_⟩
    intro hy_mem
    obtain ⟨b, hb_mem, hb_eq⟩ := mvTateAlgNhd_coeff_mem n P k hy_mem l
    exact hk ⟨b, hb_mem, hb_eq⟩
  by_contra hall
  push Not at hall
  obtain ⟨b, _, hb_eq⟩ := hall 0
  have hb_all : ∀ k : ℕ, b ∈ P.I ^ k := by
    intro k
    obtain ⟨b_k, hb_k_mem, hb_k_eq⟩ := hall k
    have : b = b_k := Subtype.ext (hb_eq.trans hb_k_eq.symm)
    rw [this]; exact hb_k_mem
  have hb_zero : b = 0 := mvPairIdeal_iInter_eq_zero P b hb_all
  rw [hb_zero] at hb_eq
  simp at hb_eq
  exact hl hb_eq.symm

omit [IsTopologicalRing A] in
/-- The canonical natural Tate topology on `A⟨X₁,…,Xₙ⟩` is nonarchimedean: the
`RingSubgroupsBasis` (open additive subgroups `mvTateAlgNhd n P k`) provides a
nonarchimedean topology. Generalizes the `n = 1` use `tateAlgBasis'.nonarchimedean`
(TopologyComparison.lean) to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTate_nonarchimedean [IsTateRing A] (n : ℕ) :
    @NonarchimedeanRing ↥(restrictedMvPowerSeriesSubring n A) _ (mvTateAlgebraTopology' n) :=
  (mvTateAlgBasis' n).nonarchimedean

omit [IsTopologicalRing A] in
/-- The uniformity of `A⟨X₁,…,Xₙ⟩` (w.r.t. `mvTateUniformSpace n`) is countably generated:
the `0`-neighborhood basis `mvTateAlgNhd n P` is `ℕ`-indexed. Generalizes the `n = 1`
inline derivation in `tateAlgebraTopology'_completeSpace` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTate_uniformity_isCountablyGenerated [IsTateRing A] (n : ℕ) :
    @Filter.IsCountablyGenerated _
      (@uniformity ↥(restrictedMvPowerSeriesSubring n A) (mvTateUniformSpace n)) := by
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  haveI hring : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology'_isTopologicalRing n
  haveI haddgrp : IsTopologicalAddGroup ↥(restrictedMvPowerSeriesSubring n A) :=
    IsTopologicalRing.to_topologicalAddGroup
  letI uT : UniformSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateUniformSpace n
  haveI : @IsUniformAddGroup _ uT _ := mvTate_isUniformAddGroup n
  haveI : (@nhds _ τ (0 : ↥(restrictedMvPowerSeriesSubring n A))).IsCountablyGenerated :=
    (mvTateAlgBasis' n).hasBasis_nhds_zero.isCountablyGenerated
  exact @IsUniformAddGroup.uniformity_countably_generated _ uT _ _ (by
    convert ‹(@nhds _ τ (0 : ↥(restrictedMvPowerSeriesSubring n A))).IsCountablyGenerated›)

omit [NonarchimedeanRing A] in
/-- The image of `P.I^k` under `Subtype.val : P.A₀ → A` is a closed additive subgroup.
Generalizes `TateAlgebra.pow_image_isClosed` (no index dependence); Wedhorn Prop 6.21(2). -/
private theorem mvPow_image_isClosed (P : PairOfDefinition A) (k : ℕ) :
    IsClosed (Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) := by
  rw [show Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) =
    (AddSubgroup.map P.A₀.subtype.toAddMonoidHom (P.I ^ k).toAddSubgroup : Set A) from rfl]
  exact AddSubgroup.isClosed_of_isOpen _ (P.pow_image_isOpen k)

/-- **T-MVT-3:** `A⟨X₁,…,Xₙ⟩` is complete with the canonical natural Tate topology, provided
the ground ring `A` is complete and Hausdorff. Generalizes
`TateAlgebra.tateAlgebraTopology'_completeSpace` from `Fin 1` to `Fin n`; Wedhorn Prop 6.21(2).

The proof uses `UniformSpace.complete_of_cauchySeq_tendsto`: the uniformity is countably
generated (basis `mvTateAlgNhd n P k` is `ℕ`-indexed), so it suffices to show every Cauchy
sequence converges; each coefficient sequence is Cauchy in `A`, converges by completeness of
`A`, the limit function is restricted, and the sequence converges coefficient-wise. -/
theorem mvTate_completeSpace [IsTateRing A] [T2Space A] (n : ℕ)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    @CompleteSpace ↥(restrictedMvPowerSeriesSubring n A) (mvTateUniformSpace n) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  haveI hring : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology'_isTopologicalRing n
  haveI haddgrp : IsTopologicalAddGroup ↥(restrictedMvPowerSeriesSubring n A) :=
    IsTopologicalRing.to_topologicalAddGroup
  letI uT : UniformSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateUniformSpace n
  haveI : @IsUniformAddGroup _ uT _ := mvTate_isUniformAddGroup n
  -- Step 1: The uniformity is countably generated (basis indexed by ℕ).
  haveI hcg : (@uniformity _ uT).IsCountablyGenerated :=
    mvTate_uniformity_isCountablyGenerated n
  -- Step 2: Use the sequential completeness criterion.
  apply @UniformSpace.complete_of_cauchySeq_tendsto _ uT hcg
  intro u hu
  letI uA : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : @IsUniformAddGroup A uA _ := isUniformAddGroup_of_addCommGroup
  -- hu_basis: the Cauchy condition in terms of mvTateAlgNhd.
  have hu_basis : ∀ k : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ i ≥ N,
      u m - u i ∈ mvTateAlgNhd n P k := by
    intro k
    have hmem : (fun p : ↥(restrictedMvPowerSeriesSubring n A) ×
          ↥(restrictedMvPowerSeriesSubring n A) => p.2 - p.1) ⁻¹'
        (mvTateAlgNhd n P k : Set _) ∈ @uniformity _ uT := by
      rw [@uniformity_eq_comap_nhds_zero' _ _ _ haddgrp]
      exact Filter.mem_comap.mpr ⟨(mvTateAlgNhd n P k : Set _),
        (mvTateAlgBasis' n).hasBasis_nhds_zero.mem_of_mem (i := k) trivial,
        fun p hp => by simp only [Set.mem_preimage, sub_eq_add_neg] at hp ⊢; exact hp⟩
    obtain ⟨N, hN⟩ := cauchySeq_iff.mp hu _ hmem
    exact ⟨N, fun m hm i hi => by
      have h1 := hN m hm i hi
      simp only [Set.mem_preimage] at h1
      rw [show u m - u i = -(u i - u m) from by ring]
      exact neg_mem h1⟩
  -- Step 3: For each l, the coefficient sequence is Cauchy in (A, uA).
  have hcoeff_cauchy : ∀ l : Fin n →₀ ℕ,
      CauchySeq (fun m => MvPowerSeries.coeff l (u m).val) := by
    intro l
    rw [cauchySeq_iff]
    intro V hV
    rw [uniformity_eq_comap_nhds_zero'] at hV
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
    obtain ⟨k, _, hk⟩ := P.hasBasis_nhds_zero.mem_iff.mp hW
    obtain ⟨N, hN⟩ := hu_basis k
    refine ⟨N, fun m hm i hi => ?_⟩
    have hdiff := hN m hm i hi
    obtain ⟨b, hb_mem, hb_eq⟩ := mvTateAlgNhd_coeff_mem n P k hdiff l
    apply hWV
    simp only [Set.mem_preimage]
    apply hk
    refine ⟨-b, (P.I ^ k).neg_mem hb_mem, ?_⟩
    simp only [Subring.coe_neg, hb_eq]
    change -MvPowerSeries.coeff l (u m - u i).val =
      MvPowerSeries.coeff l (u i).val + -MvPowerSeries.coeff l (u m).val
    rw [show (u m - u i).val = (u m).val - (u i).val from rfl, map_sub, neg_sub,
      sub_eq_add_neg]
  -- Extract coefficient-wise limits using completeness of A.
  have hcoeff_conv : ∀ l : Fin n →₀ ℕ, ∃ a : A,
      Tendsto (fun m => MvPowerSeries.coeff l (u m).val) atTop (nhds a) :=
    fun l => cauchySeq_tendsto_of_complete (hcoeff_cauchy l)
  choose c hc using hcoeff_conv
  -- Step 4: The limit function c is restricted.
  have hc_restricted : MvPowerSeries.IsRestricted (fun l => c l : MvPowerSeries (Fin n) A) := by
    change Tendsto c cofinite (nhds 0)
    rw [tendsto_nhds]
    intro U hU h0U
    rw [Filter.mem_cofinite]
    obtain ⟨k, _, hk⟩ := P.hasBasis_nhds_zero.mem_iff.mp (hU.mem_nhds h0U)
    obtain ⟨N, hN⟩ := hu_basis k
    have hfin : ∀ᶠ l in cofinite,
        MvPowerSeries.coeff l (u N).val ∈
          (Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) :=
      mvTateAlgebra_coeff_eventually_in_pow n P (u N) k
    set S : Set (Fin n →₀ ℕ) := {l |
      MvPowerSeries.coeff l (u N).val ∉
        (Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A)}
    have hS_fin : S.Finite := hfin
    suffices hsub : {l | c l ∉ U} ⊆ S from hS_fin.subset hsub
    intro l hl
    simp only [Set.mem_setOf_eq] at hl ⊢
    intro h_in
    apply hl; apply hk
    apply (mvPow_image_isClosed P k).mem_of_tendsto (hc l)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨b_diff, hb_diff_mem, hb_diff_eq⟩ := mvTateAlgNhd_coeff_mem n P k (hN m hm N le_rfl) l
    obtain ⟨b_N, hb_N_mem, hb_N_eq⟩ := h_in
    refine ⟨b_N + b_diff, (P.I ^ k).add_mem hb_N_mem hb_diff_mem, ?_⟩
    push_cast
    rw [hb_N_eq, hb_diff_eq]
    simp [map_sub]
  -- Step 5: Construct the limit element.
  let f : ↥(restrictedMvPowerSeriesSubring n A) := ⟨fun l => c l, hc_restricted⟩
  refine ⟨f, ?_⟩
  -- Step 6: Show u m → f in mvTateAlgebraTopology'.
  rw [((mvTateAlgBasis' n).hasBasis_nhds f).tendsto_right_iff]
  intro k _
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := hu_basis k
  refine ⟨N, fun m hm => ?_⟩
  change u m - f ∈ mvTateAlgNhd n P k
  have hcoeff_diff : ∀ l : Fin n →₀ ℕ,
      ∃ b : ↥P.A₀, b ∈ P.I ^ k ∧ (b : A) = MvPowerSeries.coeff l (u m - f).val := by
    intro l
    have hcoeff_val : MvPowerSeries.coeff l (u m - f).val =
        MvPowerSeries.coeff l (u m).val - c l := by
      change MvPowerSeries.coeff l ((u m).val - f.val) =
        MvPowerSeries.coeff l (u m).val - c l
      rw [map_sub]
      simp only [MvPowerSeries.coeff_apply, f]
    have htend : Tendsto (fun i => MvPowerSeries.coeff l (u m).val -
        MvPowerSeries.coeff l (u i).val)
        atTop (nhds (MvPowerSeries.coeff l (u m).val - c l)) :=
      tendsto_const_nhds.sub (hc l)
    have hev : ∀ᶠ i in atTop,
        MvPowerSeries.coeff l (u m).val - MvPowerSeries.coeff l (u i).val ∈
          (Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) := by
      rw [Filter.eventually_atTop]
      refine ⟨N, fun i hi => ?_⟩
      obtain ⟨b, hb_mem, hb_eq⟩ := mvTateAlgNhd_coeff_mem n P k (hN m hm i hi) l
      exact ⟨b, hb_mem, by rw [hb_eq]; simp [map_sub]⟩
    have hlim_mem := (mvPow_image_isClosed P k).mem_of_tendsto htend hev
    rw [← hcoeff_val] at hlim_mem
    exact hlim_mem
  have hpair : (u m - f) ∈ mvPairSubring n P := by
    intro s
    obtain ⟨b, _, hb_eq⟩ := hcoeff_diff s
    rw [← hb_eq]; exact b.property
  let PP := IsTateRing.principalPair A
  exact mvTateAlgNhd_of_coeff_mem_principal n PP.toPairOfDefinition k PP.π PP.I_eq_span
    PP.π_isUnit hpair hcoeff_diff

/-! ### `A⟨X₁,…,Xₙ⟩` is a Tate ring (Wedhorn Prop 6.21(2), headline) -/

omit [IsTopologicalRing A] in
/-- The preimage of `mvTateAlgNhd n P k` under the inclusion `mvPairSubring n P ↪ A⟨X⟩` equals
`(mvPairIdeal n P)^k`. Generalizes `TateAlgebra.tateAlgNhd_preimage_eq` from `Fin 1` to
`Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvTateAlgNhd_preimage_eq (n : ℕ) (P : PairOfDefinition A) (k : ℕ) :
    (mvPairSubring n P).subtype ⁻¹'
        (mvTateAlgNhd n P k : Set ↥(restrictedMvPowerSeriesSubring n A)) =
      ((mvPairIdeal n P) ^ k : Ideal ↥(mvPairSubring n P)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, heq⟩
    obtain rfl : x = y := Subtype.val_injective heq.symm
    exact hy
  · exact fun hx => ⟨x, hx, rfl⟩

omit [IsTopologicalRing A] in
/-- The subspace topology on `mvPairSubring n P` from `mvTateAlgebraTopology' n` equals the
`mvPairIdeal n P`-adic topology. Generalizes `TateAlgebra.pairIdeal_isAdic_subspace` from
`Fin 1` to `Fin n`; Wedhorn Prop 6.21(2). -/
theorem mvPairIdeal_isAdic_subspace [IsTateRing A] (n : ℕ) :
    @IsAdic ↥(mvPairSubring n (IsTateRing.principalPair A).toPairOfDefinition) _
      (@instTopologicalSpaceSubtype ↥(restrictedMvPowerSeriesSubring n A)
        (· ∈ (mvPairSubring n (IsTateRing.principalPair A).toPairOfDefinition :
          Subring ↥(restrictedMvPowerSeriesSubring n A)))
        (mvTateAlgebraTopology' n))
      (mvPairIdeal n (IsTateRing.principalPair A).toPairOfDefinition) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  haveI hring : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology'_isTopologicalRing n
  letI τ_sub : TopologicalSpace ↥(mvPairSubring n P) :=
    instTopologicalSpaceSubtype
  haveI hring_sub : @IsTopologicalRing ↥(mvPairSubring n P) τ_sub _ :=
    Subring.instIsTopologicalRing (mvPairSubring n P)
  rw [@isAdic_iff _ _ _ hring_sub]
  refine ⟨fun k => ?_, fun s hs => ?_⟩
  · rw [show ((mvPairIdeal n P ^ k : Ideal ↥(mvPairSubring n P)) :
        Set ↥(mvPairSubring n P)) =
      (mvPairSubring n P).subtype ⁻¹'
        (mvTateAlgNhd n P k : Set ↥(restrictedMvPowerSeriesSubring n A)) from
      (mvTateAlgNhd_preimage_eq n P k).symm]
    exact isOpen_induced ((mvTateAlgBasis' n).openAddSubgroup k).isOpen'
  · rw [nhds_subtype_eq_comap] at hs
    obtain ⟨U, hU, hsU⟩ := Filter.mem_comap.mp hs
    rw [show (0 : ↥(mvPairSubring n P)).val = (0 : ↥(restrictedMvPowerSeriesSubring n A))
      from rfl] at hU
    obtain ⟨k, -, hk⟩ := (mvTateAlgBasis' n).hasBasis_nhds_zero.mem_iff.mp hU
    exact ⟨k, (mvTateAlgNhd_preimage_eq n P k ▸ Set.preimage_mono hk).trans hsU⟩

/-- A `PairOfDefinition` for `A⟨X₁,…,Xₙ⟩` equipped with `mvTateAlgebraTopology' n`. Ring of
definition `mvPairSubring n P = A₀⟨X⟩`, ideal of definition `mvPairIdeal n P = I · A₀⟨X⟩`.
Generalizes `TateAlgebra.tateAlgebra_pairOfDefinition` from `Fin 1` to `Fin n`; Wedhorn
Prop 6.21(2). -/
noncomputable def mvTateAlgebra_pairOfDefinition [IsTateRing A] (n : ℕ) :
    @PairOfDefinition ↥(restrictedMvPowerSeriesSubring n A) _
      (mvTateAlgebraTopology' n) := by
  letI : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  exact {
    A₀ := mvPairSubring n (IsTateRing.principalPair A).toPairOfDefinition
    I := mvPairIdeal n (IsTateRing.principalPair A).toPairOfDefinition
    isOpen := mvPairSubring_principalPair_isOpen' n
    fg := mvPairIdeal_fg n (IsTateRing.principalPair A).toPairOfDefinition
    isAdic := mvPairIdeal_isAdic_subspace n
  }

/-- `algebraMap A (A⟨X₁,…,Xₙ⟩)` is continuous from `A`'s topology to `mvTateAlgebraTopology' n`.
Generalizes `TateAlgebra.tateAlgebra_algebraMap_continuous` from `Fin 1` to `Fin n`; Wedhorn
Prop 6.21(2). -/
theorem mvTateAlgebra_algebraMap_continuous [IsTateRing A] (n : ℕ) :
    @Continuous _ _ _ (mvTateAlgebraTopology' n)
      (algebraMap A ↥(restrictedMvPowerSeriesSubring n A)) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  haveI hring : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology'_isTopologicalRing n
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have hU_nhds : U ∈ @nhds _ τ (algebraMap A _ a) := hU.mem_nhds ha
  obtain ⟨k, -, hk⟩ := ((mvTateAlgBasis' n).hasBasis_nhds (algebraMap A _ a)).mem_iff.mp hU_nhds
  apply mem_nhds_iff.mpr
  refine ⟨(fun x => x + a) '' (Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀)), ?_, ?_, ?_⟩
  · rintro x ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    rw [Set.mem_preimage]
    apply hk
    change algebraMap A ↥(restrictedMvPowerSeriesSubring n A) ((b : A) + a) -
      algebraMap A ↥(restrictedMvPowerSeriesSubring n A) a ∈ mvTateAlgNhd n P k
    rw [map_add, add_sub_cancel_right]
    refine ⟨mvPairConstantHom n P b, ?_, ?_⟩
    · rw [show (mvPairIdeal n P) ^ k = Ideal.map (mvPairConstantHom n P) (P.I ^ k) from by
        simp only [mvPairIdeal, ← Ideal.map_pow]]
      exact Ideal.mem_map_of_mem _ hb
    · apply Subtype.ext; rfl
  · have hopen : IsOpen (Subtype.val '' ((P.I ^ k : Ideal P.A₀) : Set P.A₀) : Set A) :=
      P.pow_image_isOpen k
    exact (Homeomorph.addRight a).isOpenMap _ hopen
  · exact ⟨0, ⟨0, (P.I ^ k).zero_mem, rfl⟩, by simp⟩

/-- `A⟨X₁,…,Xₙ⟩` with `mvTateAlgebraTopology' n` is a Tate ring (the headline of Wedhorn
Prop 6.21(2)). Generalizes `TateAlgebra.tateAlgebra_isTateRing` from `Fin 1` to `Fin n`. The
topologically nilpotent unit is `algebraMap π`, the image of the generator `π` of the
principal pair of `A`. -/
theorem mvTate_isTateRing [IsTateRing A] (n : ℕ) :
    @IsTateRing ↥(restrictedMvPowerSeriesSubring n A) _ (mvTateAlgebraTopology' n) := by
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  haveI hring : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology'_isTopologicalRing n
  exact @IsTateRing.mk _ _ τ
    ⟨⟨mvTateAlgebra_pairOfDefinition n⟩⟩
    (by
      obtain ⟨u, hu_nilp⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
      refine ⟨Units.map
        (algebraMap A ↥(restrictedMvPowerSeriesSubring n A) :
          A →* ↥(restrictedMvPowerSeriesSubring n A)) u, ?_⟩
      change Tendsto (fun m => ((Units.map
        (algebraMap A ↥(restrictedMvPowerSeriesSubring n A) :
          A →* ↥(restrictedMvPowerSeriesSubring n A)) u :
            ↥(restrictedMvPowerSeriesSubring n A)) ^ m)) atTop (@nhds _ τ 0)
      have hval : ∀ m : ℕ, (Units.map
          (algebraMap A ↥(restrictedMvPowerSeriesSubring n A) :
            A →* ↥(restrictedMvPowerSeriesSubring n A)) u :
              ↥(restrictedMvPowerSeriesSubring n A)) ^ m =
          algebraMap A ↥(restrictedMvPowerSeriesSubring n A) ((u : A) ^ m) := by
        intro m
        rw [show (Units.map (algebraMap A ↥(restrictedMvPowerSeriesSubring n A) :
          A →* ↥(restrictedMvPowerSeriesSubring n A)) u :
            ↥(restrictedMvPowerSeriesSubring n A)) =
          algebraMap A ↥(restrictedMvPowerSeriesSubring n A) (u : A) from rfl, map_pow]
      simp_rw [hval]
      rw [show (0 : ↥(restrictedMvPowerSeriesSubring n A)) =
        algebraMap A ↥(restrictedMvPowerSeriesSubring n A) 0 from (map_zero _).symm]
      exact (mvTateAlgebra_algebraMap_continuous n).continuousAt.tendsto.comp hu_nilp)

omit [IsTopologicalRing A] in
/-- **Proposition 6.17 for the multivariate Tate algebra** (faithful, noetherian-WHOLE-ring).
Every ideal of `A⟨X₁,…,Xₙ⟩` is closed in the canonical Tate topology, when `A` is a complete,
Hausdorff, strongly noetherian Tate ring.

Source: Wedhorn Prop 6.17, p. 51 (wedhorn.txt:2449: "A complete Tate ring is noetherian iff every
ideal is closed"). Discharged via the faithful engine `fg_topologicalClosure_isClosed`
(WedhornBanachTheorem.lean, §3.7.2/1) applied to `C := A⟨X⟩` as a module over itself: `C` is
noetherian by `IsStronglyNoetherian.isNoetherianRing_restricted n` (the WHOLE ring `C`, NOT a
noetherian ring of definition — so this holds for ℂ_p-type rings without a noetherian `A₀`), hence
`J.topologicalClosure` is finitely generated, and the engine returns closedness of `J`. -/
theorem mvTate_isClosed_ideal [IsTateRing A] [T2Space A] [IsStronglyNoetherian A] (n : ℕ)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (J : Ideal ↥(restrictedMvPowerSeriesSubring n A)) :
    @IsClosed ↥(restrictedMvPowerSeriesSubring n A) (mvTateAlgebraTopology' n)
      (J : Set ↥(restrictedMvPowerSeriesSubring n A)) := by
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateAlgebraTopology' n
  haveI hring : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring n A) :=
    mvTateAlgebraTopology'_isTopologicalRing n
  letI uC : UniformSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTateUniformSpace n
  haveI : IsUniformAddGroup ↥(restrictedMvPowerSeriesSubring n A) := mvTate_isUniformAddGroup n
  haveI : CompleteSpace ↥(restrictedMvPowerSeriesSubring n A) := mvTate_completeSpace n hA_complete
  haveI : (@uniformity ↥(restrictedMvPowerSeriesSubring n A) uC).IsCountablyGenerated :=
    mvTate_uniformity_isCountablyGenerated n
  haveI : T2Space ↥(restrictedMvPowerSeriesSubring n A) := mvTate_t2Space n
  haveI : IsTateRing ↥(restrictedMvPowerSeriesSubring n A) := mvTate_isTateRing n
  haveI : ContinuousSMul ↥(restrictedMvPowerSeriesSubring n A)
      ↥(restrictedMvPowerSeriesSubring n A) := ⟨continuous_mul⟩
  haveI hnoeth : IsNoetherianRing ↥(restrictedMvPowerSeriesSubring n A) :=
    IsStronglyNoetherian.isNoetherianRing_restricted n
  exact ValuationSpectrum.fg_topologicalClosure_isClosed J
    (Module.Finite.iff_fg.mpr (isNoetherian_def.mp hnoeth _))

omit [IsTopologicalRing A] in
/-- A multivariate power series whose support is contained in the box `[0, N)^m` (all coefficients
at multi-indices with some component `≥ N` vanish) is restricted. Generalizes
`isRestricted₂_of_eventually_zero` from `Fin 2` to `Fin m`. -/
private theorem mvIsRestricted_of_eventually_zero (m : ℕ)
    (h : MvPowerSeries (Fin m) A) (N : ℕ)
    (hh : ∀ l : Fin m →₀ ℕ, (∃ i, N ≤ l i) → h l = 0) :
    MvPowerSeries.IsRestricted h := by
  classical
  change Filter.Tendsto (fun l => h l) Filter.cofinite (nhds 0)
  rw [tendsto_nhds]
  intro U hU h0U
  rw [Filter.mem_cofinite]
  apply Set.Finite.subset
    (Set.finite_range (fun f : Fin m → Fin N =>
      (Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ)) : Fin m →₀ ℕ)))
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  have hbox : ∀ i, s i < N := by
    intro i
    by_contra h_ge
    push Not at h_ge
    exact hs (by rw [hh s ⟨i, h_ge⟩]; exact h0U)
  refine ⟨fun i => ⟨s i, hbox i⟩, ?_⟩
  ext i
  simp [Finsupp.equivFunOnFinite]

/-- The box-truncation of `g ∈ A⟨X₁,…,Xₘ⟩` at size `N^m`: keep coefficients at multi-indices in
`[0, N)^m`, set the rest to zero. Generalizes `truncTateC₂` from `Fin 2` to `Fin m`. -/
private noncomputable def truncMv (m : ℕ) (g : ↥(restrictedMvPowerSeriesSubring m A)) (N : ℕ) :
    ↥(restrictedMvPowerSeriesSubring m A) :=
  ⟨fun l => if ∀ i, l i < N then g.val l else 0,
   mvIsRestricted_of_eventually_zero m _ N (fun l hl => by
     obtain ⟨i, hi⟩ := hl
     simp only [ite_eq_right_iff]
     intro hbox
     exact absurd (hbox i) (by omega))⟩

private theorem truncMv_val (m : ℕ) (g : ↥(restrictedMvPowerSeriesSubring m A)) (N : ℕ)
    (l : Fin m →₀ ℕ) :
    (truncMv m g N).val l = if ∀ i, l i < N then g.val l else 0 := rfl

private theorem truncMv_coeff_outside (m : ℕ) (g : ↥(restrictedMvPowerSeriesSubring m A)) (N : ℕ)
    (l : Fin m →₀ ℕ) (hl : ∃ i, N ≤ l i) :
    (truncMv m g N).val l = 0 := by
  obtain ⟨i, hi⟩ := hl
  simp only [truncMv_val, ite_eq_right_iff]
  intro hbox
  exact absurd (hbox i) (by omega)

/-- **Polynomials (box-finite-support elements) are dense in `A⟨X₁,…,Xₘ⟩`** for the canonical
multivariate Tate topology. Generalizes `tateAlgebra₂_polynomials_dense_canonical` from `Fin 2`
to `Fin m`; the density half of Wedhorn Example 6.38 ("`A[M]` is dense in `Â⟨T/s⟩`",
`wedhorn.txt:2696`). This is sub-leaf AG1a of the `presheafValue` strong-noetherian propagation. -/
theorem mvTateAlgebra_polynomials_dense [IsTateRing A] (m : ℕ) :
    @Dense ↥(restrictedMvPowerSeriesSubring m A) (mvTateAlgebraTopology' m)
      {g | ∃ N : ℕ, ∀ l : Fin m →₀ ℕ, (∃ i, N ≤ l i) → g.val l = 0} := by
  classical
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(restrictedMvPowerSeriesSubring m A) := mvTateAlgebraTopology' m
  intro g
  rw [mem_closure_iff]
  intro O hO hgO
  have hO_nhds : O ∈ nhds g := hO.mem_nhds hgO
  obtain ⟨n, -, hn⟩ := (mvTateAlgBasis' (A := A) m).hasBasis_nhds g |>.mem_iff.mp hO_nhds
  have hfin : ∀ᶠ (l : Fin m →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l g.val ∈
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) :=
    mvTateAlgebra_coeff_eventually_in_pow m P g n
  set S : Set (Fin m →₀ ℕ) := {l |
    MvPowerSeries.coeff l g.val ∉
      (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A)} with hS_def
  have hS_fin : S.Finite := hfin
  let N := (hS_fin.toFinset.sup (fun l => Finset.univ.sup (fun i => l i))) + 1
  have hbad_lt : ∀ l ∈ S, ∀ i, l i < N := by
    intro l hl i
    have h1 : l i ≤ Finset.univ.sup (fun j => l j) :=
      Finset.le_sup (f := fun j => l j) (Finset.mem_univ i)
    have h2 : Finset.univ.sup (fun j => l j) ≤
        hS_fin.toFinset.sup (fun l' => Finset.univ.sup (fun j => l' j)) :=
      Finset.le_sup (f := fun l' => Finset.univ.sup (fun j => l' j))
        (hS_fin.mem_toFinset.mpr hl)
    omega
  refine ⟨truncMv m g N, hn ?_, ⟨N, fun l hl => truncMv_coeff_outside m g N l hl⟩⟩
  have hdiff_pair : g - truncMv m g N ∈ mvPairSubring m P := by
    intro l
    change (g.val l - (truncMv m g N).val l) ∈ (P.A₀ : Set A)
    rw [truncMv_val]
    by_cases hlt : ∀ i, l i < N
    · rw [if_pos hlt, sub_self]; exact P.A₀.zero_mem
    · rw [if_neg hlt, sub_zero]
      have hl_not_bad : l ∉ S := fun hl => hlt (hbad_lt l hl)
      rw [hS_def, Set.mem_setOf_eq, not_not] at hl_not_bad
      obtain ⟨b, _, hb_eq⟩ := hl_not_bad
      rw [show g.val l = (b : A) from hb_eq.symm]; exact b.property
  have hdiff_coeff : ∀ l, ∃ b : P.A₀, b ∈ P.I ^ n ∧
      (b : A) = MvPowerSeries.coeff l (g - truncMv m g N).val := by
    intro l
    change ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = g.val l - (truncMv m g N).val l
    rw [truncMv_val]
    by_cases hlt : ∀ i, l i < N
    · rw [if_pos hlt, sub_self]
      exact ⟨0, (P.I ^ n).zero_mem, rfl⟩
    · rw [if_neg hlt, sub_zero]
      have hl_not_bad : l ∉ S := fun hl => hlt (hbad_lt l hl)
      rw [hS_def, Set.mem_setOf_eq, not_not] at hl_not_bad
      exact hl_not_bad
  have hg_diff_mem : g - truncMv m g N ∈ mvTateAlgNhd m P n :=
    mvTateAlgNhd_of_coeff_mem_principal m P n
      (IsTateRing.principalPair A).π
      (IsTateRing.principalPair A).I_eq_span
      (IsTateRing.principalPair A).π_isUnit
      hdiff_pair hdiff_coeff
  change truncMv m g N - g ∈ mvTateAlgNhd m P n
  rw [show truncMv m g N - g = -(g - truncMv m g N) from by ring]
  exact neg_mem hg_diff_mem

/-- **The variable `Xⱼ` is power-bounded in `A⟨X₁,…,Xₘ⟩`** (the canonical Tate topology).
`Xⱼ` lies in the ring of definition `mvPairSubring` (its coefficients are `0`/`1`, both in `A₀`),
all of whose elements are power-bounded (`PairOfDefinition.isBounded_A₀`). Needed for the relative
Example-6.38 evaluation tuple (sub-leaf AG2 of the strong-noetherian propagation). -/
theorem mvPowerSeries_X_isBounded [IsTateRing A] {m : ℕ} (j : Fin m) :
    @TopologicalRing.IsBounded _ _ (mvTateAlgebraTopology' m)
      (Set.range ((⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
        ↥(restrictedMvPowerSeriesSubring m A)) ^ · :
        ℕ → ↥(restrictedMvPowerSeriesSubring m A))) := by
  classical
  letI : TopologicalSpace ↥(restrictedMvPowerSeriesSubring m A) := mvTateAlgebraTopology' m
  haveI : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring m A) :=
    mvTateAlgebraTopology'_isTopologicalRing m
  set P := (IsTateRing.principalPair A).toPairOfDefinition with hP
  set Xj : ↥(restrictedMvPowerSeriesSubring m A) :=
    ⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ with hXj
  have hX_in : Xj ∈ mvPairSubring m P := by
    intro s
    change MvPowerSeries.coeff s (MvPowerSeries.X j) ∈ P.A₀
    rw [MvPowerSeries.coeff_X]
    split
    · exact P.A₀.one_mem
    · exact P.A₀.zero_mem
  have hpow : ∀ n, Xj ^ n ∈ mvPairSubring m P := fun n => (mvPairSubring m P).pow_mem hX_in n
  have hbd : TopologicalRing.IsBounded
      ((mvPairSubring m P : Subring ↥(restrictedMvPowerSeriesSubring m A)) :
        Set ↥(restrictedMvPowerSeriesSubring m A)) :=
    PairOfDefinition.isBounded_A₀ (mvTateAlgebra_pairOfDefinition m)
  exact hbd.subset (by rintro _ ⟨n, rfl⟩; exact hpow n)

/-- **`algebraMap` (the constant-series map) preserves boundedness** into `A⟨X₁,…,Xₘ⟩`: a bounded
set `S ⊆ A` has bounded image under `a ↦` (constant series `a`).
Since `coeffₗ(C(s)·v) = s·coeffₗ(v)`
and `S` is bounded, the small coefficients of `v` (in `Iᵏ`) are absorbed: `s·coeffₗ(v) ∈ S·Iᵏ ⊆ Iʲ`.
Needed for the relative Example-6.38 evaluation tuple (the `tᵢ/s` constant entries). -/
theorem mvTateAlgebra_algebraMap_isBounded [IsTateRing A] {m : ℕ} {S : Set A}
    (hS : TopologicalRing.IsBounded S) :
    @TopologicalRing.IsBounded _ _ (mvTateAlgebraTopology' m)
      ((algebraMap A ↥(restrictedMvPowerSeriesSubring m A)) '' S) := by
  classical
  letI : TopologicalSpace ↥(restrictedMvPowerSeriesSubring m A) := mvTateAlgebraTopology' m
  haveI : IsTopologicalRing ↥(restrictedMvPowerSeriesSubring m A) :=
    mvTateAlgebraTopology'_isTopologicalRing m
  set P := (IsTateRing.principalPair A).toPairOfDefinition with hP
  intro U hU
  obtain ⟨j, -, hjU⟩ := (mvTateAlgBasis' m).hasBasis_nhds_zero.mem_iff.mp hU
  have hIj_nhd : (Subtype.val '' ((P.I ^ j : Ideal P.A₀) : Set P.A₀) : Set A) ∈ 𝓝 (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem (i := j) trivial
  obtain ⟨VB, hVB, hSVB⟩ := hS _ hIj_nhd
  obtain ⟨k, -, hkV⟩ := P.hasBasis_nhds_zero.mem_iff.mp hVB
  refine ⟨mvTateAlgNhd m P k,
    (mvTateAlgBasis' m).hasBasis_nhds_zero.mem_of_mem (i := k) trivial, ?_⟩
  rintro _ ⟨_, ⟨s, hs, rfl⟩, v, hv, rfl⟩
  apply hjU
  -- `algebraMap s * v ∈ mvTateAlgNhd j`: all coefficients lie in `P.Iʲ`.
  have hcoeff : ∀ l : Fin m →₀ ℕ,
      MvPowerSeries.coeff l ((algebraMap A ↥(restrictedMvPowerSeriesSubring m A) s * v).val) =
        s * MvPowerSeries.coeff l v.val := by
    intro l
    change MvPowerSeries.coeff l
      ((MvPowerSeries.C s : MvPowerSeries (Fin m) A) * v.val) = _
    rw [MvPowerSeries.coeff_C_mul]
  have hmem : ∀ l : Fin m →₀ ℕ, ∃ b : P.A₀, b ∈ P.I ^ j ∧
      (b : A) = MvPowerSeries.coeff l
        ((algebraMap A ↥(restrictedMvPowerSeriesSubring m A) s * v).val) := by
    intro l
    -- `coeffₗ v ∈ image(Iᵏ) ⊆ VB`, so `s · coeffₗ v ∈ S·VB ⊆ image(Iʲ)`.
    obtain ⟨bv, hbv_mem, hbv_eq⟩ := mvTateAlgNhd_coeff_mem m P k hv l
    have hcoeffv_VB : MvPowerSeries.coeff l v.val ∈ VB :=
      hkV ⟨bv, hbv_mem, hbv_eq⟩
    have hprod : s * MvPowerSeries.coeff l v.val ∈
        (Subtype.val '' ((P.I ^ j : Ideal P.A₀) : Set P.A₀) : Set A) :=
      hSVB (Set.mul_mem_mul hs hcoeffv_VB)
    obtain ⟨b, hb_mem, hb_eq⟩ := hprod
    exact ⟨b, hb_mem, by rw [hcoeff l, hb_eq]⟩
  refine mvTateAlgNhd_of_coeff_mem_principal m P j (IsTateRing.principalPair A).π
    (IsTateRing.principalPair A).I_eq_span (IsTateRing.principalPair A).π_isUnit ?_ hmem
  intro l
  obtain ⟨b, hb_mem, hb_eq⟩ := hmem l
  rw [← hb_eq]; exact b.property

/-- The canonical ring hom from polynomials into the restricted power series subring:
`MvPolynomial.coeToMvPowerSeries.ringHom`, corestricted (a polynomial has finitely many
nonzero coefficients, so its coefficient family is eventually zero, hence restricted). -/
noncomputable def mvPolynomialToTate (m : ℕ) :
    MvPolynomial (Fin m) A →+* ↥(restrictedMvPowerSeriesSubring m A) :=
  RingHom.codRestrict (MvPolynomial.coeToMvPowerSeries.ringHom)
    (restrictedMvPowerSeriesSubring m A) (fun p => by
      classical
      refine mvIsRestricted_of_eventually_zero m _
        ((p.support.sup fun v => Finset.univ.sup v) + 1) (fun l hl => ?_)
      obtain ⟨i, hi⟩ := hl
      show MvPowerSeries.coeff l (MvPolynomial.coeToMvPowerSeries.ringHom p) = 0
      rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
      by_contra hne
      have hmem : l ∈ p.support := MvPolynomial.mem_support_iff.mpr hne
      have hle : l i ≤ p.support.sup fun v => Finset.univ.sup v :=
        le_trans (Finset.le_sup (f := fun j => l j) (Finset.mem_univ i))
          (Finset.le_sup (f := fun v : Fin m →₀ ℕ => Finset.univ.sup v) hmem)
      omega)

/-- `mvPolynomialToTate` sends the constant polynomial `C a` to the constant series. -/
@[simp] theorem mvPolynomialToTate_C (m : ℕ) (a : A) :
    mvPolynomialToTate m (MvPolynomial.C a) =
      algebraMap A ↥(restrictedMvPowerSeriesSubring m A) a := by
  apply Subtype.ext
  show (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.C a) :
    MvPowerSeries (Fin m) A) = _
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C]
  rfl

/-- `mvPolynomialToTate` sends the variable `X j` to the variable series. -/
@[simp] theorem mvPolynomialToTate_X (m : ℕ) (j : Fin m) :
    mvPolynomialToTate m (MvPolynomial.X j) =
      (⟨MvPowerSeries.X j, MvPowerSeries.X_isRestricted j⟩ :
        ↥(restrictedMvPowerSeriesSubring m A)) := by
  apply Subtype.ext
  show (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X j) :
    MvPowerSeries (Fin m) A) = _
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]

/-- **Polynomials are dense in `A⟨X₁,…,Xₘ⟩`** (range form): the range of
`mvPolynomialToTate` is dense for the canonical Tate topology. Range form of
`mvTateAlgebra_polynomials_dense` (every eventually-zero series is the image of its
truncating polynomial), suited for `Continuous.ext_on` equalizer arguments. -/
theorem mvPolynomialToTate_denseRange [IsTateRing A] (m : ℕ) :
    @DenseRange _ (mvTateAlgebraTopology' m) _ (⇑(mvPolynomialToTate (A := A) m)) := by
  classical
  letI : TopologicalSpace ↥(restrictedMvPowerSeriesSubring m A) := mvTateAlgebraTopology' m
  refine Dense.mono ?_ (mvTateAlgebra_polynomials_dense (A := A) m)
  rintro g ⟨N, hN⟩
  refine ⟨∑ v ∈ Finset.image
      (fun f : Fin m → Fin N => (Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)))
      Finset.univ,
    MvPolynomial.monomial v (g.val v), ?_⟩
  apply Subtype.ext
  show (MvPolynomial.coeToMvPowerSeries.ringHom _ : MvPowerSeries (Fin m) A) = g.val
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  ext l
  rw [MvPolynomial.coeff_coe]
  refine (MvPolynomial.coeff_sum _ _ _).trans ?_
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' _ l (fun x => g.val x)]
  split_ifs with hl
  · rfl
  · -- `l` outside the box: some coordinate is `≥ N`, so `g.val l = 0`.
    by_contra hne
    apply hl
    have hbox : ∀ i, l i < N := by
      intro i
      by_contra hge
      push Not at hge
      exact hne ((hN l ⟨i, hge⟩).symm)
    refine Finset.mem_image.mpr ⟨fun i => ⟨l i, hbox i⟩, Finset.mem_univ _, ?_⟩
    have : (fun i => ((⟨l i, hbox i⟩ : Fin N) : ℕ)) = ⇑l := by funext i; rfl
    rw [this]
    exact Finsupp.equivFunOnFinite.symm_apply_apply l

end MvTateAlgebra
