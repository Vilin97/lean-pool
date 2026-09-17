/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

-- Adapted for Lean Pool from 0stellensatz/MassFormula at 7fa41a621f724f110183904d3fd19c6730a932ad.
module

public import LeanPool.MassFormula.Defs
import LeanPool.MassFormula.First
import LeanPool.MassFormula.Orbit
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Auxiliary file: `tsum_one_div_w_mul_q_pow_c`—**Theorem 2** (p.1031)

The mass formula proper: for any set `R` of representatives of the isomorphism classes of the
elements of `sigma K n`, the sum of `1 / ((w M.1 : ℝ≥0∞) * (q K : ℝ≥0∞) ^ c M.1)` over `M` in `R` is
`1` ([Serre 1978, Theorem 2, p.1031][Serre1978]). It is Theorem 1 regrouped along the partition of
`sigma K n` into isomorphism classes:

- `c` is an invariant of the `K`-isomorphism class (`c_eq_of_algEquiv`): `discIdeal` is defined
  from the integral `K`-bases of the subextension alone, and a `K`-isomorphism carries the integral
  bases of the one field onto those of the other with the same discriminant
  (`Algebra.discr_eq_discr_of_algEquiv`), so `discIdeal`—hence `d`, hence `c`—transports, with
  no contact with `integers` or the ramification data.
- Grouping the terms of Theorem 1 by the representative of the class (`ENNReal.tsum_fiberwise`, over
  `ℝ≥0∞` where no rearrangement needs justifying) makes each class contribute its cardinality times
  `1 / q ^ c`; the class is finite of cardinality `n / w` by Remark 3° (`ncard_isomorphic_mul_w`),
  which is also what evaluates the constant inner sum.
- The regrouped identity reads `n` = the sum over `R` of `(n / w M) * (1 / q ^ c M)`; cancelling
  `n`—legitimate in `ℝ≥0∞` since `0 < n` and `n ≠ ⊤`—is the theorem.

## References

* [Serre1978] J-P. Serre, *Une «formule de masse» pour les extensions totalement ramifiées de
  degré donné d'un corps local*, C. R. Acad. Sci. Paris **286** (1978), Série A, 1031–1036.
-/

@[expose] public section

open ValuativeRel
open scoped ENNReal

namespace MassFormula

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- A `K`-isomorphism carries every integral `K`-basis of `L` onto an integral `K`-basis of `M`
with the same discriminant (`Algebra.discr_eq_discr_of_algEquiv`), so every generator of
`discIdeal L` is among the generators of `discIdeal M`. -/
private theorem discIdeal_le_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : ↥L ≃ₐ[K] ↥M) : discIdeal L ≤ discIdeal M := by
  refine Ideal.span_mono ?_
  rintro x ⟨b, hbint, hbdisc⟩
  have hfr : Module.finrank K ↥L = Module.finrank K ↥M := e.toLinearEquiv.finrank_eq
  refine ⟨(b.map e.toLinearEquiv).reindex (finCongr hfr), fun i => ?_, ?_⟩
  · -- the transported entries are integral over `𝒪[K]`
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
    exact (hbint _).map (e.toAlgHom.restrictScalars ↥𝒪[K])
  · -- the transported basis has the same discriminant
    have hmap : ⇑(b.map e.toLinearEquiv) = ⇑e ∘ ⇑b :=
      funext fun i => b.map_apply e.toLinearEquiv i
    rw [hbdisc, Algebra.discr_eq_discr_of_algEquiv (⇑b) e, ← hmap,
      ← Algebra.discr_reindex (A := K) (b := b.map e.toLinearEquiv) (f := finCongr hfr),
      ← Module.Basis.coe_reindex]

omit [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] in
/-- `discIdeal` is an invariant of the `K`-isomorphism class: the two inclusions of
`discIdeal_le_of_algEquiv`. -/
private theorem discIdeal_eq_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : ↥L ≃ₐ[K] ↥M) : discIdeal L = discIdeal M :=
  le_antisymm (discIdeal_le_of_algEquiv K e) (discIdeal_le_of_algEquiv K e.symm)

omit [IsUniformAddGroup K] in
/-- `c` is an invariant of the `K`-isomorphism class: `d` is one through
`discIdeal_eq_of_algEquiv`, and the degree is one through the underlying `K`-linear isomorphism. -/
private theorem c_eq_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : ↥L ≃ₐ[K] ↥M) : c L = c M := by
  have hd : d L = d M := congrArg (multiplicity 𝓂[K]) (discIdeal_eq_of_algEquiv K e)
  have hfr : Module.finrank K ↥L = Module.finrank K ↥M := e.toLinearEquiv.finrank_eq
  have h : d L + 1 - Module.finrank K ↥L = d M + 1 - Module.finrank K ↥M := by rw [hd, hfr]
  exact h

/-- The sum of `1 / ((w M.1 : ℝ≥0∞) * (q K : ℝ≥0∞) ^ c M.1)` over any set `R` of representatives of
the isomorphism classes of the elements of `sigma K n` is `1` ([Serre 1978, Theorem 2,
p.1031][Serre1978]). Theorem 1 is regrouped
along the fibers of the map sending a member of `sigma K n` to its representative: each fiber is the
isomorphism class of its representative, finite of cardinality `n / w` by Remark 3°
(`ncard_isomorphic_mul_w`), and `c` is constant on it (`c_eq_of_algEquiv`), so the fiber contributes
`(n / w) * (1 / q ^ c)`; cancelling `n` from the resulting identity is the claim. -/
theorem tsum_one_div_w_mul_q_pow_c (n : ℕ) (hn : 0 < n)
    (R : Set (IntermediateField K (SeparableClosure K))) (hR : IsRepresentativeSet n R) :
    ∑' M : R, 1 / ((w M.1 : ℝ≥0∞) * (q K : ℝ≥0∞) ^ c M.1) = 1 := by
  classical
  -- the representative map: each member of `Σ_n` goes to the member of `R` it is isomorphic to
  set rep : ↥(sigma K n) → ↥R := fun L =>
    ⟨(hR.2 L.1 L.2).choose, ((hR.2 L.1 L.2).choose_spec.1).1⟩ with hrep
  have hrep_iso : ∀ L : ↥(sigma K n), Nonempty (↥L.1 ≃ₐ[K] ↥(rep L).1) := fun L =>
    ((hR.2 L.1 L.2).choose_spec.1).2
  have hrep_eq : ∀ (L : ↥(sigma K n)) (M : ↥R), Nonempty (↥L.1 ≃ₐ[K] ↥M.1) → rep L = M :=
    fun L M hiso => Subtype.ext ((hR.2 L.1 L.2).choose_spec.2 M.1 ⟨M.2, hiso⟩).symm
  -- the fiber of the representative map over `M` is the isomorphism class of `M` inside `Σ_n`
  have hmem_class : ∀ (M : ↥R) (L : ↥(sigma K n)), rep L = M →
      L.1 ∈ {M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')} := by
    intro M L hLM
    refine Set.mem_sep_iff.mpr ⟨L.2, ?_⟩
    have h := hrep_iso L
    rw [hLM] at h
    exact h.map fun e => e.symm
  have hequiv : ∀ M : ↥R,
      ↑(rep ⁻¹' {M}) ≃ ↥{M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')} := fun M =>
    { toFun := fun L => ⟨L.1.1, hmem_class M L.1 L.2⟩
      invFun := fun M' => ⟨⟨M'.1, (Set.mem_sep_iff.mp M'.2).1⟩,
        hrep_eq ⟨M'.1, (Set.mem_sep_iff.mp M'.2).1⟩ M
          ((Set.mem_sep_iff.mp M'.2).2.map fun e => e.symm)⟩
      left_inv := fun L => rfl
      right_inv := fun M' => rfl }
  have hcard : ∀ M : ↥R,
      Nat.card ↑(rep ⁻¹' {M}) = ({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard :=
    fun M => by rw [Nat.card_congr (hequiv M), Nat.card_coe_set_eq]
  -- Remark 3° makes each class, hence each fiber, finite
  have hfin : ∀ M : ↥R, Finite ↑(rep ⁻¹' {M}) := by
    intro M
    have hcls := ncard_isomorphic_mul_w K n hn M.1 (hR.1 M.2)
    have hne : ({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcls
      omega
    have := (Set.finite_of_ncard_ne_zero hne).to_subtype
    exact Finite.of_equiv _ (hequiv M).symm
  -- the inner sum over a fiber: `c` is constant on the class, which is finite
  have hinner : ∀ M : ↥R,
      ∑' L : ↑(rep ⁻¹' {M}), (1 : ℝ≥0∞) / (q K : ℝ≥0∞) ^ c L.1.1 =
      (({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard : ℝ≥0∞) *
        (1 / (q K : ℝ≥0∞) ^ c M.1) := by
    intro M
    have := hfin M
    have : Fintype ↑(rep ⁻¹' {M}) := Fintype.ofFinite _
    have hc : ∀ L : ↑(rep ⁻¹' {M}), c L.1.1 = c M.1 := by
      intro L
      have hLM : rep L.1 = M := L.2
      have h := hrep_iso L.1
      rw [hLM] at h
      exact c_eq_of_algEquiv K (Classical.choice h)
    calc ∑' L : ↑(rep ⁻¹' {M}), (1 : ℝ≥0∞) / (q K : ℝ≥0∞) ^ c L.1.1
        = ∑' _L : ↑(rep ⁻¹' {M}), (1 : ℝ≥0∞) / (q K : ℝ≥0∞) ^ c M.1 :=
          tsum_congr fun L => by rw [hc L]
      _ = ∑ _L : ↑(rep ⁻¹' {M}), (1 : ℝ≥0∞) / (q K : ℝ≥0∞) ^ c M.1 := tsum_fintype _
      _ = Fintype.card ↑(rep ⁻¹' {M}) • ((1 : ℝ≥0∞) / (q K : ℝ≥0∞) ^ c M.1) := by
          rw [Finset.sum_const, Finset.card_univ]
      _ = (Nat.card ↑(rep ⁻¹' {M}) : ℝ≥0∞) * (1 / (q K : ℝ≥0∞) ^ c M.1) := by
          rw [nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ = (({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard : ℝ≥0∞) *
            (1 / (q K : ℝ≥0∞) ^ c M.1) := by rw [hcard M]
  -- Theorem 1, regrouped along the fibers of the representative map
  have hgroup : ∑' M : ↥R,
      (({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard : ℝ≥0∞) *
        (1 / (q K : ℝ≥0∞) ^ c M.1) = (n : ℝ≥0∞) :=
    calc ∑' M : ↥R, (({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard : ℝ≥0∞) *
          (1 / (q K : ℝ≥0∞) ^ c M.1)
        = ∑' M : ↥R, ∑' L : ↑(rep ⁻¹' {M}), (1 : ℝ≥0∞) / (q K : ℝ≥0∞) ^ c L.1.1 :=
          tsum_congr fun M => (hinner M).symm
      _ = ∑' L : ↥(sigma K n), 1 / (q K : ℝ≥0∞) ^ c L.1 :=
          ENNReal.tsum_fiberwise (fun L : ↥(sigma K n) => 1 / (q K : ℝ≥0∞) ^ c L.1) rep
      _ = (n : ℝ≥0∞) := tsum_one_div_q_pow_c K n hn
  -- cancel `n`: each summand of the regrouped identity is `n` times the corresponding mass
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  refine (ENNReal.mul_right_inj hn0 hntop).mp ?_
  rw [mul_one, ← ENNReal.tsum_mul_left]
  refine Eq.trans (tsum_congr fun M => ?_) hgroup
  have hcls := ncard_isomorphic_mul_w K n hn M.1 (hR.1 M.2)
  have hw0 : (w M.1 : ℝ≥0∞) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at hcls
    omega
  have hwtop : (w M.1 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [one_div, one_div, ENNReal.mul_inv (Or.inl hw0) (Or.inl hwtop)]
  calc (n : ℝ≥0∞) * ((w M.1 : ℝ≥0∞)⁻¹ * ((q K : ℝ≥0∞) ^ c M.1)⁻¹)
      = ((({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard : ℝ≥0∞) * (w M.1 : ℝ≥0∞)) *
          ((w M.1 : ℝ≥0∞)⁻¹ * ((q K : ℝ≥0∞) ^ c M.1)⁻¹) := by
        rw [← Nat.cast_mul, hcls]
    _ = (({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard : ℝ≥0∞) *
          ((w M.1 : ℝ≥0∞) * (w M.1 : ℝ≥0∞)⁻¹) * ((q K : ℝ≥0∞) ^ c M.1)⁻¹ := by
        ring
    _ = (({M' ∈ sigma K n | Nonempty (↥M.1 ≃ₐ[K] ↥M')}).ncard : ℝ≥0∞) *
          ((q K : ℝ≥0∞) ^ c M.1)⁻¹ := by
        rw [ENNReal.mul_inv_cancel hw0 hwtop, mul_one]

end MassFormula
